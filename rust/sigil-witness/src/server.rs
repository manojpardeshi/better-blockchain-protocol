//! Wire protocol v0 (docs/WIRE.md): JSON over HTTP/1.1, the same calls as `sigil/server.py`.
//!
//! | Method | Path            | Body                | `ok` result            |
//! |--------|-----------------|---------------------|------------------------|
//! | GET    | `/v0/info`      | —                   | `{pk, constellation, version, frozen, stamps: {n, e} \| null}` |
//! | GET    | `/v0/charters`  | —                   | `{cid: [charter, …]}`  |
//! | POST   | `/v0/spend`     | `{request}`         | vote                   |
//! | POST   | `/v0/release`   | `{sigil, proof}`    | new generation         |
//! | POST   | `/v0/status`    | `{sigil}`           | `{gen, tid, votes}`    |
//! | POST   | `/v0/sell_stamp`| `{blinded: hex}`    | blind signature (hex)  |
//! | GET    | `/v0/proofs`    | —                   | `{proofs, forks}`      |
//! | POST   | `/v0/gossip`    | `{charters?, proofs?, forks?}` | `{charters, proofs, forks}` (counts accepted) |
//! | POST   | `/v0/freeze`    | `{charter}` (admin) | `{sig, snapshot}`      |
//! | POST   | `/v0/adopt`     | `{constellation, version, snapshots}` (admin) | `{constellation, version}` |
//!
//! Replies are `{"ok": result}` or `{"error": kind, "message": str, "vote": vote|null}` with
//! HTTP 409 (`conflict`), 403 (`rejected`), 400 (`bad_request`) or 500 (`internal`). Unlike
//! the reference, calls are served concurrently; the persist-before-answer rule is kept by
//! waiting for the store's group commit before any reply leaves. Everything that verifies
//! signatures (SPEND, RELEASE, gossip, FREEZE, ADOPT) runs on the blocking pool, never on the
//! async workers.
//!
//! The rotation calls (`freeze`, `adopt`) need `Authorization: Bearer <admin token>`; without
//! a configured token they are refused. Their bodies may be up to [`MAX_ADMIN_BODY`], read
//! only after the token was checked.
//!
//! Admission control (docs/WIRE.md, [`crate::ratelimit`]): [`router_with_limits`] answers a
//! client over its token bucket with HTTP 429 `rejected` before the call runs, and [`serve`]
//! caps open connections and closes those that wait on their client too long.

use std::future::Future;
use std::io;
use std::net::SocketAddr;
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll};
use std::time::Duration;

use axum::body::{to_bytes, Body};
use axum::extract::{ConnectInfo, Path, Request, State};
use axum::http::{header, HeaderMap, HeaderValue, StatusCode};
use axum::middleware::{self, Next};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::Router;
use tokio::io::{AsyncRead, AsyncWrite, ReadBuf};

use crate::json::{obj, parse, parse_with_depth, Json, MAX_DEPTH};
use crate::ratelimit::{client_key, ConnectionLimiter, RateLimiter, IDLE_TIMEOUT, MAX_CONNECTIONS};
use crate::witness::{Error, Outcome, Witness};

pub const MAX_BODY: usize = 1 << 20;
/// ADOPT carries every predecessor's evidence.
pub const MAX_ADMIN_BODY: usize = 256 << 20;
pub const ADMIN_METHODS: [&str; 2] = ["freeze", "adopt"];

pub fn reply(code: StatusCode, v: &Json) -> Response {
    (code, [(header::CONTENT_TYPE, "application/json")], v.canonical()).into_response()
}

fn error(code: StatusCode, kind: &str, message: &str, vote: Option<Json>) -> Response {
    reply(
        code,
        &obj([("error", Json::str(kind)), ("message", Json::str(message)), ("vote", vote.unwrap_or(Json::Null))]),
    )
}

fn bad_request(message: &str) -> Response {
    error(StatusCode::BAD_REQUEST, "bad_request", message, None)
}

fn internal() -> Response {
    error(StatusCode::INTERNAL_SERVER_ERROR, "internal", "internal error", None)
}

fn result_response(r: Result<Json, Error>) -> Response {
    match r {
        Ok(v) => reply(StatusCode::OK, &obj([("ok", v)])),
        Err(Error::Conflict(vote)) => error(StatusCode::CONFLICT, "conflict", "sigil bound to a different transition", vote),
        Err(Error::Rejected(m)) => error(StatusCode::FORBIDDEN, "rejected", &m, None),
        Err(Error::BadRequest(m)) => bad_request(&m),
    }
}

#[derive(Clone)]
struct App {
    w: Arc<Witness>,
    admin_token: Option<Arc<str>>,
}

/// The router without rotation calls (no admin token).
pub fn router(w: Arc<Witness>) -> Router {
    router_with_admin(w, None)
}

/// The router; `admin_token` enables `/v0/freeze` and `/v0/adopt` for requests carrying it.
pub fn router_with_admin(w: Arc<Witness>, admin_token: Option<String>) -> Router {
    router_with_limits(w, admin_token, None)
}

/// [`router_with_admin`], with every call but the rotation calls charged to its client's token
/// bucket in `limiter` (the client is the peer address [`serve`] records; without one, all
/// requests share one bucket).
pub fn router_with_limits(w: Arc<Witness>, admin_token: Option<String>, limiter: Option<Arc<RateLimiter>>) -> Router {
    let r = Router::new()
        .route("/v0/info", get(info))
        .route("/v0/charters", get(charters))
        .route("/v0/proofs", get(proofs))
        .route("/v0/:method", post(call))
        .fallback(|| async { error(StatusCode::NOT_FOUND, "bad_request", "unknown path", None) })
        .with_state(App { w, admin_token: admin_token.map(Arc::from) });
    match limiter {
        Some(l) => r.layer(middleware::from_fn_with_state(l, admit)),
        None => r,
    }
}

/// Charge the client one token; answer 429 `rejected` (with `Retry-After`) if it has none left.
/// The body of a refused request is read and dropped, so the client reliably gets the answer.
async fn admit(State(limiter): State<Arc<RateLimiter>>, req: Request, next: Next) -> Response {
    let path = req.uri().path();
    if ADMIN_METHODS.contains(&path.strip_prefix("/v0/").unwrap_or(path)) {
        return next.run(req).await; // refused before their body is read, unless authorised
    }
    let key = req.extensions().get::<ConnectInfo<SocketAddr>>().map(|c| client_key(c.0.ip())).unwrap_or_default();
    let wait = limiter.admit(&key);
    if wait == 0 {
        return next.run(req).await;
    }
    let _ = tokio::time::timeout(IDLE_TIMEOUT, to_bytes(req.into_body(), MAX_BODY)).await;
    let mut r = error(StatusCode::TOO_MANY_REQUESTS, "rejected", "rate limited", None);
    r.headers_mut().insert(header::RETRY_AFTER, HeaderValue::from(wait));
    r
}

async fn info(State(app): State<App>) -> Response {
    reply(StatusCode::OK, &obj([("ok", app.w.info())]))
}

async fn charters(State(app): State<App>) -> Response {
    reply(StatusCode::OK, &obj([("ok", app.w.registry().to_json())]))
}

async fn proofs(State(app): State<App>) -> Response {
    reply(StatusCode::OK, &obj([("ok", app.w.proofs())]))
}

fn field<'a>(body: &'a Json, k: &str) -> Result<&'a Json, Response> {
    body.get(k).ok_or_else(|| bad_request(&format!("'{k}'")))
}

/// Constant-time comparison of the `Authorization` header with `Bearer <token>`.
fn check_admin(token: Option<&str>, headers: &HeaderMap) -> Result<(), Response> {
    let Some(token) = token else {
        return Err(error(StatusCode::FORBIDDEN, "rejected", "rotation calls are disabled on this witness (no admin token)", None));
    };
    let want = format!("Bearer {token}");
    let got = headers.get(header::AUTHORIZATION).map(|v| v.as_bytes()).unwrap_or(b"");
    let same = got.len() == want.len() && got.iter().zip(want.as_bytes()).fold(0u8, |acc, (a, b)| acc | (a ^ b)) == 0;
    if same {
        Ok(())
    } else {
        Err(error(StatusCode::FORBIDDEN, "rejected", "bad admin token", None))
    }
}

/// Run `f` on the blocking pool (signature checks must never stall the async workers).
async fn blocking(f: impl FnOnce() -> Outcome + Send + 'static) -> Result<Outcome, Response> {
    tokio::task::spawn_blocking(f).await.map_err(|_| internal())
}

async fn call(State(app): State<App>, Path(method): Path<String>, headers: HeaderMap, body: Body) -> Response {
    let admin = ADMIN_METHODS.contains(&method.as_str());
    if admin {
        if let Err(r) = check_admin(app.admin_token.as_deref(), &headers) {
            return r;
        }
    }
    // A client that stops sending is dropped, never waited on forever (an authorised operator
    // sending ADOPT evidence is given all the time it needs).
    let limit = if admin { MAX_ADMIN_BODY } else { MAX_BODY };
    let patience = if admin { Duration::MAX } else { IDLE_TIMEOUT };
    let bytes = match tokio::time::timeout(patience, to_bytes(body, limit)).await {
        Ok(Ok(b)) => b,
        Ok(Err(_)) => return bad_request("body too large"),
        Err(_) => return bad_request("body not received in time"),
    };
    let body = if bytes.is_empty() {
        Json::Obj(Default::default())
    } else {
        // Evidence nests what requests carried a few levels deeper (as in the store).
        match if admin { parse_with_depth(&bytes, MAX_DEPTH + 16) } else { parse(&bytes) } {
            Ok(v) => v,
            Err(e) => return bad_request(&e.to_string()),
        }
    };
    if body.as_obj().is_none() {
        return bad_request("body must be an object");
    }
    let w = app.w.clone();
    let outcome: Result<Outcome, Response> = match method.as_str() {
        "spend" => match field(&body, "request") {
            Ok(req) => {
                let req = req.clone();
                blocking(move || w.spend(&req)).await
            }
            Err(r) => Err(r),
        },
        "release" => match (field(&body, "sigil"), field(&body, "proof")) {
            (Ok(s), Ok(p)) => {
                let (sigil, proof) = (s.clone(), p.clone());
                // Death proofs can carry many signatures.
                blocking(move || w.release(&sigil, &proof)).await
            }
            (Err(r), _) | (_, Err(r)) => Err(r),
        },
        "status" => field(&body, "sigil").map(|s| w.status(s)),
        "sell_stamp" => field(&body, "blinded").map(|b| w.sell_stamp(b)),
        "gossip" => blocking(move || w.gossip(&body)).await,
        "freeze" => match field(&body, "charter") {
            Ok(c) => {
                let c = c.clone();
                blocking(move || w.freeze(&c)).await
            }
            Err(r) => Err(r),
        },
        "adopt" => {
            let checked = field(&body, "constellation")
                .and_then(|_| field(&body, "version"))
                .and_then(|_| field(&body, "snapshots"))
                .and_then(|s| if s.as_arr().is_some() { Ok(()) } else { Err(bad_request("snapshots must be a list")) });
            match checked {
                Ok(()) => {
                    blocking(move || {
                        let null = Json::Null;
                        let (c, v) = (body.get("constellation").unwrap_or(&null), body.get("version").unwrap_or(&null));
                        let snaps = body.get("snapshots").and_then(Json::as_arr).map(Vec::as_slice).unwrap_or(&[]);
                        w.adopt_once(c, v, snaps)
                    })
                    .await
                }
                Err(r) => Err(r),
            }
        }
        other => Err(bad_request(&format!("unknown method '{other}'"))),
    };
    let (result, seq) = match outcome {
        Ok(o) => o,
        Err(r) => return r,
    };
    app.w.store.wait_async(seq).await; // persist before answering (SPEC §5)
    result_response(result)
}

// --------------------------------------------------------------------------- serving

/// Serve `app` on `listener` until `shutdown` resolves, then finish the open connections.
///
/// At most [`MAX_CONNECTIONS`] connections are open at once, and at most `per_client` from one
/// client ([`client_key`]); a connection over a cap is closed unread. A connection is closed if
/// its client takes longer than [`IDLE_TIMEOUT`] to send a request's headers (also between
/// requests), to send its body (see `call`), or to accept the reply. Each request carries the
/// peer address as `ConnectInfo<SocketAddr>`, which the rate limit uses.
pub async fn serve<F>(listener: tokio::net::TcpListener, app: Router, per_client: Option<usize>, shutdown: F) -> io::Result<()>
where
    F: Future<Output = ()> + Send + 'static,
{
    serve_with(listener, app, ConnectionLimiter::new(MAX_CONNECTIONS, per_client), IDLE_TIMEOUT, shutdown).await
}

/// [`serve`] with explicit connection caps and idle timeout (for tests).
pub async fn serve_with<F>(
    listener: tokio::net::TcpListener,
    app: Router,
    conns: Arc<ConnectionLimiter>,
    idle: Duration,
    shutdown: F,
) -> io::Result<()>
where
    F: Future<Output = ()> + Send + 'static,
{
    let (stop_tx, stop_rx) = tokio::sync::watch::channel(false);
    let mut tasks = tokio::task::JoinSet::new();
    tokio::pin!(shutdown);
    loop {
        let (stream, addr) = tokio::select! {
            r = listener.accept() => match r {
                Ok(x) => x,
                Err(e) => {
                    // Out of descriptors and the like: back off instead of spinning.
                    if !matches!(e.kind(), io::ErrorKind::ConnectionAborted | io::ErrorKind::ConnectionReset | io::ErrorKind::ConnectionRefused) {
                        tokio::time::sleep(Duration::from_millis(100)).await;
                    }
                    continue;
                }
            },
            _ = &mut shutdown => break,
        };
        while tasks.try_join_next().is_some() {}
        let Some(slot) = conns.acquire(&client_key(addr.ip())) else {
            drop(stream); // over a cap: closed unread
            continue;
        };
        let _ = stream.set_nodelay(true);
        let app = app.clone();
        let mut stop = stop_rx.clone();
        tasks.spawn(async move {
            let _slot = slot;
            let svc = hyper::service::service_fn(move |mut req: hyper::Request<hyper::body::Incoming>| {
                req.extensions_mut().insert(ConnectInfo(addr));
                let mut app = app.clone();
                async move { tower_service::Service::call(&mut app, req.map(Body::new)).await }
            });
            let mut builder = hyper::server::conn::http1::Builder::new();
            builder.timer(hyper_util::rt::TokioTimer::new()).header_read_timeout(idle);
            let io = hyper_util::rt::TokioIo::new(WriteTimeout::new(stream, idle));
            let conn = builder.serve_connection(io, svc);
            tokio::pin!(conn);
            tokio::select! {
                _ = conn.as_mut() => {}
                _ = stop.changed() => {
                    conn.as_mut().graceful_shutdown();
                    let _ = conn.await;
                }
            }
        });
    }
    drop(listener);
    let _ = stop_tx.send(true);
    while tasks.join_next().await.is_some() {}
    Ok(())
}

/// A stream whose writes fail once the peer has accepted nothing for `timeout` (a client that
/// never reads its reply would otherwise hold its connection forever). Reads are untouched:
/// hyper times out reading headers, and `call` times out reading bodies.
struct WriteTimeout<S> {
    io: S,
    timeout: Duration,
    deadline: Option<Pin<Box<tokio::time::Sleep>>>,
}

impl<S> WriteTimeout<S> {
    fn new(io: S, timeout: Duration) -> WriteTimeout<S> {
        WriteTimeout { io, timeout, deadline: None }
    }

    /// After a write returned `Pending`: fail if the deadline has passed, else keep waiting.
    fn stalled(&mut self, cx: &mut Context<'_>) -> Poll<io::Error> {
        let timeout = self.timeout;
        let d = self.deadline.get_or_insert_with(|| Box::pin(tokio::time::sleep(timeout)));
        match d.as_mut().poll(cx) {
            Poll::Ready(()) => Poll::Ready(io::Error::new(io::ErrorKind::TimedOut, "client stopped reading")),
            Poll::Pending => Poll::Pending,
        }
    }
}

impl<S: AsyncRead + Unpin> AsyncRead for WriteTimeout<S> {
    fn poll_read(mut self: Pin<&mut Self>, cx: &mut Context<'_>, buf: &mut ReadBuf<'_>) -> Poll<io::Result<()>> {
        Pin::new(&mut self.io).poll_read(cx, buf)
    }
}

impl<S: AsyncWrite + Unpin> AsyncWrite for WriteTimeout<S> {
    fn poll_write(mut self: Pin<&mut Self>, cx: &mut Context<'_>, buf: &[u8]) -> Poll<io::Result<usize>> {
        match Pin::new(&mut self.io).poll_write(cx, buf) {
            Poll::Pending => self.stalled(cx).map(Err),
            done => {
                self.deadline = None;
                done
            }
        }
    }

    fn poll_flush(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        match Pin::new(&mut self.io).poll_flush(cx) {
            Poll::Pending => self.stalled(cx).map(Err),
            done => {
                self.deadline = None;
                done
            }
        }
    }

    fn poll_shutdown(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        Pin::new(&mut self.io).poll_shutdown(cx)
    }
}
