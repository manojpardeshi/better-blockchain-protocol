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

use std::sync::Arc;

use axum::body::{to_bytes, Body};
use axum::extract::{Path, State};
use axum::http::{header, HeaderMap, StatusCode};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::Router;

use crate::json::{obj, parse, parse_with_depth, Json, MAX_DEPTH};
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
    Router::new()
        .route("/v0/info", get(info))
        .route("/v0/charters", get(charters))
        .route("/v0/proofs", get(proofs))
        .route("/v0/:method", post(call))
        .fallback(|| async { error(StatusCode::NOT_FOUND, "bad_request", "unknown path", None) })
        .with_state(App { w, admin_token: admin_token.map(Arc::from) })
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
    let bytes = match to_bytes(body, if admin { MAX_ADMIN_BODY } else { MAX_BODY }).await {
        Ok(b) => b,
        Err(_) => return bad_request("body too large"),
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
