//! Wire protocol v0 (docs/WIRE.md): JSON over HTTP/1.1.
//!
//! | Method | Path            | Body                | `ok` result            |
//! |--------|-----------------|---------------------|------------------------|
//! | GET    | `/v0/info`      | —                   | `{pk, constellation, version, frozen, stamps: null}` |
//! | GET    | `/v0/charters`  | —                   | `{cid: [charter, …]}`  |
//! | POST   | `/v0/spend`     | `{request}`         | vote                   |
//! | POST   | `/v0/release`   | `{sigil, proof}`    | new generation         |
//! | POST   | `/v0/status`    | `{sigil}`           | `{gen, tid, votes}`    |
//! | GET    | `/v0/proofs`    | —                   | `{proofs: [], forks: []}` (gossip is not stored) |
//! | POST   | `/v0/gossip`    | anything            | `{charters: 0, proofs: 0, forks: 0}` |
//! | POST   | `/v0/sell_stamp`| `{blinded}`         | always `rejected`: this witness sells no stamps |
//!
//! Replies are `{"ok": result}` or `{"error": kind, "message": str, "vote": vote|null}` with
//! HTTP 409 (`conflict`), 403 (`rejected`), 400 (`bad_request`) or 500 (`internal`). Unlike
//! the reference, calls are served concurrently; the persist-before-answer rule is kept by
//! waiting for the store's group commit before any reply leaves.

use std::sync::Arc;

use axum::body::{to_bytes, Body};
use axum::extract::{Path, State};
use axum::http::{header, StatusCode};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::Router;

use crate::json::{obj, parse, Json};
use crate::witness::{Error, Outcome, Witness};

pub const MAX_BODY: usize = 1 << 20;

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

fn result_response(r: Result<Json, Error>) -> Response {
    match r {
        Ok(v) => reply(StatusCode::OK, &obj([("ok", v)])),
        Err(Error::Conflict(vote)) => error(StatusCode::CONFLICT, "conflict", "sigil bound to a different transition", vote),
        Err(Error::Rejected(m)) => error(StatusCode::FORBIDDEN, "rejected", &m, None),
        Err(Error::BadRequest(m)) => bad_request(&m),
    }
}

pub fn router(w: Arc<Witness>) -> Router {
    Router::new()
        .route("/v0/info", get(info))
        .route("/v0/charters", get(charters))
        .route("/v0/proofs", get(proofs))
        .route("/v0/:method", post(call))
        .fallback(|| async { error(StatusCode::NOT_FOUND, "bad_request", "unknown path", None) })
        .with_state(w)
}

async fn info(State(w): State<Arc<Witness>>) -> Response {
    reply(StatusCode::OK, &obj([("ok", w.info())]))
}

async fn charters(State(w): State<Arc<Witness>>) -> Response {
    reply(StatusCode::OK, &obj([("ok", w.registry.to_json())]))
}

async fn proofs() -> Response {
    reply(StatusCode::OK, &obj([("ok", obj([("proofs", Json::Arr(vec![])), ("forks", Json::Arr(vec![]))]))]))
}

fn field<'a>(body: &'a Json, k: &str) -> Result<&'a Json, Response> {
    body.get(k).ok_or_else(|| bad_request(&format!("'{k}'")))
}

async fn call(State(w): State<Arc<Witness>>, Path(method): Path<String>, body: Body) -> Response {
    let bytes = match to_bytes(body, MAX_BODY).await {
        Ok(b) => b,
        Err(_) => return bad_request("body too large"),
    };
    let body = if bytes.is_empty() {
        Json::Obj(Default::default())
    } else {
        match parse(&bytes) {
            Ok(v) => v,
            Err(e) => return bad_request(&e.to_string()),
        }
    };
    if body.as_obj().is_none() {
        return bad_request("body must be an object");
    }
    let outcome: Outcome = match method.as_str() {
        "spend" => match field(&body, "request") {
            Ok(req) => w.spend(req),
            Err(r) => return r,
        },
        "release" => {
            let (sigil, proof) = match (field(&body, "sigil"), field(&body, "proof")) {
                (Ok(s), Ok(p)) => (s.clone(), p.clone()),
                (Err(r), _) | (_, Err(r)) => return r,
            };
            // Death proofs can carry many signatures: verify off the async workers.
            let w2 = w.clone();
            match tokio::task::spawn_blocking(move || w2.release(&sigil, &proof)).await {
                Ok(o) => o,
                Err(_) => return error(StatusCode::INTERNAL_SERVER_ERROR, "internal", "internal error", None),
            }
        }
        "status" => match field(&body, "sigil") {
            Ok(s) => w.status(s),
            Err(r) => return r,
        },
        "sell_stamp" => match field(&body, "blinded") {
            Ok(_) => (Err(Error::Rejected("this witness does not sell stamps".into())), 0),
            Err(r) => return r,
        },
        "gossip" => (Ok(obj([("charters", Json::Int(0)), ("proofs", Json::Int(0)), ("forks", Json::Int(0))])), 0),
        other => return bad_request(&format!("unknown method '{other}'")),
    };
    let (result, seq) = outcome;
    w.store.wait_async(seq).await; // persist before answering (SPEC §5)
    result_response(result)
}
