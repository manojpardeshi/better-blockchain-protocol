//! A minimal blocking HTTP/1.1 client for the v0 wire protocol: a standby member challenging the
//! members of its version for heartbeats (SPEC §5.5). One request per connection, `http://` only,
//! no new dependencies. Nothing it reads is trusted: callers verify what comes back.

use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::Duration;

use crate::json::{parse, Json};

/// The largest reply read (a heartbeat is a few hundred bytes).
pub const MAX_REPLY: usize = 64 << 10;

/// `POST {url}/v0/{method}` with `body`; the `ok` result of an HTTP 200 reply, else an error.
pub fn post(url: &str, method: &str, body: &Json, timeout: Duration) -> Result<Json, String> {
    let rest = url.strip_prefix("http://").ok_or_else(|| format!("{url}: only http:// URLs are supported"))?;
    let hostport = rest.split('/').next().unwrap_or(rest);
    let addr = hostport.to_socket_addrs().map_err(|e| format!("{url}: {e}"))?.next().ok_or_else(|| format!("{url}: no address"))?;
    let mut s = TcpStream::connect_timeout(&addr, timeout).map_err(|e| format!("{url}: {e}"))?;
    s.set_read_timeout(Some(timeout)).map_err(|e| e.to_string())?;
    s.set_write_timeout(Some(timeout)).map_err(|e| e.to_string())?;
    let data = body.canonical();
    let head = format!(
        "POST /v0/{method} HTTP/1.1\r\nHost: {hostport}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        data.len()
    );
    s.write_all(head.as_bytes()).and_then(|_| s.write_all(&data)).map_err(|e| format!("{url}: {e}"))?;
    let mut buf = Vec::new();
    s.take(MAX_REPLY as u64 + 1).read_to_end(&mut buf).map_err(|e| format!("{url}: {e}"))?;
    if buf.len() > MAX_REPLY {
        return Err(format!("{url}: reply too large"));
    }
    let end = buf.windows(4).position(|w| w == b"\r\n\r\n").ok_or_else(|| format!("{url}: malformed reply"))?;
    let head = std::str::from_utf8(&buf[..end]).map_err(|_| format!("{url}: malformed reply"))?;
    let status = head.split_whitespace().nth(1).ok_or_else(|| format!("{url}: malformed reply"))?;
    let mut payload = &buf[end + 4..];
    for line in head.lines().skip(1) {
        if let Some((k, v)) = line.split_once(':') {
            if k.trim().eq_ignore_ascii_case("content-length") {
                let n: usize = v.trim().parse().map_err(|_| format!("{url}: malformed reply"))?;
                payload = payload.get(..n).ok_or_else(|| format!("{url}: short reply"))?;
            }
        }
    }
    if status != "200" {
        return Err(format!("{url}: HTTP {status}"));
    }
    let v = parse(payload).map_err(|e| format!("{url}: {e}"))?;
    v.get("ok").cloned().ok_or_else(|| format!("{url}: no result"))
}
