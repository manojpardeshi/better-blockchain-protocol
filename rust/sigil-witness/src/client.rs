//! A minimal blocking HTTP/1.1 client for the v0 wire protocol: a standby member challenging the
//! members of its version for heartbeats (SPEC §5.5). One request per connection, `http://` only,
//! no new dependencies. Nothing it reads is trusted: callers verify what comes back.

use std::io::{ErrorKind, Read, Write};
use std::net::{SocketAddr, TcpStream, ToSocketAddrs};
use std::time::{Duration, Instant};

use crate::json::{parse, Json};

/// The largest reply read (a heartbeat is a few hundred bytes).
pub const MAX_REPLY: usize = 64 << 10;

/// The whole exchange (connect, request, reply) must finish within this many timeouts.
pub const REPLY_DEADLINE: u32 = 4;

/// What is left of the exchange's budget, as a socket timeout (an error once it is spent).
fn left(url: &str, deadline: Instant, timeout: Duration) -> Result<Duration, String> {
    let rest = deadline.saturating_duration_since(Instant::now());
    if rest.is_zero() {
        return Err(format!("{url}: no complete reply in time"));
    }
    Ok(rest.min(timeout))
}

// DNS may return an unreachable address first. Reserve a share of the connect
// budget for every remaining address while respecting the exchange deadline.
fn connect_any(url: &str, addrs: impl IntoIterator<Item = SocketAddr>, deadline: Instant, timeout: Duration) -> Result<TcpStream, String> {
    let addrs: Vec<_> = addrs.into_iter().collect();
    if addrs.is_empty() {
        return Err(format!("{url}: no address"));
    }
    let mut last_error = String::new();
    for (index, addr) in addrs.iter().enumerate() {
        let slice = left(url, deadline, timeout)? / (addrs.len() - index) as u32;
        if slice.is_zero() {
            return Err(format!("{url}: connection timed out"));
        }
        match TcpStream::connect_timeout(addr, slice) {
            Ok(stream) => return Ok(stream),
            Err(error) => last_error = error.to_string(),
        }
    }
    Err(format!("{url}: {last_error}"))
}

/// `POST {url}/v0/{method}` with `body`; the `ok` result of an HTTP 200 reply, else an error.
///
/// Every socket operation is bounded by `timeout` and the whole exchange by `REPLY_DEADLINE`
/// timeouts, so a member trickling bytes (status line, headers or body) cannot hold the prober.
pub fn post(url: &str, method: &str, body: &Json, timeout: Duration) -> Result<Json, String> {
    let deadline = Instant::now() + timeout * REPLY_DEADLINE;
    let rest = url.strip_prefix("http://").ok_or_else(|| format!("{url}: only http:// URLs are supported"))?;
    let hostport = rest.split('/').next().unwrap_or(rest);
    let addrs = hostport.to_socket_addrs().map_err(|e| format!("{url}: {e}"))?;
    let mut s = connect_any(url, addrs, deadline, timeout)?;
    let data = body.canonical();
    let head = format!(
        "POST /v0/{method} HTTP/1.1\r\nHost: {hostport}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        data.len()
    );
    let mut out = head.into_bytes();
    out.extend_from_slice(&data);
    let mut sent = 0;
    while sent < out.len() {
        s.set_write_timeout(Some(left(url, deadline, timeout)?)).map_err(|e| e.to_string())?;
        match s.write(&out[sent..]) {
            Ok(0) => return Err(format!("{url}: connection closed")),
            Ok(n) => sent += n,
            Err(e) if e.kind() == ErrorKind::Interrupted => continue,
            Err(e) => return Err(format!("{url}: {e}")),
        }
    }
    let mut buf = Vec::new();
    let mut chunk = [0u8; 16 << 10];
    loop {
        s.set_read_timeout(Some(left(url, deadline, timeout)?)).map_err(|e| e.to_string())?;
        let n = match s.read(&mut chunk) {
            Ok(n) => n,
            Err(e) if e.kind() == ErrorKind::Interrupted => continue,
            Err(e) => return Err(format!("{url}: {e}")),
        };
        if n == 0 {
            break;
        }
        buf.extend_from_slice(&chunk[..n]);
        if buf.len() > MAX_REPLY {
            return Err(format!("{url}: reply too large"));
        }
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{SocketAddr, TcpListener};
    use std::time::Instant;

    #[test]
    fn tries_next_address_after_connection_failure() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let reachable = listener.local_addr().unwrap();
        let unreachable: SocketAddr = "127.0.0.1:0".parse().unwrap();
        let stream = connect_any("test", [unreachable, reachable], Instant::now() + Duration::from_secs(4), Duration::from_secs(1)).unwrap();
        assert_eq!(stream.peer_addr().unwrap(), reachable);
    }

    /// A member that trickles its reply one byte at a time, each just inside the socket
    /// timeout, must not hold the prober: the whole reply has a deadline (before: the prober
    /// kept reading for as long as the bytes kept coming, up to `MAX_REPLY` of them).
    #[test]
    fn a_trickling_reply_hits_the_deadline() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let url = format!("http://{}", listener.local_addr().unwrap());
        std::thread::spawn(move || {
            if let Ok((mut s, _)) = listener.accept() {
                let _ = s.write_all(b"HTTP/1.1 200 OK\r\n\r\n");
                for _ in 0..150 {
                    std::thread::sleep(Duration::from_millis(100));
                    if s.write_all(b" ").is_err() {
                        break;
                    }
                }
            }
        });
        let t0 = Instant::now();
        let out = post(&url, "heartbeat", &Json::Null, Duration::from_millis(500));
        assert!(out.is_err());
        assert!(t0.elapsed() < Duration::from_secs(3), "read for {:?}", t0.elapsed());
    }

    /// The deadline covers the whole exchange: a status line trickled from the first byte, by a
    /// member that never reads the request, ends within `REPLY_DEADLINE` timeouts.
    #[test]
    fn a_trickled_status_line_hits_the_deadline() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let url = format!("http://{}", listener.local_addr().unwrap());
        std::thread::spawn(move || {
            if let Ok((mut s, _)) = listener.accept() {
                for b in b"HTTP/1.1 200 OK\r\nX-Pad: ".iter().chain([b'a'; 200].iter()) {
                    std::thread::sleep(Duration::from_millis(300));
                    if s.write_all(&[*b]).is_err() {
                        break;
                    }
                }
            }
        });
        let t0 = Instant::now();
        assert!(post(&url, "heartbeat", &Json::Null, Duration::from_millis(500)).is_err());
        assert!(t0.elapsed() < Duration::from_secs(3), "read for {:?}", t0.elapsed());
    }

    /// Replies that are not JSON, not an object, have no `ok`, or are too large are errors.
    #[test]
    fn malformed_replies_are_errors() {
        let big = format!("{{\"ok\": \"{}\"}}", "A".repeat(MAX_REPLY));
        let deep = format!("{{\"ok\": {}{}}}", "[".repeat(100_000), "]".repeat(100_000));
        for body in ["{not json", "[1, 2]", "{}", "\u{0}\u{ff}", big.as_str(), deep.as_str()] {
            let listener = TcpListener::bind("127.0.0.1:0").unwrap();
            let url = format!("http://{}", listener.local_addr().unwrap());
            let reply = format!("HTTP/1.1 200 OK\r\nContent-Length: {}\r\n\r\n{body}", body.len());
            std::thread::spawn(move || {
                if let Ok((mut s, _)) = listener.accept() {
                    let mut buf = [0u8; 4096];
                    let _ = s.read(&mut buf);
                    let _ = s.write_all(reply.as_bytes());
                }
            });
            assert!(post(&url, "heartbeat", &Json::Null, Duration::from_secs(2)).is_err(), "{:.20}", body);
        }
    }
}
