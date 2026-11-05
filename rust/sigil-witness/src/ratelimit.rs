//! Admission control for a witness on the open network (docs/WIRE.md "Admission control"),
//! the same rules and defaults as `sigil/ratelimit.py`.
//!
//! * A **token bucket per client** ([`RateLimiter`]): `rate` requests per second, bursts of up
//!   to `burst`. The client is its IPv4 address or its IPv6 /64 ([`client_key`]). A request over
//!   the limit is answered HTTP 429 `rejected` before the witness sees it, so a refusal can only
//!   cost liveness, never safety (declining to vote is abstention, SPEC §5).
//! * **Connection caps** ([`ConnectionLimiter`]): at most [`MAX_CONNECTIONS`] open connections in
//!   all and [`MAX_CLIENT_CONNECTIONS`] per client (with a rate limit), and a connection that
//!   waits on its client for [`IDLE_TIMEOUT`] is closed.
//!
//! A witness listening on loopback has no rate limit unless asked for one (`--rate-limit`);
//! `--rate-limit 0` turns it off anywhere. `tests/vectors.rs` replays the reference's verdicts.

use std::collections::{BTreeMap, HashMap};
use std::net::IpAddr;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// Requests per second per client.
pub const DEFAULT_RATE: f64 = 20.0;
/// Tokens a client may save up.
pub const DEFAULT_BURST: u32 = 100;
/// Buckets kept; the least recently seen is forgotten first.
pub const MAX_CLIENTS: usize = 65_536;
/// Open connections in all.
pub const MAX_CONNECTIONS: usize = 256;
/// Open connections per client (with a rate limit).
pub const MAX_CLIENT_CONNECTIONS: usize = 16;
/// How long a connection may wait for its client.
pub const IDLE_TIMEOUT: Duration = Duration::from_secs(30);

/// The client a request is counted against: an IPv4 address (also when IPv4-mapped) or an
/// IPv6 /64, written `"<network>/64"`.
pub fn client_key(ip: IpAddr) -> String {
    match ip {
        IpAddr::V4(v4) => v4.to_string(),
        IpAddr::V6(v6) => match v6.to_ipv4_mapped() {
            Some(v4) => v4.to_string(),
            None => format!("{}/64", std::net::Ipv6Addr::from(u128::from(v6) >> 64 << 64)),
        },
    }
}

/// [`client_key`] of a textual address; anything that is not an IP address is its own key.
pub fn client_key_str(host: &str) -> String {
    host.parse::<IpAddr>().map(client_key).unwrap_or_else(|_| host.to_string())
}

/// Does a listen address only accept connections from this machine?
pub fn is_loopback(host: &str) -> bool {
    host == "localhost" || host.parse::<IpAddr>().is_ok_and(|ip| ip.is_loopback())
}

struct Bucket {
    tokens: f64,
    last: f64,
    seen: u64,
}

#[derive(Default)]
struct Buckets {
    by_key: HashMap<String, Bucket>,
    /// `seen` stamp -> key, oldest first (the reference's `OrderedDict` order).
    order: BTreeMap<u64, String>,
    tick: u64,
}

/// A token bucket per client key. Forgetting a bucket gives that client a full one, so evicting
/// the least recently seen when [`MAX_CLIENTS`] are tracked can only favour the evicted client.
pub struct RateLimiter {
    rate: f64,
    burst: f64,
    max_clients: usize,
    start: Instant,
    inner: Mutex<Buckets>,
}

impl RateLimiter {
    pub fn new(rate: f64, burst: u32) -> Result<RateLimiter, String> {
        RateLimiter::with_max_clients(rate, burst, MAX_CLIENTS)
    }

    pub fn with_max_clients(rate: f64, burst: u32, max_clients: usize) -> Result<RateLimiter, String> {
        if !(rate > 0.0) || burst < 1 {
            return Err("rate must be positive and burst at least 1".into());
        }
        Ok(RateLimiter { rate, burst: burst as f64, max_clients, start: Instant::now(), inner: Mutex::default() })
    }

    /// Take one token for `key` now. Returns 0 if admitted, else the seconds to wait.
    pub fn admit(&self, key: &str) -> u64 {
        self.admit_at(key, self.start.elapsed().as_secs_f64())
    }

    /// [`RateLimiter::admit`] at clock reading `now` (seconds), as `RateLimiter.admit(key, now)`.
    pub fn admit_at(&self, key: &str, now: f64) -> u64 {
        let mut b = self.inner.lock().expect("rate limiter lock");
        b.tick += 1;
        let tick = b.tick;
        let (mut tokens, last) = match b.by_key.remove(key) {
            Some(old) => {
                b.order.remove(&old.seen);
                (old.tokens, old.last)
            }
            None => (self.burst, now),
        };
        tokens = self.burst.min(tokens + (now - last).max(0.0) * self.rate);
        let mut wait = 0;
        if tokens >= 1.0 {
            tokens -= 1.0;
        } else {
            wait = (((1.0 - tokens) / self.rate).ceil() as u64).max(1);
        }
        b.by_key.insert(key.to_string(), Bucket { tokens, last: now, seen: tick });
        b.order.insert(tick, key.to_string());
        while b.by_key.len() > self.max_clients {
            let Some((_, oldest)) = b.order.pop_first() else { break };
            b.by_key.remove(&oldest);
        }
        wait
    }

    /// How many clients are tracked.
    pub fn len(&self) -> usize {
        self.inner.lock().expect("rate limiter lock").by_key.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Counts open connections, in all and per client.
pub struct ConnectionLimiter {
    total: usize,
    per_client: Option<usize>,
    open: Mutex<(usize, HashMap<String, usize>)>,
}

/// Holds one connection slot; the slot is released when it is dropped.
pub struct ConnectionGuard {
    limiter: Arc<ConnectionLimiter>,
    key: String,
}

impl Drop for ConnectionGuard {
    fn drop(&mut self) {
        let mut o = self.limiter.open.lock().expect("connection lock");
        o.0 -= 1;
        if let Some(n) = o.1.get_mut(&self.key) {
            *n -= 1;
            if *n == 0 {
                o.1.remove(&self.key);
            }
        }
    }
}

impl ConnectionLimiter {
    pub fn new(total: usize, per_client: Option<usize>) -> Arc<ConnectionLimiter> {
        Arc::new(ConnectionLimiter { total, per_client, open: Mutex::default() })
    }

    /// A slot for a connection from `key`, or `None` if a cap is reached.
    pub fn acquire(self: &Arc<Self>, key: &str) -> Option<ConnectionGuard> {
        let mut o = self.open.lock().expect("connection lock");
        let mine = o.1.get(key).copied().unwrap_or(0);
        if o.0 >= self.total || self.per_client.is_some_and(|p| mine >= p) {
            return None;
        }
        o.0 += 1;
        o.1.insert(key.to_string(), mine + 1);
        Some(ConnectionGuard { limiter: self.clone(), key: key.to_string() })
    }

    /// Open connections now.
    pub fn open(&self) -> usize {
        self.open.lock().expect("connection lock").0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bucket_refills_and_evicts_least_recent() {
        let r = RateLimiter::with_max_clients(2.0, 3, 2).unwrap();
        assert_eq!([r.admit_at("a", 0.0), r.admit_at("a", 0.0), r.admit_at("a", 0.0)], [0, 0, 0]);
        assert_eq!(r.admit_at("a", 0.0), 1);
        assert_eq!(r.admit_at("a", 0.5), 0); // one token back after 0.5 s at 2/s
        r.admit_at("b", 1.0);
        r.admit_at("c", 1.0); // evicts a (least recently seen)
        assert_eq!(r.len(), 2);
        assert_eq!(r.admit_at("a", 1.0), 0);
        assert!(RateLimiter::new(0.0, 1).is_err() && RateLimiter::new(1.0, 0).is_err());
    }

    #[test]
    fn keys_and_loopback() {
        assert_eq!(client_key_str("10.1.2.3"), "10.1.2.3");
        assert_eq!(client_key_str("::ffff:10.1.2.3"), "10.1.2.3");
        assert_eq!(client_key_str("2001:db8:1:2:3:4:5:6"), "2001:db8:1:2::/64");
        assert_eq!(client_key_str("example"), "example");
        assert!(is_loopback("127.0.0.1") && is_loopback("::1") && is_loopback("localhost") && is_loopback("127.9.9.9"));
        assert!(!is_loopback("0.0.0.0") && !is_loopback("::") && !is_loopback("10.0.0.1") && !is_loopback("host"));
    }

    #[test]
    fn connection_caps() {
        let c = ConnectionLimiter::new(3, Some(2));
        let a1 = c.acquire("a").unwrap();
        let _a2 = c.acquire("a").unwrap();
        assert!(c.acquire("a").is_none());
        let _b = c.acquire("b").unwrap();
        assert!(c.acquire("c").is_none());
        drop(a1);
        assert_eq!(c.open(), 2);
        assert!(c.acquire("a").is_some());
    }
}
