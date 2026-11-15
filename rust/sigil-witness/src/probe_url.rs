//! Validate standby heartbeat targets before they can influence dead-man observations.

use axum::http::Uri;

/// The built-in heartbeat client accepts only root HTTP origins with explicit ports.
/// Validate syntax without resolving DNS, so a temporarily unavailable name does not
/// prevent a standby member from starting.
pub fn validate_probe_url(url: &str) -> Result<(), String> {
    let invalid = || {
        format!("{url:?}: expected http://host:port (or http://[ipv6]:port), with no path or query")
    };
    if !url.starts_with("http://") {
        return Err(format!(
            "{url:?}: standby heartbeat probes support only http:// URLs"
        ));
    }
    if url.contains('#') {
        return Err(invalid());
    }
    let uri: Uri = url.parse().map_err(|_| invalid())?;
    let authority = uri.authority().ok_or_else(invalid)?;
    if authority.host().is_empty() || authority.as_str().contains('@') {
        return Err(invalid());
    }
    if authority.port_u16().filter(|p| *p != 0).is_none() {
        return Err(format!(
            "{url:?}: standby heartbeat probes require an explicit nonzero port"
        ));
    }
    if !matches!(uri.path_and_query().map(|p| p.as_str()), None | Some("/")) {
        return Err(invalid());
    }
    Ok(())
}

pub fn validate_probe_urls(urls: &[String]) -> Result<(), String> {
    for (index, url) in urls.iter().enumerate() {
        validate_probe_url(url).map_err(|e| format!("member URL {}: {e}", index + 1))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::validate_probe_url;

    #[test]
    fn accepts_root_http_origins() {
        for url in [
            "http://example.test:7000",
            "http://127.0.0.1:7000/",
            "http://[::1]:7000",
        ] {
            assert_eq!(validate_probe_url(url), Ok(()), "{url}");
        }
    }

    #[test]
    fn rejects_targets_the_heartbeat_client_cannot_use() {
        for url in [
            "https://example.test:7000",
            "HTTP://example.test:7000",
            "example.test:7000",
            "http://example.test",
            "http://example.test:0",
            "http://example.test:65536",
            "http://example.test:7000/v0",
            "http://example.test:7000/?q=1",
            "http://user@example.test:7000",
            "http://:7000",
            "http://example.test:7000#fragment",
        ] {
            assert!(validate_probe_url(url).is_err(), "{url}");
        }
    }
}
