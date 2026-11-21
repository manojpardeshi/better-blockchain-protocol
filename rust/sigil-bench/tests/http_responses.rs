use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::process::Command;
use std::time::{Duration, Instant};

use sigil_witness::crypto::KeyPair;
use sigil_witness::json::{parse, Json};
use sigil_witness::model::transition_id;
use sigil_witness::testkit::vote;

fn request(stream: TcpStream) -> (String, Vec<u8>, BufReader<TcpStream>) {
    let mut reader = BufReader::new(stream);
    let mut line = String::new();
    reader.read_line(&mut line).unwrap();
    let path = line.split_whitespace().nth(1).unwrap().to_string();
    let mut len = 0;
    loop {
        line.clear();
        reader.read_line(&mut line).unwrap();
        if line == "\r\n" {
            break;
        }
        if let Some(value) = line.to_ascii_lowercase().strip_prefix("content-length:") {
            len = value.trim().parse().unwrap();
        }
    }
    let mut body = vec![0; len];
    reader.read_exact(&mut body).unwrap();
    (path, body, reader)
}

fn respond(mut reader: BufReader<TcpStream>, body: &[u8]) {
    write!(reader.get_mut(), "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n", body.len()).unwrap();
    reader.get_mut().write_all(body).unwrap();
}

fn accept_with_timeout(listener: &TcpListener) -> TcpStream {
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        match listener.accept() {
            Ok((stream, _)) => return stream,
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock && Instant::now() < deadline => {
                std::thread::sleep(Duration::from_millis(10));
            }
            Err(e) => panic!("fake witness did not receive request: {e}"),
        }
    }
}

#[test]
fn http_load_counts_only_matching_votes() {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    listener.set_nonblocking(true).unwrap();
    let url = format!("http://{}", listener.local_addr().unwrap());
    let server = std::thread::spawn(move || {
        let key = KeyPair::from_py_seed(b"fake-bench-witness");
        for i in 0..5 {
            let (path, body, reader) = request(accept_with_timeout(&listener));
            if i == 0 {
                assert_eq!(path, "/v0/info");
                respond(reader, br#"{"ok":{"constellation":"c"}}"#);
                continue;
            }
            assert_eq!(path, "/v0/spend");
            let payload = parse(&body).unwrap();
            let req = payload.get("request").unwrap();
            let sigil = req.get("sigil").and_then(Json::as_str).unwrap();
            let tid = transition_id(req.get("header").unwrap());
            let response = match i {
                1 => format!(
                    "{{\"ok\":{}}}",
                    vote(&key, "c", sigil, 0, &tid, 1).canonical_string()
                ),
                2 => r#"{"error":"rejected","message":"no vote"}"#.to_string(),
                3 => "not JSON".to_string(),
                4 => format!(
                    "{{\"ok\":{}}}",
                    vote(&key, "c", sigil, 0, &"f".repeat(64), 1).canonical_string()
                ),
                _ => unreachable!(),
            };
            respond(reader, response.as_bytes());
        }
    });

    let output = Command::new(env!("CARGO_BIN_EXE_sigil-bench"))
        .args([
            "http",
            "--url",
            &url,
            "--n",
            "4",
            "--concurrency",
            "1",
            "--gen-threads",
            "1",
        ])
        .output()
        .unwrap();
    server.join().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result = parse(&output.stdout).unwrap();
    assert_eq!(result.get("n").and_then(Json::as_int), Some(4));
    assert_eq!(result.get("ok").and_then(Json::as_int), Some(1));
    assert_eq!(result.get("errors").and_then(Json::as_int), Some(3));
}
