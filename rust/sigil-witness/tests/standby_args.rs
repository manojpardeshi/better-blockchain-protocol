use std::process::Command;

#[test]
fn standby_rejects_unsupported_member_url_before_opening_files() {
    let out = Command::new(env!("CARGO_BIN_EXE_sigil-witness"))
        .args([
            "standby",
            "--key",
            "does-not-exist.key",
            "--registry",
            "does-not-exist.registry",
            "--constellation",
            "example",
            "--store",
            "does-not-exist.redb",
            "--members",
            "https://example.test:7000",
        ])
        .output()
        .expect("run standby");
    assert!(!out.status.success());
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(stderr.contains("--members: member URL 1:"), "{stderr}");
    assert!(stderr.contains("only http:// URLs"), "{stderr}");
    assert!(!stderr.contains("does-not-exist.key:"), "{stderr}");
}
