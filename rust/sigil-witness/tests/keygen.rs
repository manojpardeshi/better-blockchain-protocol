use std::process::Command;

fn keygen(path: &std::path::Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_sigil-witness"))
        .args(["keygen", "--out"])
        .arg(path)
        .output()
        .expect("run keygen")
}

#[test]
fn existing_key_and_public_file_are_never_replaced() {
    let d = std::env::temp_dir().join(format!(
        "sigil-keygen-{}-{}",
        std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    ));
    std::fs::create_dir(&d).unwrap();
    let key = d.join("w.json");
    let pub_file = d.join("w.pub");

    assert!(keygen(&key).status.success());
    let original_key = std::fs::read(&key).unwrap();
    let original_pub = std::fs::read(&pub_file).unwrap();
    let repeat = keygen(&key);
    assert!(!repeat.status.success());
    assert_eq!(std::fs::read(&key).unwrap(), original_key);
    assert_eq!(std::fs::read(&pub_file).unwrap(), original_pub);

    std::fs::remove_file(&pub_file).unwrap();
    let private_collision = keygen(&key);
    assert!(!private_collision.status.success());
    assert_eq!(std::fs::read(&key).unwrap(), original_key);
    assert!(!pub_file.exists());

    std::fs::remove_file(&key).unwrap();
    std::fs::write(&pub_file, &original_pub).unwrap();
    let collision = keygen(&key);
    assert!(!collision.status.success());
    assert!(String::from_utf8_lossy(&collision.stderr).contains("refusing to replace"));
    assert!(!key.exists());
    assert_eq!(std::fs::read(&pub_file).unwrap(), original_pub);

    std::fs::remove_dir_all(&d).unwrap();
}
