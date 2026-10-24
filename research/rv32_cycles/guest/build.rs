fn main() {
    // Let the linker find link.x, and relink when it changes.
    println!("cargo:rustc-link-search={}", std::env::var("CARGO_MANIFEST_DIR").unwrap());
    println!("cargo:rerun-if-changed=link.x");
}
