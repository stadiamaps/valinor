use std::io::Result;

fn main() -> Result<()> {
    assert!(
        !(cfg!(feature = "protoc-from-src") && cfg!(feature = "protoc-vendored")),
        "It looks like you've enabled both protoc-from-src and protoc-vendored at the same time. You probably want to pick just one.\n\n(Hint: did you forget to add default-features = false in your Cargo.toml?)"
    );

    println!("cargo:rerun-if-env-changed=PROTOC");
    let mut config = prost_build::Config::new();

    #[cfg(feature = "protoc-from-src")]
    config.protoc_executable(protobuf_src::protoc());

    #[cfg(feature = "protoc-vendored")]
    match protoc_bin_vendored::protoc_bin_path() {
        Ok(path) => {
            config.protoc_executable(path);
        }
        Err(err) => println!(
            "cargo:warning=vendored protoc unavailable ({err}); using PROTOC or protoc on PATH"
        ),
    }
    config.compile_protos(&["proto/api.proto"], &["proto/"])?;
    Ok(())
}
