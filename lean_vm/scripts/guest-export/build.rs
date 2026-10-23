//! The overlay: leanVM's `rec_aggregation` sources, copied verbatim into `OUT_DIR` (the guest
//! with them, so their `include_str!("../guests/lean_ethereum.py")` still resolves), with one
//! line appended to `aggregation.rs` that declares this crate's `src/export/` as its child
//! module `lean_export`. Nothing under `.leanvm/` is written.

use std::path::{Path, PathBuf};

/// leanVM's checkout, relative to this crate: the one `../../../leanvm-tree.sh` makes. `LEANVM_DIR`
/// overrides it.
const DEFAULT_LEANVM: &str = "../../../.leanvm";

fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for entry in std::fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.is_file() {
            println!("cargo:rerun-if-changed={}", path.display());
            std::fs::copy(&path, to.join(entry.file_name())).unwrap();
        }
    }
}

fn main() {
    println!("cargo:rerun-if-env-changed=LEANVM_DIR");
    println!("cargo:rerun-if-changed=build.rs");
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let leanvm = std::env::var("LEANVM_DIR").map(PathBuf::from).unwrap_or_else(|_| manifest.join(DEFAULT_LEANVM));
    let leanvm = leanvm
        .canonicalize()
        .unwrap_or_else(|e| panic!("leanVM's checkout {}: {e}; run leanvm-tree.sh", leanvm.display()));
    let crate_dir = leanvm.join("crates/rec_aggregation");
    let out = PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("rec_aggregation");
    copy_dir(&crate_dir.join("src"), &out.join("src"));
    copy_dir(&crate_dir.join("guests"), &out.join("guests"));

    let export = manifest.join("src/export/mod.rs");
    let aggregation = out.join("src/aggregation.rs");
    let mut text = std::fs::read_to_string(&aggregation).unwrap();
    text.push_str(&format!(
        "\n// Appended by leanvm-guest-export's build.rs.\n#[path = {:?}]\npub mod lean_export;\n",
        export.display().to_string()
    ));
    std::fs::write(&aggregation, text).unwrap();

    // The leanVM checkout and commit the data is exported from, for the generated headers.
    let rev = std::process::Command::new("git")
        .args(["-C", &leanvm.display().to_string(), "rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".into());
    println!("cargo:rustc-env=LEANVM_REV={rev}");
    println!("cargo:rustc-env=LEANVM_DIR={}", leanvm.display());

    let overlay = format!(
        "#[path = {:?}]\npub mod aggregation;\n\n#[cfg(feature = \"signers-cache\")]\n#[path = {:?}]\npub mod signers_cache;\n",
        aggregation.display().to_string(),
        out.join("src/signers_cache.rs").display().to_string()
    );
    std::fs::write(out.join("overlay.rs"), overlay).unwrap();
}
