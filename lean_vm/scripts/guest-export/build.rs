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
        } else if path.is_dir() {
            copy_dir(&path, &to.join(entry.file_name()));
        }
    }
}

/// Every `.rs` file under `dir`.
fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
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
    // A fresh copy: a file leanVM moved or removed must not linger from an earlier pin.
    let _ = std::fs::remove_dir_all(&out);
    copy_dir(&crate_dir.join("src"), &out.join("src"));
    copy_dir(&crate_dir.join("guests"), &out.join("guests"));

    let export = manifest.join("src/export/mod.rs");
    // `aggregation` is a directory module (`aggregation/mod.rs`) since leanVM #670.
    let aggregation = [out.join("src/aggregation/mod.rs"), out.join("src/aggregation.rs")]
        .into_iter()
        .find(|p| p.is_file())
        .expect("rec_aggregation has an aggregation module");
    // Since #670 the module's private items live in its submodules: the exporters, a child of
    // `aggregation`, read them as they read `aggregation.rs`'s, so every top-level item there is
    // made crate-visible (only the copy; the module's own `pub` items are unchanged).
    if aggregation.ends_with("mod.rs") {
        let mut files = Vec::new();
        rust_files(aggregation.parent().unwrap(), &mut files);
        for f in files.iter().filter(|f| **f != aggregation) {
            let text = std::fs::read_to_string(f).unwrap();
            let text: String = text
                .lines()
                .map(|l| {
                    let item = ["fn ", "struct ", "enum ", "const ", "type ", "static ", "trait ", "mod "]
                        .iter()
                        .any(|k| l.starts_with(k))
                        && !l.starts_with("const _");
                    let l = l.replacen("pub(super) ", "pub(crate) ", 1);
                    if item { format!("pub(crate) {l}\n") } else { format!("{l}\n") }
                })
                .collect();
            std::fs::write(f, text).unwrap();
        }
    }
    let mut text = std::fs::read_to_string(&aggregation).unwrap();
    text.push_str(&format!(
        "\n// Appended by leanvm-guest-export's build.rs.\n#[path = {:?}]\npub mod lean_export;\n",
        export.display().to_string()
    ));
    std::fs::write(&aggregation, text).unwrap();

    // leanVM's `lean_compiler` as this crate's module `compiler_overlay`, for the exporters that
    // read the parsed guest (`Ast`'s functions are crate-private since leanVM #669): its sources
    // copied, `lib.rs` as the module's `mod.rs`, and `crate::` paths pointed at the module.
    let compiler = PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("compiler_overlay");
    let _ = std::fs::remove_dir_all(&compiler);
    copy_dir(&leanvm.join("crates/lean_compiler/src"), &compiler);
    std::fs::rename(compiler.join("lib.rs"), compiler.join("mod.rs")).unwrap();
    let mut files = Vec::new();
    rust_files(&compiler, &mut files);
    for f in files {
        let text = std::fs::read_to_string(&f).unwrap();
        std::fs::write(&f, text.replace("crate::", "crate::compiler_overlay::")).unwrap();
    }

    // The leanVM checkout and commit the data is exported from, for the generated headers.
    let rev = std::process::Command::new("git")
        .args(["-C", &leanvm.display().to_string(), "rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".into());
    println!("cargo:rustc-env=LEANVM_REV={rev}");
    // A new pin with unchanged sources must still rebuild, or the headers keep the old commit.
    println!("cargo:rerun-if-changed={}", manifest.join("../../../leanvm-rev").display());
    println!("cargo:rustc-env=LEANVM_DIR={}", leanvm.display());

    let overlay = format!(
        "#[path = {:?}]\npub mod aggregation;\n\n#[cfg(feature = \"signers-cache\")]\n#[path = {:?}]\npub mod signers_cache;\n\n#[path = {:?}]\npub mod compiler_overlay;\n",
        aggregation.display().to_string(),
        out.join("src/signers_cache.rs").display().to_string(),
        compiler.join("mod.rs").display().to_string()
    );
    std::fs::write(out.join("overlay.rs"), overlay).unwrap();
}
