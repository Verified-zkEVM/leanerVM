#!/usr/bin/env python3
"""Run source-pinned Rust regressions without changing the reference checkout."""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parent.parent
REVISION = "48a904208d682848dac0e18ef8b01ebfc40df9ad"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("rust_checkout", type=Path)
    parser.add_argument("--target-dir", type=Path,
                        default=Path(tempfile.gettempdir()) / "leanisa-rust-contract-target")
    args = parser.parse_args()
    checkout = args.rust_checkout.resolve()
    subprocess.run(["git", "-C", str(checkout), "cat-file", "-e", f"{REVISION}^{{commit}}"],
                   check=True)
    with tempfile.TemporaryDirectory(prefix="leanisa-rust-contracts-") as directory:
        work = Path(directory)
        archive = work / "source.tar"
        subprocess.run(["git", "-C", str(checkout), "archive", "--format=tar",
                        f"--output={archive}", REVISION], check=True)
        source = work / "source"
        source.mkdir()
        with tarfile.open(archive) as contents:
            contents.extractall(source, filter="data")
        lock = (source / "Cargo.lock").read_bytes()
        destination = source / "crates/lean_vm/src/cpu/leanisa_contracts.rs"
        shutil.copyfile(ROOT / "tests/rust/leanisa_contracts.rs", destination)
        # Test-only access to the actual private per-opcode rows; production Rust is unmodified.
        with (destination.parent / "mod.rs").open("a") as module:
            module.write("\n#[cfg(test)]\nmod leanisa_contracts;\n")
        exports = work / "exports"
        exports.mkdir()
        env = os.environ.copy()
        env["CARGO_TARGET_DIR"] = str(args.target_dir.resolve())
        env["LEANISA_EXPORT_DIR"] = str(exports)
        subprocess.run(["cargo", "test", "--release", "--locked", "--offline", "-p", "lean_vm",
                        "--lib", "--", "--test-threads=1"],
                       cwd=source, env=env, check=True)
        if (source / "Cargo.lock").read_bytes() != lock:
            raise SystemExit("The reference Cargo.lock changed")
        subprocess.run(["lake", "build", "LeanerVMTests.Semantics.RustExport"],
                       cwd=ROOT, check=True)
        for name in ("zero", "plain", "stale", "fillers"):
            print(f"Checking actual Rust export: {name}", flush=True)
            subprocess.run(["lake", "env", "lean", "-E", "warning",
                            str(exports / f"{name}.lean")], cwd=ROOT, check=True)
        print(f"Rust contracts passed at {REVISION}; repository lock preserved.")


if __name__ == "__main__":
    main()
