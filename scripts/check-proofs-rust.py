#!/usr/bin/env python3
"""Verify proof files with the pinned leanVM Rust verifier, without changing the checkout.

Builds tests/rust/proof_check.rs in a temporary crate against the checkout's crates, offline,
and runs it on the given files (default: every tests/vectors/*.proof.gz). Exits nonzero unless
the verifier accepts every file.
"""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tomllib


ROOT = Path(__file__).resolve().parent.parent
PIN = "a386121f84292f6fa663aaa3e570c15bc0240ea2"
NAME = "proof-check"
CRATES = ("fiat_shamir", "lean_vm", "primitives")


def packages(lock: bytes) -> set[tuple]:
    """The packages a lock file pins, as (name, version, source, checksum)."""
    return {(p["name"], p["version"], p.get("source"), p.get("checksum"))
            for p in tomllib.loads(lock.decode())["package"]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("rust_checkout", type=Path)
    parser.add_argument("files", nargs="*", type=Path, help="proof files, plain or gzip")
    parser.add_argument("--target-dir", type=Path,
                        help="Cargo's target directory (default: the checkout's target/)")
    args = parser.parse_args()
    checkout = args.rust_checkout.resolve()
    head = subprocess.run(["git", "-C", str(checkout), "rev-parse", "HEAD"], check=True,
                          capture_output=True, text=True).stdout.strip()
    if head != PIN:
        raise SystemExit(f"leanVM checkout is at {head}, not the pin {PIN}")
    changed = subprocess.run(["git", "-C", str(checkout), "status", "--porcelain", "--",
                              "Cargo.toml", "Cargo.lock", "crates"], check=True,
                             capture_output=True, text=True).stdout
    if changed:
        raise SystemExit(f"leanVM checkout has local changes:\n{changed}")
    files = ([str(f) for f in args.files]
             or [os.path.relpath(f) for f in sorted((ROOT / "tests/vectors").glob("*.proof.gz"))])
    if not files:
        raise SystemExit("no proof files")
    target = (args.target_dir or checkout / "target").resolve()
    lock = (checkout / "Cargo.lock").read_bytes()
    with tempfile.TemporaryDirectory(prefix="leanervm-proof-check-") as directory:
        work = Path(directory)
        (work / "src").mkdir()
        shutil.copyfile(ROOT / "tests/rust/proof_check.rs", work / "src/main.rs")
        dependencies = "".join(f'{c} = {{ path = "{checkout / "crates" / c}" }}\n'
                               for c in CRATES)
        (work / "Cargo.toml").write_text(
            f'[package]\nname = "{NAME}"\nversion = "0.0.0"\nedition = "2024"\n\n'
            f"[dependencies]\n{dependencies}")
        # Cargo adds this crate to the copied lock and prunes what it does not use, so the lock
        # cannot be `--locked`; every package it keeps must be one the checkout's lock pins.
        (work / "Cargo.lock").write_bytes(lock)
        # Run from the temporary crate, outside the checkout's .cargo/config.toml (which sets
        # target-cpu=native), as scripts/dump-proof-rust.sh does, so its build artifacts serve.
        subprocess.run(["cargo", "build", "--release", "--offline", "--quiet",
                        "--target-dir", str(target)], cwd=work, check=True)
        extra = packages((work / "Cargo.lock").read_bytes()) - packages(lock)
        if {p for p in extra if p[0] != NAME}:
            raise SystemExit(f"the build resolved packages the checkout does not pin: {extra}")
    if (checkout / "Cargo.lock").read_bytes() != lock:
        raise SystemExit("The reference Cargo.lock changed")
    return subprocess.run([str(target / "release" / NAME), *files]).returncode


if __name__ == "__main__":
    sys.exit(main())
