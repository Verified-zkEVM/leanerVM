#!/usr/bin/env bash
# Build `leanvm-rust-verify` (src/main.rs) against a leanVM source tree at the pin: link the tree
# as `leanvm`, check that its `crates/verifier` and `python-verifier/verifier.py` are the pin's,
# and build the release binary, target/release/leanvm-rust-verify.
#
# Usage: scripts/rust-verifier-cli/build.sh <leanVM source tree at the pin>
#
# The tree is a git checkout at the pin or an export of it
# (`git -C <leanVM> archive <pin> | tar -x -C <dir>`). Requires `cargo` (Rust 1.88 or later,
# edition 2024).
set -euo pipefail

pin="a0ca7858f2533ce51abdc20bb635c007e19b26b3"
# sha256 of `python-verifier/verifier.py` and of the sorted sha256 list of `crates/verifier`'s
# files at the pin (`find crates/verifier -type f | sort | xargs sha256sum | sha256sum`).
python_sha256="ecce66e3d87d84fc9f5a65426982e1afba5128769abd449165b36288fd1da1af"
crate_sha256="d499c378084a6fef7af4c342c0eecece3b9d8eda5714c7e4a4499d9933b988e6"

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
tree="$(cd "${1:?usage: $0 <leanVM source tree at the pin>}" && pwd)"

actual="$(sha256sum "$tree/python-verifier/verifier.py" | cut -d' ' -f1)"
if [[ "$actual" != "$python_sha256" ]]; then
  echo "$tree/python-verifier/verifier.py is not the pin $pin's (sha256 $actual)" >&2
  exit 1
fi
actual="$(cd "$tree" && find crates/verifier -type f | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -d' ' -f1)"
if [[ "$actual" != "$crate_sha256" ]]; then
  echo "$tree/crates/verifier is not the pin $pin's (sha256 $actual)" >&2
  exit 1
fi

ln -sfn "$tree" "$here/leanvm"
cargo build --quiet --release --manifest-path "$here/Cargo.toml"
echo "$here/target/release/leanvm-rust-verify"
