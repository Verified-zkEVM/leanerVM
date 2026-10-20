# `leanvm-rust-verify`

The deployed Rust verifier of leanVM, `verifier::verify_execution` (`crates/verifier`, the
portable single-threaded verifier `leanvm_core::cpu::verify` calls), on the four files the
Python verifier's CLI reads: `bytecode.bin`, `public_input.bin`, `stream.bin` and
`merkle_openings.bin` (`python-verifier/verifier.py`, `main`; the format of
[`tests/fixtures/verifier`](../../tests/fixtures/verifier)). It decodes them as the Python's
`main` does and as `crates/leanvm_core/tests/verifiers/portable_verifier.rs` does
(`verifier::Proof::load`, `verifier::Bytecode::new`), so its verdicts can be set beside those of
the Lean verifier, `lake exe leanvm-verify` (`tests/VerifyFiles.lean`), on the same bytes.

The pin is leanVM `a0ca7858f2533ce51abdc20bb635c007e19b26b3`.

## Building

The crate depends on the `verifier` crate by path, through `leanvm`, a symbolic link to a leanVM
source tree at the pin. `build.sh` makes the link, checks that the tree's `crates/verifier` and
`python-verifier/verifier.py` hash to the pin's, and builds the release binary:

```sh
mkdir -p /path/to/leanvm-main
git -C /path/to/leanVM archive a0ca7858f2533ce51abdc20bb635c007e19b26b3 | tar -x -C /path/to/leanvm-main
scripts/rust-verifier-cli/build.sh /path/to/leanvm-main
```

The link and `target/` are ignored by Git. The `verifier` crate has no dependencies, so the
build is offline. The tree stays its own Cargo workspace (`exclude` in `Cargo.toml`), so the
crate inherits its edition and lints from there.

## Running

```sh
scripts/rust-verifier-cli/target/release/leanvm-rust-verify bytecode.bin public_input.bin stream.bin merkle_openings.bin
printf '%s\t%s\t%s\t%s\n' bytecode.bin public_input.bin stream.bin merkle_openings.bin \
  | scripts/rust-verifier-cli/target/release/leanvm-rust-verify --batch
```

A single run prints `verification succeeded` (exit 0), `verification failed: <reason>` (exit 1),
or `verification panicked: <message>` (exit 3). `--batch` reads one line of four tab-separated
paths per proof and prints one line per proof: `accept`, `reject <reason>` or `panic <message>`.

[`scripts/fuzz-verifier.py`](../fuzz-verifier.py) runs it and the Lean verifier on the fixtures
and on mutations of them, and fails on any verdict difference.
