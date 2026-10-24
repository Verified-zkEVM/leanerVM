# leanerVM

Read [`README.md`](README.md) first, then the README of the project you work in.

## The repository

- Five Lake projects, `common`, `lean_vm`, `lean_xmss`, `lean_sphincs` and `lean_da`, each built in its own directory; the root is no Lean project. `lake build` at the root (`check-all.sh`) is the full gate, as `.github/workflows/lean.yml` runs it.
- `lean_vm` is about leanVM at `leanvm-rev`. Run leanVM's Rust in `.leanvm/` (`./leanvm-tree.sh`), whose `formal/lean_vm` is a link to `lean_vm`: Never edit `.leanvm/` itself; bump `leanvm-rev` instead.
- Generated data (`lean_vm/LeanVM/Guest/Data/`, `lean_vm/tests/LeanVMTests/Spec/NodeVectors.lean`, `lean_vm/tests/LeanVMTests/Guest/{Programs,Manifest}.lean`) is regenerated, not edited: by `lean_vm/scripts/guest-export` from leanVM's sources at the pin, or by `lake exe guest-core` / `lake exe guest-cert`.
- No `sorry`, `axiom`, `admit`, `native_decide`, `implemented_by` or `unsafe`, and no local overrides of a lakefile's options; every warning is an error, deprecations included. The axiom footprint of every end theorem is Lean's three.
- Builds are heavy: run them on a large machine, after `lake exe cache get`. Cap `lean` and compiled executables with `ulimit -v`, not `lake` (it reserves about 1 GB of address space per job).
- The Rust code reached through `.leanvm/` (Rust verifier, prover, guests) is test evidence, not proof; a proof claim cites leanVM sources at a named commit.
- `lean_da` is Benedikt Wagner's work (framework, theorems and proofs, from `b-wagn/fv-pq-da`), ported and instantiated with LeanDA: credit him in its files and in every commit that touches it.

## lean_vm

- `LeanVM/Spec/` is the trusted statement: it imports nothing from `LeanVM` outside it, and every change to it changes what is proved. Keep it a faithful transcription of the leanVM sources it cites (`verifier.py:N`, `*.rs:N`, `doc/leanvm` sections), at the commit it names.
- Speed comes from proved `@[csimp]` lemmas (`LeanVM/Spec/Fast/`).
- `lake build` builds every module under `LeanVM/` (the lakefile's globs), and `LeanVM.lean` pins the end theorems' axioms. `lake test` builds every module under `tests/LeanVMTests/`. Use `lake build <Module>` to check one module, not `lake env lean`.
- Lake has no job limit, so a cold parallel `lake build` can exceed a 16 GB machine. `python3 -I scripts/ci-build.py` builds a few modules at a time by import level (CI uses it). Keep a new module under about 3.5 GB.
- Differential tests compare with the Rust verifier, `scripts/fuzz-verifier.py` on `tests/fixtures/verifier` (the README says how), and with the Python verifier (`tests/LeanVMTests/Protocol/Verifier/Helpers.lean`, `Compiled.lean`). A protocol change in the Rust verifier fails CI until `Spec/Verifier.lean` and the proofs follow; regenerate the fixtures as the README says.
