# leanerVM

Read [`README.md`](README.md) first, then the README of the project you work in.

## The repository

- Six Lake projects, each built in its own directory: `Statement` (the statement: definitions and end statements only), and the proofs, `common`, `lean_vm`, `lean_xmss`, `lean_sphincs` and `lean_da`; the root is no Lean project. `lake build` at the root (`check-all.sh`) is the full gate, as `.github/workflows/lean.yml` runs it.
- Name a project `lean_*` (or a library `Lean*`) only for a deployed object (leanVM, leanXMSS, leanSPHINCS, LeanDA); infrastructure is named for what it is (`common`, `Statement`).
- `lean_vm` is about leanVM at `leanvm-rev`. Run leanVM's Rust in `.leanvm/` (`./leanvm-tree.sh`), whose `formal/lean_vm` is a link to `lean_vm`: Never edit `.leanvm/` itself; bump `leanvm-rev` instead.
- Generated data (`Statement/Data/`, `lean_vm/LeanVM/Guest/Data/`, `lean_vm/tests/LeanVMTests/Spec/NodeVectors.lean`, `lean_vm/tests/LeanVMTests/Guest/{Programs,Manifest}.lean`) is regenerated, not edited: by `lean_vm/scripts/guest-export` from leanVM's sources at the pin, or by `lake exe guest-core` / `lake exe guest-cert`.
- No `sorry`, `axiom`, `admit`, `native_decide`, `implemented_by` or `unsafe`, and no local overrides of a lakefile's options (one exception: `lake-build.py --dev`, below); every warning is an error, deprecations included. The axiom footprint of every end theorem is Lean's three.
- Builds are heavy: run them on a large machine, after `lake exe cache get`. Cap `lean` and compiled executables with `ulimit -v`, not `lake` (it reserves about 1 GB of address space per job).
- The Rust code reached through `.leanvm/` (Rust verifier, prover, guests) is test evidence, not proof; a proof claim cites leanVM sources at a named commit.
- `lean_da` is Benedikt Wagner's work (framework, theorems and proofs, from `b-wagn/fv-pq-da`), ported and instantiated with LeanDA: credit him in its files and in every commit that touches it.

## Statement

- `Statement/` is the trusted statement: ten files (`Statement/README.md` lists them in reading order), the generated guest bytecode (`Statement/Data/`), and proved `@[csimp]` lemmas for speed only (`Statement/Fast/`, not part of what a reviewer reads). It imports only Mathlib, VCVio, CompPoly and its own files (CI checks it), and every change to it changes what is proved. No file beyond the ten without asking. Definitions and end statements only: a proof belongs to the proof projects, unless a definition needs it (a structure's law, a decidability instance).
- Keep the leanVM definitions a faithful transcription of the leanVM sources they cite (`verifier.py:N`, `*.rs:N`, `doc/leanvm` sections), at the commit they name.
- Only statements in the random-permutation model are end statements; the random-oracle model and the sponge's indifferentiability are proof steps, in the proof projects.
- Each proof project's root module is its end file: it checks each end theorem against its `Statement` proposition and pins its axioms.

## lean_vm

- Speed comes from proved `@[csimp]` lemmas (`Statement/Fast/`: a `@[csimp]` lemma acts where a definition is compiled, so the statement's own definitions must see them); lemmas about the statement's definitions are in `LeanVM/Facts/`.
- `lake build` builds every module under `LeanVM/` (the lakefile's globs), and `LeanVM.lean` pins the end theorems' axioms. `lake test` builds every module under `tests/LeanVMTests/`. Use `lake build <Module>` to check one module, not `lake env lean`.
- Lake has no job limit, so a cold parallel `lake build` can exceed a 16 GB machine. `python3 -I ../lake-build.py . LeanVM LeanVMTests` runs one `lake build` whose modules, the statement package's included, it admits by their recorded memory, the cores busy (CI uses it; `lake-build.tsv` holds the heavy modules, `--seed` rewrites it). Keep a new module under about 3.5 GB.
- `lake-build.py --dev` is for development only: it builds into `.lake/build-dev` with the kernel skipped (`debug.skipKernelTC`) on `LeanVM` (its dependencies, `Statement` among them, are built as usual), about 10x faster. Elaboration still checks ordinary proofs, but a false `decide +kernel` passes and `#print axioms` does not show it. Never use it for CI, a gate, a push or a claim: those run the build above, kernel included.
- Differential tests compare with the Rust verifier, `scripts/fuzz-verifier.py` on `tests/fixtures/verifier` (the README says how), and with the Python verifier (`tests/LeanVMTests/Protocol/Verifier/Helpers.lean`, `Compiled.lean`). A protocol change in the Rust verifier fails CI until `Statement/LeanVmVerifier.lean` and the proofs follow; regenerate the fixtures as the README says.
