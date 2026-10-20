# leanerVM

Read [`README.md`](README.md) first; each project's own `AGENTS.md` or `README.md` applies inside it.

- Four Lake projects, `lean_vm`, `lean_xmss`, `lean_sphincs` and `lean_da`, each built in its own directory; the root is no Lean project. `lake build` at the root (`check-all.sh`) is the full gate, as `.github/workflows/lean.yml` runs it.
- `lean_vm` is about leanVM at `leanvm-rev`. Run leanVM's Rust in `.leanvm/` (`./leanvm-tree.sh`), whose `formal/lean_vm` is a link to `lean_vm`: its `LEANVM_WRITE_*` tests write the Lean data here. Never edit `.leanvm/` itself; bump `leanvm-rev` instead.
- Generated data (`lean_vm/LeanVM/Guest/Data/`, `lean_vm/tests/LeanVMTests/Spec/NodeVectors.lean`, `lean_vm/tests/LeanVMTests/Guest/Programs.lean`) is regenerated, not edited: by leanVM's tests or by `lake exe guest-core` / `lake exe guest-cert`.
- No `sorry`, `axiom`, `admit`, `native_decide`, `implemented_by` or `unsafe`; every warning is an error. The axiom footprint of every end theorem is Lean's three.
- Builds are heavy. Cap `lean` and compiled executables with `ulimit -v`, not `lake` (it reserves about 1 GB of address space per job); throttle `lean_vm`'s build with `scripts/ci-build.py`.
- The Rust code reached through `.leanvm/` (Rust verifier, prover, guests) is test evidence, not proof; a proof claim cites leanVM sources at a named commit.
