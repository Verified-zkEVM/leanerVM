# leanerVM Agent Guide

Lean 4 implementation and formalization of leanVM semantics, arithmetization, proof-system
assembly, optimized execution, and implementation validation. Start with
[`README.md`](README.md) for the project overview and current status.

`AGENTS.md` is the canonical root guide for coding and proof agents working in this repository.

## Fast Start

1. Read [`CONTRIBUTING.md`](CONTRIBUTING.md) for source and review conventions, and read
   [`docs/architecture.md`](docs/architecture.md) before choosing a module or changing an import
   boundary.
2. Run `./scripts/validate.sh` before handoff. It is the complete local gate.
3. If you add, rename, or delete a file under `LeanerVM/`, update `LeanerVM.lean`. For a module
   under `tests/LeanerVMTests/`, update `tests/LeanerVMTests.lean`. Stage the changed paths and run
   validation; repository hygiene checks the Git index.
4. Before changing `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, or `upstreams.json`,
   read [`docs/dependencies.md`](docs/dependencies.md) and perform the required drift review.
5. Put executable and proof-regression coverage under `tests/`; run `lake test` for a focused
   check.

Useful focused commands:

```sh
lake build
lake test
lake env lean -E warning tests/Main.lean
./scripts/audit-lean.sh
./scripts/check-repository.sh
./scripts/check-imports.sh
./scripts/check-layers.sh
python3 ./scripts/check-docs.py
python3 ./scripts/test-policy-checks.py
```

## Where To Work

- `LeanerVM/Semantics/` — instruction set, state, memory, bytecode, transition relation, and
  pure executable interpreter.
- `LeanerVM/Parameters/` — versioned constants, encodings, layouts, and source bindings.
- `LeanerVM/Arithmetization/` — tables, buses, witness generation, constraints, and refinement
  to the VM semantics.
- `LeanerVM/Applications/` — guest specifications, exact programs, compiler boundaries, and
  application-level correctness results. Create this layer with its first concrete module.
- `LeanerVM/Protocol/` — leanVM-specific composition of reusable proof-system components.
- `tests/` — executable behavior, boundary cases, mutations, and proof regressions.
- `bench/` — benchmark contracts and reproducible workloads.
- `docs/` — durable architecture and operating knowledge.
- `scripts/` — deterministic validation and maintenance utilities.

The allowed production dependency flow is:

```text
Parameters ──→ Semantics ──→ Arithmetization ──→ Protocol
                         └──→ Applications ────────┘
```

## Lean and Proof Guardrails

- Lean defaults are `autoImplicit = false` and `relaxedAutoImplicit = false`.
- Use explicit, narrow imports and respect the layer DAG. Add every production module to the
  aggregate import in `LeanerVM.lean` exactly once.
- Files are Lean `module`s unless they import Clean, which is not a `module` at the pinned
  revision, or a file that does; `CONTRIBUTING.md` places that boundary and says what changes
  in a plain file. ArkLib is a `module` library and may be imported from either kind of file.
- ArkLib carries admitted theorems under its own baseline; a leanerVM declaration must not
  depend on one (the kernel axiom audit rejects `sorryAx`). Check with `#print axioms` before
  consuming an ArkLib theorem, and record what replaces an admitted one in the roadmap's ledger.
- Do not add `axiom`, `sorry`, `admit`, `unsafe`, or `native_decide` to accepted first-party
  Lean code. Do not override repository-wide linter or implicit-variable options in source.
- The first pull request that adds a production declaration must enable the prepared
  `lean-action` namespace axiom audit with `axiom-audit-root: LeanerVM`.
- Review every public theorem statement independently of whether its proof compiles. Check that
  assumptions, quantifiers, direction, error terms, and boundary cases match the intended claim.
- Classify major zkVM results using the obligation map in `docs/architecture.md`; state the
  artifact, soundness/completeness direction, implementation/reference boundary, and contribution
  to one or more of the T1–T8 target theorems. Use the concrete target map in
  [`docs/leanvm-target.md`](docs/leanvm-target.md); do not infer the current ISA or guest
  statement from the historical leanVM repository.
- Treat T6 recursion extraction and unconditional T7 soundness as open research targets. Keep
  inner ROM knowledge soundness separate from the conditional outer topology theorem, name every
  heuristic bridge explicitly, and do not introduce a global axiom to connect them.
- Give load-bearing configuration and certificate types concrete inhabitants. Add a mutation,
  counterexample, or negative test for the condition doing the real work.
- Prefer proofs that expose their mathematical structure and compose predictably. Use broad
  automation when it is fast and stable; when it is slow, first narrow imports, hypotheses,
  simp sets, or automation rules, or move a reusable lemma into its owner layer.
- Never weaken validation or silence warnings merely to land a change. Fix the source or make a
  tested, repository-wide policy proposal.

## Fidelity and Upstream Boundaries

- Bind semantic and implementation-correspondence claims to exact specification or implementation
  revisions. State whether a theorem describes deployed behavior or a proposed repair.
- Treat differential tests against pinned Rust leanVM as implementation evidence, not a proof of
  the Rust source. A proof claim needs an explicit formal correspondence boundary.
- Keep generic theory in its natural library: CompPoly for computable polynomial algorithms,
  ArkLib for oracle reductions and proof systems, VCVio for oracle computations and security
  carriers, and Clean for generic circuit/AIR/table infrastructure.
- Port reviewed mathematical ideas against current APIs; do not copy historical source trees.
  Preserve license notices and human attribution for substantially derived material.
- Add a third-party dependency only for a named first-party consumer and a narrow import. Update
  the toolchain, upstream baseline, and manifest together where applicable.
- Treat the Lean native/C executable as an implementation and performance target in its own
  right. Benchmark semantic changes on stable workloads when they affect execution.
- Native code is an implementation boundary, not proof evidence. Rust FFI, CUDA, and future
  domain-specific compilation require a pure Lean specification, ownership/error contract,
  differential tests, explicit trust boundary, and an isolated CI lane.

## Repository Hygiene

- Edit source files, not generated or local state such as `.lake/` and benchmark artifacts.
- Preserve unrelated work in a dirty tree; do not discard or rewrite changes you did not make.
- Keep stable operating knowledge in `docs/` and update the corresponding page when commands,
  structure, dependencies, or CI behavior change.
- Follow [`CONTRIBUTING.md`](CONTRIBUTING.md) for module structure, naming, docstrings, citations,
  attribution, and pull-request structure.

## Deeper Documentation

- [`docs/README.md`](docs/README.md) — documentation index.
- [`docs/architecture.md`](docs/architecture.md) — layer ownership and native-boundary criteria.
- [`docs/dependencies.md`](docs/dependencies.md) — pins, dependency roles, and update protocol.
- [`docs/leanvm-target.md`](docs/leanvm-target.md) — target source map and current proof gaps.
- [`docs/development.md`](docs/development.md) — validation and module workflow.
- [`docs/ci.md`](docs/ci.md) — workflow responsibilities and repository configuration.
- [`docs/roadmap/leanisa-blueprint.md`](docs/roadmap/leanisa-blueprint.md) — leanISA roadmap:
  scope, dependency contracts, the eleven layers, acceptance tests, and interfaces; tracked in
  issue #4.
- [`docs/roadmap/leanisa-status.md`](docs/roadmap/leanisa-status.md) — where the leanISA roadmap
  stands; rewritten whole when a layer lands.
- [`docs/roadmap/protocol-blueprint.md`](docs/roadmap/protocol-blueprint.md) — proof-system
  roadmap on ArkLib: the oracle protocol, its master theorems, the compiled verifier, the
  upstream ledger; tracked in issue #12.
- [`docs/roadmap/protocol-status.md`](docs/roadmap/protocol-status.md) — where the proof-system
  roadmap stands; rewritten whole when a layer lands.
- [`bench/README.md`](bench/README.md) — benchmark scope and interpretation.
