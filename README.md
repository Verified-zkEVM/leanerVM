# leanerVM

`leanerVM` is a Lean 4 implementation and formalization of
[leanVM](https://github.com/leanEthereum/leanVM), leanEthereum's minimal hash-based SNARK virtual
machine for post-quantum signature aggregation. Current leanVM uses binary fields and BLAKE2s;
the historical KoalaBear/Poseidon implementation remains available on its `koalabear` branch.

The primary application target is leanVM's recursive XMSS and SPHINCS aggregation guest. At
the pinned revision, XMSS claims are grouped by epoch with one message per group, while each
SPHINCS claim carries its own message. The final result must be bound to that exact guest and
imply the intended claim about every published key, message, epoch, and signature.

The executable Lean semantics serves three complementary purposes: it anchors proofs from VM
execution through the proof system, provides an implementation worth optimizing in its own
right, and supplies an independent reference for validating the existing Rust implementation.
That validation begins with differential testing against pinned Rust revisions and may grow into
formal verification of the relevant Rust code.

## Project status

The project is in **Phase 0: repository baseline**. The Lean module boundaries, executable test
driver, validation policy, CI, and dependency tracking are in place. VM semantics and proof
claims have not landed yet.

Recursive CTE is an open research problem: the intended knowledge-soundness arguments for the
concrete inner SNARKs live in the random-oracle model, while the known outer recursion-topology
argument requires an extraction interface that is not presently justified by such inner results.
The architecture keeps the desired final theorem as a target schema and does not claim that this
bridge has been solved.

## Assurance goals

- Give leanVM a pure executable semantics for its six-opcode instruction set, binary-field
  machine state, write-once memory, and halting behavior.
- Prove that valid arithmetized traces correspond to executions of those semantics, including
  the converse obligations needed by the intended correctness statement.
- Compose those results through witness generation, guest correctness, the base proof system,
  and recursion into versioned end-to-end soundness and completeness theorems.
- Assemble leanVM-specific protocols from reusable, reviewed components in ArkLib, VCVio,
  CompPoly, and Clean.
- Validate versioned Rust leanVM behavior with shared vectors and differential execution tests;
  pursue a proved Rust correspondence when an appropriate verification boundary is available.
- Bind constants, encodings, layouts, and challenge schedules to exact source revisions.
- State deployment gaps and cryptographic assumptions explicitly, with inhabited examples and
  negative controls for load-bearing definitions.
- Establish reproducible performance baselines and improve execution through Lean's native C
  code-generation path, specified Rust or CUDA FFI kernels, and a future domain-specific
  compiler.

Compilation is only one part of acceptance. Public theorem statements, assumptions, trust
closure, non-vacuity, and correspondence with the referenced implementation are reviewed as
part of the deliverable.

## Execution and performance

The pure Lean implementation is the semantic reference, not merely a testing oracle for Rust.
The project will measure and improve the executable produced by Lean's native C backend, while
retaining the same observable VM behavior. Where profiling justifies specialized kernels, fast
Rust or CUDA implementations may be connected through narrow FFI boundaries and checked against
the Lean reference on shared workloads.

A future domain-specific compiler can provide a more specialized execution path. Its source
language, target behavior, and preservation theorem must be explicit: generated code becomes
part of the trusted result only to the extent justified by those proofs and the documented
compiler/runtime assumptions.

## Getting started

Install [elan](https://github.com/leanprover/elan), then clone the repository and run:

```sh
./scripts/validate.sh
```

The repository is pinned by [`lean-toolchain`](lean-toolchain) to Lean `v4.33.1`. The complete
validation command checks source policy, imports, architectural dependencies, documentation,
the timing helper, the Lean build, and executable tests.

Useful focused commands are:

```sh
lake build --wfail
lake test
lake env lean -E warning tests/Main.lean
./scripts/audit-lean.sh
./scripts/check-imports.sh
./scripts/check-layers.sh
```

See [CONTRIBUTING.md](CONTRIBUTING.md) for code style, theorem review, testing, attribution,
and pull-request requirements.

## Architecture

```text
Parameters ──→ Semantics ──→ Arithmetization ──→ Protocol
                         └──→ Applications ────────┘
```

An arrow points from a foundational layer to a layer that may depend on it.
[`scripts/check-layers.sh`](scripts/check-layers.sh) enforces the forbidden reverse edges.

| Layer | Responsibility |
| --- | --- |
| `LeanerVM/Semantics/` | ISA, state, memory, bytecode, transition relation, and executable interpreter |
| `LeanerVM/Parameters/` | Versioned constants, encodings, layouts, and authoritative source bindings |
| `LeanerVM/Arithmetization/` | Tables, buses, witness generation, constraints, and semantic refinement |
| `LeanerVM/Applications/` | Guest specifications, exact programs, compiler boundaries, and application correctness |
| `LeanerVM/Protocol/` | leanVM-specific composition of polynomial, oracle, commitment, and proof-system components |

The detailed ownership and dependency rules are in
[docs/architecture.md](docs/architecture.md).

## Repository map

| Path | Contents |
| --- | --- |
| [`LeanerVM/`](LeanerVM/) | Production Lean library |
| [`LeanerVM.lean`](LeanerVM.lean) | Aggregate public import surface |
| [`tests/`](tests/) | Executable examples and proof-regression tests |
| [`bench/`](bench/) | Benchmark contracts and reproducible workloads |
| [`docs/`](docs/) | Architecture, dependencies, development, and CI documentation |
| [`scripts/`](scripts/) | Validation, repository checks, drift reporting, and timing tools |
| [`.github/workflows/`](.github/workflows/) | Build, policy, review, benchmark, and maintenance automation |

## Dependencies

Lean and library versions are tracked centrally rather than through floating branches.
[`docs/dependencies.md`](docs/dependencies.md) defines the update and review policy, while
[`upstreams.json`](upstreams.json) provides the machine-readable release baseline.
The audited target, its relationship to the original leanVM implementation, and the current
formalization gaps are recorded in
[`docs/leanvm-target.md`](docs/leanvm-target.md).

Reusable results should live in their natural upstream library:

- [ArkLib](https://github.com/Verified-zkEVM/ArkLib) for generic proof systems and oracle
  reductions;
- [VCVio](https://github.com/Verified-zkEVM/VCV-io) for oracle computations and cryptographic
  security definitions;
- [CompPoly](https://github.com/Verified-zkEVM/CompPoly) for computable polynomial and field
  infrastructure; and
- [Clean](https://github.com/Verified-zkEVM/clean) for circuit, AIR, table, and witness-generation
  infrastructure.

leanerVM owns the machine semantics, executable implementation, concrete parameters, leanVM
arithmetization instances, application specifications, protocol assembly,
implementation-validation boundary, and optimized execution paths specific to leanVM.

## Testing and automation

`lake test` runs the executable Lean test driver in [`tests/Main.lean`](tests/Main.lean), which
imports the complete [`LeanerVMTests.lean`](tests/LeanerVMTests.lean) test library. Tests for
semantics should cover successful executions, boundaries, and malformed inputs. Constraint work
should include witness mutations that demonstrate rejection, and implementation-validation work
should include differential vectors tied to authoritative Rust source revisions.
Differential agreement is regression evidence; it is not presented as a proof about the Rust
source.

CI keeps build/tests, repository policy, import layering, and documentation integrity as
independent required checks. It also provides automated PR summaries, member-triggered review,
upstream release tracking, and informational build timing. Project releases follow reviewed
milestones rather than Lean toolchain updates. The benchmark job records clean-build, warm-build,
and test-path wall/user/system time with JSONL records and logs. See
[docs/ci.md](docs/ci.md) and [bench/README.md](bench/README.md).

## License

leanerVM is licensed under the Apache License 2.0. See [LICENSE](LICENSE).
