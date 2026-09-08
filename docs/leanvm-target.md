# leanVM target baseline

leanerVM targets [leanVM](https://github.com/leanEthereum/leanVM). Its default implementation now
uses binary fields and BLAKE2s; the historical KoalaBear/Poseidon implementation remains on the
`koalabear` branch. The audited baseline is commit
[`a386121f84292f6fa663aaa3e570c15bc0240ea2`](https://github.com/leanEthereum/leanVM/commit/a386121f84292f6fa663aaa3e570c15bc0240ea2)
on `main`, dated 2026-09-03. Source-faithful
definitions, fixtures, and implementation-correspondence claims must name this or a later
explicitly reviewed commit; `main` is only the drift-monitoring branch.

The audit also examined the local checkouts supplied for comparison:

| Checkout | Audited commit | Status in this project |
| --- | --- | --- |
| Historical local `leanVM` | `98cb2ad4bdc52618674c0f8f91f715a75349ff6f` | KoalaBear/Poseidon comparison, not the target |
| Transitional `leanVM-b` checkout | `f5d6e5040d666981005371742a6f21640ce865a1` | Earlier binary-field revision |
| Transitional `leanVM-b` upstream | `c701f62b0e05a48212febfae7ed5713a37d90392` | Previous target baseline |
| `leanVM` upstream `main` | `a386121f84292f6fa663aaa3e570c15bc0240ea2` | Current target baseline |

The historical local leanVM checkout was clean. The transitional local leanVM-b checkout contained
unrelated modified and untracked files; the comparison used committed objects only. The current
target was inspected in an isolated checkout. Upstream describes it as highly experimental, and
the newly promoted binary-field version is less stable and less tested than its predecessor. The
pin is a review boundary, not a maturity claim.

## Why the current default is a new target

The binary-field/Flock default is not merely a backend variant. Definitions from the historical
implementation cannot be ported without revalidation.

| Surface | Historical leanVM (`koalabear` branch) | Current leanVM (`main`) |
| --- | --- | --- |
| Arithmetic | KoalaBear prime field and degree-five extension | `K = GF(2^64)` and a 192-bit, three-limb extension `E` |
| Hash relation | Poseidon | BLAKE2s compression, including counter and finalization metadata |
| ISA/trace | Execution table plus Poseidon and extension-operation tables | Six opcode-specific tables: `XOR`, `MUL_NATIVE`, `SET_CONSTANT`, `DEREF`, `JUMP`, `BLAKE2S` |
| Memory | Base-field write-once words with integer-style addressing | `E`-valued write-once words addressed by powers of the generator in `K` |
| Bus | LogUp-style interactions in the older stack | One width-16 M3 bus, enforced by grand products and GKR, with nonzero access counts |
| Signature guest | XMSS single-message and multi-message APIs | One recursive guest for XMSS and SPHINCS claims |
| Recursion statement | Older single/multi-message aggregation layouts | Multiple XMSS epoch groups, each with one message, plus per-signer SPHINCS messages |
| Commitment/proof stack | WHIR, SuperSpartan/AIR, Poseidon commitments | Stacked WHIR/Ligerito, Flock for BLAKE2s, ring switching, and M3 arithmetization |

The older checkout remains useful for provenance and for identifying proof ideas, but it is not an
alternative semantic authority. In particular, no leanerVM theorem should retain the old
single-message/multi-message split, Poseidon parameters, KoalaBear encodings, or three-table trace
model unless it is explicitly labelled historical.

## Concrete target map

At the pinned revision:

- `doc/leanvm/body/02-vm-specification.tex` specifies the binary-field ISA. Program counter and
  frame pointer start at `1`; the first two memory cells hold the 256-bit public input using
  canonical two-limb embeddings in `E`.
- `crates/lean_vm/src/cpu/isa.rs` and `cpu/execute.rs` implement the six opcodes and executable
  write-once-memory behavior. Prover-supplied values enter through initially unset cells and must
  be bound by later reads and checks.
- `doc/leanvm/body/05-arithmetization.tex` through `08-end-to-end-protocol.tex`, together with
  `crates/lean_vm/src/`, define the tables, bus, witness/proof pipeline, statement binding, and
  Rust prover and verifier.
- `python-verifier/verifier.py` is a dependency-free second verifier. The Rust tests compare it
  with `lean_vm::cpu::verify`.
- `crates/lean_compiler/` compiles the Python-like zkDSL to the ISA. Its extensive tests are useful
  implementation evidence, but they are not a compiler-correctness proof.
- `crates/rec_aggregation/guests/aggregate.py` is the self-recursive verifier and signature guest.
  The public Rust surface is re-exported from root `src/lib.rs`; the implementation lives in
  `crates/rec_aggregation/src/aggregation.rs`.
- The public API in
  [`src/lib.rs`](https://github.com/leanEthereum/leanVM/blob/a386121f84292f6fa663aaa3e570c15bc0240ea2/src/lib.rs)
  uses one `aggregate` function and `AggregateSignature`; it has no
  `SingleMessage`/`MultiMessage` split. The pinned
  [`tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/a386121f84292f6fa663aaa3e570c15bc0240ea2/tests/api.rs)
  is the end-to-end usage example.
- Call `setup_prover` on a machine with enough memory for the process-wide arena. Use
  `setup_prover_without_arena` on a memory-constrained machine; it uses the system allocator and
  may be slower. `setup_verifier` is the verification-only initialization path.
- XMSS claims are grouped by strictly increasing epochs. Each non-empty group binds one message
  and a strictly sorted key list. SPHINCS claims are sorted, deduplicated `(key, message)` pairs.
  Raw signatures and child proofs populate group-specific write-once coverage regions.
- A child can map its XMSS groups into parent groups with the same epoch and message. Overlap is
  accounted for through duplicate slots; a published claim must still be covered.
- The guest is self-referential. Three evaluations that are too expensive in-circuit—stacked
  bytecode and Flock matrices `A0` and `B0`—are recursively batched as deferred claims and are
  discharged natively only by root `AggregateSignature::verify`.
- No public decreasing recursion-depth measure was found in the audited statement or
  `AggregateSignature` API. `MAX_RECURSIONS` bounds child arity, not depth, and the published
  signer claim need not strictly grow from child to parent. T6 therefore needs either a statement
  change or a separate, proved well-foundedness argument before recursive extraction can be
  claimed; finiteness must not be inferred from arity alone.
- The two-cell public input is a BLAKE2s digest binding the transcript environment, signer-set
  digest, and deferred claims. The bare Rust `verify()` validates the statement carried by the
  object; a consumer must separately compare the exposed signer lists with the statement it
  expected.
- `formal/xmss/` contains a separate VCVio-based Lean theorem
  `xmss_has_127_bits_of_classical_security`. It proves 127-bit classical random-oracle security
  for its reviewed scheme statement with only `propext`, `Classical.choice`, and `Quot.sound` in
  the reported axiom footprint. It does not by itself prove correspondence with the Rust XMSS
  implementation, the zkDSL guest, or the VM constraints. SPHINCS currently has a written
  specification but no corresponding Lean security formalization.

## Obligation coverage at the baseline

“Present” means an implementation or prose specification exists in the current leanVM source
repository. “Machine checked” is reserved for a theorem checked by Lean or an equivalent proof
artifact; passing Rust/Python tests is not classified as a proof.

| Obligation | Existing evidence | Missing leanerVM result |
| --- | --- | --- |
| Guest functional correctness | zkDSL guest, Rust construction/API, positive and adversarial tests | T3: reviewed Lean guest specification and local postcondition; provisional T6 would supply recursive closure |
| Guest-to-ISA compilation | Rust zkDSL compiler and compiler regression/soundness tests | T3: certified compiler or proof for the exact emitted aggregation bytecode |
| ISA semantics | LaTeX specification and Rust interpreter | T1 prerequisite: pure Lean step/run semantics and source-revision correspondence |
| Constraints imply ISA execution (CC-S) | Constraint/table implementation and design document | T1-S: refinement from every accepted assignment to an ISA trace |
| ISA execution yields constraints (CC-C) | Rust trace construction and honest-prover path | T1-C: satisfying-assignment existence for every in-scope execution |
| Witness-generator consistency (WC) | Executable fill/trace generation and mutation tests | T2: concrete generated assignment satisfies constraints and projects to its execution |
| Bus, lookup, and memory consistency (BC) | M3 bus construction and prose lemmas for count soundness | T1: multiset, range, count, table, bytecode, and memory composition theorem |
| Hint handling | Write-once design, guest checks, and hint-tampering tests | T1/T3: every claim-relevant hinted value is constrained or checked |
| BLAKE2s opcode | Rust implementations and Flock R1CS relation; Lean `compress` and `CompressCells` (`LeanerVM/Semantics/Blake2s.lean`) pinned by RFC 7693, `hashlib`, and executor vectors | T1 prerequisite: both constraint directions and implementation correspondence |
| Proof system | Protocol document with component bounds; Rust prover/verifier | T4: formal component notions, Fiat–Shamir assumptions, composed error bound, and verifier refinement |
| Verifier implementations | Rust, Python, and recursive zkDSL implementations; differential tests | T4/T5: each accepts exactly the specified protocol and statement encoding |
| Recursion and deferred claims | Self-recursive guest, native root discharge, end-to-end tests | T5 plus provisional T6: verifier-in-circuit equivalence, batching/root discharge, well-foundedness, and the unresolved inner-ROM/outer-topology extraction bridge |
| XMSS security | Existing machine-checked 127-bit ROM theorem in `formal/xmss/` | Port plus Rust/guest/spec correspondence and integration into T7's assumptions and claim |
| SPHINCS security | Prose specification and Rust implementation/tests | Security formalization and implementation/guest correspondence for T7 |
| Final audited claim | No single machine-checked end-to-end theorem | T7 soundness schema, conditional on the open recursion bridge, plus T8 completeness |

## Formalization order implied by the audit

1. Freeze the six-opcode encodings, `K`/`E` arithmetic, write-once memory, initial/final state, and
   two-cell public-input interpretation in `Semantics` and `Parameters`.
2. Build executable vectors from the pinned Rust interpreter, including malformed addresses,
   conflicting writes, branch behavior, BLAKE2s metadata, and hint-dependent programs.
3. Model the six tables and the bus before the full cryptographic protocol. Prove T1 and T2 from
   separately reviewable CC-S, CC-C, WC, and BC components.
4. Define the role-specific VM-compression, byte/Merkle, transcript, and application-hash
   interfaces, then instantiate them with leanVM's current exact BLAKE2s constructions. Connect the
   opcode, Flock relation, signature schemes, and optimized implementations to the appropriate
   specifications without treating another hash as a drop-in parameter.
5. Formalize the exact current aggregation statement and coverage algorithm, then establish T3
   for the emitted guest or its compiler boundary. Do not resurrect the historical aggregation
   API.
6. Port the existing XMSS security result only after reviewing its VCVio migration and its
   correspondence boundary; give SPHINCS its own explicitly scoped security track.
7. Establish T4 and T5 for protocol soundness, executable-verifier correspondence, recursive
   circuit correctness, and deferred-claim discharge. Develop the inner ROM and outer topology
   sides of provisional T6 separately. Expose T7 as conditional until a reviewed extraction
   bridge and well-foundedness result justify the concrete end-to-end theorem; T8 can proceed
   independently. See [architecture.md](architecture.md).
