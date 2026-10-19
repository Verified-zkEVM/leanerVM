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
- The instruction tables of `doc/leanvm/body/07-instruction-tables.tex` place no condition on a
  row's `pc`, so a bytecode whose sentinel slot `g^(N_prog - 1)` holds a `JUMP` admits accepted
  walks that execute the sentinel, which §2 and `cpu/execute.rs` never do (the executor halts at
  the first arrival and asserts `fp = 1`). leanISA's constraint soundness therefore carries a
  well-formed-bytecode hypothesis (`WellFormedBytecode`, roadmap Layer 10); the compiler pads
  the sentinel with `SET_CONSTANT` (`crates/lean_compiler/src/lib.rs:162`), which satisfies it.
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

## Known discrepancies at the pin

What the proof system found where the specification (`doc/leanvm/body/`), the Rust (`crates/`)
and the Python verifier (`python-verifier/verifier.py`, written `py:`) differ, leave a fact to
the code, or carry a defect, at `a386121f`. Each entry has a name; where one binds a definition,
the [protocol blueprint](roadmap/protocol-blueprint.md) cites it by that name. The pinned tex is
the authority for the specification: the PDF `leanVM-b-2.pdf` predates it and must not be cited.
The leanISA roadmap's source findings are in [its status file](roadmap/leanisa-status.md). The
former code in parentheses is for reading older pull requests.

**The specification and its verifiers disagree.**

- *The public-input check.* §8.2 checks each limb, `c_ℓ = (1 + r)·w_{0,ℓ} + r·w_{1,ℓ}`; the Rust
  verifier, the Python verifier and the recursion guest check one equation on the words,
  `c_0 + y·c_1 = (1 + r)·w_0 + r·w_1`, and pool the scalars sent. Both are sound at `1/|E|`; the
  verifiers accept strictly more transcripts (`08-end-to-end-protocol.tex:29-33`;
  `lean_vm/src/cpu/mod.rs:750-755`, `py:1398-1400`, `rec_aggregation/guests/aggregate.py:1680-1683`).
  (F18)
- *One combiner more than GKR layers.* Both verifiers draw a combiner after the roots and after
  every layer, the last included and unused; §5.3 has one per layer (`05-arithmetization.tex:91`;
  `lean_vm/src/gkr.rs:369, 391, 423`, `py:435, 453`).
- *The normalized GKR round.* §5.3 does not state the layer sumcheck's round message. The
  verifiers run the normalized (Gruen) round: a cofactor of degree 4 with four coefficients on
  the wire, the constant one derived through the equality factor, and a layer check without the
  equality factor (`gkr.rs:399-404, 410-413`, `fiat_shamir/src/transcript.rs:297-302`,
  `py:411-413, 445, 449`). (S10, corrected)
- *The fingerprint bound.* The Rust charges `5·2^μ/|E|` where §5.2 proves `4·2^μ/|E|`
  (`lean_vm/src/leaf.rs:110`; `05-arithmetization.tex:37`).
- *Root order.* §8.5's prose names the count root first; the stream has the bus root first, and
  the push and pull roots are one scalar (`08-end-to-end-protocol.tex:68`; `gkr.rs:272-276,
  363-367`, `leaf.rs:890-894`). (F3, S11)
- *The announced rate.* The verifiers read the WHIR rate with the announced sizes
  (`cpu/mod.rs:123, 149`); §8.5's list of announced values does not match it
  (`08-end-to-end-protocol.tex:55`).
- *The seed.* §8.5 says the seed binds the R1CS matrices; the Rust binds `R1CS_DIGEST`, one
  constant naming the circuit, whose recipe needs matrices the pinned module no longer builds,
  and the Python and the guest copy its bytes (`cpu/mod.rs:66-93`, `flock/src/hash.rs:259-280`,
  `py:629`). (F14)
- *Setup and format checks the specification omits.* Both verifiers reject a nonzero upper limb
  in an announced size (`cpu/mod.rs:133-135`, `py:1373`), `τ_BLAKE2S < 3` (`cpu/mod.rs:162-166`,
  `py:861`), a rate outside `[1, 4]` (`cpu/mod.rs:167`, `py:1377`), a stack outside
  `μ ∈ [15, 28]` (`cpu/mod.rs:174-176`, `py:1379`), a nonzero third limb in a half of the
  commitment root (`fiat_shamir/src/merkle.rs:26-29`, `py:223`), and a stream not fully consumed
  (`cpu/mod.rs:769`, `transcript.rs:213-219`, `py:1414`); the Rust also requires `ζ` to have at
  least `τ_max` coordinates (`constraints.rs:250-253`). §8 states none of these. (F15)
- *The program in the Python verifier.* It takes the program as the stacked table and does not
  check that the unused slots are zero (`py:566, 857`).

**The specification leaves it to the code** (the blueprint transcribes these).

- *Fiat–Shamir.* §8.4 is `TODO`. The chain is BLAKE2s-256 of 64 bytes (the chain state and a
  block) with four numeric tags in lane 3 and no labels (`fiat_shamir/src/lib.rs:18-174`). (S6,
  F1)
- *Grinding.* Annex B does not mention it; every WHIR level grinds 17 bits before its queries,
  the nonce is bound even when the check fails, and `ood_samples[0] = 0`
  (`pcs/src/whir_config.rs:60`, `fiat_shamir/src/lib.rs:165-174`). (S12, F13)
- *Stack size and ties.* §4.1's `M = ⌈log₂ N⌉` has no floor or ceiling and no order for blocks of
  equal size; the verifiers floor at 15, reject above 28, and order ties by the column index, the
  six shared columns first (`04-committing-the-witness.tex:6-10`; `lean_vm/src/witness.rs:67-97`,
  `cpu/layout.rs:13-49`, `py:305-311, 890`). (S15, F17)
- *The table sumcheck.* Its target is derived, never sent; the three bus forms share the last
  three `ξ` powers; the round polynomial is a cubic of which three coefficients travel
  (`cpu/mod.rs:404-422, 728-735`, `constraints.rs:187-194, 267`, `transcript.rs:289-309`). §5.5
  charges `(ν_side + B)/|E|` for batching where its Corollary 3.9 gives one less, gives no error
  for the recycled zerocheck point, and does not say which coefficient is dropped
  (`05-arithmetization.tex:132, 155`; `03-proving-primitives.tex:67, 110`). (F4, F5, F6, F7)
- *The count tree* holds the tables' count columns only (`cpu/layout.rs:412-414`). (F11)
- *The opening batch.* Ring-switched claims take the low powers of `λ`
  (`pcs/src/stack_open.rs:400-401, 518-519`). (F8)
- *Flock's circuit and constants.* The BLAKE2s circuit and its wire positions, the slot of each
  of the eighteen limbs (`lean_vm/src/hash_flock.rs:87-115`), the selector of a limb claim
  (`pcs/src/stack_open.rs:84-97`), the fixed coordinate `g_0` (the hexadecimal expansion of π,
  `flock/src/zerocheck/univariate_skip_optimized.rs:104-106`), the embedding `φ_8` and the
  modulus of `GF(2^8)`, `k_batch = τ_BLAKE2S` and the floor `τ_BLAKE2S ≥ 3`
  (`cpu/mod.rs:162-166`, `py:1092-1095`) are in no annex. (F2)
- *No round-by-round analysis of the bus phase.* The specification's one round-by-round theorem
  is the opening's (Theorem B.7); the Rust asserts a coarse sum for the bus
  (`leaf.rs:108-118`), and its security accounting multiplies only the algebraic checks by the
  Johnson list size (`pcs/src/whir_config.rs:537-568`). (F16)
- *Lemma 5.2's proof* is `TODO` (`05-arithmetization.tex`). The specification numbers its
  equations (1) to (4) with no section prefix: the leaf decomposition is equation (2) of §5.4.
  (S9, S16)
- *The Rust verifier's rejection set* is four predicates plus truncations, with Flock's and
  WHIR's inside; structure checks on public data are `assert!`s (`leaf.rs:123-146`); the fill
  blocks make announced heights exact (`filler.rs:1-25`). (F10, F12)

**Defects of the Rust.**

- *The Flock prover's exceptional challenge.* The prover derives a coefficient through
  `(1 + r_eq)⁻¹` and at `r_eq = 1` emits a proof its own verifier rejects (probability at most
  `(k_batch + 1)/|E|` per proof). The specification's protocol is perfectly complete; no
  verifier inverts a challenge-dependent value (`flock/src/zerocheck.rs:116-118`).
- *Stale comments*: the table sumcheck's round message (`lean_vm/src/constraints.rs:24, 26,
  257-260, 265-266`); what binds Flock's counter and flags (`cpu/mod.rs:568-570, 619-620`,
  `flock/src/zerocheck.rs:389-390`, `lean_vm/src/hash_flock.rs:8-9`); level-0 grinding
  (`pcs/src/whir.rs:1364-1365, 1771-1772`; every level grinds 17 bits); the size of a WHIR Merkle
  leaf (`pcs/src/whir.rs:394-395`; 24 bytes a lane).

**The specification's analysis, checked by the proof.**

- *The fixed coordinates' independence.* Annex C's soundness argument applies
  `lem:fixed-zerocheck`, whose hypothesis is that the 128 weights `eq(a, b)` of the seven fixed
  coordinates are `F_2`-independent (`c-flock-protocol.tex:278`,
  `03-proving-primitives.tex:95-108`). The specification asserts it and the Rust tests it
  numerically (`flock/src/zerocheck/univariate_skip_optimized.rs:920`). It holds: Lean proves it
  from the constants (`fixedWeights_independent`).
- *Ring switching's error.* Annex A bounds the six coefficients together by Schwartz–Zippel, at
  total degree `2^31 + 2^15 + 2^7 + 8 + 2 + 1 < 2^32` (`a-ring-switching.tex:120-128`); the
  blueprint spreads that as `2^{2^{5−p}−1}/|E|` on `f_p`. Round by round, each coefficient costs
  `1/|E|`. If the `π`s of the slices' errors do not all vanish, one of them stays nonzero after a
  stage for every coefficient but one, since Frobenius is injective (`card_stage_zero_le_one`).
- *The constant position's error.* Annex C charges `k/|E|` for the constant position, checked at
  the random `χ_out` (`c-flock-protocol.tex:274`); the blueprint spreads that as `1/|E|` more on
  each batch round. Round by round it costs nothing: the constant position's track and a false
  claim are exclusive states, so a batch round costs `2/|E|`. The proved errors sum to
  `(3k + 169)/|E|`, against the slot's `(4k + 302 + 2^31 + 2^15)/|E|` (`sum_flockError_generic`).

**Not a discrepancy.** The Python verifier checks the caps (`16 ≤ log_mem ≤ 32`, every height at
most 32, `τ_BLAKE2S ≥ 3`, a power-of-two program: `py:856-864`, called at `py:1378`). The former
finding F9, that it omits them, was false.

## Obligation coverage at the baseline

“Present” means an implementation or prose specification exists in the current leanVM source
repository. “Machine checked” is reserved for a theorem checked by Lean or an equivalent proof
artifact; passing Rust/Python tests is not classified as a proof.

| Obligation | Existing evidence | Missing leanerVM result |
| --- | --- | --- |
| Guest functional correctness | zkDSL guest, Rust construction/API, positive and adversarial tests | T3: reviewed Lean guest specification and local postcondition; provisional T6 would supply recursive closure |
| Guest-to-ISA compilation | Rust zkDSL compiler and compiler regression/soundness tests | T3: certified compiler or proof for the exact emitted aggregation bytecode |
| ISA semantics | LaTeX specification and Rust interpreter; Lean `step`, `run`, and `ValidExecution` (`LeanerVM/Semantics/`) written from §2 and diffed arm by arm against `cpu/execute.rs` | T1 prerequisite: a formal correspondence boundary with the executor beyond the recorded diff |
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
