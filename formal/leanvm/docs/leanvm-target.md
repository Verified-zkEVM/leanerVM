# leanVM target baseline

leanerVM targets [leanVM](https://github.com/leanEthereum/leanVM). Its default implementation now
uses binary fields and BLAKE2s; the historical KoalaBear/Poseidon implementation remains on the
`koalabear` branch. The audited baseline is commit
[`a0ca7858f2533ce51abdc20bb635c007e19b26b3`](https://github.com/leanEthereum/leanVM/commit/a0ca7858f2533ce51abdc20bb635c007e19b26b3)
on `main`, dated 2026-10-17, one commit after `127510d14c98ade4e8a97646c44fa7f1ff5e752d` (2026-10-15), which changes only the
aggregation guest; the verifier, the Python and the specification are those of `127510d1`, and
citations of them name it. It was the last external pin: the project now lives in leanVM, under
`formal/leanvm`, and targets the containing commit, the scripts reading the leanVM tree they sit
in. The baselines before, and what changed between them, are reviewed in
[dependencies.md](dependencies.md). Source-faithful definitions, fixtures, and
implementation-correspondence claims must name this or a later explicitly reviewed commit.

The audit also examined the local checkouts supplied for comparison:

| Checkout | Audited commit | Status in this project |
| --- | --- | --- |
| Historical local `leanVM` | `98cb2ad4bdc52618674c0f8f91f715a75349ff6f` | KoalaBear/Poseidon comparison, not the target |
| Transitional `leanVM-b` checkout | `f5d6e5040d666981005371742a6f21640ce865a1` | Earlier binary-field revision |
| Transitional `leanVM-b` upstream | `c701f62b0e05a48212febfae7ed5713a37d90392` | Earlier target baseline |
| `leanVM` upstream `main` | `a386121f84292f6fa663aaa3e570c15bc0240ea2` | Previous target baseline |
| `leanVM` upstream `main` | `a0ca7858f2533ce51abdc20bb635c007e19b26b3` | Last external pin; the target is now the containing commit |

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
- `crates/leanvm_core/src/cpu/isa.rs` and `cpu/execute.rs` implement the six opcodes and executable
  write-once-memory behavior. Prover-supplied values enter through initially unset cells and must
  be bound by later reads and checks.
- The instruction tables of `doc/leanvm/body/07-instruction-tables.tex` place no condition on a
  row's `pc`, so a bytecode whose sentinel slot `g^(N_prog - 1)` holds a `JUMP` admits accepted
  walks that execute the sentinel, which §2 and `cpu/execute.rs` never do (the executor halts at
  the first arrival and rejects a frame other than `main`'s, `Fault::HaltOutsideMain`,
  `crates/leanvm_core/src/cpu/execute.rs:452-461`; it asserted `fp = 1` at `a386121f`).
  leanISA's constraint soundness therefore carries a well-formed-bytecode hypothesis
  (`WellFormedBytecode`, roadmap Layer 10); the compiler pads the sentinel with `SET_CONSTANT`
  (`crates/lean_compiler/src/lib.rs:194`), which satisfies it.
- `doc/leanvm/body/05-arithmetization.tex` through `08-end-to-end-protocol.tex`, together with
  `crates/leanvm_core/src/`, define the tables, bus, witness/proof pipeline, statement binding,
  and Rust prover. The Rust verifier is the self-contained crate `crates/verifier/src/`, a port
  of the Python verifier (8c31abd7); `leanvm_core::cpu::verify` only builds its inputs
  (`crates/leanvm_core/src/cpu/mod.rs:685-698`).
- `python-verifier/verifier.py` is a dependency-free second verifier. The Rust tests run it and
  the `verifier` crate on the proofs of `leanvm_core::cpu::prove`
  (`crates/leanvm_core/tests/verifiers/python_verifier.rs`, `portable_verifier.rs`).
- `crates/lean_compiler/` compiles the Python-like zkDSL to the ISA. Its extensive tests are useful
  implementation evidence, but they are not a compiler-correctness proof.
- `crates/rec_aggregation/guests/lean_ethereum.py` is the self-recursive verifier and signature
  guest; it also publishes a possibly empty list of LeanDA roots. The public Rust surface is
  re-exported from `crates/leanvm/src/lib.rs`; the implementation lives in
  `crates/rec_aggregation/src/aggregation.rs`. (At `a386121f` the guest was
  `crates/rec_aggregation/guests/aggregate.py` and the surface was root `src/lib.rs`.)
- The public API in
  [`crates/leanvm/src/lib.rs`](https://github.com/leanEthereum/leanVM/blob/127510d14c98ade4e8a97646c44fa7f1ff5e752d/crates/leanvm/src/lib.rs)
  uses one `aggregate` function and `EthereumProof` (`AggregateSignature` at `a386121f`); it has
  no `SingleMessage`/`MultiMessage` split. The pinned
  [`crates/leanvm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/127510d14c98ade4e8a97646c44fa7f1ff5e752d/crates/leanvm/tests/api.rs)
  is the end-to-end usage example.
- Call `setup_prover` before `aggregate`; `setup_verifier` is the verification-only
  initialization path. The process-wide arena and `setup_prover_without_arena` were removed with
  `crates/zk_alloc` after `a386121f`: a proof's buffers are ordinary heap allocations.
- XMSS claims are grouped by strictly increasing `(leaf_index, message)` pairs (by epoch, one
  message each, at `a386121f`); each group is non-empty with a strictly sorted key list. SPHINCS
  claims are sorted, deduplicated `(key, message)` pairs. Raw signatures and child proofs
  populate group-specific write-once coverage regions.
- A child can map its XMSS groups into parent groups with the same leaf index and message.
  Overlap is accounted for through duplicate slots; a published claim must still be covered.
- The guest is self-referential. Three evaluations that are too expensive in-circuit—stacked
  bytecode and Flock matrices `A0` and `B0`—are recursively batched as deferred claims and are
  discharged natively only by root `EthereumProof::verify`.
- No public decreasing recursion-depth measure was found in the audited statement or
  `AggregateSignature` API at `a386121f`. `MAX_RECURSIONS` still bounds child arity, not depth
  (`crates/rec_aggregation/src/aggregation.rs:83-85`), and the published signer claim need not
  strictly grow from child to parent. T6 therefore needs either a statement
  change or a separate, proved well-foundedness argument before recursive extraction can be
  claimed; finiteness must not be inferred from arity alone. The rewritten statement of
  `127510d1` has not been re-audited for such a measure.
- The two-cell public input is a BLAKE2s digest binding the transcript environment, signer-set
  digest, LeanDA root list, and deferred claims. The bare Rust `verify()` validates the statement
  carried by the object; a consumer must separately compare the exposed signer lists (and DA
  roots) with the statement it expected.
- `formal/xmss/` contains a separate VCVio-based Lean theorem
  `xmss_has_127_bits_of_classical_security`. It proves 127-bit classical random-oracle security
  for its reviewed scheme statement with only `propext`, `Classical.choice`, and `Quot.sound` in
  the reported axiom footprint. It does not by itself prove correspondence with the Rust XMSS
  implementation, the zkDSL guest, or the VM constraints. Since `a386121f`, `formal/sphincs/`
  proves 127-bit classical SUF-CMA random-oracle security for its functional model of the SPHINCS
  scheme (`Sphincs.Lifetimes.requestedSecurity`, same axiom footprint); its README states the
  model was checked against `crates/sphincs` by reading, not by a mechanized refinement.

## Known discrepancies at the pin

What the proof system found where the specification (`doc/leanvm/body/`), the Rust (`crates/`)
and the Python verifier (`python-verifier/verifier.py`, written `py:`) differ, leave a fact to
the code, or carry a defect, at `127510d1`. Line citations are at `127510d1` unless an entry
says `a386121f`. Since 8c31abd7 the Rust verifier is the crate `crates/verifier/src/`, a port of
the Python one; the Rust verifier citations of `a386121f` (`lean_vm/src/gkr.rs`, `leaf.rs`,
`constraints.rs`, `cpu/mod.rs` and the `fiat_shamir`, `flock` and `pcs` verifier paths) point at
code removed there. Each entry has a name; where one binds a definition,
the [protocol blueprint](roadmap/protocol-blueprint.md) cites it by that name. The pinned tex is
the authority for the specification: the PDF `leanVM-b-2.pdf` predates it and must not be cited.
The leanISA roadmap's source findings are in [its status file](roadmap/leanisa-status.md). The
former code in parentheses is for reading older pull requests.

**The specification and its verifiers disagree.**

- *The public-input check.* (F18) *Resolved at `127510d1`* (9084d317): the verifiers compute
  every limb's claim and the prover sends nothing, as the rewritten §8.2 does
  (`08-end-to-end-protocol.tex:33-37`; `py:1390-1396`, `crates/verifier/src/lib.rs:251-264`).
  At `a386121f`, §8.2 checked each limb, `c_ℓ = (1 + r)·w_{0,ℓ} + r·w_{1,ℓ}`, while the Rust
  verifier, the Python verifier and the recursion guest checked one equation on the words,
  `c_0 + y·c_1 = (1 + r)·w_0 + r·w_1`, and pooled the scalars sent; both were sound at `1/|E|`
  and the verifiers accepted strictly more transcripts (there `08-end-to-end-protocol.tex:29-33`,
  `lean_vm/src/cpu/mod.rs:750-755`, `py:1398-1400`,
  `rec_aggregation/guests/aggregate.py:1680-1683`).
- *One combiner more than GKR layers.* *Resolved at `127510d1`* (40bdeac6): each layer draws its
  combiner first and nothing follows the last layer, as §5.3 has one per layer
  (`05-arithmetization.tex:91`; `py:438-452`, `crates/verifier/src/bus.rs:18-21`). At
  `a386121f` both verifiers drew a combiner after the roots and after every layer, the last
  included and unused (there `lean_vm/src/gkr.rs:369, 391, 423`, `py:435, 453`).
- *The normalized GKR round.* §5.3 does not state the layer sumcheck's round message. The
  verifiers run the normalized (Gruen) round: a cofactor of degree 4 with four coefficients on
  the wire, the constant one derived through the equality factor, and a layer check without the
  equality factor (`py:410-412, 444, 448`; `crates/verifier/src/transcript.rs:199-201`,
  `bus.rs:25, 36`). (S10, corrected)
- *The fingerprint bound.* The Rust charges `5·2^μ/|E|` where §5.2 proves `4·2^μ/|E|`
  (`leanvm_core/src/leaf.rs:102`; `05-arithmetization.tex:37`).
- *Root order.* (F3, S11) *Resolved at `127510d1`* (2b7ca3b4): §8.5's prose now sends the bus root
  first, then the count root, as the stream has it, the push and pull roots being one scalar
  (`08-end-to-end-protocol.tex:72`; `gkr.rs:326-330`, `py:433`,
  `crates/verifier/src/bus.rs:13`). At `a386121f` the prose named the count root first (there
  `08-end-to-end-protocol.tex:68`).
- *The announced rate.* The verifiers read the WHIR rate with the announced sizes
  (`cpu/mod.rs:119`; `py:1369-1370`, `crates/verifier/src/lib.rs:216-217`); §8.5's list of
  announced values does not match it (`08-end-to-end-protocol.tex:59`).
- *The seed.* §8.5 says the seed binds the R1CS matrices; the Rust binds `R1CS_DIGEST`, one
  constant naming the circuit, whose recipe needs matrices the pinned module no longer builds,
  and the Python, the Rust verifier and the guest copy its bytes (`cpu/mod.rs:62-89`,
  `flock/src/hash.rs:257-278`, `py:631`, `crates/verifier/src/layout.rs:61`). (F14)
- *Setup and format checks the specification omits.* Both verifiers reject a nonzero upper limb
  in an announced size (`py:1366`, `crates/verifier/src/lib.rs:210-213`), `τ_BLAKE2S < 3`
  (`py:863`, `crates/verifier/src/layout.rs:392`), a rate outside `[1, 4]` (`py:1370`,
  `lib.rs:217`), a stack outside `μ ∈ [15, 28]` (`py:1372`, `lib.rs:219-222`), a nonzero third
  limb in a half of the commitment root (`py:222`, `crates/verifier/src/hash.rs:105-106`), and a
  stream not fully consumed (`py:415`, `crates/verifier/src/transcript.rs:206-209`). §8 states
  none of these. At `a386121f` the Rust verifier also required `ζ` to have at least `τ_max`
  coordinates (there `lean_vm/src/constraints.rs:250-253`); removed at `127510d1`, where the
  table sumcheck takes its rounds from the announced heights and `ζ` is the GKR point. (F15)
- *The program in the Python verifier.* It takes the program as the stacked table and does not
  check that the unused slots are zero (`py:558, 859`); the Rust `verifier` crate takes the same
  table (`crates/verifier/src/bytecode.rs:45`), and `leanvm_core::cpu::verify` builds it from a
  `Program` (`cpu/mod.rs:691-695`).

**The specification leaves it to the code** (the blueprint transcribes these).

- *Fiat–Shamir.* §8.4 is `TODO`. The chain is BLAKE2s-256 of 64 bytes (the chain state and a
  block) with four numeric tags in lane 3 and no labels (`fiat_shamir/src/lib.rs:18-175`,
  `crates/verifier/src/transcript.rs:32-123`). (S6, F1)
- *Grinding.* Annex B does not mention it; every WHIR level grinds 17 bits before its queries,
  the Python binds the nonce before checking it, and `ood_samples[0] = 0`
  (`pcs/src/whir_config.rs:60`, `py:376-382`; the Rust port checks first,
  `crates/verifier/src/transcript.rs:109-123`). (S12, F13)
- *Stack size and ties.* §4.1's `M = ⌈log₂ N⌉` has no floor or ceiling and no order for blocks of
  equal size; the verifiers floor at 15, reject above 28, and order ties by the column index, the
  six shared columns first (`04-committing-the-witness.tex:6-10`;
  `leanvm_core/src/witness.rs:56-91`, `cpu/layout.rs:13-49`, `py:304-310, 892`). (S15, F17)
- *The table sumcheck.* Its target is derived, never sent; the three bus forms share the last
  three `ξ` powers; the round polynomial is a cubic of which three coefficients travel
  (`cpu/mod.rs:388-406`, `leanvm_core/src/constraints.rs:123-133, 191-192`;
  `crates/verifier/src/lib.rs:233-237`, `bus.rs:222`, `transcript.rs:186-202`). §5.5
  charges `(ν_side + B)/|E|` for batching where its Corollary 3.9 gives one less, gives no error
  for the recycled zerocheck point, and does not say which coefficient is dropped
  (`05-arithmetization.tex:132, 150`; `03-proving-primitives.tex:67, 110`). (F4, F5, F6, F7)
- *The count tree* holds the tables' count columns only (`cpu/layout.rs:411-413`). (F11)
- *The opening batch.* Ring-switched claims take the low powers of `λ`
  (`pcs/src/stack_open.rs:211-212`; `crates/verifier/src/lib.rs:127, 280-281`). (F8)
- *Flock's circuit and constants.* The BLAKE2s circuit and its wire positions, the slot of each
  of the eighteen limbs (`leanvm_core/src/hash_flock.rs:80-108`), the selector of a limb claim
  (`pcs/src/stack_open.rs:74-87`), the fixed coordinate `g_0` (the hexadecimal expansion of π,
  `flock/src/zerocheck/univariate_skip_optimized.rs:104-106`), the embedding `φ_8` and the
  modulus of `GF(2^8)`, `k_batch = τ_BLAKE2S` and the floor `τ_BLAKE2S ≥ 3`
  (`crates/verifier/src/layout.rs:392`, `py:1091-1094`) are in no annex. (F2)
- *No round-by-round analysis of the bus phase.* The specification's one round-by-round theorem
  is the opening's (Theorem B.7); the Rust asserts a coarse sum for the bus
  (`leaf.rs:100-110`), and its security accounting multiplies only the algebraic checks by the
  Johnson list size (`pcs/src/whir_config.rs:505-536`). (F16)
- *Lemma 5.2's proof* is `TODO` (`05-arithmetization.tex:51`). The specification numbers the
  body's equations (1) to (6) with no section prefix: the stack split is equation (1) of §4.1
  and the leaf decomposition equation (3) of §5.4 (at `a386121f`, (1) to (4), the leaf
  decomposition (2)). (S9, S16)
- *The Rust verifier's rejection set.* At `127510d1` it is the crate `crates/verifier`, whose
  every rejection is a `VerifierError` value (`crates/verifier/src/lib.rs:45-72`); the fill
  blocks make announced heights exact (`cpu/filler.rs:1-25`). At `a386121f` it was four
  predicates plus truncations, with Flock's and WHIR's inside, and structure checks on public
  data were `assert!`s; the bus layout assertion survives on the prover side
  (`leanvm_core/src/leaf.rs:115-138`). (F10, F12)

**Defects of the Rust.**

- *The Flock prover's exceptional challenge.* *Resolved at `127510d1`* (f0fe534a): a round whose
  equality challenge is `1` now computes `G(0)` directly instead of through `(1 + r_eq)⁻¹`
  (`flock/src/zerocheck.rs:105-118, 288-296`). At `a386121f` the prover derived the coefficient
  through `(1 + r_eq)⁻¹` and at `r_eq = 1` emitted a proof its own verifier rejects (probability
  at most `(k_batch + 1)/|E|` per proof), where the specification's protocol is perfectly
  complete (there `flock/src/zerocheck.rs:116-118`).
- *Stale comments*: what binds Flock's counter and flags (`cpu/mod.rs:527-529, 569-571`);
  level-0 grinding (`pcs/src/whir.rs:1139-1140`; every level grinds 17 bits); the size of a WHIR
  Merkle leaf (`pcs/src/whir.rs:169-170`; 24 bytes a lane). Fixed or removed at `127510d1`: the
  table sumcheck's round message (now stated correctly, `leanvm_core/src/constraints.rs:20-27`;
  at `a386121f`, `lean_vm/src/constraints.rs:24, 26, 257-260, 265-266`), the Flock verifier's and
  `hash_flock.rs`'s comments (at `a386121f`, `flock/src/zerocheck.rs:389-390`,
  `lean_vm/src/hash_flock.rs:8-9`) and the WHIR verifier's grinding comment (at `a386121f`,
  `pcs/src/whir.rs:1771-1772`), all with the Rust verifiers of 8c31abd7 or rewritten.

**The specification's analysis, checked by the proof.**

- *The fixed coordinates' independence.* Annex C's soundness argument applies
  `lem:fixed-zerocheck`, whose hypothesis is that the 128 weights `eq(a, b)` of the seven fixed
  coordinates are `F_2`-independent (`c-flock-protocol.tex:278`,
  `03-proving-primitives.tex:95-108`). The specification asserts it and the Rust tests it
  numerically (`flock/src/zerocheck/univariate_skip_optimized.rs:1128`). It holds: Lean proves it
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
most 32, `τ_BLAKE2S ≥ 3`, a power-of-two program: `py:858-866`, called at `py:1371`). The former
finding F9, that it omits them, was false.

## Obligation coverage at the baseline

“Present” means an implementation or prose specification exists in the current leanVM source
repository. “Machine checked” is reserved for a theorem checked by Lean or an equivalent proof
artifact; passing Rust/Python tests is not classified as a proof.

| Obligation | Existing evidence | Missing leanerVM result |
| --- | --- | --- |
| Guest functional correctness | zkDSL guest, Rust construction/API, positive and adversarial tests | T3: reviewed Lean guest specification and local postcondition; provisional T6 would supply recursive closure |
| Guest-to-ISA compilation | Rust zkDSL compiler and compiler regression/soundness tests | T3: certified compiler or proof for the exact emitted aggregation bytecode |
| ISA semantics | LaTeX specification and Rust interpreter; Lean `step`, `run`, and `ValidExecution` (`LeanerVM/Spec/Isa.lean`) written from §2 and diffed arm by arm against `cpu/execute.rs` | T1 prerequisite: a formal correspondence boundary with the executor beyond the recorded diff |
| Constraints imply ISA execution (CC-S) | Constraint/table implementation and design document | T1-S: refinement from every accepted assignment to an ISA trace |
| ISA execution yields constraints (CC-C) | Rust trace construction and honest-prover path | T1-C: satisfying-assignment existence for every in-scope execution |
| Witness-generator consistency (WC) | Executable fill/trace generation and mutation tests | T2: concrete generated assignment satisfies constraints and projects to its execution |
| Bus, lookup, and memory consistency (BC) | M3 bus construction and prose lemmas for count soundness | T1: multiset, range, count, table, bytecode, and memory composition theorem |
| Hint handling | Write-once design, guest checks, and hint-tampering tests | T1/T3: every claim-relevant hinted value is constrained or checked |
| BLAKE2s opcode | Rust implementations and Flock R1CS relation; Lean `compress` and `CompressCells` (`Spec/Blake2s.lean`, `Spec/Isa.lean`) pinned by RFC 7693, `hashlib`, and executor vectors | T1 prerequisite: both constraint directions and implementation correspondence |
| Proof system | Protocol document with component bounds; Rust prover/verifier | T4: formal component notions, Fiat–Shamir assumptions, composed error bound, and verifier refinement |
| Verifier implementations | Rust, Python, and recursive zkDSL implementations; differential tests | T4/T5: each accepts exactly the specified protocol and statement encoding |
| Recursion and deferred claims | Self-recursive guest, native root discharge, end-to-end tests | T5 plus provisional T6: verifier-in-circuit equivalence, batching/root discharge, well-foundedness, and the unresolved inner-ROM/outer-topology extraction bridge |
| XMSS security | Existing machine-checked 127-bit ROM theorem in `formal/xmss/` | Port plus Rust/guest/spec correspondence and integration into T7's assumptions and claim |
| SPHINCS security | Prose specification, Rust implementation/tests, and the 127-bit ROM theorem for the Lean model in `formal/sphincs/` (since `a386121f`) | Port plus Rust/guest/spec correspondence and integration into T7's assumptions and claim |
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
