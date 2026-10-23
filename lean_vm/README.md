# lean_vm

A Lean 4 proof that leanVM's verifier is knowledge sound and complete in the random-oracle model, for the verifier, the instruction set and the arithmetization of the leanVM commit in [`../leanvm-rev`](../leanvm-rev).

## What is proved

The statements are in [`LeanVM/Spec/`](LeanVM/Spec/README.md), which imports nothing else from this project (CI checks it): the rest is proof. Read in this order:

| File | What it is |
| --- | --- |
| [`Field.lean`](LeanVM/Spec/Field.lean) | the fields `K = GF(2^64)`, `E = GF(2^192)` and the generator `g` |
| [`Blake2s.lean`](LeanVM/Spec/Blake2s.lean) | BLAKE2s: the compression function and the hash of bytes |
| [`Isa.lean`](LeanVM/Spec/Isa.lean) | leanISA: memory, the six instructions, programs, one step, `ValidExecution`, `Trace.count` |
| [`Verifier.lean`](LeanVM/Spec/Verifier.lean) | the verifier, `python-verifier/verifier.py` transcribed section by section, for any hash function |
| [`Extractor.lean`](LeanVM/Spec/Extractor.lean) | the knowledge extractor: from the proof and the oracle's answers to the adversary's queries, the committed word, its Johnson list and the execution a candidate's memory holds |
| [`Statement.lean`](LeanVM/Spec/Statement.lean) | `KnowledgeSoundness` and `Completeness` |
| [`Guest.lean`](LeanVM/Spec/Guest.lean) | what a proof of the aggregation guest establishes, its witness named: `GuestKnowledge`, `AggregateSound` |
| [`Da.lean`](LeanVM/Spec/Da.lean), [`Node.lean`](LeanVM/Spec/Node.lean) | the DA claim, on LeanDA as [`lean_da`](../lean_da) defines it, and what a node of the aggregation guest establishes (`NodeSpec`) |

The proofs are `LeanVM.knowledgeSoundness_holds` and `LeanVM.completeness_holds` ([`LeanVM/Protocol/LeanVM.lean`](LeanVM/Protocol/LeanVM.lean)).

The knowledge-soundness error is `soundnessError Q = (Q + 13213)(2^-128 + 5(Q + 13213)/2^256) + 13213/2^256` for an adversary of `Q` queries (`13213` bounds the verifier's queries; the last term pays for a fresh answer to one of them equal to a Merkle root the adversary announced without computing it, which the extractor, reading only the adversary's queries, would miss). It is at most `2^-63` for `Q ≤ 2^64` (`soundnessError_le`).

For the deployed aggregation guest's bytecode, the headline is `LeanVM.Guest.End.aggregate_sound_outer` ([`LeanVM/Guest/EndKnow.lean`](LeanVM/Guest/EndKnow.lean)), `AggregateSound guest decode` ([`LeanVM/Spec/Guest.lean`](LeanVM/Spec/Guest.lean)): in the random-oracle model, the outer verifier's checks pass on a statement `s` (the proof on its digest under the deployed seed, its deferred claim, its DA digests) while the execution the proof commits to does not decode to the deployed seed, `s` and a witness holding it, nor yield a BLAKE2s collision with `s`, with probability at most `soundnessError Q`. The collision is excused, not bounded: it is defined through the non-constructive extractor and decoder, so the statement assumes BLAKE2s collision resistance rather than reducing to it. It rests on `LeanVM.Guest.End.guest_knowledge`, which proves `GuestKnowledge guest decode` ([`LeanVM/Spec/Guest.lean`](LeanVM/Spec/Guest.lean)): every valid execution of the guest on a public input decodes, from its memory, to a statement of the input's digest under the decoded seed and a witness holding it (`NodeRel`). The decoder `decode` reads the statement off `main`'s frame and each signature, blob matrix and child proof off the frame of the function that checked it, the frame at which that function's code holds on the call's words (`LeanVM/Guest/Located/`); it makes no choice beyond taking, for each call, the first frame at which the callee's code holds (`tests/LeanVMTests/Guest/DecodeNoChoice.lean`). `aggregate_knowledge` is the same in the random-oracle experiment, composed with the verifier's fixed straight-line extractor `LeanVM.extractor`, which `AggregateSound` also names. The seed is the guest's hint, bound by the digest: `decode_binds` gives a consumer whose statement, under the deployed seed, has the public input's digest that the decoded seed and statement are its own, or a BLAKE2s collision.

The recursion step is `LeanVM.Guest.Batch.children_sound` ([`LeanVM/Guest/Batch/Children.lean`](LeanVM/Guest/Batch/Children.lean)): for a witness of `NodeRel` under the deployed seed whose statement's deferred claim holds (what `aggregate_sound_outer` gives of an accepted root), every child's proof is accepted by the deployed verifier and the child's own deferred claim holds, or a challenge of the node's batching is bad (`BatchBad`: a lambda that the gaps and the earlier lambdas fix, or a sumcheck challenge that is a root of a nonzero quadratic its round fixes; `batch_sound`, [`LeanVM/Guest/Batch/`](LeanVM/Guest/Batch/)). It rests on `verify_of_verifyDeferred` (the deferring verifier with true claims under the deployed IV is the deployed verifier) and `verifyDeferred_shaped` ([`LeanVM/Protocol/Verifier/`](LeanVM/Protocol/Verifier/)). That no batching challenge is bad is the batching's soundness in the random-oracle model, `LeanVM.Guest.Batch.batch_rom` ([`LeanVM/Guest/Batch/Rom.lean`](LeanVM/Guest/Batch/Rom.lean)): the batching as a verifier program (`batchProg`, which is `Node.batch` with its deferred claim checked, `runProof_batchProg`), run with BLAKE2s a random oracle, accepts children of the bytecode's shapes with a false claim with probability at most `(QA + QV) · (2/|E| + failBound)`, through `romSound` with a doom certificate built from `batch_sound`'s pieces (`restSpec`). The guest computes the batching with BLAKE2s itself, so applying it is the Fiat-Shamir assumption for the batching, as `aggregate_sound_outer` is for the outer proof; the two random-oracle statements are separate experiments. Recursion beyond one level is not proved: see below.

The existential forms remain: `LeanVM.Guest.End.guest_sound` ([`LeanVM/Guest/EndFinal.lean`](LeanVM/Guest/EndFinal.lean)) proves `GuestSound`: a valid execution of the guest on a statement's digest gives a statement of that digest, of the guest's shape, that `NodeSpec` holds. `LeanVM.Guest.End.guest_complete` ([`LeanVM/Guest/EndFinalComplete.lean`](LeanVM/Guest/EndFinalComplete.lean)) proves `GuestCompleteWithin B2C.b2cBudget'`: a witness of `NodeRel` within the deployed limits (`Limits`, where `NodeRel` admits witnesses the guest cannot run; [the guest's triage](#the-guests-triage)), its children's openings agreeing in the guest's Merkle caps (`CapsAgree`) and the node within the budget, gives a valid execution of the guest on the statement's digest within the verifier's committed size. The budget hypothesis (`b2cBudget'.size (work s w) ≤ 2^28`, an over-approximation of the run's size) has no proved instance in this repository. Both statements are in [`LeanVM/Guest/End.lean`](LeanVM/Guest/End.lean); `aggregate_sound` and `aggregate_complete` are them in the random-oracle experiment. `NodeSpec` is that some witness holds the statement; since a verifying signature, proof or matrix exists for almost every claim, and the empty statement holds under any seed ([`tests/LeanVMTests/Guest/Knowledge.lean`](tests/LeanVMTests/Guest/Knowledge.lean)), `GuestSound` says little: `guest_knowledge` is the statement to read.

[`LeanVM.lean`](LeanVM.lean) fails the build if the axioms of any of these theorems grow beyond `propext`, `Classical.choice` and `Quot.sound`.

In `KnowledgeSoundness`, `Completeness`, `aggregate_sound_outer` and `batch_rom`, BLAKE2s outside the executed program (Fiat-Shamir, Merkle commitments) is a random oracle; inside the program the deployed BLAKE2s compression is proved. `KnowledgeSoundness` is stated for one extractor, `LeanVM.extractor` ([`Spec/Extractor.lean`](LeanVM/Spec/Extractor.lean)), which is straight-line: from the proof and the oracle's answers to the adversary's own queries alone (not the verifier's; no rewinding) it reads the announced sizes and the stack's Merkle root off the proof as the verifier's first two steps do, reads the committed word off the adversary's answers by inverting the Merkle tree, and returns the halting run of the memory image of a stack in the word's Johnson list (its Reed–Solomon encoding agreeing with the word on at least level 0's Johnson threshold of columns) that is a valid execution, if one is. So an accepted proof commits, except with probability `soundnessError Q`, to a stack whose memory columns hold a valid execution. The choice within the list is classical: the extractor is a definition, not an efficient algorithm. The statement applies to programs whose last instruction is not a `JUMP` (`SentinelSafe`: for others the deployed verifier accepts invalid runs), which the guest satisfies (`guest_sentinelSafe`). A proof is the Python verifier's format (full Merkle paths); the Rust verifier's expansion of the pruned wire paths is not formalized. That the Lean verifier is the Rust and Python ones is test evidence: it accepts the Rust prover's proofs, and gives the Rust verifier's verdict on mutated ones.

`Completeness` covers every valid execution within the verifier's size cap: its committed size (`Trace.committedSize`, the cells the prover commits to, set by the memory, the bytecode and how many instructions of each opcode it executes) at most `2^28`.

## From these theorems to an aggregate's security (not proved)

The theorems compose, on paper, into the security of an aggregate: if the verifier accepts a statement, every leanXMSS and leanSPHINCS claim in it is held by a signature (at the node or a descendant) that verifies with BLAKE2s, and the schemes are strongly unforgeable (127 bits, [`lean_xmss`](../lean_xmss), [`lean_sphincs`](../lean_sphincs)). This composition is not formalized, and it rests on:

1. **BLAKE2s is a random oracle everywhere**, inside the guest's executions too. `NodeRel` checks signatures with the deployed BLAKE2s, while the schemes' security is proved with a random oracle; the binding lemmas excuse BLAKE2s collisions.
2. **Knowledge soundness of the children's proofs.** A child's proof is verified inside the parent's execution; to apply `guest_knowledge` level by level, a valid execution of each child must be extractable (straight-line, from the same transcript). `children_sound` gives that each child's proof is accepted and its deferred claim holds; that this makes the child's statement hold with a witness is the in-guest Fiat-Shamir assumption.
3. **Several honest keys.** The schemes are proved secure for one key: a hybrid over the `n` honest keys loses a factor `n`, each step also paying the other keys' generation in its hash budget.
4. **DA claims** are not covered: the guest's check makes the committed rows codewords only with high probability, and its link to `lean_da`'s code binding (whose bound is a forking bound, about `2^-62` at `2^64` queries) is not proved.
5. **Honest signers use their keys as the games allow.** A leanXMSS key never signs twice at one leaf index (the game counts a forgery only then, and `NodeRel`'s claims do not record the index); a leanSPHINCS key has one of the seven proved subtree heights and signs at most that height's limit of messages (the deployed code accepts any height up to 26, and `sphincsVerify` does not depend on it).

## The guest's proof

The goal: for the deployed guest bytecode `guest : Program`, soundness (a valid execution on the public input `statementDigest seed s` gives `seed'`, `s'` with the same digest, `s'.defer` shaped and `NodeRel seed' s'`) and completeness (`NodeRel` within the deployed limits gives a valid execution), without trusting the zkDSL compiler. [the triage](#the-guests-triage) is the function-by-function map of the guest.

### The chain

```text
bytecode  ⇐ B2 ⇒  core IR of the guest  =  expand (source AST)  ⇐ B1 ⇒  NodeRel
```

* **Source AST.** `crates/rec_aggregation/guests/lean_ethereum.py` after placeholder substitution, as data (`Guest/Data/Source.lean`, exported by the Rust parser). It is not trusted: a parser bug makes B1 or B2 fail, never a false theorem.
* **Expansion** (`Guest/Expand.lean`): the zkDSL front end, written in Lean: `Const` specialization, `unroll`, `@inline`, compile-time folding in its two regimes, virtual bindings, `StackBuf` and slices, `mul_range` lifted to loop functions. It turns a source function and its `Const` arguments into a core IR function. The source semantics is defined as the core semantics of the expansion, and the structural lemmas B1 needs (an `unroll` is a conjunction over its index, a call is its callee's relation) are theorems about `expand`.
* **Core IR** (`Guest/Core.lean`): straight-line SSA statements over field values (sums, products, constants, heap reads and stores as equations on one global memory, hints as free values, `assert ==`, `!=`, range checks, `assert_in_k`, BLAKE2s compressions), calls, forward branches, `match`, loop functions. Its semantics is relational: a function's meaning is a predicate on the memory and its argument and return values. `HeapBuf` is an existential g-power and fresh cells carry no distinctness, so soundness never relies on the allocator.
* **The mirror** of the goal is `expand` applied to the source AST: executable (an interpreter runs it on recorded hints for the differential check), structured as the guest, never out of sync with it.

### B2: bytecode and core IR

The bytecode is data too (`Guest/Data/Bytecode*.lean`, one definition per compiled function, operands as `Nat` offsets so that no `g^n` is ever evaluated), exported by Rust; a Rust test regenerates it and fails when it is stale, as for `NodeVectors.lean`. The certificates (`Guest/Data/Cert*.lean`: the frame cell of each core IR value, the executor's facts, bounds, windows) are generated in Lean by `lake exe guest-cert` from the core IR and the bytecode, since the core IR's values are named by Lean's expansion; the generator is untrusted (a wrong cell fails a check) and CI runs `guest-cert --check`.

* **Program logic** (`Guest/Logic.lean`): `FunSpec f P Q`, in continuation form on `run`: from `f`'s entry with frame `fp` and a run that halts, the run returns to the caller's `(pc, fp)` stored at `fp[0]`, `fp[1]`, with `Q` holding of the memory. All functions are proved together by strong induction on the remaining steps; a loop's tail call is its own spec at the next frame.
* **Symbolic executor** (`Guest/Exec.lean`): walks one compiled function's code once and cuts it into segments at the joins of its forward control flow; each segment's items are atoms (one per executed instruction, plus the meanings of the gadgets: range check, `!=`, copy as `MUL·1`, booleanity, `assert ==`) and forward branches, and its exits are classified (local jump, return, call or fused dispatch into a callee frame holding its return registers, and any other jump by the registers it names: tail call, table dispatch, halt). Frame knowledge (constants that are powers of `g`, the self frame pointer, a loop's next frame) is an environment, intersected at joins and checked by `Result.linked`, never trusted. Inputs (`Facts`): the entry environment, the powers of `g` the constants name (checked by the kernel), dispatch arms; a selector's bound is not an input, the dispatch exit naming the cell its target is read into. Sound (`exec_sound`, step accounting for `funSpec_induction`) and complete (`exec_complete`) against the program logic; the two largest functions are run in windows (`execWin`, `Result.linkedExt`).
* **Checker** (`Guest/Check.lean`, `CheckSound.lean`): with the certificate's cell map, every core IR constraint is implied by an atom on the path (soundness, `checkWins_run`), and every atom holds of the honest memory built from the core IR values (completeness). Evaluated by the kernel (`decide +kernel`, `Guest/Checked/`), over structural recursion, `Nat` keys, no field arithmetic. A function is checked in windows, each its own kernel evaluation: the largest functions in windows of about a thousand instructions, each starting with the facts the previous one hands on, and `main` and `verify_sub` at the points where they start knowing a semantic fact (below). `Guest/Sound.lean` composes the checks into B2's contracts (`b2_step`, `b2_main`).
* **Control-flow integrity.** A `match` dispatch reads its target from the jump table at the selector, so the selector must be in range before it on the path; the jump table's slots are the `SET`s of `__jump_tables`, executed first by every run. 111 of the 207 dispatch sites range-check their selector in the same function. The others are bounded elsewhere, and their bound enters the function's spec: as a precondition its callers establish (`da_list_digest`), as the postcondition of a callee run before the dispatch (`da_verify`, `da_verify_column`, through `da_row_shape`), or, for the 92 column selectors of `check_opening_terminal`, as a precondition carrying the semantic fact that every column's `κ` is below 29, which B1's lemmas about `certify_placement`, `log2_ceil_in_the_exponent` and the candidate selection establish. So B2's soundness for those sites rests on B1 facts proved about code run earlier: `verify_sub` is checked in two windows, the second, from the terminal call, taking the bound from its first `1927` statements (`VsKnown`, which holds over the exponent tables, so `verify_sub`'s precondition carries `ExpTables` of its arguments 4 and 5, `Sig.sem`, established by `main` from `exponent_tables`' relation through `__loop5`).
* **Completeness** additionally builds the memory (`Guest/Memory.lean`) from an honest evaluation, a call tree with one valuation per call instance and a phantom for each frame a `callIf` sets up without entering it (`Memory/Eval.lean`, faithful to `Program.Rel`, and every derivation of it one when every `callIf` callee takes any arguments and every `match` has at most `2^64 - 1` arms, the order of `g`, `Memory/Tree.lean`, as the guest's do, `Memory/GuestWf.lean`): frames and `HeapBuf`s by a bump allocator, each subtree contiguous and a loop's next iteration right after its frame (`Memory/Alloc.lean`), the image holding every frame cell and every word the paths read, write-once consistent, within `2^32` words.

### B1: core IR and the specification

Per source function, a lemma relating its relation to the Spec definition it computes ([the triage](#the-guests-triage): 37 by a representation lemma, 39 guest-specific). The honest hint generator (`Guest/Hints.lean`, `honestStreams`) is a Lean function of a `NodeRel` witness, mirroring the Rust producers push for push and replaying a child's proof with the Spec's deferring verifier; completeness assumes the deployed limits of the triage's findings.

### B2 completeness

`Guest/B2C/` instantiates the memory: the frame sizes and certificate cells (`Defs.lean`), and the checker's facts about the honest memory. Three kernel-checked families, all generated by `lake exe guest-cert`, carry it: the sharing check (`Share`, `B2C/Shared/`: values the compiler puts in one cell are equal on every path), the completeness walk (`Cpl*`, `B2C/Cplw/`: every instruction of every path justified by the core atoms on it, the fixed cells and the callee frames), and the soundness windows it reuses. `FrameAll` builds each running instance's frame from the honest memory, `B2Final` gives End's `b2` and `count`. The instruction counts are `T.weight (pathMax · op) + jtSets op`, the most instructions of each opcode over a function's intra-frame paths.

### End theorems

`Guest/EndFinal.lean` and `Guest/EndFinalComplete.lean`, pinned in `LeanVM.lean`:

* `guest_sound : GuestSound`: a valid execution of the guest on `statementDigest seed s` gives `seed'`, `s'` with the same digest, `s'.defer` shaped and `NodeRel seed' s'`; `aggregate_sound` bounds an adversary's success against the random oracle.
* `guest_complete : GuestCompleteWithin B2C.b2cBudget'`: `NodeRel` within the deployed limits (`Limits`), the children's openings agreeing in the guest's Merkle caps (`CapsAgree`, which fails only on a BLAKE2s collision), and the node's budget within `2^28` give a valid execution of committed size within `2^28`; `aggregate_complete` adds the honest prover's acceptance. The budget is linear in the node's `work` (`End.Work`: claims, raw signatures of each scheme, DA matrices and their rows, children and their claims): words from each callee's bound at the deployed frame sizes, instruction counts from the path maxima carried on the tree `main`'s completeness builds (`RelAtInW`), `da_verify`'s and `verify_sub`'s included, `verify_sub`'s statically bounded callees (`open_stacked` at every configuration among them) by their static certificates (`Count/OsStatic`).

### Open

* The budget's slack, which limits how many children a node within `2^28` may have: first `verify_sub`'s words bound (`vsBound`: `open_stacked`'s `osBop` and its callees' loops at their deployed maxima), which sets the node's memory height; then its instruction weight, which carries the same loops (`verify_tables`', `verify_bus_gkr`'s, `check_opening_terminal`'s) at their maxima, not the honest run's trip counts. Bounding them by each child's own layout would need per-child layout terms in `End.Work`.
* Modules above about 3.5 GB: a few generated windows that are one statement (a `match` or `dispatch` of many arms) and the largest hand-written `Tables` decides.

## The guest's triage

`crates/rec_aggregation/guests/lean_ethereum.py` (G below) against the specification, function by function: **S** computes what a Spec definition already defines (up to representation), **GS** is guest-specific and needs its own mirror and a refinement lemma. It decides the shape of the guest mirror (`LeanVM/Guest/`). V is `Spec/Verifier.lean`, N `Spec/Node.lean`, LX `formal/lean_xmss/LeanXmss/Scheme.lean`, SP `formal/lean_sphincs/Sphincs/Scheme.lean`, LD `formal/lean_da/LeanDa/Scheme.lean`.

Representation conventions: a canonical cell `c0 + y·c1` is the 16 bytes `kBytes c0 ++ kBytes c1`, a digest its two cells (`digestScalars`); a count `n` is `gpow n`; an integer word is its bit pattern (`eOfNat`); an `E` cell in a transcript is its three limbs, 24 bytes (`blockOf`).

The compiled guest (`BYTECODE_LOG = 18`): 262144 instructions, 1044 functions (488 `__loop` helpers, specializations `f__L…`); the largest are `open_stacked` (28 specializations), `verify_sig_lean_sphincs` and `verify_lean_xmss`.

### Functions

#### Fiat-Shamir, bits, exponent gadgets, sumcheck, Merkle, WHIR (G:446-1317)

| # | function | label and correspondence | hints, and what pins them |
|---|---|---|---|
| 1 | pack64x2 | S: `E.ofLimbs a b 0` | `assert_in_k` |
| 2 | assert_canonical | S: `IsCanonical128` | `hint_f192_limbs`: unique tower representation |
| 3 | canonical_limbs | S: limbs 0, 1 | as #2 |
| 4 | challenge_from_state | S: `challengeOf` (V:477) | `hint_f192_limbs`: `assert_in_k` |
| 5 | fs_compress | S: `absorbBlock cv (blockOf x tag)` (V:522) | `hint_f192_limbs`: `assert_in_k`, canonical operand |
| 6 | obs | S: `.read` absorb, `Node.observe` | |
| 7 | fs_next | S: `run .read` (V:557) | stream word, bound by the absorb |
| 8 | squeeze_state | S: `absorbBlock cv (blockOf 0 2)` | |
| 9 | squeeze | S: `.sample`, `Node.squeeze` | via #4 |
| 10 | absorb_nonce | S: `.grind`'s new chaining value | |
| 11 | squeeze_step | S: `.sample`, both words exposed | via #4 |
| 12 | bind_bits | dead code, never called | |
| 13 | exponent_tables | GS: constant tables `g^j ↦ eOfNat (2^j)`, `g^j ↦ g^(2^j)` | |
| 14 | g_power_of_word | GS: `gpow (kToNat v.limb0)`, upper limbs zero | `hint_decompose_bits`: booleanity, reconstruction |
| 15 | verify_log2_ceil | GS: `log2Ceil` (V:695), floored | `hint_log2_ceil`: pinned by the two bounds |
| 16 | log2_ceil_in_the_exponent | GS: as #15 on `g^N` (completes for `N ≤ 2^33`: the log is range-checked below `SIZE_BITS = 34`, G:627) | `hint_decompose_bits_exponent` |
| 17 | decode_query_bits | S: one step of `sampleQueriesAux` (V:1598) | `hint_decompose_bits(192)`: booleanity, reconstruction |
| 18 | grind_check | S: `.grind`, `powOk` (V:482) | `hint_f192_limbs`, `hint_decompose_bits(64)` |
| 19-24 | eq_weight, eqtree, lag64, eq_prefix_chain, rs_eq_run, fold_final_msg | S: `eqKernel`, `lagrangeWeights 64` over `windowDenominator`, `eqEval`, `ringWeight`'s products, `multilinearEval` | |
| 25, 26 | sumcheck_round4, sumcheck_round5 | S: `sumcheckRoundPoly` (V:1313), plain and eq mode | stream |
| 27 | batch_sumcheck | S: `Node.batchRounds` (N:215) | bound by the absorbs |
| 28 | verify_merkle_path | GS: `climb` (V:526) below the cap | `merkle_children`: selected child pinned by write-once, parent hashed, direction bits from #17 |
| 29, 30 | hash_cap_node, verify_merkle_cap | GS: the cap's root on every queried path | `merkle_caps`, `merkle_cap_active`: a zero on a path refuted by `flags[parent] = 1` |
| 31-34 | opening_fold, opening_ood_point, opening_final_message, opening_row_weights | S: `foldRounds`/`tailRounds`, `sampleN`, `readN`, `eqKernel` (reversed at level 0) | stream |
| 35 | opening_queries | GS: `openAll` (V:543) and `enforcedSum` (V:1622) | `merkle_leaf_rows`: limbs in `K`, bound by the root |
| 36 | open_stacked | GS: `verifyWhir`/`whirLevels` (V:1718) per candidate (stack log 22..28, rate 1..4), same reads, samples and grinds in Spec order; the terminal moves to #43 | via #30, #18 |

#### Bus, tables, Flock, the child verifier (G:1320-2281)

| # | function | label and correspondence | hints, and what pins them |
|---|---|---|---|
| 37 | verify_bus_gkr | GS: `verifyGkrGrandProducts`/`gkrLayers` (V:1392), same reads, samples, values; an odd depth runs a binary root layer first | |
| 38 | padding_weight (29 arms) | S value: `paddingWeight` (V:713), and `τ = log2Ceil n` | `hint_decompose_bits(τ+1)` |
| 39 | verify_tables | GS: `verifyBusBalance` after GKR, `tablePhase`, `publicInputPhase`; 112 claims in Spec order | `sort_order`: range check, order, write-once and pigeonhole give a bijection; `bytecode_val` is `FixedClaims.bytecodeValue` (deferred) |
| 40 | verify_flock | S: `verifyFlock (.claimed c)` (V:1997), in Spec order | `matpart` is `FixedClaims.matrixValue`, pinned by the terminal |
| 41 | certify_placement | GS: `placementsOf`/`stackOffsets`/`columnKappas` | `col_sort_order`: as `sort_order` |
| 42 | column_selector (29 arms) | S: `Placement.eqAbove` (V:870), padded to 28 coordinates | `hint_decompose_bits_exponent(28)` |
| 43 | check_opening_terminal | S: `verifyStackedOpening`'s weight and terminal (V:1781) | |
| 44 | verify_sub | GS: `verifyDeferredWith` (V:2235): seed, `readSizes`, `commitStack`, bus, tables, Flock, ring switch, stacked opening, then `defer_out = Node.fixedCells` | `stream`, `table_logs` |

#### Signature verifiers (G:2285-2658)

| # | function | label and correspondence | hints, and what pins them |
|---|---|---|---|
| 45, 46 | shifts, is_child | GS gadgets: `keyAt`/node index, `nodePayload` order | caller pins bits; `siblings` |
| 47, 48 | chain_step, walk | S: a step of `chainWalk`, `recoverChain` (LX:276, SP:466) | `chain_starts`: canonical |
| 49 | walk_group | GS: dispatch over three base-4 digits; product `g^Σd`, encoded `Σ d·4^i` | `digits` |
| 50 | hash_values | S: `leafHash` (LX:285, SP:476); needs `n mod 4 ∈ {0, 2}` | |
| 51 | merkle_path | GS: `treeFold` (LX:312, SP:497) with hinted ordered children | `siblings` |
| 52 | verify_lean_xmss | GS: must be `xmssVerify` (N:64, LX:335) | `leaf_index_bits`, `randomizer`, `digits`, `chain_starts`, `siblings` |
| 53 | sp_forest_key (256 specializations) | S: `childRecover … (lut t)` (SP:563) | `sp_forest_values` |
| 54-56 | sp_fold, sp_subtree_arm, sp_tree_arm | S/GS: `subFold`/`topFold`/`orderTops`; dispatch arms | `sp_forest_nodes`, `sp_keys`, `sp_leaves` |
| 57 | verify_sig_lean_sphincs | GS: must be `sphincsVerify` (N:70, SP:739) | `sp_*`, `digits`, `chain_starts`, `siblings` |

#### Digests, claim lists, LeanDA (G:2661-3116)

| # | function | label and correspondence | hints, and what pins them |
|---|---|---|---|
| 58 | statement_digest | S: `statementDigest` (N:191), byte for byte | `hint_f192_limbs` |
| 59 | scaled_log | GS gadget: `2^shift · log x` as a bit pattern | `hint_decompose_bits_exponent(16)` |
| 60, 61 | claims_window, claims_tail | GS: chunks of `blake2sBytes`, counters by disjoint bits | `claims` |
| 62 | claim_list_digest | S: `xmssListDigest`/`sphincsListDigest` (N:167) | `signers_split`, `claims` |
| 63-65 | child_claims_window, child_claims_tail, child_claim_list_digest | GS: a child's list digest rebuilt from this node's table, each claim marking its slot | `child_claim_index`: range check, write-once |
| 66 | da_verify | S: `Da.Witness.Opens` (`commitCodewords`, `vectorDigest`, row orthogonality) | via #67 |
| 67 | da_row_shape | GS: `r ∈ [1, 1024]`, `lp = clog r` | `da_shape` |
| 68-72 | da_verify_column, da_verify_cell, da_levels, da_vector_dispatch, da_vector_cell | S/GS: `treeRoot` over the column-major list, `listCellDigest`, `vectorDigest` segments | `da_symbols`, `da_weights` |
| 73, 74 | da_list_digest, da_hash_roots | S: `daListDigest` (N:181) | |
| 75 | cover_da_root | GS: coverage of a DA slot | `da_index` |

#### Top level (G:3119-3486)

| # | function | label and correspondence |
|---|---|---|
| 76 | main | GS: one node; must give `∃ seed s w`, public input `statementDigest seed s`, `NodeRel`. Counts, `fs_seed` (pinned by the public input), DA roots and list digests, signers digest, raw signatures (`.direct` holders), at most one direct DA, per child its lists rebuilt from this node's table, its `statementDigest`, `verify_sub`; coverage `written = n_total`; `AtZero` or `aggregate_claims`; own digest against `m[0]`, `m[1]` |
| 77 | aggregate_claims | S: `Node.batch` (N:261), same values in the same order |

Effort: 37 functions need only a representation lemma, 39 a guest-specific mirror and a refinement lemma, 1 is dead. Shared infrastructure: chained BLAKE2s over cells equals `blake2sBytes`; address cells equal `tweakFields` bytes; write-once and pigeonhole bijections; the baked placeholder tables checked against their Spec definitions by kernel decision.

### The hint interface

Each stream is a FIFO of entries popped by `hint_witness`; computed hints (`hint_decompose_bits`, `_exponent`, `hint_log2_ceil`, `hint_f192_limbs`) and the VM's own advice (inverses for `!=`, back-solved products) need no stream. All producers are in `crates/rec_aggregation/src/aggregation.rs`, and every stream is pushed in the order the guest pops it.

| level | streams |
|---|---|
| node (`aggregate_with_stats`) | `meta`, `da_meta`, `fs_seed`, `da_roots`, `claims`, `dup_claims`, `signers_split`, `raw_index`, `sp_raw_index`, `child_meta`, `child_claim_index`, `child_defer`, `child_da_count`, `da_index`, `leaf_defer` |
| batching (`aggregate_deferred_claims`) | `bc_sumcheck_msgs`, `mat_sumcheck_msgs`, `bc_star_hint`, `mat_stars_hint` |
| per child (`gen_verify`) | `stream` (zero-padded to 8192), `table_logs`, `sort_order`, `bytecode_val`, `zc_tau_max`, `matpart`, `col_sort_order`, `merkle_caps`, `merkle_cap_active`, `merkle_leaf_rows`, `merkle_children` |
| signatures | `leaf_index_bits`, `randomizer`, `digits`, `chain_starts`, `siblings`, `sp_*` (raw leanXMSS first, then leanSPHINCS) |
| DA | `da_weights`, `da_shape`, `da_symbols` |

### Findings

No soundness bug and no unpinned hint: every hint is pinned, or is existential content of the statement, the witness or a proof.

`NodeRel` admits witnesses the guest cannot run, so completeness assumes the deployed limits (`NodeRel` stays as it is unless one of them is a real mismatch):

1. a child's stack log is in `[22, 28]` (G:2246; the Spec admits 15);
2. a child's proof stream is at most 8192 scalars (G:2095);
3. at most one direct DA holder (G:3154);
4. repeated declared claims held through a child need distinct child entries (G:2815, 2835, 2876, 3291), where N:363 lets two equal claims share one holder;
5. at most 16 children, at most 16 DA roots per statement and per child, every list and the coverage below `2^16` (G:3145-3169, 3275);
6. at least one declared claim (G:3207).

Minor: `bind_bits` is dead; `hash_values` needs `n mod 4 ∈ {0, 2}`; `Spec/Da.lean` cites a stale guest range, and `Spec/Node.lean` an older leanVM commit.

## Layout

| Path | Contents |
| --- | --- |
| `LeanVM/Spec/` | the statements |
| `LeanVM/Parameters/`, `LeanVM/Semantics/` | constants and encodings; lemmas about the ISA |
| `LeanVM/Arithmetization/` | the tables, the bus and the constraints, sound and complete for valid executions |
| `LeanVM/Protocol/` | the proof system and its proofs; `To{ArkLib,Clean,CompPoly,VCVio}/` hold lemmas meant for those libraries |
| `LeanVM/Guest/` | the aggregation guest: its compiled bytecode (`Data/Bytecode*`, generated) as a `Program` and the program logic for its runs (`Code`, `Bytecode`, `Logic`); its mirror, the source AST (`Source`, the generated `Data/Source`), the core IR and its relational semantics (`Core`, `CoreLemmas`), the renumbering of a function's values (`Renumber`) and the guest's core IR as data (`CoreData`, the generated `Data/Core*`), the zkDSL expansion (`Expand`, `ExpandLemmas`) and an interpreter (`Interp`); the honest hint generator (`Hints`); the value lemmas (`Value/`); the honest memory of an evaluation for completeness (`Memory`, `Memory/`) |
| `tests/` | `#guard`s and `example`s, checked by `lake test`; `fixtures/verifier/` are proofs of the Rust prover |
| `cli/` | `leanvm-verify`, the compiled verifier on a proof's files, `node-vectors`, the costly checks of the Rust vectors, `guest-core`, the writer of the guest's core IR data, and `guest-diff`, the guest's mirror and hint generator against Rust aggregations |
| `scripts/` | the Rust-vs-Lean fuzz, its Rust verifier CLI, the fixture exporter, and the WHIR parameter table generator |

## Building and testing

```sh
lake exe cache get
lake build
lake test
lake exe node-vectors
```

`lake build` at the repository root runs all of it, with the Rust checks below, for the four projects (`../check-all.sh`).

The Rust checks run against leanVM at [`../leanvm-rev`](../leanvm-rev), which `../leanvm-tree.sh` checks out into `../.leanvm`, its `formal/lean_vm` a link to this directory. leanVM's tests that write the Lean data (the guest's bytecode and source, the compiler's test programs, the node vectors) fail when this copy differs from what they write; CI runs them:

```sh
../leanvm-tree.sh
(cd ../.leanvm && cargo test --release -p rec_aggregation --lib -- guest_bytecode_lean guest_source_lean node_spec_vectors)
```

The Rust-vs-Lean differential, as CI runs it:

```sh
lake build leanvm-verify
cargo build --release --manifest-path scripts/rust-verifier-cli/Cargo.toml
python3 -I scripts/fuzz-verifier.py tests/fixtures/verifier --jobs 4
```

The guest's mirror and hint generator against Rust aggregations, as CI runs it: the Rust test writes each case (a leaf of both schemes with a blob, a leaf whose list is longer than a digest window, a node over them), and `guest-diff` checks that the witness holds the statement, that `Hints.honestStreams` is the streams the Rust installed, that the public input is the statement's digest, and that the interpreter runs the guest's core IR on them, printing the first divergence:

```sh
lake build guest-diff
(cd ../.leanvm && LEANVM_GUEST_DIFF=/tmp/guest-diff cargo test --release -p rec_aggregation guest_diff -- --ignored)
.lake/build/bin/guest-diff /tmp/guest-diff/*.txt
```

After a bump of `../leanvm-rev` to a protocol change, regenerate the fixtures with `scripts/export-verifier-fixtures-rust.sh tests/fixtures/verifier`, and the node vectors with `LEANVM_WRITE_NODE_VECTORS=1 cargo test --release -p rec_aggregation node_spec_vectors` in `../.leanvm`. After one to a change to the guest, its compiler or the compiler's test programs, regenerate the guest data with `LEANVM_WRITE_GUEST=1 cargo test --release -p rec_aggregation guest_` in `../.leanvm`. Both write here, through the link. After that, or a change to the expansion (`Guest/Expand.lean`) or the core IR (`Guest/Core.lean`), regenerate the guest's core IR (`LeanVM/Guest/Data/Core*`, the expansion of the source as data, its values renumbered) with `lake exe guest-core`; `lake exe guest-core --check`, which CI runs, fails when it is stale, and `lake exe guest-core --values f` prints the expansion's name of each value of the function `f`.

## Credits

The formalization was started in `Verified-zkEVM/leanerVM`, by scaraven, aryaethn, Alexander Hicks, Elias Judin, Stefano Rocca and Aristotle (Harmonic). Modules derived from the earlier leanth formalization say so in their docstrings.
