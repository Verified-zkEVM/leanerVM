
## C. Hypotheses, and where each is discharged

The chain, soundness direction: `verify prog input proof = true` →(`verify_iff_compiled`)→
`∃ s, s.Admissible prog ∧` the Fiat–Shamir-compiled oracle verifier of `leanIsaInstance prog s`
accepts →(`verify_knowledgeSound`, in the random-oracle model)→ the extracted stack `q`
satisfies `M3Holds (leanIsaInstance prog s) input q` except with probability `niError`
→(`satisfiedBy_witnessOf`)→ `SatisfiedBy prog input (witnessOf prog s q)`
→(`constraintSoundness`)→ `∃ t, AssignmentRepresents (witnessOf prog s q) t ∧ ValidExecution
prog input t`. Completeness direction: `ValidExecution prog input t` →(`constraintCompleteness`)→
`∃ w, SatisfiedBy prog input w ∧ AssignmentRepresents w t` →(`Sizes.ofWitness`, `stackOf gen`)→
`M3Holds (leanIsaInstance prog s) input (stackOf gen w hs)` →(`piop_perfectCompleteness`, the
compilation)→ `verify prog input (prove …) = true`.

Every hypothesis on the chain, in four kinds: **(P)** a condition on public data anyone can
check; **(V)** a property the verifier checks; **(O)** a theorem another roadmap or library
owes; **(N)** nothing discharges it.

| Hypothesis | Where it appears | Kind | Discharged by | Status |
| --- | --- | --- | --- | --- |
| `s.Admissible prog` | `satisfiedBy_witnessOf` (`:815`), `verify_iff_compiled` (`:1220`) | V | `read_public` (`cpu/mod.rs:157-176`), reproduced by `verify`; supplied by `verify_iff_compiled`'s `∃ s` | consistent, once `Admissible` contains the `μ` and rate windows (`gt-bus.md` G4) |
| `Sizes.ofWitness w = some s` | `stackOf`, `m3Holds_stackOf`, `witnessOf_stackOf` (`:811-819`) | O (leanISA) | `SatisfiedBy.caps.heights`, `seed_rows`, `bytecode_rows` give power-of-two heights | provable from `SatisfiedBy`; ill-defined while `Sizes` holds `logInvRate` (E.3) |
| `FlockWitnessGen` (the generator and its lemma "generated wires satisfy the R1CS when the limbs compress") | `stackOf` (`:811`), `m3Holds_stackOf` | O (#3) | an explicit argument until #3 supplies it (`:857-861`) | named; no statement of its type in the blueprint |
| "the R1CS holds of `q_flock` ⇒ the eighteen limb slots compress" | `satisfiedBy_witnessOf` (`:855-857`) | O (#3) | nothing carries it: `satisfiedBy_witnessOf`'s sketched signature has no argument for it, `FlockInterface (I)` has no such field (`:1077-1085`), and `leanIsaInstance`'s `aux` needs #3's R1CS to be *defined* | **N** until a carrier is named (finding 7) |
| `WellFormedBytecode prog` (`sentinelSafe`, used by soundness; `hasFillBlocks`, used by completeness) | `constraintSoundness`, `constraintCompleteness` (`leanisa-blueprint.md:1156-1166`) | P (decidable on the program: `SentinelSafe` has an instance, `Execution.lean:77-78`; `HasFillBlocks` is undefined yet) | no verifier checks it (leanVM's does not, `leanvm-target.md:57-62`); the compiler emits both (`lean_compiler/src/lib.rs:162`, `filler.rs`); the guest owner (T3) owes it | **N** in the blueprint: `baseVerifier_extractsExecution` (`:1247`) has no such hypothesis and `baseProver_complete` (`:1249`) has `HasFillBlocks` only (finding 3; `docs-debt.md` B.6) |
| `constraintSoundness`, `constraintCompleteness` themselves | Layer 13 (`:1253-1256`) | O (leanISA Layer 10) | not stated in Lean; Layer 9's four statements are block comments (`Statement.lean:442-480`), blocked on Clean's ℕ-counted balance (issue #16, Clean #452/#464) | planned |
| a resource bound on the trace (every table ≤ `2^32` rows) | `constraintCompleteness` as sketched has none | N (leanISA's) | nothing: `ValidExecution` bounds nothing but `κ ≤ 32`, and a run of `2^40` distinct `(pc, fp)` states needs `2^40` rows of one table, which `Caps.heights` forbids | **N** (note 18, out of scope; it reaches T4 through `baseProver_complete`) |
| the stacking window `μ ∈ [15, 28]` and the rate window | `verify`'s acceptance in `baseProver_complete` | V (`cpu/mod.rs:174-176`, `pcs.rs:49-51`) | nothing on the completeness side: `SatisfiedBy.caps` has neither (`Statement.lean:79-81`); a valid execution at `κ = 32` has `4 · 2^32 > 2^28` committed cells | **N**: `baseProver_complete` is false without it (finding 4) |
| a witness *constructed* from `t` ("`prove prog input (witness of t)`", `:1250`) | `baseProver_complete` | O (T2, out of scope `:147-148`) | `constraintCompleteness` gives `∃ w` only | **N** as written (finding 4) |
| `Phases.Complete`, `Phases.Security` for `leanIsaInstance prog s` | the two master theorems (`Spine/Compose.lean:162-177`) | O (holes P1-P8; P5 built) | the phases | assumed interface until every hole is filled (`:1419-1426`) |
| `FiatShamirSecurity`, `BcsSecurity`, `McaJohnson` | `verify_knowledgeSound` (`:1226`) | O (ArkLib, ledger rows *Fiat–Shamir and BCS*, *mutual correlated agreement*) | explicit arguments | assumed interfaces |
| the Flock phase's `Security` (`FlockInterface`) | `verify_knowledgeSound`'s `flock` argument | O (#3) | explicit argument | assumed interface; circular with the instance (finding 7) |
| BLAKE2s as a random oracle | the step from `verify_knowledgeSound` (ROM) to the concrete `verify` | N (a heuristic) | nothing; the blueprint's `baseVerifier_extractsExecution` names `verify` and a probability in one sentence (`:1247-1248`) | **N**: must be stated as the hypothesis it is (finding 3) |
| the round-by-round-to-plain implication | the plain corollary (`:261`) | O (ArkLib, admitted at the pin) | "stated once the implication lands upstream" | consistent; `code-spine.md` C.7 notes it forgets the named extractor |
| the top limb of the public words is zero | `read_public` (`cpu/mod.rs:141-143`) | V in the Rust; by type in Lean (`Memory.lean:107-110`) | the parser of `PublicInput` | consistent; undocumented as a parsing obligation (finding 15) |
| the bytecode is decodable and of power-of-two length ≤ `2^32` | `read_public` (`:157-159`); the Python accepts any array | V in the Rust; by type in Lean (`Program`, `Instruction.lean:87-93`) | the loader of `Program` | consistent; coverage gap recorded (`leanvm-faithfulness-review.md:72`) |
| `κ < 64` for `MemImage.read_gpow` | inside `satisfiedBy_witnessOf`'s `word0_eq` | V | from `s.Admissible prog` (`logMem ≤ 32`) | consistent |
| the count columns are exactly the pulls' count coordinates | `counts_nonzero` both ways | O (Layer 2/3) | a Category-B transcription of `count_columns()` per table (`layout.rs:412-414`), which `Component.toM3` cannot derive from `(sep, dir)` alone | unspecified (finding 11) |

Violations of "nothing is assumed on one side of the boundary which the other side does not
prove": the four rows marked **N** that are not heuristics, namely `WellFormedBytecode` (the
proof system assumes nothing of it and the arithmetization requires it), the resource
bounds and the constructed witness of completeness (the proof system's completeness theorem
requires what the arithmetization's does not give), and the Flock consequence lemma (the
adaptor consumes a theorem no interface carries). The random-oracle heuristic is a fifth,
inherent, and must simply be written down.
