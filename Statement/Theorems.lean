module

public import Statement.LeanVm
public import Statement.LeanVmGuestCompleteness
public import Statement.LeanXmss
public import Statement.LeanSphincs
public import Statement.LeanDa
public import Statement.CostMachine

/-!
# The theorems

Everything this repository proves, in one place: each field of `Theorems` is one end statement,
defined in the file of `Statement/` named next to it, or, for the guest decoder program
(`GuestKnowledgeSoundness`, its encodings, size bound and budget), in this file's first section.
`lean_vm/LeanVM.lean` proves `Statement.Theorems` for its compiled programs (`LeanVM.theorems_hold`:
`leanVmKnowledgeExtractor := LeanVM.Cost.compiledKnowledgeExtractor`,
`guestWitnessDecoder := LeanVM.Cost.compiledGuestWitnessDecoder`), and the build fails if its axioms
are ever more than Lean's three (`propext`, `Classical.choice`, `Quot.sound`).

Statements that follow from these, in their composed form (what an accepted proof of the leanISA
guest program establishes; the guest program's completeness on recursion nodes and leaves), are in
`Corollaries.lean`, proved from the fields of `Theorems` alone; a reviewer may skip it.

`Theorems` takes two programs of the cost machine (`CostMachine.lean`) as parameters, of the same
type, so every use names them: `leanVmKnowledgeExtractor`, the extractor leanVM's knowledge
soundness is stated for (`LeanVM.extractorComputedBy`: the program, of size at most
`leanVmKnowledgeExtractorSizeBound`, run within a budget in the number of queries), and
`guestWitnessDecoder`, the decoder that names the guest program's witness
(`GuestKnowledgeSoundness`, below; `LeanVmGuest.lean` says why its content is in that decoder). A
program's size is `MachineProgram.size`: one per term node, a literal by its size. `lean_vm` names
both programs (`LeanVM.Cost.compiledKnowledgeExtractor` and
`LeanVM.Cost.compiledGuestWitnessDecoder`, its extractor and decoder compiled). The statement
constrains them only by their size bounds and budgets; `leanVmKnowledgeExtractorSizeBound`
(`CostMachine.lean`), `guestWitnessDecoderSizeBound` and the guest decoder's budget (below) say what
those exclude and what they do not. Every statement with an adversary is in the random-permutation
model (`Statement/README.md`).
-/

/-! ## The guest decoder a program computes

`GuestKnowledgeSoundness` (`LeanVmGuest.lean`'s guest program, its witness named) takes the decoder
that names the witness as a program `D` of the cost machine, as `KnowledgeSoundness` takes the
extractor: `D`, of size at most `guestWitnessDecoderSizeBound`, is run on the encoded program and
execution (`encodeGuestWitnessDecoderInput`) within `guestWitnessDecoderBudget`, and its output is
the encoding (`encodeValue`, the encodings below: a constructor of tag `0` for each structure, its
fields in order) of a seed, a statement and a witness that explain the public input. There is no
parse: the statement names the decoding whose encoding `D` outputs, and the encoding is injective
(`lean_vm`'s `LeanVM.Cost.encodeValue_decoded_injective`), so the output determines it.

The statement accepts any program that computes the witness from the execution within the budget; it
need not read the witness off the memory as the proofs' decoder does. The extractor program is
treated the same way: the statement asks only that it compute a valid execution within its budget,
whatever algorithm it runs. What excludes a decoder that chooses: `D` is a program (no classical
choice), the machine's only runtime data is its input, its size is bounded
(`guestWitnessDecoderSizeBound`, which says what the bound excludes and what it does not), and its
budget (`guestWitnessDecoderBudget`) is a proved upper bound on the compiled decoder's price. One
that output another statement of the same digest would exhibit a Keccak-256 collision; what excludes
it is that none is known. -/

namespace LeanVM.Cost

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-! ### The encodings of a decoding: a constructor of tag `0` for each structure, its fields in
order -/

/-- A bit vector: its number. -/
instance {w : ℕ} : MachineEncoding (BitVec w) := ⟨fun v ↦ .nat v.toNat⟩

instance : MachineEncoding HashSig.PublicKey :=
  ⟨fun k ↦ .constructor 0 [encodeValue k.root, encodeValue k.parameter]⟩

instance : MachineEncoding LeanXmss.LayerSignature :=
  ⟨fun σ ↦ .constructor 0 [encodeValue σ.randomizer, encodeValue σ.chainValues, encodeValue
      σ.authenticationPath]⟩

instance : MachineEncoding LeanXmss.Signature :=
  ⟨fun σ ↦ .constructor 0 [encodeValue σ.leafIndex, encodeValue σ.layers]⟩

instance : MachineEncoding Sphincs.SubtreeOpening :=
  ⟨fun o ↦ .constructor 0 [encodeValue o.values, encodeValue o.path]⟩

instance : MachineEncoding Sphincs.CoordinateOpening :=
  ⟨fun o ↦ .constructor 0 [encodeValue o.subtreeOpenings, encodeValue o.topTreePath]⟩

instance : MachineEncoding Sphincs.Signature :=
  ⟨fun σ ↦ .constructor 0 [encodeValue σ.randomizer, encodeValue σ.forestOpening, encodeValue
      σ.counter,
      encodeValue σ.chainValues, encodeValue σ.authenticationPath]⟩

instance : MachineEncoding BytecodeClaim :=
  ⟨fun c ↦ .constructor 0 [encodeValue c.bytecodePoint, encodeValue c.bytecodeValue]⟩

instance : MachineEncoding DaClaim :=
  ⟨fun c ↦ .constructor 0 [encodeValue c.daRoot, encodeValue c.membershipVectorDigest]⟩

instance : MachineEncoding Da.MatrixWitness :=
  ⟨fun m ↦ .constructor 0 [encodeValue m.rows, encodeValue m.orthogonalVector]⟩

instance : MachineEncoding NodeClaims :=
  ⟨fun c ↦ .constructor 0 [encodeValue c.xmss, encodeValue c.sphincs, encodeValue c.daDigest]⟩

instance : MachineEncoding NodeStatement :=
  ⟨fun s ↦ .constructor 0 [encodeValue s.claims, encodeValue s.deferredClaim]⟩

instance : MachineEncoding Child :=
  ⟨fun c ↦ .constructor 0 [encodeValue c.statement, encodeValue c.freshClaim, encodeValue c.proof]⟩

/-- `signature` the constructor of tag `0`, `child` of tag `1`. -/
instance {W : Type} [MachineEncoding W] : MachineEncoding (ClaimHolder W) where
  encodeValue
    | .signature w => .constructor 0 [encodeValue w]
    | .child i => .constructor 1 [encodeValue i]

instance : MachineEncoding BatchingHints :=
  ⟨fun h ↦ .constructor 0 [encodeValue h.sumcheckMessages, encodeValue h.finalBytecodeValue]⟩

instance : MachineEncoding NodeWitness :=
  ⟨fun w ↦ .constructor 0 [encodeValue w.children, encodeValue w.xmssHolders, encodeValue
      w.sphincsHolders,
    encodeValue w.daMatrix, encodeValue w.batchingHints]⟩

instance : MachineEncoding SeedStatementAndWitness :=
  ⟨fun decoding ↦ .constructor 0 [encodeValue decoding.seed, encodeValue decoding.statement,
    encodeValue decoding.witness]⟩

/-- **The decoder's input**: the program and its execution (the memory's log-size `κ`, its `2^κ`
words, the steps). -/
def encodeGuestWitnessDecoderInput (program : Semantics.LeanIsaProgram)
    (execution : Execution program) : MachineValue :=
  .constructor 0 [encodeValue program, encodeValue execution]

end

end LeanVM.Cost

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- **The bound on the guest decoder program's size** (`MachineProgram.size`): `786000`, the
compiled decoder's size (`785688`: `lean_vm`'s `Cost/DecoderSize.lean` proves the size at most that,
and its test `LeanVMTests/Cost/DecoderSize.lean` measures it exactly) and a slack of `312`. That
size counts in full the guest program's per-function tables, which the decoder's replay of the run
reads and which are literals of the decoder program (`CostMachine.lean`: a literal counts by its
size; the frame cells of the guest's functions are `749835` of it). The slack bounds a table of
witnesses the compiled decoder could carry beside its code (hard-coded signatures, matrices or
proofs that would mask a bug of the guest program on finitely many statements): it is room for one
leanXMSS signature's encoding (`309`) but not two, so no useful table fits (as the extractor's
`14500` against its `14109`). It does not bound what a program written differently could hold: the
guest's frame-cell table (`749835` of the size, cells below `2^20`) packs to about a third, three
cells to a limb, freeing room for about `1600` signatures' encodings. Nor is the compiled program
compact: its size also counts, a literal `0` each, the indices without a body left by the
numbering it shares with the extractor's compiled functions; renumbered compactly, the same
program would leave room for a few signatures' encodings (`lean_vm/README.md` has the
measurements). -/
def guestWitnessDecoderSizeBound : ℕ := 786000

/-! ### The guest decoder's budget -/

/-- **The guest decoder's budget** on an execution of `program` of `steps` steps on a memory of
`2^κ` words: the most the decoder's run may cost, in the machine's price (so also the most steps it
may execute), with `lg = log₂(steps + 1)`,
`(steps + 1)·(2^21 + 2^13·lg) + (70κ + 374)·2^κ + 2^37·(lg + 16)`. `lean_vm` proves the compiled
decoder's price at most this on every valid execution (`Cost/Prices.lean` has the exact price, part
by part). Per step, the decoder replays the step and files the state in its sorted table of function
entries (`2^20.41` to `2^20.75` a step, against the budget's `2^21` to `2^21.3`, growing as
`log(steps)`); the second term builds the sorted
table of the memory's addresses; the third reads the witness at the counts and cursors the guest
program's own asserts bound on every valid execution (`16` children, `65535` claims of each scheme
and coverage slots, a child's cursor at most `8192` words, `da_verify`'s rows at most `1024`) and
its frame lookups (about `2^26.6`, each a binary search over the entries), `2^37·(lg + 16)`, about
`2^42` to `2^43`. So about `2^42.7` at `κ = 20` and `2^20` steps, `2^49.2` at `κ = 28` and `2^28`,
`2^51.2` at `κ = 32` and `2^30`, `2^72.3` at `κ = 32` and `2^51` steps; a valid execution of the
guest program has fewer than `2^51` steps (`2^ℓ·2^κ` states, `ℓ = 19`, `κ ≤ 32`, no state repeated
in a halting run; argued, not a Lean theorem). The constants are the deployed guest program's (its
tables of preconditions and entries, its frames), not those of any program: `program` is only ever
`LeanVM.Guest.guestProgram`. -/
def guestWitnessDecoderBudget {program : LeanIsaProgram} (execution : Execution program) : ℕ :=
  (execution.stepCount + 1) * (2 ^ 21 + 2 ^ 13 * Nat.log2 (execution.stepCount + 1)) +
    (70 * execution.logMemorySize + 374) * 2 ^ execution.logMemorySize +
    2 ^ 37 * (Nat.log2 (execution.stepCount + 1) + 16)

/-- **Knowledge soundness of the leanISA guest program, its witness named**: on every valid
execution `execution` of `guest` on a public input, the decoder program `guestWitnessDecoder`, of
size at most `guestWitnessDecoderSizeBound`, run on the encoded program and execution within its
budget (`encodeGuestWitnessDecoderInput`, `guestWitnessDecoderBudget`), outputs the encoding of a
decoding `decoding`: a seed, the node statement the input commits to under that seed, and a witness
proving it (`ExplainsPublicInput`, `LeanVmGuest.lean`). A larger program, or a run that fails or
exceeds its budget, outputs nothing, so `GuestKnowledgeSoundness` fails at that execution: a program
larger than `guestWitnessDecoderSizeBound` satisfies it only if the guest program has no valid
execution, which the completeness statements exclude, so `GuestKnowledgeSoundness` bounds the
program's size. Its `guest` is only ever `LeanVM.Guest.guestProgram`, whose program the budget's
constants are. -/
def GuestKnowledgeSoundness (guest : LeanIsaProgram) (guestWitnessDecoder : Cost.MachineProgram) :
    Prop :=
  ∀ input (execution : Execution guest), ValidExecution guest input execution →
    ∃ decoding : SeedStatementAndWitness,
      Cost.outputWithin guestWitnessDecoder guestWitnessDecoderSizeBound
          (guestWitnessDecoderBudget execution)
          (Cost.encodeGuestWitnessDecoderInput guest execution) =
        some (Cost.encodeValue decoding) ∧
      ExplainsPublicInput guest input decoding

end

end LeanVM.Node

@[expose] public section

namespace Statement

/-- **The end theorems**, for the extractor program and the guest decoder program (two parameters
of the same type: every use names them). -/
structure Theorems
    (leanVmKnowledgeExtractor guestWitnessDecoder : LeanVM.Cost.MachineProgram) : Prop where
  /-- leanVM is knowledge sound for the straight-line extractor the program computes,
  `extractorComputedBy leanVmKnowledgeExtractor`: at most `(Q + 2^14) · 2^-128 +
  5 (Q + 2^14)² · 2^-256` for `Q ≤ 2^128` queries (`LeanVm.lean`).

  **Efficiency.** The extractor is the program run within its budget,
  `leanVmKnowledgeExtractorBudget N` for a transcript of `N` permutation queries
  (`CostMachine.lean`): `outputWithin` returns the program's output only if its run's price, the sum
  of its steps' prices, each at least `1`, is at most the budget, and only if the program's size is
  at most `leanVmKnowledgeExtractorSizeBound`; otherwise the extractor extracts nothing (`none`).
  Extracting nothing from an accepted proof breaks knowledge soundness (`BreaksKnowledgeSoundness`).
  So this statement implies that, but with the probability above, the program extracts a valid
  execution of an accepted proof within the budget: at most that many steps, about `2^81` up to
  `2^50` permutation queries and `O(N·log³N)` for `N`. That a price unit is a constant number of
  instructions of a 64-bit CPU is trusted (`CostMachine.lean`, *Why the prices are honest*). -/
  leanVmKnowledgeSoundness : LeanVM.KnowledgeSoundness
      (LeanVM.extractorComputedBy leanVmKnowledgeExtractor)
  /-- leanVM is complete: the honest prover's (`LeanVM.leanVmHonestProver`, the executable
  `LeanVM.Prover.prove` of `Prover/Prove.lean`) proof of a valid execution of committed size at
  most `2^28`, at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4` and `2^25` nonces per proof of work, is
  rejected with probability at most `2^-256` (`LeanVm.lean`). -/
  leanVmCompleteness : LeanVM.Completeness

  /-- Every valid execution of the leanISA guest program proves the node statement its public input
  commits to: the decoder program, of size at most `guestWitnessDecoderSizeBound`, outputs, within
  its budget, the encoding of a seed, a statement whose digest under that seed is the input's
  digest, and a witness for it: each signature claim of the statement is held, by a signature or a
  child whose proof the deferring verifier accepts, the bytecode's value at the child's point taken
  from the witness and checked only at the root, and its DA digest is that of the blob matrix it
  checks, zeros or a child's, and its deferred claim is the batching of its children's
  (`NodeRelation`, `LeanVmGuest.lean`). -/
  guestKnowledgeSoundness : LeanVM.Node.GuestKnowledgeSoundness LeanVM.Guest.guestProgram
      guestWitnessDecoder
  /-- A statement's digest binds the seed and the statement, up to a Keccak-256 collision among the
  candidates (`LeanVmGuest.lean`). With `leanVmKnowledgeSoundness` and `guestKnowledgeSoundness` it
  gives what an accepted proof establishes: an accepted proof of the leanISA guest program on
  `statementDigest (deployedSeed guestProgram) s` yields, by `leanVmKnowledgeSoundness`, an
  extracted execution; by `guestKnowledgeSoundness`, the decoder program's seed and statement of the
  same digest, with a witness; by `statementDigestBinds`, that they are `deployedSeed guestProgram`
  and `s`, or a Keccak-256 collision. The composed bound is `Statement.Corollaries`'
  `aggregateSound`, which `lean_vm` derives from these fields (`LeanVM.corollaries_of_theorems`);
  its form for the memory decoder `decode`, `MemoryAggregateSound`, is also proved directly
  (`LeanVM.Guest.End.aggregate_sound_outer`). -/
  statementDigestBinds : LeanVM.Node.StatementDigestBinds
  /-- The leanISA guest program is complete on the eight families of `CoveredNode`, mixed nodes and
  nodes checking one DA matrix of at most `32` rows among them, under the deployed seed and within
  the deployed limits, wherever every child carries the honest prover's proof (`HonestChild`: its
  fresh claim true, its proof the honest one with the deployed Keccak of an execution of the guest
  program of committed size at least `2^22`, accepted by the verifier refusing a zero challenge)
  (`LeanVmGuestCompleteness.lean`). -/
  guestCompleteOnHonestChildren : LeanVM.Guest.Completeness.GuestCompleteOnHonestChildren
  /-- The same honest prover's proof of an execution of the guest program is rarely refused: it
  makes none, or the verifier refusing a zero challenge rejects it, with probability at most
  `2^-126` in the random-permutation model (`LeanVmGuestCompleteness.lean`). Read for the deployed
  Keccak, it is what makes a child carrying the honest proof a `HonestChild`. -/
  honestProofRarelyRefused : LeanVM.Guest.Completeness.HonestProofRarelyRefused
  /-- The batching run outside the circuit is sound: at most `(QA + QV + 1) · M · 2^-191 +
  5 (QA + QV)² · 2^-256` for fewer than `M` children, `QA ≤ 2^128`, `QV ≤ 2^96`; it does not
  compose with the in-circuit statements (`LeanVmGuestCompleteness.lean`). -/
  batchingSound : LeanVM.Guest.Batch.BatchingSound
  /-- leanXMSS is strongly unforgeable: at most `(Q + 1) · 2^-127` for `Q ≥ 1` permutation
  calls of the whole game (`LeanXmss.lean`), key generation and the honest signer's worst-case
  grinding, about `2^33` calls per signing request, included: about `2^-62` at a full lifetime. -/
  leanXmssStronglyUnforgeable : LeanXmss.RandomPermutationModel.LeanXmssStronglyUnforgeable
  /-- leanSPHINCS is strongly unforgeable at every proved lifetime: at most `(Q + 1) · 2^-127` for
  `Q ≥ 1` permutation calls of the whole game (`LeanSphincs.lean`), key generation and the honest
  signer's worst-case grinding, up to about `2^35` calls per signing request, included. -/
  leanSphincsStronglyUnforgeable : Sphincs.Lifetimes.LeanSphincsStronglyUnforgeable

  /-- LeanDA is perfectly complete, for every `π` (`LeanDa.lean`). -/
  leanDaComplete : LeanDa.LeanDaPerfectlyComplete
  /-- LeanDA is position binding: at most `(Q + 1)² · 2^-256` for every `Q` (`LeanDa.lean`). -/
  leanDaPositionBinding : LeanDa.LeanDaPositionBinding
  /-- LeanDA is code binding if its argument, querying the model's oracles, is knowledge sound in
  the random-permutation model with a straight-line extractor (`LeanDa.lean`). -/
  leanDaCodeBinding : LeanDa.LeanDaCodeBinding

end Statement

end
