module

public import Statement.LeanVm
public import Statement.LeanVmGuest
public import Statement.LeanXmss
public import Statement.LeanSphincs
public import Statement.LeanDa
public import Statement.CostMachine

/-!
# The theorems

Everything this repository proves, in one place: each field of `Theorems` is one end statement,
defined in the file of `Statement/` named next to it, or, for the guest decoder program
(`GuestKnowledge`, its encodings, size bound and budget), in this file's first section.
`lean_vm/LeanVM.lean` proves `Statement.Theorems (extractorProgram := LeanVM.Cost.extractorProgram)
(decoderProgram := D)` (`LeanVM.theorems_hold`, `D` the compiled decoder
`LeanVM.Cost.decoderProgram`), and the build fails if its axioms are ever more than Lean's three
(`propext`, `Classical.choice`, `Quot.sound`).

Statements that follow from these, in their composed form (what an accepted proof of the leanISA
guest program establishes; the guest program's completeness on recursion nodes and leaves), are in
`Corollaries.lean`, proved from the fields of `Theorems` alone; a reviewer may skip it.

The guest program's knowledge statement takes the decoder that names the witness as a parameter,
`decoderProgram`: a program of the cost machine (`CostMachine.lean`) of size at most
`guestDecoderSizeBound` (`MachineProgram.size`: one per term node, a literal by its size), run
within a budget per execution (`guestDecoderBudget`), whose
output is the encoding of a decoding (`GuestKnowledge`; `LeanVmGuest.lean` says why its content
is in that decoder). leanVM's knowledge soundness takes the extractor as a parameter of the same
kind, `extractorProgram`: a program of size at most `extractorSizeBound`, its extractor the
program run within a budget per shape (`LeanVM.extractorOf`). The two parameters have the same
type, so every use names them (`Statement.Theorems (extractorProgram := …) (decoderProgram :=
…)`). `lean_vm` names the extractor program (`LeanVM.Cost.extractorProgram`, its knowledge
extractor compiled); a reader need not know which programs they are. Every statement with an
adversary is in the random-permutation model (`Statement/README.md`).
-/

/-! ## The guest decoder a program computes

`GuestKnowledge` (`LeanVmGuest.lean`'s guest program, its witness named) takes the decoder that
names the witness as a program `D` of the cost machine (`CostMachine.lean`), as
`KnowledgeSoundness` takes the extractor: `D` is run on the encoded program and execution
(`encodeDecoderInput`) within `guestDecoderBudget`, and its output is the encoding (`encodeValue`,
the encodings below: a constructor of tag `0` for each structure, its fields in order) of a seed,
a statement and a witness that explain the public input. There is no parse: the statement names
the decoding whose encoding `D` outputs, and the encoding is injective (`lean_vm`'s
`LeanVM.Cost.encodeValue_decoded_injective`), so the output determines it.

The statement accepts any program that computes the witness from the execution within the budget;
it need not read the witness off the memory as the proofs' decoder does. The extractor program is
treated the same way: the statement asks only that it compute an execution within its budget,
whatever algorithm it runs. What excludes a decoder that chooses: `D` is a program (no classical
choice), the machine's only runtime data is its input, its size bound leaves no room for a useful
table of witnesses beside the compiled decoder, and its budget is a proved upper bound on the
compiled decoder's price. One that output another statement of the same digest would exhibit a
Keccak-256 collision; what excludes it is that none is known. The size bound is the compiled
decoder's measured size and a slack of two leanXMSS signatures' encodings
(`guestDecoderSizeBound`); the budget is an upper bound on the compiled decoder's price, proved
(`guestDecoderPrice`): at `κ = 32` and the guest's `ℓ = 19` a constant of about `2^47.04` (the
witness's reading at the counts a valid execution's own asserts bound), frame lookups and
`2^26.3` to `2^26.7` per step, `O(steps·log² steps)` in all. -/

namespace LeanVM.Cost

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-! ### The encodings of a decoding: a constructor of tag `0` for each structure, its fields in
order -/

/-- A bit vector: its number. -/
instance {w : ℕ} : MachineEncoding (BitVec w) := ⟨fun v ↦ .nat v.toNat⟩

instance : MachineEncoding HashSig.PublicKey :=
  ⟨fun k ↦ .ctor 0 [encodeValue k.root, encodeValue k.parameter]⟩

instance : MachineEncoding LeanXmss.LayerSignature :=
  ⟨fun σ ↦ .ctor 0 [encodeValue σ.randomness, encodeValue σ.chainValues, encodeValue σ.path]⟩

instance : MachineEncoding LeanXmss.Signature :=
  ⟨fun σ ↦ .ctor 0 [encodeValue σ.leafIndex, encodeValue σ.layers]⟩

instance : MachineEncoding Sphincs.SubOpening :=
  ⟨fun o ↦ .ctor 0 [encodeValue o.values, encodeValue o.path]⟩

instance : MachineEncoding Sphincs.CoordOpening :=
  ⟨fun o ↦ .ctor 0 [encodeValue o.sub, encodeValue o.top]⟩

instance : MachineEncoding Sphincs.Signature :=
  ⟨fun σ ↦ .ctor 0 [encodeValue σ.randomness, encodeValue σ.forest, encodeValue σ.counter,
      encodeValue σ.chainValues, encodeValue σ.path]⟩

instance : MachineEncoding BytecodeClaim :=
  ⟨fun c ↦ .ctor 0 [encodeValue c.bytecodePoint, encodeValue c.bytecodeValue]⟩

instance : MachineEncoding DaClaim :=
  ⟨fun c ↦ .ctor 0 [encodeValue c.daRoot, encodeValue c.membershipVectorDigest]⟩

instance : MachineEncoding Da.MatrixWitness :=
  ⟨fun m ↦ .ctor 0 [encodeValue m.rows, encodeValue m.vector]⟩

instance : MachineEncoding Claims :=
  ⟨fun c ↦ .ctor 0 [encodeValue c.xmss, encodeValue c.sphincs, encodeValue c.da]⟩

instance : MachineEncoding NodeStatement :=
  ⟨fun s ↦ .ctor 0 [encodeValue s.claims, encodeValue s.deferredClaim]⟩

instance : MachineEncoding Child :=
  ⟨fun c ↦ .ctor 0 [encodeValue c.statement, encodeValue c.freshClaim, encodeValue c.proof]⟩

/-- `direct` the constructor of tag `0`, `child` of tag `1`. -/
instance {W : Type} [MachineEncoding W] : MachineEncoding (ClaimHolder W) where
  encodeValue | .direct w => .ctor 0 [encodeValue w] | .child i => .ctor 1 [encodeValue i]

instance : MachineEncoding BatchingHints :=
  ⟨fun h ↦ .ctor 0 [encodeValue h.sumcheckMessages, encodeValue h.finalBytecodeValue]⟩

instance : MachineEncoding NodeWitness :=
  ⟨fun w ↦ .ctor 0 [encodeValue w.children, encodeValue w.xmss, encodeValue w.sphincs,
    encodeValue w.daMatrix, encodeValue w.batchingHints]⟩

instance : MachineEncoding Decoded :=
  ⟨fun d ↦ .ctor 0 [encodeValue d.seed, encodeValue d.statement, encodeValue d.witness]⟩

/-- **The decoder's input**: the program and its execution (the memory's size, its words, the
steps). -/
def encodeDecoderInput (prog : Semantics.Program) (t : Execution prog) : MachineValue :=
  .ctor 0 [encodeValue prog, encodeValue t]

end

end LeanVM.Cost

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- **The bound on the guest decoder program's size** (`MachineProgram.size`): `786000`, the
compiled decoder's measured size (`785092`, `lean_vm`'s `Cost/DecoderSize.lean`) and a slack of
`908`. That size counts in full the guest program's per-function tables, which the decoder's
replay of the run reads and which are literals of the decoder program (`CostMachine.lean`: a
literal counts by its size; the frame cells of the guest's functions are `749835` of it). The
slack bounds a table of witnesses our program could carry beside its code (hard-coded
signatures, matrices or proofs that would mask a bug of the guest program on finitely many
statements): it is room for two leanXMSS signatures' encodings (`309` each) but not three, so no
useful table fits. It does not bound what a program written differently could hold: the guest's
frame-cell table (`749835` of the size, cells below `2^20`) packs to about a third, three cells
to a limb, freeing room for about `1600` signatures' encodings. -/
def guestDecoderSizeBound : ℕ := 786000

/-! ### The guest decoder's price

A closed-form upper bound that `lean_vm` proves on the compiled decoder's price
(`Cost/Bounds/Guest/Budget.lean`), as `extractorPrice` is the extractor's: a price per step of the
run and a constant. Per step, the decoder replays the step (`runnerStepPrice`) and files the
state in its table of function entries (`guestDecoderStateFilingPrice`: the precondition test of
each function entered there, at most two, and an insertion in a sorted map of at most
`2·(steps + 1)` keys, whose price grows as `log²(steps)`). The constant is the witness's reading
at the counts a valid execution bounds: the decoder reads its counts off the memory, and the
guest program's own asserts bound them on every valid execution (`lean_vm`'s `valid_counts`: at
most `16` children, `65535` declared claims of each scheme and `65535` slots of both regions),
while `da_verify`'s rows are clamped at `1024` (`LeanDa.maxRows`, which `da_verify` asserts) on
every input. It is dominated by the children's cursor lengths, each priced at its `2^32` maximum
(`16·2^32` steps of the cursor), and the memory's address tables (`2614·2^33`):
`guestDecoderWorstMemoryWitnessPrice ≈ 2^47.04`. A frame lookup (`guestDecoderFramePrice`,
growing as `log²(steps)`) is paid about `2^26.57` times (`guestDecoderWorstFrameLookupCount`).

So the bound is `O(steps·log² steps)`, not linear: per step about `2^26.3` to `2^26.7`, and it
has no term in the memory's or the program's size (`κ` and `ℓ` enter only the step's price,
`runnerStepPrice`). At `κ = 32` and the guest's `ℓ = 19` it is `2^47.23` at `2^10` steps,
`2^48.08` at `2^20`, `2^56.43` at `2^30`, `2^77.60` at `2^51` and `2^86.69` at `2^60`: the
constant and the frame lookups (`2^47.07` to `2^49.11`) dominate up to about `2^21` steps, the
per-step price beyond; the steps enter through the entry table's key exponent,
`Nat.log2 (2·(steps + 1)) + 1`. A valid execution of the guest program has fewer than `2^51`
steps by the argument that no state `(pc, fp)` repeats (`2^ℓ·2^κ` states, `ℓ = 19`, `κ ≤ 32`;
argued, not a Lean theorem). The budget remains above what the compiled decoder spends on an
honest execution (the cursor lengths and the address tables are priced at their maxima, not at
the run's); that looseness is an accepted trade-off.

The literals (`8339`, `113699`, `12895`, `17047343`, the `+ 23`, `+ 25`, `+ 15`, and the other
constants below) are upper bounds `lean_vm` proves of the compiled decoder's parts
(`topConst_le`, `fileStatePrice_eq`, `Cost/Bounds/`); a reviewer checks only their size. They
are the deployed guest program's (its tables of preconditions and entries, its frames), not
those of any program of `2^ℓ` instructions: the budget's constants are `LeanVM.Guest.guest`'s,
and `GuestKnowledge`'s `guest` is only ever that program. -/

/-- The entry table's key exponent: `2·(steps + 1) < 2^exponent` bounds the table's keys. -/
def guestDecoderEntryTableKeyExponent (steps : ℕ) : ℕ := Nat.log2 (2 * (steps + 1)) + 1

/-- The limbs of the entry table's positions and weights (below `2^(exponent + 1)`). -/
def guestDecoderEntryTablePositionLimbs (exponent : ℕ) : ℕ :=
  LeanVM.Cost.limbsBelowTwoPow (exponent + 1)

/-- A lookup in the entry table (keys of at most `22` words). -/
def guestDecoderEntryTableLookupPrice (exponent : ℕ) : ℕ :=
  exponent * (17 + (134 * 22 + 89 + 9 * guestDecoderEntryTablePositionLimbs exponent) *
    (exponent + 2)) + 9

/-- An insertion in the entry table, amortized. -/
def guestDecoderEntryTableInsertPrice (exponent : ℕ) : ℕ :=
  guestDecoderEntryTableLookupPrice exponent + (134 * 22 + 71) * exponent +
    (2 * guestDecoderEntryTablePositionLimbs exponent + 40) * (exponent + 1) + 30

/-- A function's precondition test at a state: `269` memory reads (`1472` each), `99` discrete
logarithms (`402684` each, with the bound's check) and `1057586` for the rest of the test (its
checks over the deployed table of preconditions, `preTestAt_cost_deployed`, and the call). -/
def guestDecoderPreconditionPrice : ℕ := 269 * 1472 + 99 * 402684 + 1057586

/-- Filing one state of the run in the entry table: a lookup of its pc (`8339`), and for each of
the at most two functions entered there the precondition test, the call's key (`32` reads, and
`113699` for the rest of the key, `entryKeyT_cost`'s `113685`, and the filing's glue) and the
insertion. -/
def guestDecoderStateFilingPrice (exponent : ℕ) : ℕ :=
  8339 + (guestDecoderPreconditionPrice + 32 * 1472 + guestDecoderEntryTableInsertPrice exponent +
    113699 + 15) * 2 + 25 + 15

/-- A lookup of a call's frame in the entry table (at most `16` words of arguments and returns)
and a word of the frame. -/
def guestDecoderFramePrice (exponent : ℕ) : ℕ :=
  exponent * (17 + (67 * 16 + 89 + 9 * guestDecoderEntryTablePositionLimbs exponent) *
    (exponent + 2)) + 28 * 16 + 1472 + 11070

/-- The witness's and the decoding's price at the counts a valid execution bounds, the frame
lookups apart: `16` children (their cursors each up to `2^32`) of up to `65535` claims of each
scheme, the declared claims' holders (up to `65535` of each scheme), the DA matrix of up to `1024`
rows, the children's proofs, the tables built once (the discrete logarithm's, the readers', the
address tables of `2^32` words). About `2^47.04`. -/
def guestDecoderWorstMemoryWitnessPrice : ℕ := 144294535527556

/-- How many frame lookups the constant pays for: about `2^26.57`. -/
def guestDecoderWorstFrameLookupCount : ℕ := 99702868

/-- **An upper bound on the guest decoder's price** on a memory of `2^κ` words, the deployed guest
program (`2^ℓ` instructions, `ℓ = 19`) and a run of `steps` steps: per step the replay and the
filing of the state, then the guest's tables of preconditions (`12895`) and of entries
(`17047343`), the witness at a valid execution's counts and its frame lookups. -/
def guestDecoderPrice (κ ℓ steps : ℕ) : ℕ :=
  (LeanVM.Cost.runnerStepPrice κ ℓ + 48 +
      guestDecoderStateFilingPrice (guestDecoderEntryTableKeyExponent steps)) * (steps + 1) +
    12895 + 17047343 + guestDecoderWorstMemoryWitnessPrice +
    guestDecoderWorstFrameLookupCount *
      guestDecoderFramePrice (guestDecoderEntryTableKeyExponent steps) + 23

/-- **The guest decoder's budget** on an execution of `prog`: `guestDecoderPrice` at the
memory's log-size, the program's and the number of steps. Its constants are the deployed guest
program's: `prog` is only ever `LeanVM.Guest.guest`. -/
def guestDecoderBudget {prog : Program} (t : Execution prog) : ℕ :=
  guestDecoderPrice t.logMemorySize prog.logSize t.steps

/-- **Knowledge soundness of the leanISA guest program, its witness named**: on every valid
execution `t` of `guest` on a public input, the decoder program `decoderProgram`, run on the
encoded program and execution within its budget (`encodeDecoderInput`, `guestDecoderBudget`),
outputs the encoding of a decoding `d`: a seed, the node statement the input commits to under that
seed, and a witness proving it (`ExplainsInput`, `LeanVmGuest.lean`). A run that fails or exceeds
its budget outputs nothing, so `GuestKnowledge` fails at that execution. Its `guest` is only ever
`LeanVM.Guest.guest`, whose program the budget's constants are. -/
def GuestKnowledge (guest : Program) (decoderProgram : Cost.MachineProgram) : Prop :=
  ∀ input (t : Execution guest), ValidExecution guest input t →
    ∃ d : Decoded, Cost.outputWithin decoderProgram (Cost.encodeDecoderInput guest t)
        (guestDecoderBudget t) = some (Cost.encodeValue d) ∧
      ExplainsInput guest input d

end

end LeanVM.Node

@[expose] public section

namespace Statement

/-- **The end theorems**, for the extractor program and the guest decoder program (two parameters
of the same type: every use names them). -/
structure Theorems (extractorProgram decoderProgram : LeanVM.Cost.MachineProgram) : Prop where
  /-- The extractor program's size is at most `extractorSizeBound` (`11000`): the slack over the
  compiled extractor's size is room for one leanXMSS signature's encoding, so it carries no
  useful table of witnesses (`CostMachine.lean`). -/
  extractorSize : extractorProgram.size ≤ LeanVM.extractorSizeBound
  /-- leanVM is knowledge sound for the straight-line extractor the program computes within its
  budget, `extractorOf extractorProgram` (a run out of budget extracts nothing, a break; the
  machine's prices are trusted to be honest, `CostMachine.lean`): at most
  `(Q + 2^14) · 2^-128 + 5 (Q + 2^14)² · 2^-256` for `Q ≤ 2^128` queries (`LeanVm.lean`). The
  budget is about `2^117.67 + 2^14.7·N·log²N` for `N` permutation queries at the worst shape
  (`O(N·log³N)` as `N` grows). -/
  knowledgeSoundness : LeanVM.KnowledgeSoundness (LeanVM.extractorOf extractorProgram)
  /-- leanVM is complete: the honest prover's (`LeanVM.prover`, the executable
  `LeanVM.Prover.prove` of `Prover/Prove.lean`) proof of a valid execution of committed size at
  most `2^28`, at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4` and `2^25` nonces per proof of work, is
  rejected with probability at most `2^-256` (`LeanVm.lean`). -/
  completeness : LeanVM.Completeness

  /-- The guest decoder program's size is at most `guestDecoderSizeBound` (`786000`), its literals
  counted in full: the slack over the compiled decoder's size is room for two leanXMSS
  signatures' encodings, so it carries no useful table of witnesses (above). -/
  decoderSize : decoderProgram.size ≤ LeanVM.Node.guestDecoderSizeBound
  /-- Every valid execution of the leanISA guest program proves the node statement its public input
  commits to: the decoder program outputs, within its budget, the encoding of a seed, a statement
  whose digest under that seed is the input's digest, and a witness for it: each signature claim
  of the statement is held, by a signature or a child whose proof the deferring verifier accepts,
  the bytecode's value at the child's point taken from the witness and checked only at the root,
  and its DA digest is that of the blob matrix it checks, zeros or a child's (`NodeRelation`,
  `LeanVmGuest.lean`). -/
  guestKnowledge : LeanVM.Node.GuestKnowledge LeanVM.Guest.guest decoderProgram
  /-- A statement's digest binds the seed and the statement, up to a Keccak-256 collision among
  the candidates (`LeanVmGuest.lean`). With the two fields above it gives what an accepted proof
  establishes: an accepted proof of the leanISA guest program on
  `statementDigest (deployedSeed guest) s` yields, by `knowledgeSoundness`, an extracted execution;
  by `guestKnowledge`, the decoder program's seed and statement of the same digest, with a witness;
  by `digestBinds`, that they are `deployedSeed guest` and `s`, or a Keccak-256 collision. The
  composed bound is `Statement.Corollaries`' `aggregateSound`, proved in `lean_vm` as
  `LeanVM.Guest.End.aggregate_sound_outer` (for the memory decoder). -/
  digestBinds : LeanVM.Node.DigestBinds
  /-- The leanISA guest program is complete on the eight families of `CoveredNode`, mixed nodes and
  nodes checking one DA matrix of at most `32` rows among them. The completeness statements assume
  the children's hypotheses (`AcceptableChild`), which `guestChildComplete` gives honest proofs
  (`LeanVmGuest.lean`). -/
  guestCompleteCovered : LeanVM.Guest.Budget.GuestCompleteCovered
  /-- The same honest prover's proof of an execution of the guest program is a child the guest
  program accepts: rejected with probability at most `2^-126` in the random-permutation model, and
  with the deployed Keccak, where accepted, meeting every hypothesis the guest program's
  completeness assumes of a child (`LeanVmGuest.lean`). -/
  guestChildComplete : LeanVM.Guest.Budget.GuestChildComplete
  /-- The batching run outside the circuit is sound: at most `(QA + QV + 1) · M · 2^-191 +
  5 (QA + QV)² · 2^-256` for fewer than `M` children, `QA ≤ 2^128`, `QV ≤ 2^96`; it does not
  compose with the in-circuit statements (`LeanVmGuest.lean`). -/
  batchSound : LeanVM.Guest.Batch.BatchingSound
  /-- leanXMSS is strongly unforgeable: at most `(Q + 1) · 2^-127` for `Q ≥ 1` permutation
  calls of the whole game (`LeanXmss.lean`), key generation and the honest signer's worst-case
  grinding, about `2^33` calls per signing request, included: about `2^-62` at a full lifetime. -/
  leanXmss : LeanXmss.Rpm.LeanXmssStronglyUnforgeable
  /-- leanSPHINCS is strongly unforgeable at every proved lifetime: at most `(Q + 1) · 2^-127` for
  `Q ≥ 1` permutation calls of the whole game (`LeanSphincs.lean`), key generation and the honest
  signer's worst-case grinding, up to about `2^35` calls per signing request, included. -/
  leanSphincs : Sphincs.Lifetimes.LeanSphincsStronglyUnforgeable

  /-- LeanDA is perfectly complete, for every `π` (`LeanDa.lean`). -/
  leanDaComplete : LeanDa.PerfectlyCompleteRpm
  /-- LeanDA is position binding: at most `(Q + 1)² · 2^-256` for every `Q` (`LeanDa.lean`). -/
  leanDaPositionBinding : LeanDa.PositionBindingRpm
  /-- LeanDA is code binding if its argument, querying the model's oracles, is knowledge sound in
  the random-permutation model with a straight-line extractor (`LeanDa.lean`). -/
  leanDaCodeBinding : LeanDa.CodeBindingRpm

end Statement

end
