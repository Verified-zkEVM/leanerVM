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
`lean_vm/LeanVM.lean` proves `Statement.Theorems (decoderProgram := D) (extractorProgram :=
LeanVM.Cost.extractorProgram)` (`LeanVM.theorems_hold`, for now under the hypothesis that a
decoder program `D` meets its specification), and the build fails if its axioms are ever more
than Lean's three (`propext`, `Classical.choice`, `Quot.sound`).

Statements that follow from these, in their composed form (what an accepted proof of the leanISA
guest program establishes; the guest program's completeness on recursion nodes and leaves), are in
`Corollaries.lean`, proved from the fields of `Theorems` alone; a reviewer may skip it.

The guest program's knowledge statement takes the decoder that names the witness as a parameter,
`decoderProgram`: a program of the cost machine (`CostMachine.lean`) of at most
`guestDecoderSizeBound` terms, run within a budget per execution (`guestDecoderBudget`), whose
output is the encoding of a decoding (`GuestKnowledge`; `LeanVmGuest.lean` says why its content
is in that decoder). leanVM's knowledge soundness takes the extractor as a parameter of the same
kind, `extractorProgram`: a program of at most `extractorSizeBound` terms, its extractor the
program run within a budget per shape (`LeanVM.extractorOf`). The two parameters have the same
type, so every use names them (`Statement.Theorems (decoderProgram := …) (extractorProgram :=
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

The statement accepts any program that computes the witness from the execution within its
budget, not only one that reads it off the memory as the proofs' decoder does: the decoder's
analog of the extractor program, of which the statement asks only that it compute an execution
within its budget, whichever algorithm it runs. What excludes a decoder that chooses: `D` is a
program (no classical choice), the machine's only runtime data is its input, its size bound limits
the table of witnesses it could carry, and its budget is linear in the execution's size. One that
output another statement of the same digest would exhibit a Keccak-256 collision; what excludes
it is that none is known. **The size bound and the price are placeholders** until the decoder
program is compiled and measured. -/

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

/-- **The bound on the guest decoder program's size**: `2^20` terms, the compiled decoder's
measured size (`786226`, `lean_vm`'s `Cost/DecoderSize.lean`) rounded up to a power of two. That
size counts in full the guest program's per-function tables, which the decoder's replay of the
run reads and which are literals of the decoder program (`CostMachine.lean`: a literal counts by
its size; the frame cells of the guest's functions are `749835` of it). The bound limits a table
of witnesses the program could carry (hard-coded signatures, matrices or proofs that would mask a
bug of the guest program on finitely many statements) to the slack between the compiled
decoder's size and the bound. -/
def guestDecoderSizeBound : ℕ := 2 ^ 20

/-- **The guest decoder's price. PLACEHOLDER**: `2^30` operations per word of the program's
`2^ℓ`, of the memory's `2^κ` and per step, to be replaced by a closed form `lean_vm` proves of the
compiled decoder, as `extractorPrice` is the extractor's. It is linear in the steps, with no cap:
`κ` and `ℓ` are capped (`32` each: `HoldsPublicInput`, `Program`) but a valid execution's steps
are not (`ValidExecution`): only the run's distinct
states `(pc, fp)` bound (a run on a fixed memory that repeats a state never halts): `2^ℓ`
instructions, each reading a cell at `fp` times an offset of its own and so stepping from at most
`2^κ` frames, at most `2^(ℓ + κ)` states, `2^64` at `ℓ = κ = 32`, where this placeholder is about
`2^94`. On an execution of committed size at most `2^28`, as an honest proof's (`κ ≤ 26`,
`ℓ ≤ 28`, fewer than `2^28` steps), it is below `2^60`. -/
def guestDecoderPrice (ℓ κ steps : ℕ) : ℕ := 2 ^ 30 * (2 ^ ℓ + 2 ^ κ + steps + 1)

/-- **The guest decoder's budget** on an execution of `prog`: `guestDecoderPrice` at the
program's log-size, the memory's and the number of steps. -/
def guestDecoderBudget {prog : Program} (t : Execution prog) : ℕ :=
  guestDecoderPrice prog.logSize t.logMemorySize t.steps

/-- **Knowledge soundness of the leanISA guest program, its witness named**: on every valid
execution `t` of `guest` on a public input, the decoder program `decoderProgram`, run on the
encoded program and execution within its budget (`encodeDecoderInput`, `guestDecoderBudget`),
outputs the encoding of a decoding `d`: a seed, the node statement the input commits to under that
seed, and a witness proving it (`ExplainsInput`, `LeanVmGuest.lean`). A run that fails or exceeds
its budget outputs nothing, a break. -/
def GuestKnowledge (guest : Program) (decoderProgram : Cost.MachineProgram) : Prop :=
  ∀ input (t : Execution guest), ValidExecution guest input t →
    ∃ d : Decoded, Cost.outputWithin decoderProgram (Cost.encodeDecoderInput guest t)
        (guestDecoderBudget t) = some (Cost.encodeValue d) ∧
      ExplainsInput guest input d

end

end LeanVM.Node

@[expose] public section

namespace Statement

/-- **The end theorems.** -/
structure Theorems (decoderProgram extractorProgram : LeanVM.Cost.MachineProgram) : Prop where
  /-- The guest decoder program has at most `guestDecoderSizeBound` terms (a placeholder), its
  literals counted in full: it can carry a table of witnesses no larger than the bound's slack
  (above). -/
  decoderSize : decoderProgram.size ≤ LeanVM.Node.guestDecoderSizeBound
  /-- The extractor program has at most `extractorSizeBound` terms (`2^15`): it cannot carry a
  table of witnesses (`CostMachine.lean`). -/
  extractorSize : extractorProgram.size ≤ LeanVM.extractorSizeBound
  /-- leanVM is knowledge sound for the straight-line extractor the program computes within its
  budget, `extractorOf extractorProgram` (a run out of budget extracts nothing, a break; the
  machine's prices are trusted to be honest, `CostMachine.lean`): at most
  `(Q + 2^14) · 2^-128 + 5 (Q + 2^14)² · 2^-256` for `Q ≤ 2^128` queries (`LeanVm.lean`). The
  budget is about `N·log³N + 2^117.67` for `N` permutation queries at the worst shape. -/
  knowledgeSoundness : LeanVM.KnowledgeSoundness (LeanVM.extractorOf extractorProgram)
  /-- leanVM is complete: the honest prover's (`LeanVM.prover`, the executable
  `LeanVM.Prover.prove` of `Prover/Prove.lean`) proof of a valid execution of committed size at
  most `2^28`, at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4` and `2^25` nonces per proof of work, is
  rejected with probability at most `2^-256` (`LeanVm.lean`). -/
  completeness : LeanVM.Completeness

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
  establishes: an accepted proof of the leanISA guest program on `dig_iv(s)` yields, by
  `knowledgeSoundness`, an extracted execution; by `guestKnowledge`, the decoder program's statement
  of the same digest with a witness; by `digestBinds`, that it is `s` under `iv` or a Keccak-256
  collision. The composed bound is `Statement.Corollaries`' `aggregateSound`, proved in `lean_vm`
  as `LeanVM.Guest.End.aggregate_sound_outer`. -/
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
