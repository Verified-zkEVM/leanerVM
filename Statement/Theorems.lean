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
`lean_vm/LeanVM.lean` proves `Statement.Theorems decoderProgram LeanVM.Cost.extractorProgram`
(`LeanVM.theorems_hold`, for now under the hypothesis that a decoder program meets its
specification), and the build fails if its
axioms are ever more than Lean's three (`propext`, `Classical.choice`, `Quot.sound`).

Statements that follow from these, in their composed form (what an accepted proof of the leanISA
guest program establishes; the guest program's completeness on recursion nodes and leaves), are in
`Corollaries.lean`, proved from the fields of `Theorems` alone; a reviewer may skip it.

The guest program's knowledge statement takes the decoder that names the witness as a parameter,
`decoderProgram`: a program of the cost machine (`CostMachine.lean`) of at most
`guestDecoderSizeBound` terms, its decoding the program run within a budget per execution
(`LeanVM.Node.decodeOf`; `LeanVmGuest.lean` says why its content is in that decoder). leanVM's
knowledge soundness takes the extractor as a parameter of the same kind, `extractorProgram`: a
program of at most `extractorSizeBound` terms, its extractor the program run within a budget per
shape (`LeanVM.extractorOf`). `lean_vm` names the extractor program
(`LeanVM.Cost.extractorProgram`, its knowledge extractor compiled); a reader need not know which
programs they are. Every statement with an
adversary is in the random-permutation model (`Statement/README.md`).
-/

/-! ## The guest decoder a program computes

`GuestKnowledge` (`LeanVmGuest.lean`'s guest program, its witness named) takes the decoder that
names the witness as a program of the cost machine (`CostMachine.lean`), as `KnowledgeSoundness`
takes the extractor: `decodeOf D t` is the program `D` run on the
encoded program and execution (`encodeDecoderInput`) within `guestDecoderBudget`, its output
parsed as a seed, a statement and a witness (`decodeDecoded`, a linear parse). Its size is at most
`guestDecoderSizeBound`. What excludes a decoder that chooses: `D` is a program (no classical
choice), its budget is far below a search for a Keccak-256 collision, its size bound excludes a
table of statements, and the machine's only runtime data is its input. -/

namespace LeanVM.Cost

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-! ### Decoding: the inverse of the encoding -/

/-- A bit vector: its number. -/
instance {w : ℕ} : MachineEncoding (BitVec w) := ⟨fun v ↦ .nat v.toNat⟩

/-- An option: `none` the constructor of tag `0`, `some a` of tag `1` with `a`'s encoding. -/
def encodeOption {α : Type} [MachineEncoding α] : Option α → MachineValue
  | none => .ctor 0 []
  | some a => .ctor 1 [encodeValue a]

/-! `MachineDecoding α` parses a value as an `α`, the inverse of `MachineEncoding α`: a linear
parse, no search, no check beyond the shape (a constructor's tag and arity, an array's length for
a `Vector` or a function of a finite domain, a natural number's bound for `Fin n`); a bit vector
of `w` bits is its number
modulo `2^w` (`BitVec.ofNat`). `none` on anything else. -/

/-- A machine decoding of `α`: the `α` a value encodes, or `none`. -/
class MachineDecoding (α : Type) where
  /-- The `α` the value encodes, or `none`. -/
  decodeValue : MachineValue → Option α

export MachineDecoding (decodeValue)

instance : MachineDecoding UInt64 where
  decodeValue | .word x => some x | _ => none

instance : MachineDecoding ℕ where
  decodeValue | .nat n => some n | _ => none

instance {n : ℕ} : MachineDecoding (Fin n) where
  decodeValue | .nat i => if h : i < n then some ⟨i, h⟩ else none | _ => none

instance : MachineDecoding Bool where
  decodeValue | .ctor 0 [] => some false | .ctor 1 [] => some true | _ => none

instance {w : ℕ} : MachineDecoding (BitVec w) where
  decodeValue | .nat n => some (BitVec.ofNat w n) | _ => none

instance : MachineDecoding K where
  decodeValue | .word a => some (K.ofLane a) | _ => none

instance : MachineDecoding E := ⟨decodeExtensionElement⟩

instance {α : Type} [MachineDecoding α] : MachineDecoding (List α) :=
  ⟨fun v ↦ (MachineValue.toList? v).bind (·.mapM decodeValue)⟩

instance {α β : Type} [MachineDecoding α] [MachineDecoding β] : MachineDecoding (α × β) where
  decodeValue | .ctor 0 [a, b] => do pure (← decodeValue a, ← decodeValue b) | _ => none

/-- An option from its encoding (`encodeOption`). -/
def decodeOption {α : Type} [MachineDecoding α] : MachineValue → Option (Option α)
  | .ctor 0 [] => some none
  | .ctor 1 [a] => (decodeValue a).map some
  | _ => none

instance {α : Type} [MachineDecoding α] {n : ℕ} : MachineDecoding (Vector α n) where
  decodeValue
    | .arr xs =>
      match xs.toList.mapM decodeValue with
      | some ys => if h : ys.length = n then some ⟨ys.toArray, by simpa using h⟩ else none
      | none => none
    | _ => none

/-- A function of a finite domain from the array of its values. -/
def decodeFiniteFunction {α : Type} [MachineDecoding α] {n : ℕ} : MachineValue → Option (Fin n → α)
  | .arr xs =>
    match xs.toList.mapM decodeValue with
    | some ys =>
      if h : ys.length = n then some fun i ↦ ys[i.val]'(by rw [h]; exact i.isLt) else none
    | none => none
  | _ => none

instance {α : Type} [MachineDecoding α] {n : ℕ} : MachineDecoding (Fin n → α) :=
  ⟨decodeFiniteFunction⟩

instance : MachineDecoding Opening where
  decodeValue | .ctor 0 [l, p] => do pure ⟨← decodeValue l, ← decodeValue p⟩ | _ => none

instance : MachineDecoding Proof where
  decodeValue | .ctor 0 [s, o] => do pure ⟨← decodeValue s, ← decodeValue o⟩ | _ => none

/-! ### The encodings of a decoding: a constructor of tag `0` for each structure, its fields in
order -/

instance : MachineEncoding HashSig.PublicKey :=
  ⟨fun k ↦ .ctor 0 [encodeValue k.root, encodeValue k.parameter]⟩

instance : MachineDecoding HashSig.PublicKey where
  decodeValue | .ctor 0 [r, p] => do pure ⟨← decodeValue r, ← decodeValue p⟩ | _ => none

instance : MachineEncoding LeanXmss.LayerSignature :=
  ⟨fun σ ↦ .ctor 0 [encodeValue σ.randomness, encodeValue σ.chainValues, encodeValue σ.path]⟩

instance : MachineDecoding LeanXmss.LayerSignature where
  decodeValue
    | .ctor 0 [r, c, p] =>
      do pure ⟨← decodeValue r, ← decodeValue c, ← decodeValue p⟩
    | _ => none

instance : MachineEncoding LeanXmss.Signature :=
  ⟨fun σ ↦ .ctor 0 [encodeValue σ.leafIndex, encodeValue σ.layers]⟩

instance : MachineDecoding LeanXmss.Signature where
  decodeValue | .ctor 0 [i, l] => do pure ⟨← decodeValue i, ← decodeValue l⟩ | _ => none

instance : MachineEncoding Sphincs.SubOpening :=
  ⟨fun o ↦ .ctor 0 [encodeValue o.values, encodeValue o.path]⟩

instance : MachineDecoding Sphincs.SubOpening where
  decodeValue | .ctor 0 [v, p] => do pure ⟨← decodeValue v, ← decodeValue p⟩ | _ => none

instance : MachineEncoding Sphincs.CoordOpening :=
  ⟨fun o ↦ .ctor 0 [encodeValue o.sub, encodeValue o.top]⟩

instance : MachineDecoding Sphincs.CoordOpening where
  decodeValue | .ctor 0 [s, t] => do pure ⟨← decodeValue s, ← decodeValue t⟩ | _ => none

instance : MachineEncoding Sphincs.Signature :=
  ⟨fun σ ↦ .ctor 0 [encodeValue σ.randomness, encodeValue σ.forest, encodeValue σ.counter,
      encodeValue σ.chainValues, encodeValue σ.path]⟩

instance : MachineDecoding Sphincs.Signature where
  decodeValue
    | .ctor 0 [r, f, c, v, p] =>
      do pure ⟨← decodeValue r, ← decodeValue f, ← decodeValue c, ← decodeValue v, ← decodeValue p⟩
    | _ => none

instance : MachineEncoding BytecodeClaim :=
  ⟨fun c ↦ .ctor 0 [encodeValue c.bytecodePoint, encodeValue c.bytecodeValue]⟩

instance : MachineDecoding BytecodeClaim where
  decodeValue | .ctor 0 [p, v] => do pure ⟨← decodeValue p, ← decodeValue v⟩ | _ => none

instance : MachineEncoding DaClaim :=
  ⟨fun c ↦ .ctor 0 [encodeValue c.daRoot, encodeValue c.membershipVectorDigest]⟩

instance : MachineDecoding DaClaim where
  decodeValue | .ctor 0 [r, v] => do pure ⟨← decodeValue r, ← decodeValue v⟩ | _ => none

instance : MachineEncoding Da.MatrixWitness :=
  ⟨fun m ↦ .ctor 0 [encodeValue m.rows, encodeValue m.vector]⟩

instance : MachineDecoding Da.MatrixWitness where
  decodeValue | .ctor 0 [r, v] => do pure ⟨← decodeValue r, ← decodeValue v⟩ | _ => none

instance : MachineEncoding Claims :=
  ⟨fun c ↦ .ctor 0 [encodeValue c.xmss, encodeValue c.sphincs, encodeValue c.da]⟩

instance : MachineDecoding Claims where
  decodeValue
    | .ctor 0 [x, s, d] =>
      do pure ⟨← decodeValue x, ← decodeValue s, ← decodeValue d⟩
    | _ => none

instance : MachineEncoding NodeStatement :=
  ⟨fun s ↦ .ctor 0 [encodeValue s.claims, encodeValue s.deferredClaim]⟩

instance : MachineDecoding NodeStatement where
  decodeValue | .ctor 0 [c, d] => do pure ⟨← decodeValue c, ← decodeValue d⟩ | _ => none

instance : MachineEncoding Child :=
  ⟨fun c ↦ .ctor 0 [encodeValue c.statement, encodeValue c.freshClaim, encodeValue c.proof]⟩

instance : MachineDecoding Child where
  decodeValue
    | .ctor 0 [s, f, p] =>
      do pure ⟨← decodeValue s, ← decodeValue f, ← decodeValue p⟩
    | _ => none

/-- `direct` the constructor of tag `0`, `child` of tag `1`. -/
instance {W : Type} [MachineEncoding W] : MachineEncoding (ClaimHolder W) where
  encodeValue | .direct w => .ctor 0 [encodeValue w] | .child i => .ctor 1 [encodeValue i]

instance {W : Type} [MachineDecoding W] : MachineDecoding (ClaimHolder W) where
  decodeValue
    | .ctor 0 [w] => (decodeValue w).map .direct
    | .ctor 1 [i] => (decodeValue i).map .child
    | _ => none

instance : MachineEncoding BatchingHints :=
  ⟨fun h ↦ .ctor 0 [encodeValue h.sumcheckMessages, encodeValue h.finalBytecodeValue]⟩

instance : MachineDecoding BatchingHints where
  decodeValue | .ctor 0 [m, v] => do pure ⟨← decodeValue m, ← decodeValue v⟩ | _ => none

instance : MachineEncoding NodeWitness :=
  ⟨fun w ↦ .ctor 0 [encodeValue w.children, encodeValue w.xmss, encodeValue w.sphincs,
    encodeOption w.daMatrix, encodeValue w.batchingHints]⟩

instance : MachineDecoding NodeWitness where
  decodeValue
    | .ctor 0 [c, x, s, d, h] =>
      do pure ⟨← decodeValue c, ← decodeValue x, ← decodeValue s, ← decodeOption d, ← decodeValue h⟩
    | _ => none

instance : MachineEncoding Decoded :=
  ⟨fun d ↦ .ctor 0 [encodeValue d.seed, encodeValue d.statement, encodeValue d.witness]⟩

instance : MachineDecoding Decoded where
  decodeValue
    | .ctor 0 [s, t, w] =>
      do pure ⟨← decodeValue s, ← decodeValue t, ← decodeValue w⟩
    | _ => none

/-- **The decoder's input**: the program and its execution (the memory's size, its words, the
steps). -/
def encodeDecoderInput (prog : Semantics.Program) (t : Execution prog) : MachineValue :=
  .ctor 0 [encodeValue prog, encodeValue t]

/-- **A decoding from its encoding**: a seed, a statement and a witness; `none` on anything
else. -/
def decodeDecoded : MachineValue → Option Decoded := decodeValue

end

end LeanVM.Cost

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- **The bound on the guest decoder program's size. PLACEHOLDER**: `2^16` terms, to be set,
as `extractorSizeBound` was, to twice the size of the compiled decoder rounded up to a power of
two once that program is measured. It excludes a program that carries a table of statements. -/
def guestDecoderSizeBound : ℕ := 2 ^ 16

/-- **The guest decoder's price. PLACEHOLDER**: `2^30` operations per word of the program's
`2^ℓ`, of the memory's `2^κ` and per step, to be replaced by the closed form `lean_vm` proves of
the compiled decoder (as `extractorPrice` is the extractor's). At `ℓ = κ = 32` and `2^35` steps
it is below `2^66`, far below a search for a Keccak-256 collision. -/
def guestDecoderPrice (ℓ κ steps : ℕ) : ℕ := 2 ^ 30 * (2 ^ ℓ + 2 ^ κ + steps + 1)

/-- **The guest decoder's budget** on an execution of `prog`: `guestDecoderPrice` at the
program's log-size, the memory's and the number of steps. -/
def guestDecoderBudget {prog : Program} (t : Execution prog) : ℕ :=
  guestDecoderPrice prog.logSize t.logMemorySize t.steps

/-- **The decoding a program computes**: the program `D` run within the budget on the encoded
program and execution (`encodeDecoderInput`, `guestDecoderBudget`), its output parsed as a seed, a
statement and a witness (`decodeDecoded`); `none` if the run fails, exceeds its budget, or outputs
no decoding's encoding. -/
def decodeOf (D : Cost.MachineProgram) {prog : Program} (t : Execution prog) : Option Decoded :=
  (Cost.outputWithin D (Cost.encodeDecoderInput prog t) (guestDecoderBudget t)).bind
    Cost.decodeDecoded

/-- **Knowledge soundness of the leanISA guest program, its witness named**: on every valid
execution of `guest` on a public input, the decoder program `decoderProgram` outputs, within its
budget, a seed, the node statement the input commits to under that seed, and a witness proving it
(`ExplainsInput`, `LeanVmGuest.lean`). -/
def GuestKnowledge (guest : Program) (decoderProgram : Cost.MachineProgram) : Prop :=
  ∀ input (t : Execution guest), ValidExecution guest input t →
    ∃ d, decodeOf decoderProgram t = some d ∧ ExplainsInput guest input d

end

end LeanVM.Node

@[expose] public section

namespace Statement

/-- **The end theorems.** -/
structure Theorems (decoderProgram extractorProgram : LeanVM.Cost.MachineProgram) : Prop where
  /-- The guest decoder program has at most `guestDecoderSizeBound` terms (a placeholder): it
  cannot carry a table of statements (above). -/
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
  commits to: the decoder program outputs, within its budget (`decodeOf`), a seed, a statement whose
  digest under that seed is the input's digest, and a witness for it: each signature claim of the
  statement is held, by a signature or a child whose proof the deferring verifier accepts, the
  bytecode's value at the child's point taken from the witness and checked only at the root, and its
  DA digest is that of the blob matrix it checks, zeros or a child's (`NodeRelation`,
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
