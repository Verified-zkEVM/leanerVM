import LeanerVM.Protocol.DecodeWalk
import LeanerVMTests.Protocol.RustProof

/-!
# The Rust proof's chain history, decoded

The verifier's chain walk on the Rust proof of the fixture (`RustProof`), its steps logged
(`walkChainLogged`), leaves a history of 996 steps whose observed scalars and nonces are the
proof's stream (`streamOf`). The decoder of the compiled protocol at the fixture's announcement
reads the whole history, as all 347 rounds of the compiled schedule; the prefix ending where each
phase begins, before its first squeeze, decodes to the rounds of the phases before it, counted off
the schedule; and so does the prefix before level 0's query positions, a group of squeezes. A
history cut inside a group of squeezes, or whose announcement is changed, decodes to nothing. With
another word for level 0, which changes the query batch's claim, the history decodes to as many
rounds (`decodePrefix_isSome_indep`).

The phases' ends are found by the verifier's walks run on the history (`historyOps`), independently
of the decoder. Decoding is interpreted here, about half a minute for the whole history, most of it
the algebra the claims need; the checks share one decoder.
-/

namespace LeanerVMTests.Protocol.DecodeChain

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Verify LeanerVM.Protocol.DecodeChain
open LeanerVMTests.Protocol.RustProof

/-- The fixture's level shapes. -/
def shs : List LevelShape :=
  levelShapes (stackMu fx.prog sizes.1) ((ladderOf fx.prog sizes.1 sizes.2).getD [])

/-- The fixture's chain walk, its steps logged: the wire and the history. -/
def logged : Option (Wire × List Reading) :=
  match walkChainLogged fx.prog sizes.1 fx.input shs blake2sBytes
      ⟨FsState.seed fx.prog fx.input, fx.proof.stream, fx.proof.merkle⟩ with
  | .ok ((w, hist), _) => some (w, hist)
  | .error _ => none

/-- The history. -/
def hist : List Reading := (logged.map (·.2)).getD []

#guard logged.isSome
#guard hist.length == 996
-- The history's observed scalars and nonces are the whole stream.
#guard streamOf hist == fx.proof.stream
-- The walk on the history reads the whole history.
#guard ((walkChain historyOps fx.prog sizes.1 fx.input shs).read hist).map (·.2) == some []

/-- The readings left after a slot reads. -/
def after {α : Type} (s : Slot Reading α) (l : List Reading) : List Reading :=
  ((s.read l).map (·.2)).getD []

/-- Where the history's phases end, by the verifier's walks on the history: the commitment, the
bus phase, the table sumcheck, the public input, the Flock phase, `λ`, and WHIR's first round
polynomial. -/
def phaseEnds : List ℕ :=
  let I := leanVm fx.prog sizes.1
  let r₁ := after (walkSetup historyOps) hist
  let r₂ := after (walkBus historyOps I.μBus I.busClaims) r₁
  let r₃ := after (walkTables historyOps I.τmax I.tableColumns) r₂
  let r₄ := after (walkPub historyOps (PublicInput.sentCount I (I.publicLines fx.input))) r₃
  let r₅ := after (walkFlock historyOps (sizes.1.τ 5)) r₄
  let r₆ := after historyOps.sample r₅
  let r₇ := after (historyOps.nextScalars 2) r₆
  [r₁, r₂, r₃, r₄, r₅, r₆, r₇].map fun r ↦ hist.length - r.length

/-- Where level 0's query positions begin: its folds' challenges and polynomials, the next root,
the out-of-domain point, value and polynomial, and the nonce. -/
def positionsStart : ℕ :=
  match shs with
  | sh :: _ => phaseEnds.getLast! + 3 * sh.fold + 2 + sh.msgLog + 1 + 2 + 1
  | [] => 0

/-- Whether a reading is a squeeze step. -/
def isSqueeze : Reading → Bool
  | (.squeeze, _) => true
  | _ => false

-- Every phase after the commitment begins with a squeeze, and so do the positions.
#guard ((phaseEnds.take 5 ++ [phaseEnds.getLast!]).all fun k ↦
    isSqueeze (hist.getD k (.squeeze, default))) &&
  isSqueeze (hist.getD positionsStart (.squeeze, default)) &&
  !isSqueeze (hist.getD (positionsStart - 1) (.squeeze, default))

/-- The checks on the history, at the fixture's announcement, one decoder built for them: the
whole history decodes as all rounds of the schedule; each phase's and the positions' start decode to
the rounds before them; another level-0 word decodes as many rounds; a cut inside the fingerprint
challenges and a changed announcement decode to nothing. -/
def checks : List Bool :=
  if h : sizes.1.Admissible fx.prog ∧ validRate sizes.2 then
    let I := leanVm fx.prog sizes.1
    let c := leanIsaChain fx.prog sizes.1 h.1 sizes.2 h.2
    let D := decoder fx.prog fx.input sizes.1 h.1 sizes.2 h.2 (Words.zero c)
    let D' := decoder fx.prog fx.input sizes.1 h.1 sizes.2 h.2
      ⟨⟨fun _ ↦ Vector.replicate _ 1⟩, Whir.Ladder.Words.zero _⟩
    let front := 1 + busRounds I + tableRounds I + 2 + flockRounds I I.flock + 1
    let n := front + StepSchedule.seqRounds (.skip :: .msg (SumcheckRound.Message E 2) ::
      c.ladder.steps)
    let starts := [1, 1 + busRounds I, 1 + busRounds I + tableRounds I,
      1 + busRounds I + tableRounds I + 2, front - 1, front, front + 1]
    let level0 := match shs with
      | sh :: _ => front + 1 + 1 + 2 * (sh.fold - 1) + 1 + 1 + sh.msgLog + 3
      | [] => 0
    let rounds := fun (E : SlotDecoder Reading _) (l : List Reading) ↦
      (E.decodePrefix l).map (·.1.val)
    [n == 347, rounds D hist == some n,
      (phaseEnds.zip starts).all fun (k, i) ↦ rounds D (hist.take k) == some i,
      rounds D (hist.take positionsStart) == some level0,
      rounds D' hist == some n,
      rounds D (hist.take 12) == none,
      rounds D ((hist.set 0 (.observe (sizeScalar 18), default))) == none]
  else [false]

#guard checks == List.replicate 7 true

-- The phases end where the walks on the history say.
#guard phaseEnds == [10, 518, 639, 642, 841, 842, 844] && positionsStart == 882

end LeanerVMTests.Protocol.DecodeChain
