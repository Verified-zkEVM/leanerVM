/-
  LeanVM.Guest.B1.VerifySub.Segments

  An honest child's accepted deferring run, cut into the segments `verify_sub`'s callees run: the
  completeness direction of `Sound.lean`'s composition.
-/

module

public import LeanVM.Guest.B1.VerifySub.NZBridge
public import LeanVM.Guest.B1.VerifySub.CompleteSpec

/-!
# The segments of an honest child's run

`flatPre`: the deferring verifier's prefix grouped as `verify_sub` runs it (Split.lean's
`deferredFlat` up to the batching challenge): the announced sizes, the stack's root, the bus
challenges, the bus's GKR, `tablesSeg`, the lanes' check, `keccakSeg`, the ring map's other five
challenges; `specPre_flat`: it is `specPre`.

`runsTo_of_runF`: a carried run of a program without commitments is a `RunsTo` on the words it
reads. `readSizes_inv`: the announced sizes' run reads `eOfNat logMem`, the row counts, `eOfNat r`
and returns `layoutOf bytecode logMem rows` (the guest's bytecode of `2^23` words). `announced_eq`:
the run's sizes are `Verifier.announced`'s, so G7's bound `muMin ≤ stackLog` applies.

`child_segments`: on G7's per-child hypotheses, the child's stream is the concatenation of the
segments' words, each segment a carried run (`ChildSegs`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The prefix, grouped as `verify_sub` runs it -/

/-- **The prefix, grouped as `verify_sub` runs it.** -/
def flatPre (c : FixedClaims) (bytecode : List K) (pi : Digest) :
    Prog (Layout × ℕ × List StackClaim) :=
  (readSizes bytecode).bind fun ls ↦
  (commitStack ls.1.stackLog ls.2).bind fun _ ↦
  (Prog.sampleN busBits).bind fun alphas ↦
  Prog.sampleE.bind fun beta ↦
  (Tables.gkrPhase (busLayout [0, ls.1.logMemory, ls.1.logBytecode] ls.1.push).depth).bind fun r ↦
  (Tables.tablesSeg (.claimed c) ls.1 pi alphas beta r.2.1 r.2.2).bind fun bc ↦
  (Prog.require ((lanesOf bc.2).map (·.column) = keccakOutputColumns ∧
    ∀ c ∈ lanesOf bc.2, c.point = ((lanesOf bc.2).headD default).point)).bind fun _ ↦
  (keccakSeg (ls.1.tableLogHeights.getD opKeccak 0) ((lanesOf bc.2).headD default).point
    ((lanesOf bc.2).map (·.value))).bind fun km ↦
  (Prog.sampleN 5).bind fun chs ↦
  Prog.ret (ls.1, ls.2, stackClaims ls.1 bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs))

theorem specPre_flat (c : FixedClaims) (bytecode : List K) (pi : Digest) :
    specPre (.claimed c) bytecode pi = flatPre c bytecode pi := by
  simp only [specPre, flatPre, restClaims, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc]
  refine congrArg _ (funext fun ls ↦ congrArg _ (funext fun _ ↦ ?_))
  rw [verifyBusBalance_split]
  simp only [Tables.tablesSeg, Prog.bind_assoc, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  refine congrArg _ (funext fun alphas ↦ congrArg _ (funext fun beta ↦ congrArg _ (funext fun r ↦
    congrArg _ (funext fun bus ↦ congrArg _ (funext fun cl ↦ congrArg _ (funext fun pc ↦ ?_))))))
  simp only [keccakPhase, lanesOf, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
  refine congrArg _ (funext fun _ ↦ ?_)
  simp only [keccakSeg, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
  refine congrArg _ (funext fun kr ↦ ?_)
  simp only [ringSwitch, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
  rw [show ringMapShifts.length = 5 + 1 from rfl, Prog.sampleN]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
  refine congrArg _ (funext fun m ↦ congrArg _ (funext fun chs ↦ ?_))
  rfl

end
end LeanVM.Guest.B1.VerifySub
