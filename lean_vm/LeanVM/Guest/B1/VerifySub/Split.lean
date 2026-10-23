/-
  LeanVM.Guest.B1.VerifySub.Split

  The deferring verifier's program (`deferredProgram`, V:2328) regrouped along `verify_sub`'s
  callees.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.B1.Gkr.Interface

/-!
# The deferring verifier, regrouped

`deferredFlat c bytecode pi` is `deferredProgram c bytecode pi` (`deferred_eq`) with its phases
grouped as `verify_sub` runs them: the announced sizes (`readSizes`), the stack's commitment, the
four bus challenges and `β`, the bus's GKR (`gkrPhase`, `verify_bus_gkr`), the bus's rest, the
table sumcheck and the public input (`tablesSeg`, `verify_tables`), the output lanes' check, the
Keccak reduction and the ring map's first challenge (`keccakSeg`, `verify_keccak`), the ring map's
other five challenges, the batching challenge, the stacked opening up to its terminal (`whirOpen`,
`open_stacked`) and the terminal's check (`check_opening_terminal`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verifyBusBalance` (V:1481) as the challenges, `gkrPhase` and `busRest`. -/
theorem verifyBusBalance_split (ev : Evaluations) (layout : Layout) :
    verifyBusBalance ev layout =
      (Prog.sampleN busBits).bind fun alphas ↦ Prog.sampleE.bind fun beta ↦
        (Tables.gkrPhase (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth).bind
          fun r ↦ Tables.busRest ev layout alphas beta r.2.1 r.2.2 := by
  simp only [verifyBusBalance, Tables.gkrPhase, Tables.busRest, Prog.bind_eq, Prog.pure_eq,
    Prog.bind_assoc, Prog.ret_bind]

/-- The output lanes' claims (V:2215). -/
def lanesOf (claims : List ColumnClaim) : List ColumnClaim :=
  claims.filter fun c ↦ c.column ∈ keccakOutputColumns

/-- The claims the opening batches, as stack claims: the ring switch's first. -/
def stackClaims (layout : Layout) (claims : List ColumnClaim) (outs : List ColumnClaim)
    (ringPoint slices challenges : List E) : List StackClaim :=
  ringSwitchClaim layout (polyEval (slices.map (phiMap · challenges)) gen)
      (fun rPrime ↦ ringWeight ringPoint rPrime (ringCoefficients challenges)) ::
    (claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) ++ outs).map (·.onStack layout)

/-- **The deferring verifier's program, regrouped.** -/
def deferredFlat (c : FixedClaims) (bytecode : List K) (pi : Digest) : Prog Bool :=
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
  Prog.sampleE.bind fun lam ↦
  let all := stackClaims ls.1 bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)
  (B1.Whir.whirOpen ls.1.stackLog ls.2 (dot (powers lam all.length) (all.map (·.2)))).bind fun w ↦
  (Prog.require (w.Accepts fun point ↦ dot (powers lam all.length) (all.map fun c ↦ c.1 point))).bind
    fun _ ↦ Prog.ret true

theorem deferred_eq (c : FixedClaims) (bytecode : List K) (pi : Digest) :
    deferredProgram c bytecode pi = deferredFlat c bytecode pi := by
  simp only [deferredProgram, verifyExecution, deferredFlat, Prog.bind_eq, Prog.pure_eq,
    Prog.bind_assoc]
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
  simp only [verifyStackedOpening, B1.Whir.verifyWhir_split, stackClaims, Prog.bind_eq,
    Prog.bind_assoc]
  refine congrArg _ (funext fun lam ↦ congrArg _ (funext fun w ↦ ?_))
  rfl

end
end LeanVM.Guest.B1.VerifySub
