/-
  LeanVM.Guest.B1.VerifySub.RunM

  The deferring verifier's run, phase by phase, over a hash model: what `verify_sub`'s soundness
  over the model assembles.
-/

module

public import LeanVM.Guest.B1.VerifySub.Run
public import LeanVM.Guest.B1.VerifySub.InterfaceM

/-!
# The deferring verifier over a hash model, phase by phase

`Run.lean` over a hash model `M`: `RunsM M p s a s'` says `p` runs from `s` to `a` and `s'` with
every hash answered by the model (`runM M`). The phases of `verifyExecution` as `verify_sub` runs
them, each chain step the model's answer (`obsAllM`, `sqAllM`, `sqCvM`):
`runs_readSizesM`, `runs_commitStackM`, `runs_ringSwitchM`, `runs_verifyStackedOpeningM`.

`verifyDeferredWith_true`: from the phases' runs over the model, the deferring verifier over the
model's hash accepts, `verifyDeferredWith M.H bytecode seed pi c π = some true` (the form
`NodeRelWith` takes).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel}

/-! ## Runs -/

variable (M) in
/-- `p` runs from `s` to `a` and `s'`, every hash answered by the model. -/
def RunsM {α : Type} (p : Prog α) (s : St) (a : α) (s' : St) : Prop :=
  runM M p s = some (some (a, s'))

theorem RunsM.bind {α β : Type} {p : Prog α} {f : α → Prog β} {s s1 s2 : St} {a : α} {b : β}
    (h1 : RunsM M p s a s1) (h2 : RunsM M (f a) s1 b s2) : RunsM M (p >>= f) s b s2 := by
  unfold RunsM at *
  rw [prog_bind_eq, runM_bind, h1]
  exact h2

theorem RunsM.ret {α : Type} (a : α) (s : St) : RunsM M (Prog.ret a) s a s := rfl

theorem RunsToM.runs {α : Type} {p : Prog α} {cv cv' : Digest} {xs : List E} {a : α}
    (h : RunsToM M p cv xs a cv') (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    RunsM M p ⟨cv, xs ++ rest, os, roots⟩ a ⟨cv', rest, os, roots⟩ := h rest os roots

theorem RunsWithM.runs {α : Type} {p : Prog α} {cv cv' : Digest} {xs : List E}
    {os : List Opening} {roots roots' : List (Digest × ℕ × ℕ)} {a : α}
    (h : RunsWithM M p cv xs os roots a cv' roots') (rest : List E) (orest : List Opening) :
    RunsM M p ⟨cv, xs ++ rest, os ++ orest, roots⟩ a ⟨cv', rest, orest, roots'⟩ := h rest orest

/-! ## The phases -/

theorem runs_readSizesM {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {logMem rate : ℕ}
    {rows : List ℕ} (hm1 : 16 ≤ logMem) (hm2 : logMem ≤ 32) (hr1 : 1 ≤ rate) (hr2 : rate ≤ 4)
    (hl : rows.length = 6) (hrows : ∀ n ∈ rows, n ≤ 2 ^ 32)
    (hs1 : minStackedLog ≤ (layoutOf bytecode logMem rows).stackLog)
    (hs2 : (layoutOf bytecode logMem rows).stackLog ≤ maxStackedLog) {cv cv' : Digest}
    (hcv : obsAllM M cv (announce logMem rows rate) = some cv') (rest : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    RunsM M (readSizes bytecode) ⟨cv, announce logMem rows rate ++ rest, os, roots⟩
      (layoutOf bytecode logMem rows, rate) ⟨cv', rest, os, roots⟩ := by
  have e : 2 + tables.length = (announce logMem rows rate).length := by
    simp [announce, hl, tables_length]
  have hall : ((announce logMem rows rate).all fun value ↦
      decide (value.limb 1 = 0 ∧ value.limb 2 = 0)) = true := by
    simp [announce, eOfNat_limb1, eOfNat_limb2]
  have hlt : ∀ n ∈ rows, n < 2 ^ 64 := fun n hn => lt_of_le_of_lt (hrows n hn) (by decide)
  have hm : kToNat (((announce logMem rows rate).headD 0).limb 0) = logMem := by
    simp only [announce, List.cons_append, List.headD_cons]
    exact kToNat_eOfNat_limb0 (by omega)
  have hrw : (((announce logMem rows rate).drop 1).take tables.length).map
      (fun value ↦ kToNat (value.limb 0)) = rows := by
    simp only [announce, List.cons_append, List.drop_succ_cons, List.drop_zero, tables_length,
      ← hl, List.take_left', List.length_map, List.map_map]
    conv_rhs => rw [← List.map_id rows]
    exact List.map_congr_left fun n hn => kToNat_eOfNat_limb0 (hlt n hn)
  have hrt : kToNat (((announce logMem rows rate).getLastD 0).limb 0) = rate := by
    simp only [announce, List.cons_append, List.getLastD_eq_getLast?, List.getLast?_cons,
      List.getLast?_append, Option.some_or, Option.getD_some]
    exact kToNat_eOfNat_limb0 (by omega)
  unfold readSizes
  rw [e]
  refine RunsM.bind (RunsToM.runs (runsToM_readN hcv) rest os roots) ?_
  simp only [Prog.bind_eq, Prog.pure_eq, hall, hm, hrw, hrt, require_pos trivial,
    require_pos (show 1 ≤ rate ∧ rate ≤ 4 from ⟨hr1, hr2⟩), Prog.ret_bind,
    buildLayout_eq hb hm1 hm2 hl hrows, Verifier.liftOption, require_pos (show _ ∧ _ from ⟨hs1, hs2⟩)]
  exact RunsM.ret _ _

theorem runs_commitStackM {μ r : ℕ} (hc : configOk μ r = true) {x0 x1 : E} {root : Digest}
    (hroot : (x0, x1) = digestScalars root) {cv cv' : Digest}
    (hcv : obsAllM M cv [x0, x1] = some cv') (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    RunsM M (commitStack μ r) ⟨cv, x0 :: x1 :: rest, os, roots⟩ ()
      ⟨cv', rest, os, roots ++ [(root, stackShape μ r)]⟩ := by
  obtain ⟨c0, h0, hr⟩ := Option.bind_eq_some_iff.mp hcv
  obtain ⟨c1, h1, h2⟩ := Option.bind_eq_some_iff.mp (show (obsCvM M c0 x1).bind
    (fun c ↦ obsAllM M c []) = some cv' from hr)
  obtain rfl : c1 = cv' := Option.some.inj h2
  unfold configOk at hc
  unfold commitStack stackShape
  split at hc
  · rename_i level levels hcfg
    rw [hcfg]
    simp only [Verifier.liftOption, Prog.bind_eq, Prog.ret_bind]
    show runM M (Prog.commit _ _ (Prog.ret ())) _ = _
    simp only [runM, Compile.run, absorbBlock, Option.bind_eq_bind]
    rw [show M.H (digestBytes cv ++ blockOf x0 1) = some c0 from h0,
      Option.bind_some, show M.H (digestBytes c0 ++ blockOf x1 1) = some c1 from h1,
      Option.bind_some, hroot, digestOfScalars_digestScalars]
    rfl
  · exact absurd hc (by simp)

theorem runs_ringSwitchM (point s : List E) {cv cv' : Digest} {mcs : List E}
    (hsq : sqAllM M 6 cv = some (mcs, cv')) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    RunsM M (ringSwitch point s) ⟨cv, rest, os, roots⟩
      (ringTarget s mcs, fun rPrime ↦ ringWeight point rPrime (ringCoefficients mcs))
      ⟨cv', rest, os, roots⟩ := by
  unfold ringSwitch
  exact RunsM.bind (RunsToM.runs (runsToM_sampleN hsq) rest os roots) (RunsM.ret _ _)

theorem runs_verifyStackedOpeningM {μ r : ℕ} {claims : List StackClaim} {cv cvL cv' : Digest}
    (hL : sqCvM M cv = some cvL) {xs : List E} {os : List Opening}
    {roots roots' : List (Digest × ℕ × ℕ)} {w : WhirEnd}
    (hw : RunsWithM M (whirOpen μ r (dot (powers (challengeOf cvL) claims.length)
      (claims.map (·.2)))) cvL xs os roots w cv' roots')
    (hacc : w.Accepts fun point ↦
      dot (powers (challengeOf cvL) claims.length) (claims.map fun c ↦ c.1 point))
    (rest : List E) (orest : List Opening) :
    RunsM M (verifyStackedOpening μ r claims) ⟨cv, xs ++ rest, os ++ orest, roots⟩ ()
      ⟨cv', rest, orest, roots'⟩ := by
  unfold verifyStackedOpening
  simp only [verifyWhir_split, Prog.bind_eq]
  refine RunsM.bind (RunsToM.runs (runsToM_sampleE hL) _ _ _) ?_
  refine RunsM.bind (RunsWithM.runs hw rest orest) ?_
  rw [require_pos hacc]
  exact RunsM.ret _ _

/-! ## The deferring verifier accepts -/

/-- **The deferring verifier over the model accepts** the proof made of the phases' words and
openings, when every phase runs over the model, from the seed's answered chain state, as
`verify_sub` runs them (`verifyDeferred_true` over `M`). -/
theorem verifyDeferredWith_true {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    (seed pi : Digest) (c : FixedClaims) {logMem rate : ℕ} {rows : List ℕ}
    (hm1 : 16 ≤ logMem) (hm2 : logMem ≤ 32) (hr1 : 1 ≤ rate) (hr2 : rate ≤ 4)
    (hl : rows.length = 6) (hrows : ∀ n ∈ rows, n ≤ 2 ^ 32)
    (hs1 : 22 ≤ (layoutOf bytecode logMem rows).stackLog)
    (hs2 : (layoutOf bytecode logMem rows).stackLog ≤ 28)
    {x0 x1 : E} {root : Digest} (hroot : (x0, x1) = digestScalars root)
    {cvS cvA cv10 cvB cvC cvG cvT cvF cvR cvL cvW : Digest} {alphas mcs : List E}
    {xsG xsT xsF xsW : List E} {os : List Opening} {roots' : List (Digest × ℕ × ℕ)}
    (hS : M.H (digestBytes seed ++ digestBytes pi) = some cvS)
    (hA : obsAllM M cvS (announce logMem rows rate) = some cvA)
    (h10 : obsAllM M cvA [x0, x1] = some cv10)
    (hB : sqAllM M 4 cv10 = some (alphas, cvB)) (hC : sqCvM M cvB = some cvC)
    {gr : E × List E × List E}
    (hG : RunsToM M (gkrPhase (pushDepth (layoutOf bytecode logMem rows))) cvC xsG gr cvG)
    {bus : BusResult} {claims : List ColumnClaim}
    (hT : RunsToM M (tablesSeg (.claimed c) (layoutOf bytecode logMem rows) pi alphas
      (challengeOf cvC) gr.2.1 gr.2.2) cvG xsT (bus, claims) cvT)
    {fp s : List E}
    (hF : RunsToM M (verifyFlock (.claimed c) (blake2sR1csLogSize +
      (layoutOf bytecode logMem rows).tableLogHeights.getD opBlake2s 0)) cvT xsF (fp, s) cvF)
    (hR : sqAllM M 6 cvF = some (mcs, cvR)) (hL : sqCvM M cvR = some cvL)
    {w : WhirEnd}
    (hW : RunsWithM M (whirOpen (layoutOf bytecode logMem rows).stackLog rate
        (dot (powers (challengeOf cvL) (claims.length + 1))
          (ringTarget s mcs :: claims.map (·.value))))
      cvL xsW os [(root, stackShape (layoutOf bytecode logMem rows).stackLog rate)] w cvW roots')
    (hacc : w.Accepts (stackWeight (layoutOf bytecode logMem rows) claims fp
      (ringCoefficients mcs) (challengeOf cvL))) :
    verifyDeferredWith M.H bytecode seed pi c
      ⟨announce logMem rows rate ++ x0 :: x1 :: (xsG ++ (xsT ++ (xsF ++ xsW))), os⟩ =
        some true := by
  have hcfg : configOk (layoutOf bytecode logMem rows).stackLog rate = true :=
    configOk_window _ (by omega) hs1 _ (by omega) hr1
  have hrun : RunsM M (deferredProgram c bytecode pi)
      ⟨cvS, announce logMem rows rate ++ x0 :: x1 :: (xsG ++ (xsT ++ (xsF ++ xsW))), os, []⟩
      true ⟨cvW, [], [], roots'⟩ := by
    unfold deferredProgram
    rw [verifyExecution_split]
    refine RunsM.bind (a := ()) (RunsM.bind (runs_readSizesM hb hm1 hm2 hr1 hr2 hl hrows
      (by unfold minStackedLog Whir.minLogStack; omega) (by exact hs2) hA _ _ _) ?_) (RunsM.ret _ _)
    generalize layoutOf bytecode logMem rows = L at hG hT hF hW hacc hcfg ⊢
    simp only
    refine RunsM.bind (runs_commitStackM hcfg hroot h10 _ _ _) ?_
    refine RunsM.bind (RunsToM.runs (runsToM_sampleN hB) _ _ _) ?_
    refine RunsM.bind (RunsToM.runs (runsToM_sampleE hC) _ _ _) ?_
    refine RunsM.bind (RunsToM.runs hG _ _ _) ?_
    refine RunsM.bind (RunsToM.runs hT _ _ _) ?_
    refine RunsM.bind (RunsToM.runs hF _ _ _) ?_
    refine RunsM.bind (runs_ringSwitchM _ _ hR _ _ _) ?_
    have hlen : (ringSwitchClaim L (ringTarget s mcs)
        (fun rPrime ↦ ringWeight fp rPrime (ringCoefficients mcs)) ::
          claims.map (·.onStack L)).length = claims.length + 1 := by
      simp
    have hvals : (ringSwitchClaim L (ringTarget s mcs)
        (fun rPrime ↦ ringWeight fp rPrime (ringCoefficients mcs)) ::
          claims.map (·.onStack L)).map (·.2) =
        ringTarget s mcs :: claims.map (·.value) := by
      simp [ringSwitchClaim, ColumnClaim.onStack, Function.comp_def]
    have key := runs_verifyStackedOpeningM
      (claims := ringSwitchClaim L (ringTarget s mcs)
        (fun rPrime ↦ ringWeight fp rPrime (ringCoefficients mcs)) ::
          claims.map (·.onStack L)) hL
      (by rw [hlen, hvals]; exact hW) (by
        convert hacc using 1
        funext x
        simp only [stackWeight, ringSwitchClaim, List.length_cons, List.map_cons]) [] []
    rw [List.append_nil, List.append_nil] at key
    dsimp only [List.nil_append]
    exact key
  unfold verifyDeferredWith runProof
  unfold RunsM at hrun
  simp only [bind, hS, Option.bind_some]
  rw [show run (m := Option) M.H (deferredProgram c bytecode pi) _ = _ from hrun]
  rfl

end
end LeanVM.Guest.B1.VerifySub
