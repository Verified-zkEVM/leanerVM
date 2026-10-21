/-
  LeanVM.Guest.B1.Whir.StackedLevelsM

  All the levels of `open_stacked` under a hash model against `whirLevelsOpen` over the model's
  answered hash, up to the tail.
-/

module

public import LeanVM.Guest.B1.Whir.StackedLevelM
public import LeanVM.Guest.B1.Whir.StackedLevels

/-!
# The levels of the stacked opening under a hash model (TRIAGE #36)

`osLevels_soundM`: by induction over the levels, `osLevel_soundM` at each; the guest's levels read
words and openings over which `whirLevelsOpen` runs over `M.H` to its tail (`osTailOpen`), from
the state the guest leaves after its last level (`OsEndInv`), whatever the tail then reads.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {M : HashModel} {rd : Reader} {σ : Val}

/-- **The levels under a hash model** (G:1096-1213 at every level): from level `lvl` with `j`
levels after it, the guest's levels read words `ys` and openings `os`; from the state the guest
leaves, any run of the tail over `M.H` is a run of `whirLevelsOpen` from level `lvl`. -/
theorem osLevels_soundM {C : CallRel} (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) {cfg : OsCfg}
    {logN lane : ℕ} {Lall : List Whir.Level}
    (hlen : Lall.length = cfg.levels.length)
    (hspec : ∀ i < Lall.length, LvSpec cfg logN i (Lall.getD i default) (Lall.drop (i + 1)))
    (hcall : ∀ i < Lall.length, LvCalleesM M rd cfg i)
    {wq : ℕ → List E → List E → List Opening}
    (hqW : ∀ i < Lall.length, SoundQueriesWCM M C rd (cfg.lv i).queriesFn (if i = 0 then 1 else 0)
      (2 ^ (cfg.lv i).folds) (cfg.lv i).depth (cfg.lv i).capDepth (wq i))
    (hfin : ∀ a r, coreProgram.RelB M.sem rd cfg.finalMsg a r →
      MeaningOpeningFinalMessageWith M cfg.yrLen rd a r)
    {cur : E} {kret : List E → Prop} :
    ∀ (j lvl : ℕ) (st : OsSt) (cv : Digest) (xs : List E) (w : WhirState)
      (roots : List (Digest × ℕ × ℕ)), lvl + j + 1 = Lall.length →
      OsLvInv rd σ cfg logN cur lvl st cv xs w roots →
      Stmt.HoldsListB M.sem C rd σ (osLevels cfg lvl (cfg.levels.drop lvl) st).1 True kret →
      ∃ (ys : List E) (os : List Opening) (cvL : Digest) (wL : WhirState)
        (rootsL : List (Digest × ℕ × ℕ)) (residual : List E),
        os = osLevelsOs cfg lvl (cfg.levels.drop lvl) st σ wq ∧
        OsEndInv rd σ cfg logN cur Lall.length (osLevels cfg lvl (cfg.levels.drop lvl) st).2 cvL
          (xs ++ ys) wL ∧
        residual.length = cfg.yrLen ∧ ReadsAt rd (σ (.n osFmsg)) residual ∧
        ∀ (r : List E) (o : List Opening) (we : WhirEnd) (st' : St),
          RunsM M (osTailOpen (logN - osLevelF cfg (Lall.length - 1)) lane wL residual)
            ⟨cvL, r, o, rootsL⟩ we st' →
          RunsM M (whirLevelsOpen logN lane lvl (Lall.drop lvl) w) ⟨cv, ys ++ r, os ++ o, roots⟩ we st' := by
  intro j
  induction j with
  | zero =>
    intro lvl st cv xs w roots hj hinv h
    have hl : lvl < Lall.length := by omega
    rw [List.drop_eq_getElem_cons (by omega), osLevels_cons, show cfg.levels[lvl] = cfg.lv lvl by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show lvl < cfg.levels.length by omega)]]
      at h ⊢
    have hrest : cfg.levels.drop (lvl + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hrest] at h ⊢
    simp only [osLevels, List.append_nil] at h ⊢
    have hLrest : Lall.drop (lvl + 1) = [] := List.drop_eq_nil_of_le (by omega)
    have hs := hspec lvl hl
    rw [hLrest] at hs
    obtain ⟨ys1, cv1, w1, chs, hrun1, hw1l, ysM, cv2, residual, pending, roots2, hrunM, ysQ, os, cv',
      w', hosE, hrunQ, hlast, -⟩ := osLevel_soundM hC hs (hcall lvl hl) (hqW lvl hl) hfin hinv h
    obtain ⟨hresl, hres, hend⟩ := hlast rfl
    refine ⟨ys1 ++ ysM ++ ysQ, os, cv', w', roots2, residual, by simp [osLevelsOs, hosE],
      by simpa [hlen, show lvl + 1 = Lall.length by omega]
      using hend, hresl, hres, fun r o we st' htail => ?_⟩
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl], hLrest, os_whirLevelsOpen_cons]
    rw [show Lall.length - 1 = lvl by omega] at htail
    rw [← hw1l] at hrunM hrunQ htail
    simp only [List.append_assoc]
    refine RunsM.bind (hrun1.runsM _ _ _) ?_
    refine RunsM.bind (hrunM _ _) ?_
    refine RunsM.bind (hrunQ _ _) ?_
    exact htail
  | succ j ih =>
    intro lvl st cv xs w roots hj hinv h
    have hl : lvl < Lall.length := by omega
    rw [List.drop_eq_getElem_cons (by omega), osLevels_cons, show cfg.levels[lvl] = cfg.lv lvl by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show lvl < cfg.levels.length by omega)]]
      at h ⊢
    rw [holdsListB_append] at h
    obtain ⟨h1, h2⟩ := holdsListB_true_of (osLevel_noRet _ _ _ _) h
    have hs := hspec lvl hl
    have hne : Lall.drop (lvl + 1) ≠ [] := by
      intro he; have := congrArg List.length he; simp at this; omega
    obtain ⟨ys1, cv1, w1, chs, hrun1, hw1l, ysM, cv2, residual, pending, roots2, hrunM, ysQ, os, cv',
      w', hosE, hrunQ, -, hmid⟩ := osLevel_soundM hC hs (hcall lvl hl) (hqW lvl hl) hfin hinv h1
    obtain ⟨ys, os', cvL, wL, rootsL, res, hosE', hend, hresl, hres, hrun⟩ :=
      ih (lvl + 1) _ cv' _ w' roots2 (by omega) (hmid hne) h2
    refine ⟨ys1 ++ ysM ++ ysQ ++ ys, os ++ os', cvL, wL, rootsL, res, by rw [osLevelsOs, hosE, hosE'],
      by simpa using hend, hresl, hres, fun r o we st' htail => ?_⟩
    obtain ⟨L2, rest2, hrest2⟩ : ∃ L2 rest2, Lall.drop (lvl + 1) = L2 :: rest2 := by
      cases h' : Lall.drop (lvl + 1) with
      | nil => exact absurd h' hne
      | cons a b => exact ⟨a, b, rfl⟩
    have hrun' := hrun r o we st' htail
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl], os_whirLevelsOpen_cons]
    rw [← hw1l] at hrunM hrunQ
    simp only [List.append_assoc]
    refine RunsM.bind (hrun1.runsM _ _ _) ?_
    refine RunsM.bind (hrunM _ _) ?_
    refine RunsM.bind (hrunQ _ _) ?_
    rw [hrest2] at hrun' ⊢
    exact hrun'

end
end LeanVM.Guest.B1
