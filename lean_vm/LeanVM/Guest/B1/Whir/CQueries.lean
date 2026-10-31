/-
  LeanVM.Guest.B1.Whir.CQueries

  A level's queries block, honestly: its three calls given, the block holds.
-/

module

public import LeanVM.Guest.B1.Whir.CFold

/-!
# A level's queries block, honestly

`osQueries_complete`: given the three calls of the block on the arguments the block passes them
(`opening_row_weights` on the level's folds and the weights' buffer `wp`, `verify_merkle_cap` on the
level's cap returning the root's cells `r0, r1`, which `level_roots` holds, `opening_queries`
returning `sum`) and the intro message's two words at the cursor, the block holds, the queries'
sum, `c0`, `c1 = sum + c2` and `c2` left in its values.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem rangeVals_sub {σ : Val} {k k' a b : ℕ} {f g : ℕ → E} (h : RangeVals σ k k' f)
    (ha : k ≤ a) (hb : b ≤ k') (hfg : ∀ i, a ≤ i → i < b → f i = g i) : RangeVals σ a b g :=
  fun i h1 h2 ↦ (h i (by omega) (by omega)).trans (hfg i h1 h2)

theorem matVal_congr {σ σ' : Val} {base off k : ℕ} (h : σ' (.n base) = σ (.n base)) :
    matVal σ base off k = matVal σ' base off k := by
  funext i; simp only [matVal, h]

/-- The queries block's number of statements' values: the next free value. -/
theorem osQueries_k (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam lamN : ℕ) (s : OsSt) :
    (osQueries c lvl lv lam lamN s).2.1 =
      (osMat osQbp lv.posOff (osMat osFlags lv.capOff (osMat osCaps (4 * lv.capOff)
        ((osMat osFlags lv.capOff (osMat osCaps (4 * lv.capOff)
          (osMat osFch lv.foldsOff (s.k + 2)).2.2).2.2).2.2 + 2)).2.2).2.2).2.2 + 5 := rfl

/-- The values of a level's queries block. -/
def queriesF (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) (σ : Val)
    (wp r0 r1 sum ic0 ic2 : E) : ℕ → E :=
  let k := s.k
  let fp := osMat osFch lv.foldsOff (k + 2)
  let cp := osMat osCaps (4 * lv.capOff) fp.2.2
  let flp := osMat osFlags lv.capOff cp.2.2
  let r := flp.2.2
  let cp2 := osMat osCaps (4 * lv.capOff) (r + 2)
  let flp2 := osMat osFlags lv.capOff cp2.2.2
  let bp := osMat osQbp lv.posOff flp2.2.2
  let g := bp.2.2
  fun i ↦
    if i = k then gw c.maxIl else if i = k + 1 then wp
    else if i < fp.2.2 then matVal σ osFch lv.foldsOff (k + 2) i
    else if i < cp.2.2 then matVal σ osCaps (4 * lv.capOff) fp.2.2 i
    else if i < r then matVal σ osFlags lv.capOff cp.2.2 i
    else if i = r then r0 else if i = r + 1 then r1
    else if i < cp2.2.2 then matVal σ osCaps (4 * lv.capOff) (r + 2) i
    else if i < flp2.2.2 then matVal σ osFlags lv.capOff cp2.2.2 i
    else if i < g then matVal σ osQbp lv.posOff flp2.2.2 i
    else [gw (lv.queries / (1 + if lvl = 0 then 1 else 0)), sum, ic0, ic2, sum + ic2].getD (i - g) 0

/-- **A level's queries block, honestly.** -/
theorem osQueries_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {lam lamN : ℕ} {s : OsSt} (σ : Val)
    (hb : s.Below) (hk : 34 ≤ s.k) (hl : lam < s.k) (hlN : lamN < s.k)
    (hbo : lv.foldsOff < u128Bound ∧ 4 * lv.capOff < u128Bound ∧ lv.capOff < u128Bound ∧
      lv.posOff < u128Bound ∧ lv.queries / (1 + if lvl = 0 then 1 else 0) < u128Bound)
    (wp r0 r1 sum ic0 ic2 : E)
    (hRW : C ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
      [σ (.n osFch) * gen ^ lv.foldsOff, wp] [])
    (hCap : C ("verify_merkle_cap__L" ++ natStr lv.capDepth)
      [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff] [r0, r1])
    (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) r0)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) r1)
    (hQ : C (osQueriesName lvl lv) [σ (.n osCaps) * gen ^ (4 * lv.capOff),
      σ (.n osFlags) * gen ^ lv.capOff, σ (.n lam), σ (.n lamN), σ (.n osQbp) * gen ^ lv.posOff, wp,
      gen ^ (lv.queries / (1 + if lvl = 0 then 1 else 0))] [sum])
    (hi0 : LoadHolds rd (σ (.n s.cb)) s.co ic0) (hi2 : LoadHolds rd (σ (.n s.cb)) (s.co + 1) ic2) :
    BlkF C rd σ s.k (osQueries c lvl lv lam lamN s).2.1
      (queriesF c lvl lv s σ wp r0 r1 sum ic0 ic2) (osQueries c lvl lv lam lamN s).1
      (fun σ' ↦ σ' (.n (osQueries c lvl lv lam lamN s).2.2.1) = sum ∧
        σ' (.n (osQueries c lvl lv lam lamN s).2.2.2.1) = ic0 ∧
        σ' (.n (osQueries c lvl lv lam lamN s).2.2.2.2.2) = ic2 ∧
        σ' (.n (osQueries c lvl lv lam lamN s).2.2.2.2.1) = sum + ic2 ∧ AgreeBelow s.k σ σ') := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hbo
  set k := s.k with hkdef
  set fp := osMat osFch lv.foldsOff (k + 2)
  set cp := osMat osCaps (4 * lv.capOff) fp.2.2
  set flp := osMat osFlags lv.capOff cp.2.2
  set r := flp.2.2
  set cp2 := osMat osCaps (4 * lv.capOff) (r + 2)
  set flp2 := osMat osFlags lv.capOff cp2.2.2
  set bp := osMat osQbp lv.posOff flp2.2.2
  set g := bp.2.2
  set N0 := lv.queries / (1 + if lvl = 0 then 1 else 0)
  have hFk : osFch < k := by unfold osFch; omega
  have hCk : osCaps < k := by unfold osCaps; omega
  have hLk : osFlags < k := by unfold osFlags; omega
  have hRk : osRoots < k := by unfold osRoots; omega
  have hQk : osQbp < k := by unfold osQbp; omega
  have o1 : k + 2 ≤ fp.2.2 := osMat_next osFch lv.foldsOff (k + 2)
  have o2 : fp.2.2 ≤ cp.2.2 := osMat_next osCaps (4 * lv.capOff) fp.2.2
  have o3 : cp.2.2 ≤ r := osMat_next osFlags lv.capOff cp.2.2
  have o4 : r + 2 ≤ cp2.2.2 := osMat_next osCaps (4 * lv.capOff) (r + 2)
  have o5 : cp2.2.2 ≤ flp2.2.2 := osMat_next osFlags lv.capOff cp2.2.2
  have o6 : flp2.2.2 ≤ g := osMat_next osQbp lv.posOff flp2.2.2
  have hst : (osQueries c lvl lv lam lamN s).1 = osHeap c.maxIl k ++ fp.1 ++
      [.call ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
        natStr (if lvl = 0 then 1 else 0)) [.n fp.2.1, .n (k + 1)] []] ++
      cp.1 ++ flp.1 ++
      [.call ("verify_merkle_cap__L" ++ natStr lv.capDepth) [.n cp.2.1, .n flp.2.1] [.n r, .n (r + 1)],
        .atom (.load (.n r) (.n osRoots) (2 * lvl)),
        .atom (.load (.n (r + 1)) (.n osRoots) (2 * lvl + 1))] ++
      cp2.1 ++ flp2.1 ++ bp.1 ++
      [.atom (.const (.n g) (gw N0)),
        .call (osQueriesName lvl lv) [.n cp2.2.1, .n flp2.2.1, .n lam, .n lamN, .n bp.2.1,
          .n (k + 1), .n g] [.n (g + 1)],
        .atom (.load (.n (g + 2)) (.n s.cb) s.co), .atom (.load (.n (g + 3)) (.n s.cb) (s.co + 1)),
        .atom (.add (.n (g + 4)) (.n (g + 1)) (.n (g + 3)))] := rfl
  have hr : (osQueries c lvl lv lam lamN s).2 = (g + 5, g + 1, g + 2, g + 4, g + 3) := rfl
  rw [hst, hr]
  set f := queriesF c lvl lv s σ wp r0 r1 sum ic0 ic2 with hfdef
  have hfv : ∀ i, f i =
      if i = k then gw c.maxIl else if i = k + 1 then wp
      else if i < fp.2.2 then matVal σ osFch lv.foldsOff (k + 2) i
      else if i < cp.2.2 then matVal σ osCaps (4 * lv.capOff) fp.2.2 i
      else if i < r then matVal σ osFlags lv.capOff cp.2.2 i
      else if i = r then r0 else if i = r + 1 then r1
      else if i < cp2.2.2 then matVal σ osCaps (4 * lv.capOff) (r + 2) i
      else if i < flp2.2.2 then matVal σ osFlags lv.capOff cp2.2.2 i
      else if i < g then matVal σ osQbp lv.posOff flp2.2.2 i
      else [gw N0, sum, ic0, ic2, sum + ic2].getD (i - g) 0 :=
    fun i ↦ rfl
  intro σ' ha hv
  have eF : σ' (.n osFch) = σ (.n osFch) := ha _ (by unfold osFch; omega)
  have eC : σ' (.n osCaps) = σ (.n osCaps) := ha _ (by unfold osCaps; omega)
  have eL : σ' (.n osFlags) = σ (.n osFlags) := ha _ (by unfold osFlags; omega)
  have eR : σ' (.n osRoots) = σ (.n osRoots) := ha _ (by unfold osRoots; omega)
  have eQ : σ' (.n osQbp) = σ (.n osQbp) := ha _ (by unfold osQbp; omega)
  have el : σ' (.n lam) = σ (.n lam) := ha _ hl
  have elN : σ' (.n lamN) = σ (.n lamN) := ha _ hlN
  have ecb : σ' (.n s.cb) = σ (.n s.cb) := ha _ hb.cb
  have hself : ∀ m, AgreeBelow m σ' σ' := fun _ _ _ ↦ rfl
  -- the pointers
  have rF : RangeVals σ' (k + 2) fp.2.2 (matVal σ' osFch (lv.foldsOff) (k + 2)) :=
    rangeVals_sub (k' := g + 5) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [← matVal_congr eF]; rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show i < fp.2.2 by omega,
        ↓reduceIte]
  obtain ⟨okF, vF⟩ := osMat_complete (C := C) (rd := rd) (base := osFch) (off := lv.foldsOff) (k := k + 2) hb1 (by omega) (hself (k + 2)) rF
  have rC : RangeVals σ' (fp.2.2) cp.2.2 (matVal σ' osCaps (4 * lv.capOff) (fp.2.2)) :=
    rangeVals_sub (k' := g + 5) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [← matVal_congr eC]; rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show ¬ i < fp.2.2 by omega,
        show i < cp.2.2 by omega, ↓reduceIte]
  obtain ⟨okC, vC⟩ := osMat_complete (C := C) (rd := rd) (base := osCaps) (off := 4 * lv.capOff) (k := fp.2.2) hb2 (by omega) (hself (fp.2.2)) rC
  have rL : RangeVals σ' (cp.2.2) r (matVal σ' osFlags (lv.capOff) (cp.2.2)) :=
    rangeVals_sub (k' := g + 5) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [← matVal_congr eL]; rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show ¬ i < fp.2.2 by omega,
        show ¬ i < cp.2.2 by omega, show i < r from h2, ↓reduceIte]
  obtain ⟨okL, vL⟩ := osMat_complete (C := C) (rd := rd) (base := osFlags) (off := lv.capOff) (k := cp.2.2) hb3 (by omega) (hself (cp.2.2)) rL
  have rC2 : RangeVals σ' (r + 2) cp2.2.2 (matVal σ' osCaps (4 * lv.capOff) (r + 2)) :=
    rangeVals_sub (k' := g + 5) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [← matVal_congr eC]; rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show ¬ i < fp.2.2 by omega,
        show ¬ i < cp.2.2 by omega, show ¬ i < r by omega, show i ≠ r by omega,
        show i ≠ r + 1 by omega, show i < cp2.2.2 by omega, ↓reduceIte]
  obtain ⟨okC2, vC2⟩ := osMat_complete (C := C) (rd := rd) (base := osCaps) (off := 4 * lv.capOff) (k := r + 2) hb2 (by omega) (hself (r + 2)) rC2
  have rL2 : RangeVals σ' (cp2.2.2) flp2.2.2 (matVal σ' osFlags (lv.capOff) (cp2.2.2)) :=
    rangeVals_sub (k' := g + 5) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [← matVal_congr eL]; rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show ¬ i < fp.2.2 by omega,
        show ¬ i < cp.2.2 by omega, show ¬ i < r by omega, show i ≠ r by omega,
        show i ≠ r + 1 by omega, show ¬ i < cp2.2.2 by omega, show i < flp2.2.2 by omega,
        ↓reduceIte]
  obtain ⟨okL2, vL2⟩ := osMat_complete (C := C) (rd := rd) (base := osFlags) (off := lv.capOff) (k := cp2.2.2) hb3 (by omega) (hself (cp2.2.2)) rL2
  have rQ : RangeVals σ' (flp2.2.2) g (matVal σ' osQbp (lv.posOff) (flp2.2.2)) :=
    rangeVals_sub (k' := g + 5) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [← matVal_congr eQ]; rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show ¬ i < fp.2.2 by omega,
        show ¬ i < cp.2.2 by omega, show ¬ i < r by omega, show i ≠ r by omega,
        show i ≠ r + 1 by omega, show ¬ i < cp2.2.2 by omega, show ¬ i < flp2.2.2 by omega,
        show i < g from h2, ↓reduceIte]
  obtain ⟨okQ, vQ⟩ := osMat_complete (C := C) (rd := rd) (base := osQbp) (off := lv.posOff) (k := flp2.2.2) hb4 (by omega) (hself (flp2.2.2)) rQ
  rw [eF] at vF; rw [eC] at vC vC2; rw [eL] at vL vL2; rw [eQ] at vQ
  -- the single values
  have tail : ∀ j < 5, σ' (.n (g + j)) = [gw N0, sum, ic0, ic2, sum + ic2].getD j 0 := fun j hj ↦ by
    rw [hv (g + j) (by omega) (by omega)]; rw [hfv]
    simp only [show g + j ≠ k by omega, show g + j ≠ k + 1 by omega, show ¬ g + j < fp.2.2 by omega,
      show ¬ g + j < cp.2.2 by omega, show ¬ g + j < r by omega, show g + j ≠ r by omega,
      show g + j ≠ r + 1 by omega, show ¬ g + j < cp2.2.2 by omega,
      show ¬ g + j < flp2.2.2 by omega, show ¬ g + j < g by omega, ↓reduceIte,
      Nat.add_sub_cancel_left]
  have v0 := tail 0 (by omega); have v1 := tail 1 (by omega); have v2 := tail 2 (by omega)
  have v3 := tail 3 (by omega); have v4 := tail 4 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4
  have vk : σ' (.n k) = gw c.maxIl := by rw [hv k le_rfl (by omega)]; simp [hfv]
  have vk1 : σ' (.n (k + 1)) = wp := by rw [hv (k + 1) (by omega) (by omega)]; simp [hfv]
  have vr : σ' (.n r) = r0 := by
    rw [hv r (by omega) (by omega)]; rw [hfv]
    simp only [show r ≠ k by omega, show r ≠ k + 1 by omega, show ¬ r < fp.2.2 by omega,
      show ¬ r < cp.2.2 by omega, lt_irrefl, ↓reduceIte]
  have vr1 : σ' (.n (r + 1)) = r1 := by
    rw [hv (r + 1) (by omega) (by omega)]; rw [hfv]
    simp only [show r + 1 ≠ k by omega, show r + 1 ≠ k + 1 by omega,
      show ¬ r + 1 < fp.2.2 by omega, show ¬ r + 1 < cp.2.2 by omega, show ¬ r + 1 < r by omega,
      show r + 1 ≠ r by omega, ↓reduceIte]
  refine ⟨?_, by rw [v1], by rw [v2], by rw [v3], by rw [v4], ha⟩
  simp only [osHeap, allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds,
    List.map_cons, List.map_nil]
  simp only [and_assoc]
  refine ⟨vk, okF, ?_, okC, okL, ?_, ?_, ?_, okC2, okL2, okQ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vF, vk1]; exact hRW
  · rw [vC, vL, vr, vr1]; exact hCap
  · rw [vr, eR]; exact hr0
  · rw [vr1, eR]; exact hr1
  · exact v0
  · rw [vC2, vL2, el, elN, vQ, vk1, v0, gw_eq hb5, v1]; exact hQ
  · rw [v2, ecb]; exact hi0
  · rw [v3, ecb]; exact hi2
  · rw [v4, v1, v3]

end
end LeanVM.Guest.B1.Whir
