/-
  LeanVM.Guest.B1.Whir.Residuals

  A level's residual sum: the residual loop over its query pairs, the odd query inline, the
  running `inner` advanced by the level's scale times the sum.
-/

module

public import LeanVM.Guest.B1.Whir.ResLoop

/-!
# The residual sums (G:1575-1598)

`osResidual_sound`: level `lvl`'s block reads its positions `P` and weights `W`, its row's words
`D` in `basis_d`, its scale `L` in `level_scale`, and stores
`inner[lvl + 1] = inner[lvl] + L·Σ_{i<q} W_i·R(P_i)`, `R` the level's `residual_query`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- A level's residual at a position. -/
abbrev lvRes (lv : OsLv) (D : ℕ → E) (p : E) : E :=
  residualProd (osVals lv.vanish lv.logCols) p D lv.logCols

/-- **A level's residual sum** (G:1575-1598). -/
theorem osResidual_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {ich bd ls k : ℕ}
    (hloop : FnIs (c.resLoop lvl) (osParams 6) (resLoopBody c lvl lv (c.resLoop lvl)))
    (hml : 1 ≤ lv.logCols) (hpo : lv.posOff < u128Bound) (hwo : lvl * c.maxQ < u128Bound)
    (hq2 : 2 ≤ lv.queries) (hqo : lv.queries / 2 < ordG) (hqu : lv.queries / 2 < u128Bound)
    {D P W : ℕ → E} {I L : E}
    (hD : ∀ s < lv.logCols, LoadHolds rd (σ (.n bd)) (lvl * ligColsCap + s) (D s))
    (hP : ∀ i < lv.queries, LoadHolds rd (σ (.n osQpos)) (lv.posOff + i) (P i))
    (hW : ∀ i < lv.queries, LoadHolds rd (σ (.n osQw)) (lvl * c.maxQ + i) (W i))
    (hI : LoadHolds rd (σ (.n ich)) lvl I) (hL : LoadHolds rd (σ (.n ls)) lvl L)
    (hok : AllOk (coreProgram.Rel rd) rd σ (osResidual c ich bd ls lvl lv k).1) :
    LoadHolds rd (σ (.n ich)) (lvl + 1)
      (I + L * ∑ i ∈ Finset.range lv.queries, W i * lvRes lv D (P i)) := by
  obtain ⟨fn, hfind, hps, hbody⟩ := hloop
  set n := lv.queries / 2
  -- the loop's part, common to both parities
  have hpre : ∀ (evs rest : List Stmt),
      AllOk (coreProgram.Rel rd) rd σ (osHeap (c.maxQ + 1) k ++
        [.atom (.const (.n (k + 2)) (word 0 0 0)), .atom (.load (.n (k + 2)) (.n (k + 1)) 0)] ++
        osLoopCall (c.resLoop lvl) n [osQpos, osQw, bd, k + 1] (k + 3) ++
        [.atom (.load (.n (k + 8)) (.n (k + 1)) n)] ++ evs ++ rest) →
      AllOk (coreProgram.Rel rd) rd σ (evs ++ rest) ∧
        σ (.n (k + 8)) = ∑ i ∈ Finset.range (2 * n), W i * lvRes lv D (P i) := by
    intro evs rest h
    simp only [allOk_append] at h
    obtain ⟨⟨⟨⟨⟨-, hz⟩, hc⟩, hl⟩, hev⟩, hrest⟩ := h
    refine ⟨allOk_append.mpr ⟨hev, hrest⟩, ?_⟩
    simp only [osLoopCall, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons,
      List.map_nil] at hz hc hl
    obtain ⟨z2, s2⟩ := hz
    obtain ⟨c3, c4, a5, c6, c7, -, hcall⟩ := hc
    have hgn : gw n = gen ^ n := gw_eq hqu
    have hit := resLoop_sound hfind c lvl lv hps hbody hml hpo hwo (D := D) (n := n)
      (by omega) hqo (σ (.n osQpos)) (σ (.n osQw)) (σ (.n bd)) (σ (.n (k + 1))) hD (by
        rw [a5, c3, c4, c6, c7, hgn, word_one] at hcall
        exact hcall)
    rw [z2, word_zero] at s2
    have := resChain (P := P) (W := W) (fun i hi ↦ hP i (by omega)) (fun i hi ↦ hW i (by omega))
      s2 hit n le_rfl
    exact loadHolds_unique hl this
  rcases Nat.mod_two_eq_zero_or_one lv.queries with he | ho
  · have hc : (lv.queries % 2 = 1) = False := eq_false (by omega)
    simp only [osResidual, hc, ↓reduceIte] at hok
    obtain ⟨hrest, hsum⟩ := hpre [] _ hok
    simp only [List.nil_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hrest
    obtain ⟨l0, l1, m2, a3, s4⟩ := hrest
    rw [a3, m2, loadHolds_unique l0 hI, loadHolds_unique l1 hL, hsum,
      show 2 * n = lv.queries by omega] at s4
    exact s4
  · have hc : (lv.queries % 2 = 1) = True := eq_true ho
    simp only [osResidual, hc, ↓reduceIte] at hok
    obtain ⟨hrest, hsum⟩ := hpre _ _ hok
    simp only [allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds,
      List.cons_append, List.nil_append, and_assoc] at hrest
    obtain ⟨lp, hr, lw, m1, a2, l0, l1, m2, a3, s4⟩ := hrest
    have hD' : ∀ s < lv.logCols, LoadHolds rd (σ (.n bd)) (lvl * ligColsCap + s) (D s) := hD
    have hv := osResQuery_val hml hD' hr
    have hpq := loadHolds_unique lp (by
      have := hP (lv.queries - 1) (by omega)
      rwa [← Nat.add_sub_assoc (by omega)] at this)
    have hwq := loadHolds_unique lw (by
      have := hW (lv.queries - 1) (by omega)
      rwa [← Nat.add_sub_assoc (by omega)] at this)
    rw [a3, m2, loadHolds_unique l0 hI, loadHolds_unique l1 hL, a2, m1, hsum, hv, hpq, hwq] at s4
    have hsplit : ∀ f : ℕ → E, ∑ i ∈ Finset.range lv.queries, f i =
        ∑ i ∈ Finset.range (2 * n), f i + f (lv.queries - 1) := by
      intro f
      obtain ⟨m, hm⟩ : ∃ m, lv.queries = m + 1 := ⟨lv.queries - 1, by omega⟩
      have h2 : 2 * n = m := by omega
      rw [hm, Finset.sum_range_succ, h2, Nat.add_sub_cancel]
    rw [hsplit]
    exact s4

end
end LeanVM.Guest.B1.Whir
