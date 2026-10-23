/-
  LeanVM.Guest.B1.Whir.CFinRes

  A level's residual sum, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinResQ
public import LeanVM.Guest.B1.Whir.Residuals

/-!
# A level's residual sum, honestly

`osResidual_complete`: the chain's buffer allocated at `RC` (its first word zero, its word `n` the
pairs' sum `acc`), the loop called (a hypothesis on the call relation), at an odd count the last
query inline (`osResQuery_complete`) weighted, `inner[lvl + 1] = inner[lvl] + scale·sum` stored.
`osResiduals_complete`: every level.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The values before the last query: the buffer, its first word, the loop's call, the pairs' sum. -/
def resPreVals (c : OsCfg) (n : ℕ) (RC acc : E) : List E :=
  [gw (c.maxQ + 1), RC, word 0 0 0, word 1 0 0, gw n, word 1 0 0 + gw n, word 1 0 0, gw n, acc]

/-- **The part before the last query, honestly.** -/
theorem osResPre_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {bd k : ℕ} (σ : Val) (RC acc : E)
    (hk : 34 ≤ k) (hbd : bd < k) (hn : lv.queries / 2 < u128Bound)
    (hL : IsInK (1 + gen ^ (lv.queries / 2)) ∧ (1 + gen ^ (lv.queries / 2) ≠ 0 →
      C (c.resLoop lvl) [1, gen ^ (lv.queries / 2), σ (.n osQpos), σ (.n osQw), σ (.n bd), RC] []))
    (h0 : LoadHolds rd RC 0 0) (hacc : LoadHolds rd RC (lv.queries / 2) acc) :
    BlkF C rd σ k (k + 9) (fun j ↦ (resPreVals c (lv.queries / 2) RC acc).getD (j - k) 0)
      (osHeap (c.maxQ + 1) k ++
        [.atom (.const (.n (k + 2)) (word 0 0 0)), .atom (.load (.n (k + 2)) (.n (k + 1)) 0)] ++
        osLoopCall (c.resLoop lvl) (lv.queries / 2) [osQpos, osQw, bd, k + 1] (k + 3) ++
        [.atom (.load (.n (k + 8)) (.n (k + 1)) (lv.queries / 2))])
      (fun σ' ↦ σ' (.n (k + 8)) = acc ∧ σ' (.n (k + 1)) = RC ∧ AgreeBelow k σ σ') := by
  intro σ' ha hr
  have V : ∀ j < 9, σ' (.n (k + j)) = (resPreVals c (lv.queries / 2) RC acc).getD j 0 :=
    fun j hj ↦ by rw [hr _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
  have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
  have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
  have v6 := V 6 (by omega); have v7 := V 7 (by omega); have v8 := V 8 (by omega)
  simp only [resPreVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8
  refine ⟨?_, v8, v1, ha⟩
  have hgn : gw (lv.queries / 2) = gen ^ (lv.queries / 2) := gw_eq hn
  simp only [osHeap, osLoopCall, allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds,
    List.map_cons, List.map_nil, and_assoc]
  have eq1 : σ' (.n osQpos) = σ (.n osQpos) := ha _ (show osQpos < k by unfold osQpos; omega)
  have eq2 : σ' (.n osQw) = σ (.n osQw) := ha _ (show osQw < k by unfold osQw; omega)
  have eq3 := ha _ hbd
  refine ⟨v0, v2, by rw [v2, v1, word_zero]; exact h0, v3, v4, by rw [v5, v3, v4], v6, v7,
    by rw [v5, word_one, hgn]; exact hL.1, fun h ↦ ?_, by rw [v8, v1]; exact hacc⟩
  rw [v5, word_one, hgn] at h
  rw [v6, v7, v1, word_one, hgn, eq1, eq2, eq3]
  exact hL.2 h

/-- The values of the last query of an odd count. -/
def resOddF (lvl : ℕ) (lv : OsLv) (bd k : ℕ) (σ : Val) (P W : E) (D : ℕ → E) : ℕ → E :=
  let r := osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)
  seqF σ (k + 9) (k + 10) (fun _ ↦ P) fun σ1 ↦
  seqF σ1 (k + 10) r.2.2 (resQueryF lv.vanish lv.logCols (k + 9) (k + 10) σ1 D) fun σ2 ↦
  fun j ↦ [W, W * σ2 (.n r.2.1), σ2 (.n (k + 8)) + W * σ2 (.n r.2.1)].getD (j - r.2.2) 0

/-- **The last query of an odd count, honestly.** -/
theorem osResOdd_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {bd k : ℕ} (σ : Val) (hk : 34 ≤ k)
    (hbd : bd < k) (hml : 1 ≤ lv.logCols) {P W : E} {D : ℕ → E}
    (hP : LoadHolds rd (σ (.n osQpos)) (lv.posOff + lv.queries - 1) P)
    (hD : ∀ s < lv.logCols, LoadHolds rd (σ (.n bd)) (lvl * ligColsCap + s) (D s))
    (hW : LoadHolds rd (σ (.n osQw)) (lvl * c.maxQ + lv.queries - 1) W) :
    BlkF C rd σ (k + 9)
      ((osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)).2.2 + 3)
      (resOddF lvl lv bd k σ P W D)
      ([.atom (.load (.n (k + 9)) (.n osQpos) (lv.posOff + lv.queries - 1))] ++
        (osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)).1 ++
        [.atom (.load (.n (osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)).2.2)
            (.n osQw) (lvl * c.maxQ + lv.queries - 1)),
          .atom (.mul (.n ((osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)).2.2 + 1))
            (.n (osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)).2.2)
            (.n (osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)).2.1)),
          .atom (.add (.n ((osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)).2.2 + 2))
            (.n (k + 8))
            (.n ((osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)).2.2 + 1)))])
      (fun σ' ↦ σ' (.n ((osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols
          (k + 10)).2.2 + 2)) = σ (.n (k + 8)) + W * lvRes lv D P ∧ AgreeBelow (k + 9) σ σ') := by
  set r := osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10) with hr
  have hrk : r.2.2 = k + 10 + 2 + 6 * (lv.logCols - 1) :=
    (osResQ_k (k + 9) bd (lvl * ligColsCap) lv.vanish (lv.logCols - 1) 1 (k + 11) (k + 12)).1
  have hr1 : r.2.1 < r.2.2 := by
    have := osResQ_k (k + 9) bd (lvl * ligColsCap) lv.vanish (lv.logCols - 1) 1 (k + 11) (k + 12)
    show (osResQ (k + 9) bd (lvl * ligColsCap) lv.vanish (lv.logCols - 1) 1 (k + 11) (k + 12)).2.1 < _
    rcases Nat.eq_zero_or_pos (lv.logCols - 1) with h | h
    · rw [this.2.1 h, hrk]; omega
    · rw [this.2.2 h, hrk]; omega
  unfold resOddF
  rw [← hr, List.append_assoc]
  refine BlkF.then (k1 := k + 10) (by omega) (by omega)
    (load_complete σ (show osQpos < k + 9 by unfold osQpos; omega) hP) fun σ1 _ ⟨h1, ha1⟩ ↦ ?_
  have hQ := osResQuery_complete (C := C) (rd := rd) (pos := k + 9) (bd := bd) (row := lvl * ligColsCap)
    (vo := lv.vanish) (n := lv.logCols) (k := k + 10) (D := D) σ1 hml (by omega) (by omega)
    (by omega) (fun s hs ↦ by rw [ha1 bd (by omega)]; exact hD s hs)
  rw [h1] at hQ
  refine BlkF.then (k1 := r.2.2) (by omega) (by omega) hQ fun σ2 _ ⟨hv, ha2⟩ ↦ ?_
  intro σ' ha hrv
  have V : ∀ j < 3, σ' (.n (r.2.2 + j)) = [W, W * σ2 (.n r.2.1),
      σ2 (.n (k + 8)) + W * σ2 (.n r.2.1)].getD j 0 := fun j hj ↦ by
    rw [hrv _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
  have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2
  have e8 : σ2 (.n (k + 8)) = σ (.n (k + 8)) := (ha2 _ (by omega)).trans (ha1 _ (by omega))
  have er1 : σ' (.n r.2.1) = σ2 (.n r.2.1) := ha _ hr1
  refine ⟨?_, ?_, fun i hi ↦ (ha i (by omega)).trans ((ha2 i (by omega)).trans (ha1 i hi))⟩
  · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    refine ⟨?_, by rw [v1, v0, er1], by rw [v2, v1, ha _ (show k + 8 < r.2.2 by omega)]⟩
    rw [v0, ha _ (show osQw < r.2.2 by unfold osQw; omega), ha2 _ (show osQw < k + 10 by unfold osQw; omega),
      ha1 _ (show osQw < k + 9 by unfold osQw; omega)]
    exact hW
  · rw [v2, e8, hv]

end
end LeanVM.Guest.B1.Whir
