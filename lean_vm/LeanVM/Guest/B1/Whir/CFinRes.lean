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

/-- A level's sum's value: the pairs' sum, plus the last query's weighted at an odd count. -/
def resSum (lv : OsLv) (acc W : E) (D : ℕ → E) (P : E) : E :=
  if lv.queries % 2 = 1 then acc + W * lvRes lv D P else acc

/-- The values after the level's sum: the inner value, the scale, the scaled sum, the new inner. -/
def resEndVals (I L sum : E) : List E := [I, L, L * sum, I + L * sum]

/-- The end of a level's residual: the inner value and the scale read, the new inner value
stored. -/
theorem resEnd_complete {ich ls e sv lvl : ℕ} (σ : Val) (hich : ich < e) (hls : ls < e)
    (hsv : sv < e) {I L : E} (hI : LoadHolds rd (σ (.n ich)) lvl I)
    (hL : LoadHolds rd (σ (.n ls)) lvl L)
    (hout : LoadHolds rd (σ (.n ich)) (lvl + 1) (I + L * σ (.n sv))) :
    BlkF C rd σ e (e + 4) (fun j ↦ (resEndVals I L (σ (.n sv))).getD (j - e) 0)
      [.atom (.load (.n e) (.n ich) lvl), .atom (.load (.n (e + 1)) (.n ls) lvl),
        .atom (.mul (.n (e + 2)) (.n (e + 1)) (.n sv)), .atom (.add (.n (e + 3)) (.n e) (.n (e + 2))),
        .atom (.load (.n (e + 3)) (.n ich) (lvl + 1))]
      (fun σ' ↦ AgreeBelow e σ σ') := by
  intro σ' ha hr
  have V : ∀ j < 4, σ' (.n (e + j)) = (resEndVals I L (σ (.n sv))).getD j 0 := fun j hj ↦ by
    rw [hr _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
  have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
  have v3 := V 3 (by omega)
  simp only [resEndVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3
  refine ⟨?_, ha⟩
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  refine ⟨by rw [v0, ha _ hich]; exact hI, by rw [v1, ha _ hls]; exact hL,
    by rw [v2, v1, ha _ hsv], by rw [v3, v0, v2], by rw [v3, ha _ hich]; exact hout⟩

/-- The value holding a level's sum and the level's last value before its end. -/
def resSumIdx (lvl : ℕ) (lv : OsLv) (bd k : ℕ) : ℕ × ℕ :=
  if lv.queries % 2 = 1 then
    ((osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)).2.2 + 2,
      (osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)).2.2 + 3)
  else (k + 8, k + 9)

/-- The values of a level's residual. -/
def residualF (c : OsCfg) (lvl : ℕ) (lv : OsLv) (bd k : ℕ) (σ : Val) (RC acc P W I L : E)
    (D : ℕ → E) : ℕ → E :=
  seqF σ k (k + 9) (fun j ↦ (resPreVals c (lv.queries / 2) RC acc).getD (j - k) 0) fun σ1 ↦
  seqF σ1 (k + 9) (resSumIdx lvl lv bd k).2
    (if lv.queries % 2 = 1 then resOddF lvl lv bd k σ1 P W D else fun _ ↦ 0) fun σ2 ↦
  fun j ↦ (resEndVals I L (σ2 (.n (resSumIdx lvl lv bd k).1))).getD (j - (resSumIdx lvl lv bd k).2) 0

theorem osResidual_eq (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (k : ℕ) :
    osResidual c ich bd ls lvl lv k =
      ((osHeap (c.maxQ + 1) k ++
        [.atom (.const (.n (k + 2)) (word 0 0 0)), .atom (.load (.n (k + 2)) (.n (k + 1)) 0)] ++
        osLoopCall (c.resLoop lvl) (lv.queries / 2) [osQpos, osQw, bd, k + 1] (k + 3) ++
        [.atom (.load (.n (k + 8)) (.n (k + 1)) (lv.queries / 2))]) ++
        ((if lv.queries % 2 = 1 then
          [.atom (.load (.n (k + 9)) (.n osQpos) (lv.posOff + lv.queries - 1))] ++
            (osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)).1 ++
            [.atom (.load (.n (osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols
                (k + 10)).2.2) (.n osQw) (lvl * c.maxQ + lv.queries - 1)),
              .atom (.mul (.n ((osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols
                (k + 10)).2.2 + 1)) (.n (osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols
                (k + 10)).2.2) (.n (osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols
                (k + 10)).2.1)),
              .atom (.add (.n ((osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols
                (k + 10)).2.2 + 2)) (.n (k + 8)) (.n ((osResQuery (k + 9) bd (lvl * ligColsCap)
                lv.vanish lv.logCols (k + 10)).2.2 + 1)))]
          else []) ++
        [.atom (.load (.n (resSumIdx lvl lv bd k).2) (.n ich) lvl),
          .atom (.load (.n ((resSumIdx lvl lv bd k).2 + 1)) (.n ls) lvl),
          .atom (.mul (.n ((resSumIdx lvl lv bd k).2 + 2)) (.n ((resSumIdx lvl lv bd k).2 + 1))
            (.n (resSumIdx lvl lv bd k).1)),
          .atom (.add (.n ((resSumIdx lvl lv bd k).2 + 3)) (.n (resSumIdx lvl lv bd k).2)
            (.n ((resSumIdx lvl lv bd k).2 + 2))),
          .atom (.load (.n ((resSumIdx lvl lv bd k).2 + 3)) (.n ich) (lvl + 1))]),
        (resSumIdx lvl lv bd k).2 + 4) := by
  unfold osResidual resSumIdx
  split_ifs <;> simp [List.append_assoc]

/-- **A level's residual sum, honestly.** -/
theorem osResidual_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {ich bd ls k : ℕ} (σ : Val)
    (hk : 34 ≤ k) (hich : ich < k) (hbd : bd < k) (hls : ls < k) (hml : 1 ≤ lv.logCols)
    (hn : lv.queries / 2 < u128Bound) (RC acc : E)
    (hL : IsInK (1 + gen ^ (lv.queries / 2)) ∧ (1 + gen ^ (lv.queries / 2) ≠ 0 →
      C (c.resLoop lvl) [1, gen ^ (lv.queries / 2), σ (.n osQpos), σ (.n osQw), σ (.n bd), RC] []))
    (h0 : LoadHolds rd RC 0 0) (hacc : LoadHolds rd RC (lv.queries / 2) acc)
    {P W : E} {D : ℕ → E}
    (hP : lv.queries % 2 = 1 → LoadHolds rd (σ (.n osQpos)) (lv.posOff + lv.queries - 1) P)
    (hD : lv.queries % 2 = 1 → ∀ s < lv.logCols, LoadHolds rd (σ (.n bd)) (lvl * ligColsCap + s) (D s))
    (hW : lv.queries % 2 = 1 → LoadHolds rd (σ (.n osQw)) (lvl * c.maxQ + lv.queries - 1) W)
    {I L : E} (hI : LoadHolds rd (σ (.n ich)) lvl I) (hLs : LoadHolds rd (σ (.n ls)) lvl L)
    (hout : LoadHolds rd (σ (.n ich)) (lvl + 1) (I + L * resSum lv acc W D P)) :
    BlkF C rd σ k (osResidual c ich bd ls lvl lv k).2 (residualF c lvl lv bd k σ RC acc P W I L D)
      (osResidual c ich bd ls lvl lv k).1 (fun σ' ↦ AgreeBelow k σ σ') := by
  rw [osResidual_eq]
  dsimp only
  unfold residualF
  have hpre := osResPre_complete (C := C) (rd := rd) (c := c) (lvl := lvl) (lv := lv) (bd := bd)
    (k := k) σ RC acc hk hbd hn hL h0 hacc
  have hsi : k + 9 ≤ (resSumIdx lvl lv bd k).2 ∧ (resSumIdx lvl lv bd k).1 < (resSumIdx lvl lv bd k).2 := by
    unfold resSumIdx
    have := (osResQ_k (k + 9) bd (lvl * ligColsCap) lv.vanish (lv.logCols - 1) 1 (k + 11) (k + 12)).1
    split_ifs
    · show k + 9 ≤ (osResQ (k + 9) bd (lvl * ligColsCap) lv.vanish (lv.logCols - 1) 1 (k + 11)
        (k + 12)).2.2 + 3 ∧ _
      omega
    · omega
  refine BlkF.then (k1 := k + 9) (by omega) (by omega) hpre fun σ1 _ ⟨h8, h1, ha1⟩ ↦ ?_
  refine BlkF.then (k1 := (resSumIdx lvl lv bd k).2) hsi.1 (by omega)
    (OutA := fun σ' ↦ σ' (.n (resSumIdx lvl lv bd k).1) = resSum lv acc W D P ∧
      AgreeBelow (k + 9) σ1 σ') ?_ fun σ2 _ ⟨hs, ha2⟩ ↦ ?_
  · by_cases hodd : lv.queries % 2 = 1
    · simp only [hodd, ↓reduceIte]
      have := osResOdd_complete (C := C) (rd := rd) (c := c) (lvl := lvl) (lv := lv) (bd := bd) (k := k)
        σ1 hk hbd hml (P := P) (W := W) (D := D)
        (by rw [ha1 _ (show osQpos < k by unfold osQpos; omega)]; exact hP hodd)
        (fun s hs ↦ by rw [ha1 _ hbd]; exact hD hodd s hs)
        (by rw [ha1 _ (show osQw < k by unfold osQw; omega)]; exact hW hodd)
      rw [h8] at this
      have e : resSumIdx lvl lv bd k = ((osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish
          lv.logCols (k + 10)).2.2 + 2, (osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols
          (k + 10)).2.2 + 3) := by simp [resSumIdx, hodd]
      rw [e]
      refine BlkF.mono this fun σ' ⟨hv, ha⟩ ↦ ⟨?_, ha⟩
      rw [hv]; simp [resSum, hodd]
    · simp only [hodd, ↓reduceIte]
      have e : resSumIdx lvl lv bd k = (k + 8, k + 9) := by simp [resSumIdx, hodd]
      rw [e]
      exact BlkF.nil fun σ' ha ↦ ⟨by rw [ha _ (by omega), h8]; simp [resSum, hodd], ha⟩
  · have e2 : ∀ v, v < k → σ2 (.n v) = σ (.n v) := fun v hv ↦
      (ha2 v (by omega)).trans (ha1 v hv)
    refine BlkF.mono (resEnd_complete (C := C) (rd := rd) (ich := ich) (ls := ls)
      (e := (resSumIdx lvl lv bd k).2) (sv := (resSumIdx lvl lv bd k).1) (lvl := lvl) σ2
      (by omega) (by omega) hsi.2 (by rw [e2 _ hich]; exact hI) (by rw [e2 _ hls]; exact hLs)
      (by rw [e2 _ hich, hs]; exact hout)) fun σ' ha3 i hi ↦
        (ha3 i (by omega)).trans ((ha2 i (by omega)).trans (ha1 i hi))

/-- What a level's residual reads and stores, its honest data named. -/
structure ResMem (C : CallRel) (rd : Reader) (σ : Val) (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv)
    (RC acc P W I L : E) (D : ℕ → E) : Prop where
  hml : 1 ≤ lv.logCols
  hn : lv.queries / 2 < u128Bound
  hL : IsInK (1 + gen ^ (lv.queries / 2)) ∧ (1 + gen ^ (lv.queries / 2) ≠ 0 →
    C (c.resLoop lvl) [1, gen ^ (lv.queries / 2), σ (.n osQpos), σ (.n osQw), σ (.n bd), RC] [])
  h0 : LoadHolds rd RC 0 0
  hacc : LoadHolds rd RC (lv.queries / 2) acc
  hP : lv.queries % 2 = 1 → LoadHolds rd (σ (.n osQpos)) (lv.posOff + lv.queries - 1) P
  hD : lv.queries % 2 = 1 → ∀ s < lv.logCols, LoadHolds rd (σ (.n bd)) (lvl * ligColsCap + s) (D s)
  hW : lv.queries % 2 = 1 → LoadHolds rd (σ (.n osQw)) (lvl * c.maxQ + lv.queries - 1) W
  hI : LoadHolds rd (σ (.n ich)) lvl I
  hLs : LoadHolds rd (σ (.n ls)) lvl L
  hout : LoadHolds rd (σ (.n ich)) (lvl + 1) (I + L * resSum lv acc W D P)

/-- The values of every level's residual. -/
def residualsF (c : OsCfg) (bd : ℕ) (RC acc P W I L : ℕ → E) (D : ℕ → ℕ → E) :
    ℕ → List OsLv → ℕ → Val → ℕ → E
  | lvl, lv :: rest, k, σ =>
    seqF σ k (osResidual c 0 bd 0 lvl lv k).2
      (residualF c lvl lv bd k σ (RC lvl) (acc lvl) (P lvl) (W lvl) (I lvl) (L lvl) (D lvl))
      fun σ1 ↦ residualsF c bd RC acc P W I L D (lvl + 1) rest (osResidual c 0 bd 0 lvl lv k).2 σ1
  | _, [], _, _ => fun _ ↦ 0

theorem osResidual_k_eq (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (k : ℕ) :
    (osResidual c ich bd ls lvl lv k).2 = (osResidual c 0 bd 0 lvl lv k).2 := by
  rw [osResidual_eq, osResidual_eq]

theorem osResidual_k (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (k : ℕ) :
    k + 13 ≤ (osResidual c ich bd ls lvl lv k).2 := by
  rw [osResidual_eq]
  have := (osResQ_k (k + 9) bd (lvl * ligColsCap) lv.vanish (lv.logCols - 1) 1 (k + 11) (k + 12)).1
  unfold resSumIdx
  split_ifs
  · show k + 13 ≤ (osResQ (k + 9) bd (lvl * ligColsCap) lv.vanish (lv.logCols - 1) 1 (k + 11)
      (k + 12)).2.2 + 3 + 4
    omega
  · simp

theorem osResiduals_k (c : OsCfg) (ich bd ls : ℕ) : ∀ (lvl : ℕ) (levels : List OsLv) (k : ℕ),
    k ≤ (osResiduals c ich bd ls lvl levels k).2
  | _, [], _ => le_rfl
  | lvl, lv :: rest, k => by
    simp only [osResiduals]
    have := osResidual_k c ich bd ls lvl lv k
    have := osResiduals_k c ich bd ls (lvl + 1) rest (osResidual c ich bd ls lvl lv k).2
    omega

/-- **Every level's residual sum, honestly.** -/
theorem osResiduals_complete {c : OsCfg} {ich bd ls : ℕ} (RC acc P W I L : ℕ → E)
    (D : ℕ → ℕ → E) : ∀ (levels : List OsLv) (lvl k : ℕ) (σ : Val), 34 ≤ k → ich < k → bd < k →
      ls < k → (∀ i (hi : i < levels.length), ResMem C rd σ c ich bd ls (lvl + i) levels[i]
        (RC (lvl + i)) (acc (lvl + i)) (P (lvl + i)) (W (lvl + i)) (I (lvl + i)) (L (lvl + i))
        (D (lvl + i))) →
      BlkF C rd σ k (osResiduals c ich bd ls lvl levels k).2
        (residualsF c bd RC acc P W I L D lvl levels k σ) (osResiduals c ich bd ls lvl levels k).1
        (fun σ' ↦ AgreeBelow k σ σ')
  | [], lvl, k, σ, _, _, _, _, _ => by
    simp only [osResiduals]; exact BlkF.nil fun _ h ↦ h
  | lv :: rest, lvl, k, σ, hk, hich, hbd, hls, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hA := osResidual_complete (C := C) (rd := rd) (c := c) (lvl := lvl) (lv := lv) (ich := ich)
      (bd := bd) (ls := ls) (k := k) σ hk hich hbd hls h0.hml h0.hn (RC lvl) (acc lvl) h0.hL h0.h0
      h0.hacc h0.hP h0.hD h0.hW h0.hI h0.hLs h0.hout
    simp only [osResiduals, residualsF]
    rw [← osResidual_k_eq c ich bd ls lvl lv k]
    have hk1 := osResidual_k c ich bd ls lvl lv k
    have hk2 := osResiduals_k c ich bd ls (lvl + 1) rest (osResidual c ich bd ls lvl lv k).2
    refine BlkF.then (k1 := (osResidual c ich bd ls lvl lv k).2) (by omega) hk2 hA
      fun σ1 _ ha1 ↦ ?_
    refine BlkF.mono (osResiduals_complete RC acc P W I L D rest (lvl + 1) _ σ1 (by omega) (by omega)
      (by omega) (by omega) fun i hi ↦ ?_) fun σ' ha2 i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)
    have := h (i + 1) (by simp; omega)
    rw [show lvl + (i + 1) = lvl + 1 + i by ring] at this
    have e : ∀ v, v < k → σ1 (.n v) = σ (.n v) := ha1
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := this
    exact ⟨g1, g2, by
      rw [e _ (show osQpos < k by unfold osQpos; omega), e _ (show osQw < k by unfold osQw; omega),
        e _ hbd]; exact g3, g4, g5,
      fun h ↦ by rw [e _ (show osQpos < k by unfold osQpos; omega)]; exact g6 h,
      fun h ↦ by rw [e _ hbd]; exact g7 h,
      fun h ↦ by rw [e _ (show osQw < k by unfold osQw; omega)]; exact g8 h,
      by rw [e _ hich]; exact g9, by rw [e _ hls]; exact g10, by rw [e _ hich]; exact g11⟩

end
end LeanVM.Guest.B1.Whir
