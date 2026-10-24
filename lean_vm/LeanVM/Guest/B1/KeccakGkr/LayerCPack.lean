/-
  LeanVM.Guest.B1.KeccakGkr.LayerCPack

  A layer's pack rounds, honestly: the round records in memory give every iteration's meaning
  (`PackStep`) and, with `y` odd, the last round's (`MeaningKeccakRound`).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCHon

/-!
# The pack rounds, honestly

With the records' buffer (`recWords`), the claim's point, the stream words and the challenges
(`chs`) in memory:

* `recWords_rec`: record `j` is a `RoundRec`;
* `packStep_honest`: iteration `j < ⌊y/2⌋` of the pack loop has its meaning;
* `round_honest`: with `y` odd, `keccak_round` at record `⌊y/2⌋` has its meaning.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem flatPairs_get : ∀ (ms : List (E × E)) (k : ℕ) (hk : k < ms.length),
    (ms.flatMap fun m ↦ [m.1, m.2]).getD (2 * k) 0 = ms[k].1 ∧
      (ms.flatMap fun m ↦ [m.1, m.2]).getD (2 * k + 1) 0 = ms[k].2
  | [], _, hk => absurd hk (by simp)
  | m :: ms, 0, _ => by simp
  | m :: ms, k + 1, hk => by
    have := flatPairs_get ms k (by simpa using hk)
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem_cons_succ]
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, show 2 * k + 1 + 1 + 1 = 2 * k + 1 + 1 + 1 from rfl,
      List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
    exact this

theorem kk_readsAt_getD {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ} (hk : k < xs.length) :
    LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

namespace LayerData

variable {D : LayerData} {first : ℕ}

/-- The pack rounds' messages, read at `cur·g^47`. -/
theorem xs_packReads (hpl : D.product.length = 47) {cur : E} (hxs : ReadsAt rd cur D.xs) {k : ℕ}
    (hk : k < D.packMsgs.length) :
    LoadHolds rd cur (47 + 2 * k) (D.packMsgs[k]).1 ∧
      LoadHolds rd cur (47 + 2 * k + 1) (D.packMsgs[k]).2 := by
  have h := hxs
  simp only [xs, List.append_assoc] at h
  rw [readsAt_append, hpl] at h
  obtain ⟨-, h⟩ := h
  rw [readsAt_append] at h
  obtain ⟨h, -⟩ := h
  obtain ⟨h1, h2⟩ := flatPairs_get D.packMsgs k hk
  have hl := flatMap_pairs_length D.packMsgs
  have l1 := kk_readsAt_getD h (k := 2 * k) (by omega)
  have l2 := kk_readsAt_getD h (k := 2 * k + 1) (by omega)
  rw [h1, loadHolds_mul_gen_pow] at l1
  rw [h2, loadHolds_mul_gen_pow] at l2
  exact ⟨l1, by rwa [Nat.add_assoc]⟩

theorem xs_length (hpl : D.product.length = 47) (hpm : D.packMsgs.length = D.y)
    (hlm : D.localMsgs.length = 11) : D.xs.length = 47 + 2 * D.y + 36 := by
  simp only [xs, List.length_append, hpl, flatMap_pairs_length, flatMap_triples_length, hpm, hlm,
    List.length_cons, List.length_nil]

/-- **Record `j` in memory.** -/
theorem recWords_rec {base cur : E} (h : ReadsAt rd base (D.recWords first cur)) {j : ℕ}
    (hj : j < 16) (hjy : j ≤ D.y / 2 + D.y % 2) :
    RoundRec rd (base * gen ^ j) 0 (D.run first (D.recK j)).2.cap (D.recCur cur j)
      (D.run first (D.recK j)).1.1 (D.run first (D.recK j)).1.2.1 := by
  have field : ∀ f < 8, LoadHolds rd (base * gen ^ j) (16 * f) (D.recField first cur f j) := by
    intro f hf
    rw [loadHolds_mul_gen_pow]
    have hl : j + 16 * f < (D.recWords first cur).length := by simp [recWords]; omega
    have := h _ hl
    simp only [recWords, List.getElem_map, List.getElem_range] at this
    rw [show (j + 16 * f) % 16 = j by omega, show (j + 16 * f) / 16 = f by omega] at this
    simp only [hjy, ↓reduceIte] at this
    exact this
  obtain ⟨⟨hcl, -⟩, -⟩ := run_cap (D := D) (first := first) (D.recK j)
  refine ⟨⟨hcl, fun i hi ↦ ?_⟩, ?_, ?_, ?_⟩
  · have := field i (by omega)
    simp only [recField, show i < 5 by omega, ↓reduceIte] at this
    rw [List.getD_eq_getElem _ _ hi] at this
    rwa [zero_add, show i * krCap = 16 * i by simp [krCap]; ring]
  · have := field 5 (by norm_num)
    simpa [recField, krCap] using this
  · have := field 6 (by norm_num)
    simpa [recField, krCap] using this
  · have := field 7 (by norm_num)
    simpa [recField, krCap] using this

/-- A record at `rec·g^(j+1)` is the one written at offset `1` from `rec·g^j`. -/
theorem roundRec_pred {rec : E} {j : ℕ} {cap : List E} {cur cl sc : E}
    (h : RoundRec rd (rec * gen ^ (j + 1)) 0 cap cur cl sc) :
    RoundRec rd (rec * gen ^ j) 1 cap cur cl sc := by
  obtain ⟨⟨hl, hc⟩, h1, h2, h3⟩ := h
  refine ⟨⟨hl, fun i hi => ?_⟩, ?_, ?_, ?_⟩
  · have := hc i hi
    rw [show 1 + i * krCap = 1 + (0 + i * krCap) by omega, loadHolds_rec_succ]
    exact this
  · rw [show 1 + 5 * krCap = 1 + (0 + 5 * krCap) by omega, loadHolds_rec_succ]; exact h1
  · rw [show 1 + 6 * krCap = 1 + (0 + 6 * krCap) by omega, loadHolds_rec_succ]; exact h2
  · rw [show 1 + 7 * krCap = 1 + (0 + 7 * krCap) by omega, loadHolds_rec_succ]; exact h3

theorem getD_append_two {l : List E} {a b : E} {n : ℕ} (hl : l.length = n) :
    (l ++ [a, b]).getD n 0 = a ∧ (l ++ [a, b]).getD (n + 1) 0 = b := by
  subst hl
  simp

/-- **An iteration of the pack loop, honestly.** -/
theorem packStep_honest (hpl : D.product.length = 47) (hpm : D.packMsgs.length = D.y)
    {rec pp pt cur : E} (hrec : ReadsAt rd rec (D.recWords first cur))
    (hpp : ReadsAt rd pp D.c.point) (hxs : ReadsAt rd cur D.xs)
    (hpt : ReadsAt rd pt (D.chs first)) (hy30 : D.y ≤ 30) {j : ℕ} (hj : j < D.y / 2) :
    PackStep rd rec pp pt (gen ^ j) := by
  have hy : D.y = D.c.point.length := rfl
  have hk0 : D.recK j = 2 * j := by unfold recK; omega
  have hk1 : D.recK (j + 1) = 2 * (j + 1) := by unfold recK; omega
  have r0 := recWords_rec hrec (j := j) (by omega) (by omega)
  have r1 := recWords_rec hrec (j := j + 1) (by omega) (by omega)
  rw [hk0] at r0
  have e2 := run_pair (D := D) (first := first) hpm (j := j) (by omega)
  have hsl : (D.run first (2 * j)).1.2.2.length = 2 * j := run_chs_length hpm (by omega)
  have hcl := chs_length (D := D) (first := first) hpm
  have c0 := run_chsD (D := D) (first := first) hpm (k := 2 * (j + 1)) (by omega) (i := 2 * j)
    (by omega)
  have c1 := run_chsD (D := D) (first := first) hpm (k := 2 * (j + 1)) (by omega)
    (i := 2 * j + 1) (by omega)
  rw [hk1, e2] at r1
  rw [e2] at c0 c1
  simp only [cont, packRunF_pair] at r1 c0 c1
  rw [(getD_append_two hsl).1] at c0
  rw [(getD_append_two hsl).2] at c1
  obtain ⟨g1e, g2e⟩ := xs_packReads hpl hxs (k := 2 * j) (by omega)
  obtain ⟨g1e', g2e'⟩ := xs_packReads hpl hxs (k := 2 * j + 1) (by omega)
  rw [← List.getD_eq_getElem (d := (0, 0))] at g1e g2e g1e' g2e'
  refine ⟨(D.run first (2 * j)).2.cap, D.recCur cur j, (D.run first (2 * j)).1.1,
    (D.run first (2 * j)).1.2.1, D.c.point.getD (2 * j) 0, D.c.point.getD (2 * j + 1) 0,
    (D.packMsgs.getD (2 * j) (0, 0)).1, (D.packMsgs.getD (2 * j) (0, 0)).2,
    (D.packMsgs.getD (2 * j + 1) (0, 0)).1, (D.packMsgs.getD (2 * j + 1) (0, 0)).2,
    by simpa [recCur, hk0] using r0, (run_cap (2 * j)).1.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gen_sq, loadHolds_mul_gen_pow, Nat.add_zero]
    exact kk_readsAt_getD hpp (by omega)
  · rw [gen_sq, loadHolds_mul_gen_pow]
    exact kk_readsAt_getD hpp (by omega)
  · rw [recCur, hk0]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rw [pow_add, ← mul_assoc, loadHolds_mul_gen_pow, loadHolds_mul_gen_pow]
    interval_cases k
    · convert g1e using 2; rfl
    · convert g2e using 2; rfl
    · convert g1e' using 2; rfl
    · convert g2e' using 2; rfl
  · rw [gen_sq, loadHolds_mul_gen_pow, Nat.add_zero, ← c0]
    exact kk_readsAt_getD hpt (by omega)
  · rw [gen_sq, loadHolds_mul_gen_pow, ← c1]
    exact kk_readsAt_getD hpt (by omega)
  · refine roundRec_pred ?_
    simp only [recCur, hk1] at r1
    rw [recCur, hk0, mul_assoc, ← pow_add,
      show 47 + 2 * (2 * j) + 4 = 47 + 2 * (2 * (j + 1)) by ring]
    exact r1

/-- **The last round, honestly** (`y` odd). -/
theorem round_honest (hpl : D.product.length = 47) (hpm : D.packMsgs.length = D.y)
    {rec pp pt cur : E} (hrec : ReadsAt rd rec (D.recWords first cur))
    (hpp : ReadsAt rd pp D.c.point) (hxs : ReadsAt rd cur D.xs)
    (hpt : ReadsAt rd pt (D.chs first)) (hy30 : D.y ≤ 30) (hodd : D.y % 2 = 1) :
    MeaningKeccakRound rd [rec * gen ^ (D.y / 2), pp * (gen ^ (D.y / 2)) ^ 2,
      pt * (gen ^ (D.y / 2)) ^ 2] [] := by
  have hy : D.y = D.c.point.length := rfl
  obtain ⟨j, hjdef⟩ : ∃ j, j = D.y / 2 := ⟨_, rfl⟩
  rw [← hjdef]
  have hk0 : D.recK j = 2 * j := by unfold recK; omega
  have hk1 : D.recK (j + 1) = D.y := by unfold recK; omega
  have r0 := recWords_rec hrec (j := j) (by omega) (by omega)
  have r1 := recWords_rec hrec (j := j + 1) (by omega) (by omega)
  rw [hk0] at r0
  have e1 := run_one (D := D) (first := first) hpm (j := j) (by omega)
  have hsl : (D.run first (2 * j)).1.2.2.length = 2 * j := run_chs_length hpm (by omega)
  have hcl := chs_length (D := D) (first := first) hpm
  have c0 := run_chsD (D := D) (first := first) hpm (k := D.y) le_rfl (i := 2 * j) (by omega)
  rw [hk1, e1] at r1
  rw [e1] at c0
  simp only [cont, packRunF_eqRound, packRunF_nil] at r1 c0
  rw [show ∀ l : List E, ∀ a : E, l.length = 2 * j → (l ++ [a]).getD (2 * j) 0 = a from
    fun l a hl ↦ by rw [← hl]; simp] at c0
  · obtain ⟨g1e, g2e⟩ := xs_packReads hpl hxs (k := 2 * j) (by omega)
    rw [← List.getD_eq_getElem (d := (0, 0))] at g1e g2e
    refine ⟨rfl, (D.run first (2 * j)).2.cap, D.recCur cur j, (D.run first (2 * j)).1.1,
      (D.run first (2 * j)).1.2.1, D.c.point.getD (2 * j) 0, (D.packMsgs.getD (2 * j) (0, 0)).1,
      (D.packMsgs.getD (2 * j) (0, 0)).2, by simpa [recCur, hk0] using r0, (run_cap (2 * j)).1.2,
      ?_, ?_, ?_, ?_⟩
    · rw [gen_sq, loadHolds_mul_gen_pow, Nat.add_zero]
      exact kk_readsAt_getD hpp (by omega)
    · rw [recCur, hk0]
      intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      rw [pow_add, ← mul_assoc, loadHolds_mul_gen_pow, loadHolds_mul_gen_pow]
      interval_cases k
      · convert g1e using 2; rfl
      · convert g2e using 2; rfl
    · rw [gen_sq, loadHolds_mul_gen_pow, Nat.add_zero, ← c0]
      exact kk_readsAt_getD hpt (by omega)
    · refine roundRec_pred ?_
      simp only [recCur, hk1] at r1
      rw [recCur, hk0, mul_assoc, ← pow_add, show 47 + 2 * (2 * j) + 2 = 47 + 2 * D.y by omega]
      exact r1
  · exact hsl

end LayerData

end
end LeanVM.Guest.B1.VerifySub
