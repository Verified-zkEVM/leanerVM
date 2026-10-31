import Sphincs.H0Tables

/-! **The near moment.** A target is *half covered* at tree `c`, subtree `j`, when every chain of the
WOTS key it selects in subtree `j` of tree `c` is opened deep enough. Its probability over `n`
uniform marks is `ΨH(n) = Σ_k C(n,k) (1/16)^k (15/16)^(n-k) μ_k`, by the inclusion-exclusion of the
first per-tree moment restricted to one subtree. The near witness of a target, summed over the free
subtree `(c, j)`, has per-index mean `Σ_{c,j} Ψ1(n)^7 ΨH(n)`. -/

open ENNReal

namespace SphincsLayered.Security.H0


set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-! ### One subtree, as tuples -/

/-- Every chain of subtree `j` that the target needs is opened deep enough. -/
def CoverHT (t : MT) (j : SubIdx) (X : Multiset MT) : Prop := ∀ i, need t j i = 0 ∨ ∃ x ∈ X, KC x t j i

/-- The half-cover indicator as a real number. -/
noncomputable def coverHR (t : MT) (j : SubIdx) (X : Multiset MT) : ℝ := by
  classical
  exact if CoverHT t j X then 1 else 0

/-- A choice of chains in subtree `j` only. -/
def single (j : SubIdx) (T : Finset FChain) : SubIdx → Finset FChain := fun j' => if j' = j then T else ∅

theorem prod_single {β : Type} [CommMonoid β] (j : SubIdx) (g : SubIdx → β) (hg : ∀ j', j' ≠ j → g j' = 1) :
    ∏ j', g j' = g j := by
  rw [Finset.prod_eq_single j (fun j' _ hj' => hg j' hj') (fun h => absurd (Finset.mem_univ j) h)]

theorem sgnS_single (j : SubIdx) (T : Finset FChain) : sgnS (single j T) = (-1) ^ T.card := by
  unfold sgnS
  rw [prod_single j _ (fun j' hj' => by simp [single, hj'])]
  simp [single]

theorem needA_single (t : MT) (j : SubIdx) (T : Finset FChain) :
    needA t (single j T) = needA1 (t.2 j).2 T := by
  unfold needA needA1
  rw [prod_single j _ (fun j' hj' => by simp [single, hj'])]
  simp only [single, ite_true]
  rfl

theorem avoidB_single (t : MT) (j : SubIdx) (T : Finset FChain) (x : MT) :
    avoidB t (single j T) x = ∏ i ∈ T, (1 - if KC x t j i then (1 : ℝ) else 0) := by
  classical
  unfold avoidB
  rw [prod_single j _ (fun j' hj' => by simp [single, hj'])]
  simp only [single, ite_true]

theorem coverHR_eq_prod (t : MT) (j : SubIdx) (X : Multiset MT) :
    coverHR t j X = ∏ i, (1 - (if need t j i = 0 then 0 else 1) *
      (X.map fun x => (1 - if KC x t j i then (1 : ℝ) else 0)).prod) := by
  classical
  have hpt : ∀ i, (1 - (if need t j i = 0 then (0 : ℝ) else 1) *
      (X.map fun x => (1 - if KC x t j i then (1 : ℝ) else 0)).prod) =
      if need t j i = 0 ∨ ∃ x ∈ X, KC x t j i then 1 else 0 := by
    intro i
    by_cases h0 : need t j i = 0
    · rw [ite_eq_left h0, zero_mul, sub_zero, ite_eq_left (Or.inl h0)]
    · rw [ite_eq_right h0, one_mul]
      by_cases hx : ∃ x ∈ X, KC x t j i
      · obtain ⟨x, hx, hk⟩ := hx
        rw [ite_eq_left (Or.inr ⟨x, hx, hk⟩), Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨x, hx, by simp [hk]⟩),
          sub_zero]
      · push Not at hx
        rw [ite_eq_right (by rintro (h | ⟨x, hx', hk⟩); exact h0 h; exact hx x hx' hk)]
        rw [Multiset.prod_eq_one (fun y hy => by
          obtain ⟨x, hx', rfl⟩ := Multiset.mem_map.1 hy
          simp [hx x hx'])]
        ring
  simp only [hpt]
  unfold coverHR CoverHT
  by_cases hc : ∀ i, need t j i = 0 ∨ ∃ x ∈ X, KC x t j i
  · rw [ite_eq_left hc]
    symm
    exact Finset.prod_eq_one fun i _ => ite_eq_left (hc i)
  · rw [ite_eq_right hc]
    push Not at hc
    obtain ⟨i, hi⟩ := hc
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [ite_eq_right]
    rintro (h | ⟨x, hx, hk⟩)
    · exact hi.1 h
    · exact hi.2 x hx hk

/-- **Inclusion-exclusion of the half-cover indicator.** -/
theorem coverHR_expand (t : MT) (j : SubIdx) (X : Multiset MT) :
    coverHR t j X = ∑ T : Finset FChain, sgnS (single j T) * needA t (single j T) *
      (X.map (avoidB t (single j T))).prod := by
  classical
  rw [coverHR_eq_prod, prod_one_sub_mul]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [sgnS_single, needA_single]
  have hav : avoidB t (single j T) = fun x => ∏ i ∈ T, (1 - if KC x t j i then (1 : ℝ) else 0) :=
    funext fun x => avoidB_single t j T x
  have hn : needA1 (t.2 j).2 T = ∏ i ∈ T, if need t j i = 0 then (0 : ℝ) else 1 := rfl
  rw [hav, multiset_prod_finset_prod, hn]

/-- The half-cover moment. -/
noncomputable def ΨHR (j : SubIdx) (n : ℕ) : ℝ :=
  avgNR (fun X : Multiset MT => avgR fun t : MT => coverHR t j X) n 0

theorem G_empty (w : LutIdx) : G w ∅ = 1 := by
  unfold G
  simp only [Finset.prod_empty]
  exact avgR_const 1

theorem avgR_avoidB_single (t : MT) (j : SubIdx) (T : Finset FChain) :
    avgR (avoidB t (single j T)) = 15 / 16 + 1 / 16 * (7 / 8 + 1 / 8 * G (t.2 j).2 T) := by
  rw [avgR_avoidB]
  congr 2
  rw [prod_single j _ (fun j' hj' => by simp [single, hj', G_empty]; norm_num)]
  simp [single]

theorem ΨHR_signed (j : SubIdx) (n : ℕ) :
    ΨHR j n = avgR fun t : MT => ∑ T : Finset FChain, sgnS (single j T) * needA t (single j T) *
      avgR (avoidB t (single j T)) ^ n := by
  unfold ΨHR
  rw [avgNR_avgR]
  refine congrArg avgR (funext fun t => ?_)
  have hc : coverHR t j = fun X => ∑ T : Finset FChain,
      sgnS (single j T) * needA t (single j T) * (X.map (avoidB t (single j T))).prod :=
    funext fun X => coverHR_expand t j X
  rw [hc, avgNR_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [avgNR_const_mul, avgNR_prod_map, Multiset.map_zero, Multiset.prod_zero, one_mul]

/-- Averages of a function of one subtree's codeword. -/
theorem avgR_word (j : SubIdx) (g : LutIdx → ℝ) : avgR (fun t : MT => g (t.2 j).2) = avgR g := by
  calc avgR (fun t : MT => g (t.2 j).2) = avgR (fun w : SubIdx → LutIdx => g (w j)) :=
        avgR_words (fun w => g (w j))
    _ = avgR (fun w : SubIdx → LutIdx => ∏ j', (if j' = j then g (w j') else (1 : ℝ))) := by
        refine congrArg avgR (funext fun w => ?_)
        rw [prod_single j _ (fun j' hj' => by simp only [ite_eq_right hj'])]
        simp
    _ = ∏ j', avgR (fun x : LutIdx => if j' = j then g x else (1 : ℝ)) :=
        avgR_prod_pi (fun j' (x : LutIdx) => if j' = j then g x else (1 : ℝ))
    _ = avgR g := by
        rw [prod_single j _ (fun j' hj' => by simp only [ite_eq_right hj']; exact avgR_const 1)]
        simp

/-- **The half-cover moment.** -/
theorem ΨHR_eq (j : SubIdx) (n : ℕ) :
    ΨHR j n = ∑ k ∈ Finset.range (n + 1), (1 / 16) ^ k * (15 / 16) ^ (n - k) * (n.choose k : ℝ) * μR k := by
  rw [ΨHR_signed]
  simp only [avgR_avoidB_single, sgnS_single, needA_single]
  rw [avgR_word j (fun w => ∑ T : Finset FChain, (-1) ^ T.card * needA1 w T *
    (15 / 16 + 1 / 16 * (7 / 8 + 1 / 8 * G w T)) ^ n)]
  have hexp : ∀ w : LutIdx, (∑ T : Finset FChain, (-1) ^ T.card * needA1 w T *
      (15 / 16 + 1 / 16 * (7 / 8 + 1 / 8 * G w T)) ^ n) =
      ∑ k ∈ Finset.range (n + 1), (1 / 16) ^ k * (15 / 16) ^ (n - k) * (n.choose k : ℝ) *
        ∑ T : Finset FChain, (-1) ^ T.card * needA1 w T * (1 / 8 * G w T + 7 / 8) ^ k := by
    intro w
    simp only [pow_affine (15 / 16 : ℝ) (1 / 16 : ℝ), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun T _ => ?_
    have h78 : (7 / 8 + 1 / 8 * G w T : ℝ) = 1 / 8 * G w T + 7 / 8 := by ring
    rw [h78]
    ring
  simp only [hexp]
  rw [avgR_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [avgR_const_mul]
  rfl

theorem coverHR_nonneg (t : MT) (j : SubIdx) (X : Multiset MT) : 0 ≤ coverHR t j X := by
  unfold coverHR; split_ifs <;> norm_num

theorem coverHAvg_nonneg (j : SubIdx) (X : Multiset MT) : 0 ≤ avgR fun t : MT => coverHR t j X := by
  unfold avgR
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun t _ => coverHR_nonneg t j X)

end SphincsLayered.Security.H0
