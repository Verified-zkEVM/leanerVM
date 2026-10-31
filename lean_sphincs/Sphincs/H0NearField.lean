import Sphincs.H0NearMom
import Sphincs.H0Bridge

/-! **The near moment, on fields.** The half cover of `H0NearMom.lean` on the uniform field values
(`φH`, `avgN_φH`) and the near value of an index (`yN`, `avgN_yN`). Apart from `H0NearMom.lean`,
so that the near moment, which the kernel-checked tables read, does not depend on the scheme. -/

open ENNReal

namespace SphincsLayered.Security.H0

open Concrete H0Avg SphincsFors.Security.Domination

set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-! ### One subtree, as fields -/

/-- Every chain the target field needs in subtree `j` is opened deep enough by a disclosed field. -/
def CoverHF (t : FieldVal) (j : SubIdx) (Xs : Multiset FieldVal) : Prop :=
  ∀ i, chainNeed t j i = 0 ∨ ∃ x ∈ Xs, KeyCovers x t j i

theorem coverHF_iff (t : FieldVal) (j : SubIdx) (Xs : Multiset FieldVal) :
    CoverHF t j Xs ↔ CoverHT (fieldMT t) j (Xs.map fieldMT) := by
  unfold CoverHF CoverHT
  simp only [Multiset.mem_map]
  constructor
  · intro h i
    rcases h i with h0 | ⟨x, hx, hk⟩
    · exact Or.inl h0
    · exact Or.inr ⟨fieldMT x, ⟨x, hx, rfl⟩, hk⟩
  · intro h i
    rcases h i with h0 | ⟨_, ⟨x, hx, rfl⟩, hk⟩
    · exact Or.inl h0
    · exact Or.inr ⟨x, hx, hk⟩

open Classical in
/-- The per-tree half-cover fraction. -/
noncomputable def φH (j : SubIdx) (Xs : Multiset FieldVal) : ℝ≥0∞ :=
  freshAvg Finset.univ fun t : FieldVal => if CoverHF t j Xs then 1 else 0

theorem φH_eq (j : SubIdx) (Xs : Multiset FieldVal) :
    φH j Xs = ENNReal.ofReal (avgR fun t : MT => coverHR t j (Xs.map fieldMT)) := by
  classical
  unfold φH
  have hpt : ∀ t : FieldVal, (if CoverHF t j Xs then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal (coverHR (fieldMT t) j (Xs.map fieldMT)) := by
    intro t
    unfold coverHR
    by_cases h : CoverHF t j Xs
    · rw [ite_eq_left h, ite_eq_left ((coverHF_iff t j Xs).1 h), ENNReal.ofReal_one]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((coverHF_iff t j Xs).2 h')), ENNReal.ofReal_zero]
  simp only [hpt]
  rw [freshAvg_ofReal _ (fun t => coverHR_nonneg _ _ _), avgR_equiv fieldMT]
  simp only [Equiv.apply_symm_apply]

theorem avgN_φH (j : SubIdx) (n : ℕ) : avgN (φH j) n 0 = ENNReal.ofReal (ΨHR j n) := by
  rw [avgN_field (φH j) (fun X => avgR fun t : MT => coverHR t j X) (coverHAvg_nonneg j) (φH_eq j) n 0]
  rfl

theorem φH_le_one (j : SubIdx) (Xs : Multiset FieldVal) : φH j Xs ≤ 1 := by
  classical
  unfold φH
  calc freshAvg Finset.univ (fun t : FieldVal => if CoverHF t j Xs then (1 : ℝ≥0∞) else 0)
      ≤ freshAvg Finset.univ (fun _ : FieldVal => (1 : ℝ≥0∞)) :=
        freshAvg_mono _ fun t _ => by split_ifs <;> simp
    _ = 1 := by rw [freshAvg_const _ Finset.univ_nonempty]

/-! ### The near value of an index -/

/-- The per-tree factor of the near value: the half cover at the free tree, the cover elsewhere. -/
noncomputable def nearFactor (c : Coord) (j : SubIdx) (c' : Coord) : Multiset FieldVal → ℝ≥0∞ :=
  if c' = c then φH j else φF

/-- **The near value of a multiset of disclosed marks at one index.** -/
noncomputable def yN (Ms : Multiset (Coord → FieldVal)) : ℝ≥0∞ :=
  ∑ c, ∑ j, ∏ c', nearFactor c j c' (Ms.map fun m => m c')

theorem avgN_sum_fin {U : Type} [Fintype U] [Nonempty U] {β : Type} [DecidableEq β] (s : Finset β)
    (φ : β → Multiset U → ℝ≥0∞) (n : ℕ) (X : Multiset U) :
    avgN (fun Y => ∑ b ∈ s, φ b Y) n X = ∑ b ∈ s, avgN (φ b) n X := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact avgN_const 0 n X
  | insert b s hb ih =>
      have h1 : (fun Y => ∑ b' ∈ insert b s, φ b' Y) = fun Y => φ b Y + ∑ b' ∈ s, φ b' Y :=
        funext fun Y => Finset.sum_insert hb
      rw [h1, avgN_add, ih, Finset.sum_insert hb]

/-- **`E[near | n] = Σ_{c,j} Ψ1(n)^7 ΨH(n)`.** -/
theorem avgN_yN (n : ℕ) :
    avgN yN n 0 = ∑ _c : Coord, ∑ j : SubIdx, ENNReal.ofReal (ΨHR j n) * ENNReal.ofReal (Ψ1R n) ^ 7 := by
  unfold yN
  rw [avgN_sum_fin]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [avgN_sum_fin]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [avgN_prod_coords (nearFactor c j) n 0]
  simp only [Multiset.map_zero]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
  have h1 : avgN (nearFactor c j c) n 0 = ENNReal.ofReal (ΨHR j n) := by
    simp only [nearFactor, ite_true]; exact avgN_φH j n
  have h2 : ∀ c' ∈ Finset.univ.erase c, avgN (nearFactor c j c') n 0 = ENNReal.ofReal (Ψ1R n) := by
    intro c' hc'
    simp only [nearFactor, ite_eq_right (Finset.ne_of_mem_erase hc')]
    exact avgN_φF n
  rw [h1, Finset.prod_congr rfl h2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, card_coord]

theorem yN_le (Ms : Multiset (Coord → FieldVal)) : yN Ms ≤ 16 := by
  unfold yN
  calc ∑ c, ∑ j, ∏ c', nearFactor c j c' (Ms.map fun m => m c') ≤ ∑ _c : Coord, ∑ _j : SubIdx, (1 : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun j _ => ?_
        refine Finset.prod_le_one fun c' _ => ?_
        unfold nearFactor
        split_ifs
        · exact φH_le_one j _
        · exact φF_le_one _
    _ = 16 := by
        simp only [Finset.sum_const, Finset.card_univ, card_coord, nsmul_eq_mul, mul_one]
        norm_num

end SphincsLayered.Security.H0
