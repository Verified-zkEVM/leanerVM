/-
  LeanerVM.Protocol.ToArkLib.McaJohnson

  Mutual correlated agreement of Reed–Solomon codes up to the Johnson bound as an interface with
  its constant a parameter, inhabited at the printed constant of [BCHKS25, Thm. 4.6]; the
  fold-line generator `z ↦ (1 - z, z)`, whose error is the affine line's; and the count of bad
  seeds that an error bound gives. Candidate for ArkLib.
-/

module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability

/-!
# Mutual correlated agreement up to the Johnson bound

`McaJohnson F a` is the statement of [BCHKS25, Thm. 4.6] over the finite field `F` with its
constant a parameter: for every Reed–Solomon code of block length `n` and degree bound `D`
(dimension `D + 1`), with `ρ = D / n` and a slack `η > 0` such that `√ρ + η ≤ 1`, the mutual
correlated agreement error of the affine line `u₀ + z · u₁` at radius `1 - √ρ - η` is at most
`a n D η / |F|`.

* `mcaJohnson_comparisonEstimate`: `McaJohnson F johnsonComparisonEstimate` over every finite
  field, the composition of `ReedSolomon.mcaError_affineLine_johnson_le` (the proved bound, with
  ArkLib's exception count) and `johnsonExceptionCount_le_comparisonEstimate` (that count is at
  most the printed constant).
* `FoldLineGenerator F` is `z ↦ (1 - z, z)`, the combination `(1 - z) · u₀ + z · u₁`, and
  `mcaError_foldLine_eq_affineLine` equates its error with the affine line's, at every radius, for
  every module code over a field: `(u₀, u₁) ↦ (u₀, u₁ - u₀)` is a bijection of pairs that keeps
  "both rows extend to codewords on `T`" and carries the one combination to the other.
* `natCard_isMCA_le_of_mcaError_le`: an error bound `B / |S|` leaves at most `⌊B⌋₊` bad seeds for
  every family, the counting form of an error bound over a uniform seed.

## References

* [BCHKS25] Ben-Sasson, Carmon, Haböck, Kopparty, Saraf, *On Proximity Gaps for Reed–Solomon
  Codes*, Cryptology ePrint Archive 2025/2055, Theorem 4.6.
-/

namespace LeanerVM.Protocol

open ReedSolomon ReedSolomon.HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

@[expose] public section

/-! ## The interface and its inhabitant -/

/-- **Mutual correlated agreement up to the Johnson bound**, with its constant `a` a parameter:
for a Reed–Solomon code over `F` of block length `n` and degree bound `D` (dimension `D + 1`),
with `ρ = D / n` and slack `η`, the affine line's error at radius `1 - √ρ - η` is at most
`a n D η / |F|` ([BCHKS25, Thm. 4.6], with `a` its constant). -/
structure McaJohnson (F : Type) [Field F] [Fintype F] [SampleableType F]
    (a : ℕ → ℕ → ℝ → ℝ) : Prop where
  /-- The error bound in the Johnson range. -/
  le : ∀ (n : ℕ) (domain : Fin n ↪ F) (D : ℕ) (η : ℝ), 1 ≤ D → D ≤ n - 2 → 0 < η →
    √((D : ℝ) / n) + η ≤ 1 →
    mcaError (AffineLineGenerator F) (code domain (D + 1)) (1 - √((D : ℝ) / n) - η) ≤
      ENNReal.ofReal (a n D η / Fintype.card F)

/-- **[BCHKS25]'s printed constant holds over every finite field**: the proved bound with ArkLib's
exception count, which is at most `johnsonComparisonEstimate n D η`. -/
theorem mcaJohnson_comparisonEstimate (F : Type) [Field F] [Fintype F] [SampleableType F] :
    McaJohnson F johnsonComparisonEstimate where
  le n domain D η hD hDn hη ha := by
    have ha' : johnsonAgreement n D η ≤ 1 := ha
    have h := mcaError_affineLine_johnson_le domain hD hDn hη ha'
    rw [show 1 - √((D : ℝ) / n) - η = 1 - johnsonAgreement n D η by
      simp only [johnsonAgreement, johnsonRhoMinus]; ring]
    refine h.trans (min_le_right _ _ |>.trans (ENNReal.ofReal_le_ofReal ?_))
    exact div_le_div_of_nonneg_right
      (johnsonExceptionCount_le_comparisonEstimate hD hDn hη ha' (Nat.le_ceil _))
      (Nat.cast_nonneg _)

/-! ## The fold line -/

/-- The fold-line generator `z ↦ (1 - z, z)`: the combination `(1 - z) · u₀ + z · u₁`. -/
abbrev FoldLineGenerator (F : Type) [Field F] : Generator F (Fin 2) F :=
  fun z ↦ ![1 - z, z]

/-- The change of pair `(u₀, u₁) ↦ (u₀, u₁ - u₀)`. -/
private def shear {ι A : Type} [AddCommGroup A] : (Fin 2 → ι → A) ≃ (Fin 2 → ι → A) where
  toFun U := ![U 0, U 1 - U 0]
  invFun V := ![V 0, V 1 + V 0]
  left_inv U := by
    ext i x
    fin_cases i <;> simp
  right_inv V := by
    ext i x
    fin_cases i <;> simp

/-- A seed is MCA-bad for the fold line and a pair exactly when it is for the affine line and the
sheared pair. -/
private theorem isMCA_foldLine_iff_shear {ι F A : Type} [Fintype ι] [Field F] [Fintype F]
    [AddCommGroup A] [Module F A] (MC : ModuleCode ι F A) (z : F) (U : Fin 2 → ι → A)
    (δ : ℝ) :
    IsMCA (FoldLineGenerator F) MC z U δ ↔ IsMCA (AffineLineGenerator F) MC z (shear U) δ := by
  have hcomb : (fun k ↦ ∑ j, FoldLineGenerator F z j • U j k) =
      fun k ↦ ∑ j, AffineLineGenerator F z j • shear U j k := by
    funext k
    simp only [Fin.sum_univ_two, FoldLineGenerator, AffineLineGenerator, shear, Equiv.coe_fn_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, sub_smul, one_smul, smul_sub]
    abel
  have hrows : ∀ T : Finset ι,
      (∃ j, projectedWord (U j) T ∉ projectedCodeSubmod MC T) ↔
        ∃ j, projectedWord (shear U j) T ∉ projectedCodeSubmod MC T := by
    intro T
    rw [← not_forall_not, ← not_forall_not]
    simp only [not_not]
    refine not_congr ?_
    rw [Fin.forall_fin_two, Fin.forall_fin_two]
    simp only [shear, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hsub : projectedWord (U 1 - U 0) T = projectedWord (U 1) T - projectedWord (U 0) T :=
      rfl
    rw [hsub]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨h0, Submodule.sub_mem _ h1 h0⟩
    · rintro ⟨h0, h1⟩
      have := Submodule.add_mem _ h1 h0
      rw [sub_add_cancel] at this
      exact ⟨h0, this⟩
  unfold IsMCA
  simp only [hcomb]
  exact exists_congr fun T ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ hrows T

/-- **The fold line's error is the affine line's**, for every module code over a field, at every
radius: the shear `(u₀, u₁) ↦ (u₀, u₁ - u₀)` is a bijection of pairs that carries the one event
to the other. No characteristic hypothesis. -/
theorem mcaError_foldLine_eq_affineLine {ι F A : Type} [Fintype ι] [Field F] [Fintype F]
    [SampleableType F] [AddCommGroup A] [Module F A] (MC : ModuleCode ι F A) (δ : ℝ) :
    mcaError (FoldLineGenerator F) MC δ = mcaError (AffineLineGenerator F) MC δ := by
  simp only [mcaError]
  conv_rhs => rw [← shear.iSup_comp]
  exact iSup_congr fun U ↦ prEvent_congr _ _ _ fun x ↦ isMCA_foldLine_iff_shear MC x U δ

/-! ## Counting the bad seeds -/

/-- **An error bound counts the bad seeds**: if the MCA error at radius `δ` is at most `B / |S|`,
every family has at most `⌊B⌋₊` seeds at which the MCA event holds. -/
theorem natCard_isMCA_le_of_mcaError_le {ι F ℓ S A : Type} [Fintype ι] [Field F] [Fintype ℓ]
    [Nonempty S] [Fintype S] [SampleableType S] [AddCommMonoid A] [Module F A]
    (G : Generator S ℓ F) (MC : ModuleCode ι F A) {δ B : ℝ}
    (h : mcaError G MC δ ≤ ENNReal.ofReal (B / Fintype.card S)) (U : ℓ → ι → A) :
    Nat.card {x : S // IsMCA G MC x U δ} ≤ ⌊B⌋₊ := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hpr : Pr{let x ←$ᵗ S}[IsMCA G MC x U δ] ≤ mcaError G MC δ :=
    le_iSup (fun U ↦ Pr{let x ←$ᵗ S}[IsMCA G MC x U δ]) U
  rw [SampleableType.prEvent_uniformSample_eq_ofReal] at hpr
  have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  rcases (ENNReal.ofReal_le_ofReal_iff').mp (hpr.trans h) with hle | hle
  · exact Nat.le_floor ((div_le_div_iff_of_pos_right hS).mp hle)
  · have h0 : ((Finset.univ.filter fun x : S ↦ IsMCA G MC x U δ).card : ℝ) ≤ 0 := by
      simpa using (div_le_iff₀ hS).mp hle
    have h0' : (Finset.univ.filter fun x : S ↦ IsMCA G MC x U δ).card = 0 := by
      exact_mod_cast le_antisymm h0 (Nat.cast_nonneg _)
    simp [h0']

end

end LeanerVM.Protocol
