import LeanDa.RpmScheme
import Common.Duplex.Vec
import Common.Rerun
import LeanDa.Defs

/-!
# LeanDA's challenges as a duplex

The challenges' sponge (`membershipChallengesM`) over the direct calls `F` of the two-oracle model
is a duplex challenge derivation in the sense of `Common.Duplex` (`daDuplex`): the initial state
is the label's hash in lanes `0 … 3` (`Sponge.new`), absorbing the root writes its words and tags
over the rate (`first`), a later sample writes zeros over the rate (`next`), and a challenge is
the three lanes `0 … 2` of an answer (`out`). Every one of these keeps lanes `16 … 24`, the bytes
`128 … 199` of the state (`cap_first`, `cap_next`), which the duplex lemma calls the capacity:
`72` bytes, so a uniform state has a given capacity with probability `2^-576` (`daDuplex_cap`).
Over `F`, the challenges are the duplex's (`membershipChallengesM_eq_chalP`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.Duplex
open scoped ENNReal

namespace LeanDa

/-! ## The state as bytes -/

theorem bytesEquiv_apply (y : KState) (i : Fin 200) : bytesEquiv y i = byteAt y i := rfl

/-! ## Splitting the bytes -/

theorem splitEquiv_fst {m k : ℕ} (f : Fin (m + k) → UInt8) (j : Fin m) :
    (splitEquiv m k f).1 j = f (Fin.castAdd k j) := by
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

theorem daBuild_symm_fst (y : KState) :
    (daBuild.symm y).1 = limbsEquiv fun j : Fin 24 ↦ byteAt y j := by
  simp only [daBuild, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_fst]
  congr 1

/-! ## The duplex -/

/-! ## The root's words determine the root -/

/-! ## The challenge of an answer -/

theorem limbsEquiv_apply (f : Fin 24 → UInt8) :
    limbsEquiv f = CompPoly.Extension.Ext.ofFn (P := BF64.ext3Params) fun a : Fin 3 ↦
      laneBytes.symm (Vector.ofFn fun b : Fin 8 ↦ f (finProdFinEquiv (a, b))) := rfl

theorem ofFn_eq_ofLimbs (g : Fin 3 → K) :
    (CompPoly.Extension.Ext.ofFn (P := BF64.ext3Params) g : E) = ofLimbs (g 0) (g 1) (g 2) := by
  simp only [CompPoly.Extension.Ext.ofFn, ofLimbs]
  congr 1

/-- **The challenge an answer carries is its lanes `0 … 2`** (`Sponge.sample`). -/
theorem daBuild_symm_fst_eq (y : KState) :
    (daBuild.symm y).1 =
      ofLimbs (stateToLanes y)[0] (stateToLanes y)[1] (stateToLanes y)[2] := by
  rw [daBuild_symm_fst, limbsEquiv_apply]
  have key : ∀ a : Fin 3, laneBytes.symm (Vector.ofFn fun b : Fin 8 ↦
      byteAt y (finProdFinEquiv (a, b) : ℕ)) = (stateToLanes y)[(a : ℕ)] := by
    intro a
    simp only [stateToLanes, Vector.getElem_ofFn, byteAt]
    refine congrArg laneBytes.symm ?_
    apply Vector.ext
    intro b hb
    simp only [Vector.getElem_ofFn, finProdFinEquiv_apply_val]
    congr 1
    ring
  rw [ofFn_eq_ofLimbs, key 0, key 1, key 2]
  rfl

/-! ## LeanDA's duplex -/

theorem card_bytes (k : ℕ) : Fintype.card (Fin k → UInt8) = 256 ^ k := by
  rw [Fintype.card_fun, card_uInt8, Fintype.card_fin]

/-- **A capacity is hit with probability `2^-576`.** -/
theorem daDuplex_cap (c : DaCp) :
    Pr{let w ← ($ᵗ DaW : ProbComp DaW)}[daDuplex.capW w = c] ≤ (2 ^ 576 : ℝ≥0∞)⁻¹ := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hf : (Finset.univ.filter fun w : DaW ↦ daDuplex.capW w = c) =
      (Finset.univ : Finset (Fin 104 → UInt8)) ×ˢ {c} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    exact Iff.rfl
  simp only [hf, Finset.card_product, Finset.card_singleton, mul_one, Finset.card_univ, Fintype.card_prod, card_bytes, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have h256 : (256 : ℝ≥0∞) ^ 72 = 2 ^ 576 := by
    rw [show (256 : ℝ≥0∞) = 2 ^ 8 by norm_num, ← pow_mul]
  have ha : (256 : ℝ≥0∞) ^ 104 ≠ 0 := pow_ne_zero _ (by norm_num)
  have ha' : (256 : ℝ≥0∞) ^ 104 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  refine le_of_eq ?_
  rw [h256, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl ha) (Or.inl ha'),
    mul_comm ((256 : ℝ≥0∞) ^ 104)⁻¹, mul_assoc, ENNReal.inv_mul_cancel ha ha', mul_one]

/-! ## The challenges over `F` are the duplex's -/

theorem daDuplex_out (y : KState) :
    daDuplex.out y = ofLimbs (stateToLanes y)[0] (stateToLanes y)[1] (stateToLanes y)[2] :=
  daBuild_symm_fst_eq y

theorem samplesM_eq_chainP (k : ℕ) (y : KState) :
    Sponge.samplesM pR k ⟨stateToLanes y, []⟩ = chainP daDuplex k y := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    simp only [Sponge.samplesM, Sponge.sampleM, Sponge.duplexM, pR, lanePerm, chainP,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun y' ↦ ?_
    rw [ih, daDuplex_out]

/-- **Over `F`, LeanDA's challenges are the duplex's.** -/
theorem membershipChallengesM_eq_chalP (root : Digest) :
    membershipChallengesM hR pR root = chalP daDuplex root := by
  simp only [membershipChallengesM, Sponge.fromLabelM, Sponge.newM, Sponge.observeM,
    Sponge.absorbM, pR, lanePerm, chalP, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  refine bind_congr fun iv ↦ bind_congr fun y₀ ↦ ?_
  have h0 : ¬ ([] : List (E × K)).length = rateScalars := by simp [rateScalars]
  simp only [h0, ↓reduceIte, pure_bind, List.nil_append]
  show Sponge.samplesM pR (13 + 1) ⟨stateToLanes y₀, rootScalars root⟩ = _
  rw [Sponge.samplesM]
  simp only [Sponge.sampleM, Sponge.duplexM, pR, lanePerm,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  refine bind_congr fun y₁ ↦ ?_
  rw [samplesM_eq_chainP, daDuplex_out]

end LeanDa
