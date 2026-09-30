import LeanerVM.Protocol.Field
import LeanerVM.Protocol.ToVCVio.UniformSample
import LeanerVM.Protocol.ToArkLib.Oracles

/-!
Probe `Layer0`: the declarations of the proof system's Layer 0, their axioms, the instances
instance search finds, and the uniformity of the two samplers.
-/

open LeanerVM.Parameters LeanerVM.Protocol CompPoly OracleComp
open scoped NNReal ENNReal

/-! ## 1. Which instances are found -/

#synth SampleableType K
#synth SampleableType E
#synth SampleableType (Vector K 3)
#synth SampleableType (Fin (2 ^ 64))
#synth Fintype K
#synth Fintype E
#synth DecidableEq K
#synth DecidableEq E
#synth OracleInterface (Column 3)
#synth OracleInterface E
#synth OracleInterface (List E)

/-! ## 2. Signatures as elaborated -/

#check @finEquivK
#check @limbsEquiv
#check @instSampleableTypeK
#check @instSampleableTypeE
#check @card_E
#check @evalOracle
#check @evalOracle_answer
#check @probEvent_uniformSample_le_of_card_le
#check @probEvent_uniformSample_le_of_subsingleton
#check @NoOracle
#check @OneOracle
#check @noOracle_eq
#print SampleableType
#print evalOracle
#print instSampleableTypeK
#print instSampleableTypeE

/-! ## 3. Axioms -/

#print axioms finEquivK
#print axioms limbsEquiv
#print axioms instSampleableTypeK
#print axioms instSampleableTypeE
#print axioms card_E
#print axioms evalOracle
#print axioms evalOracle_answer
#print axioms instOracleInterfaceE
#print axioms instOracleInterfaceListE
#print axioms probEvent_uniformSample_le_of_card_le
#print axioms probEvent_uniformSample_le_of_subsingleton
#print axioms noOracle_eq
-- the library facts Layer 0 rests on
#print axioms BF64.card_ext3
#print axioms BF64.card_bf64
#print axioms BF64.basePoly_irreducible
#print axioms BF64.ext3Poly_irreducible
#print axioms BF64.instField
#print axioms SampleableType.ofEquiv
#print axioms probOutput_uniformSample
#print axioms probEvent_uniformSample
#print axioms CMlPolynomialEval.eval_mle_eq_eval
#print axioms CMlPolynomialEval.eval₂_mle_eq_eval₂

/-! ## 4. The two equivalences are bijections, and the samplers are uniform -/

example : Function.Bijective finEquivK := finEquivK.bijective
example : Function.Bijective limbsEquiv := limbsEquiv.bijective

-- every element of `K` is drawn with probability `1 / |K|`
example (x : K) : Pr[= x | $ᵗ K] = (Fintype.card K : ℝ≥0∞)⁻¹ := probOutput_uniformSample K x
-- every element of `E` is drawn with probability `1 / |E|`
example (x : E) : Pr[= x | $ᵗ E] = (Fintype.card E : ℝ≥0∞)⁻¹ := probOutput_uniformSample E x
-- and `|E| = 2^192`
example (x : E) : Pr[= x | $ᵗ E] = ((2 ^ 192 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [probOutput_uniformSample, card_E]
-- the samplers never fail and reach every element
example : Pr[⊥ | $ᵗ E] = 0 := probFailure_uniformSample E
example : support ($ᵗ E) = Set.univ := support_uniformSample E
-- the sampler of `E` is by definition the image of three independent limbs
example : ($ᵗ E) = limbsEquiv <$> ($ᵗ (Vector K 3)) := rfl
example : ($ᵗ K) = finEquivK <$> ($ᵗ (Fin (2 ^ 64))) := rfl

/-! ## 5. The oracle interface of a column -/

example (n : ℕ) : OracleInterface.Query (Column n) = Vector E n := rfl
example (n : ℕ) (r : Vector E n) : OracleInterface.Response (Message := Column n) r = E := rfl
example (n : ℕ) (q : Column n) (r : Vector E n) :
    OracleInterface.answer q r = CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) r :=
  evalOracle_answer n q r
-- the answer is the dot product of the lifted table with the Lagrange basis at `r`
example (n : ℕ) (q : Column n) (r : Vector E n) :
    OracleInterface.answer q r =
      CMlPolynomialEval.eval (CMlPolynomialEval.map (algebraMap K E) q.values) r := by
  rw [evalOracle_answer, CMlPolynomialEval.eval₂_mle_eq_eval₂]; rfl
-- the scalar interfaces: query `Unit`, the answer is the message
example : OracleInterface.Query E = Unit := rfl
example (x : E) : OracleInterface.answer x () = x := rfl
example : OracleInterface.Query (List E) = Unit := rfl
example (l : List E) : OracleInterface.answer l () = l := rfl
-- `ofK` is `algebraMap K E`
example (a : K) : ofK a = algebraMap K E a := rfl
