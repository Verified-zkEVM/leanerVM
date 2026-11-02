module

public import LeanVM.Protocol.Extraction.Fast.EvalMat.Product
public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis

/-!
# PM-basis on evaluation-domain products

`evalRuntime T mulCtx lowCtx leafCutoff`: CompPoly's kernel-leaf PM-basis runtime with its two
matrix products, the basis composition and the residual's column-truncated product, replaced by
`mulEval T mulCtx` and `mulTruncEval T mulCtx`. **`evalRuntime_eq`**: it is CompPoly's runtime
`kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff c`, for every composition cutoff
`c` (the products are equal as functions: `mulEval_eq_mulStrassenWith`,
`mulTruncEval_eq_mulTruncColumnStrassenWith`), so CompPoly's PM-basis correctness theorems
(`PMBasis/Correctness.lean`, stated on that runtime) hold of it by rewriting; `evalPMBasisContext`
packages them.
-/

namespace LeanVM.Extraction.Fast.EvalMat

open CompPoly PolynomialMatrix Approximant

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- **The PM-basis runtime on evaluation-domain products.** -/
@[expose] def evalRuntime (T : EvalTransform F) (mulCtx : CPolynomial.MulContext F)
    (lowCtx : MulLowContext F) (leafCutoff : ℕ) : PMBasisRuntime F where
  mulContext := mulCtx
  lowMulContext := lowCtx
  composeBasis := mulEval T mulCtx
  residualProduct := mulTruncEval T mulCtx
  leafCutoff := leafCutoff
  leafBasis := kernelLeafBasis

/-- **The runtime is CompPoly's**, at every composition cutoff. -/
theorem evalRuntime_eq (T : EvalTransform F) (mulCtx : CPolynomial.MulContext F)
    (lowCtx : MulLowContext F) (leafCutoff composeLeafCutoff : ℕ) :
    evalRuntime T mulCtx lowCtx leafCutoff =
      kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff composeLeafCutoff := by
  rw [evalRuntime, kernelLeafRuntimeWithLowAndCompose]
  congr 1
  · exact funext fun A ↦ funext fun B ↦ mulEval_eq_mulStrassenWith T mulCtx lowCtx _ A B
  · exact funext fun orders ↦ funext fun A ↦ funext fun B ↦
      mulTruncEval_eq_mulTruncColumnStrassenWith T mulCtx lowCtx _ orders A B

/-- PM-basis on the evaluation-domain runtime is CompPoly's. -/
theorem pmBasis_evalRuntime (T : EvalTransform F) (mulCtx : CPolynomial.MulContext F)
    (lowCtx : MulLowContext F) (leafCutoff composeLeafCutoff : ℕ) :
    pmBasis (evalRuntime T mulCtx lowCtx leafCutoff) =
      pmBasis (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff composeLeafCutoff) := by
  rw [evalRuntime_eq T mulCtx lowCtx leafCutoff composeLeafCutoff]

/-- **The PM-basis context on evaluation-domain products**: CompPoly's soundness and shifted
minimality, carried over through `evalRuntime_eq`. -/
@[expose] def evalPMBasisContext (T : EvalTransform F) (mulCtx : CPolynomial.MulContext F)
    (lowCtx : MulLowContext F) (leafCutoff : ℕ) : PMBasisContext F where
  runtime := evalRuntime T mulCtx lowCtx leafCutoff
  basis := pmBasis (evalRuntime T mulCtx lowCtx leafCutoff)
  sound := by
    intro problem shift row hrow
    rw [evalRuntime_eq T mulCtx lowCtx leafCutoff 0] at hrow ⊢
    exact pmBasis_kernelLeaf_approximates mulCtx lowCtx leafCutoff 0 problem shift hrow
  complete_minimal := by
    let : DecidableEq F := instDecidableEqOfLawfulBEq
    intro problem shift row hpos hwf happrox hnz hwidth
    rw [evalRuntime_eq T mulCtx lowCtx leafCutoff 0] at happrox ⊢
    exact pmBasis_kernelLeaf_complete_minimal mulCtx lowCtx leafCutoff 0 problem shift row hpos
      hwf happrox hnz hwidth

/-- Its basis is CompPoly's kernel-leaf PM-basis, at every composition cutoff. -/
theorem evalPMBasisContext_basis (T : EvalTransform F) (mulCtx : CPolynomial.MulContext F)
    (lowCtx : MulLowContext F) (leafCutoff composeLeafCutoff : ℕ) :
    (evalPMBasisContext T mulCtx lowCtx leafCutoff).basis =
      (kernelLeafPMBasisContextWithLowAndCompose mulCtx lowCtx leafCutoff
        composeLeafCutoff).basis := by
  show pmBasis _ = pmBasis _
  rw [evalRuntime_eq T mulCtx lowCtx leafCutoff composeLeafCutoff]

end

end LeanVM.Extraction.Fast.EvalMat
