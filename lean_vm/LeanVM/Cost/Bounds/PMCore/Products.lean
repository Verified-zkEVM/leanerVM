module

public import LeanVM.Cost.Extractor.PMEval
public import LeanVM.Cost.Bounds.PMBasis.Defs

/-!
# The PM-basis's two matrix products: the prices this proof takes from track fft

The PM-basis node multiplies twice: the composition `P₂·P₁` (`mulEvalPC`) and the residual's
column-truncated product `P₁·A` (`mulTruncEvalPC`). Their prices are track fft's to prove
(`Cost/Bounds/PMFFT/`); here they are stated as the propositions this proof assumes
(`MulEvalPCost`, `MulTruncEvalPCost`), in the model's `evalMatPrice` (`Bounds/PMBasis/Defs.lean`):

* `MulEvalPCost P p`: `A` of degree at most `dA`, `B` of degree at most `dB`, word-sized:
  `mulEvalPC A B ≤ evalMatPrice p |A| |B| (width B) dA dB`;
* `MulTruncEvalPCost P p`: `A` of degree at most `dA`, the orders at most `O ≥ 1`, `B`'s entries
  word-sized (of any degree: the product truncates them at `O`):
  `mulTruncEvalPC orders A B ≤ evalMatPrice p |A| |B| (width B) dA (O − 1)`.
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Parameters LeanVM.Cost.Bounds.PMBasis
open CompPoly CompPoly.PolynomialMatrix

public section

/-- Every entry of `M` has degree at most `d`. -/
@[expose] def DegLe (M : PolynomialMatrix K) (d : ℕ) : Prop :=
  ∀ i j, (rowGet (M.getD i #[]) j).natDegree ≤ d

/-- Every entry of `M` has at most `D` coefficients. -/
@[expose] def SizeLe (M : PolynomialMatrix K) (D : ℕ) : Prop :=
  ∀ i j, (rowGet (M.getD i #[]) j).val.size ≤ D

/-- **The composition's price** (track fft's `mulEvalPC`, assumed here). -/
@[expose] def MulEvalPCost (P : MachineProgram) (p : PMPrices) : Prop :=
  ∀ (A B : PolynomialMatrix K) (dA dB : ℕ), DegLe A dA → DegLe B dB → dA + dB < 2 ^ 40 →
    A.size < 2 ^ 30 → B.size < 2 ^ 30 → MatrixWidth B < 2 ^ 30 →
    machineCost P mulEvalPC.costIdx [encodeValue A, encodeValue B] ≤
      evalMatPrice p A.size B.size (MatrixWidth B) dA dB

/-- **The column-truncated product's price** (track fft's `mulTruncEvalPC`, assumed here). -/
@[expose] def MulTruncEvalPCost (P : MachineProgram) (p : PMPrices) : Prop :=
  ∀ (orders : Array ℕ) (A B : PolynomialMatrix K) (dA O : ℕ), DegLe A dA → 1 ≤ O →
    (∀ c, orders.getD c 0 ≤ O) → SizeLe B (2 ^ 62) → dA + O < 2 ^ 40 →
    A.size < 2 ^ 30 → B.size < 2 ^ 30 → MatrixWidth B < 2 ^ 30 →
    machineCost P mulTruncEvalPC.costIdx [encodeValue orders, encodeValue A, encodeValue B] ≤
      evalMatPrice p A.size B.size (MatrixWidth B) dA (O - 1)

end

end LeanVM.Cost.Bounds.PMCore
