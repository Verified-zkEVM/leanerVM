module

public import LeanVM.Cost.Extractor.PMEval
public import LeanVM.Cost.Bounds.PMBasis.Defs

/-!
# The PM-basis's two matrix products: the prices this proof takes from track fft

The PM-basis node multiplies twice: the composition `P₂·P₁` (`mulEvalPC`) and the residual's
column-truncated product `P₁·A` (`mulTruncEvalPC`). Their prices are track fft's to prove
(`Cost/Bounds/PMFFT/`); here they are stated as the propositions this proof assumes
(`MulEvalPCost`, `MulTruncEvalPCost`), in the model's `evalMatPrice` (`Bounds/PMBasis/Defs.lean`):

* `MulEvalPCost P p`: `A` of degree at most `dA`, `B` of degree at most `dB`, `2^36` points at
  most: `mulEvalPC A B ≤ evalMatPrice p |A| |B| (width B) dA dB`;
* `MulTruncEvalPCost P p`: the same with the orders at most `O`, the degrees capped at `O − 1`,
  and `ovh·(R·S + S·T + R·T)·(O + 1)` for the entries truncated at `O`.

They are track fft's `mulEvalPC_cost`, `mulTruncEvalPC_cost` (`INTERFACES.md`), less their
`FFTPricesOK p`, which the composition discharges at `marginPrices`.
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

/-- **The composition's price** (track fft's `mulEvalPC_cost`, as published in
`INTERFACES.md`, assumed here): transforms of size at most `2^36`. -/
@[expose] def MulEvalPCost (P : MachineProgram) (p : PMPrices) : Prop :=
  ∀ (A B : PolynomialMatrix K) (dA dB : ℕ), DegLe A dA → DegLe B dB →
    clog2 (dA + dB + 1) ≤ 36 → A.size < 2 ^ 32 → B.size < 2 ^ 32 → MatrixWidth B < 2 ^ 32 →
    machineCost P mulEvalPC.costIdx [encodeValue A, encodeValue B] ≤
      evalMatPrice p A.size B.size (MatrixWidth B) dA dB

/-- **The column-truncated product's price** (track fft's `mulTruncEvalPC_cost`, as published
in `INTERFACES.md`, assumed here): the entries truncated at the largest order `O` first, the extra
`ovh·(R·S + S·T + R·T)·(O + 1)`. -/
@[expose] def MulTruncEvalPCost (P : MachineProgram) (p : PMPrices) : Prop :=
  ∀ (orders : Array ℕ) (A B : PolynomialMatrix K) (dA dB O : ℕ), DegLe A dA → DegLe B dB →
    (∀ c, orders.getD c 0 ≤ O) → clog2 (min dA (O - 1) + min dB (O - 1) + 1) ≤ 36 →
    A.size < 2 ^ 32 → B.size < 2 ^ 32 → MatrixWidth B < 2 ^ 32 → O < 2 ^ 40 →
    machineCost P mulTruncEvalPC.costIdx [encodeValue orders, encodeValue A, encodeValue B] ≤
      evalMatPrice p A.size B.size (MatrixWidth B) (min dA (O - 1)) (min dB (O - 1)) +
        p.ovh * ((A.size * B.size + B.size * MatrixWidth B + A.size * MatrixWidth B) * (O + 1))

end

end LeanVM.Cost.Bounds.PMCore
