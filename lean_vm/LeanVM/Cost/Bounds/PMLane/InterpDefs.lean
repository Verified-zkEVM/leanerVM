module

public import LeanVM.Cost.Bounds.PMBasis.LaneDefs

/-!
# The interpolation's proved price, as definitions

The price formulas of the lanes' interpolation bound (`interpolatePMC_cost_price`,
`Bounds/PMSolve/Final.lean`), which holds at the shapes where `PMInterpOK n params` and
`interpPMModel marginPrices n params ≤ interpPMPrice marginPrices n params`, both decided per shape
in `Bounds/PMLane/Shapes.lean`. Definitions only, in the namespaces of the proofs that use them
(`PMFFT`: the transforms' Newton inverse; `PMCore`: the PM-basis leaf; `PMSolve`: the lift, the
certified solve, the GS data, the interpolation), so that the shape checks import no proof
(`Bounds/PMLane/ShapesFirewall.lean`).
-/

namespace LeanVM.Cost.Bounds.PMFFT

open LeanVM.Parameters LeanVM.Extraction CompPoly LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Bounds.PMBasis

public section

/-- The schedule's Karatsuba branch's price. -/
@[expose] def karMax : ℕ := 2 ^ 29

/-- Newton's price per step beyond its two products, at precision `≤ k`: the `karMax` and the
`2^20` of each product (the latter left over from the products' telescoping), the subtraction. -/
@[expose] def newtonExtra (k : ℕ) : ℕ := 2 * karMax + 161 * k + 2 ^ 21 + 207

/-- **Newton's inverse modulo `X^k`, proved price**: four products at the last precision (the
precisions `2, 4, …, k` double, so do the products' prices: their sum is at most twice the last's,
two products a step) and `⌈log₂ k⌉` times `newtonExtra k`, the inversion of the constant term. -/
@[expose] def newtonBound (p : PMPrices) (k : ℕ) : ℕ :=
  4 * polyMulPrice p (clog2 (2 * k - 1)) + clog2 k * newtonExtra k + k + 2863

end

end LeanVM.Cost.Bounds.PMFFT

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Parameters LeanVM.Extraction CompPoly LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Bounds.PMBasis

public section

/-- The price of one pivot of the RREF on `E` rows of at most `r` entries. -/
@[expose] def pivotPrice (E r : ℕ) : ℕ := 2871 * r + (69 * r + E + 87) * E + 3 * E + 100

/-- The price of one step of the pivot table on rows of width `r`. -/
@[expose] def stepPrice (r : ℕ) : ℕ := 1774 * r + 3567

/-- The price of one incremental insertion beyond the rank potential, `r` rows wide. -/
@[expose] def incPrice (r : ℕ) : ℕ :=
  (r + 1) * (stepPrice r + 18) + (84 * r + 66) * (r + 1) + (39 * r + 30) * r + 23 * r + 110

/-- **The leaf's price**, `n` rows, `m` orders, at order at most one. -/
@[expose] def leafBound (n m : ℕ) : ℕ :=
  -- the reduced kernel rows
  (36 * m + 26) +
    (36 * m + 26 + (m * m + 160 * m + 64) + (69 * n + 45) * m + 20) + 1 +
    ((n + 1) * (42 * m + 80) + m * pivotPrice m n + (33 * n + 55) * n * n + (16 * n + 90) * n + 70) +
    3 * n + ((129 * n + 34) * n + 3) + n +
    (36 * m + ((25 + 83) * n + 36) * n + 18 * n + 50) + 2 * n +
    (stepPrice n * (2 * n * (2 * n)) + (incPrice n + 16) * (2 * n) + 11) + 28 +
  -- the slots filled
    (n + (191 * n + 126) * n + 12) + ((36 * m + 108 * n + 75) * n + 6) + n + 18 + 6 +
  -- the compaction
    ((29 * n + 28) * n + 8)

end

end LeanVM.Cost.Bounds.PMCore

namespace LeanVM.Cost.Bounds.PMSolve

open LeanVM.Parameters LeanVM.Extraction CompPoly LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Bounds.PMBasis

public section

/-- A product of at most `N` coefficients. -/
@[expose] def fftMB (p : PMPrices) (N : ℕ) : ℕ := polyMulPrice p (clog2 N) + 2 ^ 32

/-- A truncated product at precision `≤ N`. -/
@[expose] def fftLB (p : PMPrices) (N : ℕ) : ℕ :=
  polyMulPrice p (clog2 (2 * N)) + 2 ^ 32 + 49 * N + 46

/-- Newton's inverse at precision `≤ N` (the telescoped `PMFFT.newtonBound`). -/
@[expose] def fftIB (p : PMPrices) (N : ℕ) : ℕ := PMFFT.newtonBound p N

/-- The lift's price: `w·m` entries reduced on the first branch, `−diag(M)`, the orders. -/
@[expose] def liftPrice (Q w m : ℕ) : ℕ :=
  w * (m * (120 * Q + 203) + 48) + m * (m * (16 * Q + 53) + 48) + w + 40 * m + 90

/-- **The certified solve's price** (`certifiedSolveC_cost`): the lift twice, the PM-basis core
(`pmTreeEval`), the basis rows' certificates and principal parts, the guard and the shifts. -/
@[expose] def certSolveCost (p : PMPrices) (L Q w m o : ℕ) : ℕ :=
  2 * liftPrice Q w m + pmTreeEval 1 L (pmNodePrice p (w + m) m) o +
    (w + m) * (90 * (w + m) + 78) + (37 * w + 32) * (w + m) + 4 * (w + m) + 50 * w + 72 * m + 300

/-- The column's step's price (`colStep`). -/
@[expose] def colStep (N w MB LB LBq : ℕ) : ℕ := MB + LB + LBq + 1350 * N + 4 * w + 1500

/-- The column's price. -/
@[expose] def colPrice (N w MB LB LBq IB : ℕ) : ℕ :=
  IB + w * (colStep N w MB LB LBq + 9) + 150 * N + 30 * w + 300

/-- The matrix's price: `m` columns, the matrix assembled. -/
@[expose] def matPrice (N w m MB LB LBq IB : ℕ) : ℕ :=
  m * (colPrice N w MB LB LBq IB + 25) + w * (m * 42 + 48) + 20 * m + 100

/-- The GS data's price. -/
@[expose] def dataPrice (N m w MB LB LBq IB : ℕ) : ℕ :=
  (MB + m + 40) * (m - 1) + 34 * m + 120 + matPrice N w m MB LB LBq IB + 40 * w + 80

/-- **The interpolation's price** (`interpolatePMC_cost`): `G` and `R` (the chain's), the GS data,
the certified solve, the least row, the row read and normalized. -/
@[expose] def interpPMCost (p : PMPrices) (L N n m w W MB LB LBq IB : ℕ) : ℕ :=
  3720 * (n * n) + 1700 * ((n + 1) * n) + 27100 * n + 1000 + dataPrice N m w MB LB LBq IB +
    certSolveCost p L (m * n + 1) w m (m * n + W + 2) + (90 * w + 130) * (w + m) +
    (3 * (m * n + W + 2 + 2) + 41) * w + normBound W w + 200

/-- The sizes the interpolation's price reads, besides the chain's `InterpSizes`. -/
@[expose] def PMInterpSizes (n : ℕ) (params : GuruswamiSudan.GSInterpParams) : Prop :=
  1 ≤ n ∧ 1 ≤ params.multiplicity ∧
    params.multiplicity ≤ GuruswamiSudan.interpolationWidth params ∧
    GuruswamiSudan.interpolationWidth params < 2 ^ 20 ∧
    (params.multiplicity + 1) * n + 1 < 2 ^ 45 ∧ params.weightedDegreeBound < 2 ^ 40

instance (n : ℕ) (params : GuruswamiSudan.GSInterpParams) : Decidable (PMInterpSizes n params) := by
  unfold PMInterpSizes; infer_instance

/-- The shapes where the interpolation's price is proved: the sizes, the products within `2^36`
points, the core's shift bound. -/
@[expose] def PMInterpOK (n : ℕ) (params : GuruswamiSudan.GSInterpParams) : Prop :=
  PMInterpSizes n params ∧ (params.multiplicity + 1) * n + 1 ≤ 2 ^ 35 ∧
    4 * params.weightedDegreeBound + 2 * (params.multiplicity * n) + 7 < 2 ^ 39 ∧
    3 * (params.multiplicity * n + 1 + params.weightedDegreeBound + 2) ≤ 2 ^ 37

instance (n : ℕ) (params : GuruswamiSudan.GSInterpParams) : Decidable (PMInterpOK n params) := by
  unfold PMInterpOK PMInterpSizes; infer_instance

/-- **The interpolation's proved price** at prices `p`, `n` points: the products of at most
`N = (m + 1)·n + 1` coefficients, the back-products at precision `m·n`, the quotients and the
inverses at precision `n`, the PM-basis leaf at its proved price. -/
@[expose] def interpPMModel (p : PMPrices) (n : ℕ) (params : GuruswamiSudan.GSInterpParams) : ℕ :=
  let m := params.multiplicity
  let w := GuruswamiSudan.interpolationWidth params
  let N := (m + 1) * n + 1
  interpPMCost p (PMCore.leafBound (w + m) m + 21 * m + 32) N n m w params.weightedDegreeBound
    (fftMB p N) (fftLB p (m * n)) (fftLB p n) (fftIB p n)

end

end LeanVM.Cost.Bounds.PMSolve
