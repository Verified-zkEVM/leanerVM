module

public import LeanVM.Protocol.Extraction.Extractor
public import Statement.CostMachine
public import LeanVM.Cost.Prices

/-!
# Bounds: the decoder's bounds, as definitions

The bounds the decoder's proofs (`Bounds/Decoder/*.lean`) establish, from Roth–Ruckenstein's
nodes and the roots in `K` up to `decoderBound`, and `DecoderShapeOk` (`DecoderLaneSizes` and the
decoder's bound at most `listDecoderWorstPrice`), which `Bounds/DecoderShapes.lean` decides at each
admissible shape by kernel evaluation. They are here, apart from their proofs, so that those
checks import only what they evaluate (the extractor's parameter search and these numbers): an
edit of a proof rebuilds no check (`Bounds/DecoderShapesFirewall.lean` guards it).
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Parameters CompPoly CompPoly.GuruswamiSudan LeanVM.Extraction

public section

/-- The bound of `L` levels of the butterfly Taylor shift on at most `Y` rows of at most `X`
coefficients: per level a power by squaring and `Y` entries, each at most a scaled sum of rows. -/
@[expose] def bfLoopBound (X Y L : ℕ) : ℕ :=
  L * ((324 * X + 160) * Y + 535 * (Nat.log2 Y + 1) + 100) + 20

/-- The bound of the substitution on `Y` rows of at most `X` coefficients: the butterfly's
`log₂ Y + 1` levels, then each row shifted. -/
@[expose] def substBound (X Y : ℕ) : ℕ :=
  bfLoopBound X Y (Nat.log2 Y + 1) + (28 * (X + Y) + 90) * Y + 50

/-- The bound of a product modulo `u`, operands and `u` of at most `B` coefficients. -/
@[expose] def mulModBound (B : ℕ) : ℕ := 2500 * (B * B) + 1000 * B + 20000

/-- The bound of a remainder, operands of at most `B` coefficients. -/
@[expose] def rawModBound (B : ℕ) : ℕ := 400 * (B * B) + 2100 * B + 41000

/-- The bound of a monic gcd's step, operands of at most `B` coefficients. -/
@[expose] def gcdStepBound (B : ℕ) : ℕ := rawModBound B + 61 * B + 60

/-- The bound of a monic gcd, operands of at most `B` coefficients. -/
@[expose] def gcdBound (B : ℕ) : ℕ := gcdStepBound B * (2 * B + 1) + 430 * B + 20100

/-- The bound of `k` Frobenius powers modulo `u`, `u` of at most `B` coefficients. -/
@[expose] def frobBound (B k : ℕ) : ℕ := (2 * mulModBound B + 23 * B + 70) * k + 450 * B + 21000

/-- The bound of the trace polynomial over `64` powers of at most `B` coefficients. -/
@[expose] def traceBound (B : ℕ) : ℕ := (1040 * B + 1200) * 64 + 1200

/-- The bound of one base constant's child. -/
@[expose] def refineLamBound (B : ℕ) : ℕ := gcdBound B + 520 * B + 20300

/-- The bound of one factor's refinement, the factor of at most `B` coefficients, the cache of at
most `L` entries of at most `C` coefficients. -/
@[expose] def refineFactorBound (B C L : ℕ) : ℕ :=
  450 * B + 20000 + (15 * B + 3 * C + 20) * L + frobBound B 64 + traceBound B +
    2 * (refineLamBound B + 9) + 300

/-- The slope of a factor's refinement in its size, factors of at most `B` coefficients:
`refineFactorBound b C L ≤ b·refineSlope B + 2846718 + (15·b + 3·C + 20)·L` for `b ≤ B`. -/
@[expose] def refineSlope (B : ℕ) : ℕ := 1600 * (B * B) + 329444 * B + 367394

/-- The bound of one trace coordinate over the factors (`refineFactorsFast`), at most `F` factors
of at most `B` coefficients, their sizes summing to at most `S`, the cache of at most `L`
entries: each factor priced at its own size. -/
@[expose] def refineFactorsBound (B S F L : ℕ) : ℕ :=
  S * refineSlope B + (2846718 + 2 * F + 33) * F + 15 * S * L + (3 * B + 20) * F * L + 15

/-- The bound of the splitter on a polynomial of at most `B` coefficients: `64` trace
coordinates, each over factors of sizes summing to at most `2·B`, at most `B` of them, the cache
of at most `64·B` entries. -/
@[expose] def splitBound (B : ℕ) : ℕ :=
  64 * (refineFactorsBound B (2 * B) B (64 * B) + 40) + 450 * B + 23000

/-- The bound of the root product, `p` of at most `B` coefficients. -/
@[expose] def rootProductBound (B : ℕ) : ℕ :=
  gcdBound B + 1500 * B + 65000 + (2 * mulModBound B + 50) * 65

/-- **The roots of `F` linear factors**, validated against `p` (of at most `B` coefficients),
deduplicated: at most `rootsFromBound B F`. -/
@[expose] def rootsFromBound (B F : ℕ) : ℕ := (272 * B + 20100) * F + (16 * F + 30) * F + 40

/-- The bound of the roots in `K` of a polynomial of at most `B` coefficients. -/
@[expose] def rootsBound (B : ℕ) : ℕ :=
  20 * B + 60 + rootsFromBound B 1 + rootProductBound B + splitBound B + (B + 30) * B + 3 * B +
    10 + rootsFromBound B B

/-- The price of a node of `Y` rows of at most `X` coefficients, beyond its children: the
`X`-adic order, the division by `X^s`, the initial coefficient polynomial, its roots. -/
@[expose] def rrNodePrice (X Y : ℕ) : ℕ :=
  (65 * X + 220) * Y + rootsBound Y + 200

/-- The price of a child in its parent's fold, `k` the depth bound: the substitution, the
truncation, the prefix extended. -/
@[expose] def rrChildPrice (X Y k : ℕ) : ℕ :=
  substBound X Y + (27 * (X + Y) + 80) * Y + 222 * k + 400

/-- The bound of Roth–Ruckenstein's search on `1 + k·ℓ` nodes of `Y` rows of at most `X`
coefficients, `k` levels. -/
@[expose] def rrBound (X Y k ℓ : ℕ) : ℕ :=
  (rrNodePrice X Y + rrChildPrice X Y k + Y * k) * (1 + k * ℓ)

/-- The bound of a product over `K[X]`: `≤ rp` rows of entries of `≤ a` coefficients by `≤ rq`
rows, the two factors' entry sizes summing to at most `s`. -/
@[expose] def mulBBound (rp rq a s : ℕ) : ℕ :=
  3 * ((930 * (((a + 1) * (s + 1)) * rq) + 110 * (s * (rp + rq)) + 200 * (rp + rq) + 112) * rp) +
    (3 * s + 41) * (rp + rq) + 100

/-- A row `i ≤ m`: the product `G^(m−i)·(Y − R)^i` and its coefficient row. -/
@[expose] def rowProdBound (m w N : ℕ) : ℕ :=
  mulBBound 1 (m + 1) (m * N + 1) (m * N + 2) + 34 * w + 50

/-- A row `i > m`: the shift `Y^(i−m)·(Y − R)^m` and its coefficient row. -/
@[expose] def rowShiftBound (m w N : ℕ) : ℕ :=
  (3 * (m * N + 1) + 41) * (w + m + 1) + 2 * w + m + 34 * w + 60

/-- The bound of `leeRowsFast`: `Y − R` and `G`, the `m + 1` powers of each, `m + 1` products
`G^(m−i)·(Y − R)^i` and `w` shifts, `w` coefficient rows. -/
@[expose] def leeRowsBound (m w N : ℕ) : ℕ :=
  703 * (N + 1) + 2460 + (mulBBound 2 (m + 1) (N + 1) ((m + 1) * N + 2) + 3 + 20) * (m + 1) +
    (mulBBound 1 1 (N + 1) ((m + 1) * N + 2) + 3 + 20) * (m + 1) + 2 * (m + 1) + 18 * w +
    (rowProdBound m w N + 11) * (m + 1) + (rowShiftBound m w N + 11) * w + 120

/-- The price of one iteration on `r` rows of width `w`, shifted degrees at most `D`: the
leading positions, the conflict search, one step. -/
@[expose] def msIterBound (r w D : ℕ) : ℕ :=
  190 * (w * r) + 64 * (r * r) + 740 * ((D + 1) * w) + 184 * r + 970 * w + 30 * D + 21200

/-- The bound of the normalization on `rows` rows. -/
@[expose] def normBound (W rows : ℕ) : ℕ :=
  (20057 * (W + 1) + 265) * rows + 121

/-- The bound of the interpolation on `n` points, multiplicity `m`, `w = ℓ + 1` columns, the
basis's degree bound `D`, the weighted degree `W`. -/
@[expose] def interpCoreBound (n m w D W : ℕ) : ℕ :=
  3720 * (n * n) + 1700 * ((n + 1) * n) + 30000 * n + 1000 + leeRowsBound m w n + 40 * w +
    ((w * ((D + 1) * (w + 1)) + 1) * msIterBound w w D + 90 * (w * w) + 77 * w + 66) +
    ((90 * w + 140) * w + 40) + (90 * w + 30) + ((3 * (D + 1) + 41) * w + 17) + normBound W w + 80

/-- The sizes the interpolation's bound needs, all word-sized. -/
@[expose] def InterpSizes (n : ℕ) (params : GSInterpParams) : Prop :=
  n < 2 ^ 55 ∧ params.weightedDegreeBound + 1 < 2 ^ 60 ∧ params.messageDegree < 2 ^ 64 ∧
    yWeight params * (params.weightedDegreeBound + 1) < 2 ^ 64 ∧
    interpolationYCap params + 1 < 2 ^ 55 ∧ params.multiplicity < 2 ^ 55 ∧
    (params.multiplicity + 1) * n + 2 < 2 ^ 55 ∧
    2 * (params.multiplicity * n + interpolationYCap params * yWeight params + 1) +
      interpolationYCap params * yWeight params < 2 ^ 62 ∧
    (interpolationYCap params + 2) * (interpolationYCap params + 2) *
      (params.multiplicity * n + interpolationYCap params * yWeight params +
        interpolationYCap params * yWeight params + 2) < 2 ^ 64

/-- The bound of one lane's Guruswami–Sudan run on `n` points: the interpolation, the truncation,
Roth–Ruckenstein's search (`rrBound`), the filter. -/
@[expose] def gsRunBound (n : ℕ) (params : GSInterpParams) : ℕ :=
  interpCoreBound n params.multiplicity (interpolationYCap params + 1)
      (params.multiplicity * n + interpolationYCap params * yWeight params)
      params.weightedDegreeBound + 10 +
    ((27 * (params.weightedDegreeBound + 1) + 80) * (interpolationYCap params + 1) + 40) +
    rrBound (params.weightedDegreeBound + 1) (interpolationYCap params + 2) params.messageDegree
      (interpolationYCap params) +
    ((272 * params.messageDegree + 34) * n + 50) * max 1 (interpolationYCap params) + 40

/-- The price of one lane beyond its Guruswami–Sudan run: at most `L` candidates of at most `k`
coefficients, `N = 2^κ`, `M = 2^(κ+R)`. -/
@[expose] def laneExtraBound (κ R L k : ℕ) : ℕ :=
  ((272 * k + 33) * 2 ^ κ + κ * (760 * 2 ^ κ + 19790) + 57) * L +
    ((17 * 2 ^ κ + 22) * L + 30) * L + (50 * 2 ^ κ + 124) * (L * L) +
    (κ * (760 * 2 ^ (κ + R) + 19793) + 30 * 2 ^ (κ + R) + 61) * L + 60

/-- The bound of the pruning over `U` lanes of `n = 2^(κ+R)` columns: the word's table (a column
price `BW`, columns of at most `Lw` symbols), per lane its candidates (`G`) and the pruning step
(`Smax` survivors, `Lc` candidates). -/
@[expose] def pruneBound (κ R U BW Lw G Lc Smax : ℕ) : ℕ :=
  (BW + 10 * Lw + 28) * 2 ^ (κ + R) + 17 * 2 ^ (κ + R) +
    (G + Smax * (Lc * (41 * 2 ^ (κ + R) + 9 * U + 62) + 32) + 60) * U + 17 * U + 80

/-- The bound of a lane's Guruswami–Sudan run (`gsLaneDistinct κ R A`): the parameter search, the
lane's `n = 2^(κ+R)` points (`BS` per symbol), the run (`gsRunBound`). -/
@[expose] def decoderLaneRunBound (κ R A BS : ℕ) : ℕ :=
  190 * gsMultiplicityBoundAt (2 ^ κ) (2 ^ (κ + R)) A + (BS + 28) * 2 ^ (κ + R) +
    gsRunBound (2 ^ (κ + R)) (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp + 200

/-- The sizes at which a lane is bounded: word-sized parameters (`InterpSizes`, …), `k > 1`, at
most `2^20` multiplicities tried. -/
@[expose] def DecoderLaneSizes (κ R A : ℕ) : Prop :=
  κ + R ≤ 30 ∧ A ≤ 2 ^ (κ + R) ∧ gsMultiplicityBoundAt (2 ^ κ) (2 ^ (κ + R)) A < 2 ^ 20 ∧
    InterpSizes (2 ^ (κ + R)) (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp ∧
    1 < (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.messageDegree ∧
    (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.weightedDegreeBound + 1 < 2 ^ 56 ∧
    interpolationYCap (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp + 2 < 2 ^ 28

instance (κ R A : ℕ) : Decidable (DecoderLaneSizes κ R A) := by
  unfold DecoderLaneSizes InterpSizes; infer_instance

/-- The bound of a lane's candidates (`laneEncodedDistinct κ R A`): the run, then at most
`max 1 ℓ` candidates of at most `2^κ` coefficients (`laneExtraBound`). -/
@[expose] def decoderLaneBound (κ R A BS : ℕ) : ℕ :=
  decoderLaneRunBound κ R A BS +
    laneExtraBound κ R (max 1 (interpolationYCap (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp))
      (2 ^ κ)

/-- The bound of the decoder at the shape `(μ, R)` (`κ = μ − 6`, `n = 2^(κ+R)`, the Johnson
threshold `A`): the threshold, the `2^6` lanes pruned (`pruneBound`: the word's table, `BW` per
column and `Lw` symbols per column; a lane `decoderLaneBound`, at most `max 1 ℓ` candidates, at
most `2^18` survivors), a stack per survivor. -/
@[expose] def decoderBound (μ R BW Lw : ℕ) : ℕ :=
  pruneBound (μ - Whir.initialFold) R (2 ^ Whir.initialFold) BW Lw
      (decoderLaneBound (μ - Whir.initialFold) R (johnsonThreshold μ R) 12)
      (max 1 (interpolationYCap (gsParamsFor (2 ^ (μ - Whir.initialFold))
        (2 ^ (μ - Whir.initialFold + R)) (johnsonThreshold μ R)).interp))
      (2 ^ 18) +
    ((15 * 2 ^ Whir.initialFold + 56) * 2 ^ μ + 34) * 2 ^ 18 + 16330

/-- What the decoder's bound needs at a shape, and its value at most the worst. -/
@[expose] def DecoderShapeOk (μ R : ℕ) : Prop :=
  DecoderLaneSizes (μ - Whir.initialFold) R (johnsonThreshold μ R) ∧
    decoderBound μ R 0 0 ≤ listDecoderWorstPrice

instance (μ R : ℕ) : Decidable (DecoderShapeOk μ R) := by
  unfold DecoderShapeOk; infer_instance

end

end LeanVM.Cost.Bounds.Decoder
