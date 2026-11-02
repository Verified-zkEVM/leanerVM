module

public import LeanVM.Cost.Bounds.PMSolve.Interp
public import LeanVM.Cost.Bounds.PMFFT.InvCost
public import LeanVM.Cost.Bounds.PMCore.At28_4

/-!
# Bounds: the lanes' interpolation within its price, the hypotheses discharged

The products, truncated products and Newton inverses at sizes `≤ N` (track fft's
`mulViaFFTC_cost`, `rawMulLowFFTC_cost`, `inverseModXFFTC_cost`): `mulBound_fft`, `lowBound_fft`,
`invBound_fft`, at the prices `fftMB`, `fftLB`, `fftIB`; the PM-basis core (track pmcost's
`pmCoreC_cost_le_model`, the leaf's `leafCost`): `pmCoreCostAt_model`.

**`interpolatePMC_cost_model`**: the lanes' interpolation at most `interpPMModel p n params`, on
the shapes `PMInterpOK n params` (decidable: the sizes, the transforms within `2^36` points, the
core's shift bound, the leaf within the model's leaf price).
-/

namespace LeanVM.Cost.Bounds.PMSolve

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open LeanVM.Cost.Bounds.PMBasis

public section

/-- A product at sizes `≤ N`. -/
@[expose] def fftMB (p : PMPrices) (N : ℕ) : ℕ := polyMulPrice p (clog2 (2 * N)) + 2 ^ 32

/-- A truncated product at precision and sizes `≤ N`. -/
@[expose] def fftLB (p : PMPrices) (N : ℕ) : ℕ :=
  polyMulPrice p (clog2 (2 * N)) + 2 ^ 32 + 49 * N + 46

/-- Newton's inverse at precision `≤ N`. -/
@[expose] def fftIB (p : PMPrices) (N : ℕ) : ℕ :=
  clog2 N * (2 * polyMulPrice p (clog2 (2 * N)) + 2 * 2 ^ 32 + 224 * N + 500) + N + 19740

variable (P : MachineProgram)

theorem mulBound_fft (hP : Includes P mulViaFFTC.costDeps) (p : PMPrices)
    (hp : PMFFT.FFTPricesOK p) (N : ℕ) (hN : 2 * N ≤ 2 ^ 36) : MulBound P N (fftMB p N) := by
  intro f g hf hg
  have := PMFFT.mulViaFFTC_cost P hP p hp f g (by omega)
  have := polyMulPrice_mono p (clog2_mono (show f.val.size + g.val.size - 1 ≤ 2 * N by omega))
  unfold fftMB
  unfold PMFFT.karMax at *
  omega

theorem lowBound_fft (hP : Includes P rawMulLowFFTC.costDeps) (p : PMPrices)
    (hp : PMFFT.FFTPricesOK p) (N : ℕ) (hN : N ≤ 2 ^ 35) : LowBound P N (fftLB p N) := by
  intro k a b hk _ _
  have := PMFFT.rawMulLowFFTC_cost P hP p hp k (by omega) a b
  have := polyMulPrice_mono p (clog2_mono (show 2 * k - 1 ≤ 2 * N by omega))
  unfold fftLB
  unfold PMFFT.karMax at *
  omega

theorem invBound_fft (hP : Includes P inverseModXFFTC.costDeps) (p : PMPrices)
    (hp : PMFFT.FFTPricesOK p) (N : ℕ) (hN : N ≤ 2 ^ 35) : InvBound P N (fftIB p N) := by
  intro k a hk _
  have := PMFFT.inverseModXFFTC_cost P hP p hp k (by omega) a
  have h1 := polyMulPrice_mono p (clog2_mono (show 2 * k - 1 ≤ 2 * N by omega))
  have h2 : PMFFT.newtonStep p k ≤
      2 * polyMulPrice p (clog2 (2 * N)) + 2 * 2 ^ 32 + 224 * N + 500 := by
    unfold PMFFT.newtonStep PMFFT.karMax
    omega
  have h3 := Nat.mul_le_mul (clog2_mono hk) h2
  unfold fftIB
  omega

/-- **The PM-basis core within the model**, given the leaf within the model's leaf price. -/
theorem pmCoreCostAt_model (hP : Includes P pmCoreC.costDeps) (p : PMPrices)
    (hp : PMFFT.FFTPricesOK p) {r m SB : ℕ} (hr : 2 ≤ r) (hm : m ≤ r) (hr28 : r < 2 ^ 28)
    (hSB : SB < 2 ^ 39) (hleaf : PMCore.leafBound r m + 18 * m + 60 ≤ pmLeafPrice p r) :
    PMCoreCostAt P p r m SB := by
  intro problem shift hI
  have hL := PMCore.leafCost P hP (r := r) (m := m) (SB := SB) (by omega) (by omega) hSB
  refine PMCore.pmCoreC_cost_le_model P hP hp hr hm (by omega) hSB (fun pr sh hI' ho ↦ ?_)
    (by omega) problem shift hI
  have := hL pr sh hI' ho
  omega

/-- The shapes where the interpolation's price is proved: the sizes, the transforms within `2^36`
points, the core's shift bound, the leaf within the model's leaf price. -/
@[expose] def PMInterpOK (p : PMPrices) (n : ℕ) (params : GuruswamiSudan.GSInterpParams) : Prop :=
  PMInterpSizes n params ∧ 2 * ((params.multiplicity + 1) * n + 1) ≤ 2 ^ 36 ∧
    3 * params.weightedDegreeBound + 1 + 2 * (params.multiplicity * n + 3) < 2 ^ 39 ∧
    3 * (params.multiplicity * n + 1 + params.weightedDegreeBound + 2) ≤ 2 ^ 37 ∧
    PMCore.leafBound (GuruswamiSudan.interpolationWidth params + params.multiplicity)
        params.multiplicity + 18 * params.multiplicity + 60 ≤
      pmLeafPrice p (GuruswamiSudan.interpolationWidth params + params.multiplicity)

instance (p : PMPrices) (n : ℕ) (params : GuruswamiSudan.GSInterpParams) :
    Decidable (PMInterpOK p n params) := by
  unfold PMInterpOK PMInterpSizes; infer_instance

/-- **The interpolation's proved price** at prices `p`, `n` points. -/
@[expose] def interpPMModel (p : PMPrices) (n : ℕ) (params : GuruswamiSudan.GSInterpParams) : ℕ :=
  let N := (params.multiplicity + 1) * n + 1
  interpPMCost p N n params.multiplicity (GuruswamiSudan.interpolationWidth params)
    params.weightedDegreeBound (fftMB p N) (fftLB p N) (fftIB p N)

/-- **The lanes' interpolation, compiled, within its proved price** (`interpolatePMC`): no
hypothesis but the shape's (`PMInterpOK`, decidable) and the chain's `InterpSizes`. -/
theorem interpolatePMC_cost_model (hP : Includes P interpolatePMC.costDeps) (p : PMPrices)
    (hp : PMFFT.FFTPricesOK p) (points : Array (K × K)) (params : GuruswamiSudan.GSInterpParams)
    (hok : PMInterpOK p points.size params) (hsz : InterpSizes points.size params)
    (hk : 1 < params.messageDegree) :
    machineCost P interpolatePMC.costIdx [encodeValue points, encodeValue params] ≤
      interpPMModel p points.size params := by
  obtain ⟨hpm, hN36, hSB, h37, hleaf⟩ := hok
  have hpm' := hpm
  obtain ⟨hn1, hm1, hmw, hw20, hN45, hW40⟩ := hpm'
  exact interpolatePMC_cost P (by includes) p points params
    (mulBound_fft P (by includes) p hp _ hN36) (lowBound_fft P (by includes) p hp _ (by omega))
    (invBound_fft P (by includes) p hp _ (by omega))
    (pmCoreCostAt_model P (by includes) p hp (by omega) (by omega) (by omega) hSB hleaf)
    (by omega) h37 hsz hpm hk

end

end LeanVM.Cost.Bounds.PMSolve
