/-
  LeanerVM.Protocol.Prove.RomComplete

  The honest prover in the random-oracle model: at admissible sizes and a valid rate it returns a
  proof except with small probability, the probability that a grind runs out of fuel.
-/

module

public import LeanerVM.Protocol.Prove.Hom
public import LeanerVM.Protocol.Prove.Complete
public import LeanerVM.Protocol.ChainGroups
public import LeanerVM.Protocol.ToVCVio.ProofOfWork
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The honest prover's grinds in the random-oracle model

`proveWith hashQuery` is the honest prover with every hash a query to the oracle
`List UInt8 →ₒ Digest`; `runRandom` answers the queries by the lazy random oracle.
`Prove.prEvent_proveWith_eq_none_le`: at sizes admissible with the rate, a prover run of at most
`N` queries returns no proof with probability at most
`(N + 1) (1 - 2^-17)^min(fuel, 2^64) + N^2 / 2^256`, whatever the Flock specification.

The proof needs nothing about where the grinds sit in the run:

1. a run of the lazy random oracle ending at the cache `c` is the run at the hash
   `H_c t := (c t).getD d₀`, `d₀` the zero digest, which clears every grinding check (VCVio's
   `simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching`, `proveWith_simulateQ`);
2. at any hash, the prover returns no proof only when a grind finds no nonce among its `fuel`
   candidates (`Prove.proveWith_eq_none`); at `H_c` each candidate that fails is cached with a
   failing answer, since an uncached one is answered by `d₀`, and the grind's base is `d₀` or a
   cached answer to a grinding-base query: the proof-of-work search `grindSearch` is exhausted;
3. `PowSearch.prEvent_exhausted_le` bounds the probability of an exhausted search.

The candidate nonces are `nonceOf n` for `n < fuel`; `nonceOf` repeats from `2^64` on, so only
`min fuel (2^64)` of them are distinct. At the executable's default fuel, `2^24`, a search fails
with probability `(1 - 2^-17)^(2^24) ≤ e^-128 ≤ 2^-184` (`one_sub_pow_fuel_le`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization Blake2sHash LeanIsa Whir
open OracleComp OracleSpec
open Air.Flat (EnsembleWitness)
open scoped ENNReal

@[expose] public section

namespace Prove

/-! ## The grind as a proof-of-work search -/

/-- The zero digest: it clears every grinding check. -/
def zeroDigest : Digest := Vector.replicate 8 0

theorem lowBitsZero_zeroDigest (bits : ℕ) : FsState.lowBitsZero zeroDigest bits = true := by
  simp [FsState.lowBitsZero, zeroDigest]

/-- The proof-of-work search of a grind of `bits` bits with `fuel` candidates: the bases are the
answers to grinding-base queries `stepBytes cv 0 powBaseTag`, a candidate is
`stepBytes b (nonceOf n) powNonceTag`, and the zero digest is counted from the start. -/
def grindSearch (fuel bits : ℕ) : PowSearch (List UInt8) Digest where
  isBase x := ∃ cv, x = baseInput cv
  cand b n := checkInput b (FsState.nonceOf n)
  ok d := FsState.lowBitsZero d bits = true
  start := zeroDigest
  F := min fuel (2 ^ 64)
  cand_inj {b b' n n'} hn hn' h := by
    obtain ⟨rfl, hblk⟩ := input_inj (b := .nonce (FsState.nonceOf n))
      (c := .nonce (FsState.nonceOf n')) h
    refine ⟨rfl, K.ofBits_inj (lt_of_lt_of_le hn (min_le_right _ _))
      (lt_of_lt_of_le hn' (min_le_right _ _)) ?_⟩
    have := congrArg (fun x : E ↦ x.limb 0) (Block.nonce.inj hblk)
    simpa [FsState.nonceOf] using this
  cand_not_base b {n} _ := by
    rintro ⟨cv, h⟩
    have := Block.parse?_input b (.nonce (FsState.nonceOf n))
    rw [show Block.input b (.nonce (FsState.nonceOf n)) = baseInput cv from h,
      parse?_baseInput] at this
    cases this

/-- A search that found no nonce among `fuel` candidates from `n`: every candidate fails. -/
private theorem findNonce_eq_none {H : List UInt8 → Digest} {base : Digest} {bits fuel n : ℕ}
    (h : Id.run (FsState.findNonce H base bits fuel n) = none) :
    ∀ k < fuel,
      FsState.lowBitsZero (H (checkInput base (FsState.nonceOf (n + k)))) bits = false := by
  induction fuel generalizing n with
  | zero => intro k hk; omega
  | succ fuel ih =>
    intro k hk
    have hid : ∀ t, Id.run (H t) = H t := fun _ ↦ rfl
    simp only [FsState.findNonce, FsState.powOk, Id.run_bind, Id.run_pure, hid] at h
    by_cases hok : FsState.lowBitsZero (H (FsState.stepBytes base (FsState.nonceOf n)
        FsState.powNonceTag)) bits = true
    · simp [hok] at h
    · rw [Bool.not_eq_true] at hok
      simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
      cases k with
      | zero => exact hok
      | succ k =>
        have := ih h k (by omega)
        rwa [show n + 1 + k = n + (k + 1) by omega] at this

/-- **A grind that fails at the cache's hash exhausts a search.** At the hash answering by the
cache `c` and by the zero digest elsewhere, a grind of `bits` bits that finds no nonce among
`fuel` candidates leaves the search from its base exhausted in `c`. -/
private theorem exhausted_of_grind_eq_none (c : hashSpec.QueryCache) {fs : FsState} {fuel bits : ℕ}
    (hbits : bits ≠ 0)
    (h : Id.run (fs.grind (fun t ↦ (c t).getD zeroDigest) fuel bits) = none) :
    (grindSearch fuel bits).Exhausted c := by
  set H : List UInt8 → Digest := fun t ↦ (c t).getD zeroDigest
  have hid : ∀ t, Id.run (H t) = H t := fun _ ↦ rfl
  have hfind : Id.run (FsState.findNonce H (H (FsState.stepBytes fs.cv 0 FsState.powBaseTag))
      bits fuel 0) = none := by
    simp only [FsState.grind, FsState.powBase, hbits, ↓reduceIte, Id.run_bind, hid] at h
    revert h
    rcases Id.run (FsState.findNonce H (H (FsState.stepBytes fs.cv 0 FsState.powBaseTag))
      bits fuel 0) with _ | n
    · simp
    · simp [FsState.absorbNonce]
  refine ⟨H (FsState.stepBytes fs.cv 0 FsState.powBaseTag), ?_, fun n hn ↦ ?_⟩
  · cases hc : c (FsState.stepBytes fs.cv 0 FsState.powBaseTag) with
    | none =>
      refine .inl ?_
      show (c _).getD _ = _
      rw [hc]
      rfl
    | some b =>
      refine .inr ⟨FsState.stepBytes fs.cv 0 FsState.powBaseTag, ⟨fs.cv, rfl⟩, ?_⟩
      show c _ = some ((c _).getD _)
      rw [hc]
      rfl
  · have hfail := findNonce_eq_none hfind n (lt_of_lt_of_le hn (min_le_left _ _))
    rw [Nat.zero_add] at hfail
    cases hc : c (checkInput (H (FsState.stepBytes fs.cv 0 FsState.powBaseTag))
        (FsState.nonceOf n)) with
    | none =>
      have hH : H (checkInput (H (FsState.stepBytes fs.cv 0 FsState.powBaseTag))
          (FsState.nonceOf n)) = zeroDigest := by
        show (c _).getD _ = _
        rw [hc]
        rfl
      rw [hH, lowBitsZero_zeroDigest] at hfail
      cases hfail
    | some d =>
      have hH : H (checkInput (H (FsState.stepBytes fs.cv 0 FsState.powBaseTag))
          (FsState.nonceOf n)) = d := by
        show (c _).getD _ = _
        rw [hc]
        rfl
      rw [hH] at hfail
      exact ⟨d, hc, by simp [grindSearch, hfail]⟩

/-! ## The bound -/

/-- A uniform digest fails a grinding check of `bits ≤ 64` bits with probability at most
`1 - 2^-bits`. -/
private theorem prEvent_not_lowBitsZero {bits : ℕ} (hb : bits ≤ 64) :
    Pr{let d ← $ᵗ Digest}[¬ FsState.lowBitsZero d bits = true] ≤ 1 - (2 ^ bits : ℝ≥0∞)⁻¹ := by
  have h := prEvent_add_prEvent_not_eq_prEvent_true ($ᵗ Digest)
    fun d ↦ FsState.lowBitsZero d bits = true
  rw [prEvent_lowBitsZero hb, OracleComp.prEvent_true_eq_one] at h
  exact ENNReal.le_sub_of_add_le_left (by simp) h.le

/-- **The honest prover in the random-oracle model returns a proof, except with small
probability.** At sizes admissible with the rate, the prover with every hash a query to the lazy
random oracle, a run of at most `N` queries, returns no proof with probability at most
`(N + 1) (1 - 2^-17)^min(fuel, 2^64) + N^2 / 2^256`, whatever the Flock specification. The factor
`N + 1` counts every query that could be a grind's base, and the zero digest, not the few grinds a
proof makes: the bound is loose by design. -/
theorem prEvent_proveWith_eq_none_le (fuel : ℕ) (F : FlockSpec) {prog : Program}
    {input : PublicInput} {κ : ℕ} {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ}
    {s : Sizes} (hws : Sizes.ofWitness w = some s) (hs : s.Admissible prog) (hρ : validRate ρ)
    {N : ℕ} (hN : IsTotalQueryBound (proveWith hashQuery fuel F prog input w ρ) N) :
    Pr{let z ← runRandom (proveWith hashQuery fuel F prog input w ρ)}[z.1 = none] ≤
      (N + 1) * (1 - (2 ^ queryGrindingBits : ℝ≥0∞)⁻¹) ^ min fuel (2 ^ 64) +
        N * N / 2 ^ 256 := by
  have hev : ∀ z ∈ support (runRandom (proveWith hashQuery fuel F prog input w ρ)),
      z.1 = none → (grindSearch fuel queryGrindingBits).Exhausted z.2 := by
    intro z hz hnone
    set H : List UInt8 → Digest := fun t ↦ (z.2 t).getD zeroDigest
    have hrun := QueryCache.evalWithAnswerFn_eq_of_agreesWithFn (f := H)
      (fun t u h ↦ by simp [H, h]) _
      (QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching _ _ hz)
    have hsim := proveWith_simulateQ (r := Id) (fun t ↦ pure (H t)) fuel F prog input w ρ
    have hnone' : proveWith (m := Id) H fuel F prog input w ρ = none :=
      hsim.symm.trans (hrun.trans hnone)
    rcases proveWith_eq_none H fuel F hnone' with hn | ⟨s', hs', hc⟩
    · rw [hws] at hn
      cases hn
    · obtain rfl := Option.some.inj (hws.symm.trans hs')
      rcases hc with h | h | ⟨fs, -, hg⟩
      · exact absurd hs h
      · exact absurd hρ h
      · exact exhausted_of_grind_eq_none z.2 (by decide) hg
  refine (prEvent_mono_of_support _ _ _ hev).trans ?_
  refine ((grindSearch fuel queryGrindingBits).prEvent_exhausted_le
    (prEvent_not_lowBitsZero (by decide)) (by simp) hN).trans_eq ?_
  rw [card_digest, Nat.cast_pow, Nat.cast_ofNat]
  rfl

/-! ## At the default fuel -/

private theorem pow_le_exp :
    ((1 : ℝ) - (2 ^ 17 : ℝ)⁻¹) ^ (2 ^ 24 : ℕ) ≤ Real.exp (-128) := by
  have h := Real.one_sub_div_pow_le_exp_neg (n := 2 ^ 24) (t := 128) (by norm_num)
  rwa [show (128 : ℝ) / ((2 ^ 24 : ℕ) : ℝ) = (2 ^ 17 : ℝ)⁻¹ by norm_num] at h

private theorem exp_le : Real.exp (-128) ≤ (2 ^ 184 : ℝ)⁻¹ := by
  rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) (by positivity)]
  have h := Real.log_two_lt_d9
  have : (2 : ℝ) ^ 184 = Real.exp (((184 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [this]
  exact Real.exp_le_exp.mpr (by push_cast; linarith)

/-- **A grind of 17 bits with `2^24` candidates** fails at a random function with probability
`(1 - 2^-17)^(2^24) ≤ e^-128 ≤ 2^-184`. -/
theorem one_sub_pow_fuel_le :
    (1 - (2 ^ queryGrindingBits : ℝ≥0∞)⁻¹) ^ min (2 ^ 24) (2 ^ 64) ≤ (2 ^ 184 : ℝ≥0∞)⁻¹ := by
  rw [min_eq_left (by norm_num)]
  have e : (1 - (2 ^ queryGrindingBits : ℝ≥0∞)⁻¹) = ENNReal.ofReal (1 - (2 ^ 17 : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_inv_of_pos (by positivity)]
    norm_num [queryGrindingBits]
  have e2 : (2 ^ 184 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((2 ^ 184 : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    norm_num
  rw [e, e2, ← ENNReal.ofReal_pow (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (pow_le_exp.trans exp_le)

end Prove

end
end LeanerVM.Protocol
