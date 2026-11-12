/-
  LeanerVM.Protocol.HonestGame

  Completeness of the deployed pair for leanISA's constraint statement in the random-oracle
  model: the honest prover's proof, then the verifier on it, both asking one lazy random oracle.
-/

module

public import LeanerVM.Protocol.LeanIsa.Complete
public import LeanerVM.Protocol.Prove.RomComplete
public import LeanerVM.Protocol.Prove.Queries
import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# The honest run in the random-oracle model

For a witness of leanISA's constraint statement whose sizes keep the stack within `2^maxMu`, at a
valid rate, the deployed prover with every hash a query to the lazy random oracle returns no proof
with probability at most `(N + 1) (1 - 2^-17)^min(fuel, 2^64) + N^2 / 2^256`,
`N = 264246250 + 6 · fuel` a bound on its queries (`prove_rom_eq_none_le`); the honest run, the
prover and then the verifier on its proof asking the same oracle (`honestGame`), is rejected with
the same probability (`honestGame_rom_rejects_le`). At the executable's default fuel `2^24` both
are at most `2^-154` (`prove_rom_eq_none_le_default`, `honestGame_rom_rejects_le_default`).

The run is the deterministic run at the hash its final cache defines, where a failing grind leaves
an exhausted proof-of-work search in the cache (`Prove.exhausted_of_grind_eq_none`), which
`PowSearch.prEvent_exhausted_le` bounds given the prover's query count; the count
(`Prove.isTotalQueryBound_proveWith_closed`) is the verifier's phase by phase, with each
commitment's tree and each grind's candidates, maximised over the window of sizes. A proof the
prover returns is accepted at the cache's hash by the deployed pair's completeness
(`Prove.baseProver_complete`), and the verifier's run at the same oracle answers the prover's
queries as the cache does.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization Blake2sHash LeanIsa
open OracleComp OracleSpec Verify
open Air.Flat (EnsembleWitness)
open LeanerVM.Parameters.Whir (queryGrindingBits)
open scoped ENNReal

@[expose] public section

/-- **The deployed prover in the random-oracle model returns a proof, except with small
probability.** For a witness of the constraint statement with sizes `s` that keep the stack within
`2^maxMu`, at a valid rate, the deployed prover with every hash a query to the lazy random oracle
returns no proof with probability at most `(N + 1) (1 - 2^-17)^min(fuel, 2^64) + N^2 / 2^256`,
where `N = 264246250 + 6 · fuel` bounds its queries (`Prove.isTotalQueryBound_proveWith_closed`). -/
theorem prove_rom_eq_none_le (fuel : ℕ) {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} {s : Sizes}
    (hsat : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hμ : leanIsaμ prog s ≤ maxMu) (hρ : validRate ρ) :
    Pr{let z ← runRandom (proveWith hashQuery fuel Blake2sFlock.blake2sFlockSpec prog input w ρ)}[
      z.1 = none] ≤
      (((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) + 1) *
          (1 - (2 ^ queryGrindingBits : ℝ≥0∞)⁻¹) ^ min fuel (2 ^ 64) +
        ((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) * ((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  Prove.prEvent_proveWith_eq_none_le fuel _ hs ((admissible_iff_of_satisfiedBy hsat hs).mpr hμ)
    hρ (Prove.isTotalQueryBound_proveWith_closed fuel hsat hs hμ hρ)

/-- The honest run in the random-oracle model: the deployed prover's proof, then the verifier on
it, both asking the one hash oracle; a prover that returns no proof is rejected. -/
def honestGame (fuel : ℕ) (prog : Program) (input : PublicInput) {κ : ℕ}
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) (ρ : ℕ) : OracleComp hashSpec Bool := do
  match ← proveWith hashQuery fuel Blake2sFlock.blake2sFlockSpec prog input w ρ with
  | none => pure false
  | some proof => verifyWith hashQuery prog input proof

/-- **Completeness of the deployed pair in the random-oracle model.** For a witness of the
constraint statement with sizes `s` that keep the stack within `2^maxMu`, at a valid rate, the
honest run with the hash a lazy random oracle is rejected with probability at most
`(N + 1) (1 - 2^-17)^min(fuel, 2^64) + N^2 / 2^256`, `N = 264246250 + 6 · fuel`: every proof the
prover returns is accepted by the verifier asking the same oracle. -/
theorem honestGame_rom_rejects_le (fuel : ℕ) {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} {s : Sizes}
    (hsat : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hμ : leanIsaμ prog s ≤ maxMu) (hρ : validRate ρ) :
    Pr{let z ← runRandom (honestGame fuel prog input w ρ)}[z.1 = false] ≤
      (((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) + 1) *
          (1 - (2 ^ queryGrindingBits : ℝ≥0∞)⁻¹) ^ min fuel (2 ^ 64) +
        ((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) * ((264246250 + 6 * fuel : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold runRandom honestGame
  rw [simulateQ_bind, StateT.run_bind]
  refine (prEvent_bind_le_add_iSup _ _ (fun z₁ ↦ z₁.1 = none) _).trans ?_
  refine le_of_le_of_eq (add_le_add (prove_rom_eq_none_le fuel hsat hs hμ hρ)
    (le_of_eq (ENNReal.iSup_eq_zero.mpr fun z₁ ↦ ENNReal.iSup_eq_zero.mpr fun hz₁ ↦
      ENNReal.iSup_eq_zero.mpr fun hne ↦ ?_)))
    (add_zero _)
  obtain ⟨p, c⟩ := z₁
  obtain ⟨proof, rfl⟩ := Option.ne_none_iff_exists'.mp hne
  refine (OracleComp.prEvent_eq_zero_iff _ _).mpr fun z hz hrej ↦ ?_
  set H : List UInt8 → Digest := fun t ↦ (z.2 t).getD Prove.zeroDigest
  have hagree : ∀ t u, z.2 t = some u → H t = u := fun t u h ↦ by simp [H, h]
  have hle := QueryImpl.le_snd_of_mem_support_run_simulateQ_withCaching _ _ hz
  have hver := QueryCache.evalWithAnswerFn_eq_of_agreesWithFn (f := H) hagree _
    (QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching _ _ hz)
  have hpro := QueryCache.evalWithAnswerFn_eq_of_agreesWithFn (f := H)
    (fun t u h ↦ hagree t u (hle h)) _
    (QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching _ _ hz₁)
  have hp : proveWith (m := Id) H fuel Blake2sFlock.blake2sFlockSpec prog input w ρ =
      some proof :=
    (proveWith_simulateQ (r := Id) (fun t ↦ pure (H t)) fuel _ prog input w ρ).symm.trans hpro
  have hv : verifyWith (m := Id) H prog input proof = z.1 :=
    (verifyWith_simulateQ (r := Id) (fun t ↦ pure (H t)) prog input proof).symm.trans hver
  rw [Prove.baseProver_complete H fuel hsat hp] at hv
  rw [← hv] at hrej
  cases hrej

/-- The bound at the default fuel `2^24`, with `N = 364909546` queries, is at most `2^-154`. -/
private theorem rom_bound_default (q : ℝ≥0∞) (hq : q ≤ (2 ^ 184 : ℝ≥0∞)⁻¹) :
    (((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) + 1) * q +
      ((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) * ((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      (2 ^ 154 : ℝ≥0∞)⁻¹ := by
  refine (add_le_add (show (((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) + 1) * q ≤
    (((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) + 1) * (2 ^ 184 : ℝ≥0∞)⁻¹ by gcongr) le_rfl).trans ?_
  have h1 : (((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) + 1) * (2 ^ 184 : ℝ≥0∞)⁻¹ =
      ENNReal.ofReal (364909547 / 2 ^ 184) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    norm_num [div_eq_mul_inv]
  have h2 : ((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) * ((264246250 + 6 * 2 ^ 24 : ℕ) : ℝ≥0∞) /
      2 ^ 256 = ENNReal.ofReal (364909546 * 364909546 / 2 ^ 256) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    norm_num
  have h3 : (2 ^ 154 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((2 ^ 154 : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    norm_num
  rw [h1, h2, h3, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **The deployed prover at the default fuel `2^24` in the random-oracle model** returns no proof
with probability at most `2^-154`. -/
theorem prove_rom_eq_none_le_default {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} {s : Sizes}
    (hsat : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hμ : leanIsaμ prog s ≤ maxMu) (hρ : validRate ρ) :
    Pr{let z ← runRandom (proveWith hashQuery (2 ^ 24) Blake2sFlock.blake2sFlockSpec prog input
      w ρ)}[z.1 = none] ≤ (2 ^ 154 : ℝ≥0∞)⁻¹ :=
  (prove_rom_eq_none_le (2 ^ 24) hsat hs hμ hρ).trans
    (rom_bound_default _ Prove.one_sub_pow_fuel_le)

/-- **Completeness of the deployed pair at the default fuel `2^24` in the random-oracle model**:
the honest run is rejected with probability at most `2^-154`. -/
theorem honestGame_rom_rejects_le_default {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ} {s : Sizes}
    (hsat : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hμ : leanIsaμ prog s ≤ maxMu) (hρ : validRate ρ) :
    Pr{let z ← runRandom (honestGame (2 ^ 24) prog input w ρ)}[z.1 = false] ≤
      (2 ^ 154 : ℝ≥0∞)⁻¹ :=
  (honestGame_rom_rejects_le (2 ^ 24) hsat hs hμ hρ).trans
    (rom_bound_default _ Prove.one_sub_pow_fuel_le)

end

end LeanerVM.Protocol
