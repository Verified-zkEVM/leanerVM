/-
  LeanVM.E2E.Complete.Rom.Bounds

  T6-prob's probability bounds: G1 (a proof-of-work search exhausting its fuel) from the
  proof-of-work potential of `romComplete`, G2 (the matrices' weights vanishing) from the weights'
  potential, the two potentials together through the engine, and the numeric error.
-/

module

public import LeanVM.E2E.Batch.Weights
public import LeanVM.Protocol.Compile.Rom.Complete
public import LeanVM.Protocol.EndToEnd.Blind.Assemble

/-!
# T6-prob's bounds

`docs/roadmap/t6-prob.md` §4.5 and §4.6 (package P4).

* `one_le_powPot_of_proveFromM`: G1. A failed proof-of-work search of the honest prover on the
  log (`proveFromM (look ℓ) … = some none`) of a program whose proofs of work all ask for `17`
  bits makes the proof-of-work potential `powPot 17 pfuel ℓ` at least one (the `none` branch of
  `Protocol.Compile.Rom.one_le_powPot`, as a lemma). `grind17_blindProgram`: the guest's
  verifier program asks for `17` bits (`movesOK_blindProgram`).
* `sumPot_step`: one fresh query raises `powPot 17 pfuel + weightsPot`, in expectation, by at most
  `(1 - 2^-17)^pfuel + |ℓ|/2^256 + 2^-192 + failBound batchSeedsAll (|ℓ| + 2)` (`powPot_step`,
  `weightsPot_step`).
* `prEvent_le_completeError`: an event of an oracle computation of at most `Q` queries, run
  against `Rom.loggedRO` from the empty log, on which the two potentials sum to at least one, has
  probability at most `completeError Q pfuel` (`prEvent_run_loggedRO_le_of_freshStepBelow`).
* `completeError_le`: at `pfuel = 2^25` and `Q ≤ 2^64` the error is at most `2^-124`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Rom
open LeanVM.Protocol.EndToEnd.Blind LeanVM.E2E
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## The error -/

/-- **T6-prob's error**: `Q` fresh queries, each raising the proof-of-work potential by at most
`(1 - 2^-17)^pfuel + Q/2^256` and the weights' potential by at most
`2^-192 + failBound batchSeedsAll (Q + 1)`. -/
noncomputable def completeError (Q pfuel : ℕ) : ℝ≥0∞ :=
  Q * (missProb 17 ^ pfuel + Q / 2 ^ 256) + Q * ((2 : ℝ≥0∞)⁻¹ ^ 192 + failBound batchSeedsAll (Q + 1))

/-- The error grows with the queries. -/
theorem completeError_mono {Q Q' pfuel : ℕ} (h : Q ≤ Q') :
    completeError Q pfuel ≤ completeError Q' pfuel := by
  unfold completeError
  have hc : (Q : ℝ≥0∞) ≤ Q' := by exact_mod_cast h
  have hf : failBound batchSeedsAll (Q + 1) ≤ failBound batchSeedsAll (Q' + 1) := by
    unfold failBound
    exact ENNReal.div_le_div_right (by exact_mod_cast Nat.mul_le_mul_left _ (by omega)) _
  gcongr

/-- **The numbers**: at `pfuel = 2^25` and at most `2^64` queries, the error is at most
`2^-124`. With `e = 2^-256`: `(1 - 2^-17)^(2^25) ≤ e` (`missProb_pow_le 17 256`), and
`failBound batchSeedsAll N = 4N · e`, so the error is at most
`(2^64 (1 + 2^64) + 2^64 (2^64 + 4 (2^64 + 1))) · e ≤ 2^132 · e = 2^-124`. -/
theorem completeError_le {Q : ℕ} (hQ : Q ≤ 2 ^ 64) :
    completeError Q (2 ^ 25) ≤ (2 : ℝ≥0∞)⁻¹ ^ 124 := by
  refine (completeError_mono hQ).trans ?_
  set e : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ 256 with he
  have hmiss : missProb 17 ^ (2 ^ 25) ≤ e := by
    have := missProb_pow_le 17 256
    rwa [show 2 ^ 17 * 256 = 2 ^ 25 by norm_num] at this
  have hdiv : ∀ n : ℕ, (n : ℝ≥0∞) / 2 ^ 256 = n * e := fun n ↦ by
    rw [he, div_eq_mul_inv, ENNReal.inv_pow]
  have hpow : ∀ a b : ℕ, (2 : ℝ≥0∞)⁻¹ ^ a = ((2 ^ b : ℕ) : ℝ≥0∞) * 2⁻¹ ^ (a + b) := fun a b ↦ by
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_add, mul_left_comm, ← mul_pow,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]
  have hfb : failBound batchSeedsAll (2 ^ 64 + 1) = ((4 * (2 ^ 64 + 1) : ℕ) : ℝ≥0∞) * e := by
    rw [failBound, show batchSeedsAll.steps.length = 0 from rfl, hdiv]
  unfold completeError
  rw [hdiv, hpow 192 64, hfb, hpow 124 132]
  calc _ ≤ ((2 ^ 64 : ℕ) : ℝ≥0∞) * (e + ((2 ^ 64 : ℕ) : ℝ≥0∞) * e) +
        ((2 ^ 64 : ℕ) : ℝ≥0∞) * (((2 ^ 64 : ℕ) : ℝ≥0∞) * e +
          ((4 * (2 ^ 64 + 1) : ℕ) : ℝ≥0∞) * e) := by gcongr
    _ = ((2 ^ 64 * (1 + 2 ^ 64) + 2 ^ 64 * (2 ^ 64 + 4 * (2 ^ 64 + 1)) : ℕ) : ℝ≥0∞) * e := by
        push_cast; ring
    _ ≤ ((2 ^ 132 : ℕ) : ℝ≥0∞) * e := by gcongr; norm_num

/-! ## G1: a failed proof-of-work search -/

/-- **G1 from a failed proof-of-work search on the log**: if the honest prover, run with every
hash read from the log `ℓ`, fails (`some none`), on a program whose proofs of work all ask for
`17` bits, then the proof-of-work potential of `ℓ` is at least one. The base of the failed
search is in the log and all its `pfuel` nonces fail there, so its term is `1` (the `none`
branch of `Protocol.Compile.Rom.one_le_powPot`). -/
theorem one_le_powPot_of_proveFromM {ℓ : Log} {P : Prog Bool} {S : Strategy} {seed : Digest}
    {pfuel : ℕ} (hg : ∀ h b k, P.after h = some (.grind b k) → b = 17)
    (h : proveFromM (look ℓ) S pfuel P seed [] = some none) : 1 ≤ powPot 17 pfuel ℓ := by
  obtain ⟨h', b', k, cv, ha, hf⟩ :=
    proveFromM_eq_some_none S pfuel P seed [] (Prog.after.eq_1 P) h
  rw [hg h' b' k ha] at hf
  obtain ⟨-, base, hbase, hall⟩ := findNonceM_eq_some_none hf
  have hS : ¬ Solved 17 pfuel ℓ base := by
    rintro ⟨n, hn, d, hd, hp⟩
    obtain ⟨d', hd', hp'⟩ := hall n hn
    rw [hd'] at hd
    cases hd
    rw [hp'] at hp
    cases hp
  have hT : (tried pfuel ℓ base).card = pfuel := by
    have : tried pfuel ℓ base = Finset.range pfuel := by
      refine Finset.filter_true_of_mem fun n hn ↦ ?_
      obtain ⟨d, hd, -⟩ := hall n (Finset.mem_range.mp hn)
      simp [hd]
    rw [this, Finset.card_range]
  have hterm : powTerm 17 pfuel ℓ base = 1 := by
    simp [powTerm, hS, hT]
  obtain ⟨i, hi, he, -⟩ := (look_eq_some_iff ℓ _ base).mp hbase
  calc (1 : ℝ≥0∞) = ind (∃ cv', (ℓ[i]).1 = baseInput cv') * powTerm 17 pfuel ℓ (ℓ[i]).2 := by
        rw [he, ind_of ⟨cv, rfl⟩, one_mul, hterm]
    _ ≤ powPot 17 pfuel ℓ := List.single_le_sum (fun _ _ ↦ bot_le) _
        (List.mem_map.mpr ⟨ℓ[i], List.getElem_mem hi, rfl⟩)

/-- Every proof of work of the guest's verifier program asks for `17` bits
(`movesOK_blindProgram`). -/
theorem grind17_blindProgram (bc : List K) (pd : Digest) :
    ∀ h b k, (blindProgram bc pd).after h = some (.grind b k) → b = 17 :=
  fun _ _ _ ha ↦ ((movesOK_blindProgram bc pd).after ha).1

/-! ## The two potentials together -/

/-- **The combined step**: one fresh query raises `powPot 17 pfuel + weightsPot`, in expectation,
by at most `(1 - 2^-17)^pfuel + |ℓ|/2^256 + 2^-192 + failBound batchSeedsAll (|ℓ| + 2)`. -/
theorem sumPot_step {pfuel : ℕ} (hpf : pfuel ≤ 2 ^ 64) {ℓ : Log} {t : Bytes}
    (ht : look ℓ t = none) :
    (∑ u, (powPot 17 pfuel (ℓ ++ [(t, u)]) + weightsPot (ℓ ++ [(t, u)]))) /
        Fintype.card Digest ≤
      (powPot 17 pfuel ℓ + weightsPot ℓ) +
        (missProb 17 ^ pfuel + ℓ.length / Fintype.card Digest +
          ((2 : ℝ≥0∞)⁻¹ ^ 192 + failBound batchSeedsAll (ℓ.length + 2))) := by
  rw [Finset.sum_add_distrib, ENNReal.add_div, add_add_add_comm]
  exact add_le_add (powPot_step (by norm_num) (by norm_num) hpf ht) (weightsPot_step ht)

/-- **The engine at the two potentials**: an event of an oracle computation of at most `Q`
queries, run against the lazy oracle from the empty log, on whose outcomes the two potentials
sum to at least one, has probability at most `completeError Q pfuel`. A log of fewer than `Q`
entries makes the step's `|ℓ|/2^256` at most `Q/2^256` and its failure term at most
`failBound batchSeedsAll (Q + 1)`. -/
theorem prEvent_le_completeError {α : Type} (oa : OracleComp HashSpec α) {Q pfuel : ℕ}
    (hpf : pfuel ≤ 2 ^ 64) (hQ : IsTotalQueryBound oa Q) (ev : α → Log → Prop)
    (hev : ∀ z ∈ support ((simulateQ loggedRO oa).run []), ev z.1 z.2 →
      1 ≤ powPot 17 pfuel z.2 + weightsPot z.2) :
    Pr{let z ← (simulateQ loggedRO oa).run []}[ev z.1 z.2] ≤ completeError Q pfuel := by
  have h := prEvent_run_loggedRO_le_of_freshStepBelow
    (Φ := fun ℓ ↦ powPot 17 pfuel ℓ + weightsPot ℓ)
    (δ := missProb 17 ^ pfuel + (Q : ℝ≥0∞) / 2 ^ 256 +
      ((2 : ℝ≥0∞)⁻¹ ^ 192 + failBound batchSeedsAll (Q + 1))) Q
    (fun ℓ t hN ht ↦ by
      refine (sumPot_step hpf ((logLookup_eq_none_iff ℓ t).mpr ht)).trans
        (add_le_add le_rfl (add_le_add (add_le_add le_rfl ?_) (add_le_add le_rfl ?_)))
      · rw [card_digest, Nat.cast_pow, Nat.cast_ofNat]
        gcongr
      · unfold failBound
        exact ENNReal.div_le_div_right (by exact_mod_cast Nat.mul_le_mul_left _ (by omega)) _)
    oa Q hQ [] (by simp) ev hev
  simp only [powPot_nil, weightsPot_nil, add_zero, zero_add] at h
  refine h.trans (le_of_eq ?_)
  rw [completeError, ← mul_add]

end
end LeanVM.E2E.Complete
