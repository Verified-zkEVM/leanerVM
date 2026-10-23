/-
  LeanVM.Protocol.LeanVM

  The proof of the two statements of `LeanVM/Spec/Statement.lean`: knowledge soundness of the
  leanVM verifier in the random-oracle model, at 128 bits per query, and completeness.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Statements
public import LeanVM.Protocol.EndToEnd.Sound.Extractor
public import LeanVM.Protocol.EndToEnd.Complete.Rom

/-!
# leanVM, end to end

The statements are in `LeanVM/Spec/` (the ISA, the verifier, the extractor and
`Statement.lean`), which imports nothing else from the repository. This page proves them,
`knowledgeSoundness_holds` and `completeness_holds`, the latter with an explicit honest prover,
and gives the numbers.

**Knowledge soundness** (`knowledgeSoundness`): an adversary making at most `Q` queries to the
random oracle outputs a statement (a program and a public input) and a proof, choosing all three
after querying the oracle. The probability that the verifier accepts while the program's last
instruction is not a `JUMP` and the extractor (`extractor`, `LeanVM/Spec/Extractor.lean`: from
the proof and the oracle's answers to the adversary's queries only, the halting run of the memory
image of a stack in the Johnson list of the word the proof commits to) does not return a valid
execution of the program on the public input is at most
`soundnessError Q = (Q + 13213) · (2^-128 + 5·(Q + 13213)/2^256) + 13213/2^256`, which is at most
`2^-63` for `Q ≤ 2^64` (`soundnessError_le`). The `2^-128` is per oracle query: every group of the
protocol's challenges, discounted by the proof of work before it, escapes with probability at
most `2^-128`, certified for every admissible size and rate (`Whir.Params.Deployed`).

The proof (`knowledgeSoundness`) runs the experiment over the ordered log of fresh queries, the
adversary's part first (`experiment_eq`, `Sound.logged2`). The proof's own extractor
(`Sound.extractStack`) reads the whole log and picks a stack satisfying the leanISA relation; an
accepted proof on which it fails is doomed, or the log fails (an answer collides with or predicts
a digest it refers to), and both have probability at most the first term (`Sound.romSound_log`).
When it succeeds, the specification's extractor, reading the adversary's part of the log only,
returns a valid execution (`Sound.extractor_of_extracted`): without failure, every climb to the
announced root through the log runs through the adversary's queries, unless a fresh answer of
the verifier is the root itself, which has probability at most `13213/2^256`
(`Sound.prEvent_logged2_root_le`, the second term).

**Completeness** (`completeness`): for a valid execution whose committed size
(`Trace.committedSize`: the memory, the bytecode and a table per opcode, each at its height) is at
most `2^28`, the most the verifier admits, the honest prover
(`honestProver`), run in the same random-oracle experiment, makes the verifier reject with probability at most
`completenessError fuel`, which is below `2^-128` at a fuel of `2^25` nonces per proof of work
(`completenessError_le`). The honest prover is a specification, not an implementation.

**Scope and trust.**

* BLAKE2s is modelled as a random oracle.
* The extractor is straight-line (it reads the proof and the answers to the adversary's
  queries, never the verifier's, and does not rewind) but information-theoretic, not
  efficient: a classical choice in the list of codewords near the committed word.
* A proof is the Python verifier's format: the scalar stream and one full Merkle path per query.
  The Rust prover ships pruned paths (shared siblings per batch, `MerkleOpenings::Pruned`), which
  the deployed `leanvm_core::cpu::verify` expands into these paths and checks more strictly; that
  expansion is not formalized.
* That `verifier` is the Python and Rust verifiers is test evidence: it is a transcription of the
  Python, it accepts the Rust prover's proofs, and on mutated proofs it gives the Rust verifier's
  verdict every time (`scripts/fuzz-verifier.py`).
* Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Blake2sHash
open Air.Flat (EnsembleWitness)
open LeanVM.Protocol.Rom (cacheOf map_run_simulateQ_loggedRO_nil map_run_simulateQ_loggedRO)
open scoped ENNReal

@[expose] public section

/-- `verify` is the transcription of the deployed verifier, run with BLAKE2s
(`LeanVM.Protocol.Verifier.verify`, what `lake exe leanvm-verify` runs). -/
theorem verify_eq (prog : Program) (input : PublicInput) (proof : Proof) :
    verify prog input proof =
      LeanVM.Protocol.Verifier.verify (Front.bytecodeWords prog) (Complete.publicDigest input)
        proof :=
  rfl

/-- The verifier of the experiment, on a statement and a proof. -/
abbrev expVerifier : Statement × Proof → OracleComp HashSpec Bool :=
  fun z ↦ verifier queryH z.1.1 z.1.2 z.2

/-- The experiment's verifier is the random-oracle theorem's verifier of every statement. -/
theorem expVerifier_eq : expVerifier = Rom.verifierFam Sound.leanVmSeeds Sound.anyProgram := by
  funext z
  rw [Sound.verifierFam_leanVm, verifierComp_leanVm]
  rfl

/-- **The experiment over the ordered log**: the adversary's run from the empty log, then the
verifier's from the log it left (`Sound.logged2`), each log read as a cache. -/
theorem experiment_eq (A : Adversary) :
    experiment A = (fun w ↦ ((w.1.1, w.2.1), cacheOf w.2.2, cacheOf w.1.2)) <$>
      Sound.logged2 A expVerifier := by
  simp only [experiment, Sound.logged2, ← map_run_simulateQ_loggedRO_nil, bind_map_left,
    map_bind, Functor.map_map]
  refine bind_congr fun p ↦ ?_
  rw [← map_run_simulateQ_loggedRO, bind_map_left]
  simp [map_eq_bind_pure_comp]

/-- The experiment without the adversary's cache is the generic adversary-then-verifier
experiment. -/
theorem experiment_map (A : Adversary) :
    (fun z ↦ (z.1, z.2.1)) <$> experiment A = Rom.romExperiment A expVerifier := by
  rw [experiment_eq, Functor.map_map, ← Rom.map_logExperiment, Sound.logExperiment_eq_logged2,
    Functor.map_map]

/-! ## Knowledge soundness -/

/-- **Knowledge soundness in the random-oracle model.** For an adversary making at most `Q`
queries, which chooses the program, the public input and the proof, the verifier accepts while
the program's last instruction is not a `JUMP` and the extractor `extractor`
(`LeanVM/Spec/Extractor.lean`) does not return a valid execution of the program on the public
input with probability at most `soundnessError Q`. -/
theorem knowledgeSoundness {A : Adversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment A}[Breaks extractor z] ≤ soundnessError Q := by
  -- Doom or failure, read off the final log.
  have h1 := Sound.romSound_log Sound.anyProgram Sound.anyCert Sound.leanVmSeeds
    (fun x ↦ Sound.rootOk_stmtHistory x) Sound.εLean Sound.anyCert_bound A Q hA
    leanVmQueryBound Sound.isTotalQueryBound_leanVmFam
    (fun z ℓ ↦ SentinelSafe z.1.1 ∧ (Fail Sound.leanVmSeeds ℓ ∨
      Rom.verify (look ℓ) (leanVmSeed (Front.bytecodeWords z.1.1) (Complete.publicDigest z.1.2))
        (leanVmProgram (Front.bytecodeWords z.1.1) (Complete.publicDigest z.1.2)) z.2 ≠
          some true ∨
      ¬ Sound.Extracted z.1.1 z.1.2 (cacheOf ℓ) z.2))
    (fun z ℓ hf hv hb ↦ by
      simp only [Sound.leanVmSeeds, Sound.nodeAt_stmtHistory] at hv
      rcases hb.2 with hb | hb | hb
      · exact absurd hb hf
      · exact absurd hv hb
      · exact Sound.doomed_of_doomedRun hv (Sound.doomed_of_not_extracted z.1.1 z.1.2 hv hb))
  rw [Sound.logExperiment_eq_logged2, prEvent_map] at h1
  -- A fresh answer of the verifier that is the announced root.
  have h2 := Sound.prEvent_logged2_root_le A (Rom.verifierFam Sound.leanVmSeeds Sound.anyProgram)
    leanVmQueryBound Sound.isTotalQueryBound_leanVmFam (fun z ↦ Sound.announcedRoot z.1.1 z.2)
  rw [experiment_eq, expVerifier_eq, prEvent_map, soundnessError]
  refine (prEvent_mono _ _ _ ?_).trans ((prEvent_or_le _ _ _).trans
    (add_le_add (h1.trans (le_of_eq ?_)) (h2.trans (le_of_eq ?_))))
  · rintro w ⟨hacc, hsafe, hno⟩
    dsimp only at hacc hsafe hno ⊢
    by_contra hne
    rw [not_or] at hne
    obtain ⟨hn1, hn2⟩ := hne
    have hf : ¬ Fail Sound.leanVmSeeds w.2.2 := fun h ↦ hn1 ⟨hacc, hsafe, Or.inl h⟩
    have hv : Rom.verify (look w.2.2)
        (leanVmSeed (Front.bytecodeWords w.1.1.1.1) (Complete.publicDigest w.1.1.1.2))
        (leanVmProgram (Front.bytecodeWords w.1.1.1.1) (Complete.publicDigest w.1.1.1.2))
        w.1.1.2 = some true := by
      by_contra h
      exact hn1 ⟨hacc, hsafe, Or.inr (Or.inl h)⟩
    have hx : Sound.Extracted w.1.1.1.1 w.1.1.1.2 (cacheOf w.2.2) w.1.1.2 := by
      by_contra h
      exact hn1 ⟨hacc, hsafe, Or.inr (Or.inr h)⟩
    have hpre : w.1.2 <+: w.2.2 := by
      by_contra h
      exact hn2 (Or.inl h)
    obtain ⟨t, ht, htv⟩ := Sound.extractor_of_extracted Sound.leanVmSeeds hsafe hf hv
      (fun r hr e he hre ↦ hn2 (Or.inr ⟨r, hr, e, he, hre⟩)) hx
    rw [← List.prefix_iff_eq_take.mp hpre] at ht
    exact hno ⟨t, ht, htv⟩
  · rw [leanVmQueryBound_eq, failBound]
    rfl
  · rw [leanVmQueryBound_eq, div_eq_mul_inv]
    norm_num

/-- **The extractor's list is short**: at every admissible stack size and rate, the candidates of
any word at the Johnson threshold are at most `2^18` (level 0's list bound). -/
theorem candidates_ncard_le {μ R : ℕ} (h : Parameters.Whir.Admissible μ R) (W : ℕ → List K) :
    (Extraction.Candidates μ R (Extraction.johnsonThreshold μ R) W).ncard ≤ 2 ^ 18 :=
  Sound.spec_candidates_ncard_le h W

/-- **The numbers**: against `2^64` queries, the soundness error is at most `2^-63`. -/
theorem soundnessError_le {Q : ℕ} (hQ : Q ≤ 2 ^ 64) : soundnessError Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 63 := by
  have h2 : ((2 ^ 256 : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 256 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  have h13 : (13213 : ℝ≥0∞) = ((13213 : ℕ) : ℝ≥0∞) := by norm_num
  rw [soundnessError, Sound.inv_pow_eq_div 128 256 (by norm_num), ← h2,
    ENNReal.div_add_div_same, ← mul_div_assoc, ← Nat.cast_add, ← Nat.cast_mul, h13,
    ENNReal.div_add_div_same, ← Nat.cast_add, Sound.inv_pow_eq_div 63 256 (by norm_num)]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [show 256 - 128 = 128 from rfl, show 256 - 63 = 193 from rfl]
  have hN : Q + 13213 ≤ 2 ^ 64 + 13213 := by omega
  calc (Q + 13213) * (2 ^ 128 + 5 * (Q + 13213)) + 13213
      ≤ (2 ^ 64 + 13213) * (2 ^ 128 + 5 * (2 ^ 64 + 13213)) + 13213 :=
        Nat.add_le_add_right (Nat.mul_le_mul hN (Nat.add_le_add_left
          (Nat.mul_le_mul_left 5 hN) _)) _
    _ ≤ 2 ^ 193 := by norm_num

/-! ## Completeness -/

/-- **The honest prover**: the proof of the execution `t` at the commitment's inverse rate `2^ρ`,
every hash a query to the random oracle, each proof-of-work search trying at most `fuel` nonces
(the empty proof if one fails). A specification: it takes a witness of leanISA's constraint
system representing the execution (a classical choice), pads its tables with the public padding
rows, and runs the honest strategy of every phase through the Fiat-Shamir transform. -/
noncomputable def honestProver (prog : Program) (input : PublicInput) (t : Trace prog)
    (ρ fuel : ℕ) : Adversary :=
  (fun proof ↦ ((prog, input), proof)) <$> Complete.honestComp prog input t ρ fuel

theorem completenessError_eq (fuel : ℕ) :
    completenessError fuel = Complete.completenessError fuel := by
  have hc : leanVmCost = 13210 := by decide
  have hQ : Complete.completenessQueries fuel = 13216 + 13210 * (2 ^ 27 + fuel + 1) := by
    rw [Complete.completenessQueries, proverFactor, costHeight, hc, leanVmQueryBound_eq]
    ring
  rw [completenessError, Complete.completenessError, hQ]
  rfl

/-- **Completeness.** For a valid execution whose committed size is at most `2^28`, at an inverse
rate `2^ρ` with `1 ≤ ρ ≤ 4`: the verifier rejects the honest prover's proof, in the random-oracle
experiment, with probability at most `completenessError fuel`. -/
theorem completeness {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28) {ρ : ℕ}
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← experiment (honestProver prog input t ρ fuel)}[z.1.2 = false] ≤
      completenessError fuel := by
  have hV : (fun π ↦ verifier queryH prog input π) =
      verifierComp (leanVmSeed (Front.bytecodeWords prog) (Complete.publicDigest input))
        (leanVmProgram (Front.bytecodeWords prog) (Complete.publicDigest input)) :=
    funext fun π ↦ (verifierComp_leanVm _ _ π).symm
  have h := Complete.romComplete_leanVm hv hbudget hρ hfuel
  rw [← hV, ← completenessError_eq] at h
  have e := prEvent_map (experiment (honestProver prog input t ρ fuel)) (fun z ↦ (z.1, z.2.1))
    (fun z ↦ z.1.2 = false)
  rw [experiment_map] at e
  refine (le_of_eq e.symm).trans ?_
  unfold honestProver
  rw [Rom.romExperiment_map, prEvent_map]
  exact h

/-- **The numbers**: at a fuel of `2^25` nonces per proof of work, the completeness error is
below `2^-128`. -/
theorem completenessError_le : completenessError (2 ^ 25) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  rw [completenessError_eq]
  exact Complete.completenessError_le

/-! ## The statements of `LeanVM/Spec/Statement.lean` -/

/-- **Knowledge soundness holds**, for the extractor `extractor`. -/
theorem knowledgeSoundness_holds : KnowledgeSoundness :=
  fun _ _ hA ↦ knowledgeSoundness hA

/-- **Completeness holds**, with the honest prover `honestProver`. -/
theorem completeness_holds : Completeness :=
  ⟨Complete.honestComp, fun _ _ _ _ _ hv hbudget hρ hfuel ↦ completeness hv hbudget hρ hfuel⟩

end
end LeanVM
