/-
  LeanVM.Protocol.LeanVMSound

  The proof of knowledge soundness, the first statement of `LeanVM/Spec/Statement.lean`: the
  leanVM verifier in the random-oracle model, at 128 bits per query.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Statements
public import LeanVM.Protocol.EndToEnd.Sound.Extractor

/-!
# leanVM, knowledge soundness

The statements are in `LeanVM/Spec/` (the ISA, the verifier, the extractor and
`Statement.lean`), which imports nothing else from the repository. This page proves the first,
`knowledgeSoundness_holds`, and gives the numbers; `LeanVM.Protocol.LeanVM` proves the second,
completeness.

The verifier is leanVM's at `3375f7a137c50b803f3416f6466b5d4e0719708a` (`verifier.py`), its
Fiat-Shamir sponge a duplex sponge over Keccak-f[1600] and its Merkle hash Keccak-256. Both are
modelled as independent random oracles (`HashSpec = (Bytes →ₒ Digest) + (KState →ₒ KState)`).

**Knowledge soundness** (`knowledgeSoundness`): an adversary making at most `Q` queries to the
random oracles outputs a statement (a program and a public input) and a proof, choosing all three
after querying the oracles. The probability that the verifier accepts while the program's last
instruction is not a `JUMP` and the extractor (`extractor`, `LeanVM/Spec/Extractor.lean`: from
the proof and the oracle's answers to the adversary's Keccak-256 queries only, the halting run of
the memory image of a stack in the Johnson list of the word the proof commits to) does not return
a valid execution of the program on the public input is at most
`soundnessError Q = (Q + 12008) · (2^-128 + 7·(Q + 12008)/2^256) + 12008/2^256`, which is at most
`2^-63` for `Q ≤ 2^64` (`soundnessError_le`). The `2^-128` is per oracle query: every group of the
protocol's challenges, discounted by the proof of work before it, escapes with probability at
most `2^-128`, certified for every admissible size and rate (`Whir.Params.Deployed`). The
`12008` bounds the verifier's queries on every statement and proof
(`Verifier.leanVmQueryBound_eq`).

The proof (`knowledgeSoundness`) runs the experiment over the ordered log of fresh queries, the
adversary's part first (`experiment_eq`, `Sound.logged2`). The proof's own extractor
(`Sound.extractStack`) reads the whole log and picks a stack satisfying the leanISA relation; an
accepted proof on which it fails is doomed, or the log fails (a fresh answer collides with or
predicts a digest or a sponge state's capacity the log refers to: `5 + 2` per earlier query, the
`2` the seed's two offsets), and both have probability at most the first term
(`Compile.Rom.romSound_log`). When it succeeds, the specification's extractor, reading the
adversary's part of the log only, returns a valid execution (`Sound.extractor_of_extracted`):
without failure, every climb to the announced root through the log runs through the adversary's
queries, unless a fresh Keccak-256 answer of the verifier is the root itself, which has
probability at most `12008/2^256` (`Sound.prEvent_logged2_root_le`, the second term).

**Scope and trust.**

* Keccak-256 and Keccak-f[1600] are modelled as independent random oracles.
* The extractor is straight-line (it reads the proof and the answers to the adversary's
  queries, never the verifier's, and does not rewind) but information-theoretic, not
  efficient: a classical choice in the list of codewords near the committed word.
* That `verifier` is the Python and Rust verifiers is test evidence, not proof.
* Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Rom (cacheOf map_run_simulateQ_loggedRO_nil map_run_simulateQ_loggedRO)
open scoped ENNReal

@[expose] public section

/-- `verify` is the transcription of the deployed verifier, run with Keccak-256 and
Keccak-f[1600] (`LeanVM.Protocol.Verifier.verify`, what `lake exe leanvm-verify` runs). -/
theorem verify_eq (prog : Program) (input : PublicInput) (proof : Proof) :
    verify prog input proof =
      LeanVM.Protocol.Verifier.verify (bytecodeWords prog) (publicDigest input) proof :=
  rfl

/-- The verifier of the experiment, on a statement and a proof. -/
abbrev expVerifier : Statement × Proof → OracleComp HashSpec Bool :=
  fun z ↦ verifier queryH queryF z.1.1 z.1.2 z.2

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
    (fun z ↦ (z.1, z.2.1)) <$> experiment A = LeanVM.Protocol.Rom.romExperiment A expVerifier := by
  rw [experiment_eq, Functor.map_map, ← LeanVM.Protocol.Rom.map_logExperiment,
    Sound.logExperiment_eq_logged2, Functor.map_map]

/-! ## Knowledge soundness -/

/-- **Knowledge soundness in the random-oracle model.** For an adversary making at most `Q`
queries, which chooses the program, the public input and the proof, the verifier accepts while
the program's last instruction is not a `JUMP` and the extractor `extractor`
(`LeanVM/Spec/Extractor.lean`) does not return a valid execution of the program on the public
input with probability at most `soundnessError Q`. -/
theorem knowledgeSoundness {A : Adversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment A}[Breaks extractor z] ≤ soundnessError Q := by
  -- Doom or failure, read off the final log.
  have h1 := romSound_log Sound.anyProgram Sound.anyCert Sound.leanVmSeeds
    (fun x ↦ Sound.rootOk_stmtHistory x) Sound.εLean Sound.anyCert_bound A Q hA
    leanVmQueryBound Sound.isTotalQueryBound_leanVmFam
    (fun z ℓ ↦ SentinelSafe z.1.1 ∧ (Fail Sound.leanVmSeeds ℓ ∨
      Rom.verify (lookH ℓ) (lookF ℓ)
        (leanVmSeed (bytecodeWords z.1.1) (publicDigest z.1.2))
        (leanVmProgram (bytecodeWords z.1.1) (publicDigest z.1.2)) z.2 ≠ some true ∨
      ¬ Sound.Extracted z.1.1 z.1.2 (cacheOf ℓ) z.2))
    (fun z ℓ hf hv hb ↦ by
      simp only [Sound.leanVmSeeds, Sound.nodeAt_stmtHistory] at hv
      rcases hb.2 with hb | hb | hb
      · exact absurd hb hf
      · exact absurd hv hb
      · exact Sound.doomed_of_doomedRun hv (Sound.doomed_of_not_extracted z.1.1 z.1.2 hv hb))
  rw [Sound.logExperiment_eq_logged2, prEvent_map] at h1
  -- A fresh Keccak-256 answer of the verifier that is the announced root.
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
    have hv : Rom.verify (lookH w.2.2) (lookF w.2.2)
        (leanVmSeed (bytecodeWords w.1.1.1.1) (publicDigest w.1.1.1.2))
        (leanVmProgram (bytecodeWords w.1.1.1.1) (publicDigest w.1.1.1.2))
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
      (fun r hr x hx ↦ hn2 (Or.inr ⟨r, hr, x, hx⟩)) hx
    rw [← List.prefix_iff_eq_take.mp hpre] at ht
    exact hno ⟨t, ht, htv⟩
  · rw [leanVmQueryBound_eq, failBound]
    rfl
  · rw [leanVmQueryBound_eq, div_eq_mul_inv, verifierQueries]

/-- **The extractor's list is short**: at every admissible stack size and rate, the candidates of
any word at the Johnson threshold are at most `2^18` (level 0's list bound). -/
theorem candidates_ncard_le {μ R : ℕ} (h : Parameters.Whir.Admissible μ R) (W : ℕ → List K) :
    (Extraction.Candidates μ R (Extraction.johnsonThreshold μ R) W).ncard ≤ 2 ^ 18 :=
  Sound.spec_candidates_ncard_le h W

/-- **The numbers**: against `2^64` queries, the soundness error is at most `2^-63`. -/
theorem soundnessError_le {Q : ℕ} (hQ : Q ≤ 2 ^ 64) : soundnessError Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 63 := by
  have h2 : ((2 ^ 256 : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 256 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  have hV : (verifierQueries : ℝ≥0∞) = ((12008 : ℕ) : ℝ≥0∞) := rfl
  rw [soundnessError, hV, show verifierQueries = 12008 from rfl,
    Sound.inv_pow_eq_div 128 256 (by norm_num), ← h2,
    ENNReal.div_add_div_same, ← mul_div_assoc, ← Nat.cast_add, ← Nat.cast_mul,
    ENNReal.div_add_div_same, ← Nat.cast_add, Sound.inv_pow_eq_div 63 256 (by norm_num)]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [show 256 - 128 = 128 from rfl, show 256 - 63 = 193 from rfl]
  have hN : Q + 12008 ≤ 2 ^ 64 + 12008 := by omega
  calc (Q + 12008) * (2 ^ 128 + 7 * (Q + 12008)) + 12008
      ≤ (2 ^ 64 + 12008) * (2 ^ 128 + 7 * (2 ^ 64 + 12008)) + 12008 :=
        Nat.add_le_add_right (Nat.mul_le_mul hN (Nat.add_le_add_left
          (Nat.mul_le_mul_left 7 hN) _)) _
    _ ≤ 2 ^ 193 := by norm_num

/-! ## The statement of `LeanVM/Spec/Statement.lean` -/

/-- **Knowledge soundness holds**, for the extractor `extractor`. -/
theorem knowledgeSoundness_holds : KnowledgeSoundness :=
  fun _ _ hA ↦ knowledgeSoundness hA

end
end LeanVM
