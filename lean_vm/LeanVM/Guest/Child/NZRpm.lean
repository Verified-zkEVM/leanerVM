/-
  LeanVM.Guest.Child.NZRpm

  The child prover against the verifier refusing a zero challenge in the random-permutation model:
  rejected with probability at most `nzCompletenessError fuel + rpmError (completenessPermCalls
  fuel)`, below `2^-126` at a fuel of `2^25`.
-/

import LeanVM.Guest.Child.NZRom
import LeanVM.Guest.Child.Honest
import LeanVM.Protocol.LeanVMRpm

/-!
# Refusing a zero challenge, in the random-permutation model

`romChild`: against the two random oracles, the child prover's proof (`childComp`) is rejected
by the verifier refusing a zero challenge (`Budget.verifierNZ`) with probability at most
`nzCompletenessError fuel = Q · ((1 - 2^-17)^fuel + 2^-192)`, `Q = completenessQueries fuel`
(`romCompleteNZ` at leanVM's program and seed). `rpmChild`: in the random-permutation model, at
most that plus `rpmError (completenessPermCalls fuel)`, the transfer of `completenessRpm`: the
prover and the verifier follow the duplex discipline (`duplexVm_childRun`) and make at most
`completenessPermCalls fuel` permutation calls (`isWeightBound_childRun`). `rpmChild_le`: at a
fuel of `2^25`, at most `2^-126`.
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Rom LeanVM.Protocol.KeccakHash LeanVM.Rpm OracleComp OracleSpec
open scoped ENNReal

/-! ## The run -/

/-- The child prover, then the verifier refusing a zero challenge. -/
noncomputable def childRun (prog : Program) (input : PublicInput) (t : Trace prog) (ρ fuel : ℕ) :
    OracleComp HashSpec Bool :=
  childComp prog input t ρ fuel >>= fun proof ↦ Budget.verifierNZ queryH queryF prog input proof

/-- The verifier refusing a zero challenge is the seeded verifier of `nzProgram`. -/
theorem verifierNZ_eq_comp (prog : Program) (input : PublicInput) (π : Proof) :
    Budget.verifierNZ queryH queryF prog input π =
      verifierComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
        (nzProgram (bytecodeWords prog) (publicDigest input)) π := by
  simp only [verifierComp, Rom.verify, Budget.verifierNZ, seedRun_leanVmSeed]
  rfl

/-! ## Against the random oracles -/

/-- The completeness error of the verifier refusing a zero challenge, against the random
oracles. -/
noncomputable def nzCompletenessError (fuel : ℕ) : ℝ≥0∞ :=
  (completenessQueries fuel : ℝ≥0∞) * (missProb Whir.queryGrindingBits ^ fuel + (2 : ℝ≥0∞)⁻¹ ^ 192)

set_option maxHeartbeats 1000000 in
/-- **The child prover against the random oracles.** -/
theorem romChild {prog : Program} {input : PublicInput} {t : Trace prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ maxMu)
    (hρ : validRate ρ) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← romExperiment (childComp prog input t ρ fuel)
        (fun π ↦ Budget.verifierNZ queryH queryF prog input π)}[z.1.2 = false] ≤
      nzCompletenessError fuel := by
  have hex := exists_childFor hv hbudget hρ
  unfold childComp
  simp only [hex, ↓reduceDIte]
  obtain ⟨⟨hρ', hw', hs', hadm', -⟩, -⟩ := hex.choose_spec.choose_spec
  have hq := m3Honest_stackOf hw' hs'
  have hrun := runI_leanVmProgram (input := input) hadm' hρ' hq
  simp only [verifierNZ_eq_comp]
  have h := romCompleteNZ (leanVmProgram (bytecodeWords prog) (publicDigest input))
    (nzProgram (bytecodeWords prog) (publicDigest input)) (nz_nzProgram _ _) _
    (leanVmSeed (bytecodeWords prog) (publicDigest input)) (bits := Whir.queryGrindingBits)
    (by decide) (by decide) hfuel (fun _ _ _ hg ↦ EndToEnd.Sound.grind_bits_eq _ _ hg)
    (fun chal ↦ (hrun chal).1) (fun chal ↦ (hrun chal).2)
    (costLE_leanVmProgram (bytecodeWords prog) (publicDigest input))
    (costLE_nzProgram (bytecodeWords prog) (publicDigest input))
  refine h.trans (le_of_eq ?_)
  rfl

/-! ## The discipline and the calls -/

theorem duplexVm_childComp (prog : Program) (input : PublicInput) (t : Trace prog)
    (ρ fuel : ℕ) : DuplexVm (childComp prog input t ρ fuel) [] := by
  rw [duplexVm_iff_duplexP]
  unfold childComp
  split
  · simp only [Rom.honestComp, seedRun_leanVmSeed, proveM, bind_assoc]
    exact (duplexP_seedWith _ _ []).bind fun seed h' hs ↦
      (duplexP_proveFromM _ _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial
  · trivial

theorem duplexVm_verifierNZ (prog : Program) (input : PublicInput) (proof : Proof) :
    DuplexVm (Budget.verifierNZ queryH queryF prog input proof) [] := by
  rw [duplexVm_iff_duplexP]
  simp only [Budget.verifierNZ]
  exact (duplexP_seedWith _ _ []).bind fun seed h' hs ↦ duplexP_runProof _ hs _

theorem duplexVm_childRun (prog : Program) (input : PublicInput) (t : Trace prog) (ρ fuel : ℕ) :
    DuplexVm (childRun prog input t ρ fuel) [] :=
  (duplexVm_childComp prog input t ρ fuel).bind fun proof ↦ duplexVm_verifierNZ prog input proof

/-- A refining program commits words no wider. -/
theorem widthsLE_of_refines {α : Type} {W : ℕ} {P' P : Prog α} (h : Limits.Refines P' P) :
    WidthsLE W P → WidthsLE W P' := by
  induction h with
  | fail P => intro _; trivial
  | ret a => intro hc; exact hc
  | read _ ih => intro hc; exact fun x ↦ ih x (hc x)
  | sample _ ih => intro hc; exact fun x ↦ ih x (hc x)
  | grind _ ih => intro hc; exact ih hc
  | commit _ ih => intro hc; exact ⟨hc.1, ih hc.2⟩
  | query _ ih => intro hc; exact fun r ↦ ih r (hc r)

theorem allQ_verifierNZ (prog : Program) (input : PublicInput) (proof : Proof) :
    AllQueriesSatisfy (Budget.verifierNZ queryH queryF prog input proof) Short := by
  rw [verifierNZ_eq_comp]
  exact allQueriesSatisfy_bind (allQ_seedRun prog input) fun seed ↦
    allQ_runProof _ seed proof (widthsLE_of_refines (refines_nzProgram _ _)
      (widthsLE_leanVmProgram _ _))

set_option maxHeartbeats 1000000 in
theorem allQ_childComp (prog : Program) (input : PublicInput) (t : Trace prog) (ρ fuel : ℕ) :
    AllQueriesSatisfy (childComp prog input t ρ fuel) Short := by
  unfold childComp
  split
  · rename_i hex
    obtain ⟨⟨hρ', hw', hs', hadm', -⟩, -⟩ := hex.choose_spec.choose_spec
    have hq := m3Honest_stackOf hw' hs'
    exact allQ_romHonestComp prog input _ fuel fun chal ↦
      (runI_leanVmProgram (input := input) hadm' hρ' hq chal).2
  · exact allQ_pure _

theorem isTotalQueryBound_childComp (prog : Program) (input : PublicInput) (t : Trace prog)
    (ρ fuel : ℕ) :
    IsTotalQueryBound (childComp prog input t ρ fuel) (4 + 48017 * (2 ^ 27 + 2 * fuel + 2)) := by
  unfold childComp
  split
  · rename_i hex
    have h := Rom.isTotalQueryBound_honestComp
      (costLE_leanVmProgram (bytecodeWords prog) (publicDigest input)) (leanVmProver
        prog hex.choose_spec.choose ρ (LeanIsa.stackOf prog hex.choose_spec.choose hex.choose))
      fuel (σ := leanVmSeed (bytecodeWords prog) (publicDigest input))
    have hc : leanVmCost = 48017 := by decide
    rw [hc] at h
    exact h
  · trivial

/-- **The child prover and the verifier refusing a zero challenge make at most
`completenessPermCalls fuel` permutation calls.** -/
theorem isWeightBound_childRun (prog : Program) (input : PublicInput) (t : Trace prog)
    (ρ fuel : ℕ) :
    Common.IsWeightBound (childRun prog input t ρ fuel) hashBlocks (completenessPermCalls fuel) := by
  have hN : IsTotalQueryBound (childRun prog input t ρ fuel)
      (12012 + 48017 * (2 ^ 27 + 2 * fuel + 2)) := by
    have h := isTotalQueryBound_bind (isTotalQueryBound_childComp prog input t ρ fuel)
      fun proof ↦ by
        have := isTotalQueryBound_verifierComp
          (costLE_nzProgram (bytecodeWords prog) (publicDigest input))
          (leanVmSeed (bytecodeWords prog) (publicDigest input)) proof
        rw [← verifierNZ_eq_comp] at this
        exact this
    refine h.mono ?_
    have : leanVmCost / 4 = 12004 := by decide
    simp only [leanVmSeed, List.length_cons, List.length_nil, this]
    omega
  exact isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 32) hN
    ((allQueriesSatisfy_bind (allQ_childComp prog input t ρ fuel) fun proof ↦
      allQ_verifierNZ prog input proof).mono fun _ h ↦ hashBlocks_le_of_short h)

theorem isWeightBound_childGame (prog : Program) (input : PublicInput) (t : Trace prog)
    (ρ fuel : ℕ) :
    Common.IsWeightBound (honestGame (childRun prog input t ρ fuel)) gameCost
      (completenessPermCalls fuel) := by
  rw [honestGame, Common.rpmGame2, simulateQ_pure, pure_bind, simulateQ_pure, pure_bind]
  exact isWeightBound_hfEmbed_toRHF (isWeightBound_childRun prog input t ρ fuel)

/-! ## In the random-permutation model -/

/-- The run against the random oracles is the experiment's verdict. -/
theorem run'_childRun (prog : Program) (input : PublicInput) (t : Trace prog) (ρ fuel : ℕ) :
    (simulateQ HashSpec.randomOracle (childRun prog input t ρ fuel)).run' ∅ =
      (fun z ↦ z.1.2) <$> romExperiment (childComp prog input t ρ fuel)
        (fun π ↦ Budget.verifierNZ queryH queryF prog input π) := by
  simp only [childRun, romExperiment, simulateQ_map, StateT.run_map, map_bind,
    simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  refine bind_congr fun p ↦ ?_
  simp

/-- **The child prover against the verifier refusing a zero challenge, in the
random-permutation model.** -/
theorem rpmChild {prog : Program} {input : PublicInput} {t : Trace prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28)
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let v ← (simulateQ rpmImpl (childRun prog input t ρ fuel)).run' []}[v = false] ≤
      nzCompletenessError fuel + rpmError (completenessPermCalls fuel) := by
  rw [(rpmHonest_evalDistEq _).prEvent_eq, honestGame]
  obtain ⟨h1, -⟩ := Common.keccak256_transfer2 (pure ()) (fun _ ↦ (pure () : OracleComp RSpec Unit))
    (fun _ _ ↦ simulateQ toRHF (childRun prog input t ρ fuel))
    (fun _ _ ↦ duplex_toRHF _ [] (duplexVm_childRun prog input t ρ fuel))
    (completenessPermCalls fuel) (isWeightBound_childGame prog input t ρ fuel) (· = false)
  refine h1.trans (add_le_add (le_of_eq_of_le ?_ (romChild hv hbudget hρ hfuel)) le_rfl)
  have e1 : Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
      Common.advS2 Common.keccakPadding Common.KState.zero
        ((fun _ ↦ (pure () : OracleComp RSpec Unit)) x) >>= fun a ↦
          (fun _ _ ↦ simulateQ toRHF (childRun prog input t ρ fuel)) x a) =
      (simulateQ HFS.romImpl (simulateQ toRHF (childRun prog input t ρ fuel))).run' ∅ := by
    simp [Common.romRun2, Common.advS2]
  rw [e1, (run'_toRHF _ _).prEvent_eq, cmap_empty, run'_childRun, prEvent_map]

/-! ## The numbers -/

/-- **At a fuel of `2^25` nonces per proof of work, at most `2^-126`**: `completenessRpm_le`'s two
terms, each at most `2^-128`, and `Q · 2^-192 ≤ 2^44 · 2^-192`. -/
theorem rpmChild_le :
    nzCompletenessError (2 ^ 25) + rpmError (completenessPermCalls (2 ^ 25)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 126 := by
  have hQ : completenessQueries (2 ^ 25) ≤ 2 ^ 44 := by decide
  have hz : (completenessQueries (2 ^ 25) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 :=
    calc (completenessQueries (2 ^ 25) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 192
        ≤ (2 : ℝ≥0∞) ^ 44 * (2 : ℝ≥0∞)⁻¹ ^ (44 + 148) := by
          gcongr
          exact_mod_cast hQ
      _ = (2 : ℝ≥0∞)⁻¹ ^ 148 := Common.two_pow_mul_inv_pow 44 148
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := Common.inv_two_pow_le_of_le (by norm_num)
  have e : nzCompletenessError (2 ^ 25) = EndToEnd.Complete.completenessError (2 ^ 25) +
      (completenessQueries (2 ^ 25) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 192 := by
    rw [nzCompletenessError, mul_add]
    rfl
  rw [e]
  calc EndToEnd.Complete.completenessError (2 ^ 25) +
        (completenessQueries (2 ^ 25) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 192 +
        rpmError (completenessPermCalls (2 ^ 25))
      ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 + (2 : ℝ≥0∞)⁻¹ ^ 128 + (2 : ℝ≥0∞)⁻¹ ^ 128 :=
        add_le_add (add_le_add EndToEnd.Complete.completenessError_le hz)
          rpmError_completenessPermCalls_le
    _ ≤ 4 * (2 : ℝ≥0∞)⁻¹ ^ 128 := by
        rw [show (4 : ℝ≥0∞) = 1 + 1 + 1 + 1 by norm_num]
        simp only [add_mul, one_mul]
        exact le_self_add
    _ = (2 : ℝ≥0∞)⁻¹ ^ 126 := by
        rw [show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num, show (128 : ℕ) = 2 + 126 from rfl]
        exact Common.two_pow_mul_inv_pow 2 126

/-- **The child prover in the random-permutation model, at `2^25` nonces**: rejected by the
verifier refusing a zero challenge with probability at most `2^-126`. -/
theorem rpmChild_126 {prog : Program} {input : PublicInput} {t : Trace prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28)
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) :
    Pr{let v ← (simulateQ rpmImpl (childRun prog input t ρ (2 ^ 25))).run' []}[v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 126 :=
  (rpmChild hv hbudget hρ (by norm_num)).trans rpmChild_le

end LeanVM.Guest.Child
