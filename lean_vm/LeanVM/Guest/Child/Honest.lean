/-
  LeanVM.Guest.Child.Honest

  The honest prover of a child: the compiled honest prover of a witness whose sizes are the
  execution's own, so that its stack is the execution's committed size. Its proof with the
  deployed Keccak, when the verifier accepts it, is the pure prover's proof of that witness.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Rom
public import Statement.LeanVmGuest
public import LeanVM.Guest.Child.Fresh
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.WithHash

/-!
# The honest prover of a child

`childComp` is `EndToEnd.Complete.honestComp` with its witness chosen among those whose stacked
size is the execution's committed size (`ChildFor`; one exists within the verifier's cap,
`exists_childFor`, as `exists_admissible_witness` builds it). Its proof with Keccak-256 and
Keccak-f[1600] (`honestProofWithDeployedKeccak`) is the pure prover's (`atKeccak_childComp`), and a proof the
verifier accepts is not the empty one (`runProof_execWith_empty`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.KeccakHash OracleComp OracleSpec
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- The witness of a child's proof: an honest witness of the execution whose stacked size is the
execution's committed size. -/
def ChildFor (prog : Program) (input : PublicInput) (t : Execution prog) (ρ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog)) (s : Sizes) : Prop :=
  HonestFor prog input t ρ w s ∧ (LeanIsa.blocks prog s).total = t.committedSize

/-- **A child's witness exists** for a valid execution within the verifier's cap, at a valid
rate: `exists_admissible_witness`'s witness. -/
theorem exists_childFor {prog : Program} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ maxMu)
    (hρ : validRate ρ) : ∃ w s, ChildFor prog input t ρ w s := by
  have hcount : ∀ op, t.count op = t.runRows op := Execution.count_eq_runRows hv.2
  have hheight : ∀ op, 2 ^ Nat.clog 2 (t.count op) ≤ t.committedSize := by
    intro op
    have : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
    have hk : 2 ^ Nat.clog 2 (t.count .keccak) ≤ 2 ^ max (Nat.clog 2 (t.count .keccak)) 9 :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    simp only [Execution.committedSize]
    cases op <;> omega
  have hcap : (2 : ℕ) ^ maxMu ≤ 2 ^ maxLogRows := Nat.pow_le_pow_right (by norm_num) (by decide)
  have hrows : ∀ op, t.runRows op ≤ 2 ^ maxLogRows := fun op ↦ by
    rw [← hcount]
    exact (Nat.le_pow_clog (by norm_num) _).trans (((hheight op).trans hbudget).trans hcap)
  obtain ⟨w, hw, hrep, hlen⟩ := constraintCompleteness_rows hv hrows
  obtain ⟨s, hs⟩ := sizes_of_satisfiedBy hw
  have hs0 := hs
  obtain ⟨hpos, rfl⟩ := eq_of_ofWitness hs
  have hmem : (witnessSizes w hpos).logMem = t.logMemorySize := hrep.κ_eq
  have hr : ∀ j : Fin 6, (witnessSizes w hpos).rows j = t.count (tableOpcode j) :=
    fun j ↦ (hlen j).trans (hcount _).symm
  have htotal : (LeanIsa.blocks prog (witnessSizes w hpos)).total = t.committedSize := by
    have e : tableOpcode 0 = .xor ∧ tableOpcode 1 = .mulNative ∧ tableOpcode 2 = .setConstant ∧
        tableOpcode 3 = .deref ∧ tableOpcode 4 = .jump ∧ tableOpcode 5 = .keccak := by decide
    rw [blocks_total_eq, hmem, pow_add 2 _ 6]
    simp only [Sizes.τ, hr, e, Execution.committedSize]
    have f0 : tableLogFloors.getD ((0 : Fin 6) : ℕ) 0 = 0 := rfl
    have f1 : tableLogFloors.getD ((1 : Fin 6) : ℕ) 0 = 0 := rfl
    have f2 : tableLogFloors.getD ((2 : Fin 6) : ℕ) 0 = 0 := rfl
    have f3 : tableLogFloors.getD ((3 : Fin 6) : ℕ) 0 = 0 := rfl
    have f4 : tableLogFloors.getD ((4 : Fin 6) : ℕ) 0 = 0 := rfl
    have f5 : tableLogFloors.getD ((5 : Fin 6) : ℕ) 0 = 9 := rfl
    simp only [f0, f1, f2, f3, f4, f5, Nat.max_zero]
    ring
  refine ⟨w, _, ⟨hρ, hw, hs0, ⟨?_, ?_, fun j ↦ (hr j).trans_le (by rw [hcount]; exact hrows _),
    leanIsaμ_le_of_total_le (htotal ▸ hbudget)⟩, hrep⟩, htotal⟩
  · rw [hmem]
    exact hv.1.1
  · rw [hmem]
    exact hv.1.2.1

open Classical in
/-- **The honest prover of a child**: `honestComp` at a child's witness (`ChildFor`, chosen
classically); the empty proof when there is none. -/
noncomputable def childComp (prog : Program) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) : OracleComp KeccakCalls Proof :=
  if h : ∃ w s, ChildFor prog input t ρ w s then
    Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
      (leanVmProgram (bytecodeWords prog) (publicDigest input))
      (leanVmProver prog h.choose_spec.choose ρ (stackOf prog h.choose_spec.choose h.choose)) fuel
  else pure ⟨[], []⟩

/-- The honest prover of a child, as an `HonestProver`. -/
noncomputable def childProver : HonestProverWithHash := childComp

/-- `deployedKeccakCalls` is the total implementation at Keccak-256 and Keccak-f[1600]. -/
theorem keccakImpl_eq : Budget.deployedKeccakCalls = totalImpl keccak256 keccakF1600 := by
  funext q
  rcases q with x | s <;> rfl

/-- The specification's honest prover of a child at a witness: `Rom.honestComp` at leanVM's seed,
program and the witness's strategy. -/
abbrev ChildSpec (A : HonestProverWithHash) (prog : Program) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) : Prop :=
  A prog input t ρ fuel = pure ⟨[], []⟩ ∨ ∃ w s, ChildFor prog input t ρ w s ∧
    A prog input t ρ fuel = Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
      (leanVmProgram (bytecodeWords prog) (publicDigest input))
      (leanVmProver prog s ρ (stackOf prog s w)) fuel

/-- **The child prover is the specification at a child's witness**, or the empty proof. -/
theorem childSpec_childProver (prog : Program) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) : ChildSpec childProver prog input t ρ fuel := by
  by_cases h : ∃ w s, ChildFor prog input t ρ w s
  · refine Or.inr ⟨_, _, h.choose_spec.choose_spec, ?_⟩
    unfold childProver childComp
    simp only [h, ↓reduceDIte]
  · refine Or.inl ?_
    unfold childProver childComp
    simp only [h, ↓reduceDIte]

/-- **A prover's proof with Keccak**, where it is the specification's honest prover of a
strategy: the pure prover's proof, or the empty proof. -/
theorem atKeccak_of_eq {A : HonestProverWithHash} {prog : Program} {input : PublicInput} {t : Execution prog}
    {ρ fuel : ℕ} {S : Strategy}
    (hA : A prog input t ρ fuel = Rom.honestComp (leanVmSeed (bytecodeWords prog)
      (publicDigest input)) (leanVmProgram (bytecodeWords prog) (publicDigest input)) S fuel) :
    Budget.honestProofWithDeployedKeccakWithHash A prog input t ρ fuel =
      (prove keccak256 keccakF1600 (leanVmProgram (bytecodeWords prog) (publicDigest input)) S
        (seed (bytecodeWords prog) (publicDigest input)) fuel).getD ⟨[], []⟩ := by
  unfold Budget.honestProofWithDeployedKeccakWithHash
  rw [hA]
  simp only [keccakImpl_eq, Rom.honestComp, simulateQ_bind,
    simulateQ_proveM, simulateQ_pure, implH_totalImpl, implF_totalImpl, seedRun_leanVmSeed]
  rw [← proveM_id]
  rfl

/-- **The child's proof with Keccak**, in the branch with a witness: the pure prover's proof, or
the empty proof. -/
theorem atKeccak_childComp {prog : Program} {input : PublicInput} {t : Execution prog} {ρ fuel : ℕ}
    (h : ∃ w s, ChildFor prog input t ρ w s) :
    Budget.honestProofWithDeployedKeccakWithHash childProver prog input t ρ fuel =
      (prove keccak256 keccakF1600 (leanVmProgram (bytecodeWords prog) (publicDigest input))
        (leanVmProver prog h.choose_spec.choose ρ (stackOf prog h.choose_spec.choose h.choose))
        (seed (bytecodeWords prog) (publicDigest input)) fuel).getD ⟨[], []⟩ := by
  unfold Budget.honestProofWithDeployedKeccakWithHash childProver childComp
  simp only [h, ↓reduceDIte, keccakImpl_eq, Rom.honestComp, simulateQ_bind,
    simulateQ_proveM, simulateQ_pure, implH_totalImpl, implF_totalImpl, seedRun_leanVmSeed]
  rw [← proveM_id]
  rfl

/-- The verifier refusing a zero challenge, at Keccak, is the run of `execWith`. -/
theorem verifierNZ_eq (prog : Program) (input : PublicInput) (π : Proof) :
    Budget.verifierNZ (m := Id) keccak256 keccakF1600 prog input π =
      Id.run (runProofWithHash (m := Id) keccak256 keccakF1600
        ((execWith computedValue Limits.verifyStackedOpeningNZ (bytecodeWords prog)
          (publicDigest input)).bind fun _ ↦ Prog.ret true)
        (seed (bytecodeWords prog) (publicDigest input)) π) := rfl

/-- The statement's refusing verifier, at Keccak, is the run of `execWith` refusing zero
challenges. -/
theorem verifierRZ_eq (prog : Program) (input : PublicInput) (π : Proof) :
    Budget.verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 prog input π =
      Id.run (runProofWithHash (m := Id) keccak256 keccakF1600
        ((execWith computedValue verifyStackedOpening (bytecodeWords prog)
          (publicDigest input)).bind fun _ ↦ Prog.ret true).refusingZeroChallenge
        (seed (bytecodeWords prog) (publicDigest input)) π) := by
  unfold Budget.verifierRefusingZeroWithHash
  rw [Verifier.leanVmProgram_eq]
  rfl

/-- **No program reading first accepts the empty proof.** -/
theorem runProof_read_empty (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState) (k : E → Prog Bool)
    (sd : KeccakState) : Id.run (runProofWithHash H F (Prog.read k) sd ⟨[], []⟩) = false := rfl

/-- The verifier reads first. -/
theorem execWith_bind_read (ev : (List K → List E → Prog E)) (opening : ℕ → ℕ → List StackClaim → Prog Unit)
    (bytecode : List K) (publicInput : Digest) (f : Unit → Prog Bool) :
    ∃ k, (execWith ev opening bytecode publicInput).bind f = Prog.read k :=
  ⟨_, rfl⟩

/-- **A proof with Keccak that the verifier accepts**, of a prover that is the specification at a
child's witness or the empty proof, is the pure prover's proof of a child's witness. -/
theorem prove_of_verifierNZ_of {A : HonestProverWithHash} {prog : Program} {input : PublicInput}
    {t : Execution prog} {ρ fuel : ℕ} (hA : ChildSpec A prog input t ρ fuel)
    (hacc : Budget.verifierNZ (m := Id) keccak256 keccakF1600 prog input
      (Budget.honestProofWithDeployedKeccakWithHash A prog input t ρ fuel) = true) :
    ∃ w s, ChildFor prog input t ρ w s ∧
      prove keccak256 keccakF1600 (leanVmProgram (bytecodeWords prog) (publicDigest input))
        (leanVmProver prog s ρ (stackOf prog s w)) (seed (bytecodeWords prog) (publicDigest input))
        fuel = some (Budget.honestProofWithDeployedKeccakWithHash A prog input t ρ fuel) := by
  rcases hA with hA | ⟨w, s, hc, hA⟩
  · exfalso
    have e : Budget.honestProofWithDeployedKeccakWithHash A prog input t ρ fuel = ⟨[], []⟩ := by
      unfold Budget.honestProofWithDeployedKeccakWithHash
      rw [hA, simulateQ_pure]
      rfl
    rw [e, verifierNZ_eq] at hacc
    obtain ⟨k, hk⟩ := execWith_bind_read computedValue Limits.verifyStackedOpeningNZ
      (bytecodeWords prog) (publicDigest input) fun _ ↦ Prog.ret true
    rw [hk] at hacc
    exact absurd hacc (by simp [runProof_read_empty])
  · refine ⟨w, s, hc, ?_⟩
    have e := atKeccak_of_eq hA
    revert hacc
    rw [e]
    cases hp : prove keccak256 keccakF1600 _ _ _ fuel with
    | some π => intro _; rfl
    | none =>
      intro hacc
      rw [verifierNZ_eq] at hacc
      obtain ⟨k, hk⟩ := execWith_bind_read computedValue Limits.verifyStackedOpeningNZ
        (bytecodeWords prog) (publicDigest input) fun _ ↦ Prog.ret true
      rw [hk] at hacc
      exact absurd hacc (by simp [runProof_read_empty])

end
end LeanVM.Guest.Child
