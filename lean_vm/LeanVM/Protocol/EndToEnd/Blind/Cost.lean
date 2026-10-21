/-
  LeanVM.Protocol.EndToEnd.Blind.Cost

  The query cost of the Flock-blind verifier program V°: the deployed bound, since deleting the
  lincheck's terminal check removes no hash query, and the compiled V° with the hash a query.
-/

module

public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Spec.Ideal.Blind

/-!
# The query cost of V°

`blindProgram bytecode publicInput` (`LeanVM.Spec.Ideal.Blind`) is `leanVmProgram` with the
lincheck's matrices value and terminal `require` deleted, neither of which hashes: its runs cost at
most `leanVmCost = 13210` (`costLE_blindProgram`), and the compiled V° makes at most
`leanVmQueryBound = 13213` queries on every proof (`isTotalQueryBound_blind`), with the deployed
seed (`verifierComp_blind`: the seeded V° is `verifyBlindWith` with the hash a query).
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Blake2sHash
open OracleComp OracleSpec

@[expose] public section

section Phases

variable {height : ℕ}

/-- The lincheck without its terminal check: eight rounds and the `64` slices. -/
theorem costs_verifyFlockLincheckBlind (zc : ZerocheckResult) :
    Prog.Costs height (verifyFlockLincheckBlind zc) 89 fun _ ↦ True := by
  refine Prog.Costs.seq Prog.Costs.sampleE (fun _ _ ↦ Prog.Costs.seq (costs_sumcheck _ _ _)
    (fun r _ ↦ ?_) ?_) ?_
  · obtain ⟨roundChallenges, rLc⟩ := r
    exact Prog.Costs.seq (Prog.Costs.readN kBits) (fun _ _ ↦ trivial)
      (by simp only [List.length_replicate, flockNumLincheckRounds_eq, kBits,
        show max 3 2 = 3 from rfl]; omega)
  all_goals (try simp only [List.length_replicate, flockNumLincheckRounds_eq,
    show max 3 2 = 3 from rfl])
  all_goals omega

/-- **Flock without its terminal check** at `logN` variables. -/
theorem costs_verifyFlockBlind (logN : ℕ) :
    Prog.Costs height (verifyFlockBlind logN) (4 * (logN - 13) + 177) fun _ ↦ True :=
  Prog.Costs.seq (costs_verifyFlockZerocheck logN) (fun zc _ ↦
    (costs_verifyFlockLincheckBlind zc).mono (by omega) fun _ h ↦ h) (by omega)

end Phases

/-- An entry of a list of bounded numbers is bounded. -/
private theorem getD_le_of_forall' {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) (i : ℕ) :
    l.getD i 0 ≤ M := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some x => exact h x (List.mem_of_getElem? hi)

/-- **The cost of `verifyExecutionBlind`**: the deployed bound. -/
theorem costs_verifyExecutionBlind (bytecode : List K) (publicInput : Digest) :
    Prog.Costs costHeight (verifyExecutionBlind bytecode publicInput) leanVmCost
      fun _ ↦ True := by
  unfold leanVmCost
  refine Prog.Costs.seq (costs_readSizes bytecode) (fun p hp ↦ ?_) (by omega)
  obtain ⟨layout, logInverseRate⟩ := p
  obtain ⟨hl, -, -, -, -⟩ := hp
  have hblake : layout.tableLogHeights.getD opBlake2s 0 ≤ 32 :=
    getD_le_of_forall' hl.heights_le opBlake2s
  refine Prog.Costs.seq (costs_commitStack _ _ fun levels h ↦ (ladder_cost _ _ levels h).2.1)
    (fun _ _ ↦ Prog.Costs.seq (costs_verifyBusBalance_le hl) (fun bus _ ↦ Prog.Costs.seq
      (costs_tablePhase hl bus) (fun claims _ ↦ Prog.Costs.seq
        (costs_publicInputPhase layout publicInput) (fun publicClaims _ ↦ Prog.Costs.seq
          (costs_verifyFlockBlind _) (fun r _ ↦ ?_) ?_) ?_) ?_) ?_) ?_
  · obtain ⟨flockPoint, flockS⟩ := r
    refine Prog.Costs.seq (costs_ringSwitch flockPoint flockS) (fun r _ ↦ ?_) ?_
    · obtain ⟨ringTarget, ringWeight⟩ := r
      refine (costs_verifyStackedOpening _ _ _ whirBound fun levels h ↦
        ⟨(ladder_cost _ _ levels h).1, (ladder_cost _ _ levels h).2.2⟩).mono ?_
          fun _ h ↦ h
      simp only [flockBound, blake2sR1csLogSize] at *
      omega
    · simp only [flockBound, blake2sR1csLogSize] at *
      omega
  all_goals simp only [flockBound, blake2sR1csLogSize] at *
  all_goals omega

/-- **The cost of the Flock-blind verifier program**: every run costs at most `leanVmCost`, every
commitment of height at most `costHeight`. -/
theorem costLE_blindProgram (bytecode : List K) (publicInput : Digest) :
    (blindProgram bytecode publicInput).CostLE costHeight leanVmCost :=
  Prog.Costs.seq (costs_verifyExecutionBlind bytecode publicInput) (fun _ _ ↦ trivial) le_rfl

/-- The seeded verifier of the random-oracle theorem at the deployed seed and V° is
`verifyBlindWith` with the hash a query. -/
theorem verifierComp_blind (bytecode : List K) (publicInput : Digest) (π : Proof) :
    verifierComp (leanVmSeed bytecode publicInput) (blindProgram bytecode publicInput) π =
      verifyBlindWith queryH bytecode publicInput π := by
  simp only [verifierComp, Rom.verify, verifyBlindWith, seedRun_leanVmSeed]

/-- **The compiled V° makes at most `leanVmQueryBound = 13213` queries** on every proof. -/
theorem isTotalQueryBound_blind (bytecode : List K) (publicInput : Digest) (π : Proof) :
    IsTotalQueryBound
      (verifierComp (leanVmSeed bytecode publicInput) (blindProgram bytecode publicInput) π)
      leanVmQueryBound :=
  isTotalQueryBound_verifierComp (costLE_blindProgram bytecode publicInput) _ π

end
end LeanVM.Protocol.Verifier
