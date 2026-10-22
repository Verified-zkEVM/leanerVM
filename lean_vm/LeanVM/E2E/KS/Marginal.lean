/-
  LeanVM.E2E.KS.Marginal

  The deployed game is the game before verification followed by the verifier, so an event of the
  outcome before verification has the same probability in both (decision E2E-15).
-/

module

public import LeanVM.E2E.KS.Prefix
public import LeanVM.E2E.KS.Closed

/-!
# The verifier stage is a marginal

* `run_verifyAggregateWith_hashQuery`: the deployed verifier, run in the game's monad, keeps the
  signers' state (`rel_verifyAggregateWith`).
* `dGameComp_eq`: the deployed game is `pGameComp` then the verifier.
* `prEvent_dGame_pre`: every event of the outcome before verification (`DOutcome.pre`) has the same
  probability in `dGame` as in `pGame`; oracle computations are lossless.
-/

namespace LeanVM.E2E.KS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.E2E OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ}

/-- The deployed verifier with the game's hash, in the oracle computation. -/
noncomputable def verifyO (guest : Program) (s : NodeStatement) (π : Proof) :
    OracleComp GameSpec Bool :=
  verifyAggregateWith (fun x ↦ (liftM (HashSpec.query x) : OracleComp GameSpec Digest)) guest s π

/-- **The verifier stage keeps the signers' state**: run in the game's monad, it is the oracle
computation `verifyO` with the state unchanged. -/
theorem run_verifyAggregateWith_hashQuery (guest : Program) (s : NodeStatement) (π : Proof)
    (st : SignState nx ns) :
    (verifyAggregateWith (hashQuery (nx := nx) (ns := ns)) guest s π).run st =
      (fun b ↦ (b, st)) <$> verifyO guest s π := by
  refine rel_verifyAggregateWith
    (fun {α} (x : GameM nx ns α) (y : OracleComp GameSpec α) ↦
      ∀ st, x.run st = (fun a ↦ (a, st)) <$> y) ?_ ?_ _ _ ?_ guest s π st
  · intro α a st
    simp
  · intro α β x y f g hxy hfg st
    rw [StateT.run_bind, hxy st, bind_map_left, map_bind]
    simp only [hfg]
  · intro x st
    simp [hashQuery]

variable [Sphincs.Params]

/-- **The deployed game is the game before verification, then the verifier.** -/
theorem dGameComp_eq (guest : Program) (A : DAdversary nx ns) :
    dGameComp guest A = pGameComp A >>= fun z ↦
      (fun b ↦ (⟨z.keys, z.statement, z.proof, z.trace, b, z.state⟩ : DOutcome nx ns)) <$>
        verifyO guest z.statement z.proof := by
  unfold dGameComp pGameComp
  simp only [StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind,
    run_verifyAggregateWith_hashQuery, map_eq_bind_pure_comp, Function.comp_def]

/-- The game's oracle: coins forwarded, the hash lazily sampled over the log. -/
noncomputable abbrev dImpl : QueryImpl GameSpec (StateT Log ProbComp) :=
  coinImpl + (Rom.loggedRO : QueryImpl HashSpec (StateT Log ProbComp))

/-- **An event before verification has the same probability in the deployed game as in the game
before verification**: the verifier changes neither the outcome before it nor the total mass. -/
theorem prEvent_dGame_pre (guest : Program) (A : DAdversary nx ns) (ev : POutcome nx ns → Prop) :
    Pr{let z ← dGame guest A}[ev z.1.pre] = Pr{let z ← pGame A}[ev z.1] := by
  classical
  have e : dGame guest A = pGame A >>= fun x ↦
      (simulateQ dImpl ((fun b ↦ (⟨x.1.keys, x.1.statement, x.1.proof, x.1.trace, b, x.1.state⟩ :
        DOutcome nx ns)) <$> verifyO guest x.1.statement x.1.proof)).run x.2 := by
    rw [dGame, dGameComp_eq, simulateQ_bind, StateT.run_bind]
    rfl
  rw [e]
  conv_rhs => rw [← bind_pure (pGame A)]
  refine prEvent_bind_congr _ _ _ _ _ fun x ↦ ?_
  rw [prEvent_pure]
  have hsupp : ∀ y ∈ support ((simulateQ dImpl ((fun b ↦ (⟨x.1.keys, x.1.statement, x.1.proof,
      x.1.trace, b, x.1.state⟩ : DOutcome nx ns)) <$> verifyO guest x.1.statement x.1.proof)).run
        x.2), y.1.pre = x.1 := by
    intro y hy
    rw [simulateQ_map, StateT.run_map, support_map] at hy
    obtain ⟨w, -, rfl⟩ := hy
    rfl
  rw [prEvent_congr_of_support _ _ (fun _ ↦ ev x.1) fun y hy ↦ by rw [hsupp y hy]]
  split_ifs with h
  · exact prEvent_const_of_lossless _ (prEvent_true_eq_one _) h
  · exact prEvent_const_of_not _ h

end
end LeanVM.E2E.KS
