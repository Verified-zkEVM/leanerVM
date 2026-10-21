/-
  LeanVM.Guest.B1.Main.BatchSpecM

  `Node.batchWith` over a hash model run on the chain: the transcript, the lambdas, the two
  sumchecks and the final check, each hash answered (`BatchSpec.lean` over a `HashModel`).
-/

module

public import LeanVM.Guest.B1.Main.AggChainM

/-!
# `Node.batchWith`, run over a hash model

`batchWith_of`: the batching from the chain state `s0` over the model's hash closes on the
claim `⟨rB, v, rM, a, b⟩` when the model answers its transcript (`obsCvM` of the count,
`obsAllM` of every child's cells, `childCells`), its lambdas (`sq2M`, `sq3M`: two and three
answered squeezes per child), its two `batchRoundsWith` runs, and the two final checks hold. It is
the forward direction of `batch_spec` with every chaining value the answer of the step before.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

variable {M : HashModel}

/-- Two answered squeezes per child: the lambdas and the state after them (`sq2`). -/
def sq2M (M : HashModel) : ℕ → Digest → Option (List (E × E) × Digest)
  | 0, cv => some ([], cv)
  | n + 1, cv => (sqCvM M cv).bind fun a => (sqCvM M a).bind fun b =>
      (sq2M M n b).map fun r => ((challengeOf a, challengeOf b) :: r.1, r.2)

/-- Three answered squeezes per child (`sq3`). -/
def sq3M (M : HashModel) : ℕ → Digest → Option (List (E × E × E) × Digest)
  | 0, cv => some ([], cv)
  | n + 1, cv => (sqCvM M cv).bind fun a => (sqCvM M a).bind fun b => (sqCvM M b).bind fun e =>
      (sq3M M n e).map fun r => ((challengeOf a, challengeOf b, challengeOf e) :: r.1, r.2)

/-- One more child's two squeezes, at the end. -/
theorem sq2M_succ : ∀ (n : ℕ) (cv : Digest), sq2M M (n + 1) cv =
    (sq2M M n cv).bind fun r => (sqCvM M r.2).bind fun a => (sqCvM M a).map fun b =>
      (r.1 ++ [(challengeOf a, challengeOf b)], b)
  | 0, cv => by
    simp only [sq2M, Option.bind_some]
    cases sqCvM M cv with
    | none => rfl
    | some a =>
      simp only [Option.bind_some]
      cases sqCvM M a <;> rfl
  | n + 1, cv => by
    rw [sq2M]
    conv_rhs => rw [sq2M]
    simp only [Option.bind_assoc]
    congr 1; funext a; congr 1; funext b
    rw [sq2M_succ n b]
    cases sq2M M n b with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, Option.map_some]
      cases sqCvM M r.2 with
      | none => rfl
      | some a' =>
        simp only [Option.bind_some]
        cases sqCvM M a' <;> rfl

/-- One more child's three squeezes, at the end. -/
theorem sq3M_succ : ∀ (n : ℕ) (cv : Digest), sq3M M (n + 1) cv =
    (sq3M M n cv).bind fun r => (sqCvM M r.2).bind fun a => (sqCvM M a).bind fun b =>
      (sqCvM M b).map fun e => (r.1 ++ [(challengeOf a, challengeOf b, challengeOf e)], e)
  | 0, cv => by
    simp only [sq3M, Option.bind_some]
    cases sqCvM M cv with
    | none => rfl
    | some a =>
      simp only [Option.bind_some]
      cases sqCvM M a with
      | none => rfl
      | some b =>
        simp only [Option.bind_some]
        cases sqCvM M b <;> rfl
  | n + 1, cv => by
    rw [sq3M]
    conv_rhs => rw [sq3M]
    simp only [Option.bind_assoc]
    congr 1; funext a; congr 1; funext b; congr 1; funext e
    rw [sq3M_succ n e]
    cases sq3M M n e with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, Option.map_some]
      cases sqCvM M r.2 with
      | none => rfl
      | some a' =>
        simp only [Option.bind_some]
        cases sqCvM M a' with
        | none => rfl
        | some b' =>
          simp only [Option.bind_some]
          cases sqCvM M b' <;> rfl

theorem observeWith_runM (x : E) (cv : Digest) :
    (observeWith (m := Option) M.H x).run cv = (obsCvM M cv x).map fun d => ((), d) := by
  simp only [observeWith, obsCvM, StateT.run_bind, StateT.run_get, StateT.run_set,
    StateT.run_monadLift, monadLift_self, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  cases M.H (digestBytes cv ++ blockOf x 1) <;> rfl

theorem squeezeWith_runM (cv : Digest) :
    (squeezeWith (m := Option) M.H).run cv = (sqCvM M cv).map fun d => (challengeOf d, d) := by
  simp only [squeezeWith, sqCvM, StateT.run_bind, StateT.run_get, StateT.run_set,
    StateT.run_monadLift, monadLift_self, StateT.run_pure, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  cases M.H (digestBytes cv ++ blockOf 0 2) <;> rfl

theorem forIn_observe_runM (xs : List E) (cv : Digest) :
    (forIn xs PUnit.unit (fun x _ => do
        observeWith (m := Option) M.H x
        pure (ForInStep.yield PUnit.unit))).run cv =
      (obsAllM M cv xs).map fun d => ((), d) := by
  induction xs generalizing cv with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, StateT.run_bind, observeWith_runM, obsAllM]
    cases obsCvM M cv x with
    | none => rfl
    | some d =>
      simp only [Option.map_some, Option.bind_some]
      exact ih d

theorem forIn_children_runM (cs : List ChildClaims) (cv : Digest) :
    (forIn cs PUnit.unit fun (c : ChildClaims) _ => do
        observeWith (m := Option) M.H (digestScalars c.publicInput).1
        observeWith (m := Option) M.H (digestScalars c.publicInput).2
        forIn (fixedCells c.fresh ++ c.carried.cells) PUnit.unit fun x _ => do
          observeWith (m := Option) M.H x
          pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit)).run cv =
      (obsAllM M cv (cs.flatMap childCells)).map fun d => ((), d) := by
  induction cs generalizing cv with
  | nil => rfl
  | cons c cs ih =>
    have e : (c :: cs).flatMap childCells = (digestScalars c.publicInput).1 ::
        (digestScalars c.publicInput).2 :: ((fixedCells c.fresh ++ c.carried.cells) ++
          cs.flatMap childCells) := by
      simp [childCells]
    rw [e]
    simp only [obsAllM, obsAllM_append (xs := fixedCells c.fresh ++ c.carried.cells)]
    simp only [List.forIn_cons, StateT.run_bind, observeWith_runM, forIn_observe_runM]
    rcases obsCvM M cv (digestScalars c.publicInput).1 with _ | d1
    · rfl
    · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rcases obsCvM M d1 (digestScalars c.publicInput).2 with _ | d2
      · rfl
      · simp only [Option.map_some, Option.bind_some]
        rcases obsAllM M d2 (fixedCells c.fresh ++ c.carried.cells) with _ | d3
        · rfl
        · simp only [Option.map_some, Option.bind_some]
          exact ih d3

theorem forIn_sq2_runM {α : Type} (l : List α) (acc : List (E × E)) (cv : Digest) :
    (forIn l acc (fun _ acc => do
        let lf ← squeezeWith (m := Option) M.H
        let lc ← squeezeWith (m := Option) M.H
        pure (ForInStep.yield (acc ++ [(lf, lc)])))).run cv =
      (sq2M M l.length cv).map fun r => (acc ++ r.1, r.2) := by
  induction l generalizing acc cv with
  | nil => simp [sq2M]
  | cons a l ih =>
    simp only [List.forIn_cons, List.length_cons, sq2M, StateT.run_bind, squeezeWith_runM]
    rcases sqCvM M cv with _ | a'
    · rfl
    · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rcases sqCvM M a' with _ | b
      · rfl
      · simp only [Option.map_some, Option.bind_some, Option.pure_def, StateT.run_pure]
        rw [ih]
        cases sq2M M l.length b <;> simp

theorem forIn_sq3_runM {α : Type} (l : List α) (acc : List (E × E × E)) (cv : Digest) :
    (forIn l acc (fun _ acc => do
        let lf ← squeezeWith (m := Option) M.H
        let la ← squeezeWith (m := Option) M.H
        let lb ← squeezeWith (m := Option) M.H
        pure (ForInStep.yield (acc ++ [(lf, la, lb)])))).run cv =
      (sq3M M l.length cv).map fun r => (acc ++ r.1, r.2) := by
  induction l generalizing acc cv with
  | nil => simp [sq3M]
  | cons a l ih =>
    simp only [List.forIn_cons, List.length_cons, sq3M, StateT.run_bind, squeezeWith_runM]
    rcases sqCvM M cv with _ | a'
    · rfl
    · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rcases sqCvM M a' with _ | b
      · rfl
      · simp only [Option.map_some, Option.bind_some]
        rcases sqCvM M b with _ | e
        · rfl
        · simp only [Option.map_some, Option.bind_some, Option.pure_def, StateT.run_pure]
          rw [ih]
          cases sq3M M l.length e <;> simp

/-- An answered run of the rounds draws one challenge per round. -/
theorem batchRoundsWith_length : ∀ (rounds : List (E × E)) (claim : E) (cv cv' : Digest)
    (rs : List E) (final : E),
    (batchRoundsWith (m := Option) M.H claim rounds).run cv = some ((rs, final), cv') →
      rs.length = rounds.length
  | [], claim, cv, cv', rs, final, h => by
    simp only [batchRoundsWith, StateT.run_pure, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at h
    rw [← h.1.1]; rfl
  | (g1, gInf) :: rest, claim, cv, cv', rs, final, h => by
    simp only [batchRoundsWith, StateT.run_bind, observeWith_runM, squeezeWith_runM,
      Option.bind_eq_bind] at h
    rcases h1 : obsCvM M cv g1 with _ | d1
    · rw [h1] at h; cases h
    · rw [h1] at h
      simp only [Option.map_some, Option.bind_some] at h
      rcases h2 : obsCvM M d1 gInf with _ | d2
      · rw [h2] at h; cases h
      · rw [h2] at h
        simp only [Option.map_some, Option.bind_some] at h
        rcases h3 : sqCvM M d2 with _ | d3
        · rw [h3] at h; cases h
        · rw [h3] at h
          simp only [Option.map_some, Option.bind_some] at h
          rcases hr : (batchRoundsWith (m := Option) M.H
            ((gInf * challengeOf d3 + (claim + g1 + g1 + gInf)) * challengeOf d3 + (claim + g1))
              rest).run d3 with _ | ⟨⟨rs', f'⟩, c'⟩
          · rw [hr] at h; cases h
          · rw [hr] at h
            simp only [Option.bind_some, StateT.run_pure, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at h
            rw [← h.1.1, List.length_cons, batchRoundsWith_length rest _ _ _ _ _ hr,
              List.length_cons]

/-- **The batching over a hash model, forward**: from the chain state `s0`, the answered
transcript, lambdas and rounds, and the two final checks, close the batching on the claim of the
two rounds' points, the hinted values. -/
theorem batchWith_of {s0 cv1 cvA cvB cvC cvD cvE : Digest} {cs : List ChildClaims}
    {h : BatchHints} {lB : List (E × E)} {lM : List (E × E × E)} {rs rM : List E}
    {final finalM : E}
    (h1 : obsCvM M s0 (ofK (Parameters.gpow cs.length)) = some cv1)
    (hA : obsAllM M cv1 (cs.flatMap childCells) = some cvA)
    (hB : sq2M M cs.length cvA = some (lB, cvB))
    (hrun : (batchRoundsWith (m := Option) M.H (sumE (List.zipWith (fun c l ↦
      l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) cs lB)) h.bytecodeRounds).run cvB =
        some ((rs, final), cvC))
    (hC : sq3M M cs.length cvC = some (lM, cvD))
    (hrunM : (batchRoundsWith (m := Option) M.H (sumE (List.zipWith (fun c l ↦
      l.1 * c.fresh.matrixValue + l.2.1 * c.carried.matrixA + l.2.2 * c.carried.matrixB) cs lM))
        h.matrixRounds).run cvD = some ((rM, finalM), cvE))
    (hc1 : final = h.bytecodeValue * sumE (List.zipWith (fun c l ↦
      l.1 * eqEval c.fresh.bytecodePoint rs + l.2 * eqEval c.carried.bytecodePoint rs) cs lB))
    (hc2 : finalM = h.matrixA * sumE (List.zipWith (fun c l ↦ l.1 * freshWeight c.fresh rM +
        l.2.1 * eqEval c.carried.matrixPoint rM) cs lM) +
      h.matrixB * sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.alpha * freshWeight c.fresh rM +
        l.2.2 * eqEval c.carried.matrixPoint rM) cs lM)) :
    batchWith (m := Option) M.H s0 cs h = some (some ⟨rs, h.bytecodeValue, rM, h.matrixA, h.matrixB⟩) := by
  simp only [batchWith, batchWith.go, StateT.run'_eq, StateT.run_bind, observeWith_runM, h1,
    Option.map_some, Option.bind_eq_bind, Option.bind_some]
  rw [forIn_children_runM, hA]
  simp only [Option.map_some, Option.bind_some]
  rw [forIn_sq2_runM, hB]
  simp only [Option.map_some, Option.bind_some, List.nil_append]
  rw [hrun]
  simp only [Option.bind_some]
  rw [forIn_sq3_runM, hC]
  simp only [Option.map_some, Option.bind_some, List.nil_append]
  rw [hrunM]
  simp only [Option.bind_some, ← hc1, ← hc2, and_self, ↓reduceIte, StateT.run_pure]
  rfl

end
end LeanVM.Guest.B1.Main
