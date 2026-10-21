/-
  LeanVM.E2E.Budget

  The game's budgeted run of V_I against a hash answered by a function `H`: it is V_I's `Id` run
  with `H`, the state's `spent` advanced by V_I's query count, when the count fits the budget,
  and a rejection otherwise (L16 of `docs/roadmap/t6-completeness.md`).
-/

module

public import LeanVM.E2E.Natural

/-!
# The budgeted run

The game runs V_I against `budgetedQuery budget` in `OptionT (GameM nx ns)`: each hash query is
counted in the state's `spent` and refused once `spent` reaches `budget`. With the game's oracle
simulated by any implementation `impl` answering every hash query `x` with `pure (H x)` (into any
lawful monad), the run from a state `st` is (`run_idealVerify_budgetedQuery`)

* `pure (some v, st')` with `v` V_I's `Id` run with `H` and `st'` the state with `spent` advanced
  by V_I's query count `queryCount H …` (the queries of the `Id` run, with multiplicity), when that
  count is `0` or `st.spent + count ≤ budget`;
* `pure (none, st')` with `spent` at `max st.spent budget` otherwise.

The proof is three applications of V_I's naturality (`Natural.lean`): the simulation of the game's
oracle under `OptionT` and `StateT` is a monad morphism (`simHash`), taking `budgetedQuery` to the
charge (`charge`) of one counted query; the charge of a counted computation (`Counted`: a value
and a count) is a monad morphism, so it commutes with V_I; and the value of the counted run is the
`Id` run (`val_idealVerify_counted`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open OracleSpec OracleComp

@[expose] public section

/-! ## Counted computations -/

/-- **A computation with its count of hash queries**: a value and a count, the counts of a
sequence added. -/
structure Counted (α : Type) where
  /-- The number of queries. -/
  count : ℕ
  /-- The value. -/
  val : α

/-- Counted computations form a monad: `pure` counts nothing, `bind` adds the counts. -/
instance : Monad Counted where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.count + (f x.val).count, (f x.val).val⟩

/-- The counted monad is lawful. -/
instance : LawfulMonad Counted := LawfulMonad.mk'
  (id_map := fun x ↦ by
    show (⟨x.count + 0, x.val⟩ : Counted _) = x
    simp)
  (pure_bind := fun a f ↦ by
    show (⟨0 + (f a).count, (f a).val⟩ : Counted _) = f a
    simp)
  (bind_assoc := fun x f g ↦ by
    show (⟨x.count + (f x.val).count + (g (f x.val).val).count, (g (f x.val).val).val⟩ :
      Counted _) = ⟨x.count + ((f x.val).count + (g (f x.val).val).count), (g (f x.val).val).val⟩
    rw [Nat.add_assoc])

/-- One query of the hash `H`, counted. -/
def countQuery (H : Bytes → Digest) (x : Bytes) : Counted Digest := ⟨1, H x⟩

/-- **V_I's query count** with the hash `H`: the hash queries of its run, with multiplicity. -/
noncomputable def queryCount (H : Bytes → Digest) (prog : Program) (ip : IdealProof) (fuel : ℕ)
    (s : NodeStatement) : ℕ :=
  (idealVerify (countQuery H) prog ip fuel s).count

/-- The value of a counted computation is a monad morphism to `Id`. -/
theorem isMorphism_val : IsMorphism (m := Counted) (n := Id) fun x ↦ x.val :=
  ⟨fun _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- **The value of V_I's counted run is its `Id` run.** -/
theorem val_idealVerify_counted (H : Bytes → Digest) (prog : Program) (ip : IdealProof)
    (fuel : ℕ) (s : NodeStatement) :
    (idealVerify (countQuery H) prog ip fuel s).val =
      Id.run (idealVerify (fun x ↦ (pure (H x) : Id Digest)) prog ip fuel s) :=
  idealVerify_natural isMorphism_val (countQuery H) prog ip fuel s

/-! ## The charge of a count -/

variable {nx ns : ℕ} {b : Type → Type} [Monad b] [LawfulMonad b]

/-- **The charge of a counted computation against a budget**: its value, `spent` advanced by its
count, when the count is `0` or fits the budget; otherwise a rejection with `spent` at the
budget (or above, where it was). -/
def charge (budget : ℕ) {α : Type} (x : Counted α) : OptionT (StateT (SignState nx ns) b) α :=
  OptionT.mk (StateT.mk fun st ↦ pure
    (if x.count = 0 ∨ st.spent + x.count ≤ budget then
      (some x.val, { st with spent := st.spent + x.count })
    else (none, { st with spent := max st.spent budget })))

omit [LawfulMonad b] in
/-- Running a charge. -/
theorem run_charge (budget : ℕ) {α : Type} (x : Counted α) (st : SignState nx ns) :
    ((charge (b := b) budget x).run).run st = pure
      (if x.count = 0 ∨ st.spent + x.count ≤ budget then
        (some x.val, { st with spent := st.spent + x.count })
      else (none, { st with spent := max st.spent budget })) := rfl

/-- **The charge is a monad morphism.** -/
theorem isMorphism_charge (budget : ℕ) :
    IsMorphism (m := Counted) (n := OptionT (StateT (SignState nx ns) b)) (charge budget) := by
  constructor
  · intro α a
    refine OptionT.ext (StateT.ext fun st ↦ ?_)
    rw [run_charge]
    show _ = (pure (some a, st) : b _)
    cases st
    simp only [show (pure a : Counted α).count = 0 from rfl, true_or, ↓reduceIte, Nat.add_zero]
    rfl
  · intro α β x f
    refine OptionT.ext (StateT.ext fun st ↦ ?_)
    rw [run_charge, OptionT.run_bind, Option.elimM, StateT.run_bind, run_charge, pure_bind]
    show (pure (if x.count + (f x.val).count = 0 ∨ st.spent + (x.count + (f x.val).count) ≤ budget
      then _ else _) : b _) = _
    have hv : (x >>= f).val = (f x.val).val := rfl
    have hc : (x >>= f).count = x.count + (f x.val).count := rfl
    rw [hv, hc]
    by_cases h1 : x.count = 0 ∨ st.spent + x.count ≤ budget
    · simp only [h1, ↓reduceIte, Option.elim, run_charge]
      congr 1
      split_ifs with h2 h3 h3 <;> simp only [Prod.mk.injEq, SignState.mk.injEq, true_and,
        reduceCtorEq, false_and] <;> omega
    · simp only [h1, ↓reduceIte, Option.elim]
      show _ = (pure (none, _) : b _)
      congr 1
      split_ifs with h2
      · omega
      · rfl

/-! ## The game's oracle simulated -/

/-- **The game's oracle simulated by `impl`**, under the game's `OptionT` and state. -/
noncomputable def simHash (impl : QueryImpl GameSpec b) {α : Type} (x : OptionT (GameM nx ns) α) :
    OptionT (StateT (SignState nx ns) b) α :=
  OptionT.mk (StateT.mk fun st ↦ simulateQ impl ((x.run).run st))

omit [LawfulMonad b] in
/-- Running a simulation. -/
theorem run_simHash (impl : QueryImpl GameSpec b) {α : Type} (x : OptionT (GameM nx ns) α)
    (st : SignState nx ns) :
    ((simHash impl x).run).run st = simulateQ impl ((x.run).run st) := rfl

/-- **The simulation is a monad morphism.** -/
theorem isMorphism_simHash (impl : QueryImpl GameSpec b) :
    IsMorphism (m := OptionT (GameM nx ns)) (n := OptionT (StateT (SignState nx ns) b))
      (simHash impl) := by
  constructor
  · intro α a
    refine OptionT.ext (StateT.ext fun st ↦ ?_)
    rw [run_simHash]
    rfl
  · intro α β x f
    refine OptionT.ext (StateT.ext fun st ↦ ?_)
    rw [run_simHash, OptionT.run_bind, Option.elimM, StateT.run_bind, OptionT.run_bind,
      Option.elimM, StateT.run_bind, simulateQ_bind, run_simHash]
    refine congrArg _ (funext fun z ↦ ?_)
    rcases z with ⟨_ | a, st'⟩
    · rfl
    · rfl

/-- **A budgeted query, simulated, is the charge of one counted query** when the simulation
answers the hash query `x` with `H x`. -/
theorem simHash_budgetedQuery (impl : QueryImpl GameSpec b) (H : Bytes → Digest)
    (himpl : ∀ x, simulateQ impl (liftM (HashSpec.query x) : OracleComp GameSpec Digest) =
      pure (H x))
    (budget : ℕ) (x : Bytes) :
    simHash (nx := nx) (ns := ns) impl (budgetedQuery budget x) = charge budget (countQuery H x) := by
  refine OptionT.ext (StateT.ext fun st ↦ ?_)
  rw [run_simHash, run_charge]
  unfold budgetedQuery
  have hget : StateT.run (get : OptionT (GameM nx ns) (SignState nx ns)).run st =
      pure (some st, st) := rfl
  rw [OptionT.run_bind, Option.elimM, StateT.run_bind, hget, simulateQ_bind, simulateQ_pure,
    pure_bind]
  by_cases hb : budget ≤ st.spent
  · have : ¬ ((countQuery H x).count = 0 ∨ st.spent + (countQuery H x).count ≤ budget) := by
      simp only [countQuery]; omega
    simp only [this, ↓reduceIte, Option.elim, hb]
    show (pure (none, st) : b _) = _
    rw [Nat.max_eq_left hb]
  · have : (countQuery H x).count = 0 ∨ st.spent + (countQuery H x).count ≤ budget := by
      simp only [countQuery]; omega
    simp only [this, ↓reduceIte, Option.elim, hb]
    have hrun : StateT.run (OptionT.run (do
        modify fun st : SignState nx ns ↦ { st with spent := st.spent + 1 }
        (liftM (hashQuery (nx := nx) (ns := ns) x) : OptionT (GameM nx ns) Digest))) st =
        (liftM (HashSpec.query x) : OracleComp GameSpec Digest) >>= fun d ↦
          pure (some d, { st with spent := st.spent + 1 }) := by
      simp [OptionT.run_bind, Option.elimM, hashQuery]
      rfl
    rw [hrun, simulateQ_bind, himpl, pure_bind, simulateQ_pure]
    rfl

/-! ## The budgeted run -/

/-- **The game's budgeted run of V_I, its oracle answering every hash query `x` with `H x`, is
V_I's counted run charged against the budget.** -/
theorem simulateQ_idealVerify_budgetedQuery (impl : QueryImpl GameSpec b) (H : Bytes → Digest)
    (himpl : ∀ x, simulateQ impl (liftM (HashSpec.query x) : OracleComp GameSpec Digest) =
      pure (H x))
    (budget : ℕ) (prog : Program) (ip : IdealProof) (fuel : ℕ) (s : NodeStatement)
    (st : SignState nx ns) :
    simulateQ impl (((idealVerify (budgetedQuery budget) prog ip fuel s).run).run st) =
      ((charge budget (idealVerify (countQuery H) prog ip fuel s)).run).run st := by
  rw [← run_simHash, idealVerify_natural (isMorphism_simHash impl),
    idealVerify_natural (isMorphism_charge budget)]
  simp only [simHash_budgetedQuery impl H himpl]

/-- **L16: the budgeted run is the `Id` run within the budget.** With the game's oracle simulated
by any `impl` answering every hash query `x` with `pure (H x)`, V_I's budgeted run from a state
`st` returns V_I's `Id` run with `H`, the state's `spent` advanced by V_I's query count, when the
count is `0` or `st.spent` plus the count is within the budget; otherwise it rejects, `spent` at
`max st.spent budget`. -/
theorem run_idealVerify_budgetedQuery (impl : QueryImpl GameSpec b) (H : Bytes → Digest)
    (himpl : ∀ x, simulateQ impl (liftM (HashSpec.query x) : OracleComp GameSpec Digest) =
      pure (H x))
    (budget : ℕ) (prog : Program) (ip : IdealProof) (fuel : ℕ) (s : NodeStatement)
    (st : SignState nx ns) :
    simulateQ impl (((idealVerify (budgetedQuery budget) prog ip fuel s).run).run st) =
      pure (if queryCount H prog ip fuel s = 0 ∨ st.spent + queryCount H prog ip fuel s ≤ budget
        then (some (Id.run (idealVerify (fun x ↦ (pure (H x) : Id Digest)) prog ip fuel s)),
          { st with spent := st.spent + queryCount H prog ip fuel s })
        else (none, { st with spent := max st.spent budget })) := by
  rw [simulateQ_idealVerify_budgetedQuery impl H himpl, run_charge, val_idealVerify_counted]
  rfl

/-- **L16, within the budget**: V_I's budgeted run is its `Id` run with `H`, `spent` advanced by
its query count. -/
theorem run_idealVerify_budgetedQuery_of_le (impl : QueryImpl GameSpec b) (H : Bytes → Digest)
    (himpl : ∀ x, simulateQ impl (liftM (HashSpec.query x) : OracleComp GameSpec Digest) =
      pure (H x))
    {budget : ℕ} {prog : Program} {ip : IdealProof} {fuel : ℕ} {s : NodeStatement}
    {st : SignState nx ns} (hb : st.spent + queryCount H prog ip fuel s ≤ budget) :
    simulateQ impl (((idealVerify (budgetedQuery budget) prog ip fuel s).run).run st) =
      pure (some (Id.run (idealVerify (fun x ↦ (pure (H x) : Id Digest)) prog ip fuel s)),
        { st with spent := st.spent + queryCount H prog ip fuel s }) := by
  rw [run_idealVerify_budgetedQuery impl H himpl]
  simp only [hb, or_true, ↓reduceIte]

/-- **The oracle of a fixed hash**: coins forwarded, every hash query `x` answered `H x`. -/
noncomputable def hashImplOf (H : Bytes → Digest) : QueryImpl GameSpec ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + (fun x ↦ pure (H x) : QueryImpl HashSpec ProbComp)

/-- The oracle of a fixed hash answers its hash queries. -/
theorem simulateQ_hashImplOf (H : Bytes → Digest) (x : Bytes) :
    simulateQ (hashImplOf H) (liftM (HashSpec.query x) : OracleComp GameSpec Digest) =
      pure (H x) := by
  change simulateQ _ (liftM (GameSpec.query (.inr x)) : OracleComp GameSpec Digest) = _
  rw [simulateQ_spec_query]
  rfl

end
end LeanVM.E2E
