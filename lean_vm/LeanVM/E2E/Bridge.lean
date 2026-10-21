/-
  LeanVM.E2E.Bridge

  The game-to-cache bridge: on every reachable outcome of the game, V_I's acceptance (its run
  against the game's budgeted hash) is the cache form of T4, its `Option` run answered by the
  game's final log.
-/

module

public import LeanVM.E2E.Rel
public import LeanVM.E2E.Engine
public import LeanVM.E2E.Knowledge

/-!
# From the game's run of V_I to the cache form

The game (`game`, `LeanVM.E2E.Statement`) runs V_I against `budgetedQuery`, a hash query of the
game's random oracle (`Rom.loggedRO`, lazily sampled over the ordered log of its fresh queries)
while fewer than `budget` were made, a failure past the budget. T4
(`aggregate_knowledge_cache`) reads V_I's acceptance in cache form,
`idealVerify (look ℓ) … = some true`, with every hash answered by the log `ℓ`.

**The bridge** (`game_accepted`). On every reachable outcome `(z, ℓ)` of the game, `z.accepted`
implies the cache form at the final log. A run of a V_I computation `x` against the game's
oracle from a state and a log only extends the log, and if it returns `some a`, the `Option`
run `x'` of the same computation by any lookup `L` extending the final log's returns `some a`
(`AnsRel L x x'`): every answer the run got is in its final log, and a run past the budget
returns `none`. `AnsRel L` holds of pure computations, is closed under `bind` (the log of the
first part is a prefix of the final one), and holds of `budgetedQuery x` against `L x`; so it
holds of V_I's two runs (`rel_idealVerify`). The game's final log is the log after V_I.

**T4 in the game** (`prEvent_game_accepted_le`): the probability that V_I accepts while some
root claim is not known under the final log is at most the sum of T1's, W6's, E5's and T3's
terms (`prEvent_game_aggregate_le`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom LeanVM.Protocol.EndToEnd.Blind LeanVM.Protocol.EndToEnd.Sound
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ}

/-! ## Runs against the game's oracle -/

/-- The run of a computation of `OptionT (GameM nx ns)` against the game's oracle, from the
signers' state `st` and the log `ℓ`. -/
noncomputable def runG {α : Type} (x : OptionT (GameM nx ns) α) (st : SignState nx ns) (ℓ : Log) :
    ProbComp ((Option α × SignState nx ns) × Log) :=
  (simulateQ gameImpl ((x.run).run st)).run ℓ

/-- The run of `pure`. -/
theorem runG_pure {α : Type} (a : α) (st : SignState nx ns) (ℓ : Log) :
    runG (pure a : OptionT (GameM nx ns) α) st ℓ = pure ((some a, st), ℓ) := by
  simp [runG]

/-- The run of a bind: the first part's run, then, at `some a`, the continuation's from the
state and log it reached; at `none`, nothing more. -/
theorem runG_bind {α β : Type} (x : OptionT (GameM nx ns) α) (f : α → OptionT (GameM nx ns) β)
    (st : SignState nx ns) (ℓ : Log) :
    runG (x >>= f) st ℓ = runG x st ℓ >>= fun q ↦ match q.1.1 with
      | none => pure ((none, q.1.2), q.2)
      | some a => runG (f a) q.1.2 q.2 := by
  simp only [runG, OptionT.run_bind, Option.elimM, StateT.run_bind, simulateQ_bind]
  refine bind_congr fun q ↦ ?_
  rcases q with ⟨⟨_ | a, st'⟩, ℓ'⟩ <;> simp

/-- A point of the run of a bind comes from a point of the first part's run. -/
theorem mem_support_runG_bind {α β : Type} {x : OptionT (GameM nx ns) α}
    {f : α → OptionT (GameM nx ns) β} {st : SignState nx ns} {ℓ : Log}
    {p : (Option β × SignState nx ns) × Log} (hp : p ∈ support (runG (x >>= f) st ℓ)) :
    ∃ q ∈ support (runG x st ℓ), (q.1.1 = none ∧ p = ((none, q.1.2), q.2)) ∨
      ∃ a, q.1.1 = some a ∧ p ∈ support (runG (f a) q.1.2 q.2) := by
  rw [runG_bind, mem_support_bind_iff] at hp
  obtain ⟨q, hq, hp⟩ := hp
  refine ⟨q, hq, ?_⟩
  rcases hq' : q.1.1 with _ | a
  · rw [hq'] at hp
    exact Or.inl ⟨rfl, by simpa using hp⟩
  · rw [hq'] at hp
    exact Or.inr ⟨a, rfl, hp⟩

/-- A hash query of the game's oracle extends the log, which answers it. -/
theorem mem_support_gameImpl_hash {x : Bytes} {ℓ : Log} {p : Digest × Log}
    (hp : p ∈ support ((gameImpl (.inr x)).run ℓ)) : ℓ <+: p.2 ∧ look p.2 x = some p.1 := by
  rw [gameImpl_isLazySampler (.inr x) ℓ] at hp
  simp only [gameLookup, gameRecord] at hp
  rcases h : look ℓ x with _ | u
  · rw [h] at hp
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨u, -, rfl⟩ := hp
    refine ⟨List.prefix_append _ _, ?_⟩
    change logLookup (ℓ ++ [(x, u)]) x = some u
    simp [logLookup_append_singleton ℓ x x u h]
  · rw [h] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨List.prefix_refl _, h⟩

/-- **The answered relation** at the lookup `L`: every run of `x` against the game's oracle
extends its log, and if the final log's lookup is extended by `L`, a result `some a` of the run
is the `Option` run `x'`'s. -/
def AnsRel (L : Bytes → Option Digest) {α : Type} (x : OptionT (GameM nx ns) α)
    (x' : Option α) : Prop :=
  ∀ (st : SignState nx ns) (ℓ : Log), ∀ p ∈ support (runG x st ℓ),
    ℓ <+: p.2 ∧ (LookSub (look p.2) L → OptLE p.1.1 x')

/-- `AnsRel` holds of `pure`. -/
theorem ansRel_pure (L : Bytes → Option Digest) {α : Type} (a : α) :
    AnsRel (nx := nx) (ns := ns) L (pure a) (pure a) := by
  intro st ℓ p hp
  rw [runG_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  exact ⟨List.prefix_refl _, fun _ ↦ optLE_pure a⟩

/-- `AnsRel` is closed under `bind`. -/
theorem ansRel_bind (L : Bytes → Option Digest) {α β : Type} (x : OptionT (GameM nx ns) α)
    (x' : Option α) (f : α → OptionT (GameM nx ns) β) (f' : α → Option β) (hx : AnsRel L x x')
    (hf : ∀ a, AnsRel L (f a) (f' a)) : AnsRel L (x >>= f) (x' >>= f') := by
  intro st ℓ p hp
  obtain ⟨q, hq, hpq⟩ := mem_support_runG_bind hp
  obtain ⟨hℓq, hxq⟩ := hx st ℓ q hq
  rcases hpq with ⟨-, rfl⟩ | ⟨a, ha, hp'⟩
  · exact ⟨hℓq, fun _ b hb ↦ absurd hb (by simp)⟩
  · obtain ⟨hqp, hfp⟩ := hf a q.1.2 q.2 p hp'
    refine ⟨hℓq.trans hqp, fun hL ↦ ?_⟩
    have hx' := hxq ((lookSub_of_prefix hqp).trans hL) a ha
    intro b hb
    rw [hx']
    exact hfp hL b hb

/-- A budgeted query within the budget: one hash query, the count raised. -/
theorem run_budgetedQuery_of_lt {budget : ℕ} {x : Bytes} {st : SignState nx ns}
    (hb : ¬ budget ≤ st.spent) :
    ((budgetedQuery budget x : OptionT (GameM nx ns) Digest).run).run st =
      (fun d ↦ (some d, { st with spent := st.spent + 1 })) <$>
        (liftM (GameSpec.query (.inr x)) : OracleComp GameSpec Digest) := by
  unfold budgetedQuery
  simp [hb, Option.elimM, OptionT.run_bind, run_get_optionT, run_modify_optionT]
  change (fun p ↦ (some p.1, p.2)) <$> ((liftM (liftM (GameSpec.query (.inr x)) :
    OracleComp GameSpec Digest) : GameM nx ns Digest).run _) = _
  rw [OracleComp.liftM_run_StateT]
  simp

/-- A budgeted query past the budget fails. -/
theorem run_budgetedQuery_of_le {budget : ℕ} {x : Bytes} {st : SignState nx ns}
    (hb : budget ≤ st.spent) :
    ((budgetedQuery budget x : OptionT (GameM nx ns) Digest).run).run st = pure (none, st) := by
  unfold budgetedQuery
  simp [hb, Option.elimM, OptionT.run_bind, run_get_optionT]

/-- `AnsRel` holds of a budgeted query against the lookup's answer: past the budget the run
returns `none`; otherwise its answer is the final log's. -/
theorem ansRel_budgetedQuery (L : Bytes → Option Digest) (budget : ℕ) (x : Bytes) :
    AnsRel (nx := nx) (ns := ns) L (budgetedQuery budget x) (L x) := by
  intro st ℓ p hp
  unfold runG at hp
  by_cases hb : budget ≤ st.spent
  · rw [run_budgetedQuery_of_le hb] at hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨List.prefix_refl _, fun _ b hb' ↦ absurd hb' (by simp)⟩
  · rw [run_budgetedQuery_of_lt hb, simulateQ_map, StateT.run_map, simulateQ_spec_query,
      support_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨hpre, hlook⟩ := mem_support_gameImpl_hash hq
    exact ⟨hpre, fun hL b hb' ↦ by
      simp only [Option.some.injEq] at hb'
      subst hb'
      exact hL _ _ hlook⟩

/-- **`AnsRel` holds of V_I's two runs**: the game's, against the budgeted hash, and the
`Option` run by `L`. -/
theorem ansRel_idealVerify (L : Bytes → Option Digest) (budget : ℕ) (prog : Program)
    (ip : IdealProof) (fuel : ℕ) (s : NodeStatement) :
    AnsRel (nx := nx) (ns := ns) L (idealVerify (budgetedQuery budget) prog ip fuel s)
      (idealVerify L prog ip fuel s) :=
  rel_idealVerify (fun x x' ↦ AnsRel L x x') (ansRel_pure L) (ansRel_bind L) _ _
    (ansRel_budgetedQuery L budget) prog ip fuel s

/-- A point of a run of a bind of the game's monad comes from a point of the first part's run. -/
theorem mem_support_run_bind {α β : Type} {x : GameM nx ns α} {f : α → GameM nx ns β}
    {st : SignState nx ns} {ℓ : Log} {p : (β × SignState nx ns) × Log}
    (hp : p ∈ support ((simulateQ gameImpl ((x >>= f).run st)).run ℓ)) :
    ∃ q ∈ support ((simulateQ gameImpl (x.run st)).run ℓ),
      p ∈ support ((simulateQ gameImpl ((f q.1.1).run q.1.2)).run q.2) := by
  simpa only [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] using hp

variable [Sphincs.Params]

/-- **The game-to-cache bridge.** On every reachable outcome `(z, ℓ)` of the game, V_I's
acceptance is its acceptance in cache form at the final log: its `Option` run, every hash
answered by `look ℓ`, returns `some true`. -/
theorem game_accepted {guest : Program} {fuel budget : ℕ} {A : GameAdversary nx ns}
    {z : GameOutcome nx ns × Log} (hz : z ∈ support (game guest fuel budget A))
    (ha : z.1.accepted = true) :
    idealVerify (look z.2) guest z.1.proof fuel z.1.statement = some true := by
  rw [game_eq] at hz
  unfold gameComp at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨⟨out, st⟩, ℓ⟩, hq, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨⟨⟨keys, st₁⟩, ℓ₁⟩, -, hq⟩ := mem_support_run_bind hq
  obtain ⟨⟨⟨⟨s, ip⟩, st₂⟩, ℓ₂⟩, -, hq⟩ := mem_support_run_bind hq
  obtain ⟨⟨⟨v, st₃⟩, ℓ₃⟩, hv, hq⟩ := mem_support_run_bind hq
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hq
  obtain ⟨⟨h₁, -⟩, h₃⟩ := hq
  subst h₁ h₃
  simp only at ha ⊢
  have h := (ansRel_idealVerify (look _) budget guest ip fuel s st₂ ℓ₂ _ hv).2
    (LookSub.refl _)
  cases v with
  | none => simp at ha
  | some b =>
    simp only [Option.getD_some] at ha
    subst ha
    exact h true rfl

/-- **T4 in the game, from the game's run of V_I.** For a game of the deployed guest with at
most `Q` hash queries, V_I accepting while some claim of the root statement is not known under
the final log has probability at most the sum of T1's, W6's, E5's and T3's terms, if the guest's
open callees are sound over every oracle model of every log. -/
theorem prEvent_game_accepted_le
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp Guest.guest fuel budget A) IsHash Q) :
    Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧
        ¬ ClaimsKnown z.2 z.1.statement] ≤
      Q * (εLean + failBound leanVmSeeds Q) + Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) +
        Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) + Q * (Q + 1) / 2 ^ 193 :=
  le_trans (prEvent_mono_of_support _ _ _ fun _ hz h ↦ ⟨game_accepted hz h.1, h.2⟩)
    (prEvent_game_aggregate_le hG fuel budget A Q hQ)

end

end LeanVM.E2E
