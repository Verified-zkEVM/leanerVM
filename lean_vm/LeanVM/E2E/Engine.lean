/-
  LeanVM.E2E.Engine

  The potential engine for the end-to-end game: the game's oracle, coins forwarded and the hash
  lazily sampled over the ordered log, is a lazy sampler, so a potential on logs bounds the
  game's events; and the game's query bound from its parts.
-/

module

public import LeanVM.E2E.Statement

/-!
# The game's engine

The game (`game`, `LeanVM.E2E.Statement`) runs `gameComp : OracleComp GameSpec _` against
`coinImpl + Rom.loggedRO`: coins forwarded, every hash query (the adversary's, the honest
signers', V_I's) answered by one random oracle lazily sampled over the ordered log of its fresh
queries (decision E2E-1: no hidden queries). This module makes the potential engine of
`LeanVM.Protocol.ToVCVio.Rom.Potential` apply to it.

**The sampler** (`gameImpl_isLazySampler`). `coinImpl + loggedRO` is a lazy sampler for
`GameSpec`: a coin query is never answered by the state (`gameLookup` is `none`) and records
nothing (`gameRecord` is the identity); a hash query looks the log up and appends a fresh answer.

**Free queries** (`lintegral_run_le_of_budgetedP`). The engine counts every query; here a coin
query leaves the state, so every potential, unchanged. The budgeted bound is restated for a
query bound that counts only the queries of a predicate `p` (`IsQueryBoundP`), the other fresh
queries being required not to raise the potential in expectation. Its constant and length-capped
forms (`prEvent_run_le_of_freshStepP`, `prEvent_run_le_of_freshStepBelowP`) follow.

**The game's bound** (`prEvent_game_le`, `prEvent_game_le_of_freshStepBelow`). For a potential
`Φ` on logs rising by at most `δ` per fresh hash query (at logs shorter than `N ≥ Q`, in the
capped form), an event of the game's outcome and final log that forces `1 ≤ Φ` on reachable
outcomes has probability at most `Φ [] + Q · δ`, `Q` a bound on the hash queries of `gameComp`
(`IsQueryBoundP gameComp IsHash Q`); a total bound, coins included, is one
(`isQueryBoundP_of_isTotalQueryBound`).

**V_I queries only through its hash** (`closed_idealVerify`). For every monad and every
predicate on its computations closed under `pure` and `bind` and holding of every hash query,
the predicate holds of `idealVerify`: its definition, unfolded, is binds, branches and loops
over its hash. This replaces a parametricity argument, which Lean cannot make internally.

**The query bound** (`isQueryBoundP_gameComp`). A computation of the game's monad *costs* `c`
(`Costs c`) if it makes at most `c` hash queries from every state. If every honest key
generation and signature makes at most `cxk`, `csk`, `cxs`, `css` hash queries, and the adversary
at most `qH` hash queries, `sX` leanXMSS and `sS` leanSPHINCS signing requests (coins
uncounted), then `gameComp` makes at most

  `nx · cxk + ns · csk + (qH + sX · cxs + sS · css) + budget`

hash queries. V_I's are at most the budget left (`isQueryBoundP_idealVerify`): it *spends* its
budget (`Spends`: followed by a continuation making at most `N` plus the budget left, it makes at
most `N` plus the budget left at its start), because `budgetedQuery` makes one query exactly
when it counts one in the state (`spends_budgetedQuery`) and spending is closed under `pure` and
`bind`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom OracleSpec OracleComp MeasureTheory
open scoped ENNReal

@[expose] public section

/-! ## The engine with free queries -/

section Free

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}
  [∀ t, SampleableType (spec.Range t)] [∀ t, Fintype (spec.Range t)]
  {σ : Type} {lookup : σ → (t : spec.Domain) → Option (spec.Range t)}
  {record : σ → (t : spec.Domain) → spec.Range t → σ}

/-- **The budgeted potential bound, counting the queries of `p` only.** A fresh `p`-query
lowers the budget by one and does not raise the potential in expectation; a fresh query outside
`p` keeps the budget and does not raise the potential in expectation either; more budget never
lowers the potential. Then a computation with at most `Q` queries of `p`, run against the lazy
sampler from `s₀`, has expected payoff at most `Φ Q s₀` for every payoff bounded on reachable
outcomes by `Φ 0` of the final state. -/
theorem lintegral_run_le_of_budgetedP {impl : QueryImpl spec (StateT σ ProbComp)}
    (himpl : IsLazySampler lookup record impl) (p : ι → Prop) [DecidablePred p] {α : Type}
    [MeasurableSpace (α × σ)] [DiscreteMeasurableSpace (α × σ)] {Φ : ℕ → σ → ℝ≥0∞}
    (hfresh : ∀ (n : ℕ) (s : σ) (t : spec.Domain), p t → lookup s t = none →
      (∑ u, Φ n (record s t u)) / Fintype.card (spec.Range t) ≤ Φ (n + 1) s)
    (hfree : ∀ (n : ℕ) (s : σ) (t : spec.Domain), ¬ p t → lookup s t = none →
      (∑ u, Φ n (record s t u)) / Fintype.card (spec.Range t) ≤ Φ n s)
    (hmono : ∀ (n : ℕ) (s : σ), Φ n s ≤ Φ (n + 1) s)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsQueryBoundP oa p Q) (s₀ : σ) (g : α × σ → ℝ≥0∞)
    (hg : ∀ z ∈ support ((simulateQ impl oa).run s₀), g z ≤ Φ 0 z.2) :
    ∫⁻ z, g z ∂𝒟[(simulateQ impl oa).run s₀] ≤ Φ Q s₀ := by
  have hle : ∀ (s : σ) {m n : ℕ}, m ≤ n → Φ m s ≤ Φ n s := fun s _ _ h ↦
    monotone_nat_of_le_succ (f := fun n ↦ Φ n s) (fun n ↦ hmono n s) h
  induction oa using OracleComp.inductionOn generalizing Q s₀ with
  | pure x =>
    rw [simulateQ_pure, StateT.run_pure] at hg ⊢
    rw [evalDist_pure, lintegral_dirac]
    exact (hg _ (by simp)).trans (hle s₀ (Nat.zero_le Q))
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hQ
    obtain ⟨hpos, hrest⟩ := hQ
    rw [simulateQ_query_bind, StateT.run_bind] at hg ⊢
    simp only [OracleQuery.input_query, monadLift_self] at hg ⊢
    change ∫⁻ z, g z ∂𝒟[(impl t).run s₀ >>= fun p ↦ (simulateQ impl (mx p.1)).run p.2] ≤ _
    change ∀ z ∈ support ((impl t).run s₀ >>= fun p ↦ (simulateQ impl (mx p.1)).run p.2), _
      at hg
    rw [himpl t s₀] at hg ⊢
    -- The budget after this query.
    set Q' := if p t then Q - 1 else Q with hQ'
    have hstep : ∀ s, s = s₀ → lookup s t = none →
        (∑ u, Φ Q' (record s t u)) / Fintype.card (spec.Range t) ≤ Φ Q s := by
      intro s hs hn
      subst hs
      by_cases hp : p t
      · obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 :=
          ⟨Q - 1, by have := hpos.resolve_left (not_not.mpr hp); omega⟩
        simp only [hQ', hp, ↓reduceIte, Nat.add_sub_cancel]
        exact hfresh n s t hp hn
      · simp only [hQ', hp, ↓reduceIte]
        exact hfree Q s t hp hn
    rcases hs : lookup s₀ t with _ | u
    · simp only [hs, bind_assoc, pure_bind] at hg ⊢
      let _ : MeasurableSpace (spec.Range t) := ⊤
      rw [lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete,
        SampleableType.evalDist_uniformSample, ProbabilityTheory.lintegral_uniformOn_univ]
      calc (∑ u, ∫⁻ z, g z ∂𝒟[(simulateQ impl (mx u)).run (record s₀ t u)])
            / Fintype.card (spec.Range t)
          ≤ (∑ u, Φ Q' (record s₀ t u)) / Fintype.card (spec.Range t) := by
            gcongr with u
            refine ih u Q' (hrest u) _ fun z hz ↦ hg z ?_
            exact (mem_support_bind_iff _ _ _).mpr ⟨u, mem_support_uniformSample _, hz⟩
        _ ≤ Φ Q s₀ := hstep s₀ rfl hs
    · simp only [hs, pure_bind] at hg ⊢
      refine (ih u Q' (hrest u) s₀ hg).trans (hle s₀ ?_)
      simp only [hQ']
      split <;> omega

/-- **Markov at one, counting the queries of `p` only, budgeted form.** -/
theorem prEvent_run_le_of_budgetedP {impl : QueryImpl spec (StateT σ ProbComp)}
    (himpl : IsLazySampler lookup record impl) (p : ι → Prop) [DecidablePred p] {α : Type}
    {Φ : ℕ → σ → ℝ≥0∞}
    (hfresh : ∀ (n : ℕ) (s : σ) (t : spec.Domain), p t → lookup s t = none →
      (∑ u, Φ n (record s t u)) / Fintype.card (spec.Range t) ≤ Φ (n + 1) s)
    (hfree : ∀ (n : ℕ) (s : σ) (t : spec.Domain), ¬ p t → lookup s t = none →
      (∑ u, Φ n (record s t u)) / Fintype.card (spec.Range t) ≤ Φ n s)
    (hmono : ∀ (n : ℕ) (s : σ), Φ n s ≤ Φ (n + 1) s)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsQueryBoundP oa p Q) (s₀ : σ) (ev : α → σ → Prop)
    (hev : ∀ z ∈ support ((simulateQ impl oa).run s₀), ev z.1 z.2 → 1 ≤ Φ 0 z.2) :
    Pr{let z ← (simulateQ impl oa).run s₀}[ev z.1 z.2] ≤ Φ Q s₀ := by
  classical
  let _ : MeasurableSpace (α × σ) := ⊤
  rw [prEvent_eq_evalDist_of_discrete _ (fun z : α × σ ↦ ev z.1 z.2),
    ← lintegral_indicator_one MeasurableSet.of_discrete]
  refine lintegral_run_le_of_budgetedP himpl p hfresh hfree hmono oa Q hQ s₀ _ fun z hz ↦ ?_
  by_cases hz' : ev z.1 z.2
  · simpa [Set.indicator_of_mem (show z ∈ {z : α × σ | ev z.1 z.2} from hz')]
      using hev z hz hz'
  · simp [Set.indicator_of_notMem (show z ∉ {z : α × σ | ev z.1 z.2} from hz')]

/-- **Markov at one, counting the queries of `p` only.** If `Φ` rises by at most `δ` per fresh
`p`-query and not at all, in expectation, per fresh query outside `p`, an event that forces
`1 ≤ Φ` of the final state has probability at most `Φ s₀ + Q · δ` after a run with at most `Q`
queries of `p`. -/
theorem prEvent_run_le_of_freshStepP {impl : QueryImpl spec (StateT σ ProbComp)}
    (himpl : IsLazySampler lookup record impl) (p : ι → Prop) [DecidablePred p] {α : Type}
    {Φ : σ → ℝ≥0∞} {δ : ℝ≥0∞}
    (hfresh : ∀ (s : σ) (t : spec.Domain), p t → lookup s t = none →
      (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s + δ)
    (hfree : ∀ (s : σ) (t : spec.Domain), ¬ p t → lookup s t = none →
      (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsQueryBoundP oa p Q) (s₀ : σ) (ev : α → σ → Prop)
    (hev : ∀ z ∈ support ((simulateQ impl oa).run s₀), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ impl oa).run s₀}[ev z.1 z.2] ≤ Φ s₀ + Q * δ := by
  refine prEvent_run_le_of_budgetedP (Φ := fun n s ↦ Φ s + n * δ) himpl p ?_ ?_ ?_ oa Q hQ s₀ ev
    fun z hz h ↦ by simpa using hev z hz h
  · intro n s t hp hn
    rw [sum_add_const_div_card]
    calc (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) + n * δ
        ≤ Φ s + δ + n * δ := by gcongr; exact hfresh s t hp hn
      _ = Φ s + ((n + 1 : ℕ) : ℝ≥0∞) * δ := by
        rw [add_assoc, Nat.cast_succ, add_one_mul, add_comm δ]
  · intro n s t hp hn
    rw [sum_add_const_div_card]
    gcongr
    exact hfree s t hp hn
  · intro n s
    gcongr
    exact_mod_cast Nat.le_succ n

/-- **Markov at one, counting the queries of `p` only, length-capped form.** For a state size
that a fresh `p`-query raises by at most one and another fresh query leaves, a step bound at
`p`-queries needed only at states of size below `N` bounds an event that forces `1 ≤ Φ` by
`Φ s₀ + Q · δ`, when `size s₀ + Q ≤ N`. -/
theorem prEvent_run_le_of_freshStepBelowP {impl : QueryImpl spec (StateT σ ProbComp)}
    (himpl : IsLazySampler lookup record impl) (p : ι → Prop) [DecidablePred p] {α : Type}
    {Φ : σ → ℝ≥0∞} {δ : ℝ≥0∞} (size : σ → ℕ) (N : ℕ)
    (hsize : ∀ s t u, p t → lookup s t = none → size (record s t u) ≤ size s + 1)
    (hsize' : ∀ s t u, ¬ p t → lookup s t = none → size (record s t u) ≤ size s)
    (hfresh : ∀ (s : σ) (t : spec.Domain), size s < N → p t → lookup s t = none →
      (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s + δ)
    (hfree : ∀ (s : σ) (t : spec.Domain), ¬ p t → lookup s t = none →
      (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsQueryBoundP oa p Q) (s₀ : σ)
    (hs₀ : size s₀ + Q ≤ N) (ev : α → σ → Prop)
    (hev : ∀ z ∈ support ((simulateQ impl oa).run s₀), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ impl oa).run s₀}[ev z.1 z.2] ≤ Φ s₀ + Q * δ := by
  have h := prEvent_run_le_of_budgetedP
    (Φ := fun n s ↦ if size s + n ≤ N then Φ s + n * δ else ⊤) himpl p ?_ ?_ ?_ oa Q hQ s₀ ev
    fun z hz h ↦ by
      split_ifs
      · simpa using hev z hz h
      · exact le_top
  · simpa only [ite_eq_left hs₀] using h
  · intro n s t hp hs
    by_cases hN : size s + (n + 1) ≤ N
    · rw [ite_eq_left hN]
      calc (∑ u, (if size (record s t u) + n ≤ N then Φ (record s t u) + n * δ else ⊤))
            / Fintype.card (spec.Range t)
          = (∑ u, (Φ (record s t u) + n * δ)) / Fintype.card (spec.Range t) := by
            congr 1
            refine Finset.sum_congr rfl fun u _ ↦ ite_eq_left ?_
            have := hsize s t u hp hs
            omega
        _ = (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) + n * δ :=
            sum_add_const_div_card t _ _
        _ ≤ Φ s + δ + n * δ := by gcongr; exact hfresh s t (by omega) hp hs
        _ = Φ s + ((n + 1 : ℕ) : ℝ≥0∞) * δ := by
            rw [add_assoc, Nat.cast_succ, add_one_mul, add_comm δ]
    · rw [ite_eq_right hN]
      exact le_top
  · intro n s t hp hs
    by_cases hN : size s + n ≤ N
    · rw [ite_eq_left hN]
      calc (∑ u, (if size (record s t u) + n ≤ N then Φ (record s t u) + n * δ else ⊤))
            / Fintype.card (spec.Range t)
          = (∑ u, (Φ (record s t u) + n * δ)) / Fintype.card (spec.Range t) := by
            congr 1
            refine Finset.sum_congr rfl fun u _ ↦ ite_eq_left ?_
            have := hsize' s t u hp hs
            omega
        _ = (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) + n * δ :=
            sum_add_const_div_card t _ _
        _ ≤ Φ s + n * δ := by gcongr; exact hfree s t hp hs
    · rw [ite_eq_right hN]
      exact le_top
  · intro n s
    by_cases hN : size s + (n + 1) ≤ N
    · rw [ite_eq_left hN, ite_eq_left (by omega)]
      gcongr
      exact_mod_cast Nat.le_succ n
    · rw [ite_eq_right hN]
      exact le_top

end Free

/-- A total query bound bounds the queries of any predicate. -/
theorem isQueryBoundP_of_isTotalQueryBound {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : ι → Prop) [DecidablePred p] {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : IsQueryBoundP oa p n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr h.1, fun u ↦ (ih u (h.2 u)).mono ?_⟩
    split <;> omega

/-! ## The game's oracle as a lazy sampler -/

/-- The game's queries' answers are finite. -/
noncomputable instance gameRangeFintype : ∀ t : GameSpec.Domain, Fintype (GameSpec.Range t)
  | .inl n => (inferInstance : Fintype (Fin (n + 1)))
  | .inr _ => (inferInstance : Fintype Digest)

/-- The game's queries' answers are sampled uniformly: a coin query as VCVio's `$[0..n]`. -/
noncomputable instance gameRangeSampleable :
    ∀ t : GameSpec.Domain, SampleableType (GameSpec.Range t)
  | .inl n => SampleableType.Fin n
  | .inr _ => (inferInstance : SampleableType Digest)

/-- The game's oracle state's answers: none to a coin query, the log's to a hash query. -/
def gameLookup (ℓ : Log) : (t : GameSpec.Domain) → Option (GameSpec.Range t)
  | .inl _ => none
  | .inr x => look ℓ x

/-- The game's oracle's recording: nothing for a coin, the fresh entry for a hash query. -/
def gameRecord (ℓ : Log) : (t : GameSpec.Domain) → GameSpec.Range t → Log
  | .inl _, _ => ℓ
  | .inr x, u => ℓ ++ [(x, u)]

/-- The game's oracle. -/
noncomputable abbrev gameImpl : QueryImpl GameSpec (StateT Log ProbComp) :=
  coinImpl + (Rom.loggedRO : QueryImpl HashSpec (StateT Log ProbComp))

/-- **The game's oracle is a lazy sampler**: coins forwarded, the hash lazily sampled over the
log. -/
theorem gameImpl_isLazySampler : IsLazySampler gameLookup gameRecord gameImpl := by
  rintro (n | x) ℓ
  · change (coinImpl n).run ℓ = _
    simp only [gameLookup, gameRecord]
    simp [coinImpl]
    rfl
  · change (Rom.loggedRO x).run ℓ = _
    rw [loggedRO_isLazySampler x ℓ]
    simp only [gameLookup, gameRecord, look]
    rcases logLookup ℓ x with _ | u
    · rfl
    · rfl

/-- The hash queries of the game. -/
def IsHash : GameSpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

/-- Hash queries are decidable. -/
instance : DecidablePred IsHash
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- A coin query leaves every function of the log unchanged in expectation. -/
theorem sum_gameRecord_coin (Φ : Log → ℝ≥0∞) (ℓ : Log) (n : ℕ) :
    (∑ u, Φ (gameRecord ℓ (.inl n) u)) / Fintype.card (GameSpec.Range (.inl n)) = Φ ℓ := by
  simp only [gameRecord, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_comm, ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)]

section Game

variable {nx ns : ℕ} [Sphincs.Params]

/-- The game is the run of `gameComp` against the game's oracle from the empty log. -/
theorem game_eq (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    game guest fuel budget A = (simulateQ gameImpl (gameComp guest fuel budget A)).run [] := rfl

/-- **The game's potential bound.** If `Φ` rises by at most `δ` per fresh hash query, an event of
the game's outcome and final log that forces `1 ≤ Φ` on reachable outcomes has probability at
most `Φ [] + Q · δ`, `Q` a bound on `gameComp`'s hash queries. -/
theorem prEvent_game_le {Φ : Log → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LogFreshStepBound Φ δ)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q)
    (ev : GameOutcome nx ns → Log → Prop)
    (hev : ∀ z ∈ support (game guest fuel budget A), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← game guest fuel budget A}[ev z.1 z.2] ≤ Φ [] + Q * δ := by
  rw [game_eq] at hev ⊢
  refine prEvent_run_le_of_freshStepP gameImpl_isLazySampler IsHash ?_ ?_ _ Q hQ [] ev hev
  · rintro ℓ (n | x) hp hn
    · exact absurd hp id
    · exact hΦ ℓ x hn
  · rintro ℓ (n | x) hp _
    · exact (sum_gameRecord_coin Φ ℓ n).le
    · exact absurd trivial hp

/-- **The game's potential bound, length-capped form.** As `prEvent_game_le`, with the step
bound needed only at logs shorter than `N ≥ Q`. -/
theorem prEvent_game_le_of_freshStepBelow {Φ : Log → ℝ≥0∞} {δ : ℝ≥0∞} (N : ℕ)
    (hΦ : ∀ (ℓ : Log) (t : Bytes), ℓ.length < N → t ∉ ℓ.map Prod.fst →
      (∑ u, Φ (ℓ ++ [(t, u)])) / Fintype.card Digest ≤ Φ ℓ + δ)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) (hN : Q ≤ N)
    (ev : GameOutcome nx ns → Log → Prop)
    (hev : ∀ z ∈ support (game guest fuel budget A), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← game guest fuel budget A}[ev z.1 z.2] ≤ Φ [] + Q * δ := by
  rw [game_eq] at hev ⊢
  refine prEvent_run_le_of_freshStepBelowP gameImpl_isLazySampler IsHash List.length N ?_ ?_ ?_
    ?_ _ Q hQ [] (by simpa using hN) ev hev
  · rintro ℓ (n | x) u _ _ <;> simp [gameRecord]
  · rintro ℓ (n | x) u hp _
    · simp [gameRecord]
    · exact absurd trivial hp
  · rintro ℓ (n | x) hN' hp hn
    · exact absurd hp id
    · exact hΦ ℓ x hN' ((logLookup_eq_none_iff ℓ x).mp hn)
  · rintro ℓ (n | x) hp _
    · exact (sum_gameRecord_coin Φ ℓ n).le
    · exact absurd trivial hp

/-- **The game's potential bound, for a total query bound** (coins included). -/
theorem prEvent_game_le_of_total {Φ : Log → ℝ≥0∞} {δ : ℝ≥0∞} (hΦ : LogFreshStepBound Φ δ)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsTotalQueryBound (gameComp guest fuel budget A) Q)
    (ev : GameOutcome nx ns → Log → Prop)
    (hev : ∀ z ∈ support (game guest fuel budget A), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← game guest fuel budget A}[ev z.1 z.2] ≤ Φ [] + Q * δ :=
  prEvent_game_le hΦ guest fuel budget A Q (isQueryBoundP_of_isTotalQueryBound _ hQ) ev hev

/-- **The game's potential bound, length-capped form, for a total query bound** (coins
included). -/
theorem prEvent_game_le_of_freshStepBelow_of_total {Φ : Log → ℝ≥0∞} {δ : ℝ≥0∞} (N : ℕ)
    (hΦ : ∀ (ℓ : Log) (t : Bytes), ℓ.length < N → t ∉ ℓ.map Prod.fst →
      (∑ u, Φ (ℓ ++ [(t, u)])) / Fintype.card Digest ≤ Φ ℓ + δ)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsTotalQueryBound (gameComp guest fuel budget A) Q) (hN : Q ≤ N)
    (ev : GameOutcome nx ns → Log → Prop)
    (hev : ∀ z ∈ support (game guest fuel budget A), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← game guest fuel budget A}[ev z.1 z.2] ≤ Φ [] + Q * δ :=
  prEvent_game_le_of_freshStepBelow N hΦ guest fuel budget A Q
    (isQueryBoundP_of_isTotalQueryBound _ hQ) hN ev hev

end Game

/-! ## Computations that query only through their hash

`G` is a predicate on the computations of a monad, closed under `pure` and `bind`; `H` a hash
every query of which satisfies `G`. Then `G` holds of every computation V_I makes with `H`.
-/

section Closed
variable {m : Type → Type} [Monad m] [LawfulMonad m] (G : ∀ {α : Type}, m α → Prop)
  (hpure : ∀ {α : Type} (a : α), G (pure a))
  (hbind : ∀ {α β : Type} (x : m α) (f : α → m β), G x → (∀ a, G (f a)) → G (x >>= f))
include hpure hbind

/-- A closed predicate holds of a map. -/
theorem closed_map {α β : Type} (f : α → β) (x : m α) (hx : G x) : G (f <$> x) := by
  rw [map_eq_bind_pure_comp]; exact hbind _ _ hx fun _ ↦ hpure _

/-- A closed predicate holds of a `mapM` of computations it holds of. -/
theorem closed_mapM {α β : Type} (f : α → m β) (hf : ∀ a, G (f a)) :
    ∀ l : List α, G (l.mapM f)
  | [] => hpure _
  | a :: l => by
    rw [List.mapM_cons]
    exact hbind _ _ (hf a) fun _ ↦ hbind _ _ (closed_mapM f hf l) fun _ ↦ hpure _

omit [LawfulMonad m] in
/-- A closed predicate holds of an `allM` of computations it holds of. -/
theorem closed_allM {α : Type} (f : α → m Bool) (hf : ∀ a, G (f a)) :
    ∀ l : List α, G (l.allM f)
  | [] => by rw [List.allM_nil]; exact hpure _
  | a :: l => by
    rw [List.allM_cons]
    exact hbind _ _ (hf a) fun b ↦ by
      cases b
      · exact hpure _
      · exact closed_allM f hf l

omit [LawfulMonad m] in
/-- A closed predicate holds of a `for` loop over a list whose body it holds of. -/
theorem closed_forIn {α β : Type} (f : α → β → m (ForInStep β)) (hf : ∀ a b, G (f a b)) :
    ∀ (l : List α) (b : β), G (forIn l b f)
  | [], _ => hpure _
  | a :: l, b => by
    rw [List.forIn_cons]
    exact hbind _ _ (hf a b) fun s ↦ by
      cases s
      · exact hpure _
      · exact closed_forIn f hf l _

variable (H : Bytes → m Digest) (hH : ∀ x, G (H x))
include hH

/-- A closed predicate holds of a Merkle root computed with the hash. -/
theorem closed_rootOfLevelM : ∀ (k : ℕ) (level : List Digest), G (rootOfLevelM H k level)
  | 0, _ => hpure _
  | k + 1, _ =>
    hbind _ _ (closed_mapM G hpure hbind _ (fun _ ↦ hH _) _) fun _ ↦ closed_rootOfLevelM k _

omit [LawfulMonad m] in
/-- A closed predicate holds of a node of a partial tree computed with the hash. -/
theorem closed_pNodeM (P : PWord) : ∀ (k j : ℕ), G (pNodeM H P k j)
  | 0, j => by
    unfold pNodeM
    split
    · exact hpure _
    · exact hH _
  | k + 1, j => by
    unfold pNodeM
    split
    · exact hpure _
    · exact hbind _ _ (closed_pNodeM P k _) fun _ ↦ hbind _ _ (closed_pNodeM P k _) fun _ ↦ hH _

omit [LawfulMonad m] in
/-- A closed predicate holds of V_I's table check. -/
theorem closed_tableOKWith (rows : List BlakeRow) : G (tableOKWith H rows) := by
  unfold tableOKWith
  repeat' first
    | exact hpure _
    | (refine closed_allM G hpure hbind _ (fun _ ↦ ?_) _)
    | (refine hbind _ _ (hH _) fun _ ↦ ?_)
    | split

omit [LawfulMonad m] in
/-- A closed predicate holds of one node of V_I. -/
theorem closed_nodeStep (prog : Program) (seed : Digest) (ip : IdealProof) (ν : Node) :
    G (nodeStep H prog seed ip ν) := by
  unfold nodeStep
  repeat' first
    | exact hpure _
    | exact hH _
    | exact closed_mapM G hpure hbind _ (fun _ ↦ hH _) _
    | exact closed_rootOfLevelM G hpure hbind H hH _ _
    | exact closed_pNodeM G hpure hbind H hH _ _ _
    | exact closed_tableOKWith G hpure hbind H hH _
    | (refine hbind _ _ ?_ fun _ ↦ ?_)
    | (refine closed_forIn G hpure hbind _ (fun _ _ ↦ ?_) _ _)
    | split
    | dsimp only

omit [LawfulMonad m] in
/-- A closed predicate holds of V_I's closure. -/
theorem closed_closure (prog : Program) (seed : Digest) (ip : IdealProof) :
    ∀ (fuel : ℕ) (todo done : List Node), G (closure H prog seed ip fuel todo done)
  | _, [], _ => by unfold closure; exact hpure _
  | 0, _ :: _, _ => by unfold closure; exact hpure _
  | fuel + 1, ν :: todo, done => by
    unfold closure
    split
    · exact closed_closure prog seed ip fuel _ _
    · refine hbind _ _ (closed_nodeStep G hpure hbind H hH prog seed ip ν) fun o ↦ ?_
      split
      · exact hpure _
      · exact closed_closure prog seed ip fuel _ _

omit [LawfulMonad m] in
/-- A closed predicate holds of a Merkle path's climb. -/
theorem closed_climb : ∀ (node : Digest) (q : ℕ) (path : List Digest), G (climb H node q path)
  | _, _, [] => hpure _
  | _, _, _ :: _ => by
    unfold climb
    dsimp only
    split <;> exact hbind _ _ (hH _) fun _ ↦ closed_climb _ _ _

omit [LawfulMonad m] in
/-- A closed predicate holds of the openings' check. -/
theorem closed_openAll (root : Digest) (height width : ℕ) :
    ∀ (qs : List ℕ) (os : List Opening), G (openAll H root height width qs os)
  | [], _ => hpure _
  | _ :: _, [] => hpure _
  | q :: qs, o :: os => by
    unfold openAll
    refine hbind _ _ ?_ fun b ↦ ?_
    · unfold openOne
      split
      · exact hbind _ _ (hH _) fun _ ↦ hbind _ _ (closed_climb G hpure hbind H hH _ _ _)
          fun _ ↦ hpure _
      · exact hpure _
    · split
      · exact hbind _ _ (closed_openAll root height width qs os) fun _ ↦ hpure _
      · exact hpure _

omit [LawfulMonad m] in
/-- A closed predicate holds of the compiled reading of every program. -/
theorem closed_run {α : Type} (P : Prog α) : ∀ s : St, G (run H P s) := by
  induction P with
  | ret a => intro s; exact hpure _
  | fail => intro s; exact hpure _
  | read k ih =>
    intro s; unfold Compile.run; split
    · exact hpure _
    · exact hbind _ _ (hH _) fun _ ↦ ih _ _
  | sample k ih => intro s; exact hbind _ _ (hH _) fun _ ↦ ih _ _
  | grind bits k ih =>
    intro s; unfold Compile.run; split
    · exact hpure _
    · refine hbind _ _ (hH _) fun _ ↦ hbind _ _ (hH _) fun _ ↦ hbind _ _ (hH _) fun _ ↦ ?_
      split
      · exact ih _
      · exact hpure _
  | commit height width k ih =>
    intro s; unfold Compile.run; split
    · refine hbind _ _ (hH _) fun _ ↦ hbind _ _ (hH _) fun _ ↦ ?_
      split
      · exact ih _
      · exact hpure _
    · exact hpure _
  | query i ps k ih =>
    intro s; unfold Compile.run; split
    · exact hpure _
    · refine hbind _ _ (closed_openAll G hpure hbind H hH _ _ _ _ _) fun o ↦ ?_
      split
      · exact ih _ _
      · exact hpure _

omit [LawfulMonad m] in
/-- A closed predicate holds of a program's run on a proof. -/
theorem closed_runProof (P : Prog Bool) (seed : Digest) (π : Proof) : G (runProof H P seed π) := by
  unfold runProof
  refine hbind _ _ (closed_run G hpure hbind H hH P _) fun o ↦ ?_
  split <;> exact hpure _

omit [LawfulMonad m] hH in
/-- A closed predicate holds of the DA squeezes with a hash it holds of. -/
theorem closed_squeezesWith (HD : List UInt8 → m LeanDa.Digest) (hHD : ∀ x, G (HD x)) :
    ∀ (n : ℕ) (state : LeanDa.Digest), G (Da.squeezesWith HD n state)
  | 0, _ => hpure _
  | n + 1, _ => hbind _ _ (hHD _) fun _ ↦ hbind _ _ (closed_squeezesWith HD hHD n _)
      fun _ ↦ hpure _

/-- A closed predicate holds of V_I's outer checks. -/
theorem closed_outerChecksWith (prog : Program) (s : NodeStatement) :
    G (outerChecksWith H prog s) := by
  have hHD : ∀ x, G (Da.daHash H x) := fun x ↦ closed_map G hpure hbind _ _ (hH x)
  unfold outerChecksWith
  refine hbind _ _ (closed_allM G hpure hbind _ (fun c ↦ ?_) _) fun _ ↦ hpure _
  refine hbind _ _ ?_ fun _ ↦ hpure _
  unfold Da.vectorDigestOfWith Da.membershipVectorWith Da.membershipChallengesWith
  exact hbind _ _ (closed_map G hpure hbind _ _ (hbind _ _ (hHD _) fun _ ↦ hbind _ _ (hHD _)
    fun _ ↦ hbind _ _ (hHD _) fun _ ↦ closed_squeezesWith G hpure hbind _ hHD _ _))
    fun _ ↦ hHD _

/-- **V_I queries only through its hash**: a predicate on computations closed under `pure`
and `bind` and holding of every hash query holds of V_I, in every monad. -/
theorem closed_idealVerify (prog : Program) (ip : IdealProof) (fuel : ℕ) (s : NodeStatement) :
    G (idealVerify H prog ip fuel s) := by
  unfold idealVerify verifyBlindWith seedWith
  repeat' first
    | exact hpure _
    | exact hH _
    | exact closed_runProof G hpure hbind H hH _ _ _
    | exact closed_outerChecksWith G hpure hbind H hH _ _
    | exact closed_closure G hpure hbind H hH _ _ _ _ _ _
    | (refine hbind _ _ ?_ fun _ ↦ ?_)
    | split
end Closed

section Queries

variable {nx ns : ℕ}

/-! ## Hash queries in the game's monad -/

/-- `x` makes at most `c` hash queries, from every state. -/
def Costs (c : ℕ) {α : Type} (x : GameM nx ns α) : Prop :=
  ∀ st, IsQueryBoundP (x.run st) IsHash c

/-- A cost bound can be loosened. -/
theorem Costs.mono {c c' : ℕ} {α : Type} {x : GameM nx ns α} (h : Costs c x) (hc : c ≤ c') :
    Costs c' x := fun st ↦ (h st).mono hc

/-- `pure` costs nothing. -/
theorem costs_pure {α : Type} (a : α) : Costs 0 (pure a : GameM nx ns α) := fun st ↦ by
  simp

/-- The costs of a sequence add. -/
theorem costs_bind {c c' : ℕ} {α β : Type} {x : GameM nx ns α} {f : α → GameM nx ns β}
    (hx : Costs c x) (hf : ∀ a, Costs c' (f a)) : Costs (c + c') (x >>= f) := fun st ↦ by
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (hx st) fun p _ ↦ hf p.1 p.2

/-- Reading the signers' state costs nothing. -/
theorem costs_get : Costs 0 (get : GameM nx ns (SignState nx ns)) := fun st ↦ by
  simp

/-- Changing the signers' state costs nothing. -/
theorem costs_modify (f : SignState nx ns → SignState nx ns) :
    Costs 0 (modify f : GameM nx ns Unit) := fun st ↦ by
  simp

/-- A map costs what the computation does. -/
theorem costs_map {c : ℕ} {α β : Type} (f : α → β) {x : GameM nx ns α} (hx : Costs c x) :
    Costs c (f <$> x) := fun st ↦ by
  rw [StateT.run_map, isQueryBoundP_map_iff]
  exact hx st

/-- A computation on coins makes no hash query. -/
theorem isQueryBoundP_liftM_probComp {α : Type} (p : ProbComp α) :
    IsQueryBoundP (liftM p : OracleComp GameSpec α) IsHash 0 := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    rw [liftM_bind]
    change IsQueryBoundP (liftM (GameSpec.query (.inl t)) >>= fun a ↦ liftM (mx a)) IsHash 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl id, fun u ↦ ih u⟩

/-- Coins cost no hash query. -/
theorem costs_coins {α : Type} (p : ProbComp α) : Costs 0 (coins p : GameM nx ns α) := fun st ↦ by
  change IsQueryBoundP ((liftM (liftM p : OracleComp GameSpec α) : GameM nx ns α).run st) IsHash 0
  rw [OracleComp.liftM_run_StateT]
  exact isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_liftM_probComp p) fun _ _ ↦ trivial

/-- A hash query costs one. -/
theorem costs_hashQuery (x : Bytes) : Costs 1 (hashQuery x : GameM nx ns Digest) := fun st ↦ by
  change IsQueryBoundP ((liftM (liftM (GameSpec.query (.inr x)) : OracleComp GameSpec Digest) :
    GameM nx ns Digest).run st) IsHash 1
  rw [OracleComp.liftM_run_StateT, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr Nat.one_pos, fun _ ↦ trivial⟩

/-- A computation run with one hash query per query costs its total query bound. -/
theorem costs_simulateQ_hash {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (impl : QueryImpl spec (GameM nx ns)) (himpl : ∀ t, Costs 1 (impl t))
    {oa : OracleComp spec α} {c : ℕ} (hoa : IsTotalQueryBound oa c) :
    Costs c (simulateQ impl oa) := fun st ↦
  IsQueryBoundP.simulateQ_run_StateT_of_step (p := fun _ ↦ True)
    (isQueryBoundP_of_isTotalQueryBound _ hoa) (fun t s ↦ by simpa using himpl t s) st

/-- A leanXMSS computation costs its total query bound. -/
theorem costs_xmssRun {α : Type} {oa : OracleComp LeanXmss.HashSpec α} {c : ℕ}
    (hoa : IsTotalQueryBound oa c) : Costs c (xmssRun oa : GameM nx ns α) :=
  costs_simulateQ_hash _ (fun _ ↦ costs_map _ (costs_hashQuery _)) hoa

/-- A leanSPHINCS computation costs its total query bound. -/
theorem costs_sphincsRun {α : Type} {oa : OracleComp Sphincs.HashSpec α} {c : ℕ}
    (hoa : IsTotalQueryBound oa c) : Costs c (sphincsRun oa : GameM nx ns α) :=
  costs_simulateQ_hash _ (fun _ ↦ costs_map _ (costs_hashQuery _)) hoa

/-- A `mapM` over a list costs its length times the cost of an entry. -/
theorem costs_list_mapM {α β : Type} {c : ℕ} (f : α → GameM nx ns β) (hf : ∀ a, Costs c (f a)) :
    ∀ l : List α, Costs (l.length * c) (l.mapM f)
  | [] => by simpa using costs_pure (nx := nx) (ns := ns) ([] : List β)
  | a :: l => by
    rw [List.mapM_cons, List.length_cons, show (l.length + 1) * c = c + (l.length * c + 0) by ring]
    exact costs_bind (hf a) fun _ ↦ costs_bind (costs_list_mapM f hf l) fun _ ↦ costs_pure _

/-- A `mapM` over a vector costs its size times the cost of an entry. -/
theorem costs_vector_mapM {α β : Type} {n c : ℕ} (f : α → GameM nx ns β) (hf : ∀ a, Costs c (f a))
    (v : Vector α n) : Costs (n * c) (v.mapM f) := fun st ↦ by
  have h := costs_list_mapM f hf v.toList st
  rw [← Vector.toList_mapM, StateT.run_map, isQueryBoundP_map_iff, Vector.length_toList] at h
  exact h

variable [Sphincs.Params]

/-- **Key generation costs the keys' generation costs.** -/
theorem costs_keygen {cxk csk : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk) :
    Costs (nx * cxk + ns * csk) (keygen : GameM nx ns (Keys nx ns)) := by
  unfold keygen
  rw [show nx * cxk + ns * csk = nx * cxk + (ns * csk + 0) by ring]
  refine costs_bind (costs_vector_mapM _ (fun _ ↦ ?_) _) fun _ ↦
    costs_bind (costs_vector_mapM _ (fun _ ↦ ?_) _) fun _ ↦ costs_pure _
  · simpa using costs_bind (costs_coins _) fun s ↦ costs_xmssRun (nx := nx) (ns := ns) (hxk s)
  · simpa using costs_bind (costs_coins _) fun s ↦ costs_sphincsRun (nx := nx) (ns := ns) (hsk s)

/-- A leanXMSS signing request costs at most a signature. -/
theorem costs_xmssSign {cxs : ℕ}
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (keys : Keys nx ns) (j : Fin nx) (req : XmssRequest) : Costs cxs (xmssSign keys j req) := by
  unfold xmssSign
  rw [show cxs = 0 + cxs by ring]
  refine costs_bind costs_get fun st ↦ ?_
  split
  · exact (costs_pure _).mono (Nat.zero_le _)
  · rw [show cxs = cxs + (0 + 0) by ring]
    exact costs_bind (costs_xmssRun (hxs _ _ _)) fun _ ↦ costs_bind (costs_modify _)
      fun _ ↦ costs_pure _

/-- A leanSPHINCS signing request costs at most a signature. -/
theorem costs_sphincsSign {css : ℕ}
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (keys : Keys nx ns) (j : Fin ns) (msg : Sphincs.Message) :
    Costs css (sphincsSign keys j msg) := by
  unfold sphincsSign
  rw [show css = 0 + css by ring]
  refine costs_bind costs_get fun st ↦ ?_
  split
  · exact (costs_pure _).mono (Nat.zero_le _)
  · rw [show css = css + (0 + 0) by ring]
    exact costs_bind (costs_sphincsRun (hss _ _)) fun _ ↦ costs_bind (costs_modify _)
      fun _ ↦ costs_pure _

/-! ## V_I's queries -/

omit [Sphincs.Params] in
/-- **`x` spends its budget**: from every state, `x` followed by a continuation that makes at most
`N` hash queries plus the budget left makes at most `N` plus the budget left at the start. -/
def Spends (budget : ℕ) {α : Type} (x : OptionT (GameM nx ns) α) : Prop :=
  ∀ (st : SignState nx ns) (β : Type) (k : Option α × SignState nx ns → OracleComp GameSpec β)
    (N : ℕ), (∀ z, IsQueryBoundP (k z) IsHash (N + (budget - z.2.spent))) →
    IsQueryBoundP ((x.run).run st >>= k) IsHash (N + (budget - st.spent))

omit [Sphincs.Params] in
/-- `pure` spends nothing. -/
theorem spends_pure (budget : ℕ) {α : Type} (a : α) :
    Spends budget (pure a : OptionT (GameM nx ns) α) := by
  intro st β k N hk
  simpa using hk (some a, st)

omit [Sphincs.Params] in
/-- Spending is closed under sequencing. -/
theorem spends_bind (budget : ℕ) {α β : Type} (x : OptionT (GameM nx ns) α)
    (f : α → OptionT (GameM nx ns) β) (hx : Spends budget x) (hf : ∀ a, Spends budget (f a)) :
    Spends budget (x >>= f) := by
  intro st γ k N hk
  rw [OptionT.run_bind, Option.elimM, StateT.run_bind, bind_assoc]
  refine hx st γ _ N fun z ↦ ?_
  rcases z with ⟨_ | a, st'⟩
  · simpa using hk (none, st')
  · simpa using hf a st' γ k N hk

omit [Sphincs.Params] in
/-- Reading the state under `OptionT`. -/
theorem run_get_optionT :
    (get : OptionT (GameM nx ns) (SignState nx ns)).run = (some <$> get : GameM nx ns _) := rfl

omit [Sphincs.Params] in
/-- Changing the state under `OptionT`. -/
theorem run_modify_optionT (f : SignState nx ns → SignState nx ns) :
    (modify f : OptionT (GameM nx ns) Unit).run = (some <$> modify f : GameM nx ns _) := rfl

omit [Sphincs.Params] in
/-- A lifted computation under `OptionT`. -/
theorem run_liftM_optionT {α : Type} (x : GameM nx ns α) :
    (liftM x : OptionT (GameM nx ns) α).run = (some <$> x : GameM nx ns _) := rfl

omit [Sphincs.Params] in
/-- **A budgeted query spends the budget it consumes**: it makes one hash query exactly when
it counts one in the state, and none past the budget. -/
theorem spends_budgetedQuery (budget : ℕ) (x : Bytes) :
    Spends budget (budgetedQuery budget x : OptionT (GameM nx ns) Digest) := by
  intro st β k N hk
  unfold budgetedQuery
  by_cases hb : budget ≤ st.spent
  · simp [hb, Option.elimM, OptionT.run_bind, run_get_optionT]
    simpa [Nat.sub_eq_zero_of_le hb] using hk (none, st)
  · simp [hb, Option.elimM, OptionT.run_bind, run_get_optionT, run_modify_optionT]
    change IsQueryBoundP ((((liftM (liftM (GameSpec.query (.inr x)) :
      OracleComp GameSpec Digest) : GameM nx ns Digest)).run _) >>= _) _ _
    rw [OracleComp.liftM_run_StateT, bind_assoc]
    simp only [pure_bind]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr (by omega), fun d ↦ ?_⟩
    have h := hk (some d, { st with spent := st.spent + 1 })
    simp only [IsHash, ↓reduceIte] at h ⊢
    exact h.mono (by omega)

omit [Sphincs.Params] in
/-- **V_I makes at most the budget left of hash queries.** -/
theorem isQueryBoundP_idealVerify (budget : ℕ) (guest : Program) (ip : IdealProof) (fuel : ℕ)
    (s : NodeStatement) (st : SignState nx ns) :
    IsQueryBoundP (((idealVerify (budgetedQuery budget) guest ip fuel s).run).run st) IsHash
      (budget - st.spent) := by
  have h := closed_idealVerify (G := fun x ↦ Spends (nx := nx) (ns := ns) budget x)
    (fun a ↦ spends_pure budget a) (fun x f hx hf ↦ spends_bind budget x f hx hf)
    (budgetedQuery budget) (spends_budgetedQuery budget) guest ip fuel s st _ pure 0
    fun _ ↦ trivial
  simpa using h

/-! ## The adversary's queries -/

omit [Sphincs.Params] in
/-- The adversary's hash queries. -/
def AdvHash : (AdvSpec nx ns).Domain → Prop
  | .inl (.inl (.inr _)) => True
  | _ => False

omit [Sphincs.Params] in
/-- The adversary's leanXMSS signing requests. -/
def AdvXmss : (AdvSpec nx ns).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

omit [Sphincs.Params] in
/-- The adversary's leanSPHINCS signing requests. -/
def AdvSphincs : (AdvSpec nx ns).Domain → Prop
  | .inr _ => True
  | _ => False

/-- The adversary's hash queries are decidable. -/
instance : DecidablePred (AdvHash (nx := nx) (ns := ns))
  | .inl (.inl (.inr _)) => isTrue trivial
  | .inl (.inl (.inl _)) => isFalse id
  | .inl (.inr _) => isFalse id
  | .inr _ => isFalse id

/-- The adversary's leanXMSS requests are decidable. -/
instance : DecidablePred (AdvXmss (nx := nx) (ns := ns))
  | .inl (.inr _) => isTrue trivial
  | .inl (.inl _) => isFalse id
  | .inr _ => isFalse id

/-- The adversary's leanSPHINCS requests are decidable. -/
instance : DecidablePred (AdvSphincs (nx := nx) (ns := ns))
  | .inr _ => isTrue trivial
  | .inl _ => isFalse id

omit [Sphincs.Params] in
/-- Three predicate-targeted bounds as one bound on the triple of budgets. -/
theorem isQueryBound_triple {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {p₁ p₂ p₃ : ι → Prop} [DecidablePred p₁] [DecidablePred p₂] [DecidablePred p₃]
    {oa : OracleComp spec α} {n₁ n₂ n₃ : ℕ} (h₁ : IsQueryBoundP oa p₁ n₁)
    (h₂ : IsQueryBoundP oa p₂ n₂) (h₃ : IsQueryBoundP oa p₃ n₃) :
    IsQueryBound oa (n₁, n₂, n₃)
      (fun t b ↦ (¬ p₁ t ∨ 0 < b.1) ∧ (¬ p₂ t ∨ 0 < b.2.1) ∧ (¬ p₃ t ∨ 0 < b.2.2))
      (fun t b ↦ (if p₁ t then b.1 - 1 else b.1, if p₂ t then b.2.1 - 1 else b.2.1,
        if p₃ t then b.2.2 - 1 else b.2.2)) := by
  induction oa using OracleComp.inductionOn generalizing n₁ n₂ n₃ with
  | pure x => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h₁ h₂ h₃
    rw [isQueryBound_query_bind_iff]
    exact ⟨⟨h₁.1, h₂.1, h₃.1⟩, fun u ↦ ih u (h₁.2 u) (h₂.2 u) (h₃.2 u)⟩

/-- **The adversary's hash queries in the game**: at most `qH` of its own, `cxs` per leanXMSS
and `css` per leanSPHINCS signing request. -/
theorem costs_simulateQ_advImpl {cxs css : ℕ}
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (keys : Keys nx ns) {α : Type} (oa : OracleComp (AdvSpec nx ns) α) {qH sX sS : ℕ}
    (hH : IsQueryBoundP oa AdvHash qH) (hX : IsQueryBoundP oa AdvXmss sX)
    (hS : IsQueryBoundP oa AdvSphincs sS) :
    Costs (qH + sX * cxs + sS * css) (simulateQ (advImpl keys) oa) := by
  intro st
  have h := isQueryBound_triple hH hX hS
  rw [isQueryBoundP_def]
  refine IsQueryBound.simulateQ_run_of_step (combine := (· + ·))
    (mapBudget := fun b ↦ b.1 + b.2.1 * cxs + b.2.2 * css)
    (stepBudget := fun t _ ↦ match t with
      | .inl (.inl (.inl _)) => 0
      | .inl (.inl (.inr _)) => 1
      | .inl (.inr _) => cxs
      | .inr _ => css) h ?_ ?_ ?_ st
  · intro γ δ oa' ob b₁ b₂ h₁ h₂
    exact isQueryBoundP_bind h₁ fun x _ ↦ h₂ x
  · rintro (((n | x) | ⟨j, req⟩) | ⟨j, msg⟩) b s _
    · exact costs_coins _ s
    · exact costs_hashQuery x s
    · exact costs_xmssSign hxs keys j req s
    · exact costs_sphincsSign hss keys j msg s
  · rintro (((n | x) | ⟨j, req⟩) | ⟨j, msg⟩) ⟨b₁, b₂, b₃⟩ ⟨c₁, c₂, c₃⟩
    · simp [AdvHash, AdvXmss, AdvSphincs]
    · simp only [AdvHash, AdvXmss, AdvSphincs, ↓reduceIte, not_true_eq_false, false_or] at c₁ ⊢
      omega
    · simp only [AdvHash, AdvXmss, AdvSphincs, ↓reduceIte, not_true_eq_false, false_or] at c₂ ⊢
      obtain ⟨b, rfl⟩ : ∃ b, b₂ = b + 1 := ⟨b₂ - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    · simp only [AdvHash, AdvXmss, AdvSphincs, ↓reduceIte, not_true_eq_false, false_or] at c₃ ⊢
      obtain ⟨b, rfl⟩ : ∃ b, b₃ = b + 1 := ⟨b₃ - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring

/-- **The game's hash queries.** If every honest key generation and signature makes at most
`cxk`, `csk`, `cxs`, `css` hash queries, and the adversary, on every pair of key lists, at most
`qH` hash queries, `sX` leanXMSS and `sS` leanSPHINCS signing requests, then `gameComp` makes
at most `nx · cxk + ns · csk + (qH + sX · cxs + sS · css) + budget` hash queries. -/
theorem isQueryBoundP_gameComp {cxk csk cxs css : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) :
    IsQueryBoundP (gameComp guest fuel budget A) IsHash
      (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget) := by
  unfold gameComp
  have hV : ∀ (ip : IdealProof) (s : NodeStatement), Costs budget
      ((idealVerify (budgetedQuery budget) guest ip fuel s).run : GameM nx ns (Option Bool)) :=
    fun ip s st ↦ (isQueryBoundP_idealVerify budget guest ip fuel s st).mono (Nat.sub_le _ _)
  refine (isQueryBoundP_bind
    (n := nx * cxk + ns * csk + ((qH + sX * cxs + sS * css) + (budget + 0))) (m := 0) ?_
    fun z _ ↦ ?_).mono (by omega)
  · refine costs_bind (costs_keygen hxk hsk) (fun keys ↦ costs_bind
      (costs_simulateQ_advImpl hxs hss keys _ (hH _ _) (hX _ _) (hS _ _)) fun p ↦ ?_) _
    rcases p with ⟨s, ip⟩
    exact costs_bind (hV ip s) fun _ ↦ costs_pure _
  · rcases z with ⟨out, st⟩
    exact trivial

end Queries

end
end LeanVM.E2E
