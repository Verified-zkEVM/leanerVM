/-
  LeanVM.E2E.Vis.Engine

  W-vis, P1: the potential engine with two rates, charged by the class of a fresh query's input,
  and the game with V_I's trace split at the end of key generation.
-/

module

public import LeanVM.E2E.Reduction.Record

/-!
# The two-rate engine and the key-generation split (W-vis, P1)

The plan is `docs/roadmap/w-vis.md` §3 P1.

**Two rates** (`prEvent_run_le_twoRate`). Route B charges a fresh query by its input's class: a
fresh `p`-query (a visible one) raises the potential `Φ` by at most `δp`, a fresh `q`-query
outside `p` (a hidden one) by at most `δq`, and a fresh query outside `q` (a coin) not at all.
With at most `a` queries of `p` and `b` of `q` (`p ⊆ q`), an event forcing `1 ≤ Φ` has probability
at most `Φ s₀ + a · δp + b · δq`. As in the one-rate engine
(`prEvent_run_le_of_freshStepBelowP`), the step bounds are needed only at states of size below
`N`: a fresh `q`-query raises the size by at most one, another fresh query keeps it, and
`size s₀ + b ≤ N`. The proof is the budgeted engine with two budgets
(`lintegral_run_le_of_budgetedPQ`), the two `IsQueryBoundP` bounds read along each path.

**The key-generation split** (`gameRec_eq_keygen_bind`). The game with V_I's trace (`gameRec`)
is the key generation's run from the empty log (`keygenPhase`), then the rest (`restRec`: the
adversary with its oracles, then V_I recorded) from the keys, the signers' state and the log it
reached. The rest keeps the keys (`restRec_keys`). So a bound on the rest at every reachable
outcome of key generation bounds the game, averaged over key generation
(`prEvent_gameRec_le_of_phase`; uniform form `prEvent_gameRec_le_of_phase_const`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp MeasureTheory
open scoped ENNReal

@[expose] public section

/-! ## The engine with two budgets -/

section TwoRate

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}
  [∀ t, SampleableType (spec.Range t)] [∀ t, Fintype (spec.Range t)]
  {σ : Type} {lookup : σ → (t : spec.Domain) → Option (spec.Range t)}
  {record : σ → (t : spec.Domain) → spec.Range t → σ}

/-- A potential monotone in each budget is monotone in both. -/
theorem budgets_mono_le {Φ : ℕ → ℕ → σ → ℝ≥0∞}
    (hmono : ∀ (m n : ℕ) (s : σ), Φ m n s ≤ Φ (m + 1) n s ∧ Φ m n s ≤ Φ m (n + 1) s)
    (s : σ) {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') : Φ m n s ≤ Φ m' n' s :=
  (monotone_nat_of_le_succ (f := fun k ↦ Φ k n s) (fun k ↦ (hmono k n s).1) hm).trans
    (monotone_nat_of_le_succ (f := fun k ↦ Φ m' k s) (fun k ↦ (hmono m' k s).2) hn)

/-- **The budgeted potential bound with two budgets.** The budgets count the queries of `p` and
of `q`, `p ⊆ q`. A fresh `p`-query lowers both budgets by one, a fresh `q`-query outside `p` the
second only, another fresh query neither; none raises the potential, in expectation, above its
value at the budgets before; more budget never lowers the potential. Then a computation with at
most `a` queries of `p` and `b` of `q`, run against the lazy sampler from `s₀`, has expected
payoff at most `Φ a b s₀`, for every payoff bounded on reachable outcomes by `Φ 0 0` of the final
state. -/
theorem lintegral_run_le_of_budgetedPQ {impl : QueryImpl spec (StateT σ ProbComp)}
    (himpl : IsLazySampler lookup record impl) (p q : ι → Prop) [DecidablePred p]
    [DecidablePred q] (hpq : ∀ t, p t → q t) {α : Type}
    [MeasurableSpace (α × σ)] [DiscreteMeasurableSpace (α × σ)] {Φ : ℕ → ℕ → σ → ℝ≥0∞}
    (hP : ∀ (m n : ℕ) (s : σ) (t : spec.Domain), p t → lookup s t = none →
      (∑ u, Φ m n (record s t u)) / Fintype.card (spec.Range t) ≤ Φ (m + 1) (n + 1) s)
    (hQ : ∀ (m n : ℕ) (s : σ) (t : spec.Domain), q t → ¬ p t → lookup s t = none →
      (∑ u, Φ m n (record s t u)) / Fintype.card (spec.Range t) ≤ Φ m (n + 1) s)
    (hF : ∀ (m n : ℕ) (s : σ) (t : spec.Domain), ¬ q t → lookup s t = none →
      (∑ u, Φ m n (record s t u)) / Fintype.card (spec.Range t) ≤ Φ m n s)
    (hmono : ∀ (m n : ℕ) (s : σ), Φ m n s ≤ Φ (m + 1) n s ∧ Φ m n s ≤ Φ m (n + 1) s)
    (oa : OracleComp spec α) (a b : ℕ) (ha : IsQueryBoundP oa p a) (hb : IsQueryBoundP oa q b)
    (s₀ : σ) (g : α × σ → ℝ≥0∞)
    (hg : ∀ z ∈ support ((simulateQ impl oa).run s₀), g z ≤ Φ 0 0 z.2) :
    ∫⁻ z, g z ∂𝒟[(simulateQ impl oa).run s₀] ≤ Φ a b s₀ := by
  induction oa using OracleComp.inductionOn generalizing a b s₀ with
  | pure x =>
    rw [simulateQ_pure, StateT.run_pure] at hg ⊢
    rw [evalDist_pure, lintegral_dirac]
    exact (hg _ (by simp)).trans (budgets_mono_le hmono s₀ (Nat.zero_le a) (Nat.zero_le b))
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at ha hb
    obtain ⟨hapos, harest⟩ := ha
    obtain ⟨hbpos, hbrest⟩ := hb
    rw [simulateQ_query_bind, StateT.run_bind] at hg ⊢
    simp only [OracleQuery.input_query, monadLift_self] at hg ⊢
    change ∫⁻ z, g z ∂𝒟[(impl t).run s₀ >>= fun p ↦ (simulateQ impl (mx p.1)).run p.2] ≤ _
    change ∀ z ∈ support ((impl t).run s₀ >>= fun p ↦ (simulateQ impl (mx p.1)).run p.2), _
      at hg
    rw [himpl t s₀] at hg ⊢
    have hstep : lookup s₀ t = none →
        (∑ u, Φ (if p t then a - 1 else a) (if q t then b - 1 else b) (record s₀ t u)) /
          Fintype.card (spec.Range t) ≤ Φ a b s₀ := by
      intro hn
      by_cases hp : p t
      · have hq := hpq t hp
        obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 :=
          ⟨a - 1, by have := hapos.resolve_left (not_not.mpr hp); omega⟩
        obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 :=
          ⟨b - 1, by have := hbpos.resolve_left (not_not.mpr hq); omega⟩
        simp only [hp, hq, ↓reduceIte, Nat.add_sub_cancel]
        exact hP m n s₀ t hp hn
      · by_cases hq : q t
        · obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 :=
            ⟨b - 1, by have := hbpos.resolve_left (not_not.mpr hq); omega⟩
          simp only [hp, hq, ↓reduceIte, Nat.add_sub_cancel]
          exact hQ a n s₀ t hq hp hn
        · simp only [hp, hq, ↓reduceIte]
          exact hF a b s₀ t hq hn
    rcases hs : lookup s₀ t with _ | u
    · simp only [hs, bind_assoc, pure_bind] at hg ⊢
      let _ : MeasurableSpace (spec.Range t) := ⊤
      rw [lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete,
        SampleableType.evalDist_uniformSample, ProbabilityTheory.lintegral_uniformOn_univ]
      calc (∑ u, ∫⁻ z, g z ∂𝒟[(simulateQ impl (mx u)).run (record s₀ t u)])
            / Fintype.card (spec.Range t)
          ≤ (∑ u, Φ (if p t then a - 1 else a) (if q t then b - 1 else b) (record s₀ t u))
              / Fintype.card (spec.Range t) := by
            gcongr with u
            refine ih u _ _ (harest u) (hbrest u) _ fun z hz ↦ hg z ?_
            exact (mem_support_bind_iff _ _ _).mpr ⟨u, mem_support_uniformSample _, hz⟩
        _ ≤ Φ a b s₀ := hstep hs
    · simp only [hs, pure_bind] at hg ⊢
      refine (ih u _ _ (harest u) (hbrest u) s₀ hg).trans (budgets_mono_le hmono s₀ ?_ ?_)
      · split <;> omega
      · split <;> omega

/-- **Markov at one, two rates** (W-vis, P1). Fresh queries are charged by class: a `p`-query
raises `Φ` by at most `δp`, a `q`-query outside `p` by at most `δq`, both only needed at states
of size below `N`; a query outside `q` does not raise it. A fresh `q`-query raises the size by at
most one, another fresh query keeps it. Then after a run with at most `a` queries of `p` and `b`
of `q` from `s₀` with `size s₀ + b ≤ N`, an event that forces `1 ≤ Φ` of the final state has
probability at most `Φ s₀ + a · δp + b · δq`. -/
theorem prEvent_run_le_twoRate {impl : QueryImpl spec (StateT σ ProbComp)}
    (himpl : IsLazySampler lookup record impl)
    (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (hpq : ∀ t, p t → q t)
    {Φ : σ → ℝ≥0∞} {δp δq : ℝ≥0∞} (size : σ → ℕ) (N : ℕ)
    (hsize : ∀ s t u, q t → lookup s t = none → size (record s t u) ≤ size s + 1)
    (hsize' : ∀ s t u, ¬ q t → lookup s t = none → size (record s t u) ≤ size s)
    (hp : ∀ s t, size s < N → p t → lookup s t = none →
      (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s + δp)
    (hq : ∀ s t, size s < N → q t → ¬ p t → lookup s t = none →
      (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s + δq)
    (hfree : ∀ s t, ¬ q t → lookup s t = none →
      (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s)
    {α : Type} (oa : OracleComp spec α) (a b : ℕ) (ha : IsQueryBoundP oa p a)
    (hb : IsQueryBoundP oa q b) (s₀ : σ) (hs₀ : size s₀ + b ≤ N) (ev : α → σ → Prop)
    (hev : ∀ z ∈ support ((simulateQ impl oa).run s₀), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ impl oa).run s₀}[ev z.1 z.2] ≤ Φ s₀ + a * δp + b * δq := by
  classical
  let _ : MeasurableSpace (α × σ) := ⊤
  rw [prEvent_eq_evalDist_of_discrete _ (fun z : α × σ ↦ ev z.1 z.2),
    ← lintegral_indicator_one MeasurableSet.of_discrete]
  -- The potential with two budgets, infinite past the size cap.
  let Ψ : ℕ → ℕ → σ → ℝ≥0∞ := fun m n s ↦
    if size s + n ≤ N then Φ s + (m * δp + n * δq) else ⊤
  have key := lintegral_run_le_of_budgetedPQ (Φ := Ψ) himpl p q hpq ?_ ?_ ?_ ?_ oa a b ha hb s₀
    (Set.indicator {z : α × σ | ev z.1 z.2} 1) ?_
  · refine key.trans (le_of_eq ?_)
    simp only [Ψ, ite_eq_left hs₀, add_assoc]
  -- A `p`-query.
  · intro m n s t hpt hs
    have hqt := hpq t hpt
    by_cases hN : size s + (n + 1) ≤ N
    · simp only [Ψ, ite_eq_left hN]
      calc (∑ u, (if size (record s t u) + n ≤ N then Φ (record s t u) + (m * δp + n * δq)
              else ⊤)) / Fintype.card (spec.Range t)
          = (∑ u, (Φ (record s t u) + (m * δp + n * δq))) / Fintype.card (spec.Range t) := by
            congr 1
            refine Finset.sum_congr rfl fun u _ ↦ ite_eq_left ?_
            have := hsize s t u hqt hs
            omega
        _ = (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) + (m * δp + n * δq) :=
            sum_add_const_div_card t _ _
        _ ≤ Φ s + δp + (m * δp + n * δq) := by gcongr; exact hp s t (by omega) hpt hs
        _ ≤ Φ s + δp + (m * δp + n * δq) + δq := le_self_add
        _ = Φ s + (((m + 1 : ℕ) : ℝ≥0∞) * δp + ((n + 1 : ℕ) : ℝ≥0∞) * δq) := by
            push_cast; ring
    · simp only [Ψ, ite_eq_right hN]
      exact le_top
  -- A `q`-query outside `p`.
  · intro m n s t hqt hpt hs
    by_cases hN : size s + (n + 1) ≤ N
    · simp only [Ψ, ite_eq_left hN]
      calc (∑ u, (if size (record s t u) + n ≤ N then Φ (record s t u) + (m * δp + n * δq)
              else ⊤)) / Fintype.card (spec.Range t)
          = (∑ u, (Φ (record s t u) + (m * δp + n * δq))) / Fintype.card (spec.Range t) := by
            congr 1
            refine Finset.sum_congr rfl fun u _ ↦ ite_eq_left ?_
            have := hsize s t u hqt hs
            omega
        _ = (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) + (m * δp + n * δq) :=
            sum_add_const_div_card t _ _
        _ ≤ Φ s + δq + (m * δp + n * δq) := by gcongr; exact hq s t (by omega) hqt hpt hs
        _ = Φ s + ((m : ℝ≥0∞) * δp + ((n + 1 : ℕ) : ℝ≥0∞) * δq) := by
            push_cast; ring
    · simp only [Ψ, ite_eq_right hN]
      exact le_top
  -- A query outside `q`.
  · intro m n s t hqt hs
    by_cases hN : size s + n ≤ N
    · simp only [Ψ, ite_eq_left hN]
      calc (∑ u, (if size (record s t u) + n ≤ N then Φ (record s t u) + (m * δp + n * δq)
              else ⊤)) / Fintype.card (spec.Range t)
          = (∑ u, (Φ (record s t u) + (m * δp + n * δq))) / Fintype.card (spec.Range t) := by
            congr 1
            refine Finset.sum_congr rfl fun u _ ↦ ite_eq_left ?_
            have := hsize' s t u hqt hs
            omega
        _ = (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) + (m * δp + n * δq) :=
            sum_add_const_div_card t _ _
        _ ≤ Φ s + (m * δp + n * δq) := by gcongr; exact hfree s t hqt hs
    · simp only [Ψ, ite_eq_right hN]
      exact le_top
  -- Monotone in the budgets.
  · intro m n s
    refine ⟨?_, ?_⟩
    · by_cases hN : size s + n ≤ N
      · simp only [Ψ, ite_eq_left hN]
        gcongr
        exact_mod_cast Nat.le_succ m
      · simp only [Ψ, ite_eq_right hN, le_refl]
    · by_cases hN : size s + (n + 1) ≤ N
      · simp only [Ψ, ite_eq_left hN, ite_eq_left (show size s + n ≤ N by omega)]
        gcongr
        exact_mod_cast Nat.le_succ n
      · simp only [Ψ, ite_eq_right hN]
        exact le_top
  -- The payoff.
  · intro z hz
    by_cases hN : size z.2 + 0 ≤ N
    · simp only [Ψ, ite_eq_left hN, Nat.cast_zero, zero_mul, add_zero]
      by_cases hz' : ev z.1 z.2
      · simpa [Set.indicator_of_mem (show z ∈ {z : α × σ | ev z.1 z.2} from hz')]
          using hev z hz hz'
      · simp [Set.indicator_of_notMem (show z ∉ {z : α × σ | ev z.1 z.2} from hz')]
    · simp only [Ψ, ite_eq_right hN]
      exact le_top

end TwoRate

/-! ## The key-generation split -/

section Split

variable {nx ns : ℕ} [Sphincs.Params]

/-- **The key-generation phase**: the honest keys' generation against the game's oracle from
the empty log; the keys, the signers' state and the log it reached. -/
noncomputable def keygenPhase : ProbComp ((Keys nx ns × SignState nx ns) × Log) :=
  (simulateQ gameImpl ((keygen : GameM nx ns (Keys nx ns)).run (SignState.init nx ns))).run []

/-- **The rest of the game with V_I's trace**, from the keys and the signers' state: the
adversary with its oracles, then V_I recorded; the outcome and the trace. -/
noncomputable def restRec (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (keys : Keys nx ns) (st : SignState nx ns) : OracleComp GameSpec (GameOutcome nx ns × Log) := do
  let (out, st') ← (do
      let (s, ip) ← simulateQ (advImpl keys)
        (A (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1))
      let o ← viRec budget guest ip fuel s
      pure (keys, s, ip, o) : GameM nx ns _).run st
  pure (⟨out.1, out.2.1, out.2.2.1, (out.2.2.2.map Prod.fst).getD false, st'⟩,
    (out.2.2.2.map Prod.snd).getD [])

/-- The game's computation with V_I's trace is key generation, then the rest. -/
theorem gameCompRec_eq_keygen_bind (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    gameCompRec guest fuel budget A =
      ((keygen : GameM nx ns (Keys nx ns)).run (SignState.init nx ns)) >>= fun k ↦
        restRec guest fuel budget A k.1 k.2 := by
  unfold gameCompRec restRec
  simp only [StateT.run_bind, bind_assoc]

/-- **The game with V_I's trace is the key-generation phase, then the rest** from the keys, the
signers' state and the log it reached. -/
theorem gameRec_eq_keygen_bind (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    gameRec guest fuel budget A = keygenPhase >>= fun k ↦
      (simulateQ gameImpl (restRec guest fuel budget A k.1.1 k.1.2)).run k.2 := by
  rw [gameRec, gameCompRec_eq_keygen_bind, simulateQ_bind, StateT.run_bind, keygenPhase]

/-- **The rest keeps the keys.** -/
theorem restRec_keys {guest : Program} {fuel budget : ℕ} {A : GameAdversary nx ns}
    {keys : Keys nx ns} {st : SignState nx ns} {z : GameOutcome nx ns × Log}
    (hz : z ∈ support (restRec guest fuel budget A keys st)) : z.1.keys = keys := by
  unfold restRec at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨⟨out, st'⟩, hout, hz⟩ := hz
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rw [StateT.run_bind, mem_support_bind_iff] at hout
  obtain ⟨⟨⟨s, ip⟩, st₁⟩, -, hout⟩ := hout
  rw [StateT.run_bind, mem_support_bind_iff] at hout
  obtain ⟨⟨o, st₂⟩, -, hout⟩ := hout
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
  obtain ⟨rfl, -⟩ := hout
  rfl

/-- **Conditioning on key generation.** A bound `B k` on an event of the rest, at every reachable
outcome `k` of key generation, bounds the event of the game with V_I's trace by the average of
`B` over key generation. -/
theorem prEvent_gameRec_le_of_phase
    [MeasurableSpace ((Keys nx ns × SignState nx ns) × Log)]
    [DiscreteMeasurableSpace ((Keys nx ns × SignState nx ns) × Log)]
    {guest : Program} {fuel budget : ℕ} {A : GameAdversary nx ns}
    (ev : ((GameOutcome nx ns × Log) × Log) → Prop)
    (B : (Keys nx ns × SignState nx ns) × Log → ℝ≥0∞)
    (h : ∀ k ∈ support (keygenPhase (nx := nx) (ns := ns)),
      Pr{let z ← (simulateQ gameImpl (restRec guest fuel budget A k.1.1 k.1.2)).run k.2}[ev z] ≤
        B k) :
    Pr{let p ← gameRec guest fuel budget A}[ev p] ≤ ∫⁻ k, B k ∂𝒟[keygenPhase] := by
  rw [gameRec_eq_keygen_bind, prEvent_bind_eq_lintegral_of_discrete]
  exact lintegral_mono_ae (ae_evalDist_of_forall_mem_support _ h)

/-- **Conditioning on key generation, a uniform bound.** -/
theorem prEvent_gameRec_le_of_phase_const {guest : Program} {fuel budget : ℕ}
    {A : GameAdversary nx ns} (ev : ((GameOutcome nx ns × Log) × Log) → Prop) {ε : ℝ≥0∞}
    (h : ∀ k ∈ support (keygenPhase (nx := nx) (ns := ns)),
      Pr{let z ← (simulateQ gameImpl (restRec guest fuel budget A k.1.1 k.1.2)).run k.2}[ev z] ≤
        ε) :
    Pr{let p ← gameRec guest fuel budget A}[ev p] ≤ ε := by
  let _ : MeasurableSpace ((Keys nx ns × SignState nx ns) × Log) := ⊤
  refine (prEvent_gameRec_le_of_phase ev (fun _ ↦ ε) h).trans ?_
  rw [lintegral_const]
  exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)

end Split

end
end LeanVM.E2E
