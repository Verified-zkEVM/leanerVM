import XmssSecurity.Proof.Execution
import XmssSecurity.Proof.EvalDistEq
import LeanXmss.Scheme

/-!
# Oracle computations commute in the lazy random oracle

Two computations sharing the lazy random oracle and private sampling may run in either order: the
joint distribution of their results and the final cache is the same (`evalDist_run_bind_comm`). A
query answered once is cached, and answers at distinct inputs are independent and uniform; so two
queries commute (`evalDist_run_query_query_comm`), a query commutes past a computation, and by
induction any two computations commute.
-/

open OracleComp OracleSpec

namespace XmssSecurity.MultiUser

set_option backward.isDefEq.respectTransparency false

/-- The lazy random oracle's run of a computation from a cache. -/
noncomputable abbrev romRun {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) : ProbComp (α × QueryCache HashSpec) :=
  (simulateQ romImpl computation).run cache

theorem romRun_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    romRun ((liftM (OracleWorld.query input) : OracleComp OracleWorld _) >>= next) cache =
      (romImpl input).run cache >>= fun result => romRun (next result.1) result.2 := by
  simp only [romRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem romImpl_uniform_run (n : Nat) (cache : QueryCache HashSpec) :
    (romImpl (.inl n)).run cache =
      (fun sample => (sample, cache)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  change (unifFwdImpl HashSpec n).run cache = _
  simpa [simulateQ_query] using
    (unifFwdImpl.simulateQ_run (hashSpec := HashSpec)
      (liftM (unifSpec.query n) : ProbComp _) cache)

theorem romImpl_hash_run_some (input : HashInput) {cache : QueryCache HashSpec}
    {answer : HashOutput} (h : cache input = some answer) :
    (romImpl (.inr input)).run cache = pure (answer, cache) :=
  QueryImpl.withCaching_run_some _ h

theorem romImpl_hash_run_none (input : HashInput) {cache : QueryCache HashSpec}
    (h : cache input = none) :
    (romImpl (.inr input)).run cache =
      (fun answer => (answer, cache.cacheQuery input answer)) <$>
        (uniformSampleImpl (spec := HashSpec) input) :=
  QueryImpl.withCaching_run_none _ h

theorem romImpl_hash_cached (input : HashInput) (cache : QueryCache HashSpec)
    (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support ((romImpl (.inr input)).run cache)) :
    result.2 input = some result.1 := by
  cases hc : cache input with
  | some answer =>
      rw [romImpl_hash_run_some input hc, support_pure, Set.mem_singleton_iff] at hresult
      subst hresult
      exact hc
  | none =>
      rw [romImpl_hash_run_none input hc, support_map] at hresult
      obtain ⟨answer, _, rfl⟩ := hresult
      simp

/-- Two queries commute: the joint distribution of both answers and the final cache. -/
theorem evalDist_run_query_query_comm (first second : OracleWorld.Domain)
    (cache : QueryCache HashSpec) :
    ((romImpl first).run cache >>= fun r => (romImpl second).run r.2 >>= fun s =>
        (pure ((r.1, s.1), s.2) : ProbComp _)) =ᵈ
      ((romImpl second).run cache >>= fun s => (romImpl first).run s.2 >>= fun r =>
        (pure ((r.1, s.1), r.2) : ProbComp _)) := by
  rcases first with n | x
  · simp only [romImpl_uniform_run, bind_map_left]
    exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  · rcases second with m | y
    · simp only [romImpl_uniform_run, bind_map_left]
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
    · by_cases hxy : x = y
      · subst hxy
        have hside : ∀ (f : HashOutput × QueryCache HashSpec → HashOutput × QueryCache HashSpec →
              (HashOutput × HashOutput) × QueryCache HashSpec),
            (∀ r, f r r = ((r.1, r.1), r.2)) →
            ((romImpl (.inr x)).run cache >>= fun r => (romImpl (.inr x)).run r.2 >>= fun s =>
              (pure (f r s) : ProbComp _)) =ᵈ
            ((romImpl (.inr x)).run cache >>= fun r =>
              (pure ((r.1, r.1), r.2) : ProbComp _)) := by
          intro f hf
          refine OracleComp.EvalDistEq.bind_congr_of_support _ fun r hr => ?_
          rw [romImpl_hash_run_some x (romImpl_hash_cached x cache r hr), pure_bind, Prod.mk.eta, hf]
        exact (hside (fun r s => ((r.1, s.1), s.2)) fun r => rfl).trans
          (hside (fun s r => ((r.1, s.1), r.2)) fun r => rfl).symm
      · have hyx : y ≠ x := Ne.symm hxy
        cases hcx : cache x with
        | some u =>
            cases hcy : cache y with
            | some v =>
                simp [romImpl_hash_run_some x hcx, romImpl_hash_run_some y hcy]
            | none =>
                have hcx' : ∀ v, (cache.cacheQuery y v) x = some u := fun v => by
                  rw [QueryCache.cacheQuery_of_ne _ _ hxy, hcx]
                simp only [romImpl_hash_run_some x hcx, pure_bind, romImpl_hash_run_none y hcy,
                  bind_map_left, romImpl_hash_run_some x (hcx' _)]
                exact .rfl
        | none =>
            cases hcy : cache y with
            | some v =>
                have hcy' : ∀ u, (cache.cacheQuery x u) y = some v := fun u => by
                  rw [QueryCache.cacheQuery_of_ne _ _ hyx, hcy]
                simp only [romImpl_hash_run_none x hcx, bind_map_left,
                  romImpl_hash_run_some y (hcy' _), pure_bind, romImpl_hash_run_some y hcy]
                exact .rfl
            | none =>
                have hcy' : ∀ u, (cache.cacheQuery x u) y = none := fun u => by
                  rw [QueryCache.cacheQuery_of_ne _ _ hyx, hcy]
                have hcx' : ∀ v, (cache.cacheQuery y v) x = none := fun v => by
                  rw [QueryCache.cacheQuery_of_ne _ _ hxy, hcx]
                simp only [romImpl_hash_run_none x hcx, romImpl_hash_run_none y hcy, bind_map_left,
                  romImpl_hash_run_none y (hcy' _), romImpl_hash_run_none x (hcx' _)]
                simp only [QueryCache.cacheQuery_comm _ hxy]
                exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

theorem romRun_query_query {γ : Type} (first second : OracleWorld.Domain)
    (k : OracleWorld.Range first → OracleWorld.Range second → OracleComp OracleWorld γ)
    (cache : QueryCache HashSpec) :
    romRun ((liftM (OracleWorld.query first) : OracleComp OracleWorld _) >>= fun u =>
        (liftM (OracleWorld.query second) : OracleComp OracleWorld _) >>= fun v => k u v) cache =ᵈ
      romRun ((liftM (OracleWorld.query second) : OracleComp OracleWorld _) >>= fun v =>
        (liftM (OracleWorld.query first) : OracleComp OracleWorld _) >>= fun u => k u v) cache := by
  have hleft : romRun ((liftM (OracleWorld.query first) : OracleComp OracleWorld _) >>= fun u =>
        (liftM (OracleWorld.query second) : OracleComp OracleWorld _) >>= fun v => k u v) cache =
      ((romImpl first).run cache >>= fun r => (romImpl second).run r.2 >>= fun s =>
        (pure ((r.1, s.1), s.2) : ProbComp _)) >>= fun t => romRun (k t.1.1 t.1.2) t.2 := by
    simp only [romRun_query_bind, bind_assoc, pure_bind]
  have hright : romRun ((liftM (OracleWorld.query second) : OracleComp OracleWorld _) >>= fun v =>
        (liftM (OracleWorld.query first) : OracleComp OracleWorld _) >>= fun u => k u v) cache =
      ((romImpl second).run cache >>= fun s => (romImpl first).run s.2 >>= fun r =>
        (pure ((r.1, s.1), r.2) : ProbComp _)) >>= fun t => romRun (k t.1.1 t.1.2) t.2 := by
    simp only [romRun_query_bind, bind_assoc, pure_bind]
  rw [hleft, hright]
  exact (evalDist_run_query_query_comm first second cache).bind_left _

/-- A query commutes past a computation. -/
theorem romRun_query_comm {β γ : Type} (input : OracleWorld.Domain)
    (computation : OracleComp OracleWorld β)
    (k : OracleWorld.Range input → β → OracleComp OracleWorld γ) (cache : QueryCache HashSpec) :
    romRun ((liftM (OracleWorld.query input) : OracleComp OracleWorld _) >>= fun u =>
        computation >>= fun b => k u b) cache =ᵈ
      romRun (computation >>= fun b =>
        (liftM (OracleWorld.query input) : OracleComp OracleWorld _) >>= fun u => k u b) cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [pure_bind]; exact .rfl
  | query_bind other next ih =>
      simp only [bind_assoc]
      refine (romRun_query_query input other (fun u v => next v >>= fun b => k u b) cache).trans ?_
      rw [romRun_query_bind, romRun_query_bind]
      exact EvalDistEq.bind_right _ fun s => ih s.1 s.2

/-- **Two computations commute** in the lazy random oracle with private sampling. -/
theorem romRun_bind_comm {α β γ : Type} (first : OracleComp OracleWorld α)
    (second : OracleComp OracleWorld β) (k : α → β → OracleComp OracleWorld γ)
    (cache : QueryCache HashSpec) :
    romRun (first >>= fun a => second >>= fun b => k a b) cache =ᵈ
      romRun (second >>= fun b => first >>= fun a => k a b) cache := by
  induction first using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [pure_bind]; exact .rfl
  | query_bind input next ih =>
      simp only [bind_assoc]
      refine EvalDistEq.trans ?_ (romRun_query_comm input second
        (fun u b => next u >>= fun a => k a b) cache)
      rw [romRun_query_bind, romRun_query_bind]
      exact EvalDistEq.bind_right _ fun r => ih r.1 r.2

theorem romRun_bind {α β : Type} (first : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    romRun (first >>= next) cache = romRun first cache >>= fun r => romRun (next r.1) r.2 := by
  simp only [romRun, simulateQ_bind, StateT.run_bind]

/-- **Moving one computation of a sequence to the front.** Running computation `j` of a sequence
first, then the sequence with its result in position `j`, is running the sequence. -/
theorem romRun_sequenceFin_front {α γ : Type} :
    ∀ (n : Nat) (f : Fin n → OracleComp OracleWorld α) (j : Fin n)
      (k : α → (Fin n → α) → OracleComp OracleWorld γ) (cache : QueryCache HashSpec),
      romRun (f j >>= fun a =>
          LeanXmss.Concrete.sequenceFin (fun i : Fin n => if i = j then pure a else f i) >>= k a)
          cache =ᵈ
        romRun (LeanXmss.Concrete.sequenceFin f >>= fun keys => k (keys j) keys) cache
  | 0, _, j, _, _ => j.elim0
  | n + 1, f, j, k, cache => by
      cases j using Fin.cases with
      | zero =>
          simp only [LeanXmss.Concrete.sequenceFin, Fin.succ_ne_zero, ↓reduceIte, bind_assoc,
            pure_bind, Fin.cases_zero]
          exact .rfl
      | succ j =>
          simp only [LeanXmss.Concrete.sequenceFin, bind_assoc, pure_bind,
            show ((0 : Fin (n + 1)) = j.succ) = False from propext ⟨fun h => Fin.succ_ne_zero j h.symm,
              False.elim⟩, ↓reduceIte, Fin.succ_inj, Fin.cases_succ]
          refine (romRun_bind_comm (f j.succ) (f 0) _ cache).trans ?_
          rw [romRun_bind, romRun_bind]
          exact EvalDistEq.bind_right _ fun r =>
            romRun_sequenceFin_front n (fun i => f i.succ) j
              (fun a t => k a (Fin.cases r.1 t)) r.2

/-- Mapping each computation of a sequence maps its results. -/
theorem sequenceFin_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} :
    ∀ {n : Nat} (f : Fin n → m α) (g : Fin n → α → β),
      LeanXmss.Concrete.sequenceFin (fun i => g i <$> f i) =
        (fun results i => g i (results i)) <$> LeanXmss.Concrete.sequenceFin f
  | 0, _, _ => by
      simp only [LeanXmss.Concrete.sequenceFin, map_pure]
      congr 1
      funext i
      exact i.elim0
  | n + 1, f, g => by
      simp only [LeanXmss.Concrete.sequenceFin, map_bind, bind_map_left, map_pure]
      congr 1
      funext head
      rw [sequenceFin_map (fun i => f i.succ) (fun i => g i.succ), bind_map_left]
      congr 1
      funext tail
      congr 1
      funext i
      cases i using Fin.cases <;> rfl

/-- **The value in a pure position of a sequence is immaterial**: the continuation may overwrite it. -/
theorem sequenceFin_slot {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} {n : Nat}
    (j : Fin n) (x y : α) (c : Fin n → m α) (G : (Fin n → α) → m β) :
    (LeanXmss.Concrete.sequenceFin (fun i => if i = j then pure x else c i) >>= fun keys =>
        G (fun i => if i = j then y else keys i)) =
      LeanXmss.Concrete.sequenceFin (fun i => if i = j then pure y else c i) >>= G := by
  have h : (fun i => if i = j then pure y else c i) =
      fun i => (fun a => if i = j then y else a) <$> (if i = j then pure x else c i) := by
    funext i
    by_cases hi : i = j
    · simp only [hi, ↓reduceIte, map_pure]
    · simp only [hi, ↓reduceIte, id_map']
  rw [h, sequenceFin_map, bind_map_left]

end XmssSecurity.MultiUser
