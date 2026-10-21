/-
  LeanVM.E2E.Reduction.Commute

  Computations commute in the schemes' lazy random oracle: the joint distribution of their
  results and the final cache does not depend on their order.
-/

module

public import LeanVM.E2E.Reduction.World

/-!
# Commuting computations in the lazy random oracle

Two computations sharing the schemes' lazy random oracle (`owImpl`, coins forwarded) may run in
either order: the joint distribution of their results and the final cache is the same
(`romRun_bind_comm`). A query answered once is cached, and answers at distinct inputs are
independent and uniform; so two queries commute (`evalDistEq_run_query_query_comm`), a query
commutes past a computation, and by induction any two computations commute. (The argument is
`XmssSecurity.MultiUser.romRun_bind_comm`'s, in `lean_xmss`, for the lean_vm module system.)

The ordered log of the game's oracle does depend on the order; T5's reductions use this only
after the transport to the cache (`evalDistEq_run_toW`), on events of the game's outcome and V_I's
trace.
-/

namespace LeanVM.E2E

open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-- The schemes' lazy random oracle's run of a computation from a cache. -/
noncomputable abbrev romRun {α : Type} (oa : OracleComp OW α) (c : QueryCache LeanXmss.HashSpec) :
    ProbComp (α × QueryCache LeanXmss.HashSpec) :=
  (simulateQ owImpl oa).run c

/-- The run of a query then a continuation. -/
theorem romRun_query_bind {α : Type} (t : OW.Domain) (k : OW.Range t → OracleComp OW α)
    (c : QueryCache LeanXmss.HashSpec) :
    romRun ((liftM (OW.query t) : OracleComp OW _) >>= k) c =
      (owImpl t).run c >>= fun r ↦ romRun (k r.1) r.2 := by
  simp only [romRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

/-- A coin query leaves the cache. -/
theorem owImpl_uniform_run (n : ℕ) (c : QueryCache LeanXmss.HashSpec) :
    (owImpl (.inl n)).run c = (fun u ↦ (u, c)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  change (unifFwdImpl LeanXmss.HashSpec n).run c = _
  simpa [simulateQ_query] using
    (unifFwdImpl.simulateQ_run (hashSpec := LeanXmss.HashSpec)
      (liftM (unifSpec.query n) : ProbComp _) c)

/-- A cached hash query answers from the cache. -/
theorem owImpl_hash_run_some (x : List UInt8) {c : QueryCache LeanXmss.HashSpec}
    {u : LeanXmss.HashOutput} (h : c x = some u) : (owImpl (.inr x)).run c = pure (u, c) :=
  QueryImpl.withCaching_run_some _ h

/-- A fresh hash query samples and caches. -/
theorem owImpl_hash_run_none (x : List UInt8) {c : QueryCache LeanXmss.HashSpec} (h : c x = none) :
    (owImpl (.inr x)).run c =
      (fun u ↦ (u, c.cacheQuery x u)) <$> (uniformSampleImpl (spec := LeanXmss.HashSpec) x) :=
  QueryImpl.withCaching_run_none _ h

/-- A hash query's answer is cached after it. -/
theorem owImpl_hash_cached (x : List UInt8) (c : QueryCache LeanXmss.HashSpec)
    (r : LeanXmss.HashOutput × QueryCache LeanXmss.HashSpec)
    (hr : r ∈ support ((owImpl (.inr x)).run c)) : r.2 x = some r.1 := by
  cases hc : c x with
  | some u =>
      rw [owImpl_hash_run_some x hc, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact hc
  | none =>
      rw [owImpl_hash_run_none x hc, support_map] at hr
      obtain ⟨u, _, rfl⟩ := hr
      simp

/-- **Two queries commute**: the joint distribution of both answers and the final cache. -/
theorem evalDistEq_run_query_query_comm (first second : OW.Domain)
    (c : QueryCache LeanXmss.HashSpec) :
    ((owImpl first).run c >>= fun r ↦ (owImpl second).run r.2 >>= fun s ↦
        (pure ((r.1, s.1), s.2) : ProbComp _)) =ᵈ
      ((owImpl second).run c >>= fun s ↦ (owImpl first).run s.2 >>= fun r ↦
        (pure ((r.1, s.1), r.2) : ProbComp _)) := by
  rcases first with n | x
  · simp only [owImpl_uniform_run, bind_map_left]
    exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  · rcases second with m | y
    · simp only [owImpl_uniform_run, bind_map_left]
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
    · by_cases hxy : x = y
      · subst hxy
        have hside : ∀ (f : LeanXmss.HashOutput × QueryCache LeanXmss.HashSpec →
              LeanXmss.HashOutput × QueryCache LeanXmss.HashSpec →
              (LeanXmss.HashOutput × LeanXmss.HashOutput) × QueryCache LeanXmss.HashSpec),
            (∀ r, f r r = ((r.1, r.1), r.2)) →
            ((owImpl (.inr x)).run c >>= fun r ↦ (owImpl (.inr x)).run r.2 >>= fun s ↦
              (pure (f r s) : ProbComp _)) =ᵈ
            ((owImpl (.inr x)).run c >>= fun r ↦
              (pure ((r.1, r.1), r.2) : ProbComp _)) := by
          intro f hf
          refine OracleComp.EvalDistEq.bind_congr_of_support _ fun r hr ↦ ?_
          rw [owImpl_hash_run_some x (owImpl_hash_cached x c r hr), pure_bind, Prod.mk.eta, hf]
        exact (hside (fun r s ↦ ((r.1, s.1), s.2)) fun r ↦ rfl).trans
          (hside (fun s r ↦ ((r.1, s.1), r.2)) fun r ↦ rfl).symm
      · have hyx : y ≠ x := Ne.symm hxy
        cases hcx : c x with
        | some u =>
            cases hcy : c y with
            | some v =>
                simp only [owImpl_hash_run_some x hcx, owImpl_hash_run_some y hcy, pure_bind]
                exact .rfl
            | none =>
                have hcx' : ∀ v, (c.cacheQuery y v) x = some u := fun v ↦ by
                  rw [QueryCache.cacheQuery_of_ne _ _ hxy, hcx]
                simp only [owImpl_hash_run_some x hcx, pure_bind, owImpl_hash_run_none y hcy,
                  bind_map_left, owImpl_hash_run_some x (hcx' _)]
                exact .rfl
        | none =>
            cases hcy : c y with
            | some v =>
                have hcy' : ∀ u, (c.cacheQuery x u) y = some v := fun u ↦ by
                  rw [QueryCache.cacheQuery_of_ne _ _ hyx, hcy]
                simp only [owImpl_hash_run_none x hcx, bind_map_left,
                  owImpl_hash_run_some y (hcy' _), pure_bind, owImpl_hash_run_some y hcy]
                exact .rfl
            | none =>
                have hcy' : ∀ u, (c.cacheQuery x u) y = none := fun u ↦ by
                  rw [QueryCache.cacheQuery_of_ne _ _ hyx, hcy]
                have hcx' : ∀ v, (c.cacheQuery y v) x = none := fun v ↦ by
                  rw [QueryCache.cacheQuery_of_ne _ _ hxy, hcx]
                simp only [owImpl_hash_run_none x hcx, owImpl_hash_run_none y hcy, bind_map_left,
                  owImpl_hash_run_none y (hcy' _), owImpl_hash_run_none x (hcx' _)]
                simp only [QueryCache.cacheQuery_comm _ hxy]
                exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- Two queries commute before a continuation. -/
theorem romRun_query_query {γ : Type} (first second : OW.Domain)
    (k : OW.Range first → OW.Range second → OracleComp OW γ) (c : QueryCache LeanXmss.HashSpec) :
    romRun ((liftM (OW.query first) : OracleComp OW _) >>= fun u ↦
        (liftM (OW.query second) : OracleComp OW _) >>= fun v ↦ k u v) c =ᵈ
      romRun ((liftM (OW.query second) : OracleComp OW _) >>= fun v ↦
        (liftM (OW.query first) : OracleComp OW _) >>= fun u ↦ k u v) c := by
  have hleft : romRun ((liftM (OW.query first) : OracleComp OW _) >>= fun u ↦
        (liftM (OW.query second) : OracleComp OW _) >>= fun v ↦ k u v) c =
      ((owImpl first).run c >>= fun r ↦ (owImpl second).run r.2 >>= fun s ↦
        (pure ((r.1, s.1), s.2) : ProbComp _)) >>= fun t ↦ romRun (k t.1.1 t.1.2) t.2 := by
    simp only [romRun_query_bind, bind_assoc, pure_bind]
  have hright : romRun ((liftM (OW.query second) : OracleComp OW _) >>= fun v ↦
        (liftM (OW.query first) : OracleComp OW _) >>= fun u ↦ k u v) c =
      ((owImpl second).run c >>= fun s ↦ (owImpl first).run s.2 >>= fun r ↦
        (pure ((r.1, s.1), r.2) : ProbComp _)) >>= fun t ↦ romRun (k t.1.1 t.1.2) t.2 := by
    simp only [romRun_query_bind, bind_assoc, pure_bind]
  rw [hleft, hright]
  exact (evalDistEq_run_query_query_comm first second c).bind_left _

/-- A query commutes past a computation. -/
theorem romRun_query_comm {β γ : Type} (t : OW.Domain) (oa : OracleComp OW β)
    (k : OW.Range t → β → OracleComp OW γ) (c : QueryCache LeanXmss.HashSpec) :
    romRun ((liftM (OW.query t) : OracleComp OW _) >>= fun u ↦ oa >>= fun b ↦ k u b) c =ᵈ
      romRun (oa >>= fun b ↦ (liftM (OW.query t) : OracleComp OW _) >>= fun u ↦ k u b) c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure value => simp only [pure_bind]; exact .rfl
  | query_bind other next ih =>
      simp only [bind_assoc]
      refine (romRun_query_query t other (fun u v ↦ next v >>= fun b ↦ k u b) c).trans ?_
      rw [romRun_query_bind, romRun_query_bind]
      exact EvalDistEq.bind_right _ fun s ↦ ih s.1 s.2

/-- **Two computations commute** in the schemes' lazy random oracle with private coins. -/
theorem romRun_bind_comm {α β γ : Type} (first : OracleComp OW α) (second : OracleComp OW β)
    (k : α → β → OracleComp OW γ) (c : QueryCache LeanXmss.HashSpec) :
    romRun (first >>= fun a ↦ second >>= fun b ↦ k a b) c =ᵈ
      romRun (second >>= fun b ↦ first >>= fun a ↦ k a b) c := by
  induction first using OracleComp.inductionOn generalizing c with
  | pure value => simp only [pure_bind]; exact .rfl
  | query_bind t next ih =>
      simp only [bind_assoc]
      refine EvalDistEq.trans ?_ (romRun_query_comm t second
        (fun u b ↦ next u >>= fun a ↦ k a b) c)
      rw [romRun_query_bind, romRun_query_bind]
      exact EvalDistEq.bind_right _ fun r ↦ ih r.1 r.2

/-- The run of a bind. -/
theorem romRun_bind {α β : Type} (first : OracleComp OW α) (next : α → OracleComp OW β)
    (c : QueryCache LeanXmss.HashSpec) :
    romRun (first >>= next) c = romRun first c >>= fun r ↦ romRun (next r.1) r.2 := by
  simp only [romRun, simulateQ_bind, StateT.run_bind]

end
end LeanVM.E2E
