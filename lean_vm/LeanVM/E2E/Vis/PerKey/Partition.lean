/-
  LeanVM.E2E.Vis.PerKey.Partition

  W-vis, P7a: two lazy random oracles on a static partition of the inputs are one. The routed
  oracle (`routeImpl`) followed by the schemes' lazy oracle is the lazy oracle, the caches merged;
  routing is transparent on a computation that never asks the private class; and it forwards only
  the hash queries outside the private class.
-/

module

public import LeanVM.E2E.Vis.PerKey.Route
public import LeanVM.E2E.Vis.WalkXmss
public import LeanVM.E2E.Reduction.Count
public import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# The partition lemma (W-vis, P7a)

`routeImpl Pr` (`Vis/PerKey/Route.lean`) answers a hash query in the class `Pr` from a private lazy
oracle, its cache the state, and forwards coins and every other hash query. Run against the
schemes' lazy random oracle `owImpl`, it is `owImpl` itself:

* `evalDistEq_route_run`: from a private cache `cPriv` and a public cache `cPub`, the routed run
  against `owImpl`, its two final caches merged (`mergeCache Pr`), has the distribution of
  `owImpl`'s run from the merged cache. One step suffices (`evalDistEq_route_step`): a query in `Pr` is
  answered from the private cache, which the merged cache shows there, and a fresh private answer is
  `owImpl`'s coins' uniform 256 bits, like a fresh public one; any other query is answered from the
  public cache, which the merged cache shows there. No invariant on the caches is needed: the merge
  reads each cache only on its own side of the partition.
* `evalDistEq_route`: from an empty private cache and a public cache with no entry in `Pr`, whose
  merge is the public cache.
* `simulateQ_route_of_sat`: on a computation that never asks a hash input in `Pr` (`OffPr Pr`),
  routing changes nothing: the run returns the computation's value and the private cache unchanged.
* `isQueryBoundP_route`: the routed run's hash queries are at most the computation's hash queries
  outside `Pr` (a fresh private answer asks only coins).
-/

namespace LeanVM.E2E

open OracleSpec OracleComp

@[expose] public section

variable (Pr : List UInt8 → Prop) [DecidablePred Pr]

/-! ## The merged cache -/

theorem mergeCache_apply (cPriv cPub : QueryCache LeanXmss.HashSpec) (x : List UInt8) :
    mergeCache Pr cPriv cPub x = if Pr x then cPriv x else cPub x := rfl

/-- From an empty private cache, a public cache with no entry in `Pr` is its own merge. -/
theorem mergeCache_empty {c : QueryCache LeanXmss.HashSpec} (hc : ∀ x, Pr x → c x = none) :
    mergeCache Pr ∅ c = c := by
  refine QueryCache.ext fun x ↦ ?_
  rw [mergeCache_apply]
  split
  · next h => rw [hc x h]; rfl
  · rfl

/-- A private answer cached at a point of `Pr` is the merged cache's. -/
theorem mergeCache_cacheQuery_priv {x : List UInt8} (hx : Pr x)
    (cPriv cPub : QueryCache LeanXmss.HashSpec) (u : LeanXmss.HashOutput) :
    mergeCache Pr (cPriv.cacheQuery x u) cPub = (mergeCache Pr cPriv cPub).cacheQuery x u := by
  refine QueryCache.ext fun y ↦ ?_
  by_cases hy : y = x
  · subst hy
    simp [mergeCache_apply, hx, QueryCache.cacheQuery_self]
  · simp [mergeCache_apply, QueryCache.cacheQuery_of_ne _ _ hy]

/-- A public answer cached at a point outside `Pr` is the merged cache's. -/
theorem mergeCache_cacheQuery_pub {x : List UInt8} (hx : ¬ Pr x)
    (cPriv cPub : QueryCache LeanXmss.HashSpec) (u : LeanXmss.HashOutput) :
    mergeCache Pr cPriv (cPub.cacheQuery x u) = (mergeCache Pr cPriv cPub).cacheQuery x u := by
  refine QueryCache.ext fun y ↦ ?_
  by_cases hy : y = x
  · subst hy
    simp [mergeCache_apply, hx, QueryCache.cacheQuery_self]
  · simp [mergeCache_apply, QueryCache.cacheQuery_of_ne _ _ hy]

/-! ## The partition lemma -/

/-- The routed oracle's step, forwarding a query: the answer with the private cache unchanged. -/
theorem routeImpl_run_fwd (t : OW.Domain) (ht : ∀ x, t = .inr x → ¬ Pr x)
    (c : QueryCache LeanXmss.HashSpec) :
    (routeImpl Pr t).run c = (fun u ↦ (u, c)) <$> (liftM (OW.query t) : OracleComp OW _) := by
  rcases t with n | x
  · simp [routeImpl]
  · simp [routeImpl, ht x rfl]

/-- **One step of the partition lemma.** -/
theorem evalDistEq_route_step (t : OW.Domain) (cPriv cPub : QueryCache LeanXmss.HashSpec) :
    (fun z ↦ (z.1.1, mergeCache Pr z.1.2 z.2)) <$>
        (simulateQ owImpl ((routeImpl Pr t).run cPriv)).run cPub =ᵈ
      (owImpl t).run (mergeCache Pr cPriv cPub) := by
  rcases t with n | x
  · rw [routeImpl_run_fwd Pr _ (by simp) cPriv]
    simp [unifFwdImpl, Functor.map_map]
  · by_cases hx : Pr x
    · change (fun z ↦ (z.1.1, mergeCache Pr z.1.2 z.2)) <$>
          (simulateQ owImpl ((if Pr x then StateT.mk fun c ↦
            match c x with
            | some u => pure (u, c)
            | none => (fun u ↦ (u, c.cacheQuery x u)) <$> freshBits
            else _ : StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) _).run cPriv)).run
              cPub =ᵈ (randomOracle x).run (mergeCache Pr cPriv cPub)
      simp only [hx, ite_true]
      rw [randomOracle.run_eq, mergeCache_apply]
      simp only [hx, ite_true]
      rcases h : cPriv x with _ | u
      · simp only [StateT.run_mk, h, simulateQ_map, StateT.run_map, freshBits,
          roSim.run_liftM, Functor.map_map]
        simp only [mergeCache_cacheQuery_priv Pr hx]
        rw [map_eq_bind_pure_comp]
        exact .rfl
      · simp only [StateT.run_mk, h, simulateQ_pure, StateT.run_pure, map_pure]
        rfl
    · rw [routeImpl_run_fwd Pr _ (by simp [hx]) cPriv, simulateQ_map, StateT.run_map,
        simulateQ_spec_query, Functor.map_map]
      change _ <$> (randomOracle x).run cPub =ᵈ (randomOracle x).run (mergeCache Pr cPriv cPub)
      rw [randomOracle.run_eq, randomOracle.run_eq, mergeCache_apply]
      simp only [hx, ite_false]
      rcases h : cPub x with _ | u
      · simp [mergeCache_cacheQuery_pub Pr hx]
      · simp

/-- **The partition lemma**, from any caches: the routed run against the lazy oracle, its caches
merged, is the lazy oracle's run from the merged cache. -/
theorem evalDistEq_route_run {α : Type} (oa : OracleComp OW α)
    (cPriv cPub : QueryCache LeanXmss.HashSpec) :
    (fun z ↦ (z.1.1, mergeCache Pr z.1.2 z.2)) <$>
        (simulateQ owImpl ((simulateQ (routeImpl Pr) oa).run cPriv)).run cPub =ᵈ
      (simulateQ owImpl oa).run (mergeCache Pr cPriv cPub) := by
  induction oa using OracleComp.inductionOn generalizing cPriv cPub with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun p ↦ ih p.1.1 p.1.2 p.2) ?_
    rw [show ((simulateQ owImpl ((routeImpl Pr t).run cPriv)).run cPub >>= fun p ↦
        (simulateQ owImpl (k p.1.1)).run (mergeCache Pr p.1.2 p.2)) =
      ((fun z ↦ (z.1.1, mergeCache Pr z.1.2 z.2)) <$>
        (simulateQ owImpl ((routeImpl Pr t).run cPriv)).run cPub) >>= fun p ↦
          (simulateQ owImpl (k p.1)).run p.2 by rw [bind_map_left]]
    exact (evalDistEq_route_step Pr t cPriv cPub).bind fun _ ↦ .rfl

/-- **The partition lemma** (P7a): from an empty private cache and a public cache with no entry
in `Pr`, the routed run against the lazy oracle, its caches merged, is the lazy oracle. -/
theorem evalDistEq_route {α : Type} (oa : OracleComp OW α) (c : QueryCache LeanXmss.HashSpec)
    (hc : ∀ x, Pr x → c x = none) :
    (fun z ↦ (z.1.1, mergeCache Pr z.1.2 z.2)) <$>
      (simulateQ owImpl ((simulateQ (routeImpl Pr) oa).run ∅)).run c =ᵈ
    (simulateQ owImpl oa).run c := by
  have h := evalDistEq_route_run Pr oa ∅ c
  rw [mergeCache_empty Pr hc] at h
  exact h

/-! ## Transparency and the count -/

/-- A query that is not a hash input in `Pr`. -/
def OffPr : OW.Domain → Prop
  | .inl _ => True
  | .inr x => ¬ Pr x

instance : DecidablePred (OffPr Pr)
  | .inl _ => isTrue trivial
  | .inr x => inferInstanceAs (Decidable (¬ Pr x))

omit [DecidablePred Pr] in
theorem offPr_iff (t : OW.Domain) : OffPr Pr t ↔ ∀ x, t = .inr x → ¬ Pr x := by
  rcases t with n | x
  · simp [OffPr]
  · simp [OffPr]

/-- **Routing is transparent** on a computation that never asks a hash input in `Pr`. -/
theorem simulateQ_route_of_sat {α : Type} {oa : OracleComp OW α} (h : QueriesSat oa (OffPr Pr))
    (c : QueryCache LeanXmss.HashSpec) :
    (simulateQ (routeImpl Pr) oa).run c = (·, c) <$> oa := by
  rw [queriesSat_iff] at h
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [routeImpl_run_fwd Pr t ((offPr_iff Pr t).mp h.1) c, bind_map_left]
    exact bind_congr fun u ↦ ih u (h.2 u)

/-- Every computation asks only queries in `True`. -/
theorem walk_allQueriesSatisfy_true {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (oa : OracleComp spec α) : AllQueriesSatisfy oa (fun _ ↦ ¬ False) := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨not_false, ih⟩

/-- **The count**: the routed run's hash queries are at most the computation's hash queries
outside `Pr`. -/
theorem isQueryBoundP_route {α : Type} {oa : OracleComp OW α} {n : ℕ}
    (h : IsQueryBoundP oa (fun t ↦ IsHashW t ∧ OffPr Pr t) n) (c : QueryCache LeanXmss.HashSpec) :
    IsQueryBoundP ((simulateQ (routeImpl Pr) oa).run c) IsHashW n := by
  refine IsQueryBoundP.simulateQ_run_StateT_of_step h (fun t s ↦ ?_) c
  rcases t with m | x
  · rw [routeImpl_run_fwd Pr _ (by simp) s, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    simp [IsHashW]
  · by_cases hx : Pr x
    · have hp : ¬ (IsHashW (.inr x : OW.Domain) ∧ OffPr Pr (.inr x)) := fun h ↦ h.2 hx
      simp only [hp, ↓reduceIte]
      change IsQueryBoundP ((if Pr x then StateT.mk fun c ↦
            match c x with
            | some u => pure (u, c)
            | none => (fun u ↦ (u, c.cacheQuery x u)) <$> freshBits
            else _ : StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) _).run s) IsHashW 0
      simp only [hx, ↓reduceIte, StateT.run_mk]
      rcases s x with _ | u
      · rw [isQueryBoundP_map_iff, freshBits]
        exact IsQueryBoundP.liftComp_subSpec (p := fun _ ↦ False) (fun _ ↦ ⟨False.elim, fun h ↦ h⟩)
          (walk_isQueryBoundP_of_all (walk_allQueriesSatisfy_true _) 0)
      · trivial
    · have hp : IsHashW (.inr x : OW.Domain) ∧ OffPr Pr (.inr x) := ⟨trivial, hx⟩
      simp only [hp, and_self, ↓reduceIte]
      rw [routeImpl_run_fwd Pr _ (by simp [hx]) s, isQueryBoundP_map_iff,
        isQueryBoundP_query_iff]
      intro; exact Nat.one_pos

end
end LeanVM.E2E
