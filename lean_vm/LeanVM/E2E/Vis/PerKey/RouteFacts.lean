/-
  LeanVM.E2E.Vis.PerKey.RouteFacts

  W-vis, P7b: deterministic facts about the routed oracle. Routing is the identity on a
  computation that never queries the private class, and two classes route alike a computation
  whose queries they classify alike.
-/

module

public import LeanVM.E2E.Vis.PerKey.Sim

/-!
# The routed oracle: deterministic facts (W-vis, P7b)

* `simulateQ_routeImpl_congr`: two classes that agree on every hash query of a computation route
  it alike.
* `simulateQ_routeImpl_of_off`: routing a computation none of whose hash queries is in the class
  forwards it, the private cache untouched.
* `allQueriesSatisfy_liftM_hash`, `allQueriesSatisfy_sLift`: the queries of a scheme's computation
  lifted into the schemes' world are its hash queries.
-/

namespace LeanVM.E2E

open OracleSpec OracleComp

@[expose] public section

/-- A coin query is forwarded. -/
theorem routeImpl_inl (Pr : List UInt8 → Prop) [DecidablePred Pr] (n : ℕ) :
    routeImpl Pr (.inl n) = (liftM (liftM (OW.query (.inl n)) : OracleComp OW _) :
      StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) _) := rfl

/-- A hash query outside the class is forwarded. -/
theorem routeImpl_inr_of_not (Pr : List UInt8 → Prop) [DecidablePred Pr] {x : List UInt8}
    (hx : ¬ Pr x) :
    routeImpl Pr (.inr x) = (liftM (liftM (OW.query (.inr x)) : OracleComp OW _) :
      StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) _) := by
  simp only [routeImpl, hx, ↓reduceIte]

/-- Two classes agreeing at a query route it alike. -/
theorem routeImpl_congr (Pr Pr' : List UInt8 → Prop) [DecidablePred Pr] [DecidablePred Pr']
    (t : OW.Domain) (h : ∀ x, t = .inr x → (Pr x ↔ Pr' x)) : routeImpl Pr t = routeImpl Pr' t := by
  rcases t with n | x
  · rfl
  · have hx := h x rfl
    by_cases hp : Pr x
    · simp only [routeImpl, hp, hx.mp hp, ↓reduceIte]
    · simp only [routeImpl, hp, (not_congr hx).mp hp, ↓reduceIte]

/-- **Two classes agreeing on every hash query of a computation route it alike.** -/
theorem simulateQ_routeImpl_congr (Pr Pr' : List UInt8 → Prop) [DecidablePred Pr]
    [DecidablePred Pr'] {α : Type} {oa : OracleComp OW α}
    (h : AllQueriesSatisfy oa fun t ↦ ∀ x, t = .inr x → (Pr x ↔ Pr' x)) :
    simulateQ (routeImpl Pr) oa = simulateQ (routeImpl Pr') oa :=
  simulateQ_congr_of_allQueries _ _ _ (fun t ht ↦ routeImpl_congr Pr Pr' t ht) h

/-- The pass-through of the schemes' world under a state. -/
theorem simulateQ_liftM_stateT {σ : Type} {α : Type} (oa : OracleComp OW α) :
    simulateQ (fun t ↦ (liftM (liftM (OW.query t) : OracleComp OW _) :
      StateT σ (OracleComp OW) _)) oa = liftM oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [simulateQ_query_bind, liftM_bind]
    simp only [OracleQuery.input_query, monadLift_self]
    exact bind_congr fun u ↦ ih u

/-- **Routing forwards a computation none of whose hash queries is in the class.** -/
theorem simulateQ_routeImpl_of_off (Pr : List UInt8 → Prop) [DecidablePred Pr] {α : Type}
    {oa : OracleComp OW α} (h : AllQueriesSatisfy oa fun t ↦ ∀ x, t = .inr x → ¬ Pr x) :
    simulateQ (routeImpl Pr) oa = liftM oa := by
  rw [← simulateQ_liftM_stateT oa]
  refine simulateQ_congr_of_allQueries _ _ _ (fun t ht ↦ ?_) h
  rcases t with n | x
  · rfl
  · exact routeImpl_inr_of_not Pr (ht x rfl)

/-- The queries of a leanXMSS computation lifted into the schemes' world are its hash queries. -/
theorem allQueriesSatisfy_liftM_hash {α : Type} {oa : OracleComp LeanXmss.HashSpec α}
    {P : List UInt8 → Prop} (h : AllQueriesSatisfy oa P) :
    AllQueriesSatisfy (liftM oa : OracleComp OW α) fun t ↦ ∀ x, t = .inr x → P x := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact allQueriesSatisfy_pure _ _
  | query_bind x k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [liftM_bind]
    change AllQueriesSatisfy ((liftM (OW.query (.inr x)) : OracleComp OW _) >>= fun u ↦ liftM (k u))
      _
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨fun y hy ↦ by cases hy; exact h.1, fun u ↦ ih u (h.2 u)⟩

/-- The queries of a leanSPHINCS computation lifted into the schemes' world are its hash queries. -/
theorem allQueriesSatisfy_sLift {α : Type} {oa : OracleComp Sphincs.HashSpec α}
    {P : List UInt8 → Prop} (h : AllQueriesSatisfy oa P) :
    AllQueriesSatisfy (sLift oa) fun t ↦ ∀ x, t = .inr x → P x := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact allQueriesSatisfy_pure _ _
  | query_bind x k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    unfold sLift
    rw [liftM_bind]
    change AllQueriesSatisfy ((liftM (OW.query (.inr x)) : OracleComp OW _) >>= fun u ↦ sLift (k u))
      _
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨fun y hy ↦ by cases hy; exact h.1, fun u ↦ ih u (h.2 u)⟩

end
end LeanVM.E2E
