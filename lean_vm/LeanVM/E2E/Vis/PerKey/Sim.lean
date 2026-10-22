/-
  LeanVM.E2E.Vis.PerKey.Sim

  W-vis, P7: generic simulation facts for the per-key reductions. Implementations that agree on
  every query a computation makes simulate it alike, and the routed oracle in a world with a
  signing oracle.
-/

module

public import LeanVM.E2E.Vis.PerKey.Route
public import LeanVM.E2E.Reduction.Lift

/-!
# Simulation facts (W-vis, P7)

* `simulateQ_congr_of_allQueries`: two implementations agreeing on a predicate simulate alike a
  computation all of whose queries satisfy it.
* `liftSig Sig`: the schemes' world inside the world `OW + Sig` of a single-key game, whose
  second part is the signing oracle; `rImpl Sig Pr`: the routed oracle (`routeImpl Pr`) there,
  its forwarded queries asked in `OW + Sig` (`run_simulateQ_rImpl`).
-/

namespace LeanVM.E2E

open OracleSpec OracleComp

@[expose] public section

section Congr

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **Implementations agreeing on every query made simulate alike.** -/
theorem simulateQ_congr_of_allQueries {α : Type} (P : ι → Prop) (impl impl' : QueryImpl spec m)
    (h : ∀ t, P t → impl t = impl' t) {oa : OracleComp spec α} (hoa : AllQueriesSatisfy oa P) :
    simulateQ impl oa = simulateQ impl' oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hoa
    rw [simulateQ_query_bind, simulateQ_query_bind]
    simp only [OracleQuery.input_query, monadLift_self]
    rw [h t hoa.1]
    exact bind_congr fun u ↦ ih u (hoa.2 u)

end Congr

section Sig

variable {κ : Type} (Sig : OracleSpec.{0, 0} κ)

/-- The schemes' world inside `OW + Sig`. -/
noncomputable def liftSigImpl : QueryImpl OW (OracleComp (OW + Sig)) :=
  fun t ↦ (liftM ((OW + Sig).query (.inl t)) : OracleComp (OW + Sig) _)

/-- A computation of the schemes' world inside `OW + Sig`. -/
noncomputable def liftSig {α : Type} (oa : OracleComp OW α) : OracleComp (OW + Sig) α :=
  simulateQ (liftSigImpl Sig) oa

/-- **The routed oracle inside `OW + Sig`.** -/
noncomputable def rImpl (Pr : List UInt8 → Prop) [DecidablePred Pr] :
    QueryImpl OW (StateT (QueryCache LeanXmss.HashSpec) (OracleComp (OW + Sig))) :=
  (liftSigImpl Sig).mapStateTBase (routeImpl Pr)

/-- The routed run inside `OW + Sig` is the routed run, lifted. -/
theorem run_simulateQ_rImpl (Pr : List UInt8 → Prop) [DecidablePred Pr] {α : Type}
    (oa : OracleComp OW α) (c : QueryCache LeanXmss.HashSpec) :
    (simulateQ (rImpl Sig Pr) oa).run c = liftSig Sig ((simulateQ (routeImpl Pr) oa).run c) :=
  (QueryImpl.simulateQ_mapStateTBase_run _ _ oa c).symm

end Sig

end
end LeanVM.E2E
