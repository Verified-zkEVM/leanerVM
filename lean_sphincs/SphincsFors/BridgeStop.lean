import SphincsFors.BridgeAssembly

/-! Probabilistic semantics of the graph-view game with an explicit cost trace, and the exact
"identical until the seed is named" comparison for two fixed answer functions. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.Stop

open Completeness HiddenCost GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Private draws are real; ordinary queries read a fixed function; reveals read a fixed table;
honest-work ticks are free here (their cost is kept in the trace). -/
noncomputable def fixedCostP (f : HashInput → HashOutput) (table : HiddenGraph.Table) :
    QueryImpl CostSpec ProbComp
  | .inl (.inl draw) => liftM (unifSpec.query draw)
  | .inl (.inr (.inl input)) => pure (f input)
  | .inl (.inr (.inr coordinate)) => pure (table coordinate)
  | .inr _ => pure ()

noncomputable def costRun {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp CostSpec α) : ProbComp (α × List (Entry HashInput)) :=
  simulateQ (fixedCostP f table) (trace computation)

theorem costRun_pure {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table) (value : α) :
    costRun f table (pure value) = pure (value, []) := by
  simp [costRun, trace_pure]

theorem costRun_query_bind {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (input : CostSpec.Domain) (next : CostSpec.Range input → OracleComp CostSpec α) :
    costRun f table (liftM (CostSpec.query input) >>= next) =
      fixedCostP f table input >>= fun answer =>
        (fun result => (result.1, recorded input ++ result.2)) <$> costRun f table (next answer) := by
  rw [costRun, trace_query_bind, simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_map, costRun]

/-- The PMF handler underneath the cost writer. -/
noncomputable def fixedCostPMF (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl CostSpec PMF :=
  fun | .inl request => GraphView.fixedSource f table request | .inr _ => PMF.pure ()

/-- Writer cost is the cost of the recorded trace. -/
theorem run_withAddCost_trace {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (impl : QueryImpl CostSpec m) (computation : OracleComp CostSpec α) :
    (simulateQ (impl.withAddCost sourceCost) computation).run =
      (fun result => (result.1, Multiplicative.ofAdd (traceCost result.2))) <$>
        simulateQ impl (trace computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [trace_pure, traceCost]
  | query_bind input next ih =>
      rw [trace_query_bind, simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query,
        WriterT.run_bind, QueryImpl.withAddCost_apply]
      simp only [WriterT.run_bind, map_bind, simulateQ_map, ih]
      simp [map_eq_bind_pure_comp, bind_assoc, traceCost_append,
        recorded_cost, ← ofAdd_add]

theorem liftM_id_pmf {α : Type} (x : α) : (liftM (show Id α from x) : PMF α) = PMF.pure x := rfl

theorem evalDist_liftM_id {α : Type} (x : α) :
    (liftM (show Id α from x) : PMF α) =ᵈ (pure x : ProbComp α) := by
  rw [liftM_id_pmf]
  exact Assembly.evalDistEq_pure x

/-! ### Identical until a marked ordinary input -/

/-- Some ordinary input of the trace satisfies the marker. -/
def Hits (marked : HashInput → Prop) (entries : List (Entry HashInput)) : Prop :=
  ∃ input, Sum.inl input ∈ entries ∧ marked input

theorem hits_append_recorded (marked : HashInput → Prop) (input : CostSpec.Domain)
    (entries : List (Entry HashInput))
    (hinput : ∀ bytes, input = .inl (.inr (.inl bytes)) → ¬marked bytes) :
    Hits marked (recorded input ++ entries) ↔ Hits marked entries := by
  constructor
  · rintro ⟨bytes, hmem, hmarked⟩
    rw [List.mem_append] at hmem
    rcases hmem with hrec | htail
    · rcases input with (draw | (other | coordinate)) | amount <;> simp [recorded] at hrec
      subst other
      exact absurd hmarked (hinput bytes rfl)
    · exact ⟨bytes, htail, hmarked⟩
  · rintro ⟨bytes, hmem, hmarked⟩
    exact ⟨bytes, List.mem_append_right _ hmem, hmarked⟩

/-! ### Capping the original budget -/

theorem cap_pure' {α : Type} (value : α) (budget : Nat) :
    cap (pure value : OracleComp CostSpec α) budget = pure (some value) := rfl

theorem cap_query_bind' {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) (budget : Nat) :
    cap (liftM (CostSpec.query input) >>= next) budget =
      if sourceCost input ≤ budget then
        liftM (CostSpec.query input) >>= fun value => cap (next value) (budget - sourceCost input)
      else pure none := rfl

end SphincsFors.Security.Stop
