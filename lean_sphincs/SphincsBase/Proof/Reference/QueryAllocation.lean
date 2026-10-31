import SphincsBase.Proof.Base.QueryCapAccounting
namespace SphincsBase.QueryCap

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Index : Type} {spec : OracleSpec Index} {Result : Type}

noncomputable def recorded (computation : OracleComp spec Result) : OracleComp spec (Result × List Index) :=
  OracleComp.construct (fun result => pure (result, []))
    (fun input _ next => do
      let answer ← liftM (spec.query input)
      let result ← next answer
      pure (result.1, input :: result.2)) computation

theorem recorded_pure (result : Result) : recorded (pure result : OracleComp spec Result) = pure (result, []) := rfl

theorem recorded_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec Result) :
    recorded (liftM (spec.query input) >>= next) = (do
      let answer ← liftM (spec.query input)
      let result ← recorded (next answer)
      pure (result.1, input :: result.2)) := rfl

def calls (selected : Index → Prop) [DecidablePred selected] (inputs : List Index) : Nat :=
  inputs.countP (fun input => decide (selected input))

theorem calls_nil (selected : Index → Prop) [DecidablePred selected] : calls selected [] = 0 := rfl

theorem calls_cons (selected : Index → Prop) [DecidablePred selected] (input : Index) (inputs : List Index) :
    calls selected (input :: inputs) = (if selected input then 1 else 0) + calls selected inputs := by
  simp [calls, List.countP_cons, Nat.add_comm]

theorem recorded_counted (selected : Index → Prop) [DecidablePred selected] (computation : OracleComp spec Result) :
    (fun result => (result.1, calls selected result.2)) <$> recorded computation = counted selected computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [recorded_pure, counted_pure, map_pure, calls_nil]
  | query_bind input next ih =>
      simp only [recorded_query_bind, counted_query_bind, map_bind, map_pure, calls_cons]
      congr 1
      funext answer
      rw [← ih answer]
      simp only [bind_map_left]

theorem counted_query (selected : Index → Prop) [DecidablePred selected] (input : spec.Domain) :
    counted selected (liftM (spec.query input) : OracleComp spec _) =
      (fun answer => (answer, if selected input then 1 else 0)) <$> (liftM (spec.query input) : OracleComp spec _) := by
  have h := counted_query_bind selected input (fun answer => pure answer)
  simpa only [bind_pure, counted_pure, pure_bind, Nat.add_zero, bind_pure_comp, map_pure] using h

end SphincsBase.QueryCap
