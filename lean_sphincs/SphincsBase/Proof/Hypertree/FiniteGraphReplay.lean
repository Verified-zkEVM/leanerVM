import SphincsBase.Proof.Base.Prelude
import SphincsBase.Proof.Hypertree.FiniteGraphSampling
namespace SphincsBase.Concrete.FiniteGraphSampling

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false

variable {Node Cell Answer State : Type} [DecidableEq Node] [DecidableEq Cell]

def replay (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (answers : Node → Answer) (table : Cell → Answer) : List Node → State → State × (Cell → Answer)
  | [], state => (state, table)
  | node :: nodes, state =>
      let result := replay input advance answers table nodes (advance node (answers node) state)
      (result.1, Function.update result.2 (input node state) (answers node))

omit [DecidableEq Node] in
theorem replay_congr (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (left right : Node → Answer) (table : Cell → Answer) (nodes : List Node)
    (hagrees : ∀ node ∈ nodes, left node = right node) (state : State) :
    replay input advance left table nodes state = replay input advance right table nodes state := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node nodes ih =>
      have hfirst := hagrees node List.mem_cons_self
      have hrest := ih (fun other hother => hagrees other (List.mem_cons_of_mem _ hother))
      simp only [replay, hfirst, hrest]

theorem replay_update_of_not_mem (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (answers : Node → Answer) (table : Cell → Answer) (nodes : List Node)
    (node : Node) (hnode : node ∉ nodes) (answer : Answer) (state : State) :
    replay input advance (Function.update answers node answer) table nodes state =
      replay input advance answers table nodes state := by
  apply replay_congr
  intro other hother
  have hne : other ≠ node := by
    intro heq
    subst other
    exact hnode hother
  rw [Function.update_of_ne hne]

def patch (input : Node → Cell) (answers : Node → Answer) (table : Cell → Answer) : List Node → Cell → Answer
  | [] => table
  | node :: nodes => Function.update (patch input answers table nodes) (input node) (answers node)

variable [_root_.Finite Node] [_root_.Finite Cell] [_root_.Finite Answer] [Nonempty Answer]
  [SampleableType Answer] [SampleableType (Node → Answer)] [SampleableType (Cell → Answer)]

end SphincsBase.Concrete.FiniteGraphSampling
