import SphincsBase.Proof.Base.Prelude
import SphincsBase.Proof.Hypertree.Honest
import VCVio.EvalDist.Monad.UniformTable
import VCVio.OracleComp.Constructions.SampleableType.Measure
namespace SphincsBase.Concrete.FiniteGraphSampling

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false

variable {Node Cell Answer State : Type} [DecidableEq Cell]

def read (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (table : Cell → Answer) : List Node → State → State
  | [], state => state
  | node :: nodes, state => read input advance table nodes (advance node (table (input node state)) state)

def Separated (input : Node → State → Cell) : Prop :=
  ∀ left right, left ≠ right → ∀ before after, input left before ≠ input right after

theorem read_update_of_not_mem (input : Node → State → Cell)
    (advance : Node → Answer → State → State) (hsep : Separated input)
    (table : Cell → Answer) (nodes : List Node) (node : Node) (hnode : node ∉ nodes)
    (before state : State) (answer : Answer) :
    read input advance (Function.update table (input node before) answer) nodes state =
      read input advance table nodes state := by
  induction nodes generalizing state with
  | nil => rfl
  | cons first rest ih =>
      have hne : first ≠ node := fun h => hnode (by simp [h])
      have hrest : node ∉ rest := fun h => hnode (List.mem_cons_of_mem _ h)
      simp only [read, Function.update_of_ne (hsep first node hne state before)]
      exact ih hrest _

variable [_root_.Finite Cell] [_root_.Finite Answer] [Nonempty Answer]
  [SampleableType Answer] [SampleableType (Cell → Answer)]

noncomputable def plant (input : Node → State → Cell)
    (advance : Node → Answer → State → State) : List Node → State → ProbComp (State × (Cell → Answer))
  | [], state => do
      let table ← $ᵗ (Cell → Answer)
      pure (state, table)
  | node :: nodes, state => do
      let answer ← $ᵗ Answer
      let result ← plant input advance nodes (advance node answer state)
      pure (result.1, Function.update result.2 (input node state) answer)

theorem evalDist_table_extract {Result : Type} (cell : Cell)
    (next : (Cell → Answer) → Answer → ProbComp Result) :
    (do let table ← ($ᵗ (Cell → Answer) : ProbComp _); next table (table cell)) =ᵈ (do
        let answer ← ($ᵗ Answer : ProbComp _)
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        next (Function.update table cell answer) answer) := by
  let : MeasurableSpace Answer := ⊤
  let : MeasurableSpace Result := ⊤
  exact EvalDistEq.of_evalDist_eq <| evalDist_bind_cell_extract ($ᵗ Answer) ($ᵗ (Cell → Answer))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample cell next

end SphincsBase.Concrete.FiniteGraphSampling
