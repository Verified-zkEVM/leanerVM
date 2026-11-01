module

public import LeanVM.Cost.Decoder.Da
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the children

A child's statement, read off the coverage table (`kidStmt`), and the child itself (`decKid`, its
proof by the reader `wV`); the coverage marks and counts (`markOf`, `countOf`, `slotOf`,
`segCount`), the regions' sizes (`lxSlots`, `lsSlots`) and the child a mark falls in (`kidOf`,
staged: `kidOfStaged`, the count of children passed to `kidOfAt` and its test a function of its
own). Each reads its logarithms by `gLogD D` (`Log.lean`), the logarithm's tables `D` given:
`…D` restates `B1.Main`'s function so, and `…D_tables` (`kidOfStaged_tables`) is the equation at
`D = discreteLogTables`.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Extraction.Fast

@[expose] public section

/-! ## The marks, the counts, the sizes -/

/-- The mark in coverage slot `s` (`markOf`). -/
noncomputable def markOfD (D : DiscreteLogTables) (rd : Reader) (σ : Val) (s : ℕ) : ℕ :=
  gLogD D (cellAt rd (σ (.n 67)) s)

/-- The running count `written[c]` (`countOf`). -/
noncomputable def countOfD (D : DiscreteLogTables) (rd : Reader) (σ : Val) (c : ℕ) : ℕ :=
  gLogD D (cellAt rd (σ (.n 380)) c)

/-- The number of children (`nKids`). -/
def nKidsD (D : DiscreteLogTables) (σ : Val) : ℕ := gLogD D (σ (.n 6))

/-- The regions' sizes (`lxSlots`, `lsSlots`). -/
def lxSlotsD (D : DiscreteLogTables) (σ : Val) : ℕ := gLogD D (σ (.n 40))
def lsSlotsD (D : DiscreteLogTables) (σ : Val) : ℕ := gLogD D (σ (.n 41))

theorem markOfD_tables : markOfD discreteLogTables = markOf := by
  funext rd σ s; unfold markOfD markOf; rw [gLogD_tables]
theorem countOfD_tables : countOfD discreteLogTables = countOf := by
  funext rd σ c; unfold countOfD countOf; rw [gLogD_tables]
theorem nKidsD_tables : nKidsD discreteLogTables = nKids := by
  funext σ; unfold nKidsD nKids; rw [gLogD_tables]
theorem lxSlotsD_tables : lxSlotsD discreteLogTables = lxSlots := by
  funext σ; unfold lxSlotsD lxSlots; rw [gLogD_tables]
theorem lsSlotsD_tables : lsSlotsD discreteLogTables = lsSlots := by
  funext σ; unfold lsSlotsD lsSlots; rw [gLogD_tables]

cost_compile markOfC := markOfD
cost_compile countOfC := countOfD
cost_compile nKidsC := nKidsD
cost_compile lxSlotsC := lxSlotsD
cost_compile lsSlotsC := lsSlotsD

/-! ## The child a mark falls in -/

/-- Whether child `c`'s segment of the running counts ends after the mark `e`. -/
noncomputable def endsAfter (D : DiscreteLogTables) (rd : Reader) (σ : Val) (e c : ℕ) : Bool :=
  decide (e < countOfD D rd σ (c + 1))

/-- The first of children `0 … n - 1` whose segment ends after the mark `e`, or `0`. -/
noncomputable def kidOfAt (D : DiscreteLogTables) (rd : Reader) (σ : Val) (e n : ℕ) : ℕ :=
  ((List.range n).find? (endsAfter D rd σ e)).getD 0

/-- `kidOf`, staged: the number of children (a logarithm) computed by the caller and passed to
`kidOfAt`, whose spec holds at every count (the kernel then never unfolds the logarithm), the test
by partial application. -/
noncomputable def kidOfStaged (D : DiscreteLogTables) (rd : Reader) (σ : Val) (e : ℕ) : ℕ :=
  kidOfAt D rd σ e (nKidsD D σ)

theorem kidOfStaged_tables : kidOfStaged discreteLogTables = kidOf := by
  funext rd σ e
  unfold kidOfStaged kidOfAt endsAfter kidOf
  rw [countOfD_tables, nKidsD_tables]

cost_compile endsAfterC := endsAfter
cost_compile kidOfAtC := kidOfAt
cost_compile kidOfC := kidOfStaged

/-! ## A child -/

/-- The slot of the region `[lo, lo + len)` holding the mark `e` (`slotOf`). -/
noncomputable def slotOfD (D : DiscreteLogTables) (rd : Reader) (σ : Val) (lo len e : ℕ) : ℕ :=
  ((List.range len).find? fun s => decide (markOfD D rd σ (lo + s) = e)).getD 0

/-- The number of slots of the region `[lo, lo + len)` whose marks lie in `[a, b)` (`segCount`). -/
noncomputable def segCountD (D : DiscreteLogTables) (rd : Reader) (σ : Val) (lo len a b : ℕ) : ℕ :=
  ((List.range len).filter fun s =>
    decide (a ≤ markOfD D rd σ (lo + s) ∧ markOfD D rd σ (lo + s) < b)).length

/-- **Child `c`'s statement** (`kidStmt`). -/
noncomputable def kidStmtD (D : DiscreteLogTables) (rd : Reader) (σ : Val) (c : ℕ) :
    NodeStatement :=
  let a := countOfD D rd σ c
  let b := countOfD D rd σ (c + 1)
  let nx := segCountD D rd σ 0 (lxSlotsD D σ) a b
  let ns := segCountD D rd σ (lxSlotsD D σ) (lsSlotsD D σ) a b
  ⟨⟨(List.range nx).map fun j => xmssAt rd (σ (.n 53)) (slotOfD D rd σ 0 (lxSlotsD D σ) (a + j)),
    (List.range ns).map fun j => sphincsAt rd (σ (.n 56))
      (slotOfD D rd σ (lxSlotsD D σ) (lsSlotsD D σ) (a + nx + j)),
    daDigestAt rd σ c⟩,
   deferOfCells (readCells rd (σ (.n 377) * gen ^ (24 * c)) 24)⟩

/-- **Child `c`** (`decKid`). -/
noncomputable def decKidD (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (c : ℕ) : Child :=
  ⟨kidStmtD D rd σ c, fixedOfCells (readCells rd (σ (.n 371) * gen ^ (24 * c)) 24),
    wV (subArgs rd σ c)⟩

theorem slotOfD_tables : slotOfD discreteLogTables = slotOf := by
  funext rd σ lo len e; unfold slotOfD slotOf; rw [markOfD_tables]
theorem segCountD_tables : segCountD discreteLogTables = segCount := by
  funext rd σ lo len a b; unfold segCountD segCount; rw [markOfD_tables]
theorem kidStmtD_tables : kidStmtD discreteLogTables = kidStmt := by
  funext rd σ c
  unfold kidStmtD kidStmt
  rw [countOfD_tables, segCountD_tables, lxSlotsD_tables, lsSlotsD_tables, slotOfD_tables]
theorem decKidD_tables : decKidD discreteLogTables = decKid := by
  funext rd σ wV c; unfold decKidD decKid; rw [kidStmtD_tables]

cost_compile slotOfC := slotOfD
cost_compile segCountC := segCountD
set_option maxHeartbeats 4000000 in
cost_compile kidStmtC := kidStmtD
cost_compile subArgsC := subArgs
cost_compile decKidC := decKidD

end

end LeanVM.Cost.Decoder
