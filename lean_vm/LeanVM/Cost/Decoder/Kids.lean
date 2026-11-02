module

public import LeanVM.Cost.Decoder.Da
public import LeanVM.Guest.Fast.Search
import all LeanVM.Guest.B1.Main.Interface
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# The guest decoder's compiled chain: the children

A child's statement, read off the coverage table (`kidStmt`), and the child itself (`decKid`, its
proof by the reader `wV`); the coverage marks and counts (`markOf`, `countOf`, `slotOf`,
`segCount`), the regions' sizes (`lxSlots`, `lsSlots`) and the child a mark falls in (`kidOf`).
Each reads its logarithms by `gLogD D` (`Log.lean`), the logarithm's tables `D` given: `…D`
restates `B1.Main`'s function so, and `…D_tables` is the equation at `D = discreteLogTables`.

The searches are not compiled as written (a scan of a region per query, quadratic in the counts):
tables built once by the caller (`Staged.lean`) answer them, on every input
(`Guest/Fast/Search.lean`):

* `regionTable D rd cover lo len`: the region's marks (one logarithm per slot) sorted with their
  slots (`coverTable`); `slotIn` of it is `slotOfD` (`slotIn_regionTable`), `countIn` of it
  `segCountD` (`countIn_regionTable`);
* `kidMax D rd w n`: the running maxima of the children's running counts; `kidIn` of it is
  `kidOfStaged` (`kidIn_kidMax`);
* `kidStmtT`, `decKidT`: a child's statement and the child off the two regions' tables, `main`'s
  words the loops read (`written`, the tables' pointers) passed as values, the slots' addresses by
  powers in `K` (`xmssAtK`); `kidStmtT_eq`, `decKidT_eq`: at the tables built they are `kidStmtD`,
  `decKidD`.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Extraction.Fast LeanVM.Guest.Fast

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



/-! ## The searches' compiled pieces -/

section Tables

attribute [local instance] lexOrd

cost_compile lowerBoundC measure fun _ _ lo hi ↦ hi - lo := lowerBound
cost_compile mergeNewerCoverC measure fun a b ↦ a.length + b.length := @mergeNewer (ℕ × ℕ) ℕ _
cost_compile levelMergeCoverC := @Level.merge (ℕ × ℕ) ℕ _ _ _
cost_compile carryCoverC measure fun _ ls ↦ ls.length := @carry (ℕ × ℕ) ℕ _ _ _
cost_compile insertCoverC := @SortedMap.insert (ℕ × ℕ) ℕ _ _ _
cost_compile coverInsertC := coverInsert
cost_compile mergeLevelC := mergeLevel
cost_compile flattenLevelsC := flattenLevels
cost_compile coverKeysC := coverKeys
cost_compile coverTableC := coverTable
cost_compile slotInC := slotIn
cost_compile countInC := countIn
cost_compile prefixMaxC measure fun _ xs ↦ xs.length := prefixMax
cost_compile kidInC := kidIn

end Tables

/-! ## The coverage tables -/

/-- A mark and its slot. -/
def markPairOf (m s : ℕ) : ℕ × ℕ := (m, s)

/-- Slot `s` of the region from `lo` of the coverage table at `cover`: its mark (a logarithm) and
`s`. -/
noncomputable def markPair (D : DiscreteLogTables) (rd : Reader) (cover : E) (lo s : ℕ) : ℕ × ℕ :=
  markPairOf (gLogD D (cellAt rd cover (lo + s))) s

/-- **The coverage table of the region `[lo, lo + len)`**: its marks sorted, with their slots
(`coverTable`), each mark read once. -/
noncomputable def regionTable (D : DiscreteLogTables) (rd : Reader) (cover : E) (lo len : ℕ) :
    Array ℕ × Array ℕ :=
  coverTable ((List.range len).map (markPair D rd cover lo))

theorem regionTable_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val) (lo len : ℕ) :
    regionTable D rd (σ (.n 67)) lo len =
      coverTable (regionPairs (fun s ↦ markOfD D rd σ (lo + s)) len) := rfl

/-- **The table's first slot is `slotOf`'s.** -/
theorem slotIn_regionTable (D : DiscreteLogTables) (rd : Reader) (σ : Val) (lo len e : ℕ) :
    slotIn (regionTable D rd (σ (.n 67)) lo len).1 (regionTable D rd (σ (.n 67)) lo len).2 e =
      slotOfD D rd σ lo len e := by
  rw [regionTable_eq, slotIn_coverTable]; rfl

/-- **The table's count is `segCount`'s.** -/
theorem countIn_regionTable (D : DiscreteLogTables) (rd : Reader) (σ : Val) (lo len a b : ℕ) :
    countIn (regionTable D rd (σ (.n 67)) lo len).1 a b = segCountD D rd σ lo len a b := by
  rw [regionTable_eq, countIn_coverTable]; rfl

/-- The running count `written[c]` at `w = written` (`countOf`). -/
noncomputable def countAtW (D : DiscreteLogTables) (rd : Reader) (w : E) (c : ℕ) : ℕ := gLogD D (cellAt rd w c)

/-- Child `c`'s segment's end `written[c + 1]`. -/
noncomputable def countNext (D : DiscreteLogTables) (rd : Reader) (w : E) (c : ℕ) : ℕ :=
  gLogD D (cellAt rd w (c + 1))

/-- **The running maxima of the children's segments' ends**, `n` children. -/
noncomputable def kidMax (D : DiscreteLogTables) (rd : Reader) (w : E) (n : ℕ) : Array ℕ :=
  (prefixMax 0 ((List.range n).map (countNext D rd w))).toArray

/-- **The child of the running maxima is `kidOf`'s.** -/
theorem kidIn_kidMax (D : DiscreteLogTables) (rd : Reader) (σ : Val) (e : ℕ) :
    kidIn (kidMax D rd (σ (.n 380)) (nKidsD D σ)) e = kidOfStaged D rd σ e :=
  kidIn_prefixMax (fun c ↦ countOfD D rd σ c) (nKidsD D σ) e

cost_compile markPairOfC := markPairOf
cost_compile markPairC := markPair
cost_compile regionTableC := regionTable
cost_compile countAtWC := countAtW
cost_compile countNextC := countNext
cost_compile kidMaxC := kidMax

/-! ## A child, off the tables -/

/-- Claim `j` of a child's leanXMSS claims from the mark `a`: the claim of the slot holding mark
`a + j` (`slotIn` of the region's table `tm`, `ts`), the table at `p53`. -/
noncomputable def xmssKidClaim (rd : Reader) (p53 : E) (tm ts : Array ℕ) (a j : ℕ) : LeanXmssClaim :=
  xmssAtK rd (p53.limb 0 * Parameters.g ^ (4 * slotIn tm ts (a + j)))

/-- Claim `j` of a child's leanSPHINCS claims from the mark `a` (`xmssKidClaim`). -/
noncomputable def sphincsKidClaim (rd : Reader) (p56 : E) (tm ts : Array ℕ) (a j : ℕ) :
    LeanSphincsClaim :=
  sphincsAtK rd (p56.limb 0 * Parameters.g ^ (4 * slotIn tm ts (a + j)))

/-- Child `c`'s statement, its segment's start `a` and its claims' counts `nx`, `ns` given. -/
noncomputable def kidStmtAt (rd : Reader) (σ : Val) (p53 p56 : E) (tx ts : Array ℕ × Array ℕ)
    (c a nx ns : ℕ) : NodeStatement :=
  ⟨⟨(List.range nx).map (xmssKidClaim rd p53 tx.1 tx.2 a),
    (List.range ns).map (sphincsKidClaim rd p56 ts.1 ts.2 (a + nx)),
    daDigestAt rd σ c⟩,
   deferOfCells (readCellsK rd ((σ (.n 377)).limb 0 * Parameters.g ^ (24 * c)) 24)⟩

/-- Child `c`'s statement, its segment `[a, b)` given: its claims counted in the tables. -/
noncomputable def kidStmtSeg (rd : Reader) (σ : Val) (p53 p56 : E) (tx ts : Array ℕ × Array ℕ)
    (c a b : ℕ) : NodeStatement :=
  kidStmtAt rd σ p53 p56 tx ts c a (countIn tx.1 a b) (countIn ts.1 a b)

/-- **Child `c`'s statement** (`kidStmt`), off the regions' tables `tx`, `ts`, `written` at
`w380` and the tables at `p53`, `p56`: its segment's ends (logarithms) read here. -/
noncomputable def kidStmtT (D : DiscreteLogTables) (rd : Reader) (σ : Val) (w380 p53 p56 : E)
    (tx ts : Array ℕ × Array ℕ) (c : ℕ) : NodeStatement :=
  kidStmtSeg rd σ p53 p56 tx ts c (countAtW D rd w380 c) (countAtW D rd w380 (c + 1))

/-- The words of child `c`'s `verify_sub` call (`subArgs`), its proof's claim's address by a
power in `K`. -/
noncomputable def subArgsK (rd : Reader) (σ : Val) (c : ℕ) : List E :=
  [cellAt rd (σ (.n 365)) (2 * c), cellAt rd (σ (.n 365)) (2 * c + 1), σ (.n 47), σ (.n 48),
    σ (.n 49), σ (.n 50), mulK (σ (.n 371)) (Parameters.g ^ (24 * c))]

/-- **Child `c`** (`decKid`), off the regions' tables. -/
noncomputable def decKidT (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ)
    (c : ℕ) : Child :=
  ⟨kidStmtT D rd σ w380 p53 p56 tx ts c,
    fixedOfCells (readCellsK rd ((σ (.n 371)).limb 0 * Parameters.g ^ (24 * c)) 24),
    wV (subArgsK rd σ c)⟩

/-- The two regions' tables, as `decWit`'s caller builds them. -/
noncomputable abbrev lxTable (D : DiscreteLogTables) (rd : Reader) (σ : Val) : Array ℕ × Array ℕ :=
  regionTable D rd (σ (.n 67)) 0 (lxSlotsD D σ)
noncomputable abbrev lsTable (D : DiscreteLogTables) (rd : Reader) (σ : Val) : Array ℕ × Array ℕ :=
  regionTable D rd (σ (.n 67)) (lxSlotsD D σ) (lsSlotsD D σ)

theorem xmssKidClaim_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val) (a : ℕ) :
    xmssKidClaim rd (σ (.n 53)) (lxTable D rd σ).1 (lxTable D rd σ).2 a =
      fun j ↦ xmssAt rd (σ (.n 53)) (slotOfD D rd σ 0 (lxSlotsD D σ) (a + j)) := by
  funext j
  rw [xmssKidClaim, slotIn_regionTable, xmssAt_eq_K]

theorem sphincsKidClaim_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val) (a : ℕ) :
    sphincsKidClaim rd (σ (.n 56)) (lsTable D rd σ).1 (lsTable D rd σ).2 a =
      fun j ↦ sphincsAt rd (σ (.n 56)) (slotOfD D rd σ (lxSlotsD D σ) (lsSlotsD D σ) (a + j)) := by
  funext j
  rw [sphincsKidClaim, slotIn_regionTable, sphincsAt_eq_K]

/-- **Off the tables built, child `c`'s statement is `kidStmtD`'s.** -/
theorem kidStmtT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val) (c : ℕ) :
    kidStmtT D rd σ (σ (.n 380)) (σ (.n 53)) (σ (.n 56)) (lxTable D rd σ) (lsTable D rd σ) c =
      kidStmtD D rd σ c := by
  unfold kidStmtT kidStmtSeg kidStmtAt kidStmtD
  rw [countIn_regionTable, countIn_regionTable, xmssKidClaim_eq, sphincsKidClaim_eq,
    ← readCells_mul_gen_pow]
  rfl

/-- **Off the tables built, child `c` is `decKidD`'s.** -/
theorem decKidT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (c : ℕ) :
    decKidT D rd σ wV (σ (.n 380)) (σ (.n 53)) (σ (.n 56)) (lxTable D rd σ) (lsTable D rd σ) c =
      decKidD D rd σ wV c := by
  unfold decKidT decKidD subArgsK subArgs
  rw [kidStmtT_eq, ← readCells_mul_gen_pow, mulK_gen_pow]

cost_compile xmssKidClaimC := xmssKidClaim
cost_compile sphincsKidClaimC := sphincsKidClaim
cost_compile kidStmtAtC := kidStmtAt
cost_compile kidStmtSegC := kidStmtSeg
cost_compile kidStmtC := kidStmtT
cost_compile subArgsC := subArgsK
cost_compile decKidC := decKidT

end

end LeanVM.Cost.Decoder
