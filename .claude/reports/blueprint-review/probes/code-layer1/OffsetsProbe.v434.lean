/-
  Probe for task code-layer1, deliverable B.2.

  leanVM's `stack_offsets` (`crates/lean_vm/src/witness.rs:67-79`, `python-verifier/verifier.py:
  305-311`) transcribed as a list function, and Layer 1's `Blocks.offset` / `Blocks.selector`
  fed with the order it produces. The expected numbers are the output of `offsets.py`, which
  runs the pinned Python verifier.

  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/code-layer1/OffsetsProbe.lean
-/
import LeanerVM.Protocol.ToCompPoly.Stacking

open LeanerVM.Protocol

namespace Probe

/-! ## `stack_offsets`, transcribed -/

/-- The stacking order: column indices sorted by size, largest first, ties by index. -/
def stackOrder (kappas : List ℕ) : List ℕ :=
  (List.range kappas.length).mergeSort fun a b ↦
    decide (kappas[b]! < kappas[a]!) || (kappas[a]! == kappas[b]! && decide (a ≤ b))

/-- Prefix sums of the heights along a list of sizes. -/
def prefixOffsets : List ℕ → ℕ → List ℕ
  | [], _ => []
  | k :: ks, off => off :: prefixOffsets ks (off + 2 ^ k)

/-- The offset of every column, in column-index order (`offsets[i] = off` for `i` in order). -/
def stackOffsets (kappas : List ℕ) : List ℕ :=
  let order := stackOrder kappas
  let offs := prefixOffsets (order.map (kappas[·]!)) 0
  (List.range kappas.length).map fun i ↦ (offs[order.idxOf i]?).getD 0

/-- A `Blocks` from a list of sizes that is already largest first. -/
def blocksOfList (l : List ℕ) (h : l.Pairwise (· ≥ ·)) : Blocks where
  n := l.length
  size := fun i ↦ l[i]
  descending := by
    intro a b hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (List.pairwise_iff_getElem.mp h) a.val b.val a.isLt b.isLt hlt

/-- Every offset of a `Blocks`, first block first. -/
def offsetsOf (B : Blocks) : List ℕ := (List.finRange B.n).map B.offset

/-- Every selector of a `Blocks`, first block first. -/
def selectorsOf (B : Blocks) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) : List ℕ :=
  (List.finRange B.n).map fun b ↦ (B.selector hμ b).val

/-! ## The small configuration

Column-index order: `mem_0, mem_1, mem_2, cntfin_mem, cntfin_bc, q_flock, table a, table b`. -/

def small : List ℕ := [4, 4, 4, 4, 2, 5, 4, 4]

-- The transcription gives what the pinned Python verifier and the Rust give (offsets.py).
#guard stackOrder small = [5, 0, 1, 2, 3, 6, 7, 4]
#guard stackOffsets small = [32, 48, 64, 80, 128, 0, 96, 112]

/-- The sorted sizes, as a `Blocks`. -/
def smallBlocks : Blocks := blocksOfList [5, 4, 4, 4, 4, 4, 4, 2] (by decide)

#guard (stackOrder small).map (small[·]!) = [5, 4, 4, 4, 4, 4, 4, 2]

theorem smallBlocks_total_le : smallBlocks.total ≤ 2 ^ 8 := by decide

example : smallBlocks.total = 132 := by decide

-- `Blocks.offset` and `Blocks.selector`, block by block, against the pinned verifiers' values.
#guard offsetsOf smallBlocks = [0, 32, 48, 64, 80, 96, 112, 128]
#guard selectorsOf smallBlocks smallBlocks_total_le = [0, 2, 3, 4, 5, 6, 7, 32]

-- Column `i` sits on block `(stackOrder small).idxOf i`; through that map the offsets are
-- leanVM's, column by column.
#guard (List.range 8).map (fun i ↦ (offsetsOf smallBlocks)[(stackOrder small).idxOf i]!) =
  stackOffsets small

/-- The order the blueprint had before finding F17: ties broken with the tables' columns
first. It sorts to the same sizes, so it is the same `Blocks`. -/
def tablesFirst : List ℕ := [5, 6, 7, 0, 1, 2, 3, 4]

#guard tablesFirst.map (small[·]!) = (stackOrder small).map (small[·]!)

-- Near miss: through that map `mem_0` sits at offset 64, not 32, and nothing about the
-- `Blocks` differs: the order of equal sizes lives in the map from columns to blocks only.
#guard (List.range 8).map (fun i ↦ (offsetsOf smallBlocks)[tablesFirst.idxOf i]!) =
  [64, 80, 96, 112, 128, 0, 32, 48]
#guard (List.range 8).map (fun i ↦ (offsetsOf smallBlocks)[tablesFirst.idxOf i]!) ≠
  stackOffsets small

-- The column-index order itself is not largest first, so it is no `Blocks`.
example : ¬ small.Pairwise (· ≥ ·) := by decide

/-! ## The pinned verifier's layout for one admissible announcement

`build_layout(log_memory = 16, taus = (3, 16, 0, 5, 16, 3), kbc = 4)`: 110 columns, 92 of
them committed. The three lists are copied from the output of `offsets.py`. -/

/-- The sizes of the 92 committed columns, in column-index order (the eighteen BLAKE2S limb
columns, global indices 82 to 99, left out). -/
def committedSizes : List ℕ :=
  [16, 16, 16, 16, 4, 11] ++ List.replicate 15 3 ++ List.replicate 15 16 ++
    List.replicate 8 0 ++ List.replicate 15 5 ++ List.replicate 14 16 ++
    List.replicate 9 3 ++ List.replicate 10 3

/-- The global column index of each committed column, in the same order. -/
def committedIndex : List ℕ := List.range 82 ++ (List.range 10).map (· + 100)

/-- Python: "column index of each block". -/
def pyOrder : List ℕ :=
  [0, 1, 2, 3, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 59, 60, 61, 62, 63,
   64, 65, 66, 67, 68, 69, 70, 71, 72, 5, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56,
   57, 58, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 73, 74, 75, 76, 77, 78,
   79, 80, 81, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 36, 37, 38, 39, 40, 41, 42, 43]

/-- Python: "offsets", first block first. -/
def pyOffsets : List ℕ :=
  [0, 65536, 131072, 196608, 262144, 327680, 393216, 458752, 524288, 589824, 655360, 720896,
   786432, 851968, 917504, 983040, 1048576, 1114112, 1179648, 1245184, 1310720, 1376256,
   1441792, 1507328, 1572864, 1638400, 1703936, 1769472, 1835008, 1900544, 1966080, 2031616,
   2097152, 2162688, 2164736, 2164768, 2164800, 2164832, 2164864, 2164896, 2164928, 2164960,
   2164992, 2165024, 2165056, 2165088, 2165120, 2165152, 2165184, 2165216, 2165232, 2165240,
   2165248, 2165256, 2165264, 2165272, 2165280, 2165288, 2165296, 2165304, 2165312, 2165320,
   2165328, 2165336, 2165344, 2165352, 2165360, 2165368, 2165376, 2165384, 2165392, 2165400,
   2165408, 2165416, 2165424, 2165432, 2165440, 2165448, 2165456, 2165464, 2165472, 2165480,
   2165488, 2165496, 2165504, 2165505, 2165506, 2165507, 2165508, 2165509, 2165510, 2165511]

/-- The sorted sizes. -/
def sortedSizes : List ℕ :=
  List.replicate 33 16 ++ [11] ++ List.replicate 15 5 ++ [4] ++ List.replicate 34 3 ++
    List.replicate 8 0

#guard committedSizes.length = 92
#guard (stackOrder committedSizes).map (committedIndex[·]!) = pyOrder
#guard (stackOrder committedSizes).map (committedSizes[·]!) = sortedSizes

/-- The sorted sizes as a `Blocks`. -/
def realBlocks : Blocks := blocksOfList sortedSizes (by decide +kernel)

#guard offsetsOf realBlocks = pyOffsets
#guard realBlocks.total = 2165512
example : realBlocks.total ≤ 2 ^ 22 := by decide +kernel
example : ¬ realBlocks.total ≤ 2 ^ 21 := by decide +kernel

end Probe
