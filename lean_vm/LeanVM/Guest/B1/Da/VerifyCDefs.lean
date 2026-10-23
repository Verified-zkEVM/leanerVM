/-
  LeanVM.Guest.B1.Da.VerifyCDefs

  `da_verify`'s honest memory: its buffers' pointers (any choice of them) and the words an honest
  run of a witness leaves there.
-/

module

public import LeanVM.Guest.B1.Da.VerifyMath
public import LeanVM.Guest.B1.Da.LevelsCDefs

/-!
# `da_verify`'s honest memory

For `r` rows, the padded count `2^L`, the symbols `syms i j` of row `i`'s cell `j` and the weights
`ws j` of column `j` (`VerifyMath`): the running sums (`accSum`), the trees' leaves (`nodeLeaves`
of column `j`, `colLeaves`, `rowLeaves`), the rows' prefixes (`prefixCells`) and the columns'
digests (`cdCells`). `DaPtrs`: `da_verify`'s buffers (prefix bases and digests, column digests,
running sums and their bases, the column and row trees) and every column's node tree and weights'
frame run. `DaMem rd P …`: the memory an honest run leaves at them.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest

@[expose] public section

variable (r L : ℕ) (syms : ℕ → ℕ → List K) (ws : ℕ → List E)

/-- Cell `(i, j)`'s inner product with column `j`'s weights. -/
def cellDot (i j : ℕ) : E := ∑ e ∈ Finset.range 256, (ws j).getD e 0 * ofK ((syms i j).getD e 0)

/-- Row `i`'s running sum before column `b`. -/
def accSum (i b : ℕ) : E := ∑ j ∈ Finset.range b, cellDot syms ws i j

/-- Column `j`'s tree's leaves: its cells' digests, then the padding cells. -/
def nodeLeaves (j : ℕ) : List (E × E) :=
  (List.range (2 ^ L)).map fun i => digestScalars (cellLeaf r syms j i)

/-- The column tree's leaves: the columns' roots. -/
def colLeaves : List (E × E) := (List.range 128).map fun j => digestScalars (mRoot L (cellLeaf r syms j))

/-- The row tree's leaves: the rows' digests, then the padding rows. -/
def rowLeaves : List (E × E) := (List.range (2 ^ L)).map fun i => digestScalars (rowLeaf r syms i)

/-- Row `i`'s prefix: its first `64` cells' digests. -/
def prefixCells (i : ℕ) : List E := (List.range 64).flatMap fun j => digestCells (cellD syms i j)

/-- The columns' digests. -/
def cdCells : List E := (List.range 128).flatMap fun j => digestCells (colD ws j)

/-- `da_verify`'s buffers and every column's node tree and weights. -/
structure DaPtrs where
  pb : E
  pd : E
  cd : E
  acc : E
  rb : E
  ct : E
  rt : E
  node : ℕ → E
  lv : ℕ → E

/-- **The memory an honest run of `da_verify` leaves** at the pointers `P`. -/
structure DaMem (rd : Reader) (P : DaPtrs) : Prop where
  pbase : ∀ i < r, LoadHolds rd (P.pb * gen ^ i) 0 (P.pd * (gen ^ i) ^ 128)
  pcells : ∀ i < r, ReadsAt rd (P.pd * (gen ^ i) ^ 128) (prefixCells syms i)
  cd : ReadsAt rd P.cd (cdCells ws)
  rbase : ∀ i < r, LoadHolds rd (P.rb * gen ^ i) 0 (P.acc * (gen ^ i) ^ 129)
  acc : ∀ i < r, ReadsAt rd (P.acc * (gen ^ i) ^ 129) ((List.range 129).map (accSum syms ws i))
  ct : TreeMem rd P.ct 7 (colLeaves r L syms)
  rt : TreeMem rd P.rt L (rowLeaves r L syms)
  node : ∀ j < 128, TreeMem rd (P.node j) L (nodeLeaves r L syms j)
  lvK : ∀ j < 128, IsInK (P.lv j)
  lv : ∀ j < 128, ReadsAt rd (P.lv j) (ws j)

end
end LeanVM.Guest.B1.Da
