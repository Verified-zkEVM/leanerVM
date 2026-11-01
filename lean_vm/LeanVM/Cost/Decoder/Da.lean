module

public import LeanVM.Cost.Decoder.Hints
public import LeanVM.Guest.Fast.Da
import LeanVM.Guest.Value.Bits

/-!
# The guest decoder's compiled chain: the DA matrix

`da_verify`'s witness off its callees' frames, keyed by the functions' indices
(`Guest.Fast.dvWitN`, equal to `Da.dvWit` at the frame map re-keyed by `decoderFunctionName`,
`Guest.Fast.dvWitN_eq`): the rows of the cells' symbols and the vector of the columns' weights,
compiled part by part. Staged, each frame looked up once:

* the number of rows (a logarithm, `gLogD D`, the logarithm's tables `D` given) computed once by
  `dvWitND` and passed to `dvWitNAt`;
* each column's frame (`dvColVN`) looked up once, its two words the rows read (`dvColWords`)
  kept in an array of the `128` columns (`dvCols`), built once by `dvWitNAt` and passed to
  `dvWitNCols`;
* each cell's row frame (`dvRowVW`) looked up once, passed as a value to `cellSymsAt`;
* the powers of `g` taken in `K` (`ofK (g^i)`, `mulK`), not in `E`.

`dvWitNAt_eq : dvWitNCols r σ Vn (dvCols σ Vn) = …` is the unstaged witness (`dvSymsPNAt`,
`dvWsPN`), and `dvWitND_tables : dvWitND discreteLogTables = dvWitN`.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Fast LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Extraction.Fast LeanVM.Protocol.Verifier

@[expose] public section

/-- The symbols, padded outside the matrix of `r` rows (`dvSymsPN`, `r` its logarithm). -/
def dvSymsPNAt (r : ℕ) (σ : Val) (Vn : NFrames) (i j : ℕ) : List K :=
  if i < r ∧ j < 128 then
    cellSymsOf (Vn 28 [dvColVN σ Vn j (.n 11)]
      [dvRowVN σ Vn i j (.n 7), dvRowVN σ Vn i j (.n 8), dvRowVN σ Vn i j (.n 9)])
  else List.replicate 256 0

/-! ## Each frame once -/

/-- A column's two words its rows read (`11`, `14`), off its valuation. -/
def colWordsOf (v : Val) : E × E := (v (.n 11), v (.n 14))

/-- Column `j`'s two words, its frame looked up once. -/
def dvColWords (σ : Val) (Vn : NFrames) (j : ℕ) : E × E := colWordsOf (dvColVN σ Vn j)

/-- The `128` columns' words. -/
def dvCols (σ : Val) (Vn : NFrames) : Array (E × E) := ((List.range 128).map (dvColWords σ Vn)).toArray

/-- Row `i`'s iteration of column `j`'s row loop (`dvRowVN`), the column's words `cw` given. -/
def dvRowVW (σ : Val) (Vn : NFrames) (cw : E × E) (i j : ℕ) : Val :=
  Vn (rowNum j) [ofK (Parameters.g ^ i), σ (.n 1), cw.1, σ (.n 27), ofK (Parameters.g ^ j), cw.2,
    σ (.n 13)] []

/-- A cell's symbols off `da_verify_cell`'s frame, the row's valuation given. -/
def cellSymsAt (Vn : NFrames) (c11 : E) (row : Val) : List K :=
  cellSymsOf (Vn 28 [c11] [row (.n 7), row (.n 8), row (.n 9)])

/-- Cell `(i, j)`'s symbols, the column's words given: its row's frame looked up once. -/
def dvSymsCell (σ : Val) (Vn : NFrames) (cw : E × E) (i j : ℕ) : List K :=
  cellSymsAt Vn cw.1 (dvRowVW σ Vn cw i j)

/-- The symbols, padded outside the matrix of `r` rows, the columns' words given. -/
def dvSymsCols (r : ℕ) (σ : Val) (Vn : NFrames) (cols : Array (E × E)) (i j : ℕ) : List K :=
  if i < r ∧ j < 128 then dvSymsCell σ Vn (cols.getD j (0, 0)) i j else List.replicate 256 0

/-- The weights, padded outside the vector (`dvWsPN`), the columns' words given. -/
def dvWsCols (σ : Val) (Vn : NFrames) (cols : Array (E × E)) (j : ℕ) : List E :=
  if j < 128 then vecWsOf (Vn 29 [mulK (σ (.n 17)) (Parameters.g ^ (2 * j))] [(cols.getD j (0, 0)).1])
  else List.replicate 256 0

/-- `da_verify`'s witness, its `r` rows and its columns' words given. -/
def dvWitNCols (r : ℕ) (σ : Val) (Vn : NFrames) (cols : Array (E × E)) : LeanVM.Da.MatrixWitness :=
  ⟨daRows r (dvSymsCols r σ Vn cols), daVector (dvWsCols σ Vn cols)⟩

/-- `da_verify`'s witness, its `r` rows given (`dvWitN`): the columns' words built once. -/
def dvWitNAt (r : ℕ) (σ : Val) (Vn : NFrames) : LeanVM.Da.MatrixWitness :=
  dvWitNCols r σ Vn (dvCols σ Vn)

theorem dvCols_getD (σ : Val) (Vn : NFrames) {j : ℕ} (hj : j < 128) :
    (dvCols σ Vn).getD j (0, 0) = (dvColVN σ Vn j (.n 11), dvColVN σ Vn j (.n 14)) := by
  simp [dvCols, dvColWords, colWordsOf, Array.getD_eq_getD_getElem?, hj]

theorem dvSymsCols_eq (r : ℕ) (σ : Val) (Vn : NFrames) (i j : ℕ) :
    dvSymsCols r σ Vn (dvCols σ Vn) i j = dvSymsPNAt r σ Vn i j := by
  unfold dvSymsCols dvSymsPNAt
  split
  · rename_i h
    rw [dvCols_getD σ Vn h.2]
    simp only [dvSymsCell, cellSymsAt, dvRowVW, dvRowVN, LeanVM.Guest.Value.gen_pow_eq_ofK]
  · rfl

theorem dvWsCols_eq (σ : Val) (Vn : NFrames) (j : ℕ) :
    dvWsCols σ Vn (dvCols σ Vn) j = dvWsPN σ Vn j := by
  unfold dvWsCols dvWsPN
  split
  · rename_i h
    rw [dvCols_getD σ Vn h, mulK_gen_pow, ← pow_mul, Nat.mul_comm]
  · rfl

/-- **The staged witness is the unstaged one.** -/
theorem dvWitNAt_eq (r : ℕ) (σ : Val) (Vn : NFrames) :
    dvWitNAt r σ Vn = ⟨daRows r (dvSymsPNAt r σ Vn), daVector (dvWsPN σ Vn)⟩ := by
  unfold dvWitNAt dvWitNCols
  have h1 : dvSymsCols r σ Vn (dvCols σ Vn) = dvSymsPNAt r σ Vn :=
    funext fun i ↦ funext fun j ↦ dvSymsCols_eq r σ Vn i j
  have h2 : dvWsCols σ Vn (dvCols σ Vn) = dvWsPN σ Vn := funext (dvWsCols_eq σ Vn)
  rw [h1, h2]

/-- **`da_verify`'s witness** (`dvWitN`), the logarithm's tables `D` given: its rows counted
once. -/
def dvWitND (D : DiscreteLogTables) (σ : Val) (Vn : NFrames) : LeanVM.Da.MatrixWitness :=
  dvWitNAt (gLogD D (σ (.n 1))) σ Vn

theorem dvWitND_tables : dvWitND discreteLogTables = dvWitN := by
  funext σ Vn
  unfold dvWitND
  rw [dvWitNAt_eq]
  unfold dvWitN dvSymsPNAt dvSymsPN
  rw [gLogD_tables]

cost_compile colNumC := colNum
cost_compile rowNumC := rowNum
cost_compile dvColVNC := dvColVN
cost_compile colWordsOfC := colWordsOf
cost_compile dvColWordsC := dvColWords
cost_compile dvColsC := dvCols
cost_compile dvRowVWC := dvRowVW
cost_compile cellSymsAtC := cellSymsAt
cost_compile dvSymsCellC := dvSymsCell
cost_compile dvSymsColsC := dvSymsCols
cost_compile dvWsColsC := dvWsCols
set_option maxHeartbeats 4000000 in
cost_compile dvWitNColsC := dvWitNCols
cost_compile dvWitNAtC := dvWitNAt
cost_compile dvWitNC := dvWitND

end

end LeanVM.Cost.Decoder
