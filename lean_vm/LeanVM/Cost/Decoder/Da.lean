module

public import LeanVM.Cost.Decoder.Hints
public import LeanVM.Guest.Fast.Da

/-!
# The guest decoder's compiled chain: the DA matrix

`da_verify`'s witness off its callees' frames, keyed by the functions' indices
(`Guest.Fast.dvWitN`, equal to `Da.dvWit` at the frame map re-keyed by `decoderFunctionName`,
`Guest.Fast.dvWitN_eq`): the rows of the cells' symbols and the vector of the columns' weights,
compiled part by part. Staged: the number of rows (a logarithm, `gLogD D`, the logarithm's tables
`D` given) computed once by `dvWitND` and passed to `dvWitNAt` and to every symbol's reader
(`dvSymsPNAt`); `dvWitND_tables : dvWitND discreteLogTables = dvWitN`.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Fast LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Extraction.Fast

@[expose] public section

/-- The symbols, padded outside the matrix of `r` rows (`dvSymsPN`, `r` its logarithm). -/
def dvSymsPNAt (r : ℕ) (σ : Val) (Vn : NFrames) (i j : ℕ) : List K :=
  if i < r ∧ j < 128 then
    cellSymsOf (Vn 28 [dvColVN σ Vn j (.n 11)]
      [dvRowVN σ Vn i j (.n 7), dvRowVN σ Vn i j (.n 8), dvRowVN σ Vn i j (.n 9)])
  else List.replicate 256 0

/-- `da_verify`'s witness, its `r` rows given (`dvWitN`). -/
def dvWitNAt (r : ℕ) (σ : Val) (Vn : NFrames) : LeanVM.Da.MatrixWitness :=
  ⟨daRows r (dvSymsPNAt r σ Vn), daVector (dvWsPN σ Vn)⟩

/-- **`da_verify`'s witness** (`dvWitN`), the logarithm's tables `D` given: its rows counted
once. -/
def dvWitND (D : DiscreteLogTables) (σ : Val) (Vn : NFrames) : LeanVM.Da.MatrixWitness :=
  dvWitNAt (gLogD D (σ (.n 1))) σ Vn

theorem dvWitND_tables : dvWitND discreteLogTables = dvWitN := by
  funext σ Vn
  unfold dvWitND dvWitNAt dvWitN dvSymsPNAt dvSymsPN
  rw [gLogD_tables]

cost_compile colNumC := colNum
cost_compile rowNumC := rowNum
cost_compile dvColVNC := dvColVN
cost_compile dvRowVNC := dvRowVN
cost_compile dvSymsPNC := dvSymsPNAt
cost_compile dvWsPNC := dvWsPN
set_option maxHeartbeats 4000000 in
cost_compile dvWitNAtC := dvWitNAt
cost_compile dvWitNC := dvWitND

end

end LeanVM.Cost.Decoder
