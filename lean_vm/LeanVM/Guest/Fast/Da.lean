module

public import LeanVM.Guest.Fast.FunctionNames
public import LeanVM.Guest.B1.Da.VerifyW

/-!
# `da_verify`'s witness reader, its frames numbered

`dvWit σ Vm` (`B1/Da/VerifyW.lean`) reads the DA matrix off `da_verify`'s callees' frames, which it
names by string literals (`colNm`, `rowNm`, `"da_vector_cell"`, `"da_verify_cell"`). `dvWitN σ Vn`
reads the same frames by the functions' indices (`Fast/FunctionNames.lean`); `dvWitN_eq`: at
`Vn k = Vm (decoderFunctionName k)` they are equal.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Da LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main

@[expose] public section

/-- Column `j`'s function (`colNm`): `da_verify_column__L1` or `__L0`. -/
def colNum (j : ℕ) : ℕ := if j < 64 then 749 else 750

/-- Column `j`'s row loop (`rowNm`): `__loop415` or `__loop417`. -/
def rowNum (j : ℕ) : ℕ := if j < 64 then 875 else 877

/-- Column `j`'s valuation (`dvColV`). -/
def dvColVN (σ : Val) (Vn : NFrames) (j : ℕ) : Val := Vn (colNum j) (dvColArgs σ j) []

/-- Row `i`'s iteration of column `j`'s row loop, its valuation (`dvRowV`). -/
def dvRowVN (σ : Val) (Vn : NFrames) (i j : ℕ) : Val :=
  Vn (rowNum j) [gen ^ i, σ (.n 1), dvColVN σ Vn j (.n 11), σ (.n 27), gen ^ j,
    dvColVN σ Vn j (.n 14), σ (.n 13)] []

/-- The symbols, padded outside the matrix (`dvSymsP`). -/
noncomputable def dvSymsPN (σ : Val) (Vn : NFrames) (i j : ℕ) : List K :=
  if i < gLog (σ (.n 1)) ∧ j < 128 then
    cellSymsOf (Vn 28 [dvColVN σ Vn j (.n 11)]
      [dvRowVN σ Vn i j (.n 7), dvRowVN σ Vn i j (.n 8), dvRowVN σ Vn i j (.n 9)])
  else List.replicate 256 0

/-- The weights, padded outside the vector (`dvWsP`). -/
def dvWsPN (σ : Val) (Vn : NFrames) (j : ℕ) : List E :=
  if j < 128 then vecWsOf (Vn 29 [σ (.n 17) * (gen ^ j) ^ 2] [dvColVN σ Vn j (.n 11)])
  else List.replicate 256 0

/-- **`da_verify`'s witness** (`dvWit`), its frames numbered. -/
noncomputable def dvWitN (σ : Val) (Vn : NFrames) : LeanVM.Da.MatrixWitness :=
  ⟨daRows (gLog (σ (.n 1))) (dvSymsPN σ Vn), daVector (dvWsPN σ Vn)⟩

theorem dvColVN_eq (σ : Val) (Vm : FrameMap) (j : ℕ) :
    dvColVN σ (fun k ↦ Vm (decoderFunctionName k)) j = dvColV σ Vm j := by
  unfold dvColVN dvColV colNum colNm
  split <;> simp only [name_da_verify_column_L1, name_da_verify_column_L0]

theorem dvRowVN_eq (σ : Val) (Vm : FrameMap) (i j : ℕ) :
    dvRowVN σ (fun k ↦ Vm (decoderFunctionName k)) i j = dvRowV σ Vm i j := by
  unfold dvRowVN dvRowV rowNum rowNm
  simp only [dvColVN_eq]
  split <;> simp only [name_loop415, name_loop417]

/-- **The readers are equal.** -/
theorem dvWitN_eq (σ : Val) (Vm : FrameMap) :
    dvWitN σ (fun k ↦ Vm (decoderFunctionName k)) = dvWit σ Vm := by
  unfold dvWitN dvWit dvSymsPN dvSymsP dvWsPN dvWsP dvSyms dvWs
  simp only [dvColVN_eq, dvRowVN_eq, name_da_vector_cell, name_da_verify_cell]

end
end LeanVM.Guest.Fast
