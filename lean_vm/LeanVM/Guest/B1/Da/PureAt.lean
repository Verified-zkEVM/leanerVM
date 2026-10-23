/-
  LeanVM.Guest.B1.Da.PureAt

  The functions `da_verify` calls that place nothing (no `HeapBuf`, no `frameAddr`): one set
  closed under calls (`daPure`), so each is `CompleteAtD` from its relation on every memory holding
  the words it reads (`completeAt_of_rel_pureD`).
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Da.ColumnDefs

/-!
# The pure callees

`daPureSet`: the cell check, the column's row and padding loops, `da_verify`'s loops over the
rows, the trees' `da_levels` and their level loops. `daPure`: it places nothing and calls only its
own members (kernel evaluation).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The level loops of the `da_levels` functions. -/
def lvlLoops : List String :=
  ["__loop306", "__loop307", "__loop308", "__loop309", "__loop310", "__loop311", "__loop312",
  "__loop313", "__loop314", "__loop315", "__loop316", "__loop317", "__loop318", "__loop319",
  "__loop320", "__loop321", "__loop322", "__loop323", "__loop324", "__loop325", "__loop326",
  "__loop327", "__loop328", "__loop329", "__loop330", "__loop331", "__loop332", "__loop333",
  "__loop334", "__loop335", "__loop336", "__loop337", "__loop338", "__loop339", "__loop340",
  "__loop341", "__loop342", "__loop343", "__loop344", "__loop345", "__loop346", "__loop347",
  "__loop348", "__loop349", "__loop350", "__loop351", "__loop352", "__loop353", "__loop354",
  "__loop355", "__loop356", "__loop357", "__loop358", "__loop359", "__loop360"]

/-- **The pure callees of `da_verify`.** -/
def daPureSet : List String :=
  ["da_verify_cell", "__loop417", "__loop418", "__loop419", "__loop420", "__loop18", "__loop19",
    "__loop22", "__loop23", "__loop24"] ++ dlNames ++ lvlLoops

/-- Every member's body places nothing and calls members only. -/
noncomputable def daPureOk : Bool :=
  daPureSet.all fun g => match coreProgram.find? g with
    | some fn => Stmt.pureList daPureSet fn.body
    | none => true

set_option maxRecDepth 100000 in
theorem daPure_ok : daPureOk = true := by decide +kernel

theorem daPure : coreProgram.PureIn daPureSet := by
  intro g hg fn hf
  have h := List.all_eq_true.mp daPure_ok g hg
  rw [hf] at h
  exact h

end
end LeanVM.Guest.B1.Da
