/-
  LeanVM.Guest.B1.Da.VerifyChk

  `da_verify`'s body and its loops, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dv_ok : dvOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l17_ok : l17Ok (coreProgram.getD 359 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l18_ok : l18Ok (coreProgram.getD 360 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l19_ok : l19Ok (coreProgram.getD 361 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l20_ok : l20Ok (coreProgram.getD 362 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dv_loops_idx : coreProgram.indexOf? "__loop17" = some 359 ∧
    coreProgram.indexOf? "__loop18" = some 360 ∧ coreProgram.indexOf? "__loop19" = some 361 ∧
    coreProgram.indexOf? "__loop20" = some 362 := by
  decide +kernel

end
end LeanVM.Guest.B1.Da
