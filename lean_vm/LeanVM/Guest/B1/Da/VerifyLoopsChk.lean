/-
  LeanVM.Guest.B1.Da.VerifyLoopsChk

  `da_verify`'s loops, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem l18_ok : (l18Ok (coreProgram.getD 356 default) && decide (coreProgram.indexOf? "__loop17" = some 356)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l19_ok : (l19Ok (coreProgram.getD 357 default) && decide (coreProgram.indexOf? "__loop18" = some 357)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l22_ok : (l22Ok (coreProgram.getD 360 default) && decide (coreProgram.indexOf? "__loop21" = some 360)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l24_ok : (gapOk (coreProgram.getD 363 default) "__loop23" padRowLo.1 padRowLo.2.1 padRowLo.2.2.1 padRowLo.2.2.2 && decide (coreProgram.indexOf? "__loop23" = some 363)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l20_ok : (colLoopOk (coreProgram.getD 358 default) "da_verify_column__L1" "__loop19" 27 && decide (coreProgram.indexOf? "__loop19" = some 358)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l21_ok : (colLoopOk (coreProgram.getD 359 default) "da_verify_column__L0" "__loop20" 325 && decide (coreProgram.indexOf? "__loop20" = some 359)) = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
