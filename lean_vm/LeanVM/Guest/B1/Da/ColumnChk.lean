/-
  LeanVM.Guest.B1.Da.ColumnChk

  `da_verify_column`'s specializations and loops, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.ColumnDefs

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem col1_ok : (colOk (coreProgram.getD 769 default) "__loop417" "__loop418" &&
    decide (coreProgram.indexOf? "da_verify_column__L1" = some 769)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem col0_ok : (colOk (coreProgram.getD 770 default) "__loop419" "__loop420" &&
    decide (coreProgram.indexOf? "da_verify_column__L0" = some 770)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem row417_ok : (rowOk (coreProgram.getD 895 default) "__loop417" true &&
    decide (coreProgram.indexOf? "__loop417" = some 895)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem row419_ok : (rowOk (coreProgram.getD 897 default) "__loop419" false &&
    decide (coreProgram.indexOf? "__loop419" = some 897)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gap418_ok : (gapOk (coreProgram.getD 896 default) "__loop418" padCellLo.1 padCellLo.2.1
    padCellLo.2.2.1 padCellLo.2.2.2 &&
    decide (coreProgram.indexOf? "__loop418" = some 896)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gap420_ok : (gapOk (coreProgram.getD 898 default) "__loop420" padCellLo.1 padCellLo.2.1
    padCellLo.2.2.1 padCellLo.2.2.2 &&
    decide (coreProgram.indexOf? "__loop420" = some 898)) = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
