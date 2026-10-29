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
theorem col1_ok : (colOk (coreProgram.getD 748 default) "__loop415" "__loop416" &&
    decide (coreProgram.indexOf? "da_verify_column__L1" = some 748)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem col0_ok : (colOk (coreProgram.getD 749 default) "__loop417" "__loop418" &&
    decide (coreProgram.indexOf? "da_verify_column__L0" = some 749)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem row417_ok : (rowOk (coreProgram.getD 874 default) "__loop415" true &&
    decide (coreProgram.indexOf? "__loop415" = some 874)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem row419_ok : (rowOk (coreProgram.getD 876 default) "__loop417" false &&
    decide (coreProgram.indexOf? "__loop417" = some 876)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gap418_ok : (gapOk (coreProgram.getD 875 default) "__loop416" padCellLo.1 padCellLo.2.1
    padCellLo.2.2.1 padCellLo.2.2.2 &&
    decide (coreProgram.indexOf? "__loop416" = some 875)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gap420_ok : (gapOk (coreProgram.getD 877 default) "__loop418" padCellLo.1 padCellLo.2.1
    padCellLo.2.2.1 padCellLo.2.2.2 &&
    decide (coreProgram.indexOf? "__loop418" = some 877)) = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
