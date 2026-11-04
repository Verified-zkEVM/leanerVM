/-
  LeanVM.Guest.B1.Digest.ChildListCChk1

  `child_claim_list_last__L{k}`, evaluated (by kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk

namespace LeanVM.Guest.B1.Digest

open LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem ccc_lo : ∀ k < 9, cccOk k (coreProgram.getD (342 + k) default) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ccc_hi : ∀ k < 8, cccOk (9 + k) (coreProgram.getD (351 + k) default) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
