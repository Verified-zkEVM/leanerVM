/-
  LeanVM.Guest.B1.Sig.SphincsWots1

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sBody` on the digit group at statement 539.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem sBody_slice_539 : (Data.core20.body.drop 539).take 4 = (sBody.drop 539).take 4 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
