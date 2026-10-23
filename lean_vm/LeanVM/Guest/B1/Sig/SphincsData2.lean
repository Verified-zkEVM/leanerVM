/-
  LeanVM.Guest.B1.Sig.SphincsData2

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sBody` from statement 619 on.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem sBody_drop_619 : Data.core20.body.drop 619 = sBody.drop 619 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
