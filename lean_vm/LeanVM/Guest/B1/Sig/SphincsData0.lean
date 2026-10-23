/-
  LeanVM.Guest.B1.Sig.SphincsData0

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sBody` on statements 0 to 198.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem sBody_slice_0 : (Data.core20.body.drop 0).take 199 = (sBody.drop 0).take 199 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
