/-
  LeanVM.Guest.B1.Sig.XmssData5

  `verify_lean_xmss` in the guest's core IR agrees with the template `xBody` on statements 278 to 292.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.XmssT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem xBody_slice_278 : (Data.core19.body.drop 278).take 15 = (xBody.drop 278).take 15 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
