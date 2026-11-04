/-
  LeanVM.Guest.B1.Sig.XmssData4

  `verify_lean_xmss` in the guest's core IR agrees with the template `xBody` on statements 263 to 277.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.XmssT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem xBody_slice_263 : (Data.core19.body.drop 263).take 15 = (xBody.drop 263).take 15 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
