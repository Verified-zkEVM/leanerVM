/-
  LeanVM.Guest.B1.Sig.XmssData8

  `verify_lean_xmss` in the guest's core IR agrees with the template `xBody` on statements 298 to 516.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.XmssT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem xBody_slice_298 : (Data.core19.body.drop 298).take 219 = (xBody.drop 298).take 219 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
