/-
  LeanVM.Guest.B1.Sig.SphincsData2

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sBody` on statements 3000 to 4295.
-/

module

public import LeanVM.Guest.Data.Core11
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem sBody_slice_3000 : (Data.core20.body.drop 3000).take 500 = (sBody.drop 3000).take 500 := by
  decide +kernel

open scoped Dec in
theorem sBody_slice_3500 : (Data.core20.body.drop 3500).take 500 = (sBody.drop 3500).take 500 := by
  decide +kernel

open scoped Dec in
theorem sBody_drop_4000 : Data.core20.body.drop 4000 = sBody.drop 4000 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
