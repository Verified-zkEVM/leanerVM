/-
  LeanVM.Guest.B1.Sig.SphincsData0

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sBody` on statements 0 to 1499.
-/

module

public import LeanVM.Guest.Data.Core11
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem sBody_slice_0 : (Data.core21.body.drop 0).take 500 = (sBody.drop 0).take 500 := by
  decide +kernel

open scoped Dec in
theorem sBody_slice_500 : (Data.core21.body.drop 500).take 500 = (sBody.drop 500).take 500 := by
  decide +kernel

open scoped Dec in
theorem sBody_slice_1000 : (Data.core21.body.drop 1000).take 500 = (sBody.drop 1000).take 500 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
