/-
  LeanVM.Guest.B1.Sig.SphincsData

  `verify_sig_lean_sphincs` in the guest's core IR is the template `sBody`.
-/

module

public import LeanVM.Guest.Data.Core11
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Sig.SphincsData0
import LeanVM.Guest.B1.Sig.SphincsData1
import LeanVM.Guest.B1.Sig.SphincsData2

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`verify_sig_lean_sphincs`'s body is the template**, checked by the kernel in slices of 500
statements. -/
theorem sBody_eq : Data.core21.body = sBody := by
  have h4000 := sBody_drop_4000
  have h3500 := drop_eq_of_take sBody_slice_3500 h4000
  have h3000 := drop_eq_of_take sBody_slice_3000 h3500
  have h2500 := drop_eq_of_take sBody_slice_2500 h3000
  have h2000 := drop_eq_of_take sBody_slice_2000 h2500
  have h1500 := drop_eq_of_take sBody_slice_1500 h2000
  have h1000 := drop_eq_of_take sBody_slice_1000 h1500
  have h500 := drop_eq_of_take sBody_slice_500 h1000
  have h0 := drop_eq_of_take sBody_slice_0 h500
  rwa [List.drop_zero, List.drop_zero] at h0

end
end LeanVM.Guest.B1.Sig
