/-
  LeanVM.Guest.B1.Sig.SphincsCoord7

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sBody` between coordinate 7's forest keys.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem sBody_slice_458 : (Data.core20.body.drop 458).take 10 = (sBody.drop 458).take 10 := by
  decide +kernel

open scoped Dec in
theorem sBody_slice_469 : (Data.core20.body.drop 469).take 11 = (sBody.drop 469).take 11 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
