/-
  LeanVM.Guest.B1.Sig.SphincsArms9_1

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sBody` in the arms 64 to 127 of statement 357's match.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem sBody_arms_357_1 : ((matchArms (Data.core20.body.getD 357 default)).drop 64).take 64 =
    ((matchArms (sBody.getD 357 default)).drop 64).take 64 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
