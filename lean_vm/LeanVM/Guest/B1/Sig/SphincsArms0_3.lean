/-
  LeanVM.Guest.B1.Sig.SphincsArms0_3

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sBody` in the arms 192 to 255 of statement 199's match.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem sBody_arms_199_3 : (matchArms (Data.core20.body.getD 199 default)).drop 192 =
    (matchArms (sBody.getD 199 default)).drop 192 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
