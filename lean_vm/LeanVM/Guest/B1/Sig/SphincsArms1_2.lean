/-
  LeanVM.Guest.B1.Sig.SphincsArms1_2

  `verify_sig_lean_sphincs` in the guest's core IR agrees with the template `sBody` in the arms 128 to 191 of statement 209's match.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.SphincsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem sBody_arms_209_2 : ((matchArms (Data.core20.body.getD 209 default)).drop 128).take 64 =
    ((matchArms (sBody.getD 209 default)).drop 128).take 64 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
