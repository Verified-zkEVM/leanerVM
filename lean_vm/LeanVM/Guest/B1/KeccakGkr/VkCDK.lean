/-
  LeanVM.Guest.B1.KeccakGkr.VkCDK

  What the kernel checks of `verify_keccak`'s openings.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK

/-!
# The openings' blocks

`vkOutKer`: of the committed outputs' opening, the loads that are not stores and the residual
loads' pointers of its lane weights (`vkOutSL`) and their dot product (`vkOutDL`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The committed outputs' lane weights. -/
abbrev vkOutSL : List Stmt := slotLanesT 3691 3711 3712 1 1

/-- The committed outputs' dot product. -/
abbrev vkOutDL : List Stmt := dotLoadsT ((List.range 25).map (slotLaneV 3712 1)) (.n 274) 30 3895

theorem vkOut_ker :
    noneIn [.load (.n 3701) (.n 3699) 0] vkSt = true ∧
    vkOutSL.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkOutSL)) = true ∧
    (resid (atomsL vkOutSL)).all (ldR [(.n 3691, 0, 6), (.n 3711, 0, 1)]) = true ∧
    noneIn (resid (atomsL vkOutSL)) vkSt = true ∧
    vkOutDL.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkOutDL)) = true ∧
    (resid (atomsL vkOutDL)).all (ldR [(.n 274, 30, 55)]) = true ∧
    noneIn (resid (atomsL vkOutDL)) vkSt = true := by
  decide +kernel

end
end LeanVM.Guest.B1.VerifySub
