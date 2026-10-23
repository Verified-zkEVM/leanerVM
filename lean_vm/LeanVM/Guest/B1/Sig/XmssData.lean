/-
  LeanVM.Guest.B1.Sig.XmssData

  `verify_lean_xmss` in the guest's core IR is the template `xBody`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.XmssT
public import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Sig.XmssData0
import LeanVM.Guest.B1.Sig.XmssData1
import LeanVM.Guest.B1.Sig.XmssData2
import LeanVM.Guest.B1.Sig.XmssData3
import LeanVM.Guest.B1.Sig.XmssData4
import LeanVM.Guest.B1.Sig.XmssData5
import LeanVM.Guest.B1.Sig.XmssData6
import LeanVM.Guest.B1.Sig.XmssData7
import LeanVM.Guest.B1.Sig.XmssData8
import LeanVM.Guest.B1.Sig.XmssData9
import LeanVM.Guest.B1.Sig.XmssData10
import LeanVM.Guest.B1.Sig.XmssData11
import LeanVM.Guest.B1.Sig.XmssData12
import LeanVM.Guest.B1.Sig.XmssData13
import LeanVM.Guest.B1.Sig.XmssData14
import LeanVM.Guest.B1.Sig.XmssData15
import LeanVM.Guest.B1.Sig.XmssData16

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The body, checked by the kernel in slices. -/
theorem xBody_eq : Data.core19.body = xBody := by
  have h594 := xBody_drop_594
  have h589 := drop_eq_of_take xBody_slice_589 h594
  have h577 := drop_eq_of_take xBody_slice_577 h589
  have h565 := drop_eq_of_take xBody_slice_565 h577
  have h553 := drop_eq_of_take xBody_slice_553 h565
  have h541 := drop_eq_of_take xBody_slice_541 h553
  have h529 := drop_eq_of_take xBody_slice_529 h541
  have h517 := drop_eq_of_take xBody_slice_517 h529
  have h298 := drop_eq_of_take xBody_slice_298 h517
  have h290 := drop_eq_of_take xBody_slice_290 h298
  have h278 := drop_eq_of_take xBody_slice_278 h290
  have h266 := drop_eq_of_take xBody_slice_266 h278
  have h254 := drop_eq_of_take xBody_slice_254 h266
  have h242 := drop_eq_of_take xBody_slice_242 h254
  have h230 := drop_eq_of_take xBody_slice_230 h242
  have h218 := drop_eq_of_take xBody_slice_218 h230
  have h0 := drop_eq_of_take xBody_slice_0 h218
  rwa [List.drop_zero, List.drop_zero] at h0

end
end LeanVM.Guest.B1.Sig
