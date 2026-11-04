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
  have h634 := xBody_drop_634
  have h624 := drop_eq_of_take xBody_slice_624 h634
  have h609 := drop_eq_of_take xBody_slice_609 h624
  have h594 := drop_eq_of_take xBody_slice_594 h609
  have h579 := drop_eq_of_take xBody_slice_579 h594
  have h564 := drop_eq_of_take xBody_slice_564 h579
  have h549 := drop_eq_of_take xBody_slice_549 h564
  have h534 := drop_eq_of_take xBody_slice_534 h549
  have h318 := drop_eq_of_take xBody_slice_318 h534
  have h308 := drop_eq_of_take xBody_slice_308 h318
  have h293 := drop_eq_of_take xBody_slice_293 h308
  have h278 := drop_eq_of_take xBody_slice_278 h293
  have h263 := drop_eq_of_take xBody_slice_263 h278
  have h248 := drop_eq_of_take xBody_slice_248 h263
  have h233 := drop_eq_of_take xBody_slice_233 h248
  have h218 := drop_eq_of_take xBody_slice_218 h233
  have h0 := drop_eq_of_take xBody_slice_0 h218
  rwa [List.drop_zero, List.drop_zero] at h0

end
end LeanVM.Guest.B1.Sig
