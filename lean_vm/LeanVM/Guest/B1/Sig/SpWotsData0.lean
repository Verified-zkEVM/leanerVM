/-
  LeanVM.Guest.B1.Sig.SpWotsData0

  `sp_wots` in the guest's core IR agrees with the template `spBody` on the powers and digit groups 0 to 10 (statements 0 to 53).
-/

module

public import LeanVM.Guest.Data.Core11
public import LeanVM.Guest.B1.Sig.SpWotsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem spBody_slice_0 : (Data.core20.body.drop 0).take 10 = (spBody.drop 0).take 10 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_10 : (Data.core20.body.drop 10).take 4 = (spBody.drop 10).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_14 : (Data.core20.body.drop 14).take 4 = (spBody.drop 14).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_18 : (Data.core20.body.drop 18).take 4 = (spBody.drop 18).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_22 : (Data.core20.body.drop 22).take 4 = (spBody.drop 22).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_26 : (Data.core20.body.drop 26).take 4 = (spBody.drop 26).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_30 : (Data.core20.body.drop 30).take 4 = (spBody.drop 30).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_34 : (Data.core20.body.drop 34).take 4 = (spBody.drop 34).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_38 : (Data.core20.body.drop 38).take 4 = (spBody.drop 38).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_42 : (Data.core20.body.drop 42).take 4 = (spBody.drop 42).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_46 : (Data.core20.body.drop 46).take 4 = (spBody.drop 46).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_50 : (Data.core20.body.drop 50).take 4 = (spBody.drop 50).take 4 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
