/-
  LeanVM.Guest.B1.Sig.SpWotsData1

  `sp_wots` in the guest's core IR agrees with the template `spBody` on digit groups 11 to 21, the checks and the leaf (statements 75 on).
-/

module

public import LeanVM.Guest.Data.Core11
public import LeanVM.Guest.B1.Sig.SpWotsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem spBody_slice_70 : (Data.core20.body.drop 70).take 5 = (spBody.drop 70).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_75 : (Data.core20.body.drop 75).take 5 = (spBody.drop 75).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_80 : (Data.core20.body.drop 80).take 5 = (spBody.drop 80).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_85 : (Data.core20.body.drop 85).take 5 = (spBody.drop 85).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_90 : (Data.core20.body.drop 90).take 5 = (spBody.drop 90).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_95 : (Data.core20.body.drop 95).take 5 = (spBody.drop 95).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_100 : (Data.core20.body.drop 100).take 5 = (spBody.drop 100).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_105 : (Data.core20.body.drop 105).take 5 = (spBody.drop 105).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_110 : (Data.core20.body.drop 110).take 5 = (spBody.drop 110).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_115 : (Data.core20.body.drop 115).take 5 = (spBody.drop 115).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_drop_120 : Data.core20.body.drop 120 = spBody.drop 120 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
