/-
  LeanVM.Guest.B1.Sig.SpWotsData1

  `sp_wots` in the guest's core IR agrees with the template `spBody` on digit groups 11 to 21, the checks and the leaf (statements 54 on).
-/

module

public import LeanVM.Guest.Data.Core11
public import LeanVM.Guest.B1.Sig.SpWotsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem spBody_slice_54 : (Data.core20.body.drop 54).take 4 = (spBody.drop 54).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_58 : (Data.core20.body.drop 58).take 4 = (spBody.drop 58).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_62 : (Data.core20.body.drop 62).take 4 = (spBody.drop 62).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_66 : (Data.core20.body.drop 66).take 4 = (spBody.drop 66).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_70 : (Data.core20.body.drop 70).take 4 = (spBody.drop 70).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_74 : (Data.core20.body.drop 74).take 4 = (spBody.drop 74).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_78 : (Data.core20.body.drop 78).take 4 = (spBody.drop 78).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_82 : (Data.core20.body.drop 82).take 4 = (spBody.drop 82).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_86 : (Data.core20.body.drop 86).take 4 = (spBody.drop 86).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_90 : (Data.core20.body.drop 90).take 4 = (spBody.drop 90).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_94 : (Data.core20.body.drop 94).take 4 = (spBody.drop 94).take 4 := by
  decide +kernel

open scoped Dec in
theorem spBody_drop_98 : Data.core20.body.drop 98 = spBody.drop 98 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
