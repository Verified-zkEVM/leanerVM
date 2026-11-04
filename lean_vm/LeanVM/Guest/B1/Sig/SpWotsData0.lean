/-
  LeanVM.Guest.B1.Sig.SpWotsData0

  `sp_wots` in the guest's core IR agrees with the template `spBody` on the powers and digit groups 0 to 10 (statements 0 to 74).
-/

module

public import LeanVM.Guest.Data.Core05
public import LeanVM.Guest.B1.Sig.SpWotsT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem spBody_slice_0 : (Data.core19.body.drop 0).take 10 = (spBody.drop 0).take 10 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_10 : (Data.core19.body.drop 10).take 10 = (spBody.drop 10).take 10 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_20 : (Data.core19.body.drop 20).take 5 = (spBody.drop 20).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_25 : (Data.core19.body.drop 25).take 5 = (spBody.drop 25).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_30 : (Data.core19.body.drop 30).take 5 = (spBody.drop 30).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_35 : (Data.core19.body.drop 35).take 5 = (spBody.drop 35).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_40 : (Data.core19.body.drop 40).take 5 = (spBody.drop 40).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_45 : (Data.core19.body.drop 45).take 5 = (spBody.drop 45).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_50 : (Data.core19.body.drop 50).take 5 = (spBody.drop 50).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_55 : (Data.core19.body.drop 55).take 5 = (spBody.drop 55).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_60 : (Data.core19.body.drop 60).take 5 = (spBody.drop 60).take 5 := by
  decide +kernel

open scoped Dec in
theorem spBody_slice_65 : (Data.core19.body.drop 65).take 5 = (spBody.drop 65).take 5 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
