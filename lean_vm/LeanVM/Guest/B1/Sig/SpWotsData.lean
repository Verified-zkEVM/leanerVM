/-
  LeanVM.Guest.B1.Sig.SpWotsData

  `sp_wots` in the guest's core IR is the template `spBody`.
-/

module

public import LeanVM.Guest.Data.Core11
public import LeanVM.Guest.B1.Sig.SpWotsT
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Sig.SpWotsData0
import LeanVM.Guest.B1.Sig.SpWotsData1

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`sp_wots`'s body is the template**, checked by the kernel in slices: the powers, each digit
group's dispatch, the checks and the leaf. -/
theorem spBody_eq : Data.core20.body = spBody := by
  have h98 := spBody_drop_98
  have h94 := drop_eq_of_take spBody_slice_94 h98
  have h90 := drop_eq_of_take spBody_slice_90 h94
  have h86 := drop_eq_of_take spBody_slice_86 h90
  have h82 := drop_eq_of_take spBody_slice_82 h86
  have h78 := drop_eq_of_take spBody_slice_78 h82
  have h74 := drop_eq_of_take spBody_slice_74 h78
  have h70 := drop_eq_of_take spBody_slice_70 h74
  have h66 := drop_eq_of_take spBody_slice_66 h70
  have h62 := drop_eq_of_take spBody_slice_62 h66
  have h58 := drop_eq_of_take spBody_slice_58 h62
  have h54 := drop_eq_of_take spBody_slice_54 h58
  have h50 := drop_eq_of_take spBody_slice_50 h54
  have h46 := drop_eq_of_take spBody_slice_46 h50
  have h42 := drop_eq_of_take spBody_slice_42 h46
  have h38 := drop_eq_of_take spBody_slice_38 h42
  have h34 := drop_eq_of_take spBody_slice_34 h38
  have h30 := drop_eq_of_take spBody_slice_30 h34
  have h26 := drop_eq_of_take spBody_slice_26 h30
  have h22 := drop_eq_of_take spBody_slice_22 h26
  have h18 := drop_eq_of_take spBody_slice_18 h22
  have h14 := drop_eq_of_take spBody_slice_14 h18
  have h10 := drop_eq_of_take spBody_slice_10 h14
  have h0 := drop_eq_of_take spBody_slice_0 h10
  rwa [List.drop_zero, List.drop_zero] at h0

end
end LeanVM.Guest.B1.Sig
