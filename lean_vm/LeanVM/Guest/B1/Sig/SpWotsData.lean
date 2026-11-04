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
  have h120 := spBody_drop_120
  have h115 := drop_eq_of_take spBody_slice_115 h120
  have h110 := drop_eq_of_take spBody_slice_110 h115
  have h105 := drop_eq_of_take spBody_slice_105 h110
  have h100 := drop_eq_of_take spBody_slice_100 h105
  have h95 := drop_eq_of_take spBody_slice_95 h100
  have h90 := drop_eq_of_take spBody_slice_90 h95
  have h85 := drop_eq_of_take spBody_slice_85 h90
  have h80 := drop_eq_of_take spBody_slice_80 h85
  have h75 := drop_eq_of_take spBody_slice_75 h80
  have h70 := drop_eq_of_take spBody_slice_70 h75
  have h65 := drop_eq_of_take spBody_slice_65 h70
  have h60 := drop_eq_of_take spBody_slice_60 h65
  have h55 := drop_eq_of_take spBody_slice_55 h60
  have h50 := drop_eq_of_take spBody_slice_50 h55
  have h45 := drop_eq_of_take spBody_slice_45 h50
  have h40 := drop_eq_of_take spBody_slice_40 h45
  have h35 := drop_eq_of_take spBody_slice_35 h40
  have h30 := drop_eq_of_take spBody_slice_30 h35
  have h25 := drop_eq_of_take spBody_slice_25 h30
  have h20 := drop_eq_of_take spBody_slice_20 h25
  have h10 := drop_eq_of_take spBody_slice_10 h20
  have h0 := drop_eq_of_take spBody_slice_0 h10
  rwa [List.drop_zero, List.drop_zero] at h0

end
end LeanVM.Guest.B1.Sig
