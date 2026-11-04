/-
  LeanVM.Guest.B1.Tables.Vt.FormsT3

  Table 3's forms on the three sides, from the guest's statements: each block's value from its
  baked terms, the table's form the blocks' selectors times their values.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsDiff
public import LeanVM.Guest.B1.Tables.Vt.PullSels
public import LeanVM.Guest.B1.Tables.Vt.Pi

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB03_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3837) = σ (.n 1053) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3675 [
    .atom (.load (.n 3827) (.n 13) 0),
    .atom (.const (.n 3828) (word 2 0 0)),
    .atom (.mul (.n 3829) (.n 3828) (.n 3620)),
    .atom (.load (.n 3830) (.n 13) 1),
    .atom (.mul (.n 3831) (.n 3830) (.n 3829)),
    .atom (.add (.n 3832) (.n 3827) (.n 3831)),
    .atom (.load (.n 3833) (.n 13) 2),
    .atom (.mul (.n 3834) (.n 3833) (.n 3631)),
    .atom (.add (.n 3835) (.n 3832) (.n 3834)),
    .atom (.add (.n 3836) (.n 14) (.n 3835)),
    .atom (.mul (.n 3837) (.n 1053) (.n 3836))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3675, a3676, a3677, a3678, a3679, a3680, a3681, a3682, a3683, a3684, a3685, -⟩ := hs
  have e3675 := tb_loadHolds_unique a3675 (hw 0 (by norm_num))
  have e3678 := tb_loadHolds_unique a3678 (hw 1 (by norm_num))
  have e3681 := tb_loadHolds_unique a3681 (hw 2 (by norm_num))
  have v3620 : σ (.n 3620) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 38) (by norm_num)).2.2
  have v3631 : σ (.n 3631) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 39) (by norm_num)).2.2
  have hB : σ (.n 3836) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v3631, v3620, a3684, a3683, a3682, e3681, a3680, a3679, e3678, a3677, a3676, e3675]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3685, hB]

set_option maxRecDepth 10000 in
theorem vtB03_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3870) = σ (.n 3837) + σ (.n 1062) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([14], 2)], [([], 8)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3686 [
    .atom (.load (.n 3838) (.n 13) 0),
    .atom (.const (.n 3839) (word 4 0 0)),
    .atom (.mul (.n 3840) (.n 3838) (.n 3839)),
    .atom (.load (.n 3841) (.n 13) 1),
    .atom (.mul (.n 3842) (.n 3841) (.n 3620)),
    .atom (.add (.n 3843) (.n 3840) (.n 3842)),
    .atom (.const (.n 3844) (word 2 0 0)),
    .atom (.mul (.n 3845) (.n 3844) (.n 3826)),
    .atom (.load (.n 3846) (.n 13) 2),
    .atom (.mul (.n 3847) (.n 3846) (.n 3845)),
    .atom (.add (.n 3848) (.n 3843) (.n 3847)),
    .atom (.load (.n 3849) (.n 13) 3),
    .atom (.const (.n 3850) (word 8 0 0)),
    .atom (.mul (.n 3851) (.n 3849) (.n 3850)),
    .atom (.add (.n 3852) (.n 3848) (.n 3851)),
    .atom (.load (.n 3853) (.n 13) 4),
    .atom (.mul (.n 3854) (.n 3853) (.n 3655)),
    .atom (.add (.n 3855) (.n 3852) (.n 3854)),
    .atom (.load (.n 3856) (.n 13) 5),
    .atom (.mul (.n 3857) (.n 3856) (.n 3666)),
    .atom (.add (.n 3858) (.n 3855) (.n 3857)),
    .atom (.load (.n 3859) (.n 13) 6),
    .atom (.mul (.n 3860) (.n 3859) (.n 3677)),
    .atom (.add (.n 3861) (.n 3858) (.n 3860)),
    .atom (.load (.n 3862) (.n 13) 7),
    .atom (.mul (.n 3863) (.n 3862) (.n 3688)),
    .atom (.add (.n 3864) (.n 3861) (.n 3863)),
    .atom (.load (.n 3865) (.n 13) 8),
    .atom (.mul (.n 3866) (.n 3865) (.n 3712)),
    .atom (.add (.n 3867) (.n 3864) (.n 3866)),
    .atom (.add (.n 3868) (.n 14) (.n 3867)),
    .atom (.mul (.n 3869) (.n 1062) (.n 3868)),
    .atom (.add (.n 3870) (.n 3837) (.n 3869))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3686, a3687, a3688, a3689, a3690, a3691, a3692, a3693, a3694, a3695, a3696, a3697, a3698, a3699,
    a3700, a3701, a3702, a3703, a3704, a3705, a3706, a3707, a3708, a3709, a3710, a3711, a3712,
    a3713, a3714, a3715, a3716, a3717, a3718, -⟩ := hs
  have e3686 := tb_loadHolds_unique a3686 (hw 0 (by norm_num))
  have e3689 := tb_loadHolds_unique a3689 (hw 1 (by norm_num))
  have e3694 := tb_loadHolds_unique a3694 (hw 2 (by norm_num))
  have e3697 := tb_loadHolds_unique a3697 (hw 3 (by norm_num))
  have e3701 := tb_loadHolds_unique a3701 (hw 4 (by norm_num))
  have e3704 := tb_loadHolds_unique a3704 (hw 5 (by norm_num))
  have e3707 := tb_loadHolds_unique a3707 (hw 6 (by norm_num))
  have e3710 := tb_loadHolds_unique a3710 (hw 7 (by norm_num))
  have e3713 := tb_loadHolds_unique a3713 (hw 8 (by norm_num))
  have v3620 : σ (.n 3620) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 38) (by norm_num)).2.2
  have v3655 : σ (.n 3655) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 40) (by norm_num)).2.2
  have v3666 : σ (.n 3666) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 41) (by norm_num)).2.2
  have v3677 : σ (.n 3677) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 42) (by norm_num)).2.2
  have v3688 : σ (.n 3688) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 43) (by norm_num)).2.2
  have v3712 : σ (.n 3712) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 44) (by norm_num)).2.2
  have v3826 : σ (.n 3826) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 52) (by norm_num)).2.2
  have hB : σ (.n 3868) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([14], 2)], [([], 8)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)]] := by
    simp only [v3826, v3712, v3688, v3677, v3666, v3655, v3620, a3716, a3715, a3714, e3713, a3712, a3711,
      e3710, a3709, a3708, e3707, a3706, a3705, e3704, a3703, a3702, e3701, a3700, a3699,
      a3698, e3697, a3696, a3695, e3694, a3693, a3692, a3691, a3690, e3689, a3688, a3687,
      e3686]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3718, a3717, hB]

set_option maxRecDepth 10000 in
theorem vtB03_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3896) = σ (.n 3870) + σ (.n 1071) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([11], 2)], [([7], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3719 [
    .atom (.load (.n 3871) (.n 13) 0),
    .atom (.const (.n 3872) (word 2 0 0)),
    .atom (.mul (.n 3873) (.n 3871) (.n 3872)),
    .atom (.mul (.n 3874) (.n 3631) (.n 3655)),
    .atom (.load (.n 3875) (.n 13) 1),
    .atom (.mul (.n 3876) (.n 3875) (.n 3874)),
    .atom (.add (.n 3877) (.n 3873) (.n 3876)),
    .atom (.const (.n 3878) (word 2 0 0)),
    .atom (.mul (.n 3879) (.n 3878) (.n 3780)),
    .atom (.load (.n 3880) (.n 13) 2),
    .atom (.mul (.n 3881) (.n 3880) (.n 3879)),
    .atom (.add (.n 3882) (.n 3877) (.n 3881)),
    .atom (.load (.n 3883) (.n 13) 3),
    .atom (.mul (.n 3884) (.n 3883) (.n 3723)),
    .atom (.add (.n 3885) (.n 3882) (.n 3884)),
    .atom (.load (.n 3886) (.n 13) 4),
    .atom (.const (.n 3887) (word 0 0 0)),
    .atom (.mul (.n 3888) (.n 3886) (.n 3887)),
    .atom (.add (.n 3889) (.n 3885) (.n 3888)),
    .atom (.load (.n 3890) (.n 13) 5),
    .atom (.const (.n 3891) (word 0 0 0)),
    .atom (.mul (.n 3892) (.n 3890) (.n 3891)),
    .atom (.add (.n 3893) (.n 3889) (.n 3892)),
    .atom (.add (.n 3894) (.n 14) (.n 3893)),
    .atom (.mul (.n 3895) (.n 1071) (.n 3894)),
    .atom (.add (.n 3896) (.n 3870) (.n 3895))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3719, a3720, a3721, a3722, a3723, a3724, a3725, a3726, a3727, a3728, a3729, a3730, a3731, a3732,
    a3733, a3734, a3735, a3736, a3737, a3738, a3739, a3740, a3741, a3742, a3743, a3744, -⟩ := hs
  have e3719 := tb_loadHolds_unique a3719 (hw 0 (by norm_num))
  have e3723 := tb_loadHolds_unique a3723 (hw 1 (by norm_num))
  have e3728 := tb_loadHolds_unique a3728 (hw 2 (by norm_num))
  have e3731 := tb_loadHolds_unique a3731 (hw 3 (by norm_num))
  have e3734 := tb_loadHolds_unique a3734 (hw 4 (by norm_num))
  have e3738 := tb_loadHolds_unique a3738 (hw 5 (by norm_num))
  have v3631 : σ (.n 3631) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 39) (by norm_num)).2.2
  have v3655 : σ (.n 3655) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 40) (by norm_num)).2.2
  have v3723 : σ (.n 3723) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 45) (by norm_num)).2.2
  have v3780 : σ (.n 3780) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 49) (by norm_num)).2.2
  have hB : σ (.n 3894) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([11], 2)], [([7], 1)], [([], 0)], [([], 0)]] := by
    simp only [v3780, v3723, v3655, v3631, a3742, a3741, a3740, a3739, e3738, a3737, a3736, a3735, e3734,
      a3733, a3732, e3731, a3730, a3729, e3728, a3727, a3726, a3725, a3724, e3723, a3722,
      a3721, a3720, e3719]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3744, a3743, hB]

set_option maxRecDepth 10000 in
theorem vtB03_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3938) = σ (.n 3896) + σ (.n 1080) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([7, 3], 1)], [([12], 2)], [([8], 1), ([5, 8], 1), ([6, 8], 1), ([5, 0], 4), ([6, 1], 1)], [([9], 1), ([5, 9], 1), ([6, 9], 1)], [([10], 1), ([5, 10], 1), ([6, 10], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3745 [
    .atom (.load (.n 3897) (.n 13) 0),
    .atom (.const (.n 3898) (word 2 0 0)),
    .atom (.mul (.n 3899) (.n 3897) (.n 3898)),
    .atom (.mul (.n 3900) (.n 3723) (.n 3666)),
    .atom (.load (.n 3901) (.n 13) 1),
    .atom (.mul (.n 3902) (.n 3901) (.n 3900)),
    .atom (.add (.n 3903) (.n 3899) (.n 3902)),
    .atom (.const (.n 3904) (word 2 0 0)),
    .atom (.mul (.n 3905) (.n 3904) (.n 3791)),
    .atom (.load (.n 3906) (.n 13) 2),
    .atom (.mul (.n 3907) (.n 3906) (.n 3905)),
    .atom (.add (.n 3908) (.n 3903) (.n 3907)),
    .atom (.mul (.n 3909) (.n 3688) (.n 3734)),
    .atom (.add (.n 3910) (.n 3734) (.n 3909)),
    .atom (.mul (.n 3911) (.n 3712) (.n 3734)),
    .atom (.add (.n 3912) (.n 3910) (.n 3911)),
    .atom (.const (.n 3913) (word 4 0 0)),
    .atom (.mul (.n 3914) (.n 3688) (.n 3620)),
    .atom (.mul (.n 3915) (.n 3913) (.n 3914)),
    .atom (.add (.n 3916) (.n 3912) (.n 3915)),
    .atom (.mul (.n 3917) (.n 3712) (.n 3631)),
    .atom (.add (.n 3918) (.n 3916) (.n 3917)),
    .atom (.load (.n 3919) (.n 13) 3),
    .atom (.mul (.n 3920) (.n 3919) (.n 3918)),
    .atom (.add (.n 3921) (.n 3908) (.n 3920)),
    .atom (.mul (.n 3922) (.n 3688) (.n 3745)),
    .atom (.add (.n 3923) (.n 3745) (.n 3922)),
    .atom (.mul (.n 3924) (.n 3712) (.n 3745)),
    .atom (.add (.n 3925) (.n 3923) (.n 3924)),
    .atom (.load (.n 3926) (.n 13) 4),
    .atom (.mul (.n 3927) (.n 3926) (.n 3925)),
    .atom (.add (.n 3928) (.n 3921) (.n 3927)),
    .atom (.mul (.n 3929) (.n 3688) (.n 3769)),
    .atom (.add (.n 3930) (.n 3769) (.n 3929)),
    .atom (.mul (.n 3931) (.n 3712) (.n 3769)),
    .atom (.add (.n 3932) (.n 3930) (.n 3931)),
    .atom (.load (.n 3933) (.n 13) 5),
    .atom (.mul (.n 3934) (.n 3933) (.n 3932)),
    .atom (.add (.n 3935) (.n 3928) (.n 3934)),
    .atom (.add (.n 3936) (.n 14) (.n 3935)),
    .atom (.mul (.n 3937) (.n 1080) (.n 3936)),
    .atom (.add (.n 3938) (.n 3896) (.n 3937))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3745, a3746, a3747, a3748, a3749, a3750, a3751, a3752, a3753, a3754, a3755, a3756, a3757, a3758,
    a3759, a3760, a3761, a3762, a3763, a3764, a3765, a3766, a3767, a3768, a3769, a3770, a3771,
    a3772, a3773, a3774, a3775, a3776, a3777, a3778, a3779, a3780, a3781, a3782, a3783, a3784,
    a3785, a3786, -⟩ := hs
  have e3745 := tb_loadHolds_unique a3745 (hw 0 (by norm_num))
  have e3749 := tb_loadHolds_unique a3749 (hw 1 (by norm_num))
  have e3754 := tb_loadHolds_unique a3754 (hw 2 (by norm_num))
  have e3767 := tb_loadHolds_unique a3767 (hw 3 (by norm_num))
  have e3774 := tb_loadHolds_unique a3774 (hw 4 (by norm_num))
  have e3781 := tb_loadHolds_unique a3781 (hw 5 (by norm_num))
  have v3620 : σ (.n 3620) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 38) (by norm_num)).2.2
  have v3631 : σ (.n 3631) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 39) (by norm_num)).2.2
  have v3666 : σ (.n 3666) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 41) (by norm_num)).2.2
  have v3688 : σ (.n 3688) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 43) (by norm_num)).2.2
  have v3712 : σ (.n 3712) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 44) (by norm_num)).2.2
  have v3723 : σ (.n 3723) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 45) (by norm_num)).2.2
  have v3734 : σ (.n 3734) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 46) (by norm_num)).2.2
  have v3745 : σ (.n 3745) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 47) (by norm_num)).2.2
  have v3769 : σ (.n 3769) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3791 : σ (.n 3791) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 50) (by norm_num)).2.2
  have hB : σ (.n 3936) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([7, 3], 1)], [([12], 2)], [([8], 1), ([5, 8], 1), ([6, 8], 1), ([5, 0], 4), ([6, 1], 1)], [([9], 1), ([5, 9], 1), ([6, 9], 1)], [([10], 1), ([5, 10], 1), ([6, 10], 1)]] := by
    simp only [v3791, v3769, v3745, v3734, v3723, v3712, v3688, v3666, v3631, v3620, a3784, a3783, a3782,
      e3781, a3780, a3779, a3778, a3777, a3776, a3775, e3774, a3773, a3772, a3771, a3770,
      a3769, a3768, e3767, a3766, a3765, a3764, a3763, a3762, a3761, a3760, a3759, a3758,
      a3757, a3756, a3755, e3754, a3753, a3752, a3751, a3750, e3749, a3748, a3747, a3746,
      e3745]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3786, a3785, hB]

set_option maxRecDepth 10000 in
theorem vtB03_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3962) = σ (.n 3938) + σ (.n 1089) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([13], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3787 [
    .atom (.load (.n 3939) (.n 13) 0),
    .atom (.const (.n 3940) (word 2 0 0)),
    .atom (.mul (.n 3941) (.n 3939) (.n 3940)),
    .atom (.mul (.n 3942) (.n 3631) (.n 3677)),
    .atom (.load (.n 3943) (.n 13) 1),
    .atom (.mul (.n 3944) (.n 3943) (.n 3942)),
    .atom (.add (.n 3945) (.n 3941) (.n 3944)),
    .atom (.const (.n 3946) (word 2 0 0)),
    .atom (.mul (.n 3947) (.n 3946) (.n 3802)),
    .atom (.load (.n 3948) (.n 13) 2),
    .atom (.mul (.n 3949) (.n 3948) (.n 3947)),
    .atom (.add (.n 3950) (.n 3945) (.n 3949)),
    .atom (.load (.n 3951) (.n 13) 3),
    .atom (.mul (.n 3952) (.n 3951) (.n 3734)),
    .atom (.add (.n 3953) (.n 3950) (.n 3952)),
    .atom (.load (.n 3954) (.n 13) 4),
    .atom (.mul (.n 3955) (.n 3954) (.n 3745)),
    .atom (.add (.n 3956) (.n 3953) (.n 3955)),
    .atom (.load (.n 3957) (.n 13) 5),
    .atom (.mul (.n 3958) (.n 3957) (.n 3769)),
    .atom (.add (.n 3959) (.n 3956) (.n 3958)),
    .atom (.add (.n 3960) (.n 14) (.n 3959)),
    .atom (.mul (.n 3961) (.n 1089) (.n 3960)),
    .atom (.add (.n 3962) (.n 3938) (.n 3961))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3787, a3788, a3789, a3790, a3791, a3792, a3793, a3794, a3795, a3796, a3797, a3798, a3799, a3800,
    a3801, a3802, a3803, a3804, a3805, a3806, a3807, a3808, a3809, a3810, -⟩ := hs
  have e3787 := tb_loadHolds_unique a3787 (hw 0 (by norm_num))
  have e3791 := tb_loadHolds_unique a3791 (hw 1 (by norm_num))
  have e3796 := tb_loadHolds_unique a3796 (hw 2 (by norm_num))
  have e3799 := tb_loadHolds_unique a3799 (hw 3 (by norm_num))
  have e3802 := tb_loadHolds_unique a3802 (hw 4 (by norm_num))
  have e3805 := tb_loadHolds_unique a3805 (hw 5 (by norm_num))
  have v3631 : σ (.n 3631) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 39) (by norm_num)).2.2
  have v3677 : σ (.n 3677) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 42) (by norm_num)).2.2
  have v3734 : σ (.n 3734) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 46) (by norm_num)).2.2
  have v3745 : σ (.n 3745) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 47) (by norm_num)).2.2
  have v3769 : σ (.n 3769) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3802 : σ (.n 3802) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 51) (by norm_num)).2.2
  have hB : σ (.n 3960) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([13], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
    simp only [v3802, v3769, v3745, v3734, v3677, v3631, a3808, a3807, a3806, e3805, a3804, a3803, e3802,
      a3801, a3800, e3799, a3798, a3797, e3796, a3795, a3794, a3793, a3792, e3791, a3790,
      a3789, a3788, e3787]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3810, a3809, hB]

set_option maxRecDepth 10000 in
theorem vtSide03 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3962) =
      vtSideVal [σ (.n 1053), σ (.n 1062), σ (.n 1071), σ (.n 1080), σ (.n 1089)]
        (σ (.n 14)) W ev vtBTerms03 := by
  rw [vtB03_4 h hw hev, vtB03_3 h hw hev, vtB03_2 h hw hev, vtB03_1 h hw hev, vtB03_0 h hw hev]
  simp only [vtSideVal, vtBTerms03, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD3_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3968) = σ (.n 1978) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3812 [
    .atom (.const (.n 3964) (word 3 0 0)),
    .atom (.mul (.n 3965) (.n 3964) (.n 3620)),
    .atom (.load (.n 3966) (.n 13) 1),
    .atom (.mul (.n 3967) (.n 3966) (.n 3965)),
    .atom (.mul (.n 3968) (.n 1978) (.n 3967))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3812, a3813, a3814, a3815, a3816, -⟩ := hs
  have e3814 := tb_loadHolds_unique a3814 (hw 1 (by norm_num))
  have v3620 : σ (.n 3620) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 38) (by norm_num)).2.2
  have hB : σ (.n 3967) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v3620, a3815, e3814, a3813, a3812]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3816, hB]

set_option maxRecDepth 10000 in
theorem vtD3_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3974) = σ (.n 3968) + σ (.n 1980) * vtSlots W ev 0
      [[], [], [([14], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3817 [
    .atom (.const (.n 3969) (word 3 0 0)),
    .atom (.mul (.n 3970) (.n 3969) (.n 3826)),
    .atom (.load (.n 3971) (.n 13) 2),
    .atom (.mul (.n 3972) (.n 3971) (.n 3970)),
    .atom (.mul (.n 3973) (.n 1980) (.n 3972)),
    .atom (.add (.n 3974) (.n 3968) (.n 3973))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3817, a3818, a3819, a3820, a3821, a3822, -⟩ := hs
  have e3819 := tb_loadHolds_unique a3819 (hw 2 (by norm_num))
  have v3826 : σ (.n 3826) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 52) (by norm_num)).2.2
  have hB : σ (.n 3972) = vtSlots W ev 0 [[], [], [([14], 3)], [], [], [], [], [], []] := by
    simp only [v3826, a3820, e3819, a3818, a3817]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3822, a3821, hB]

set_option maxRecDepth 10000 in
theorem vtD3_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3980) = σ (.n 3974) + σ (.n 1982) * vtSlots W ev 0
      [[], [], [([11], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3823 [
    .atom (.const (.n 3975) (word 3 0 0)),
    .atom (.mul (.n 3976) (.n 3975) (.n 3780)),
    .atom (.load (.n 3977) (.n 13) 2),
    .atom (.mul (.n 3978) (.n 3977) (.n 3976)),
    .atom (.mul (.n 3979) (.n 1982) (.n 3978)),
    .atom (.add (.n 3980) (.n 3974) (.n 3979))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3823, a3824, a3825, a3826, a3827, a3828, -⟩ := hs
  have e3825 := tb_loadHolds_unique a3825 (hw 2 (by norm_num))
  have v3780 : σ (.n 3780) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 49) (by norm_num)).2.2
  have hB : σ (.n 3978) = vtSlots W ev 0 [[], [], [([11], 3)], [], [], []] := by
    simp only [v3780, a3826, e3825, a3824, a3823]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3828, a3827, hB]

set_option maxRecDepth 10000 in
theorem vtD3_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3986) = σ (.n 3980) + σ (.n 1984) * vtSlots W ev 0
      [[], [], [([12], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3829 [
    .atom (.const (.n 3981) (word 3 0 0)),
    .atom (.mul (.n 3982) (.n 3981) (.n 3791)),
    .atom (.load (.n 3983) (.n 13) 2),
    .atom (.mul (.n 3984) (.n 3983) (.n 3982)),
    .atom (.mul (.n 3985) (.n 1984) (.n 3984)),
    .atom (.add (.n 3986) (.n 3980) (.n 3985))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3829, a3830, a3831, a3832, a3833, a3834, -⟩ := hs
  have e3831 := tb_loadHolds_unique a3831 (hw 2 (by norm_num))
  have v3791 : σ (.n 3791) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 50) (by norm_num)).2.2
  have hB : σ (.n 3984) = vtSlots W ev 0 [[], [], [([12], 3)], [], [], []] := by
    simp only [v3791, a3832, e3831, a3830, a3829]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3834, a3833, hB]

set_option maxRecDepth 10000 in
theorem vtD3_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3992) = σ (.n 3986) + σ (.n 1986) * vtSlots W ev 0
      [[], [], [([13], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3835 [
    .atom (.const (.n 3987) (word 3 0 0)),
    .atom (.mul (.n 3988) (.n 3987) (.n 3802)),
    .atom (.load (.n 3989) (.n 13) 2),
    .atom (.mul (.n 3990) (.n 3989) (.n 3988)),
    .atom (.mul (.n 3991) (.n 1986) (.n 3990)),
    .atom (.add (.n 3992) (.n 3986) (.n 3991))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3835, a3836, a3837, a3838, a3839, a3840, -⟩ := hs
  have e3837 := tb_loadHolds_unique a3837 (hw 2 (by norm_num))
  have v3802 : σ (.n 3802) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 51) (by norm_num)).2.2
  have hB : σ (.n 3990) = vtSlots W ev 0 [[], [], [([13], 3)], [], [], []] := by
    simp only [v3802, a3838, e3837, a3836, a3835]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3840, a3839, hB]

set_option maxRecDepth 10000 in
theorem vtSide13 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3993) =
      vtSideVal [σ (.n 1978), σ (.n 1980), σ (.n 1982), σ (.n 1984), σ (.n 1986)]
        (σ (.n 14)) W ev vtBTerms13 := by
  have hF0 : σ (.n 3962) =
      vtSideVal [σ (.n 1978), σ (.n 1980), σ (.n 1982), σ (.n 1984), σ (.n 1986)]
        (σ (.n 14)) W ev vtBTerms03 := by
    rw [vtPullSels3 h]; exact vtSide03 h hw hev
  have a3841 := h.atomAt 3841 (.add (.n 3993) (.n 3962) (.n 3992)) (by decide +kernel)
  simp only [Atom.Holds] at a3841
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull3, ← hF0, a3841, vtD3_4 h hw hev, vtD3_3 h hw hev, vtD3_2 h hw hev, vtD3_1 h hw hev, vtD3_0 h hw hev]
  simp only [vtDiffSum, vtDTerms3, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide23 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 4002) =
      vtSideVal [σ (.n 2139), σ (.n 2148), σ (.n 2157), σ (.n 2166)]
        (0) (fun _ ↦ 1) ev vtBTerms23 := by
  obtain ⟨_, hs⟩ := h.sliceAt 3844 [
    .atom (.mul (.n 3996) (.n 2139) (.n 3780)),
    .atom (.mul (.n 3997) (.n 2148) (.n 3791)),
    .atom (.add (.n 3998) (.n 3996) (.n 3997)),
    .atom (.mul (.n 3999) (.n 2157) (.n 3802)),
    .atom (.add (.n 4000) (.n 3998) (.n 3999)),
    .atom (.mul (.n 4001) (.n 2166) (.n 3826)),
    .atom (.add (.n 4002) (.n 4000) (.n 4001))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3844, a3845, a3846, a3847, a3848, a3849, a3850, -⟩ := hs
  have v3780 : σ (.n 3780) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 49) (by norm_num)).2.2
  have v3791 : σ (.n 3791) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 50) (by norm_num)).2.2
  have v3802 : σ (.n 3802) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 51) (by norm_num)).2.2
  have v3826 : σ (.n 3826) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 52) (by norm_num)).2.2
  rw [a3850, a3848, a3846, a3844, a3845, a3847, a3849, v3780, v3791, v3802, v3826]
  simp only [vtSideVal, vtBTerms23, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
