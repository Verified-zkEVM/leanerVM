/-
  LeanVM.Guest.B1.Tables.Vt.PushPad

  `verify_tables`' push side total: the framework decomposition's accumulator, the padding sum
  over the tables' blocks, the selector sum and the GKR leaf value.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SelFw

/-!
# The push side's padding and total (G:2126-2158)

`vtPushPadData` lists the push side's table blocks with their table, the value of their eq weight's
copy (`block_eq_hi[b]`) and their nonzero `COORD_PADDING` terms (slot, value). `vt_push_total`:
`bus_table_total[PUSH]` is the framework accumulator, plus `Σ_t pad_weight[t]·Σ_b eq_b·(β + 1 +
Σ w_i·pad_i)`, plus `1 + selector_sum`, plus the GKR push leaf value.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- A table's part of a side's padding sum: its blocks' eq weights (by their copies' values)
times `β + 1 + Σ w_i·pad_i` (`β1` the side's `β + 1`). -/
def vtPadTable (eqc W : ℕ → E) (β1 : E) (data : List (ℕ × ℕ × ℕ × List (ℕ × ℕ))) (t : ℕ) : E :=
  ((data.filter fun x ↦ x.2.1 = t).map fun x ↦
    eqc x.2.2.1 * (β1 + (x.2.2.2.map fun ic ↦ W ic.1 * word ic.2 0 0).sum)).sum

/-- A side's padding sum: per table, its padding weight times its part. -/
def vtPadSum (eqc pw W : ℕ → E) (β1 : E) (data : List (ℕ × ℕ × ℕ × List (ℕ × ℕ))) : E :=
  pw 0 * vtPadTable eqc W β1 data 0 + pw 1 * vtPadTable eqc W β1 data 1 +
    pw 2 * vtPadTable eqc W β1 data 2 + pw 3 * vtPadTable eqc W β1 data 3 +
    pw 4 * vtPadTable eqc W β1 data 4 + pw 5 * vtPadTable eqc W β1 data 5

/-- The push side's table blocks: block, table, copy value, padding terms. -/
def vtPushPadData : List (ℕ × ℕ × ℕ × List (ℕ × ℕ)) :=
  [(3, 0, 3051, [(0, 1)]), (4, 0, 3066, [(0, 4), (3, 1)]), (5, 0, 3081, [(0, 2)]),
    (6, 0, 3096, [(0, 2)]), (7, 0, 3111, [(0, 2)]), (8, 1, 3130, [(0, 1)]),
    (9, 1, 3149, [(0, 4), (3, 2)]), (10, 1, 3168, [(0, 2)]), (11, 1, 3187, [(0, 2)]),
    (12, 1, 3206, [(0, 2)]), (13, 2, 3225, [(0, 1)]), (14, 2, 3244, [(0, 4), (3, 4)]),
    (15, 2, 3263, [(0, 2)]), (16, 3, 3282, [(0, 1)]), (17, 3, 3301, [(0, 4), (3, 8)]),
    (18, 3, 3320, [(0, 2)]), (19, 3, 3339, [(0, 2)]), (20, 3, 3358, [(0, 2)]),
    (21, 4, 3377, [(0, 1)]), (22, 4, 3396, [(0, 4), (3, 16)]), (23, 4, 3415, [(0, 2)]),
    (24, 4, 3434, [(0, 2)]), (25, 4, 3453, [(0, 2)]), (26, 5, 3472, [(0, 1)]),
    (27, 5, 3491, [(0, 4), (3, 32)]), (28, 5, 3510, [(0, 2)]), (29, 5, 3529, [(0, 2)]),
    (30, 5, 3548, [(0, 2)]), (31, 5, 3567, [(0, 2)]), (32, 5, 3586, [(0, 2)]),
    (33, 5, 3605, [(0, 2)]), (34, 5, 3624, [(0, 2)]), (35, 5, 3643, [(0, 2)]),
    (36, 5, 3662, [(0, 2)]), (37, 5, 3681, [(0, 2)]), (38, 5, 3700, [(0, 2)]),
    (39, 5, 3719, [(0, 2)]), (40, 5, 3738, [(0, 2)]),
    (41, 5, 3757, [(0, 2), (3, 17376452488221285863), (4, 9571781953733019530)]),
    (42, 5, 3776, [(0, 2), (3, 15391093639620504046), (4, 13624874521033984333)]),
    (43, 5, 3795, [(0, 2), (3, 10027350355371872343), (4, 18417369716475457492)]),
    (44, 5, 3814, [(0, 2), (3, 10448040663659726788), (4, 10113917136857017974)]),
    (45, 5, 3833, [(0, 2), (3, 12479658147685402012), (4, 3500241080921619556)]),
    (46, 5, 3852, [(0, 2), (3, 16959053435453822517), (4, 12224711289652453635)]),
    (47, 5, 3871, [(0, 2), (3, 9342009439668884831), (4, 4879704952849025062)]),
    (48, 5, 3890, [(0, 2), (3, 140226327413610143), (4, 424854978622500449)]),
    (49, 5, 3909, [(0, 2), (3, 7259519967065370866)]),
    (50, 5, 3928, [(0, 2), (3, 7004910057750291985), (4, 13293599522548616907)]),
    (51, 5, 3947, [(0, 2), (3, 10105770293752443592), (4, 10668034807192757780)]),
    (52, 5, 3966, [(0, 2), (3, 1747952066141424100), (4, 1654286879329379778)]),
    (53, 5, 3985, [(0, 2), (3, 8500057116360352059), (4, 16929593379567477321)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The push side's total.** -/
theorem vt_push_total {rd : Reader} {σ : Val} (h : VtH rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i)) :
    σ (.n 4411) = σ (.n 3036) + vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W
      (σ (.n 2853)) vtPushPadData + (1 + σ (.n 3984)) + σ (.n 27) := by
  have a3484 := h.atomAt 3484 (.load (.n 3986) (.n 14) 0) (by decide +kernel)
  have a3485 := h.atomAt 3485 (.add (.n 3987) (.n 2853) (.n 3986)) (by decide +kernel)
  have a3486 := h.atomAt 3486 (.mul (.n 3988) (.n 3051) (.n 3987)) (by decide +kernel)
  have a3487 := h.atomAt 3487 (.load (.n 3989) (.n 14) 0) (by decide +kernel)
  have a3488 := h.atomAt 3488 (.const (.n 3990) (word 4 0 0)) (by decide +kernel)
  have a3489 := h.atomAt 3489 (.mul (.n 3991) (.n 3989) (.n 3990)) (by decide +kernel)
  have a3490 := h.atomAt 3490 (.add (.n 3992) (.n 2853) (.n 3991)) (by decide +kernel)
  have a3491 := h.atomAt 3491 (.load (.n 3993) (.n 14) 3) (by decide +kernel)
  have a3492 := h.atomAt 3492 (.add (.n 3994) (.n 3992) (.n 3993)) (by decide +kernel)
  have a3493 := h.atomAt 3493 (.mul (.n 3995) (.n 3066) (.n 3994)) (by decide +kernel)
  have a3494 := h.atomAt 3494 (.add (.n 3996) (.n 3988) (.n 3995)) (by decide +kernel)
  have a3495 := h.atomAt 3495 (.load (.n 3997) (.n 14) 0) (by decide +kernel)
  have a3496 := h.atomAt 3496 (.const (.n 3998) (word 2 0 0)) (by decide +kernel)
  have a3497 := h.atomAt 3497 (.mul (.n 3999) (.n 3997) (.n 3998)) (by decide +kernel)
  have a3498 := h.atomAt 3498 (.add (.n 4000) (.n 2853) (.n 3999)) (by decide +kernel)
  have a3499 := h.atomAt 3499 (.mul (.n 4001) (.n 3081) (.n 4000)) (by decide +kernel)
  have a3500 := h.atomAt 3500 (.add (.n 4002) (.n 3996) (.n 4001)) (by decide +kernel)
  have a3501 := h.atomAt 3501 (.load (.n 4003) (.n 14) 0) (by decide +kernel)
  have a3502 := h.atomAt 3502 (.const (.n 4004) (word 2 0 0)) (by decide +kernel)
  have a3503 := h.atomAt 3503 (.mul (.n 4005) (.n 4003) (.n 4004)) (by decide +kernel)
  have a3504 := h.atomAt 3504 (.add (.n 4006) (.n 2853) (.n 4005)) (by decide +kernel)
  have a3505 := h.atomAt 3505 (.mul (.n 4007) (.n 3096) (.n 4006)) (by decide +kernel)
  have a3506 := h.atomAt 3506 (.add (.n 4008) (.n 4002) (.n 4007)) (by decide +kernel)
  have a3507 := h.atomAt 3507 (.load (.n 4009) (.n 14) 0) (by decide +kernel)
  have a3508 := h.atomAt 3508 (.const (.n 4010) (word 2 0 0)) (by decide +kernel)
  have a3509 := h.atomAt 3509 (.mul (.n 4011) (.n 4009) (.n 4010)) (by decide +kernel)
  have a3510 := h.atomAt 3510 (.add (.n 4012) (.n 2853) (.n 4011)) (by decide +kernel)
  have a3511 := h.atomAt 3511 (.mul (.n 4013) (.n 3111) (.n 4012)) (by decide +kernel)
  have a3512 := h.atomAt 3512 (.add (.n 4014) (.n 4008) (.n 4013)) (by decide +kernel)
  have a3513 := h.atomAt 3513 (.mul (.n 4015) (.n 2646) (.n 4014)) (by decide +kernel)
  have a3514 := h.atomAt 3514 (.load (.n 4016) (.n 14) 0) (by decide +kernel)
  have a3515 := h.atomAt 3515 (.add (.n 4017) (.n 2853) (.n 4016)) (by decide +kernel)
  have a3516 := h.atomAt 3516 (.mul (.n 4018) (.n 3130) (.n 4017)) (by decide +kernel)
  have a3517 := h.atomAt 3517 (.load (.n 4019) (.n 14) 0) (by decide +kernel)
  have a3518 := h.atomAt 3518 (.const (.n 4020) (word 4 0 0)) (by decide +kernel)
  have a3519 := h.atomAt 3519 (.mul (.n 4021) (.n 4019) (.n 4020)) (by decide +kernel)
  have a3520 := h.atomAt 3520 (.add (.n 4022) (.n 2853) (.n 4021)) (by decide +kernel)
  have a3521 := h.atomAt 3521 (.load (.n 4023) (.n 14) 3) (by decide +kernel)
  have a3522 := h.atomAt 3522 (.const (.n 4024) (word 2 0 0)) (by decide +kernel)
  have a3523 := h.atomAt 3523 (.mul (.n 4025) (.n 4023) (.n 4024)) (by decide +kernel)
  have a3524 := h.atomAt 3524 (.add (.n 4026) (.n 4022) (.n 4025)) (by decide +kernel)
  have a3525 := h.atomAt 3525 (.mul (.n 4027) (.n 3149) (.n 4026)) (by decide +kernel)
  have a3526 := h.atomAt 3526 (.add (.n 4028) (.n 4018) (.n 4027)) (by decide +kernel)
  have a3527 := h.atomAt 3527 (.load (.n 4029) (.n 14) 0) (by decide +kernel)
  have a3528 := h.atomAt 3528 (.const (.n 4030) (word 2 0 0)) (by decide +kernel)
  have a3529 := h.atomAt 3529 (.mul (.n 4031) (.n 4029) (.n 4030)) (by decide +kernel)
  have a3530 := h.atomAt 3530 (.add (.n 4032) (.n 2853) (.n 4031)) (by decide +kernel)
  have a3531 := h.atomAt 3531 (.mul (.n 4033) (.n 3168) (.n 4032)) (by decide +kernel)
  have a3532 := h.atomAt 3532 (.add (.n 4034) (.n 4028) (.n 4033)) (by decide +kernel)
  have a3533 := h.atomAt 3533 (.load (.n 4035) (.n 14) 0) (by decide +kernel)
  have a3534 := h.atomAt 3534 (.const (.n 4036) (word 2 0 0)) (by decide +kernel)
  have a3535 := h.atomAt 3535 (.mul (.n 4037) (.n 4035) (.n 4036)) (by decide +kernel)
  have a3536 := h.atomAt 3536 (.add (.n 4038) (.n 2853) (.n 4037)) (by decide +kernel)
  have a3537 := h.atomAt 3537 (.mul (.n 4039) (.n 3187) (.n 4038)) (by decide +kernel)
  have a3538 := h.atomAt 3538 (.add (.n 4040) (.n 4034) (.n 4039)) (by decide +kernel)
  have a3539 := h.atomAt 3539 (.load (.n 4041) (.n 14) 0) (by decide +kernel)
  have a3540 := h.atomAt 3540 (.const (.n 4042) (word 2 0 0)) (by decide +kernel)
  have a3541 := h.atomAt 3541 (.mul (.n 4043) (.n 4041) (.n 4042)) (by decide +kernel)
  have a3542 := h.atomAt 3542 (.add (.n 4044) (.n 2853) (.n 4043)) (by decide +kernel)
  have a3543 := h.atomAt 3543 (.mul (.n 4045) (.n 3206) (.n 4044)) (by decide +kernel)
  have a3544 := h.atomAt 3544 (.add (.n 4046) (.n 4040) (.n 4045)) (by decide +kernel)
  have a3545 := h.atomAt 3545 (.mul (.n 4047) (.n 2660) (.n 4046)) (by decide +kernel)
  have a3546 := h.atomAt 3546 (.add (.n 4048) (.n 4015) (.n 4047)) (by decide +kernel)
  have a3547 := h.atomAt 3547 (.load (.n 4049) (.n 14) 0) (by decide +kernel)
  have a3548 := h.atomAt 3548 (.add (.n 4050) (.n 2853) (.n 4049)) (by decide +kernel)
  have a3549 := h.atomAt 3549 (.mul (.n 4051) (.n 3225) (.n 4050)) (by decide +kernel)
  have a3550 := h.atomAt 3550 (.load (.n 4052) (.n 14) 0) (by decide +kernel)
  have a3551 := h.atomAt 3551 (.const (.n 4053) (word 4 0 0)) (by decide +kernel)
  have a3552 := h.atomAt 3552 (.mul (.n 4054) (.n 4052) (.n 4053)) (by decide +kernel)
  have a3553 := h.atomAt 3553 (.add (.n 4055) (.n 2853) (.n 4054)) (by decide +kernel)
  have a3554 := h.atomAt 3554 (.load (.n 4056) (.n 14) 3) (by decide +kernel)
  have a3555 := h.atomAt 3555 (.const (.n 4057) (word 4 0 0)) (by decide +kernel)
  have a3556 := h.atomAt 3556 (.mul (.n 4058) (.n 4056) (.n 4057)) (by decide +kernel)
  have a3557 := h.atomAt 3557 (.add (.n 4059) (.n 4055) (.n 4058)) (by decide +kernel)
  have a3558 := h.atomAt 3558 (.mul (.n 4060) (.n 3244) (.n 4059)) (by decide +kernel)
  have a3559 := h.atomAt 3559 (.add (.n 4061) (.n 4051) (.n 4060)) (by decide +kernel)
  have a3560 := h.atomAt 3560 (.load (.n 4062) (.n 14) 0) (by decide +kernel)
  have a3561 := h.atomAt 3561 (.const (.n 4063) (word 2 0 0)) (by decide +kernel)
  have a3562 := h.atomAt 3562 (.mul (.n 4064) (.n 4062) (.n 4063)) (by decide +kernel)
  have a3563 := h.atomAt 3563 (.add (.n 4065) (.n 2853) (.n 4064)) (by decide +kernel)
  have a3564 := h.atomAt 3564 (.mul (.n 4066) (.n 3263) (.n 4065)) (by decide +kernel)
  have a3565 := h.atomAt 3565 (.add (.n 4067) (.n 4061) (.n 4066)) (by decide +kernel)
  have a3566 := h.atomAt 3566 (.mul (.n 4068) (.n 2674) (.n 4067)) (by decide +kernel)
  have a3567 := h.atomAt 3567 (.add (.n 4069) (.n 4048) (.n 4068)) (by decide +kernel)
  have a3568 := h.atomAt 3568 (.load (.n 4070) (.n 14) 0) (by decide +kernel)
  have a3569 := h.atomAt 3569 (.add (.n 4071) (.n 2853) (.n 4070)) (by decide +kernel)
  have a3570 := h.atomAt 3570 (.mul (.n 4072) (.n 3282) (.n 4071)) (by decide +kernel)
  have a3571 := h.atomAt 3571 (.load (.n 4073) (.n 14) 0) (by decide +kernel)
  have a3572 := h.atomAt 3572 (.const (.n 4074) (word 4 0 0)) (by decide +kernel)
  have a3573 := h.atomAt 3573 (.mul (.n 4075) (.n 4073) (.n 4074)) (by decide +kernel)
  have a3574 := h.atomAt 3574 (.add (.n 4076) (.n 2853) (.n 4075)) (by decide +kernel)
  have a3575 := h.atomAt 3575 (.load (.n 4077) (.n 14) 3) (by decide +kernel)
  have a3576 := h.atomAt 3576 (.const (.n 4078) (word 8 0 0)) (by decide +kernel)
  have a3577 := h.atomAt 3577 (.mul (.n 4079) (.n 4077) (.n 4078)) (by decide +kernel)
  have a3578 := h.atomAt 3578 (.add (.n 4080) (.n 4076) (.n 4079)) (by decide +kernel)
  have a3579 := h.atomAt 3579 (.mul (.n 4081) (.n 3301) (.n 4080)) (by decide +kernel)
  have a3580 := h.atomAt 3580 (.add (.n 4082) (.n 4072) (.n 4081)) (by decide +kernel)
  have a3581 := h.atomAt 3581 (.load (.n 4083) (.n 14) 0) (by decide +kernel)
  have a3582 := h.atomAt 3582 (.const (.n 4084) (word 2 0 0)) (by decide +kernel)
  have a3583 := h.atomAt 3583 (.mul (.n 4085) (.n 4083) (.n 4084)) (by decide +kernel)
  have a3584 := h.atomAt 3584 (.add (.n 4086) (.n 2853) (.n 4085)) (by decide +kernel)
  have a3585 := h.atomAt 3585 (.mul (.n 4087) (.n 3320) (.n 4086)) (by decide +kernel)
  have a3586 := h.atomAt 3586 (.add (.n 4088) (.n 4082) (.n 4087)) (by decide +kernel)
  have a3587 := h.atomAt 3587 (.load (.n 4089) (.n 14) 0) (by decide +kernel)
  have a3588 := h.atomAt 3588 (.const (.n 4090) (word 2 0 0)) (by decide +kernel)
  have a3589 := h.atomAt 3589 (.mul (.n 4091) (.n 4089) (.n 4090)) (by decide +kernel)
  have a3590 := h.atomAt 3590 (.add (.n 4092) (.n 2853) (.n 4091)) (by decide +kernel)
  have a3591 := h.atomAt 3591 (.mul (.n 4093) (.n 3339) (.n 4092)) (by decide +kernel)
  have a3592 := h.atomAt 3592 (.add (.n 4094) (.n 4088) (.n 4093)) (by decide +kernel)
  have a3593 := h.atomAt 3593 (.load (.n 4095) (.n 14) 0) (by decide +kernel)
  have a3594 := h.atomAt 3594 (.const (.n 4096) (word 2 0 0)) (by decide +kernel)
  have a3595 := h.atomAt 3595 (.mul (.n 4097) (.n 4095) (.n 4096)) (by decide +kernel)
  have a3596 := h.atomAt 3596 (.add (.n 4098) (.n 2853) (.n 4097)) (by decide +kernel)
  have a3597 := h.atomAt 3597 (.mul (.n 4099) (.n 3358) (.n 4098)) (by decide +kernel)
  have a3598 := h.atomAt 3598 (.add (.n 4100) (.n 4094) (.n 4099)) (by decide +kernel)
  have a3599 := h.atomAt 3599 (.mul (.n 4101) (.n 2688) (.n 4100)) (by decide +kernel)
  have a3600 := h.atomAt 3600 (.add (.n 4102) (.n 4069) (.n 4101)) (by decide +kernel)
  have a3601 := h.atomAt 3601 (.load (.n 4103) (.n 14) 0) (by decide +kernel)
  have a3602 := h.atomAt 3602 (.add (.n 4104) (.n 2853) (.n 4103)) (by decide +kernel)
  have a3603 := h.atomAt 3603 (.mul (.n 4105) (.n 3377) (.n 4104)) (by decide +kernel)
  have a3604 := h.atomAt 3604 (.load (.n 4106) (.n 14) 0) (by decide +kernel)
  have a3605 := h.atomAt 3605 (.const (.n 4107) (word 4 0 0)) (by decide +kernel)
  have a3606 := h.atomAt 3606 (.mul (.n 4108) (.n 4106) (.n 4107)) (by decide +kernel)
  have a3607 := h.atomAt 3607 (.add (.n 4109) (.n 2853) (.n 4108)) (by decide +kernel)
  have a3608 := h.atomAt 3608 (.load (.n 4110) (.n 14) 3) (by decide +kernel)
  have a3609 := h.atomAt 3609 (.const (.n 4111) (word 16 0 0)) (by decide +kernel)
  have a3610 := h.atomAt 3610 (.mul (.n 4112) (.n 4110) (.n 4111)) (by decide +kernel)
  have a3611 := h.atomAt 3611 (.add (.n 4113) (.n 4109) (.n 4112)) (by decide +kernel)
  have a3612 := h.atomAt 3612 (.mul (.n 4114) (.n 3396) (.n 4113)) (by decide +kernel)
  have a3613 := h.atomAt 3613 (.add (.n 4115) (.n 4105) (.n 4114)) (by decide +kernel)
  have a3614 := h.atomAt 3614 (.load (.n 4116) (.n 14) 0) (by decide +kernel)
  have a3615 := h.atomAt 3615 (.const (.n 4117) (word 2 0 0)) (by decide +kernel)
  have a3616 := h.atomAt 3616 (.mul (.n 4118) (.n 4116) (.n 4117)) (by decide +kernel)
  have a3617 := h.atomAt 3617 (.add (.n 4119) (.n 2853) (.n 4118)) (by decide +kernel)
  have a3618 := h.atomAt 3618 (.mul (.n 4120) (.n 3415) (.n 4119)) (by decide +kernel)
  have a3619 := h.atomAt 3619 (.add (.n 4121) (.n 4115) (.n 4120)) (by decide +kernel)
  have a3620 := h.atomAt 3620 (.load (.n 4122) (.n 14) 0) (by decide +kernel)
  have a3621 := h.atomAt 3621 (.const (.n 4123) (word 2 0 0)) (by decide +kernel)
  have a3622 := h.atomAt 3622 (.mul (.n 4124) (.n 4122) (.n 4123)) (by decide +kernel)
  have a3623 := h.atomAt 3623 (.add (.n 4125) (.n 2853) (.n 4124)) (by decide +kernel)
  have a3624 := h.atomAt 3624 (.mul (.n 4126) (.n 3434) (.n 4125)) (by decide +kernel)
  have a3625 := h.atomAt 3625 (.add (.n 4127) (.n 4121) (.n 4126)) (by decide +kernel)
  have a3626 := h.atomAt 3626 (.load (.n 4128) (.n 14) 0) (by decide +kernel)
  have a3627 := h.atomAt 3627 (.const (.n 4129) (word 2 0 0)) (by decide +kernel)
  have a3628 := h.atomAt 3628 (.mul (.n 4130) (.n 4128) (.n 4129)) (by decide +kernel)
  have a3629 := h.atomAt 3629 (.add (.n 4131) (.n 2853) (.n 4130)) (by decide +kernel)
  have a3630 := h.atomAt 3630 (.mul (.n 4132) (.n 3453) (.n 4131)) (by decide +kernel)
  have a3631 := h.atomAt 3631 (.add (.n 4133) (.n 4127) (.n 4132)) (by decide +kernel)
  have a3632 := h.atomAt 3632 (.mul (.n 4134) (.n 2702) (.n 4133)) (by decide +kernel)
  have a3633 := h.atomAt 3633 (.add (.n 4135) (.n 4102) (.n 4134)) (by decide +kernel)
  have a3634 := h.atomAt 3634 (.load (.n 4136) (.n 14) 0) (by decide +kernel)
  have a3635 := h.atomAt 3635 (.add (.n 4137) (.n 2853) (.n 4136)) (by decide +kernel)
  have a3636 := h.atomAt 3636 (.mul (.n 4138) (.n 3472) (.n 4137)) (by decide +kernel)
  have a3637 := h.atomAt 3637 (.load (.n 4139) (.n 14) 0) (by decide +kernel)
  have a3638 := h.atomAt 3638 (.const (.n 4140) (word 4 0 0)) (by decide +kernel)
  have a3639 := h.atomAt 3639 (.mul (.n 4141) (.n 4139) (.n 4140)) (by decide +kernel)
  have a3640 := h.atomAt 3640 (.add (.n 4142) (.n 2853) (.n 4141)) (by decide +kernel)
  have a3641 := h.atomAt 3641 (.load (.n 4143) (.n 14) 3) (by decide +kernel)
  have a3642 := h.atomAt 3642 (.const (.n 4144) (word 32 0 0)) (by decide +kernel)
  have a3643 := h.atomAt 3643 (.mul (.n 4145) (.n 4143) (.n 4144)) (by decide +kernel)
  have a3644 := h.atomAt 3644 (.add (.n 4146) (.n 4142) (.n 4145)) (by decide +kernel)
  have a3645 := h.atomAt 3645 (.mul (.n 4147) (.n 3491) (.n 4146)) (by decide +kernel)
  have a3646 := h.atomAt 3646 (.add (.n 4148) (.n 4138) (.n 4147)) (by decide +kernel)
  have a3647 := h.atomAt 3647 (.load (.n 4149) (.n 14) 0) (by decide +kernel)
  have a3648 := h.atomAt 3648 (.const (.n 4150) (word 2 0 0)) (by decide +kernel)
  have a3649 := h.atomAt 3649 (.mul (.n 4151) (.n 4149) (.n 4150)) (by decide +kernel)
  have a3650 := h.atomAt 3650 (.add (.n 4152) (.n 2853) (.n 4151)) (by decide +kernel)
  have a3651 := h.atomAt 3651 (.mul (.n 4153) (.n 3510) (.n 4152)) (by decide +kernel)
  have a3652 := h.atomAt 3652 (.add (.n 4154) (.n 4148) (.n 4153)) (by decide +kernel)
  have a3653 := h.atomAt 3653 (.load (.n 4155) (.n 14) 0) (by decide +kernel)
  have a3654 := h.atomAt 3654 (.const (.n 4156) (word 2 0 0)) (by decide +kernel)
  have a3655 := h.atomAt 3655 (.mul (.n 4157) (.n 4155) (.n 4156)) (by decide +kernel)
  have a3656 := h.atomAt 3656 (.add (.n 4158) (.n 2853) (.n 4157)) (by decide +kernel)
  have a3657 := h.atomAt 3657 (.mul (.n 4159) (.n 3529) (.n 4158)) (by decide +kernel)
  have a3658 := h.atomAt 3658 (.add (.n 4160) (.n 4154) (.n 4159)) (by decide +kernel)
  have a3659 := h.atomAt 3659 (.load (.n 4161) (.n 14) 0) (by decide +kernel)
  have a3660 := h.atomAt 3660 (.const (.n 4162) (word 2 0 0)) (by decide +kernel)
  have a3661 := h.atomAt 3661 (.mul (.n 4163) (.n 4161) (.n 4162)) (by decide +kernel)
  have a3662 := h.atomAt 3662 (.add (.n 4164) (.n 2853) (.n 4163)) (by decide +kernel)
  have a3663 := h.atomAt 3663 (.mul (.n 4165) (.n 3548) (.n 4164)) (by decide +kernel)
  have a3664 := h.atomAt 3664 (.add (.n 4166) (.n 4160) (.n 4165)) (by decide +kernel)
  have a3665 := h.atomAt 3665 (.load (.n 4167) (.n 14) 0) (by decide +kernel)
  have a3666 := h.atomAt 3666 (.const (.n 4168) (word 2 0 0)) (by decide +kernel)
  have a3667 := h.atomAt 3667 (.mul (.n 4169) (.n 4167) (.n 4168)) (by decide +kernel)
  have a3668 := h.atomAt 3668 (.add (.n 4170) (.n 2853) (.n 4169)) (by decide +kernel)
  have a3669 := h.atomAt 3669 (.mul (.n 4171) (.n 3567) (.n 4170)) (by decide +kernel)
  have a3670 := h.atomAt 3670 (.add (.n 4172) (.n 4166) (.n 4171)) (by decide +kernel)
  have a3671 := h.atomAt 3671 (.load (.n 4173) (.n 14) 0) (by decide +kernel)
  have a3672 := h.atomAt 3672 (.const (.n 4174) (word 2 0 0)) (by decide +kernel)
  have a3673 := h.atomAt 3673 (.mul (.n 4175) (.n 4173) (.n 4174)) (by decide +kernel)
  have a3674 := h.atomAt 3674 (.add (.n 4176) (.n 2853) (.n 4175)) (by decide +kernel)
  have a3675 := h.atomAt 3675 (.mul (.n 4177) (.n 3586) (.n 4176)) (by decide +kernel)
  have a3676 := h.atomAt 3676 (.add (.n 4178) (.n 4172) (.n 4177)) (by decide +kernel)
  have a3677 := h.atomAt 3677 (.load (.n 4179) (.n 14) 0) (by decide +kernel)
  have a3678 := h.atomAt 3678 (.const (.n 4180) (word 2 0 0)) (by decide +kernel)
  have a3679 := h.atomAt 3679 (.mul (.n 4181) (.n 4179) (.n 4180)) (by decide +kernel)
  have a3680 := h.atomAt 3680 (.add (.n 4182) (.n 2853) (.n 4181)) (by decide +kernel)
  have a3681 := h.atomAt 3681 (.mul (.n 4183) (.n 3605) (.n 4182)) (by decide +kernel)
  have a3682 := h.atomAt 3682 (.add (.n 4184) (.n 4178) (.n 4183)) (by decide +kernel)
  have a3683 := h.atomAt 3683 (.load (.n 4185) (.n 14) 0) (by decide +kernel)
  have a3684 := h.atomAt 3684 (.const (.n 4186) (word 2 0 0)) (by decide +kernel)
  have a3685 := h.atomAt 3685 (.mul (.n 4187) (.n 4185) (.n 4186)) (by decide +kernel)
  have a3686 := h.atomAt 3686 (.add (.n 4188) (.n 2853) (.n 4187)) (by decide +kernel)
  have a3687 := h.atomAt 3687 (.mul (.n 4189) (.n 3624) (.n 4188)) (by decide +kernel)
  have a3688 := h.atomAt 3688 (.add (.n 4190) (.n 4184) (.n 4189)) (by decide +kernel)
  have a3689 := h.atomAt 3689 (.load (.n 4191) (.n 14) 0) (by decide +kernel)
  have a3690 := h.atomAt 3690 (.const (.n 4192) (word 2 0 0)) (by decide +kernel)
  have a3691 := h.atomAt 3691 (.mul (.n 4193) (.n 4191) (.n 4192)) (by decide +kernel)
  have a3692 := h.atomAt 3692 (.add (.n 4194) (.n 2853) (.n 4193)) (by decide +kernel)
  have a3693 := h.atomAt 3693 (.mul (.n 4195) (.n 3643) (.n 4194)) (by decide +kernel)
  have a3694 := h.atomAt 3694 (.add (.n 4196) (.n 4190) (.n 4195)) (by decide +kernel)
  have a3695 := h.atomAt 3695 (.load (.n 4197) (.n 14) 0) (by decide +kernel)
  have a3696 := h.atomAt 3696 (.const (.n 4198) (word 2 0 0)) (by decide +kernel)
  have a3697 := h.atomAt 3697 (.mul (.n 4199) (.n 4197) (.n 4198)) (by decide +kernel)
  have a3698 := h.atomAt 3698 (.add (.n 4200) (.n 2853) (.n 4199)) (by decide +kernel)
  have a3699 := h.atomAt 3699 (.mul (.n 4201) (.n 3662) (.n 4200)) (by decide +kernel)
  have a3700 := h.atomAt 3700 (.add (.n 4202) (.n 4196) (.n 4201)) (by decide +kernel)
  have a3701 := h.atomAt 3701 (.load (.n 4203) (.n 14) 0) (by decide +kernel)
  have a3702 := h.atomAt 3702 (.const (.n 4204) (word 2 0 0)) (by decide +kernel)
  have a3703 := h.atomAt 3703 (.mul (.n 4205) (.n 4203) (.n 4204)) (by decide +kernel)
  have a3704 := h.atomAt 3704 (.add (.n 4206) (.n 2853) (.n 4205)) (by decide +kernel)
  have a3705 := h.atomAt 3705 (.mul (.n 4207) (.n 3681) (.n 4206)) (by decide +kernel)
  have a3706 := h.atomAt 3706 (.add (.n 4208) (.n 4202) (.n 4207)) (by decide +kernel)
  have a3707 := h.atomAt 3707 (.load (.n 4209) (.n 14) 0) (by decide +kernel)
  have a3708 := h.atomAt 3708 (.const (.n 4210) (word 2 0 0)) (by decide +kernel)
  have a3709 := h.atomAt 3709 (.mul (.n 4211) (.n 4209) (.n 4210)) (by decide +kernel)
  have a3710 := h.atomAt 3710 (.add (.n 4212) (.n 2853) (.n 4211)) (by decide +kernel)
  have a3711 := h.atomAt 3711 (.mul (.n 4213) (.n 3700) (.n 4212)) (by decide +kernel)
  have a3712 := h.atomAt 3712 (.add (.n 4214) (.n 4208) (.n 4213)) (by decide +kernel)
  have a3713 := h.atomAt 3713 (.load (.n 4215) (.n 14) 0) (by decide +kernel)
  have a3714 := h.atomAt 3714 (.const (.n 4216) (word 2 0 0)) (by decide +kernel)
  have a3715 := h.atomAt 3715 (.mul (.n 4217) (.n 4215) (.n 4216)) (by decide +kernel)
  have a3716 := h.atomAt 3716 (.add (.n 4218) (.n 2853) (.n 4217)) (by decide +kernel)
  have a3717 := h.atomAt 3717 (.mul (.n 4219) (.n 3719) (.n 4218)) (by decide +kernel)
  have a3718 := h.atomAt 3718 (.add (.n 4220) (.n 4214) (.n 4219)) (by decide +kernel)
  have a3719 := h.atomAt 3719 (.load (.n 4221) (.n 14) 0) (by decide +kernel)
  have a3720 := h.atomAt 3720 (.const (.n 4222) (word 2 0 0)) (by decide +kernel)
  have a3721 := h.atomAt 3721 (.mul (.n 4223) (.n 4221) (.n 4222)) (by decide +kernel)
  have a3722 := h.atomAt 3722 (.add (.n 4224) (.n 2853) (.n 4223)) (by decide +kernel)
  have a3723 := h.atomAt 3723 (.mul (.n 4225) (.n 3738) (.n 4224)) (by decide +kernel)
  have a3724 := h.atomAt 3724 (.add (.n 4226) (.n 4220) (.n 4225)) (by decide +kernel)
  have a3725 := h.atomAt 3725 (.load (.n 4227) (.n 14) 0) (by decide +kernel)
  have a3726 := h.atomAt 3726 (.const (.n 4228) (word 2 0 0)) (by decide +kernel)
  have a3727 := h.atomAt 3727 (.mul (.n 4229) (.n 4227) (.n 4228)) (by decide +kernel)
  have a3728 := h.atomAt 3728 (.add (.n 4230) (.n 2853) (.n 4229)) (by decide +kernel)
  have a3729 := h.atomAt 3729 (.load (.n 4231) (.n 14) 3) (by decide +kernel)
  have a3730 := h.atomAt 3730 (.const (.n 4232) (word 17376452488221285863 0 0)) (by decide +kernel)
  have a3731 := h.atomAt 3731 (.mul (.n 4233) (.n 4231) (.n 4232)) (by decide +kernel)
  have a3732 := h.atomAt 3732 (.add (.n 4234) (.n 4230) (.n 4233)) (by decide +kernel)
  have a3733 := h.atomAt 3733 (.load (.n 4235) (.n 14) 4) (by decide +kernel)
  have a3734 := h.atomAt 3734 (.const (.n 4236) (word 9571781953733019530 0 0)) (by decide +kernel)
  have a3735 := h.atomAt 3735 (.mul (.n 4237) (.n 4235) (.n 4236)) (by decide +kernel)
  have a3736 := h.atomAt 3736 (.add (.n 4238) (.n 4234) (.n 4237)) (by decide +kernel)
  have a3737 := h.atomAt 3737 (.mul (.n 4239) (.n 3757) (.n 4238)) (by decide +kernel)
  have a3738 := h.atomAt 3738 (.add (.n 4240) (.n 4226) (.n 4239)) (by decide +kernel)
  have a3739 := h.atomAt 3739 (.load (.n 4241) (.n 14) 0) (by decide +kernel)
  have a3740 := h.atomAt 3740 (.const (.n 4242) (word 2 0 0)) (by decide +kernel)
  have a3741 := h.atomAt 3741 (.mul (.n 4243) (.n 4241) (.n 4242)) (by decide +kernel)
  have a3742 := h.atomAt 3742 (.add (.n 4244) (.n 2853) (.n 4243)) (by decide +kernel)
  have a3743 := h.atomAt 3743 (.load (.n 4245) (.n 14) 3) (by decide +kernel)
  have a3744 := h.atomAt 3744 (.const (.n 4246) (word 15391093639620504046 0 0)) (by decide +kernel)
  have a3745 := h.atomAt 3745 (.mul (.n 4247) (.n 4245) (.n 4246)) (by decide +kernel)
  have a3746 := h.atomAt 3746 (.add (.n 4248) (.n 4244) (.n 4247)) (by decide +kernel)
  have a3747 := h.atomAt 3747 (.load (.n 4249) (.n 14) 4) (by decide +kernel)
  have a3748 := h.atomAt 3748 (.const (.n 4250) (word 13624874521033984333 0 0)) (by decide +kernel)
  have a3749 := h.atomAt 3749 (.mul (.n 4251) (.n 4249) (.n 4250)) (by decide +kernel)
  have a3750 := h.atomAt 3750 (.add (.n 4252) (.n 4248) (.n 4251)) (by decide +kernel)
  have a3751 := h.atomAt 3751 (.mul (.n 4253) (.n 3776) (.n 4252)) (by decide +kernel)
  have a3752 := h.atomAt 3752 (.add (.n 4254) (.n 4240) (.n 4253)) (by decide +kernel)
  have a3753 := h.atomAt 3753 (.load (.n 4255) (.n 14) 0) (by decide +kernel)
  have a3754 := h.atomAt 3754 (.const (.n 4256) (word 2 0 0)) (by decide +kernel)
  have a3755 := h.atomAt 3755 (.mul (.n 4257) (.n 4255) (.n 4256)) (by decide +kernel)
  have a3756 := h.atomAt 3756 (.add (.n 4258) (.n 2853) (.n 4257)) (by decide +kernel)
  have a3757 := h.atomAt 3757 (.load (.n 4259) (.n 14) 3) (by decide +kernel)
  have a3758 := h.atomAt 3758 (.const (.n 4260) (word 10027350355371872343 0 0)) (by decide +kernel)
  have a3759 := h.atomAt 3759 (.mul (.n 4261) (.n 4259) (.n 4260)) (by decide +kernel)
  have a3760 := h.atomAt 3760 (.add (.n 4262) (.n 4258) (.n 4261)) (by decide +kernel)
  have a3761 := h.atomAt 3761 (.load (.n 4263) (.n 14) 4) (by decide +kernel)
  have a3762 := h.atomAt 3762 (.const (.n 4264) (word 18417369716475457492 0 0)) (by decide +kernel)
  have a3763 := h.atomAt 3763 (.mul (.n 4265) (.n 4263) (.n 4264)) (by decide +kernel)
  have a3764 := h.atomAt 3764 (.add (.n 4266) (.n 4262) (.n 4265)) (by decide +kernel)
  have a3765 := h.atomAt 3765 (.mul (.n 4267) (.n 3795) (.n 4266)) (by decide +kernel)
  have a3766 := h.atomAt 3766 (.add (.n 4268) (.n 4254) (.n 4267)) (by decide +kernel)
  have a3767 := h.atomAt 3767 (.load (.n 4269) (.n 14) 0) (by decide +kernel)
  have a3768 := h.atomAt 3768 (.const (.n 4270) (word 2 0 0)) (by decide +kernel)
  have a3769 := h.atomAt 3769 (.mul (.n 4271) (.n 4269) (.n 4270)) (by decide +kernel)
  have a3770 := h.atomAt 3770 (.add (.n 4272) (.n 2853) (.n 4271)) (by decide +kernel)
  have a3771 := h.atomAt 3771 (.load (.n 4273) (.n 14) 3) (by decide +kernel)
  have a3772 := h.atomAt 3772 (.const (.n 4274) (word 10448040663659726788 0 0)) (by decide +kernel)
  have a3773 := h.atomAt 3773 (.mul (.n 4275) (.n 4273) (.n 4274)) (by decide +kernel)
  have a3774 := h.atomAt 3774 (.add (.n 4276) (.n 4272) (.n 4275)) (by decide +kernel)
  have a3775 := h.atomAt 3775 (.load (.n 4277) (.n 14) 4) (by decide +kernel)
  have a3776 := h.atomAt 3776 (.const (.n 4278) (word 10113917136857017974 0 0)) (by decide +kernel)
  have a3777 := h.atomAt 3777 (.mul (.n 4279) (.n 4277) (.n 4278)) (by decide +kernel)
  have a3778 := h.atomAt 3778 (.add (.n 4280) (.n 4276) (.n 4279)) (by decide +kernel)
  have a3779 := h.atomAt 3779 (.mul (.n 4281) (.n 3814) (.n 4280)) (by decide +kernel)
  have a3780 := h.atomAt 3780 (.add (.n 4282) (.n 4268) (.n 4281)) (by decide +kernel)
  have a3781 := h.atomAt 3781 (.load (.n 4283) (.n 14) 0) (by decide +kernel)
  have a3782 := h.atomAt 3782 (.const (.n 4284) (word 2 0 0)) (by decide +kernel)
  have a3783 := h.atomAt 3783 (.mul (.n 4285) (.n 4283) (.n 4284)) (by decide +kernel)
  have a3784 := h.atomAt 3784 (.add (.n 4286) (.n 2853) (.n 4285)) (by decide +kernel)
  have a3785 := h.atomAt 3785 (.load (.n 4287) (.n 14) 3) (by decide +kernel)
  have a3786 := h.atomAt 3786 (.const (.n 4288) (word 12479658147685402012 0 0)) (by decide +kernel)
  have a3787 := h.atomAt 3787 (.mul (.n 4289) (.n 4287) (.n 4288)) (by decide +kernel)
  have a3788 := h.atomAt 3788 (.add (.n 4290) (.n 4286) (.n 4289)) (by decide +kernel)
  have a3789 := h.atomAt 3789 (.load (.n 4291) (.n 14) 4) (by decide +kernel)
  have a3790 := h.atomAt 3790 (.const (.n 4292) (word 3500241080921619556 0 0)) (by decide +kernel)
  have a3791 := h.atomAt 3791 (.mul (.n 4293) (.n 4291) (.n 4292)) (by decide +kernel)
  have a3792 := h.atomAt 3792 (.add (.n 4294) (.n 4290) (.n 4293)) (by decide +kernel)
  have a3793 := h.atomAt 3793 (.mul (.n 4295) (.n 3833) (.n 4294)) (by decide +kernel)
  have a3794 := h.atomAt 3794 (.add (.n 4296) (.n 4282) (.n 4295)) (by decide +kernel)
  have a3795 := h.atomAt 3795 (.load (.n 4297) (.n 14) 0) (by decide +kernel)
  have a3796 := h.atomAt 3796 (.const (.n 4298) (word 2 0 0)) (by decide +kernel)
  have a3797 := h.atomAt 3797 (.mul (.n 4299) (.n 4297) (.n 4298)) (by decide +kernel)
  have a3798 := h.atomAt 3798 (.add (.n 4300) (.n 2853) (.n 4299)) (by decide +kernel)
  have a3799 := h.atomAt 3799 (.load (.n 4301) (.n 14) 3) (by decide +kernel)
  have a3800 := h.atomAt 3800 (.const (.n 4302) (word 16959053435453822517 0 0)) (by decide +kernel)
  have a3801 := h.atomAt 3801 (.mul (.n 4303) (.n 4301) (.n 4302)) (by decide +kernel)
  have a3802 := h.atomAt 3802 (.add (.n 4304) (.n 4300) (.n 4303)) (by decide +kernel)
  have a3803 := h.atomAt 3803 (.load (.n 4305) (.n 14) 4) (by decide +kernel)
  have a3804 := h.atomAt 3804 (.const (.n 4306) (word 12224711289652453635 0 0)) (by decide +kernel)
  have a3805 := h.atomAt 3805 (.mul (.n 4307) (.n 4305) (.n 4306)) (by decide +kernel)
  have a3806 := h.atomAt 3806 (.add (.n 4308) (.n 4304) (.n 4307)) (by decide +kernel)
  have a3807 := h.atomAt 3807 (.mul (.n 4309) (.n 3852) (.n 4308)) (by decide +kernel)
  have a3808 := h.atomAt 3808 (.add (.n 4310) (.n 4296) (.n 4309)) (by decide +kernel)
  have a3809 := h.atomAt 3809 (.load (.n 4311) (.n 14) 0) (by decide +kernel)
  have a3810 := h.atomAt 3810 (.const (.n 4312) (word 2 0 0)) (by decide +kernel)
  have a3811 := h.atomAt 3811 (.mul (.n 4313) (.n 4311) (.n 4312)) (by decide +kernel)
  have a3812 := h.atomAt 3812 (.add (.n 4314) (.n 2853) (.n 4313)) (by decide +kernel)
  have a3813 := h.atomAt 3813 (.load (.n 4315) (.n 14) 3) (by decide +kernel)
  have a3814 := h.atomAt 3814 (.const (.n 4316) (word 9342009439668884831 0 0)) (by decide +kernel)
  have a3815 := h.atomAt 3815 (.mul (.n 4317) (.n 4315) (.n 4316)) (by decide +kernel)
  have a3816 := h.atomAt 3816 (.add (.n 4318) (.n 4314) (.n 4317)) (by decide +kernel)
  have a3817 := h.atomAt 3817 (.load (.n 4319) (.n 14) 4) (by decide +kernel)
  have a3818 := h.atomAt 3818 (.const (.n 4320) (word 4879704952849025062 0 0)) (by decide +kernel)
  have a3819 := h.atomAt 3819 (.mul (.n 4321) (.n 4319) (.n 4320)) (by decide +kernel)
  have a3820 := h.atomAt 3820 (.add (.n 4322) (.n 4318) (.n 4321)) (by decide +kernel)
  have a3821 := h.atomAt 3821 (.mul (.n 4323) (.n 3871) (.n 4322)) (by decide +kernel)
  have a3822 := h.atomAt 3822 (.add (.n 4324) (.n 4310) (.n 4323)) (by decide +kernel)
  have a3823 := h.atomAt 3823 (.load (.n 4325) (.n 14) 0) (by decide +kernel)
  have a3824 := h.atomAt 3824 (.const (.n 4326) (word 2 0 0)) (by decide +kernel)
  have a3825 := h.atomAt 3825 (.mul (.n 4327) (.n 4325) (.n 4326)) (by decide +kernel)
  have a3826 := h.atomAt 3826 (.add (.n 4328) (.n 2853) (.n 4327)) (by decide +kernel)
  have a3827 := h.atomAt 3827 (.load (.n 4329) (.n 14) 3) (by decide +kernel)
  have a3828 := h.atomAt 3828 (.const (.n 4330) (word 140226327413610143 0 0)) (by decide +kernel)
  have a3829 := h.atomAt 3829 (.mul (.n 4331) (.n 4329) (.n 4330)) (by decide +kernel)
  have a3830 := h.atomAt 3830 (.add (.n 4332) (.n 4328) (.n 4331)) (by decide +kernel)
  have a3831 := h.atomAt 3831 (.load (.n 4333) (.n 14) 4) (by decide +kernel)
  have a3832 := h.atomAt 3832 (.const (.n 4334) (word 424854978622500449 0 0)) (by decide +kernel)
  have a3833 := h.atomAt 3833 (.mul (.n 4335) (.n 4333) (.n 4334)) (by decide +kernel)
  have a3834 := h.atomAt 3834 (.add (.n 4336) (.n 4332) (.n 4335)) (by decide +kernel)
  have a3835 := h.atomAt 3835 (.mul (.n 4337) (.n 3890) (.n 4336)) (by decide +kernel)
  have a3836 := h.atomAt 3836 (.add (.n 4338) (.n 4324) (.n 4337)) (by decide +kernel)
  have a3837 := h.atomAt 3837 (.load (.n 4339) (.n 14) 0) (by decide +kernel)
  have a3838 := h.atomAt 3838 (.const (.n 4340) (word 2 0 0)) (by decide +kernel)
  have a3839 := h.atomAt 3839 (.mul (.n 4341) (.n 4339) (.n 4340)) (by decide +kernel)
  have a3840 := h.atomAt 3840 (.add (.n 4342) (.n 2853) (.n 4341)) (by decide +kernel)
  have a3841 := h.atomAt 3841 (.load (.n 4343) (.n 14) 3) (by decide +kernel)
  have a3842 := h.atomAt 3842 (.const (.n 4344) (word 7259519967065370866 0 0)) (by decide +kernel)
  have a3843 := h.atomAt 3843 (.mul (.n 4345) (.n 4343) (.n 4344)) (by decide +kernel)
  have a3844 := h.atomAt 3844 (.add (.n 4346) (.n 4342) (.n 4345)) (by decide +kernel)
  have a3845 := h.atomAt 3845 (.mul (.n 4347) (.n 3909) (.n 4346)) (by decide +kernel)
  have a3846 := h.atomAt 3846 (.add (.n 4348) (.n 4338) (.n 4347)) (by decide +kernel)
  have a3847 := h.atomAt 3847 (.load (.n 4349) (.n 14) 0) (by decide +kernel)
  have a3848 := h.atomAt 3848 (.const (.n 4350) (word 2 0 0)) (by decide +kernel)
  have a3849 := h.atomAt 3849 (.mul (.n 4351) (.n 4349) (.n 4350)) (by decide +kernel)
  have a3850 := h.atomAt 3850 (.add (.n 4352) (.n 2853) (.n 4351)) (by decide +kernel)
  have a3851 := h.atomAt 3851 (.load (.n 4353) (.n 14) 3) (by decide +kernel)
  have a3852 := h.atomAt 3852 (.const (.n 4354) (word 7004910057750291985 0 0)) (by decide +kernel)
  have a3853 := h.atomAt 3853 (.mul (.n 4355) (.n 4353) (.n 4354)) (by decide +kernel)
  have a3854 := h.atomAt 3854 (.add (.n 4356) (.n 4352) (.n 4355)) (by decide +kernel)
  have a3855 := h.atomAt 3855 (.load (.n 4357) (.n 14) 4) (by decide +kernel)
  have a3856 := h.atomAt 3856 (.const (.n 4358) (word 13293599522548616907 0 0)) (by decide +kernel)
  have a3857 := h.atomAt 3857 (.mul (.n 4359) (.n 4357) (.n 4358)) (by decide +kernel)
  have a3858 := h.atomAt 3858 (.add (.n 4360) (.n 4356) (.n 4359)) (by decide +kernel)
  have a3859 := h.atomAt 3859 (.mul (.n 4361) (.n 3928) (.n 4360)) (by decide +kernel)
  have a3860 := h.atomAt 3860 (.add (.n 4362) (.n 4348) (.n 4361)) (by decide +kernel)
  have a3861 := h.atomAt 3861 (.load (.n 4363) (.n 14) 0) (by decide +kernel)
  have a3862 := h.atomAt 3862 (.const (.n 4364) (word 2 0 0)) (by decide +kernel)
  have a3863 := h.atomAt 3863 (.mul (.n 4365) (.n 4363) (.n 4364)) (by decide +kernel)
  have a3864 := h.atomAt 3864 (.add (.n 4366) (.n 2853) (.n 4365)) (by decide +kernel)
  have a3865 := h.atomAt 3865 (.load (.n 4367) (.n 14) 3) (by decide +kernel)
  have a3866 := h.atomAt 3866 (.const (.n 4368) (word 10105770293752443592 0 0)) (by decide +kernel)
  have a3867 := h.atomAt 3867 (.mul (.n 4369) (.n 4367) (.n 4368)) (by decide +kernel)
  have a3868 := h.atomAt 3868 (.add (.n 4370) (.n 4366) (.n 4369)) (by decide +kernel)
  have a3869 := h.atomAt 3869 (.load (.n 4371) (.n 14) 4) (by decide +kernel)
  have a3870 := h.atomAt 3870 (.const (.n 4372) (word 10668034807192757780 0 0)) (by decide +kernel)
  have a3871 := h.atomAt 3871 (.mul (.n 4373) (.n 4371) (.n 4372)) (by decide +kernel)
  have a3872 := h.atomAt 3872 (.add (.n 4374) (.n 4370) (.n 4373)) (by decide +kernel)
  have a3873 := h.atomAt 3873 (.mul (.n 4375) (.n 3947) (.n 4374)) (by decide +kernel)
  have a3874 := h.atomAt 3874 (.add (.n 4376) (.n 4362) (.n 4375)) (by decide +kernel)
  have a3875 := h.atomAt 3875 (.load (.n 4377) (.n 14) 0) (by decide +kernel)
  have a3876 := h.atomAt 3876 (.const (.n 4378) (word 2 0 0)) (by decide +kernel)
  have a3877 := h.atomAt 3877 (.mul (.n 4379) (.n 4377) (.n 4378)) (by decide +kernel)
  have a3878 := h.atomAt 3878 (.add (.n 4380) (.n 2853) (.n 4379)) (by decide +kernel)
  have a3879 := h.atomAt 3879 (.load (.n 4381) (.n 14) 3) (by decide +kernel)
  have a3880 := h.atomAt 3880 (.const (.n 4382) (word 1747952066141424100 0 0)) (by decide +kernel)
  have a3881 := h.atomAt 3881 (.mul (.n 4383) (.n 4381) (.n 4382)) (by decide +kernel)
  have a3882 := h.atomAt 3882 (.add (.n 4384) (.n 4380) (.n 4383)) (by decide +kernel)
  have a3883 := h.atomAt 3883 (.load (.n 4385) (.n 14) 4) (by decide +kernel)
  have a3884 := h.atomAt 3884 (.const (.n 4386) (word 1654286879329379778 0 0)) (by decide +kernel)
  have a3885 := h.atomAt 3885 (.mul (.n 4387) (.n 4385) (.n 4386)) (by decide +kernel)
  have a3886 := h.atomAt 3886 (.add (.n 4388) (.n 4384) (.n 4387)) (by decide +kernel)
  have a3887 := h.atomAt 3887 (.mul (.n 4389) (.n 3966) (.n 4388)) (by decide +kernel)
  have a3888 := h.atomAt 3888 (.add (.n 4390) (.n 4376) (.n 4389)) (by decide +kernel)
  have a3889 := h.atomAt 3889 (.load (.n 4391) (.n 14) 0) (by decide +kernel)
  have a3890 := h.atomAt 3890 (.const (.n 4392) (word 2 0 0)) (by decide +kernel)
  have a3891 := h.atomAt 3891 (.mul (.n 4393) (.n 4391) (.n 4392)) (by decide +kernel)
  have a3892 := h.atomAt 3892 (.add (.n 4394) (.n 2853) (.n 4393)) (by decide +kernel)
  have a3893 := h.atomAt 3893 (.load (.n 4395) (.n 14) 3) (by decide +kernel)
  have a3894 := h.atomAt 3894 (.const (.n 4396) (word 8500057116360352059 0 0)) (by decide +kernel)
  have a3895 := h.atomAt 3895 (.mul (.n 4397) (.n 4395) (.n 4396)) (by decide +kernel)
  have a3896 := h.atomAt 3896 (.add (.n 4398) (.n 4394) (.n 4397)) (by decide +kernel)
  have a3897 := h.atomAt 3897 (.load (.n 4399) (.n 14) 4) (by decide +kernel)
  have a3898 := h.atomAt 3898 (.const (.n 4400) (word 16929593379567477321 0 0)) (by decide +kernel)
  have a3899 := h.atomAt 3899 (.mul (.n 4401) (.n 4399) (.n 4400)) (by decide +kernel)
  have a3900 := h.atomAt 3900 (.add (.n 4402) (.n 4398) (.n 4401)) (by decide +kernel)
  have a3901 := h.atomAt 3901 (.mul (.n 4403) (.n 3985) (.n 4402)) (by decide +kernel)
  have a3902 := h.atomAt 3902 (.add (.n 4404) (.n 4390) (.n 4403)) (by decide +kernel)
  have a3903 := h.atomAt 3903 (.mul (.n 4405) (.n 2716) (.n 4404)) (by decide +kernel)
  have a3904 := h.atomAt 3904 (.add (.n 4406) (.n 4135) (.n 4405)) (by decide +kernel)
  have a3905 := h.atomAt 3905 (.add (.n 4407) (.n 3036) (.n 4406)) (by decide +kernel)
  have a3906 := h.atomAt 3906 (.const (.n 4408) (word 1 0 0)) (by decide +kernel)
  have a3907 := h.atomAt 3907 (.add (.n 4409) (.n 4408) (.n 3984)) (by decide +kernel)
  have a3908 := h.atomAt 3908 (.add (.n 4410) (.n 4407) (.n 4409)) (by decide +kernel)
  have a3909 := h.atomAt 3909 (.add (.n 4411) (.n 4410) (.n 27)) (by decide +kernel)
  have e3484 := tb_loadHolds_unique a3484 (hw 0 (by norm_num))
  have e3487 := tb_loadHolds_unique a3487 (hw 0 (by norm_num))
  have e3491 := tb_loadHolds_unique a3491 (hw 3 (by norm_num))
  have e3495 := tb_loadHolds_unique a3495 (hw 0 (by norm_num))
  have e3501 := tb_loadHolds_unique a3501 (hw 0 (by norm_num))
  have e3507 := tb_loadHolds_unique a3507 (hw 0 (by norm_num))
  have e3514 := tb_loadHolds_unique a3514 (hw 0 (by norm_num))
  have e3517 := tb_loadHolds_unique a3517 (hw 0 (by norm_num))
  have e3521 := tb_loadHolds_unique a3521 (hw 3 (by norm_num))
  have e3527 := tb_loadHolds_unique a3527 (hw 0 (by norm_num))
  have e3533 := tb_loadHolds_unique a3533 (hw 0 (by norm_num))
  have e3539 := tb_loadHolds_unique a3539 (hw 0 (by norm_num))
  have e3547 := tb_loadHolds_unique a3547 (hw 0 (by norm_num))
  have e3550 := tb_loadHolds_unique a3550 (hw 0 (by norm_num))
  have e3554 := tb_loadHolds_unique a3554 (hw 3 (by norm_num))
  have e3560 := tb_loadHolds_unique a3560 (hw 0 (by norm_num))
  have e3568 := tb_loadHolds_unique a3568 (hw 0 (by norm_num))
  have e3571 := tb_loadHolds_unique a3571 (hw 0 (by norm_num))
  have e3575 := tb_loadHolds_unique a3575 (hw 3 (by norm_num))
  have e3581 := tb_loadHolds_unique a3581 (hw 0 (by norm_num))
  have e3587 := tb_loadHolds_unique a3587 (hw 0 (by norm_num))
  have e3593 := tb_loadHolds_unique a3593 (hw 0 (by norm_num))
  have e3601 := tb_loadHolds_unique a3601 (hw 0 (by norm_num))
  have e3604 := tb_loadHolds_unique a3604 (hw 0 (by norm_num))
  have e3608 := tb_loadHolds_unique a3608 (hw 3 (by norm_num))
  have e3614 := tb_loadHolds_unique a3614 (hw 0 (by norm_num))
  have e3620 := tb_loadHolds_unique a3620 (hw 0 (by norm_num))
  have e3626 := tb_loadHolds_unique a3626 (hw 0 (by norm_num))
  have e3634 := tb_loadHolds_unique a3634 (hw 0 (by norm_num))
  have e3637 := tb_loadHolds_unique a3637 (hw 0 (by norm_num))
  have e3641 := tb_loadHolds_unique a3641 (hw 3 (by norm_num))
  have e3647 := tb_loadHolds_unique a3647 (hw 0 (by norm_num))
  have e3653 := tb_loadHolds_unique a3653 (hw 0 (by norm_num))
  have e3659 := tb_loadHolds_unique a3659 (hw 0 (by norm_num))
  have e3665 := tb_loadHolds_unique a3665 (hw 0 (by norm_num))
  have e3671 := tb_loadHolds_unique a3671 (hw 0 (by norm_num))
  have e3677 := tb_loadHolds_unique a3677 (hw 0 (by norm_num))
  have e3683 := tb_loadHolds_unique a3683 (hw 0 (by norm_num))
  have e3689 := tb_loadHolds_unique a3689 (hw 0 (by norm_num))
  have e3695 := tb_loadHolds_unique a3695 (hw 0 (by norm_num))
  have e3701 := tb_loadHolds_unique a3701 (hw 0 (by norm_num))
  have e3707 := tb_loadHolds_unique a3707 (hw 0 (by norm_num))
  have e3713 := tb_loadHolds_unique a3713 (hw 0 (by norm_num))
  have e3719 := tb_loadHolds_unique a3719 (hw 0 (by norm_num))
  have e3725 := tb_loadHolds_unique a3725 (hw 0 (by norm_num))
  have e3729 := tb_loadHolds_unique a3729 (hw 3 (by norm_num))
  have e3733 := tb_loadHolds_unique a3733 (hw 4 (by norm_num))
  have e3739 := tb_loadHolds_unique a3739 (hw 0 (by norm_num))
  have e3743 := tb_loadHolds_unique a3743 (hw 3 (by norm_num))
  have e3747 := tb_loadHolds_unique a3747 (hw 4 (by norm_num))
  have e3753 := tb_loadHolds_unique a3753 (hw 0 (by norm_num))
  have e3757 := tb_loadHolds_unique a3757 (hw 3 (by norm_num))
  have e3761 := tb_loadHolds_unique a3761 (hw 4 (by norm_num))
  have e3767 := tb_loadHolds_unique a3767 (hw 0 (by norm_num))
  have e3771 := tb_loadHolds_unique a3771 (hw 3 (by norm_num))
  have e3775 := tb_loadHolds_unique a3775 (hw 4 (by norm_num))
  have e3781 := tb_loadHolds_unique a3781 (hw 0 (by norm_num))
  have e3785 := tb_loadHolds_unique a3785 (hw 3 (by norm_num))
  have e3789 := tb_loadHolds_unique a3789 (hw 4 (by norm_num))
  have e3795 := tb_loadHolds_unique a3795 (hw 0 (by norm_num))
  have e3799 := tb_loadHolds_unique a3799 (hw 3 (by norm_num))
  have e3803 := tb_loadHolds_unique a3803 (hw 4 (by norm_num))
  have e3809 := tb_loadHolds_unique a3809 (hw 0 (by norm_num))
  have e3813 := tb_loadHolds_unique a3813 (hw 3 (by norm_num))
  have e3817 := tb_loadHolds_unique a3817 (hw 4 (by norm_num))
  have e3823 := tb_loadHolds_unique a3823 (hw 0 (by norm_num))
  have e3827 := tb_loadHolds_unique a3827 (hw 3 (by norm_num))
  have e3831 := tb_loadHolds_unique a3831 (hw 4 (by norm_num))
  have e3837 := tb_loadHolds_unique a3837 (hw 0 (by norm_num))
  have e3841 := tb_loadHolds_unique a3841 (hw 3 (by norm_num))
  have e3847 := tb_loadHolds_unique a3847 (hw 0 (by norm_num))
  have e3851 := tb_loadHolds_unique a3851 (hw 3 (by norm_num))
  have e3855 := tb_loadHolds_unique a3855 (hw 4 (by norm_num))
  have e3861 := tb_loadHolds_unique a3861 (hw 0 (by norm_num))
  have e3865 := tb_loadHolds_unique a3865 (hw 3 (by norm_num))
  have e3869 := tb_loadHolds_unique a3869 (hw 4 (by norm_num))
  have e3875 := tb_loadHolds_unique a3875 (hw 0 (by norm_num))
  have e3879 := tb_loadHolds_unique a3879 (hw 3 (by norm_num))
  have e3883 := tb_loadHolds_unique a3883 (hw 4 (by norm_num))
  have e3889 := tb_loadHolds_unique a3889 (hw 0 (by norm_num))
  have e3893 := tb_loadHolds_unique a3893 (hw 3 (by norm_num))
  have e3897 := tb_loadHolds_unique a3897 (hw 4 (by norm_num))
  simp only [Atom.Holds] at a3485 a3486 a3488 a3489 a3490 a3492 a3493 a3494 a3496 a3497
  simp only [Atom.Holds] at a3498 a3499 a3500 a3502 a3503 a3504 a3505 a3506 a3508 a3509
  simp only [Atom.Holds] at a3510 a3511 a3512 a3513 a3515 a3516 a3518 a3519 a3520 a3522
  simp only [Atom.Holds] at a3523 a3524 a3525 a3526 a3528 a3529 a3530 a3531 a3532 a3534
  simp only [Atom.Holds] at a3535 a3536 a3537 a3538 a3540 a3541 a3542 a3543 a3544 a3545
  simp only [Atom.Holds] at a3546 a3548 a3549 a3551 a3552 a3553 a3555 a3556 a3557 a3558
  simp only [Atom.Holds] at a3559 a3561 a3562 a3563 a3564 a3565 a3566 a3567 a3569 a3570
  simp only [Atom.Holds] at a3572 a3573 a3574 a3576 a3577 a3578 a3579 a3580 a3582 a3583
  simp only [Atom.Holds] at a3584 a3585 a3586 a3588 a3589 a3590 a3591 a3592 a3594 a3595
  simp only [Atom.Holds] at a3596 a3597 a3598 a3599 a3600 a3602 a3603 a3605 a3606 a3607
  simp only [Atom.Holds] at a3609 a3610 a3611 a3612 a3613 a3615 a3616 a3617 a3618 a3619
  simp only [Atom.Holds] at a3621 a3622 a3623 a3624 a3625 a3627 a3628 a3629 a3630 a3631
  simp only [Atom.Holds] at a3632 a3633 a3635 a3636 a3638 a3639 a3640 a3642 a3643 a3644
  simp only [Atom.Holds] at a3645 a3646 a3648 a3649 a3650 a3651 a3652 a3654 a3655 a3656
  simp only [Atom.Holds] at a3657 a3658 a3660 a3661 a3662 a3663 a3664 a3666 a3667 a3668
  simp only [Atom.Holds] at a3669 a3670 a3672 a3673 a3674 a3675 a3676 a3678 a3679 a3680
  simp only [Atom.Holds] at a3681 a3682 a3684 a3685 a3686 a3687 a3688 a3690 a3691 a3692
  simp only [Atom.Holds] at a3693 a3694 a3696 a3697 a3698 a3699 a3700 a3702 a3703 a3704
  simp only [Atom.Holds] at a3705 a3706 a3708 a3709 a3710 a3711 a3712 a3714 a3715 a3716
  simp only [Atom.Holds] at a3717 a3718 a3720 a3721 a3722 a3723 a3724 a3726 a3727 a3728
  simp only [Atom.Holds] at a3730 a3731 a3732 a3734 a3735 a3736 a3737 a3738 a3740 a3741
  simp only [Atom.Holds] at a3742 a3744 a3745 a3746 a3748 a3749 a3750 a3751 a3752 a3754
  simp only [Atom.Holds] at a3755 a3756 a3758 a3759 a3760 a3762 a3763 a3764 a3765 a3766
  simp only [Atom.Holds] at a3768 a3769 a3770 a3772 a3773 a3774 a3776 a3777 a3778 a3779
  simp only [Atom.Holds] at a3780 a3782 a3783 a3784 a3786 a3787 a3788 a3790 a3791 a3792
  simp only [Atom.Holds] at a3793 a3794 a3796 a3797 a3798 a3800 a3801 a3802 a3804 a3805
  simp only [Atom.Holds] at a3806 a3807 a3808 a3810 a3811 a3812 a3814 a3815 a3816 a3818
  simp only [Atom.Holds] at a3819 a3820 a3821 a3822 a3824 a3825 a3826 a3828 a3829 a3830
  simp only [Atom.Holds] at a3832 a3833 a3834 a3835 a3836 a3838 a3839 a3840 a3842 a3843
  simp only [Atom.Holds] at a3844 a3845 a3846 a3848 a3849 a3850 a3852 a3853 a3854 a3856
  simp only [Atom.Holds] at a3857 a3858 a3859 a3860 a3862 a3863 a3864 a3866 a3867 a3868
  simp only [Atom.Holds] at a3870 a3871 a3872 a3873 a3874 a3876 a3877 a3878 a3880 a3881
  simp only [Atom.Holds] at a3882 a3884 a3885 a3886 a3887 a3888 a3890 a3891 a3892 a3894
  simp only [Atom.Holds] at a3895 a3896 a3898 a3899 a3900 a3901 a3902 a3903 a3904 a3905
  simp only [Atom.Holds] at a3906 a3907 a3908 a3909
  have t0 : σ (.n 4014) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 2853)) vtPushPadData 0 := by
    simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, tb_word_one, mul_one, add_zero]
    simp only [e3484, a3485, a3486, e3487, a3488, a3489, a3490, e3491, a3492, a3493, a3494, e3495, a3496,
      a3497, a3498, a3499, a3500, e3501, a3502, a3503, a3504, a3505, a3506, e3507, a3508, a3509,
      a3510, a3511, a3512]
    ring
  have t1 : σ (.n 4046) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 2853)) vtPushPadData 1 := by
    simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, tb_word_one, mul_one, add_zero]
    simp only [e3514, a3515, a3516, e3517, a3518, a3519, a3520, e3521, a3522, a3523, a3524, a3525, a3526,
      e3527, a3528, a3529, a3530, a3531, a3532, e3533, a3534, a3535, a3536, a3537, a3538, e3539,
      a3540, a3541, a3542, a3543, a3544]
    ring
  have t2 : σ (.n 4067) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 2853)) vtPushPadData 2 := by
    simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, tb_word_one, mul_one, add_zero]
    simp only [e3547, a3548, a3549, e3550, a3551, a3552, a3553, e3554, a3555, a3556, a3557, a3558, a3559,
      e3560, a3561, a3562, a3563, a3564, a3565]
    ring
  have t3 : σ (.n 4100) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 2853)) vtPushPadData 3 := by
    simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, tb_word_one, mul_one, add_zero]
    simp only [e3568, a3569, a3570, e3571, a3572, a3573, a3574, e3575, a3576, a3577, a3578, a3579, a3580,
      e3581, a3582, a3583, a3584, a3585, a3586, e3587, a3588, a3589, a3590, a3591, a3592, e3593,
      a3594, a3595, a3596, a3597, a3598]
    ring
  have t4 : σ (.n 4133) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 2853)) vtPushPadData 4 := by
    simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, tb_word_one, mul_one, add_zero]
    simp only [e3601, a3602, a3603, e3604, a3605, a3606, a3607, e3608, a3609, a3610, a3611, a3612, a3613,
      e3614, a3615, a3616, a3617, a3618, a3619, e3620, a3621, a3622, a3623, a3624, a3625, e3626,
      a3627, a3628, a3629, a3630, a3631]
    ring
  have t5 : σ (.n 4404) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 2853)) vtPushPadData 5 := by
    simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, tb_word_one, mul_one, add_zero]
    simp only [e3634, a3635, a3636, e3637, a3638, a3639, a3640, e3641, a3642, a3643, a3644, a3645, a3646,
      e3647, a3648, a3649, a3650, a3651, a3652, e3653, a3654, a3655, a3656, a3657, a3658, e3659,
      a3660, a3661, a3662, a3663, a3664, e3665, a3666, a3667, a3668, a3669, a3670, e3671, a3672,
      a3673, a3674, a3675, a3676, e3677, a3678, a3679, a3680, a3681, a3682, e3683, a3684, a3685,
      a3686, a3687, a3688, e3689, a3690, a3691, a3692, a3693, a3694, e3695, a3696, a3697, a3698,
      a3699, a3700, e3701, a3702, a3703, a3704, a3705, a3706, e3707, a3708, a3709, a3710, a3711,
      a3712, e3713, a3714, a3715, a3716, a3717, a3718, e3719, a3720, a3721, a3722, a3723, a3724,
      e3725, a3726, a3727, a3728, e3729, a3730, a3731, a3732, e3733, a3734, a3735, a3736, a3737,
      a3738, e3739, a3740, a3741, a3742, e3743, a3744, a3745, a3746, e3747, a3748, a3749, a3750,
      a3751, a3752, e3753, a3754, a3755, a3756, e3757, a3758, a3759, a3760, e3761, a3762, a3763,
      a3764, a3765, a3766, e3767, a3768, a3769, a3770, e3771, a3772, a3773, a3774, e3775, a3776,
      a3777, a3778, a3779, a3780, e3781, a3782, a3783, a3784, e3785, a3786, a3787, a3788, e3789,
      a3790, a3791, a3792, a3793, a3794, e3795, a3796, a3797, a3798, e3799, a3800, a3801, a3802,
      e3803, a3804, a3805, a3806, a3807, a3808, e3809, a3810, a3811, a3812, e3813, a3814, a3815,
      a3816, e3817, a3818, a3819, a3820, a3821, a3822, e3823, a3824, a3825, a3826, e3827, a3828,
      a3829, a3830, e3831, a3832, a3833, a3834, a3835, a3836, e3837, a3838, a3839, a3840, e3841,
      a3842, a3843, a3844, a3845, a3846, e3847, a3848, a3849, a3850, e3851, a3852, a3853, a3854,
      e3855, a3856, a3857, a3858, a3859, a3860, e3861, a3862, a3863, a3864, e3865, a3866, a3867,
      a3868, e3869, a3870, a3871, a3872, a3873, a3874, e3875, a3876, a3877, a3878, e3879, a3880,
      a3881, a3882, e3883, a3884, a3885, a3886, a3887, a3888, e3889, a3890, a3891, a3892, e3893,
      a3894, a3895, a3896, e3897, a3898, a3899, a3900, a3901, a3902]
    ring
  simp only [vtPadSum, vtPadV]
  simp only [a3513, a3545, a3546, a3566, a3567, a3599, a3600, a3632, a3633, a3903, a3904, a3905, a3906,
    a3907, a3908, a3909]
  rw [← t0, ← t1, ← t2, ← t3, ← t4, ← t5, tb_word_one]

end
end LeanVM.Guest.B1.Tables
