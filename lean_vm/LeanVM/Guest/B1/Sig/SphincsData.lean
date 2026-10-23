/-
  LeanVM.Guest.B1.Sig.SphincsData

  `verify_sig_lean_sphincs` in the guest's core IR is the template `sBody`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sig.SphincsT
public import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Sig.SphincsData0
import LeanVM.Guest.B1.Sig.SphincsCoord0
import LeanVM.Guest.B1.Sig.SphincsCoord1
import LeanVM.Guest.B1.Sig.SphincsCoord2
import LeanVM.Guest.B1.Sig.SphincsCoord3
import LeanVM.Guest.B1.Sig.SphincsCoord4
import LeanVM.Guest.B1.Sig.SphincsCoord5
import LeanVM.Guest.B1.Sig.SphincsCoord6
import LeanVM.Guest.B1.Sig.SphincsCoord7
import LeanVM.Guest.B1.Sig.SphincsArms0_0
import LeanVM.Guest.B1.Sig.SphincsArms0_1
import LeanVM.Guest.B1.Sig.SphincsArms0_2
import LeanVM.Guest.B1.Sig.SphincsArms0_3
import LeanVM.Guest.B1.Sig.SphincsArms1_0
import LeanVM.Guest.B1.Sig.SphincsArms1_1
import LeanVM.Guest.B1.Sig.SphincsArms1_2
import LeanVM.Guest.B1.Sig.SphincsArms1_3
import LeanVM.Guest.B1.Sig.SphincsArms2_0
import LeanVM.Guest.B1.Sig.SphincsArms2_1
import LeanVM.Guest.B1.Sig.SphincsArms2_2
import LeanVM.Guest.B1.Sig.SphincsArms2_3
import LeanVM.Guest.B1.Sig.SphincsArms3_0
import LeanVM.Guest.B1.Sig.SphincsArms3_1
import LeanVM.Guest.B1.Sig.SphincsArms3_2
import LeanVM.Guest.B1.Sig.SphincsArms3_3
import LeanVM.Guest.B1.Sig.SphincsArms4_0
import LeanVM.Guest.B1.Sig.SphincsArms4_1
import LeanVM.Guest.B1.Sig.SphincsArms4_2
import LeanVM.Guest.B1.Sig.SphincsArms4_3
import LeanVM.Guest.B1.Sig.SphincsArms5_0
import LeanVM.Guest.B1.Sig.SphincsArms5_1
import LeanVM.Guest.B1.Sig.SphincsArms5_2
import LeanVM.Guest.B1.Sig.SphincsArms5_3
import LeanVM.Guest.B1.Sig.SphincsArms6_0
import LeanVM.Guest.B1.Sig.SphincsArms6_1
import LeanVM.Guest.B1.Sig.SphincsArms6_2
import LeanVM.Guest.B1.Sig.SphincsArms6_3
import LeanVM.Guest.B1.Sig.SphincsArms7_0
import LeanVM.Guest.B1.Sig.SphincsArms7_1
import LeanVM.Guest.B1.Sig.SphincsArms7_2
import LeanVM.Guest.B1.Sig.SphincsArms7_3
import LeanVM.Guest.B1.Sig.SphincsArms8_0
import LeanVM.Guest.B1.Sig.SphincsArms8_1
import LeanVM.Guest.B1.Sig.SphincsArms8_2
import LeanVM.Guest.B1.Sig.SphincsArms8_3
import LeanVM.Guest.B1.Sig.SphincsArms9_0
import LeanVM.Guest.B1.Sig.SphincsArms9_1
import LeanVM.Guest.B1.Sig.SphincsArms9_2
import LeanVM.Guest.B1.Sig.SphincsArms9_3
import LeanVM.Guest.B1.Sig.SphincsArms10_0
import LeanVM.Guest.B1.Sig.SphincsArms10_1
import LeanVM.Guest.B1.Sig.SphincsArms10_2
import LeanVM.Guest.B1.Sig.SphincsArms10_3
import LeanVM.Guest.B1.Sig.SphincsArms11_0
import LeanVM.Guest.B1.Sig.SphincsArms11_1
import LeanVM.Guest.B1.Sig.SphincsArms11_2
import LeanVM.Guest.B1.Sig.SphincsArms11_3
import LeanVM.Guest.B1.Sig.SphincsArms12_0
import LeanVM.Guest.B1.Sig.SphincsArms12_1
import LeanVM.Guest.B1.Sig.SphincsArms12_2
import LeanVM.Guest.B1.Sig.SphincsArms12_3
import LeanVM.Guest.B1.Sig.SphincsArms13_0
import LeanVM.Guest.B1.Sig.SphincsArms13_1
import LeanVM.Guest.B1.Sig.SphincsArms13_2
import LeanVM.Guest.B1.Sig.SphincsArms13_3
import LeanVM.Guest.B1.Sig.SphincsArms14_0
import LeanVM.Guest.B1.Sig.SphincsArms14_1
import LeanVM.Guest.B1.Sig.SphincsArms14_2
import LeanVM.Guest.B1.Sig.SphincsArms14_3
import LeanVM.Guest.B1.Sig.SphincsArms15_0
import LeanVM.Guest.B1.Sig.SphincsArms15_1
import LeanVM.Guest.B1.Sig.SphincsArms15_2
import LeanVM.Guest.B1.Sig.SphincsArms15_3
import LeanVM.Guest.B1.Sig.SphincsData1
import LeanVM.Guest.B1.Sig.SphincsWots0
import LeanVM.Guest.B1.Sig.SphincsWots1
import LeanVM.Guest.B1.Sig.SphincsWots2
import LeanVM.Guest.B1.Sig.SphincsWots3
import LeanVM.Guest.B1.Sig.SphincsWots4
import LeanVM.Guest.B1.Sig.SphincsWots5
import LeanVM.Guest.B1.Sig.SphincsWots6
import LeanVM.Guest.B1.Sig.SphincsWots7
import LeanVM.Guest.B1.Sig.SphincsWots8
import LeanVM.Guest.B1.Sig.SphincsWots9
import LeanVM.Guest.B1.Sig.SphincsWots10
import LeanVM.Guest.B1.Sig.SphincsWots11
import LeanVM.Guest.B1.Sig.SphincsWots12
import LeanVM.Guest.B1.Sig.SphincsWots13
import LeanVM.Guest.B1.Sig.SphincsWots14
import LeanVM.Guest.B1.Sig.SphincsWots15
import LeanVM.Guest.B1.Sig.SphincsWots16
import LeanVM.Guest.B1.Sig.SphincsWots17
import LeanVM.Guest.B1.Sig.SphincsWots18
import LeanVM.Guest.B1.Sig.SphincsWots19
import LeanVM.Guest.B1.Sig.SphincsWots20
import LeanVM.Guest.B1.Sig.SphincsData2

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

theorem sBody_length : Data.core20.body.length = 914 := by decide +kernel
theorem sBody_length' : sBody.length = 914 := by decide +kernel

open scoped Dec in
theorem sBody_elt_199 : Data.core20.body.getD 199 default = sBody.getD 199 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_199_3
  have h128 := drop_eq_of_take sBody_arms_199_2 h192
  have h64 := drop_eq_of_take sBody_arms_199_1 h128
  have h0 := drop_eq_of_take sBody_arms_199_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_209 : Data.core20.body.getD 209 default = sBody.getD 209 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_209_3
  have h128 := drop_eq_of_take sBody_arms_209_2 h192
  have h64 := drop_eq_of_take sBody_arms_209_1 h128
  have h0 := drop_eq_of_take sBody_arms_209_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_235 : Data.core20.body.getD 235 default = sBody.getD 235 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_235_3
  have h128 := drop_eq_of_take sBody_arms_235_2 h192
  have h64 := drop_eq_of_take sBody_arms_235_1 h128
  have h0 := drop_eq_of_take sBody_arms_235_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_246 : Data.core20.body.getD 246 default = sBody.getD 246 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_246_3
  have h128 := drop_eq_of_take sBody_arms_246_2 h192
  have h64 := drop_eq_of_take sBody_arms_246_1 h128
  have h0 := drop_eq_of_take sBody_arms_246_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_272 : Data.core20.body.getD 272 default = sBody.getD 272 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_272_3
  have h128 := drop_eq_of_take sBody_arms_272_2 h192
  have h64 := drop_eq_of_take sBody_arms_272_1 h128
  have h0 := drop_eq_of_take sBody_arms_272_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_283 : Data.core20.body.getD 283 default = sBody.getD 283 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_283_3
  have h128 := drop_eq_of_take sBody_arms_283_2 h192
  have h64 := drop_eq_of_take sBody_arms_283_1 h128
  have h0 := drop_eq_of_take sBody_arms_283_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_309 : Data.core20.body.getD 309 default = sBody.getD 309 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_309_3
  have h128 := drop_eq_of_take sBody_arms_309_2 h192
  have h64 := drop_eq_of_take sBody_arms_309_1 h128
  have h0 := drop_eq_of_take sBody_arms_309_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_320 : Data.core20.body.getD 320 default = sBody.getD 320 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_320_3
  have h128 := drop_eq_of_take sBody_arms_320_2 h192
  have h64 := drop_eq_of_take sBody_arms_320_1 h128
  have h0 := drop_eq_of_take sBody_arms_320_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_346 : Data.core20.body.getD 346 default = sBody.getD 346 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_346_3
  have h128 := drop_eq_of_take sBody_arms_346_2 h192
  have h64 := drop_eq_of_take sBody_arms_346_1 h128
  have h0 := drop_eq_of_take sBody_arms_346_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_357 : Data.core20.body.getD 357 default = sBody.getD 357 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_357_3
  have h128 := drop_eq_of_take sBody_arms_357_2 h192
  have h64 := drop_eq_of_take sBody_arms_357_1 h128
  have h0 := drop_eq_of_take sBody_arms_357_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_383 : Data.core20.body.getD 383 default = sBody.getD 383 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_383_3
  have h128 := drop_eq_of_take sBody_arms_383_2 h192
  have h64 := drop_eq_of_take sBody_arms_383_1 h128
  have h0 := drop_eq_of_take sBody_arms_383_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_394 : Data.core20.body.getD 394 default = sBody.getD 394 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_394_3
  have h128 := drop_eq_of_take sBody_arms_394_2 h192
  have h64 := drop_eq_of_take sBody_arms_394_1 h128
  have h0 := drop_eq_of_take sBody_arms_394_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_420 : Data.core20.body.getD 420 default = sBody.getD 420 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_420_3
  have h128 := drop_eq_of_take sBody_arms_420_2 h192
  have h64 := drop_eq_of_take sBody_arms_420_1 h128
  have h0 := drop_eq_of_take sBody_arms_420_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_431 : Data.core20.body.getD 431 default = sBody.getD 431 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_431_3
  have h128 := drop_eq_of_take sBody_arms_431_2 h192
  have h64 := drop_eq_of_take sBody_arms_431_1 h128
  have h0 := drop_eq_of_take sBody_arms_431_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_457 : Data.core20.body.getD 457 default = sBody.getD 457 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_457_3
  have h128 := drop_eq_of_take sBody_arms_457_2 h192
  have h64 := drop_eq_of_take sBody_arms_457_1 h128
  have h0 := drop_eq_of_take sBody_arms_457_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

open scoped Dec in
theorem sBody_elt_468 : Data.core20.body.getD 468 default = sBody.getD 468 default := by
  refine eq_of_match (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  have h192 := sBody_arms_468_3
  have h128 := drop_eq_of_take sBody_arms_468_2 h192
  have h64 := drop_eq_of_take sBody_arms_468_1 h128
  have h0 := drop_eq_of_take sBody_arms_468_0 h64
  rwa [List.drop_zero, List.drop_zero] at h0

/-- The body, checked by the kernel in slices: the forest keys' dispatches (256 arms each) a
statement at a time, their arms 64 at a time. -/
theorem sBody_eq : Data.core20.body = sBody := by
  have h619 := sBody_drop_619
  have h615 := drop_eq_of_take sBody_slice_615 h619
  have h611 := drop_eq_of_take sBody_slice_611 h615
  have h607 := drop_eq_of_take sBody_slice_607 h611
  have h603 := drop_eq_of_take sBody_slice_603 h607
  have h599 := drop_eq_of_take sBody_slice_599 h603
  have h595 := drop_eq_of_take sBody_slice_595 h599
  have h591 := drop_eq_of_take sBody_slice_591 h595
  have h587 := drop_eq_of_take sBody_slice_587 h591
  have h583 := drop_eq_of_take sBody_slice_583 h587
  have h579 := drop_eq_of_take sBody_slice_579 h583
  have h575 := drop_eq_of_take sBody_slice_575 h579
  have h571 := drop_eq_of_take sBody_slice_571 h575
  have h567 := drop_eq_of_take sBody_slice_567 h571
  have h563 := drop_eq_of_take sBody_slice_563 h567
  have h559 := drop_eq_of_take sBody_slice_559 h563
  have h555 := drop_eq_of_take sBody_slice_555 h559
  have h551 := drop_eq_of_take sBody_slice_551 h555
  have h547 := drop_eq_of_take sBody_slice_547 h551
  have h543 := drop_eq_of_take sBody_slice_543 h547
  have h539 := drop_eq_of_take sBody_slice_539 h543
  have h535 := drop_eq_of_take sBody_slice_535 h539
  have h480 := drop_eq_of_take sBody_slice_480 h535
  have h469 := drop_eq_of_take sBody_slice_469 h480
  have h468 := drop_eq_of_take (take_one_of_getD sBody_elt_468 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h469
  have h458 := drop_eq_of_take sBody_slice_458 h468
  have h457 := drop_eq_of_take (take_one_of_getD sBody_elt_457 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h458
  have h432 := drop_eq_of_take sBody_slice_432 h457
  have h431 := drop_eq_of_take (take_one_of_getD sBody_elt_431 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h432
  have h421 := drop_eq_of_take sBody_slice_421 h431
  have h420 := drop_eq_of_take (take_one_of_getD sBody_elt_420 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h421
  have h395 := drop_eq_of_take sBody_slice_395 h420
  have h394 := drop_eq_of_take (take_one_of_getD sBody_elt_394 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h395
  have h384 := drop_eq_of_take sBody_slice_384 h394
  have h383 := drop_eq_of_take (take_one_of_getD sBody_elt_383 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h384
  have h358 := drop_eq_of_take sBody_slice_358 h383
  have h357 := drop_eq_of_take (take_one_of_getD sBody_elt_357 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h358
  have h347 := drop_eq_of_take sBody_slice_347 h357
  have h346 := drop_eq_of_take (take_one_of_getD sBody_elt_346 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h347
  have h321 := drop_eq_of_take sBody_slice_321 h346
  have h320 := drop_eq_of_take (take_one_of_getD sBody_elt_320 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h321
  have h310 := drop_eq_of_take sBody_slice_310 h320
  have h309 := drop_eq_of_take (take_one_of_getD sBody_elt_309 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h310
  have h284 := drop_eq_of_take sBody_slice_284 h309
  have h283 := drop_eq_of_take (take_one_of_getD sBody_elt_283 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h284
  have h273 := drop_eq_of_take sBody_slice_273 h283
  have h272 := drop_eq_of_take (take_one_of_getD sBody_elt_272 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h273
  have h247 := drop_eq_of_take sBody_slice_247 h272
  have h246 := drop_eq_of_take (take_one_of_getD sBody_elt_246 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h247
  have h236 := drop_eq_of_take sBody_slice_236 h246
  have h235 := drop_eq_of_take (take_one_of_getD sBody_elt_235 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h236
  have h210 := drop_eq_of_take sBody_slice_210 h235
  have h209 := drop_eq_of_take (take_one_of_getD sBody_elt_209 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h210
  have h200 := drop_eq_of_take sBody_slice_200 h209
  have h199 := drop_eq_of_take (take_one_of_getD sBody_elt_199 (by rw [sBody_length]; omega)
    (by rw [sBody_length']; omega)) h200
  have h0 := drop_eq_of_take sBody_slice_0 h199
  rwa [List.drop_zero, List.drop_zero] at h0

end
end LeanVM.Guest.B1.Sig
