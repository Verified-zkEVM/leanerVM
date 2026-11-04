/-
  LeanVM.Guest.B1.Tables.VtC.FForms2

  `Vt/FormsT2.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT2

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB02_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3517) = σ (.n 1026) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3418 [
    .atom (.load (.n 3507) (.n 13) 0),
    .atom (.const (.n 3508) (word 2 0 0)),
    .atom (.mul (.n 3509) (.n 3508) (.n 3403)),
    .atom (.load (.n 3510) (.n 13) 1),
    .atom (.mul (.n 3511) (.n 3510) (.n 3509)),
    .atom (.add (.n 3512) (.n 3507) (.n 3511)),
    .atom (.load (.n 3513) (.n 13) 2),
    .atom (.mul (.n 3514) (.n 3513) (.n 3414)),
    .atom (.add (.n 3515) (.n 3512) (.n 3514)),
    .atom (.add (.n 3516) (.n 14) (.n 3515)),
    .atom (.mul (.n 3517) (.n 1026) (.n 3516))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3418, a3419, a3420, a3421, a3422, a3423, a3424, a3425, a3426, a3427, a3428, -⟩ := hs
  have e3418 := tb_loadHolds_unique a3418 (hw 0 (by norm_num))
  have e3421 := tb_loadHolds_unique a3421 (hw 1 (by norm_num))
  have e3424 := tb_loadHolds_unique a3424 (hw 2 (by norm_num))
  have v3403 : σ (.n 3403) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 30) (by norm_num)).2.2
  have v3414 : σ (.n 3414) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 31) (by norm_num)).2.2
  have hB : σ (.n 3516) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v3414, v3403, a3427, a3426, a3425, e3424, a3423, a3422, e3421, a3420, a3419, e3418]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3428, hB]

set_option maxRecDepth 10000 in
theorem vtB02_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3551) = σ (.n 3517) + σ (.n 1035) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([7], 2)], [([], 4)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3429 [
    .atom (.load (.n 3518) (.n 13) 0),
    .atom (.const (.n 3519) (word 4 0 0)),
    .atom (.mul (.n 3520) (.n 3518) (.n 3519)),
    .atom (.load (.n 3521) (.n 13) 1),
    .atom (.mul (.n 3522) (.n 3521) (.n 3403)),
    .atom (.add (.n 3523) (.n 3520) (.n 3522)),
    .atom (.const (.n 3524) (word 2 0 0)),
    .atom (.mul (.n 3525) (.n 3524) (.n 3506)),
    .atom (.load (.n 3526) (.n 13) 2),
    .atom (.mul (.n 3527) (.n 3526) (.n 3525)),
    .atom (.add (.n 3528) (.n 3523) (.n 3527)),
    .atom (.load (.n 3529) (.n 13) 3),
    .atom (.const (.n 3530) (word 4 0 0)),
    .atom (.mul (.n 3531) (.n 3529) (.n 3530)),
    .atom (.add (.n 3532) (.n 3528) (.n 3531)),
    .atom (.load (.n 3533) (.n 13) 4),
    .atom (.mul (.n 3534) (.n 3533) (.n 3438)),
    .atom (.add (.n 3535) (.n 3532) (.n 3534)),
    .atom (.load (.n 3536) (.n 13) 5),
    .atom (.mul (.n 3537) (.n 3536) (.n 3449)),
    .atom (.add (.n 3538) (.n 3535) (.n 3537)),
    .atom (.load (.n 3539) (.n 13) 6),
    .atom (.mul (.n 3540) (.n 3539) (.n 3460)),
    .atom (.add (.n 3541) (.n 3538) (.n 3540)),
    .atom (.load (.n 3542) (.n 13) 7),
    .atom (.mul (.n 3543) (.n 3542) (.n 3471)),
    .atom (.add (.n 3544) (.n 3541) (.n 3543)),
    .atom (.load (.n 3545) (.n 13) 8),
    .atom (.const (.n 3546) (word 0 0 0)),
    .atom (.mul (.n 3547) (.n 3545) (.n 3546)),
    .atom (.add (.n 3548) (.n 3544) (.n 3547)),
    .atom (.add (.n 3549) (.n 14) (.n 3548)),
    .atom (.mul (.n 3550) (.n 1035) (.n 3549)),
    .atom (.add (.n 3551) (.n 3517) (.n 3550))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3429, a3430, a3431, a3432, a3433, a3434, a3435, a3436, a3437, a3438, a3439, a3440, a3441, a3442,
    a3443, a3444, a3445, a3446, a3447, a3448, a3449, a3450, a3451, a3452, a3453, a3454, a3455,
    a3456, a3457, a3458, a3459, a3460, a3461, a3462, -⟩ := hs
  have e3429 := tb_loadHolds_unique a3429 (hw 0 (by norm_num))
  have e3432 := tb_loadHolds_unique a3432 (hw 1 (by norm_num))
  have e3437 := tb_loadHolds_unique a3437 (hw 2 (by norm_num))
  have e3440 := tb_loadHolds_unique a3440 (hw 3 (by norm_num))
  have e3444 := tb_loadHolds_unique a3444 (hw 4 (by norm_num))
  have e3447 := tb_loadHolds_unique a3447 (hw 5 (by norm_num))
  have e3450 := tb_loadHolds_unique a3450 (hw 6 (by norm_num))
  have e3453 := tb_loadHolds_unique a3453 (hw 7 (by norm_num))
  have e3456 := tb_loadHolds_unique a3456 (hw 8 (by norm_num))
  have v3403 : σ (.n 3403) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 30) (by norm_num)).2.2
  have v3438 : σ (.n 3438) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 32) (by norm_num)).2.2
  have v3449 : σ (.n 3449) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 33) (by norm_num)).2.2
  have v3460 : σ (.n 3460) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 34) (by norm_num)).2.2
  have v3471 : σ (.n 3471) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 35) (by norm_num)).2.2
  have v3506 : σ (.n 3506) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 37) (by norm_num)).2.2
  have hB : σ (.n 3549) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([7], 2)], [([], 4)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([], 0)]] := by
    simp only [v3506, v3471, v3460, v3449, v3438, v3403, a3460, a3459, a3458, a3457, e3456, a3455, a3454,
      e3453, a3452, a3451, e3450, a3449, a3448, e3447, a3446, a3445, e3444, a3443, a3442,
      a3441, e3440, a3439, a3438, e3437, a3436, a3435, a3434, a3433, e3432, a3431, a3430,
      e3429]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3462, a3461, hB]

set_option maxRecDepth 10000 in
theorem vtB02_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3575) = σ (.n 3551) + σ (.n 1044) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([6], 2)], [([3], 1)], [([4], 1)], [([5], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3463 [
    .atom (.load (.n 3552) (.n 13) 0),
    .atom (.const (.n 3553) (word 2 0 0)),
    .atom (.mul (.n 3554) (.n 3552) (.n 3553)),
    .atom (.mul (.n 3555) (.n 3414) (.n 3438)),
    .atom (.load (.n 3556) (.n 13) 1),
    .atom (.mul (.n 3557) (.n 3556) (.n 3555)),
    .atom (.add (.n 3558) (.n 3554) (.n 3557)),
    .atom (.const (.n 3559) (word 2 0 0)),
    .atom (.mul (.n 3560) (.n 3559) (.n 3495)),
    .atom (.load (.n 3561) (.n 13) 2),
    .atom (.mul (.n 3562) (.n 3561) (.n 3560)),
    .atom (.add (.n 3563) (.n 3558) (.n 3562)),
    .atom (.load (.n 3564) (.n 13) 3),
    .atom (.mul (.n 3565) (.n 3564) (.n 3449)),
    .atom (.add (.n 3566) (.n 3563) (.n 3565)),
    .atom (.load (.n 3567) (.n 13) 4),
    .atom (.mul (.n 3568) (.n 3567) (.n 3460)),
    .atom (.add (.n 3569) (.n 3566) (.n 3568)),
    .atom (.load (.n 3570) (.n 13) 5),
    .atom (.mul (.n 3571) (.n 3570) (.n 3471)),
    .atom (.add (.n 3572) (.n 3569) (.n 3571)),
    .atom (.add (.n 3573) (.n 14) (.n 3572)),
    .atom (.mul (.n 3574) (.n 1044) (.n 3573)),
    .atom (.add (.n 3575) (.n 3551) (.n 3574))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3463, a3464, a3465, a3466, a3467, a3468, a3469, a3470, a3471, a3472, a3473, a3474, a3475, a3476,
    a3477, a3478, a3479, a3480, a3481, a3482, a3483, a3484, a3485, a3486, -⟩ := hs
  have e3463 := tb_loadHolds_unique a3463 (hw 0 (by norm_num))
  have e3467 := tb_loadHolds_unique a3467 (hw 1 (by norm_num))
  have e3472 := tb_loadHolds_unique a3472 (hw 2 (by norm_num))
  have e3475 := tb_loadHolds_unique a3475 (hw 3 (by norm_num))
  have e3478 := tb_loadHolds_unique a3478 (hw 4 (by norm_num))
  have e3481 := tb_loadHolds_unique a3481 (hw 5 (by norm_num))
  have v3414 : σ (.n 3414) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 31) (by norm_num)).2.2
  have v3438 : σ (.n 3438) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 32) (by norm_num)).2.2
  have v3449 : σ (.n 3449) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 33) (by norm_num)).2.2
  have v3460 : σ (.n 3460) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 34) (by norm_num)).2.2
  have v3471 : σ (.n 3471) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 35) (by norm_num)).2.2
  have v3495 : σ (.n 3495) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 36) (by norm_num)).2.2
  have hB : σ (.n 3573) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([6], 2)], [([3], 1)], [([4], 1)], [([5], 1)]] := by
    simp only [v3495, v3471, v3460, v3449, v3438, v3414, a3484, a3483, a3482, e3481, a3480, a3479, e3478,
      a3477, a3476, e3475, a3474, a3473, e3472, a3471, a3470, a3469, a3468, e3467, a3466,
      a3465, a3464, e3463]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3486, a3485, hB]

set_option maxRecDepth 10000 in
theorem vtSide02F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3575) =
      vtSideVal [σ (.n 1026), σ (.n 1035), σ (.n 1044)]
        (σ (.n 14)) W ev vtBTerms02 := by
  rw [vtB02_2F h hw hev, vtB02_1F h hw hev, vtB02_0F h hw hev]
  simp only [vtSideVal, vtBTerms02, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD2_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3581) = σ (.n 1972) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3488 [
    .atom (.const (.n 3577) (word 3 0 0)),
    .atom (.mul (.n 3578) (.n 3577) (.n 3403)),
    .atom (.load (.n 3579) (.n 13) 1),
    .atom (.mul (.n 3580) (.n 3579) (.n 3578)),
    .atom (.mul (.n 3581) (.n 1972) (.n 3580))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3488, a3489, a3490, a3491, a3492, -⟩ := hs
  have e3490 := tb_loadHolds_unique a3490 (hw 1 (by norm_num))
  have v3403 : σ (.n 3403) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 30) (by norm_num)).2.2
  have hB : σ (.n 3580) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v3403, a3491, e3490, a3489, a3488]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3492, hB]

set_option maxRecDepth 10000 in
theorem vtD2_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3587) = σ (.n 3581) + σ (.n 1974) * vtSlots W ev 0
      [[], [], [([7], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3493 [
    .atom (.const (.n 3582) (word 3 0 0)),
    .atom (.mul (.n 3583) (.n 3582) (.n 3506)),
    .atom (.load (.n 3584) (.n 13) 2),
    .atom (.mul (.n 3585) (.n 3584) (.n 3583)),
    .atom (.mul (.n 3586) (.n 1974) (.n 3585)),
    .atom (.add (.n 3587) (.n 3581) (.n 3586))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3493, a3494, a3495, a3496, a3497, a3498, -⟩ := hs
  have e3495 := tb_loadHolds_unique a3495 (hw 2 (by norm_num))
  have v3506 : σ (.n 3506) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 37) (by norm_num)).2.2
  have hB : σ (.n 3585) = vtSlots W ev 0 [[], [], [([7], 3)], [], [], [], [], [], []] := by
    simp only [v3506, a3496, e3495, a3494, a3493]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3498, a3497, hB]

set_option maxRecDepth 10000 in
theorem vtD2_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3593) = σ (.n 3587) + σ (.n 1976) * vtSlots W ev 0
      [[], [], [([6], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3499 [
    .atom (.const (.n 3588) (word 3 0 0)),
    .atom (.mul (.n 3589) (.n 3588) (.n 3495)),
    .atom (.load (.n 3590) (.n 13) 2),
    .atom (.mul (.n 3591) (.n 3590) (.n 3589)),
    .atom (.mul (.n 3592) (.n 1976) (.n 3591)),
    .atom (.add (.n 3593) (.n 3587) (.n 3592))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3499, a3500, a3501, a3502, a3503, a3504, -⟩ := hs
  have e3501 := tb_loadHolds_unique a3501 (hw 2 (by norm_num))
  have v3495 : σ (.n 3495) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 36) (by norm_num)).2.2
  have hB : σ (.n 3591) = vtSlots W ev 0 [[], [], [([6], 3)], [], [], []] := by
    simp only [v3495, a3502, e3501, a3500, a3499]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3504, a3503, hB]

set_option maxRecDepth 10000 in
theorem vtSide12F {rd : Reader} {σ : Val} (h : VtF rd σ)
    (hq : [σ (.n 1972), σ (.n 1974), σ (.n 1976)] = [σ (.n 1026), σ (.n 1035), σ (.n 1044)]) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3594) =
      vtSideVal [σ (.n 1972), σ (.n 1974), σ (.n 1976)]
        (σ (.n 14)) W ev vtBTerms12 := by
  have hF0 : σ (.n 3575) =
      vtSideVal [σ (.n 1972), σ (.n 1974), σ (.n 1976)]
        (σ (.n 14)) W ev vtBTerms02 := by
    rw [hq]; exact vtSide02F h hw hev
  have a3505 := h.atomAt 3505 (.add (.n 3594) (.n 3575) (.n 3593)) (by decide +kernel)
  simp only [Atom.Holds] at a3505
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull2, ← hF0, a3505, vtD2_2F h hw hev, vtD2_1F h hw hev, vtD2_0F h hw hev]
  simp only [vtDiffSum, vtDTerms2, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide22F {rd : Reader} {σ : Val} (h : VtF rd σ) {ev : ℕ → E}
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3599) =
      vtSideVal [σ (.n 2121), σ (.n 2130)]
        (0) (fun _ ↦ 1) ev vtBTerms22 := by
  obtain ⟨_, hs⟩ := h.sliceAt 3508 [
    .atom (.mul (.n 3597) (.n 2121) (.n 3495)),
    .atom (.mul (.n 3598) (.n 2130) (.n 3506)),
    .atom (.add (.n 3599) (.n 3597) (.n 3598))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3508, a3509, a3510, -⟩ := hs
  have v3495 : σ (.n 3495) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 36) (by norm_num)).2.2
  have v3506 : σ (.n 3506) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 37) (by norm_num)).2.2
  rw [a3510, a3508, a3509, v3495, v3506]
  simp only [vtSideVal, vtBTerms22, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero]

end
end LeanVM.Guest.B1.Tables
