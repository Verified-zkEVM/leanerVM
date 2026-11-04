/-
  LeanVM.Guest.B1.Tables.Vt.FormsT1

  Table 1's forms on the three sides, from the guest's statements: each block's value from its
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
theorem vtB01_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3214) = σ (.n 981) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3147 [
    .atom (.load (.n 3204) (.n 13) 0),
    .atom (.const (.n 3205) (word 2 0 0)),
    .atom (.mul (.n 3206) (.n 3205) (.n 2997)),
    .atom (.load (.n 3207) (.n 13) 1),
    .atom (.mul (.n 3208) (.n 3207) (.n 3206)),
    .atom (.add (.n 3209) (.n 3204) (.n 3208)),
    .atom (.load (.n 3210) (.n 13) 2),
    .atom (.mul (.n 3211) (.n 3210) (.n 3021)),
    .atom (.add (.n 3212) (.n 3209) (.n 3211)),
    .atom (.add (.n 3213) (.n 14) (.n 3212)),
    .atom (.mul (.n 3214) (.n 981) (.n 3213))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3147, a3148, a3149, a3150, a3151, a3152, a3153, a3154, a3155, a3156, a3157, -⟩ := hs
  have e3147 := tb_loadHolds_unique a3147 (hw 0 (by norm_num))
  have e3150 := tb_loadHolds_unique a3150 (hw 1 (by norm_num))
  have e3153 := tb_loadHolds_unique a3153 (hw 2 (by norm_num))
  have v2997 : σ (.n 2997) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 15) (by norm_num)).2.2
  have v3021 : σ (.n 3021) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2
  have hB : σ (.n 3213) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v3021, v2997, a3156, a3155, a3154, e3153, a3152, a3151, e3150, a3149, a3148, e3147]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3157, hB]

set_option maxRecDepth 10000 in
theorem vtB01_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3249) = σ (.n 3214) + σ (.n 990) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([14], 2)], [([], 2)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3158 [
    .atom (.load (.n 3215) (.n 13) 0),
    .atom (.const (.n 3216) (word 4 0 0)),
    .atom (.mul (.n 3217) (.n 3215) (.n 3216)),
    .atom (.load (.n 3218) (.n 13) 1),
    .atom (.mul (.n 3219) (.n 3218) (.n 2997)),
    .atom (.add (.n 3220) (.n 3217) (.n 3219)),
    .atom (.const (.n 3221) (word 2 0 0)),
    .atom (.mul (.n 3222) (.n 3221) (.n 3203)),
    .atom (.load (.n 3223) (.n 13) 2),
    .atom (.mul (.n 3224) (.n 3223) (.n 3222)),
    .atom (.add (.n 3225) (.n 3220) (.n 3224)),
    .atom (.load (.n 3226) (.n 13) 3),
    .atom (.const (.n 3227) (word 2 0 0)),
    .atom (.mul (.n 3228) (.n 3226) (.n 3227)),
    .atom (.add (.n 3229) (.n 3225) (.n 3228)),
    .atom (.load (.n 3230) (.n 13) 4),
    .atom (.mul (.n 3231) (.n 3230) (.n 3032)),
    .atom (.add (.n 3232) (.n 3229) (.n 3231)),
    .atom (.load (.n 3233) (.n 13) 5),
    .atom (.mul (.n 3234) (.n 3233) (.n 3043)),
    .atom (.add (.n 3235) (.n 3232) (.n 3234)),
    .atom (.load (.n 3236) (.n 13) 6),
    .atom (.mul (.n 3237) (.n 3236) (.n 3054)),
    .atom (.add (.n 3238) (.n 3235) (.n 3237)),
    .atom (.load (.n 3239) (.n 13) 7),
    .atom (.const (.n 3240) (word 0 0 0)),
    .atom (.mul (.n 3241) (.n 3239) (.n 3240)),
    .atom (.add (.n 3242) (.n 3238) (.n 3241)),
    .atom (.load (.n 3243) (.n 13) 8),
    .atom (.const (.n 3244) (word 0 0 0)),
    .atom (.mul (.n 3245) (.n 3243) (.n 3244)),
    .atom (.add (.n 3246) (.n 3242) (.n 3245)),
    .atom (.add (.n 3247) (.n 14) (.n 3246)),
    .atom (.mul (.n 3248) (.n 990) (.n 3247)),
    .atom (.add (.n 3249) (.n 3214) (.n 3248))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3158, a3159, a3160, a3161, a3162, a3163, a3164, a3165, a3166, a3167, a3168, a3169, a3170, a3171,
    a3172, a3173, a3174, a3175, a3176, a3177, a3178, a3179, a3180, a3181, a3182, a3183, a3184,
    a3185, a3186, a3187, a3188, a3189, a3190, a3191, a3192, -⟩ := hs
  have e3158 := tb_loadHolds_unique a3158 (hw 0 (by norm_num))
  have e3161 := tb_loadHolds_unique a3161 (hw 1 (by norm_num))
  have e3166 := tb_loadHolds_unique a3166 (hw 2 (by norm_num))
  have e3169 := tb_loadHolds_unique a3169 (hw 3 (by norm_num))
  have e3173 := tb_loadHolds_unique a3173 (hw 4 (by norm_num))
  have e3176 := tb_loadHolds_unique a3176 (hw 5 (by norm_num))
  have e3179 := tb_loadHolds_unique a3179 (hw 6 (by norm_num))
  have e3182 := tb_loadHolds_unique a3182 (hw 7 (by norm_num))
  have e3186 := tb_loadHolds_unique a3186 (hw 8 (by norm_num))
  have v2997 : σ (.n 2997) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 15) (by norm_num)).2.2
  have v3032 : σ (.n 3032) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 17) (by norm_num)).2.2
  have v3043 : σ (.n 3043) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 18) (by norm_num)).2.2
  have v3054 : σ (.n 3054) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 19) (by norm_num)).2.2
  have v3203 : σ (.n 3203) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 29) (by norm_num)).2.2
  have hB : σ (.n 3247) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([14], 2)], [([], 2)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v3203, v3054, v3043, v3032, v2997, a3190, a3189, a3188, a3187, e3186, a3185, a3184, a3183,
      e3182, a3181, a3180, e3179, a3178, a3177, e3176, a3175, a3174, e3173, a3172, a3171,
      a3170, e3169, a3168, a3167, e3166, a3165, a3164, a3163, a3162, e3161, a3160, a3159,
      e3158]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3192, a3191, hB]

set_option maxRecDepth 10000 in
theorem vtB01_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3273) = σ (.n 3249) + σ (.n 999) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([11], 2)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3193 [
    .atom (.load (.n 3250) (.n 13) 0),
    .atom (.const (.n 3251) (word 2 0 0)),
    .atom (.mul (.n 3252) (.n 3250) (.n 3251)),
    .atom (.mul (.n 3253) (.n 3021) (.n 3032)),
    .atom (.load (.n 3254) (.n 13) 1),
    .atom (.mul (.n 3255) (.n 3254) (.n 3253)),
    .atom (.add (.n 3256) (.n 3252) (.n 3255)),
    .atom (.const (.n 3257) (word 2 0 0)),
    .atom (.mul (.n 3258) (.n 3257) (.n 3157)),
    .atom (.load (.n 3259) (.n 13) 2),
    .atom (.mul (.n 3260) (.n 3259) (.n 3258)),
    .atom (.add (.n 3261) (.n 3256) (.n 3260)),
    .atom (.load (.n 3262) (.n 13) 3),
    .atom (.mul (.n 3263) (.n 3262) (.n 3078)),
    .atom (.add (.n 3264) (.n 3261) (.n 3263)),
    .atom (.load (.n 3265) (.n 13) 4),
    .atom (.mul (.n 3266) (.n 3265) (.n 3089)),
    .atom (.add (.n 3267) (.n 3264) (.n 3266)),
    .atom (.load (.n 3268) (.n 13) 5),
    .atom (.mul (.n 3269) (.n 3268) (.n 3100)),
    .atom (.add (.n 3270) (.n 3267) (.n 3269)),
    .atom (.add (.n 3271) (.n 14) (.n 3270)),
    .atom (.mul (.n 3272) (.n 999) (.n 3271)),
    .atom (.add (.n 3273) (.n 3249) (.n 3272))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3193, a3194, a3195, a3196, a3197, a3198, a3199, a3200, a3201, a3202, a3203, a3204, a3205, a3206,
    a3207, a3208, a3209, a3210, a3211, a3212, a3213, a3214, a3215, a3216, -⟩ := hs
  have e3193 := tb_loadHolds_unique a3193 (hw 0 (by norm_num))
  have e3197 := tb_loadHolds_unique a3197 (hw 1 (by norm_num))
  have e3202 := tb_loadHolds_unique a3202 (hw 2 (by norm_num))
  have e3205 := tb_loadHolds_unique a3205 (hw 3 (by norm_num))
  have e3208 := tb_loadHolds_unique a3208 (hw 4 (by norm_num))
  have e3211 := tb_loadHolds_unique a3211 (hw 5 (by norm_num))
  have v3021 : σ (.n 3021) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2
  have v3032 : σ (.n 3032) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 17) (by norm_num)).2.2
  have v3078 : σ (.n 3078) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 20) (by norm_num)).2.2
  have v3089 : σ (.n 3089) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 21) (by norm_num)).2.2
  have v3100 : σ (.n 3100) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 22) (by norm_num)).2.2
  have v3157 : σ (.n 3157) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 26) (by norm_num)).2.2
  have hB : σ (.n 3271) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([11], 2)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
    simp only [v3157, v3100, v3089, v3078, v3032, v3021, a3214, a3213, a3212, e3211, a3210, a3209, e3208,
      a3207, a3206, e3205, a3204, a3203, e3202, a3201, a3200, a3199, a3198, e3197, a3196,
      a3195, a3194, e3193]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3216, a3215, hB]

set_option maxRecDepth 10000 in
theorem vtB01_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3297) = σ (.n 3273) + σ (.n 1008) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([12], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3217 [
    .atom (.load (.n 3274) (.n 13) 0),
    .atom (.const (.n 3275) (word 2 0 0)),
    .atom (.mul (.n 3276) (.n 3274) (.n 3275)),
    .atom (.mul (.n 3277) (.n 3021) (.n 3043)),
    .atom (.load (.n 3278) (.n 13) 1),
    .atom (.mul (.n 3279) (.n 3278) (.n 3277)),
    .atom (.add (.n 3280) (.n 3276) (.n 3279)),
    .atom (.const (.n 3281) (word 2 0 0)),
    .atom (.mul (.n 3282) (.n 3281) (.n 3168)),
    .atom (.load (.n 3283) (.n 13) 2),
    .atom (.mul (.n 3284) (.n 3283) (.n 3282)),
    .atom (.add (.n 3285) (.n 3280) (.n 3284)),
    .atom (.load (.n 3286) (.n 13) 3),
    .atom (.mul (.n 3287) (.n 3286) (.n 3111)),
    .atom (.add (.n 3288) (.n 3285) (.n 3287)),
    .atom (.load (.n 3289) (.n 13) 4),
    .atom (.mul (.n 3290) (.n 3289) (.n 3135)),
    .atom (.add (.n 3291) (.n 3288) (.n 3290)),
    .atom (.load (.n 3292) (.n 13) 5),
    .atom (.mul (.n 3293) (.n 3292) (.n 3146)),
    .atom (.add (.n 3294) (.n 3291) (.n 3293)),
    .atom (.add (.n 3295) (.n 14) (.n 3294)),
    .atom (.mul (.n 3296) (.n 1008) (.n 3295)),
    .atom (.add (.n 3297) (.n 3273) (.n 3296))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3217, a3218, a3219, a3220, a3221, a3222, a3223, a3224, a3225, a3226, a3227, a3228, a3229, a3230,
    a3231, a3232, a3233, a3234, a3235, a3236, a3237, a3238, a3239, a3240, -⟩ := hs
  have e3217 := tb_loadHolds_unique a3217 (hw 0 (by norm_num))
  have e3221 := tb_loadHolds_unique a3221 (hw 1 (by norm_num))
  have e3226 := tb_loadHolds_unique a3226 (hw 2 (by norm_num))
  have e3229 := tb_loadHolds_unique a3229 (hw 3 (by norm_num))
  have e3232 := tb_loadHolds_unique a3232 (hw 4 (by norm_num))
  have e3235 := tb_loadHolds_unique a3235 (hw 5 (by norm_num))
  have v3021 : σ (.n 3021) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2
  have v3043 : σ (.n 3043) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 18) (by norm_num)).2.2
  have v3111 : σ (.n 3111) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 23) (by norm_num)).2.2
  have v3135 : σ (.n 3135) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 24) (by norm_num)).2.2
  have v3146 : σ (.n 3146) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 25) (by norm_num)).2.2
  have v3168 : σ (.n 3168) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 27) (by norm_num)).2.2
  have hB : σ (.n 3295) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([12], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
    simp only [v3168, v3146, v3135, v3111, v3043, v3021, a3238, a3237, a3236, e3235, a3234, a3233, e3232,
      a3231, a3230, e3229, a3228, a3227, e3226, a3225, a3224, a3223, a3222, e3221, a3220,
      a3219, a3218, e3217]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3240, a3239, hB]

set_option maxRecDepth 10000 in
theorem vtB01_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3342) = σ (.n 3297) + σ (.n 1017) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([13], 2)], [([5, 8], 1), ([6, 10], 1), ([7, 9], 1)], [([5, 9], 1), ([6, 8], 1), ([6, 10], 1), ([7, 9], 1), ([7, 10], 1)], [([5, 10], 1), ([6, 9], 1), ([7, 8], 1), ([7, 10], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3241 [
    .atom (.load (.n 3298) (.n 13) 0),
    .atom (.const (.n 3299) (word 2 0 0)),
    .atom (.mul (.n 3300) (.n 3298) (.n 3299)),
    .atom (.mul (.n 3301) (.n 3021) (.n 3054)),
    .atom (.load (.n 3302) (.n 13) 1),
    .atom (.mul (.n 3303) (.n 3302) (.n 3301)),
    .atom (.add (.n 3304) (.n 3300) (.n 3303)),
    .atom (.const (.n 3305) (word 2 0 0)),
    .atom (.mul (.n 3306) (.n 3305) (.n 3192)),
    .atom (.load (.n 3307) (.n 13) 2),
    .atom (.mul (.n 3308) (.n 3307) (.n 3306)),
    .atom (.add (.n 3309) (.n 3304) (.n 3308)),
    .atom (.mul (.n 3310) (.n 3078) (.n 3111)),
    .atom (.mul (.n 3311) (.n 3089) (.n 3146)),
    .atom (.add (.n 3312) (.n 3310) (.n 3311)),
    .atom (.mul (.n 3313) (.n 3100) (.n 3135)),
    .atom (.add (.n 3314) (.n 3312) (.n 3313)),
    .atom (.load (.n 3315) (.n 13) 3),
    .atom (.mul (.n 3316) (.n 3315) (.n 3314)),
    .atom (.add (.n 3317) (.n 3309) (.n 3316)),
    .atom (.mul (.n 3318) (.n 3078) (.n 3135)),
    .atom (.mul (.n 3319) (.n 3089) (.n 3111)),
    .atom (.add (.n 3320) (.n 3318) (.n 3319)),
    .atom (.mul (.n 3321) (.n 3089) (.n 3146)),
    .atom (.add (.n 3322) (.n 3320) (.n 3321)),
    .atom (.mul (.n 3323) (.n 3100) (.n 3135)),
    .atom (.add (.n 3324) (.n 3322) (.n 3323)),
    .atom (.mul (.n 3325) (.n 3100) (.n 3146)),
    .atom (.add (.n 3326) (.n 3324) (.n 3325)),
    .atom (.load (.n 3327) (.n 13) 4),
    .atom (.mul (.n 3328) (.n 3327) (.n 3326)),
    .atom (.add (.n 3329) (.n 3317) (.n 3328)),
    .atom (.mul (.n 3330) (.n 3078) (.n 3146)),
    .atom (.mul (.n 3331) (.n 3089) (.n 3135)),
    .atom (.add (.n 3332) (.n 3330) (.n 3331)),
    .atom (.mul (.n 3333) (.n 3100) (.n 3111)),
    .atom (.add (.n 3334) (.n 3332) (.n 3333)),
    .atom (.mul (.n 3335) (.n 3100) (.n 3146)),
    .atom (.add (.n 3336) (.n 3334) (.n 3335)),
    .atom (.load (.n 3337) (.n 13) 5),
    .atom (.mul (.n 3338) (.n 3337) (.n 3336)),
    .atom (.add (.n 3339) (.n 3329) (.n 3338)),
    .atom (.add (.n 3340) (.n 14) (.n 3339)),
    .atom (.mul (.n 3341) (.n 1017) (.n 3340)),
    .atom (.add (.n 3342) (.n 3297) (.n 3341))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3241, a3242, a3243, a3244, a3245, a3246, a3247, a3248, a3249, a3250, a3251, a3252, a3253, a3254,
    a3255, a3256, a3257, a3258, a3259, a3260, a3261, a3262, a3263, a3264, a3265, a3266, a3267,
    a3268, a3269, a3270, a3271, a3272, a3273, a3274, a3275, a3276, a3277, a3278, a3279, a3280,
    a3281, a3282, a3283, a3284, a3285, -⟩ := hs
  have e3241 := tb_loadHolds_unique a3241 (hw 0 (by norm_num))
  have e3245 := tb_loadHolds_unique a3245 (hw 1 (by norm_num))
  have e3250 := tb_loadHolds_unique a3250 (hw 2 (by norm_num))
  have e3258 := tb_loadHolds_unique a3258 (hw 3 (by norm_num))
  have e3270 := tb_loadHolds_unique a3270 (hw 4 (by norm_num))
  have e3280 := tb_loadHolds_unique a3280 (hw 5 (by norm_num))
  have v3021 : σ (.n 3021) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2
  have v3054 : σ (.n 3054) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 19) (by norm_num)).2.2
  have v3078 : σ (.n 3078) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 20) (by norm_num)).2.2
  have v3089 : σ (.n 3089) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 21) (by norm_num)).2.2
  have v3100 : σ (.n 3100) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 22) (by norm_num)).2.2
  have v3111 : σ (.n 3111) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 23) (by norm_num)).2.2
  have v3135 : σ (.n 3135) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 24) (by norm_num)).2.2
  have v3146 : σ (.n 3146) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 25) (by norm_num)).2.2
  have v3192 : σ (.n 3192) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 28) (by norm_num)).2.2
  have hB : σ (.n 3340) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([13], 2)], [([5, 8], 1), ([6, 10], 1), ([7, 9], 1)], [([5, 9], 1), ([6, 8], 1), ([6, 10], 1), ([7, 9], 1), ([7, 10], 1)], [([5, 10], 1), ([6, 9], 1), ([7, 8], 1), ([7, 10], 1)]] := by
    simp only [v3192, v3146, v3135, v3111, v3100, v3089, v3078, v3054, v3021, a3283, a3282, a3281, e3280,
      a3279, a3278, a3277, a3276, a3275, a3274, a3273, a3272, a3271, e3270, a3269, a3268,
      a3267, a3266, a3265, a3264, a3263, a3262, a3261, a3260, a3259, e3258, a3257, a3256,
      a3255, a3254, a3253, a3252, a3251, e3250, a3249, a3248, a3247, a3246, e3245, a3244,
      a3243, a3242, e3241]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3285, a3284, hB]

set_option maxRecDepth 10000 in
theorem vtSide01 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3342) =
      vtSideVal [σ (.n 981), σ (.n 990), σ (.n 999), σ (.n 1008), σ (.n 1017)]
        (σ (.n 14)) W ev vtBTerms01 := by
  rw [vtB01_4 h hw hev, vtB01_3 h hw hev, vtB01_2 h hw hev, vtB01_1 h hw hev, vtB01_0 h hw hev]
  simp only [vtSideVal, vtBTerms01, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD1_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3348) = σ (.n 1962) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3287 [
    .atom (.const (.n 3344) (word 3 0 0)),
    .atom (.mul (.n 3345) (.n 3344) (.n 2997)),
    .atom (.load (.n 3346) (.n 13) 1),
    .atom (.mul (.n 3347) (.n 3346) (.n 3345)),
    .atom (.mul (.n 3348) (.n 1962) (.n 3347))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3287, a3288, a3289, a3290, a3291, -⟩ := hs
  have e3289 := tb_loadHolds_unique a3289 (hw 1 (by norm_num))
  have v2997 : σ (.n 2997) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 15) (by norm_num)).2.2
  have hB : σ (.n 3347) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v2997, a3290, e3289, a3288, a3287]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3291, hB]

set_option maxRecDepth 10000 in
theorem vtD1_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3354) = σ (.n 3348) + σ (.n 1964) * vtSlots W ev 0
      [[], [], [([14], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3292 [
    .atom (.const (.n 3349) (word 3 0 0)),
    .atom (.mul (.n 3350) (.n 3349) (.n 3203)),
    .atom (.load (.n 3351) (.n 13) 2),
    .atom (.mul (.n 3352) (.n 3351) (.n 3350)),
    .atom (.mul (.n 3353) (.n 1964) (.n 3352)),
    .atom (.add (.n 3354) (.n 3348) (.n 3353))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3292, a3293, a3294, a3295, a3296, a3297, -⟩ := hs
  have e3294 := tb_loadHolds_unique a3294 (hw 2 (by norm_num))
  have v3203 : σ (.n 3203) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 29) (by norm_num)).2.2
  have hB : σ (.n 3352) = vtSlots W ev 0 [[], [], [([14], 3)], [], [], [], [], [], []] := by
    simp only [v3203, a3295, e3294, a3293, a3292]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3297, a3296, hB]

set_option maxRecDepth 10000 in
theorem vtD1_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3360) = σ (.n 3354) + σ (.n 1966) * vtSlots W ev 0
      [[], [], [([11], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3298 [
    .atom (.const (.n 3355) (word 3 0 0)),
    .atom (.mul (.n 3356) (.n 3355) (.n 3157)),
    .atom (.load (.n 3357) (.n 13) 2),
    .atom (.mul (.n 3358) (.n 3357) (.n 3356)),
    .atom (.mul (.n 3359) (.n 1966) (.n 3358)),
    .atom (.add (.n 3360) (.n 3354) (.n 3359))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3298, a3299, a3300, a3301, a3302, a3303, -⟩ := hs
  have e3300 := tb_loadHolds_unique a3300 (hw 2 (by norm_num))
  have v3157 : σ (.n 3157) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 26) (by norm_num)).2.2
  have hB : σ (.n 3358) = vtSlots W ev 0 [[], [], [([11], 3)], [], [], []] := by
    simp only [v3157, a3301, e3300, a3299, a3298]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3303, a3302, hB]

set_option maxRecDepth 10000 in
theorem vtD1_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3366) = σ (.n 3360) + σ (.n 1968) * vtSlots W ev 0
      [[], [], [([12], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3304 [
    .atom (.const (.n 3361) (word 3 0 0)),
    .atom (.mul (.n 3362) (.n 3361) (.n 3168)),
    .atom (.load (.n 3363) (.n 13) 2),
    .atom (.mul (.n 3364) (.n 3363) (.n 3362)),
    .atom (.mul (.n 3365) (.n 1968) (.n 3364)),
    .atom (.add (.n 3366) (.n 3360) (.n 3365))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3304, a3305, a3306, a3307, a3308, a3309, -⟩ := hs
  have e3306 := tb_loadHolds_unique a3306 (hw 2 (by norm_num))
  have v3168 : σ (.n 3168) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 27) (by norm_num)).2.2
  have hB : σ (.n 3364) = vtSlots W ev 0 [[], [], [([12], 3)], [], [], []] := by
    simp only [v3168, a3307, e3306, a3305, a3304]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3309, a3308, hB]

set_option maxRecDepth 10000 in
theorem vtD1_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3372) = σ (.n 3366) + σ (.n 1970) * vtSlots W ev 0
      [[], [], [([13], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3310 [
    .atom (.const (.n 3367) (word 3 0 0)),
    .atom (.mul (.n 3368) (.n 3367) (.n 3192)),
    .atom (.load (.n 3369) (.n 13) 2),
    .atom (.mul (.n 3370) (.n 3369) (.n 3368)),
    .atom (.mul (.n 3371) (.n 1970) (.n 3370)),
    .atom (.add (.n 3372) (.n 3366) (.n 3371))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3310, a3311, a3312, a3313, a3314, a3315, -⟩ := hs
  have e3312 := tb_loadHolds_unique a3312 (hw 2 (by norm_num))
  have v3192 : σ (.n 3192) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 28) (by norm_num)).2.2
  have hB : σ (.n 3370) = vtSlots W ev 0 [[], [], [([13], 3)], [], [], []] := by
    simp only [v3192, a3313, e3312, a3311, a3310]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3315, a3314, hB]

set_option maxRecDepth 10000 in
theorem vtSide11 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3373) =
      vtSideVal [σ (.n 1962), σ (.n 1964), σ (.n 1966), σ (.n 1968), σ (.n 1970)]
        (σ (.n 14)) W ev vtBTerms11 := by
  have hF0 : σ (.n 3342) =
      vtSideVal [σ (.n 1962), σ (.n 1964), σ (.n 1966), σ (.n 1968), σ (.n 1970)]
        (σ (.n 14)) W ev vtBTerms01 := by
    rw [vtPullSels1 h]; exact vtSide01 h hw hev
  have a3316 := h.atomAt 3316 (.add (.n 3373) (.n 3342) (.n 3372)) (by decide +kernel)
  simp only [Atom.Holds] at a3316
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull1, ← hF0, a3316, vtD1_4 h hw hev, vtD1_3 h hw hev, vtD1_2 h hw hev, vtD1_1 h hw hev, vtD1_0 h hw hev]
  simp only [vtDiffSum, vtDTerms1, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide21 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3382) =
      vtSideVal [σ (.n 2085), σ (.n 2094), σ (.n 2103), σ (.n 2112)]
        (0) (fun _ ↦ 1) ev vtBTerms21 := by
  obtain ⟨_, hs⟩ := h.sliceAt 3319 [
    .atom (.mul (.n 3376) (.n 2085) (.n 3157)),
    .atom (.mul (.n 3377) (.n 2094) (.n 3168)),
    .atom (.add (.n 3378) (.n 3376) (.n 3377)),
    .atom (.mul (.n 3379) (.n 2103) (.n 3192)),
    .atom (.add (.n 3380) (.n 3378) (.n 3379)),
    .atom (.mul (.n 3381) (.n 2112) (.n 3203)),
    .atom (.add (.n 3382) (.n 3380) (.n 3381))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3319, a3320, a3321, a3322, a3323, a3324, a3325, -⟩ := hs
  have v3157 : σ (.n 3157) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 26) (by norm_num)).2.2
  have v3168 : σ (.n 3168) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 27) (by norm_num)).2.2
  have v3192 : σ (.n 3192) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 28) (by norm_num)).2.2
  have v3203 : σ (.n 3203) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 29) (by norm_num)).2.2
  rw [a3325, a3323, a3321, a3319, a3320, a3322, a3324, v3157, v3168, v3192, v3203]
  simp only [vtSideVal, vtBTerms21, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
