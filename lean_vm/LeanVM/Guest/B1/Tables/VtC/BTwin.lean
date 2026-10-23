/-
  LeanVM.Guest.B1.Tables.VtC.BTwin

  The soundness's algebra of the bus sides, replayed on `VtP` (generated:
  scripts/b1c-vt/genbtwin.py from Vt/{PushFw,PushPad,PullTotal,PullSels,CountTotal}.lean).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BBase
public import LeanVM.Guest.B1.Tables.Vt.AsmTotals

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The push side's framework accumulator.** -/
theorem vtP_push_fw {rd : Reader} {σ : Val} (h : VtP rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i)) :
    σ (.n 3036) = σ (.n 2870) * (σ (.n 15) + (W 0 + W 1 + W 2)) +
      σ (.n 2900) * (σ (.n 15) + (W 0 * gen + W 1 * σ (.n 2908) + W 2 + W 3 * σ (.n 2914) +
        W 4 * σ (.n 2927) + W 5 * σ (.n 2940))) +
      σ (.n 2975) * (σ (.n 15) + (W 0 * gen ^ 2 + W 1 * σ (.n 2983) + W 2 + σ (.n 2639))) := by
  have a2424 := h.atom 2424 (.load (.n 2874) (.n 14) 0) (by decide +kernel)
  have a2425 := h.atom 2425 (.load (.n 2875) (.n 14) 1) (by decide +kernel)
  have a2426 := h.atom 2426 (.add (.n 2876) (.n 2874) (.n 2875)) (by decide +kernel)
  have a2427 := h.atom 2427 (.load (.n 2877) (.n 14) 2) (by decide +kernel)
  have a2428 := h.atom 2428 (.add (.n 2878) (.n 2876) (.n 2877)) (by decide +kernel)
  have a2429 := h.atom 2429 (.const (.n 2879) (word 0 0 0)) (by decide +kernel)
  have a2430 := h.atom 2430 (.mul (.n 2880) (.n 2879) (.n 2639)) (by decide +kernel)
  have a2431 := h.atom 2431 (.add (.n 2881) (.n 2878) (.n 2880)) (by decide +kernel)
  have a2432 := h.atom 2432 (.add (.n 2882) (.n 15) (.n 2881)) (by decide +kernel)
  have a2433 := h.atom 2433 (.mul (.n 2883) (.n 2870) (.n 2882)) (by decide +kernel)
  have a2452 := h.atom 2452 (.load (.n 2905) (.n 14) 0) (by decide +kernel)
  have a2453 := h.atom 2453 (.const (.n 2906) (word 2 0 0)) (by decide +kernel)
  have a2454 := h.atom 2454 (.mul (.n 2907) (.n 2905) (.n 2906)) (by decide +kernel)
  have a2457 := h.atom 2457 (.load (.n 2909) (.n 14) 1) (by decide +kernel)
  have a2458 := h.atom 2458 (.mul (.n 2910) (.n 2909) (.n 2908)) (by decide +kernel)
  have a2459 := h.atom 2459 (.add (.n 2911) (.n 2907) (.n 2910)) (by decide +kernel)
  have a2460 := h.atom 2460 (.load (.n 2912) (.n 14) 2) (by decide +kernel)
  have a2461 := h.atom 2461 (.add (.n 2913) (.n 2911) (.n 2912)) (by decide +kernel)
  have a2473 := h.atom 2473 (.load (.n 2924) (.n 14) 3) (by decide +kernel)
  have a2474 := h.atom 2474 (.mul (.n 2925) (.n 2924) (.n 2914)) (by decide +kernel)
  have a2475 := h.atom 2475 (.add (.n 2926) (.n 2913) (.n 2925)) (by decide +kernel)
  have a2487 := h.atom 2487 (.load (.n 2937) (.n 14) 4) (by decide +kernel)
  have a2488 := h.atom 2488 (.mul (.n 2938) (.n 2937) (.n 2927)) (by decide +kernel)
  have a2489 := h.atom 2489 (.add (.n 2939) (.n 2926) (.n 2938)) (by decide +kernel)
  have a2501 := h.atom 2501 (.load (.n 2950) (.n 14) 5) (by decide +kernel)
  have a2502 := h.atom 2502 (.mul (.n 2951) (.n 2950) (.n 2940)) (by decide +kernel)
  have a2503 := h.atom 2503 (.add (.n 2952) (.n 2939) (.n 2951)) (by decide +kernel)
  have a2504 := h.atom 2504 (.const (.n 2953) (word 0 0 0)) (by decide +kernel)
  have a2505 := h.atom 2505 (.mul (.n 2954) (.n 2953) (.n 2639)) (by decide +kernel)
  have a2506 := h.atom 2506 (.add (.n 2955) (.n 2952) (.n 2954)) (by decide +kernel)
  have a2507 := h.atom 2507 (.add (.n 2956) (.n 15) (.n 2955)) (by decide +kernel)
  have a2508 := h.atom 2508 (.mul (.n 2957) (.n 2900) (.n 2956)) (by decide +kernel)
  have a2509 := h.atom 2509 (.add (.n 2958) (.n 2883) (.n 2957)) (by decide +kernel)
  have a2528 := h.atom 2528 (.load (.n 2980) (.n 14) 0) (by decide +kernel)
  have a2529 := h.atom 2529 (.const (.n 2981) (word 4 0 0)) (by decide +kernel)
  have a2530 := h.atom 2530 (.mul (.n 2982) (.n 2980) (.n 2981)) (by decide +kernel)
  have a2533 := h.atom 2533 (.load (.n 2984) (.n 14) 1) (by decide +kernel)
  have a2534 := h.atom 2534 (.mul (.n 2985) (.n 2984) (.n 2983)) (by decide +kernel)
  have a2535 := h.atom 2535 (.add (.n 2986) (.n 2982) (.n 2985)) (by decide +kernel)
  have a2536 := h.atom 2536 (.load (.n 2987) (.n 14) 2) (by decide +kernel)
  have a2537 := h.atom 2537 (.add (.n 2988) (.n 2986) (.n 2987)) (by decide +kernel)
  have a2538 := h.atom 2538 (.load (.n 2989) (.n 14) 3) (by decide +kernel)
  have a2539 := h.atom 2539 (.const (.n 2990) (word 0 0 0)) (by decide +kernel)
  have a2540 := h.atom 2540 (.mul (.n 2991) (.n 2989) (.n 2990)) (by decide +kernel)
  have a2541 := h.atom 2541 (.add (.n 2992) (.n 2988) (.n 2991)) (by decide +kernel)
  have a2542 := h.atom 2542 (.load (.n 2993) (.n 14) 4) (by decide +kernel)
  have a2543 := h.atom 2543 (.const (.n 2994) (word 0 0 0)) (by decide +kernel)
  have a2544 := h.atom 2544 (.mul (.n 2995) (.n 2993) (.n 2994)) (by decide +kernel)
  have a2545 := h.atom 2545 (.add (.n 2996) (.n 2992) (.n 2995)) (by decide +kernel)
  have a2546 := h.atom 2546 (.load (.n 2997) (.n 14) 5) (by decide +kernel)
  have a2547 := h.atom 2547 (.const (.n 2998) (word 0 0 0)) (by decide +kernel)
  have a2548 := h.atom 2548 (.mul (.n 2999) (.n 2997) (.n 2998)) (by decide +kernel)
  have a2549 := h.atom 2549 (.add (.n 3000) (.n 2996) (.n 2999)) (by decide +kernel)
  have a2550 := h.atom 2550 (.load (.n 3001) (.n 14) 6) (by decide +kernel)
  have a2551 := h.atom 2551 (.const (.n 3002) (word 0 0 0)) (by decide +kernel)
  have a2552 := h.atom 2552 (.mul (.n 3003) (.n 3001) (.n 3002)) (by decide +kernel)
  have a2553 := h.atom 2553 (.add (.n 3004) (.n 3000) (.n 3003)) (by decide +kernel)
  have a2554 := h.atom 2554 (.load (.n 3005) (.n 14) 7) (by decide +kernel)
  have a2555 := h.atom 2555 (.const (.n 3006) (word 0 0 0)) (by decide +kernel)
  have a2556 := h.atom 2556 (.mul (.n 3007) (.n 3005) (.n 3006)) (by decide +kernel)
  have a2557 := h.atom 2557 (.add (.n 3008) (.n 3004) (.n 3007)) (by decide +kernel)
  have a2558 := h.atom 2558 (.load (.n 3009) (.n 14) 8) (by decide +kernel)
  have a2559 := h.atom 2559 (.const (.n 3010) (word 0 0 0)) (by decide +kernel)
  have a2560 := h.atom 2560 (.mul (.n 3011) (.n 3009) (.n 3010)) (by decide +kernel)
  have a2561 := h.atom 2561 (.add (.n 3012) (.n 3008) (.n 3011)) (by decide +kernel)
  have a2562 := h.atom 2562 (.load (.n 3013) (.n 14) 9) (by decide +kernel)
  have a2563 := h.atom 2563 (.const (.n 3014) (word 0 0 0)) (by decide +kernel)
  have a2564 := h.atom 2564 (.mul (.n 3015) (.n 3013) (.n 3014)) (by decide +kernel)
  have a2565 := h.atom 2565 (.add (.n 3016) (.n 3012) (.n 3015)) (by decide +kernel)
  have a2566 := h.atom 2566 (.load (.n 3017) (.n 14) 10) (by decide +kernel)
  have a2567 := h.atom 2567 (.const (.n 3018) (word 0 0 0)) (by decide +kernel)
  have a2568 := h.atom 2568 (.mul (.n 3019) (.n 3017) (.n 3018)) (by decide +kernel)
  have a2569 := h.atom 2569 (.add (.n 3020) (.n 3016) (.n 3019)) (by decide +kernel)
  have a2570 := h.atom 2570 (.load (.n 3021) (.n 14) 11) (by decide +kernel)
  have a2571 := h.atom 2571 (.const (.n 3022) (word 0 0 0)) (by decide +kernel)
  have a2572 := h.atom 2572 (.mul (.n 3023) (.n 3021) (.n 3022)) (by decide +kernel)
  have a2573 := h.atom 2573 (.add (.n 3024) (.n 3020) (.n 3023)) (by decide +kernel)
  have a2574 := h.atom 2574 (.load (.n 3025) (.n 14) 12) (by decide +kernel)
  have a2575 := h.atom 2575 (.const (.n 3026) (word 0 0 0)) (by decide +kernel)
  have a2576 := h.atom 2576 (.mul (.n 3027) (.n 3025) (.n 3026)) (by decide +kernel)
  have a2577 := h.atom 2577 (.add (.n 3028) (.n 3024) (.n 3027)) (by decide +kernel)
  have a2578 := h.atom 2578 (.load (.n 3029) (.n 14) 13) (by decide +kernel)
  have a2579 := h.atom 2579 (.const (.n 3030) (word 0 0 0)) (by decide +kernel)
  have a2580 := h.atom 2580 (.mul (.n 3031) (.n 3029) (.n 3030)) (by decide +kernel)
  have a2581 := h.atom 2581 (.add (.n 3032) (.n 3028) (.n 3031)) (by decide +kernel)
  have a2582 := h.atom 2582 (.add (.n 3033) (.n 3032) (.n 2639)) (by decide +kernel)
  have a2583 := h.atom 2583 (.add (.n 3034) (.n 15) (.n 3033)) (by decide +kernel)
  have a2584 := h.atom 2584 (.mul (.n 3035) (.n 2975) (.n 3034)) (by decide +kernel)
  have a2585 := h.atom 2585 (.add (.n 3036) (.n 2958) (.n 3035)) (by decide +kernel)
  have e2424 := tb_loadHolds_unique a2424 (hw 0 (by norm_num))
  have e2425 := tb_loadHolds_unique a2425 (hw 1 (by norm_num))
  have e2427 := tb_loadHolds_unique a2427 (hw 2 (by norm_num))
  have e2452 := tb_loadHolds_unique a2452 (hw 0 (by norm_num))
  have e2457 := tb_loadHolds_unique a2457 (hw 1 (by norm_num))
  have e2460 := tb_loadHolds_unique a2460 (hw 2 (by norm_num))
  have e2473 := tb_loadHolds_unique a2473 (hw 3 (by norm_num))
  have e2487 := tb_loadHolds_unique a2487 (hw 4 (by norm_num))
  have e2501 := tb_loadHolds_unique a2501 (hw 5 (by norm_num))
  have e2528 := tb_loadHolds_unique a2528 (hw 0 (by norm_num))
  have e2533 := tb_loadHolds_unique a2533 (hw 1 (by norm_num))
  have e2536 := tb_loadHolds_unique a2536 (hw 2 (by norm_num))
  have e2538 := tb_loadHolds_unique a2538 (hw 3 (by norm_num))
  have e2542 := tb_loadHolds_unique a2542 (hw 4 (by norm_num))
  have e2546 := tb_loadHolds_unique a2546 (hw 5 (by norm_num))
  have e2550 := tb_loadHolds_unique a2550 (hw 6 (by norm_num))
  have e2554 := tb_loadHolds_unique a2554 (hw 7 (by norm_num))
  have e2558 := tb_loadHolds_unique a2558 (hw 8 (by norm_num))
  have e2562 := tb_loadHolds_unique a2562 (hw 9 (by norm_num))
  have e2566 := tb_loadHolds_unique a2566 (hw 10 (by norm_num))
  have e2570 := tb_loadHolds_unique a2570 (hw 11 (by norm_num))
  have e2574 := tb_loadHolds_unique a2574 (hw 12 (by norm_num))
  have e2578 := tb_loadHolds_unique a2578 (hw 13 (by norm_num))
  simp only [Atom.Holds] at a2426 a2428 a2429 a2430 a2431 a2432 a2433 a2453 a2454 a2458
  simp only [Atom.Holds] at a2459 a2461 a2474 a2475 a2488 a2489 a2502 a2503 a2504 a2505
  simp only [Atom.Holds] at a2506 a2507 a2508 a2509 a2529 a2530 a2534 a2535 a2537 a2539
  simp only [Atom.Holds] at a2540 a2541 a2543 a2544 a2545 a2547 a2548 a2549 a2551 a2552
  simp only [Atom.Holds] at a2553 a2555 a2556 a2557 a2559 a2560 a2561 a2563 a2564 a2565
  simp only [Atom.Holds] at a2567 a2568 a2569 a2571 a2572 a2573 a2575 a2576 a2577 a2579
  simp only [Atom.Holds] at a2580 a2581 a2582 a2583 a2584 a2585
  simp only [e2424, e2425, a2426, e2427, a2428, a2429, a2430, a2431, a2432, a2433, e2452, a2453, a2454,
    e2457, a2458, a2459, e2460, a2461, e2473, a2474, a2475, e2487, a2488, a2489, e2501, a2502,
    a2503, a2504, a2505, a2506, a2507, a2508, a2509, e2528, a2529, a2530, e2533, a2534, a2535,
    e2536, a2537, e2538, a2539, a2540, a2541, e2542, a2543, a2544, a2545, e2546, a2547, a2548,
    a2549, e2550, a2551, a2552, a2553, e2554, a2555, a2556, a2557, e2558, a2559, a2560, a2561,
    e2562, a2563, a2564, a2565, e2566, a2567, a2568, a2569, e2570, a2571, a2572, a2573, e2574,
    a2575, a2576, a2577, e2578, a2579, a2580, a2581, a2582, a2583, a2584, a2585]
  rw [tb_word_zero, tb_word_gen, show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The push side's total.** -/
theorem vtP_push_total {rd : Reader} {σ : Val} (h : VtP rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i)) :
    σ (.n 4411) = σ (.n 3036) + vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W
      (σ (.n 2853)) vtPushPadData + (1 + σ (.n 3984)) + σ (.n 27) := by
  have a3484 := h.atom 3484 (.load (.n 3986) (.n 14) 0) (by decide +kernel)
  have a3485 := h.atom 3485 (.add (.n 3987) (.n 2853) (.n 3986)) (by decide +kernel)
  have a3486 := h.atom 3486 (.mul (.n 3988) (.n 3051) (.n 3987)) (by decide +kernel)
  have a3487 := h.atom 3487 (.load (.n 3989) (.n 14) 0) (by decide +kernel)
  have a3488 := h.atom 3488 (.const (.n 3990) (word 4 0 0)) (by decide +kernel)
  have a3489 := h.atom 3489 (.mul (.n 3991) (.n 3989) (.n 3990)) (by decide +kernel)
  have a3490 := h.atom 3490 (.add (.n 3992) (.n 2853) (.n 3991)) (by decide +kernel)
  have a3491 := h.atom 3491 (.load (.n 3993) (.n 14) 3) (by decide +kernel)
  have a3492 := h.atom 3492 (.add (.n 3994) (.n 3992) (.n 3993)) (by decide +kernel)
  have a3493 := h.atom 3493 (.mul (.n 3995) (.n 3066) (.n 3994)) (by decide +kernel)
  have a3494 := h.atom 3494 (.add (.n 3996) (.n 3988) (.n 3995)) (by decide +kernel)
  have a3495 := h.atom 3495 (.load (.n 3997) (.n 14) 0) (by decide +kernel)
  have a3496 := h.atom 3496 (.const (.n 3998) (word 2 0 0)) (by decide +kernel)
  have a3497 := h.atom 3497 (.mul (.n 3999) (.n 3997) (.n 3998)) (by decide +kernel)
  have a3498 := h.atom 3498 (.add (.n 4000) (.n 2853) (.n 3999)) (by decide +kernel)
  have a3499 := h.atom 3499 (.mul (.n 4001) (.n 3081) (.n 4000)) (by decide +kernel)
  have a3500 := h.atom 3500 (.add (.n 4002) (.n 3996) (.n 4001)) (by decide +kernel)
  have a3501 := h.atom 3501 (.load (.n 4003) (.n 14) 0) (by decide +kernel)
  have a3502 := h.atom 3502 (.const (.n 4004) (word 2 0 0)) (by decide +kernel)
  have a3503 := h.atom 3503 (.mul (.n 4005) (.n 4003) (.n 4004)) (by decide +kernel)
  have a3504 := h.atom 3504 (.add (.n 4006) (.n 2853) (.n 4005)) (by decide +kernel)
  have a3505 := h.atom 3505 (.mul (.n 4007) (.n 3096) (.n 4006)) (by decide +kernel)
  have a3506 := h.atom 3506 (.add (.n 4008) (.n 4002) (.n 4007)) (by decide +kernel)
  have a3507 := h.atom 3507 (.load (.n 4009) (.n 14) 0) (by decide +kernel)
  have a3508 := h.atom 3508 (.const (.n 4010) (word 2 0 0)) (by decide +kernel)
  have a3509 := h.atom 3509 (.mul (.n 4011) (.n 4009) (.n 4010)) (by decide +kernel)
  have a3510 := h.atom 3510 (.add (.n 4012) (.n 2853) (.n 4011)) (by decide +kernel)
  have a3511 := h.atom 3511 (.mul (.n 4013) (.n 3111) (.n 4012)) (by decide +kernel)
  have a3512 := h.atom 3512 (.add (.n 4014) (.n 4008) (.n 4013)) (by decide +kernel)
  have a3513 := h.atom 3513 (.mul (.n 4015) (.n 2646) (.n 4014)) (by decide +kernel)
  have a3514 := h.atom 3514 (.load (.n 4016) (.n 14) 0) (by decide +kernel)
  have a3515 := h.atom 3515 (.add (.n 4017) (.n 2853) (.n 4016)) (by decide +kernel)
  have a3516 := h.atom 3516 (.mul (.n 4018) (.n 3130) (.n 4017)) (by decide +kernel)
  have a3517 := h.atom 3517 (.load (.n 4019) (.n 14) 0) (by decide +kernel)
  have a3518 := h.atom 3518 (.const (.n 4020) (word 4 0 0)) (by decide +kernel)
  have a3519 := h.atom 3519 (.mul (.n 4021) (.n 4019) (.n 4020)) (by decide +kernel)
  have a3520 := h.atom 3520 (.add (.n 4022) (.n 2853) (.n 4021)) (by decide +kernel)
  have a3521 := h.atom 3521 (.load (.n 4023) (.n 14) 3) (by decide +kernel)
  have a3522 := h.atom 3522 (.const (.n 4024) (word 2 0 0)) (by decide +kernel)
  have a3523 := h.atom 3523 (.mul (.n 4025) (.n 4023) (.n 4024)) (by decide +kernel)
  have a3524 := h.atom 3524 (.add (.n 4026) (.n 4022) (.n 4025)) (by decide +kernel)
  have a3525 := h.atom 3525 (.mul (.n 4027) (.n 3149) (.n 4026)) (by decide +kernel)
  have a3526 := h.atom 3526 (.add (.n 4028) (.n 4018) (.n 4027)) (by decide +kernel)
  have a3527 := h.atom 3527 (.load (.n 4029) (.n 14) 0) (by decide +kernel)
  have a3528 := h.atom 3528 (.const (.n 4030) (word 2 0 0)) (by decide +kernel)
  have a3529 := h.atom 3529 (.mul (.n 4031) (.n 4029) (.n 4030)) (by decide +kernel)
  have a3530 := h.atom 3530 (.add (.n 4032) (.n 2853) (.n 4031)) (by decide +kernel)
  have a3531 := h.atom 3531 (.mul (.n 4033) (.n 3168) (.n 4032)) (by decide +kernel)
  have a3532 := h.atom 3532 (.add (.n 4034) (.n 4028) (.n 4033)) (by decide +kernel)
  have a3533 := h.atom 3533 (.load (.n 4035) (.n 14) 0) (by decide +kernel)
  have a3534 := h.atom 3534 (.const (.n 4036) (word 2 0 0)) (by decide +kernel)
  have a3535 := h.atom 3535 (.mul (.n 4037) (.n 4035) (.n 4036)) (by decide +kernel)
  have a3536 := h.atom 3536 (.add (.n 4038) (.n 2853) (.n 4037)) (by decide +kernel)
  have a3537 := h.atom 3537 (.mul (.n 4039) (.n 3187) (.n 4038)) (by decide +kernel)
  have a3538 := h.atom 3538 (.add (.n 4040) (.n 4034) (.n 4039)) (by decide +kernel)
  have a3539 := h.atom 3539 (.load (.n 4041) (.n 14) 0) (by decide +kernel)
  have a3540 := h.atom 3540 (.const (.n 4042) (word 2 0 0)) (by decide +kernel)
  have a3541 := h.atom 3541 (.mul (.n 4043) (.n 4041) (.n 4042)) (by decide +kernel)
  have a3542 := h.atom 3542 (.add (.n 4044) (.n 2853) (.n 4043)) (by decide +kernel)
  have a3543 := h.atom 3543 (.mul (.n 4045) (.n 3206) (.n 4044)) (by decide +kernel)
  have a3544 := h.atom 3544 (.add (.n 4046) (.n 4040) (.n 4045)) (by decide +kernel)
  have a3545 := h.atom 3545 (.mul (.n 4047) (.n 2660) (.n 4046)) (by decide +kernel)
  have a3546 := h.atom 3546 (.add (.n 4048) (.n 4015) (.n 4047)) (by decide +kernel)
  have a3547 := h.atom 3547 (.load (.n 4049) (.n 14) 0) (by decide +kernel)
  have a3548 := h.atom 3548 (.add (.n 4050) (.n 2853) (.n 4049)) (by decide +kernel)
  have a3549 := h.atom 3549 (.mul (.n 4051) (.n 3225) (.n 4050)) (by decide +kernel)
  have a3550 := h.atom 3550 (.load (.n 4052) (.n 14) 0) (by decide +kernel)
  have a3551 := h.atom 3551 (.const (.n 4053) (word 4 0 0)) (by decide +kernel)
  have a3552 := h.atom 3552 (.mul (.n 4054) (.n 4052) (.n 4053)) (by decide +kernel)
  have a3553 := h.atom 3553 (.add (.n 4055) (.n 2853) (.n 4054)) (by decide +kernel)
  have a3554 := h.atom 3554 (.load (.n 4056) (.n 14) 3) (by decide +kernel)
  have a3555 := h.atom 3555 (.const (.n 4057) (word 4 0 0)) (by decide +kernel)
  have a3556 := h.atom 3556 (.mul (.n 4058) (.n 4056) (.n 4057)) (by decide +kernel)
  have a3557 := h.atom 3557 (.add (.n 4059) (.n 4055) (.n 4058)) (by decide +kernel)
  have a3558 := h.atom 3558 (.mul (.n 4060) (.n 3244) (.n 4059)) (by decide +kernel)
  have a3559 := h.atom 3559 (.add (.n 4061) (.n 4051) (.n 4060)) (by decide +kernel)
  have a3560 := h.atom 3560 (.load (.n 4062) (.n 14) 0) (by decide +kernel)
  have a3561 := h.atom 3561 (.const (.n 4063) (word 2 0 0)) (by decide +kernel)
  have a3562 := h.atom 3562 (.mul (.n 4064) (.n 4062) (.n 4063)) (by decide +kernel)
  have a3563 := h.atom 3563 (.add (.n 4065) (.n 2853) (.n 4064)) (by decide +kernel)
  have a3564 := h.atom 3564 (.mul (.n 4066) (.n 3263) (.n 4065)) (by decide +kernel)
  have a3565 := h.atom 3565 (.add (.n 4067) (.n 4061) (.n 4066)) (by decide +kernel)
  have a3566 := h.atom 3566 (.mul (.n 4068) (.n 2674) (.n 4067)) (by decide +kernel)
  have a3567 := h.atom 3567 (.add (.n 4069) (.n 4048) (.n 4068)) (by decide +kernel)
  have a3568 := h.atom 3568 (.load (.n 4070) (.n 14) 0) (by decide +kernel)
  have a3569 := h.atom 3569 (.add (.n 4071) (.n 2853) (.n 4070)) (by decide +kernel)
  have a3570 := h.atom 3570 (.mul (.n 4072) (.n 3282) (.n 4071)) (by decide +kernel)
  have a3571 := h.atom 3571 (.load (.n 4073) (.n 14) 0) (by decide +kernel)
  have a3572 := h.atom 3572 (.const (.n 4074) (word 4 0 0)) (by decide +kernel)
  have a3573 := h.atom 3573 (.mul (.n 4075) (.n 4073) (.n 4074)) (by decide +kernel)
  have a3574 := h.atom 3574 (.add (.n 4076) (.n 2853) (.n 4075)) (by decide +kernel)
  have a3575 := h.atom 3575 (.load (.n 4077) (.n 14) 3) (by decide +kernel)
  have a3576 := h.atom 3576 (.const (.n 4078) (word 8 0 0)) (by decide +kernel)
  have a3577 := h.atom 3577 (.mul (.n 4079) (.n 4077) (.n 4078)) (by decide +kernel)
  have a3578 := h.atom 3578 (.add (.n 4080) (.n 4076) (.n 4079)) (by decide +kernel)
  have a3579 := h.atom 3579 (.mul (.n 4081) (.n 3301) (.n 4080)) (by decide +kernel)
  have a3580 := h.atom 3580 (.add (.n 4082) (.n 4072) (.n 4081)) (by decide +kernel)
  have a3581 := h.atom 3581 (.load (.n 4083) (.n 14) 0) (by decide +kernel)
  have a3582 := h.atom 3582 (.const (.n 4084) (word 2 0 0)) (by decide +kernel)
  have a3583 := h.atom 3583 (.mul (.n 4085) (.n 4083) (.n 4084)) (by decide +kernel)
  have a3584 := h.atom 3584 (.add (.n 4086) (.n 2853) (.n 4085)) (by decide +kernel)
  have a3585 := h.atom 3585 (.mul (.n 4087) (.n 3320) (.n 4086)) (by decide +kernel)
  have a3586 := h.atom 3586 (.add (.n 4088) (.n 4082) (.n 4087)) (by decide +kernel)
  have a3587 := h.atom 3587 (.load (.n 4089) (.n 14) 0) (by decide +kernel)
  have a3588 := h.atom 3588 (.const (.n 4090) (word 2 0 0)) (by decide +kernel)
  have a3589 := h.atom 3589 (.mul (.n 4091) (.n 4089) (.n 4090)) (by decide +kernel)
  have a3590 := h.atom 3590 (.add (.n 4092) (.n 2853) (.n 4091)) (by decide +kernel)
  have a3591 := h.atom 3591 (.mul (.n 4093) (.n 3339) (.n 4092)) (by decide +kernel)
  have a3592 := h.atom 3592 (.add (.n 4094) (.n 4088) (.n 4093)) (by decide +kernel)
  have a3593 := h.atom 3593 (.load (.n 4095) (.n 14) 0) (by decide +kernel)
  have a3594 := h.atom 3594 (.const (.n 4096) (word 2 0 0)) (by decide +kernel)
  have a3595 := h.atom 3595 (.mul (.n 4097) (.n 4095) (.n 4096)) (by decide +kernel)
  have a3596 := h.atom 3596 (.add (.n 4098) (.n 2853) (.n 4097)) (by decide +kernel)
  have a3597 := h.atom 3597 (.mul (.n 4099) (.n 3358) (.n 4098)) (by decide +kernel)
  have a3598 := h.atom 3598 (.add (.n 4100) (.n 4094) (.n 4099)) (by decide +kernel)
  have a3599 := h.atom 3599 (.mul (.n 4101) (.n 2688) (.n 4100)) (by decide +kernel)
  have a3600 := h.atom 3600 (.add (.n 4102) (.n 4069) (.n 4101)) (by decide +kernel)
  have a3601 := h.atom 3601 (.load (.n 4103) (.n 14) 0) (by decide +kernel)
  have a3602 := h.atom 3602 (.add (.n 4104) (.n 2853) (.n 4103)) (by decide +kernel)
  have a3603 := h.atom 3603 (.mul (.n 4105) (.n 3377) (.n 4104)) (by decide +kernel)
  have a3604 := h.atom 3604 (.load (.n 4106) (.n 14) 0) (by decide +kernel)
  have a3605 := h.atom 3605 (.const (.n 4107) (word 4 0 0)) (by decide +kernel)
  have a3606 := h.atom 3606 (.mul (.n 4108) (.n 4106) (.n 4107)) (by decide +kernel)
  have a3607 := h.atom 3607 (.add (.n 4109) (.n 2853) (.n 4108)) (by decide +kernel)
  have a3608 := h.atom 3608 (.load (.n 4110) (.n 14) 3) (by decide +kernel)
  have a3609 := h.atom 3609 (.const (.n 4111) (word 16 0 0)) (by decide +kernel)
  have a3610 := h.atom 3610 (.mul (.n 4112) (.n 4110) (.n 4111)) (by decide +kernel)
  have a3611 := h.atom 3611 (.add (.n 4113) (.n 4109) (.n 4112)) (by decide +kernel)
  have a3612 := h.atom 3612 (.mul (.n 4114) (.n 3396) (.n 4113)) (by decide +kernel)
  have a3613 := h.atom 3613 (.add (.n 4115) (.n 4105) (.n 4114)) (by decide +kernel)
  have a3614 := h.atom 3614 (.load (.n 4116) (.n 14) 0) (by decide +kernel)
  have a3615 := h.atom 3615 (.const (.n 4117) (word 2 0 0)) (by decide +kernel)
  have a3616 := h.atom 3616 (.mul (.n 4118) (.n 4116) (.n 4117)) (by decide +kernel)
  have a3617 := h.atom 3617 (.add (.n 4119) (.n 2853) (.n 4118)) (by decide +kernel)
  have a3618 := h.atom 3618 (.mul (.n 4120) (.n 3415) (.n 4119)) (by decide +kernel)
  have a3619 := h.atom 3619 (.add (.n 4121) (.n 4115) (.n 4120)) (by decide +kernel)
  have a3620 := h.atom 3620 (.load (.n 4122) (.n 14) 0) (by decide +kernel)
  have a3621 := h.atom 3621 (.const (.n 4123) (word 2 0 0)) (by decide +kernel)
  have a3622 := h.atom 3622 (.mul (.n 4124) (.n 4122) (.n 4123)) (by decide +kernel)
  have a3623 := h.atom 3623 (.add (.n 4125) (.n 2853) (.n 4124)) (by decide +kernel)
  have a3624 := h.atom 3624 (.mul (.n 4126) (.n 3434) (.n 4125)) (by decide +kernel)
  have a3625 := h.atom 3625 (.add (.n 4127) (.n 4121) (.n 4126)) (by decide +kernel)
  have a3626 := h.atom 3626 (.load (.n 4128) (.n 14) 0) (by decide +kernel)
  have a3627 := h.atom 3627 (.const (.n 4129) (word 2 0 0)) (by decide +kernel)
  have a3628 := h.atom 3628 (.mul (.n 4130) (.n 4128) (.n 4129)) (by decide +kernel)
  have a3629 := h.atom 3629 (.add (.n 4131) (.n 2853) (.n 4130)) (by decide +kernel)
  have a3630 := h.atom 3630 (.mul (.n 4132) (.n 3453) (.n 4131)) (by decide +kernel)
  have a3631 := h.atom 3631 (.add (.n 4133) (.n 4127) (.n 4132)) (by decide +kernel)
  have a3632 := h.atom 3632 (.mul (.n 4134) (.n 2702) (.n 4133)) (by decide +kernel)
  have a3633 := h.atom 3633 (.add (.n 4135) (.n 4102) (.n 4134)) (by decide +kernel)
  have a3634 := h.atom 3634 (.load (.n 4136) (.n 14) 0) (by decide +kernel)
  have a3635 := h.atom 3635 (.add (.n 4137) (.n 2853) (.n 4136)) (by decide +kernel)
  have a3636 := h.atom 3636 (.mul (.n 4138) (.n 3472) (.n 4137)) (by decide +kernel)
  have a3637 := h.atom 3637 (.load (.n 4139) (.n 14) 0) (by decide +kernel)
  have a3638 := h.atom 3638 (.const (.n 4140) (word 4 0 0)) (by decide +kernel)
  have a3639 := h.atom 3639 (.mul (.n 4141) (.n 4139) (.n 4140)) (by decide +kernel)
  have a3640 := h.atom 3640 (.add (.n 4142) (.n 2853) (.n 4141)) (by decide +kernel)
  have a3641 := h.atom 3641 (.load (.n 4143) (.n 14) 3) (by decide +kernel)
  have a3642 := h.atom 3642 (.const (.n 4144) (word 32 0 0)) (by decide +kernel)
  have a3643 := h.atom 3643 (.mul (.n 4145) (.n 4143) (.n 4144)) (by decide +kernel)
  have a3644 := h.atom 3644 (.add (.n 4146) (.n 4142) (.n 4145)) (by decide +kernel)
  have a3645 := h.atom 3645 (.mul (.n 4147) (.n 3491) (.n 4146)) (by decide +kernel)
  have a3646 := h.atom 3646 (.add (.n 4148) (.n 4138) (.n 4147)) (by decide +kernel)
  have a3647 := h.atom 3647 (.load (.n 4149) (.n 14) 0) (by decide +kernel)
  have a3648 := h.atom 3648 (.const (.n 4150) (word 2 0 0)) (by decide +kernel)
  have a3649 := h.atom 3649 (.mul (.n 4151) (.n 4149) (.n 4150)) (by decide +kernel)
  have a3650 := h.atom 3650 (.add (.n 4152) (.n 2853) (.n 4151)) (by decide +kernel)
  have a3651 := h.atom 3651 (.mul (.n 4153) (.n 3510) (.n 4152)) (by decide +kernel)
  have a3652 := h.atom 3652 (.add (.n 4154) (.n 4148) (.n 4153)) (by decide +kernel)
  have a3653 := h.atom 3653 (.load (.n 4155) (.n 14) 0) (by decide +kernel)
  have a3654 := h.atom 3654 (.const (.n 4156) (word 2 0 0)) (by decide +kernel)
  have a3655 := h.atom 3655 (.mul (.n 4157) (.n 4155) (.n 4156)) (by decide +kernel)
  have a3656 := h.atom 3656 (.add (.n 4158) (.n 2853) (.n 4157)) (by decide +kernel)
  have a3657 := h.atom 3657 (.mul (.n 4159) (.n 3529) (.n 4158)) (by decide +kernel)
  have a3658 := h.atom 3658 (.add (.n 4160) (.n 4154) (.n 4159)) (by decide +kernel)
  have a3659 := h.atom 3659 (.load (.n 4161) (.n 14) 0) (by decide +kernel)
  have a3660 := h.atom 3660 (.const (.n 4162) (word 2 0 0)) (by decide +kernel)
  have a3661 := h.atom 3661 (.mul (.n 4163) (.n 4161) (.n 4162)) (by decide +kernel)
  have a3662 := h.atom 3662 (.add (.n 4164) (.n 2853) (.n 4163)) (by decide +kernel)
  have a3663 := h.atom 3663 (.mul (.n 4165) (.n 3548) (.n 4164)) (by decide +kernel)
  have a3664 := h.atom 3664 (.add (.n 4166) (.n 4160) (.n 4165)) (by decide +kernel)
  have a3665 := h.atom 3665 (.load (.n 4167) (.n 14) 0) (by decide +kernel)
  have a3666 := h.atom 3666 (.const (.n 4168) (word 2 0 0)) (by decide +kernel)
  have a3667 := h.atom 3667 (.mul (.n 4169) (.n 4167) (.n 4168)) (by decide +kernel)
  have a3668 := h.atom 3668 (.add (.n 4170) (.n 2853) (.n 4169)) (by decide +kernel)
  have a3669 := h.atom 3669 (.mul (.n 4171) (.n 3567) (.n 4170)) (by decide +kernel)
  have a3670 := h.atom 3670 (.add (.n 4172) (.n 4166) (.n 4171)) (by decide +kernel)
  have a3671 := h.atom 3671 (.load (.n 4173) (.n 14) 0) (by decide +kernel)
  have a3672 := h.atom 3672 (.const (.n 4174) (word 2 0 0)) (by decide +kernel)
  have a3673 := h.atom 3673 (.mul (.n 4175) (.n 4173) (.n 4174)) (by decide +kernel)
  have a3674 := h.atom 3674 (.add (.n 4176) (.n 2853) (.n 4175)) (by decide +kernel)
  have a3675 := h.atom 3675 (.mul (.n 4177) (.n 3586) (.n 4176)) (by decide +kernel)
  have a3676 := h.atom 3676 (.add (.n 4178) (.n 4172) (.n 4177)) (by decide +kernel)
  have a3677 := h.atom 3677 (.load (.n 4179) (.n 14) 0) (by decide +kernel)
  have a3678 := h.atom 3678 (.const (.n 4180) (word 2 0 0)) (by decide +kernel)
  have a3679 := h.atom 3679 (.mul (.n 4181) (.n 4179) (.n 4180)) (by decide +kernel)
  have a3680 := h.atom 3680 (.add (.n 4182) (.n 2853) (.n 4181)) (by decide +kernel)
  have a3681 := h.atom 3681 (.mul (.n 4183) (.n 3605) (.n 4182)) (by decide +kernel)
  have a3682 := h.atom 3682 (.add (.n 4184) (.n 4178) (.n 4183)) (by decide +kernel)
  have a3683 := h.atom 3683 (.load (.n 4185) (.n 14) 0) (by decide +kernel)
  have a3684 := h.atom 3684 (.const (.n 4186) (word 2 0 0)) (by decide +kernel)
  have a3685 := h.atom 3685 (.mul (.n 4187) (.n 4185) (.n 4186)) (by decide +kernel)
  have a3686 := h.atom 3686 (.add (.n 4188) (.n 2853) (.n 4187)) (by decide +kernel)
  have a3687 := h.atom 3687 (.mul (.n 4189) (.n 3624) (.n 4188)) (by decide +kernel)
  have a3688 := h.atom 3688 (.add (.n 4190) (.n 4184) (.n 4189)) (by decide +kernel)
  have a3689 := h.atom 3689 (.load (.n 4191) (.n 14) 0) (by decide +kernel)
  have a3690 := h.atom 3690 (.const (.n 4192) (word 2 0 0)) (by decide +kernel)
  have a3691 := h.atom 3691 (.mul (.n 4193) (.n 4191) (.n 4192)) (by decide +kernel)
  have a3692 := h.atom 3692 (.add (.n 4194) (.n 2853) (.n 4193)) (by decide +kernel)
  have a3693 := h.atom 3693 (.mul (.n 4195) (.n 3643) (.n 4194)) (by decide +kernel)
  have a3694 := h.atom 3694 (.add (.n 4196) (.n 4190) (.n 4195)) (by decide +kernel)
  have a3695 := h.atom 3695 (.load (.n 4197) (.n 14) 0) (by decide +kernel)
  have a3696 := h.atom 3696 (.const (.n 4198) (word 2 0 0)) (by decide +kernel)
  have a3697 := h.atom 3697 (.mul (.n 4199) (.n 4197) (.n 4198)) (by decide +kernel)
  have a3698 := h.atom 3698 (.add (.n 4200) (.n 2853) (.n 4199)) (by decide +kernel)
  have a3699 := h.atom 3699 (.mul (.n 4201) (.n 3662) (.n 4200)) (by decide +kernel)
  have a3700 := h.atom 3700 (.add (.n 4202) (.n 4196) (.n 4201)) (by decide +kernel)
  have a3701 := h.atom 3701 (.load (.n 4203) (.n 14) 0) (by decide +kernel)
  have a3702 := h.atom 3702 (.const (.n 4204) (word 2 0 0)) (by decide +kernel)
  have a3703 := h.atom 3703 (.mul (.n 4205) (.n 4203) (.n 4204)) (by decide +kernel)
  have a3704 := h.atom 3704 (.add (.n 4206) (.n 2853) (.n 4205)) (by decide +kernel)
  have a3705 := h.atom 3705 (.mul (.n 4207) (.n 3681) (.n 4206)) (by decide +kernel)
  have a3706 := h.atom 3706 (.add (.n 4208) (.n 4202) (.n 4207)) (by decide +kernel)
  have a3707 := h.atom 3707 (.load (.n 4209) (.n 14) 0) (by decide +kernel)
  have a3708 := h.atom 3708 (.const (.n 4210) (word 2 0 0)) (by decide +kernel)
  have a3709 := h.atom 3709 (.mul (.n 4211) (.n 4209) (.n 4210)) (by decide +kernel)
  have a3710 := h.atom 3710 (.add (.n 4212) (.n 2853) (.n 4211)) (by decide +kernel)
  have a3711 := h.atom 3711 (.mul (.n 4213) (.n 3700) (.n 4212)) (by decide +kernel)
  have a3712 := h.atom 3712 (.add (.n 4214) (.n 4208) (.n 4213)) (by decide +kernel)
  have a3713 := h.atom 3713 (.load (.n 4215) (.n 14) 0) (by decide +kernel)
  have a3714 := h.atom 3714 (.const (.n 4216) (word 2 0 0)) (by decide +kernel)
  have a3715 := h.atom 3715 (.mul (.n 4217) (.n 4215) (.n 4216)) (by decide +kernel)
  have a3716 := h.atom 3716 (.add (.n 4218) (.n 2853) (.n 4217)) (by decide +kernel)
  have a3717 := h.atom 3717 (.mul (.n 4219) (.n 3719) (.n 4218)) (by decide +kernel)
  have a3718 := h.atom 3718 (.add (.n 4220) (.n 4214) (.n 4219)) (by decide +kernel)
  have a3719 := h.atom 3719 (.load (.n 4221) (.n 14) 0) (by decide +kernel)
  have a3720 := h.atom 3720 (.const (.n 4222) (word 2 0 0)) (by decide +kernel)
  have a3721 := h.atom 3721 (.mul (.n 4223) (.n 4221) (.n 4222)) (by decide +kernel)
  have a3722 := h.atom 3722 (.add (.n 4224) (.n 2853) (.n 4223)) (by decide +kernel)
  have a3723 := h.atom 3723 (.mul (.n 4225) (.n 3738) (.n 4224)) (by decide +kernel)
  have a3724 := h.atom 3724 (.add (.n 4226) (.n 4220) (.n 4225)) (by decide +kernel)
  have a3725 := h.atom 3725 (.load (.n 4227) (.n 14) 0) (by decide +kernel)
  have a3726 := h.atom 3726 (.const (.n 4228) (word 2 0 0)) (by decide +kernel)
  have a3727 := h.atom 3727 (.mul (.n 4229) (.n 4227) (.n 4228)) (by decide +kernel)
  have a3728 := h.atom 3728 (.add (.n 4230) (.n 2853) (.n 4229)) (by decide +kernel)
  have a3729 := h.atom 3729 (.load (.n 4231) (.n 14) 3) (by decide +kernel)
  have a3730 := h.atom 3730 (.const (.n 4232) (word 17376452488221285863 0 0)) (by decide +kernel)
  have a3731 := h.atom 3731 (.mul (.n 4233) (.n 4231) (.n 4232)) (by decide +kernel)
  have a3732 := h.atom 3732 (.add (.n 4234) (.n 4230) (.n 4233)) (by decide +kernel)
  have a3733 := h.atom 3733 (.load (.n 4235) (.n 14) 4) (by decide +kernel)
  have a3734 := h.atom 3734 (.const (.n 4236) (word 9571781953733019530 0 0)) (by decide +kernel)
  have a3735 := h.atom 3735 (.mul (.n 4237) (.n 4235) (.n 4236)) (by decide +kernel)
  have a3736 := h.atom 3736 (.add (.n 4238) (.n 4234) (.n 4237)) (by decide +kernel)
  have a3737 := h.atom 3737 (.mul (.n 4239) (.n 3757) (.n 4238)) (by decide +kernel)
  have a3738 := h.atom 3738 (.add (.n 4240) (.n 4226) (.n 4239)) (by decide +kernel)
  have a3739 := h.atom 3739 (.load (.n 4241) (.n 14) 0) (by decide +kernel)
  have a3740 := h.atom 3740 (.const (.n 4242) (word 2 0 0)) (by decide +kernel)
  have a3741 := h.atom 3741 (.mul (.n 4243) (.n 4241) (.n 4242)) (by decide +kernel)
  have a3742 := h.atom 3742 (.add (.n 4244) (.n 2853) (.n 4243)) (by decide +kernel)
  have a3743 := h.atom 3743 (.load (.n 4245) (.n 14) 3) (by decide +kernel)
  have a3744 := h.atom 3744 (.const (.n 4246) (word 15391093639620504046 0 0)) (by decide +kernel)
  have a3745 := h.atom 3745 (.mul (.n 4247) (.n 4245) (.n 4246)) (by decide +kernel)
  have a3746 := h.atom 3746 (.add (.n 4248) (.n 4244) (.n 4247)) (by decide +kernel)
  have a3747 := h.atom 3747 (.load (.n 4249) (.n 14) 4) (by decide +kernel)
  have a3748 := h.atom 3748 (.const (.n 4250) (word 13624874521033984333 0 0)) (by decide +kernel)
  have a3749 := h.atom 3749 (.mul (.n 4251) (.n 4249) (.n 4250)) (by decide +kernel)
  have a3750 := h.atom 3750 (.add (.n 4252) (.n 4248) (.n 4251)) (by decide +kernel)
  have a3751 := h.atom 3751 (.mul (.n 4253) (.n 3776) (.n 4252)) (by decide +kernel)
  have a3752 := h.atom 3752 (.add (.n 4254) (.n 4240) (.n 4253)) (by decide +kernel)
  have a3753 := h.atom 3753 (.load (.n 4255) (.n 14) 0) (by decide +kernel)
  have a3754 := h.atom 3754 (.const (.n 4256) (word 2 0 0)) (by decide +kernel)
  have a3755 := h.atom 3755 (.mul (.n 4257) (.n 4255) (.n 4256)) (by decide +kernel)
  have a3756 := h.atom 3756 (.add (.n 4258) (.n 2853) (.n 4257)) (by decide +kernel)
  have a3757 := h.atom 3757 (.load (.n 4259) (.n 14) 3) (by decide +kernel)
  have a3758 := h.atom 3758 (.const (.n 4260) (word 10027350355371872343 0 0)) (by decide +kernel)
  have a3759 := h.atom 3759 (.mul (.n 4261) (.n 4259) (.n 4260)) (by decide +kernel)
  have a3760 := h.atom 3760 (.add (.n 4262) (.n 4258) (.n 4261)) (by decide +kernel)
  have a3761 := h.atom 3761 (.load (.n 4263) (.n 14) 4) (by decide +kernel)
  have a3762 := h.atom 3762 (.const (.n 4264) (word 18417369716475457492 0 0)) (by decide +kernel)
  have a3763 := h.atom 3763 (.mul (.n 4265) (.n 4263) (.n 4264)) (by decide +kernel)
  have a3764 := h.atom 3764 (.add (.n 4266) (.n 4262) (.n 4265)) (by decide +kernel)
  have a3765 := h.atom 3765 (.mul (.n 4267) (.n 3795) (.n 4266)) (by decide +kernel)
  have a3766 := h.atom 3766 (.add (.n 4268) (.n 4254) (.n 4267)) (by decide +kernel)
  have a3767 := h.atom 3767 (.load (.n 4269) (.n 14) 0) (by decide +kernel)
  have a3768 := h.atom 3768 (.const (.n 4270) (word 2 0 0)) (by decide +kernel)
  have a3769 := h.atom 3769 (.mul (.n 4271) (.n 4269) (.n 4270)) (by decide +kernel)
  have a3770 := h.atom 3770 (.add (.n 4272) (.n 2853) (.n 4271)) (by decide +kernel)
  have a3771 := h.atom 3771 (.load (.n 4273) (.n 14) 3) (by decide +kernel)
  have a3772 := h.atom 3772 (.const (.n 4274) (word 10448040663659726788 0 0)) (by decide +kernel)
  have a3773 := h.atom 3773 (.mul (.n 4275) (.n 4273) (.n 4274)) (by decide +kernel)
  have a3774 := h.atom 3774 (.add (.n 4276) (.n 4272) (.n 4275)) (by decide +kernel)
  have a3775 := h.atom 3775 (.load (.n 4277) (.n 14) 4) (by decide +kernel)
  have a3776 := h.atom 3776 (.const (.n 4278) (word 10113917136857017974 0 0)) (by decide +kernel)
  have a3777 := h.atom 3777 (.mul (.n 4279) (.n 4277) (.n 4278)) (by decide +kernel)
  have a3778 := h.atom 3778 (.add (.n 4280) (.n 4276) (.n 4279)) (by decide +kernel)
  have a3779 := h.atom 3779 (.mul (.n 4281) (.n 3814) (.n 4280)) (by decide +kernel)
  have a3780 := h.atom 3780 (.add (.n 4282) (.n 4268) (.n 4281)) (by decide +kernel)
  have a3781 := h.atom 3781 (.load (.n 4283) (.n 14) 0) (by decide +kernel)
  have a3782 := h.atom 3782 (.const (.n 4284) (word 2 0 0)) (by decide +kernel)
  have a3783 := h.atom 3783 (.mul (.n 4285) (.n 4283) (.n 4284)) (by decide +kernel)
  have a3784 := h.atom 3784 (.add (.n 4286) (.n 2853) (.n 4285)) (by decide +kernel)
  have a3785 := h.atom 3785 (.load (.n 4287) (.n 14) 3) (by decide +kernel)
  have a3786 := h.atom 3786 (.const (.n 4288) (word 12479658147685402012 0 0)) (by decide +kernel)
  have a3787 := h.atom 3787 (.mul (.n 4289) (.n 4287) (.n 4288)) (by decide +kernel)
  have a3788 := h.atom 3788 (.add (.n 4290) (.n 4286) (.n 4289)) (by decide +kernel)
  have a3789 := h.atom 3789 (.load (.n 4291) (.n 14) 4) (by decide +kernel)
  have a3790 := h.atom 3790 (.const (.n 4292) (word 3500241080921619556 0 0)) (by decide +kernel)
  have a3791 := h.atom 3791 (.mul (.n 4293) (.n 4291) (.n 4292)) (by decide +kernel)
  have a3792 := h.atom 3792 (.add (.n 4294) (.n 4290) (.n 4293)) (by decide +kernel)
  have a3793 := h.atom 3793 (.mul (.n 4295) (.n 3833) (.n 4294)) (by decide +kernel)
  have a3794 := h.atom 3794 (.add (.n 4296) (.n 4282) (.n 4295)) (by decide +kernel)
  have a3795 := h.atom 3795 (.load (.n 4297) (.n 14) 0) (by decide +kernel)
  have a3796 := h.atom 3796 (.const (.n 4298) (word 2 0 0)) (by decide +kernel)
  have a3797 := h.atom 3797 (.mul (.n 4299) (.n 4297) (.n 4298)) (by decide +kernel)
  have a3798 := h.atom 3798 (.add (.n 4300) (.n 2853) (.n 4299)) (by decide +kernel)
  have a3799 := h.atom 3799 (.load (.n 4301) (.n 14) 3) (by decide +kernel)
  have a3800 := h.atom 3800 (.const (.n 4302) (word 16959053435453822517 0 0)) (by decide +kernel)
  have a3801 := h.atom 3801 (.mul (.n 4303) (.n 4301) (.n 4302)) (by decide +kernel)
  have a3802 := h.atom 3802 (.add (.n 4304) (.n 4300) (.n 4303)) (by decide +kernel)
  have a3803 := h.atom 3803 (.load (.n 4305) (.n 14) 4) (by decide +kernel)
  have a3804 := h.atom 3804 (.const (.n 4306) (word 12224711289652453635 0 0)) (by decide +kernel)
  have a3805 := h.atom 3805 (.mul (.n 4307) (.n 4305) (.n 4306)) (by decide +kernel)
  have a3806 := h.atom 3806 (.add (.n 4308) (.n 4304) (.n 4307)) (by decide +kernel)
  have a3807 := h.atom 3807 (.mul (.n 4309) (.n 3852) (.n 4308)) (by decide +kernel)
  have a3808 := h.atom 3808 (.add (.n 4310) (.n 4296) (.n 4309)) (by decide +kernel)
  have a3809 := h.atom 3809 (.load (.n 4311) (.n 14) 0) (by decide +kernel)
  have a3810 := h.atom 3810 (.const (.n 4312) (word 2 0 0)) (by decide +kernel)
  have a3811 := h.atom 3811 (.mul (.n 4313) (.n 4311) (.n 4312)) (by decide +kernel)
  have a3812 := h.atom 3812 (.add (.n 4314) (.n 2853) (.n 4313)) (by decide +kernel)
  have a3813 := h.atom 3813 (.load (.n 4315) (.n 14) 3) (by decide +kernel)
  have a3814 := h.atom 3814 (.const (.n 4316) (word 9342009439668884831 0 0)) (by decide +kernel)
  have a3815 := h.atom 3815 (.mul (.n 4317) (.n 4315) (.n 4316)) (by decide +kernel)
  have a3816 := h.atom 3816 (.add (.n 4318) (.n 4314) (.n 4317)) (by decide +kernel)
  have a3817 := h.atom 3817 (.load (.n 4319) (.n 14) 4) (by decide +kernel)
  have a3818 := h.atom 3818 (.const (.n 4320) (word 4879704952849025062 0 0)) (by decide +kernel)
  have a3819 := h.atom 3819 (.mul (.n 4321) (.n 4319) (.n 4320)) (by decide +kernel)
  have a3820 := h.atom 3820 (.add (.n 4322) (.n 4318) (.n 4321)) (by decide +kernel)
  have a3821 := h.atom 3821 (.mul (.n 4323) (.n 3871) (.n 4322)) (by decide +kernel)
  have a3822 := h.atom 3822 (.add (.n 4324) (.n 4310) (.n 4323)) (by decide +kernel)
  have a3823 := h.atom 3823 (.load (.n 4325) (.n 14) 0) (by decide +kernel)
  have a3824 := h.atom 3824 (.const (.n 4326) (word 2 0 0)) (by decide +kernel)
  have a3825 := h.atom 3825 (.mul (.n 4327) (.n 4325) (.n 4326)) (by decide +kernel)
  have a3826 := h.atom 3826 (.add (.n 4328) (.n 2853) (.n 4327)) (by decide +kernel)
  have a3827 := h.atom 3827 (.load (.n 4329) (.n 14) 3) (by decide +kernel)
  have a3828 := h.atom 3828 (.const (.n 4330) (word 140226327413610143 0 0)) (by decide +kernel)
  have a3829 := h.atom 3829 (.mul (.n 4331) (.n 4329) (.n 4330)) (by decide +kernel)
  have a3830 := h.atom 3830 (.add (.n 4332) (.n 4328) (.n 4331)) (by decide +kernel)
  have a3831 := h.atom 3831 (.load (.n 4333) (.n 14) 4) (by decide +kernel)
  have a3832 := h.atom 3832 (.const (.n 4334) (word 424854978622500449 0 0)) (by decide +kernel)
  have a3833 := h.atom 3833 (.mul (.n 4335) (.n 4333) (.n 4334)) (by decide +kernel)
  have a3834 := h.atom 3834 (.add (.n 4336) (.n 4332) (.n 4335)) (by decide +kernel)
  have a3835 := h.atom 3835 (.mul (.n 4337) (.n 3890) (.n 4336)) (by decide +kernel)
  have a3836 := h.atom 3836 (.add (.n 4338) (.n 4324) (.n 4337)) (by decide +kernel)
  have a3837 := h.atom 3837 (.load (.n 4339) (.n 14) 0) (by decide +kernel)
  have a3838 := h.atom 3838 (.const (.n 4340) (word 2 0 0)) (by decide +kernel)
  have a3839 := h.atom 3839 (.mul (.n 4341) (.n 4339) (.n 4340)) (by decide +kernel)
  have a3840 := h.atom 3840 (.add (.n 4342) (.n 2853) (.n 4341)) (by decide +kernel)
  have a3841 := h.atom 3841 (.load (.n 4343) (.n 14) 3) (by decide +kernel)
  have a3842 := h.atom 3842 (.const (.n 4344) (word 7259519967065370866 0 0)) (by decide +kernel)
  have a3843 := h.atom 3843 (.mul (.n 4345) (.n 4343) (.n 4344)) (by decide +kernel)
  have a3844 := h.atom 3844 (.add (.n 4346) (.n 4342) (.n 4345)) (by decide +kernel)
  have a3845 := h.atom 3845 (.mul (.n 4347) (.n 3909) (.n 4346)) (by decide +kernel)
  have a3846 := h.atom 3846 (.add (.n 4348) (.n 4338) (.n 4347)) (by decide +kernel)
  have a3847 := h.atom 3847 (.load (.n 4349) (.n 14) 0) (by decide +kernel)
  have a3848 := h.atom 3848 (.const (.n 4350) (word 2 0 0)) (by decide +kernel)
  have a3849 := h.atom 3849 (.mul (.n 4351) (.n 4349) (.n 4350)) (by decide +kernel)
  have a3850 := h.atom 3850 (.add (.n 4352) (.n 2853) (.n 4351)) (by decide +kernel)
  have a3851 := h.atom 3851 (.load (.n 4353) (.n 14) 3) (by decide +kernel)
  have a3852 := h.atom 3852 (.const (.n 4354) (word 7004910057750291985 0 0)) (by decide +kernel)
  have a3853 := h.atom 3853 (.mul (.n 4355) (.n 4353) (.n 4354)) (by decide +kernel)
  have a3854 := h.atom 3854 (.add (.n 4356) (.n 4352) (.n 4355)) (by decide +kernel)
  have a3855 := h.atom 3855 (.load (.n 4357) (.n 14) 4) (by decide +kernel)
  have a3856 := h.atom 3856 (.const (.n 4358) (word 13293599522548616907 0 0)) (by decide +kernel)
  have a3857 := h.atom 3857 (.mul (.n 4359) (.n 4357) (.n 4358)) (by decide +kernel)
  have a3858 := h.atom 3858 (.add (.n 4360) (.n 4356) (.n 4359)) (by decide +kernel)
  have a3859 := h.atom 3859 (.mul (.n 4361) (.n 3928) (.n 4360)) (by decide +kernel)
  have a3860 := h.atom 3860 (.add (.n 4362) (.n 4348) (.n 4361)) (by decide +kernel)
  have a3861 := h.atom 3861 (.load (.n 4363) (.n 14) 0) (by decide +kernel)
  have a3862 := h.atom 3862 (.const (.n 4364) (word 2 0 0)) (by decide +kernel)
  have a3863 := h.atom 3863 (.mul (.n 4365) (.n 4363) (.n 4364)) (by decide +kernel)
  have a3864 := h.atom 3864 (.add (.n 4366) (.n 2853) (.n 4365)) (by decide +kernel)
  have a3865 := h.atom 3865 (.load (.n 4367) (.n 14) 3) (by decide +kernel)
  have a3866 := h.atom 3866 (.const (.n 4368) (word 10105770293752443592 0 0)) (by decide +kernel)
  have a3867 := h.atom 3867 (.mul (.n 4369) (.n 4367) (.n 4368)) (by decide +kernel)
  have a3868 := h.atom 3868 (.add (.n 4370) (.n 4366) (.n 4369)) (by decide +kernel)
  have a3869 := h.atom 3869 (.load (.n 4371) (.n 14) 4) (by decide +kernel)
  have a3870 := h.atom 3870 (.const (.n 4372) (word 10668034807192757780 0 0)) (by decide +kernel)
  have a3871 := h.atom 3871 (.mul (.n 4373) (.n 4371) (.n 4372)) (by decide +kernel)
  have a3872 := h.atom 3872 (.add (.n 4374) (.n 4370) (.n 4373)) (by decide +kernel)
  have a3873 := h.atom 3873 (.mul (.n 4375) (.n 3947) (.n 4374)) (by decide +kernel)
  have a3874 := h.atom 3874 (.add (.n 4376) (.n 4362) (.n 4375)) (by decide +kernel)
  have a3875 := h.atom 3875 (.load (.n 4377) (.n 14) 0) (by decide +kernel)
  have a3876 := h.atom 3876 (.const (.n 4378) (word 2 0 0)) (by decide +kernel)
  have a3877 := h.atom 3877 (.mul (.n 4379) (.n 4377) (.n 4378)) (by decide +kernel)
  have a3878 := h.atom 3878 (.add (.n 4380) (.n 2853) (.n 4379)) (by decide +kernel)
  have a3879 := h.atom 3879 (.load (.n 4381) (.n 14) 3) (by decide +kernel)
  have a3880 := h.atom 3880 (.const (.n 4382) (word 1747952066141424100 0 0)) (by decide +kernel)
  have a3881 := h.atom 3881 (.mul (.n 4383) (.n 4381) (.n 4382)) (by decide +kernel)
  have a3882 := h.atom 3882 (.add (.n 4384) (.n 4380) (.n 4383)) (by decide +kernel)
  have a3883 := h.atom 3883 (.load (.n 4385) (.n 14) 4) (by decide +kernel)
  have a3884 := h.atom 3884 (.const (.n 4386) (word 1654286879329379778 0 0)) (by decide +kernel)
  have a3885 := h.atom 3885 (.mul (.n 4387) (.n 4385) (.n 4386)) (by decide +kernel)
  have a3886 := h.atom 3886 (.add (.n 4388) (.n 4384) (.n 4387)) (by decide +kernel)
  have a3887 := h.atom 3887 (.mul (.n 4389) (.n 3966) (.n 4388)) (by decide +kernel)
  have a3888 := h.atom 3888 (.add (.n 4390) (.n 4376) (.n 4389)) (by decide +kernel)
  have a3889 := h.atom 3889 (.load (.n 4391) (.n 14) 0) (by decide +kernel)
  have a3890 := h.atom 3890 (.const (.n 4392) (word 2 0 0)) (by decide +kernel)
  have a3891 := h.atom 3891 (.mul (.n 4393) (.n 4391) (.n 4392)) (by decide +kernel)
  have a3892 := h.atom 3892 (.add (.n 4394) (.n 2853) (.n 4393)) (by decide +kernel)
  have a3893 := h.atom 3893 (.load (.n 4395) (.n 14) 3) (by decide +kernel)
  have a3894 := h.atom 3894 (.const (.n 4396) (word 8500057116360352059 0 0)) (by decide +kernel)
  have a3895 := h.atom 3895 (.mul (.n 4397) (.n 4395) (.n 4396)) (by decide +kernel)
  have a3896 := h.atom 3896 (.add (.n 4398) (.n 4394) (.n 4397)) (by decide +kernel)
  have a3897 := h.atom 3897 (.load (.n 4399) (.n 14) 4) (by decide +kernel)
  have a3898 := h.atom 3898 (.const (.n 4400) (word 16929593379567477321 0 0)) (by decide +kernel)
  have a3899 := h.atom 3899 (.mul (.n 4401) (.n 4399) (.n 4400)) (by decide +kernel)
  have a3900 := h.atom 3900 (.add (.n 4402) (.n 4398) (.n 4401)) (by decide +kernel)
  have a3901 := h.atom 3901 (.mul (.n 4403) (.n 3985) (.n 4402)) (by decide +kernel)
  have a3902 := h.atom 3902 (.add (.n 4404) (.n 4390) (.n 4403)) (by decide +kernel)
  have a3903 := h.atom 3903 (.mul (.n 4405) (.n 2716) (.n 4404)) (by decide +kernel)
  have a3904 := h.atom 3904 (.add (.n 4406) (.n 4135) (.n 4405)) (by decide +kernel)
  have a3905 := h.atom 3905 (.add (.n 4407) (.n 3036) (.n 4406)) (by decide +kernel)
  have a3906 := h.atom 3906 (.const (.n 4408) (word 1 0 0)) (by decide +kernel)
  have a3907 := h.atom 3907 (.add (.n 4409) (.n 4408) (.n 3984)) (by decide +kernel)
  have a3908 := h.atom 3908 (.add (.n 4410) (.n 4407) (.n 4409)) (by decide +kernel)
  have a3909 := h.atom 3909 (.add (.n 4411) (.n 4410) (.n 27)) (by decide +kernel)
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The pull side's total.** -/
theorem vtP_pull_total {rd : Reader} {σ : Val} (h : VtP rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i)) :
    σ (.n 4924) = σ (.n 2873) * (σ (.n 15) + (W 0 + W 1 * vtWFinalPc + W 2)) +
      σ (.n 2904) * (σ (.n 15) + (W 0 * gen + W 1 * σ (.n 4440) + W 2 * σ (.n 4444) +
        W 3 * σ (.n 4457) + W 4 * σ (.n 4461) + W 5 * σ (.n 4465))) +
      σ (.n 2979) * (σ (.n 15) + (W 0 * gen ^ 2 + W 1 * σ (.n 4485) + W 2 * σ (.n 4502) +
        σ (.n 2639))) + σ (.n 4406) +
      (1 + (σ (.n 2873) + σ (.n 2904) + σ (.n 2979) +
        (vtPushPadData.map fun x ↦ σ (.n x.2.2.1)).sum)) + σ (.n 28) := by
  have a3914 := h.atom 3914 (.load (.n 4418) (.n 14) 0) (by decide +kernel)
  have a3915 := h.atom 3915 (.load (.n 4419) (.n 14) 1) (by decide +kernel)
  have a3916 := h.atom 3916 (.const (.n 4420) (word 12261764870545049476 0 0)) (by decide +kernel)
  have a3917 := h.atom 3917 (.mul (.n 4421) (.n 4419) (.n 4420)) (by decide +kernel)
  have a3918 := h.atom 3918 (.add (.n 4422) (.n 4418) (.n 4421)) (by decide +kernel)
  have a3919 := h.atom 3919 (.load (.n 4423) (.n 14) 2) (by decide +kernel)
  have a3920 := h.atom 3920 (.add (.n 4424) (.n 4422) (.n 4423)) (by decide +kernel)
  have a3921 := h.atom 3921 (.const (.n 4425) (word 0 0 0)) (by decide +kernel)
  have a3922 := h.atom 3922 (.mul (.n 4426) (.n 4425) (.n 2639)) (by decide +kernel)
  have a3923 := h.atom 3923 (.add (.n 4427) (.n 4424) (.n 4426)) (by decide +kernel)
  have a3924 := h.atom 3924 (.add (.n 4428) (.n 15) (.n 4427)) (by decide +kernel)
  have a3925 := h.atom 3925 (.mul (.n 4429) (.n 2873) (.n 4428)) (by decide +kernel)
  have a3929 := h.atom 3929 (.add (.n 4435) (.n 2873) (.n 2904)) (by decide +kernel)
  have a3931 := h.atom 3931 (.load (.n 4437) (.n 14) 0) (by decide +kernel)
  have a3932 := h.atom 3932 (.const (.n 4438) (word 2 0 0)) (by decide +kernel)
  have a3933 := h.atom 3933 (.mul (.n 4439) (.n 4437) (.n 4438)) (by decide +kernel)
  have a3935 := h.atom 3935 (.load (.n 4441) (.n 14) 1) (by decide +kernel)
  have a3936 := h.atom 3936 (.mul (.n 4442) (.n 4441) (.n 4440)) (by decide +kernel)
  have a3937 := h.atom 3937 (.add (.n 4443) (.n 4439) (.n 4442)) (by decide +kernel)
  have a3949 := h.atom 3949 (.load (.n 4454) (.n 14) 2) (by decide +kernel)
  have a3950 := h.atom 3950 (.mul (.n 4455) (.n 4454) (.n 4444)) (by decide +kernel)
  have a3951 := h.atom 3951 (.add (.n 4456) (.n 4443) (.n 4455)) (by decide +kernel)
  have a3953 := h.atom 3953 (.load (.n 4458) (.n 14) 3) (by decide +kernel)
  have a3954 := h.atom 3954 (.mul (.n 4459) (.n 4458) (.n 4457)) (by decide +kernel)
  have a3955 := h.atom 3955 (.add (.n 4460) (.n 4456) (.n 4459)) (by decide +kernel)
  have a3957 := h.atom 3957 (.load (.n 4462) (.n 14) 4) (by decide +kernel)
  have a3958 := h.atom 3958 (.mul (.n 4463) (.n 4462) (.n 4461)) (by decide +kernel)
  have a3959 := h.atom 3959 (.add (.n 4464) (.n 4460) (.n 4463)) (by decide +kernel)
  have a3961 := h.atom 3961 (.load (.n 4466) (.n 14) 5) (by decide +kernel)
  have a3962 := h.atom 3962 (.mul (.n 4467) (.n 4466) (.n 4465)) (by decide +kernel)
  have a3963 := h.atom 3963 (.add (.n 4468) (.n 4464) (.n 4467)) (by decide +kernel)
  have a3964 := h.atom 3964 (.const (.n 4469) (word 0 0 0)) (by decide +kernel)
  have a3965 := h.atom 3965 (.mul (.n 4470) (.n 4469) (.n 2639)) (by decide +kernel)
  have a3966 := h.atom 3966 (.add (.n 4471) (.n 4468) (.n 4470)) (by decide +kernel)
  have a3967 := h.atom 3967 (.add (.n 4472) (.n 15) (.n 4471)) (by decide +kernel)
  have a3968 := h.atom 3968 (.mul (.n 4473) (.n 2904) (.n 4472)) (by decide +kernel)
  have a3969 := h.atom 3969 (.add (.n 4474) (.n 4429) (.n 4473)) (by decide +kernel)
  have a3973 := h.atom 3973 (.add (.n 4480) (.n 4435) (.n 2979)) (by decide +kernel)
  have a3975 := h.atom 3975 (.load (.n 4482) (.n 14) 0) (by decide +kernel)
  have a3976 := h.atom 3976 (.const (.n 4483) (word 4 0 0)) (by decide +kernel)
  have a3977 := h.atom 3977 (.mul (.n 4484) (.n 4482) (.n 4483)) (by decide +kernel)
  have a3979 := h.atom 3979 (.load (.n 4486) (.n 14) 1) (by decide +kernel)
  have a3980 := h.atom 3980 (.mul (.n 4487) (.n 4486) (.n 4485)) (by decide +kernel)
  have a3981 := h.atom 3981 (.add (.n 4488) (.n 4484) (.n 4487)) (by decide +kernel)
  have a3994 := h.atom 3994 (.load (.n 4512) (.n 14) 2) (by decide +kernel)
  have a3995 := h.atom 3995 (.mul (.n 4513) (.n 4512) (.n 4502)) (by decide +kernel)
  have a3996 := h.atom 3996 (.add (.n 4514) (.n 4488) (.n 4513)) (by decide +kernel)
  have a3997 := h.atom 3997 (.load (.n 4515) (.n 14) 3) (by decide +kernel)
  have a3998 := h.atom 3998 (.const (.n 4516) (word 0 0 0)) (by decide +kernel)
  have a3999 := h.atom 3999 (.mul (.n 4517) (.n 4515) (.n 4516)) (by decide +kernel)
  have a4000 := h.atom 4000 (.add (.n 4518) (.n 4514) (.n 4517)) (by decide +kernel)
  have a4001 := h.atom 4001 (.load (.n 4519) (.n 14) 4) (by decide +kernel)
  have a4002 := h.atom 4002 (.const (.n 4520) (word 0 0 0)) (by decide +kernel)
  have a4003 := h.atom 4003 (.mul (.n 4521) (.n 4519) (.n 4520)) (by decide +kernel)
  have a4004 := h.atom 4004 (.add (.n 4522) (.n 4518) (.n 4521)) (by decide +kernel)
  have a4005 := h.atom 4005 (.load (.n 4523) (.n 14) 5) (by decide +kernel)
  have a4006 := h.atom 4006 (.const (.n 4524) (word 0 0 0)) (by decide +kernel)
  have a4007 := h.atom 4007 (.mul (.n 4525) (.n 4523) (.n 4524)) (by decide +kernel)
  have a4008 := h.atom 4008 (.add (.n 4526) (.n 4522) (.n 4525)) (by decide +kernel)
  have a4009 := h.atom 4009 (.load (.n 4527) (.n 14) 6) (by decide +kernel)
  have a4010 := h.atom 4010 (.const (.n 4528) (word 0 0 0)) (by decide +kernel)
  have a4011 := h.atom 4011 (.mul (.n 4529) (.n 4527) (.n 4528)) (by decide +kernel)
  have a4012 := h.atom 4012 (.add (.n 4530) (.n 4526) (.n 4529)) (by decide +kernel)
  have a4013 := h.atom 4013 (.load (.n 4531) (.n 14) 7) (by decide +kernel)
  have a4014 := h.atom 4014 (.const (.n 4532) (word 0 0 0)) (by decide +kernel)
  have a4015 := h.atom 4015 (.mul (.n 4533) (.n 4531) (.n 4532)) (by decide +kernel)
  have a4016 := h.atom 4016 (.add (.n 4534) (.n 4530) (.n 4533)) (by decide +kernel)
  have a4017 := h.atom 4017 (.load (.n 4535) (.n 14) 8) (by decide +kernel)
  have a4018 := h.atom 4018 (.const (.n 4536) (word 0 0 0)) (by decide +kernel)
  have a4019 := h.atom 4019 (.mul (.n 4537) (.n 4535) (.n 4536)) (by decide +kernel)
  have a4020 := h.atom 4020 (.add (.n 4538) (.n 4534) (.n 4537)) (by decide +kernel)
  have a4021 := h.atom 4021 (.load (.n 4539) (.n 14) 9) (by decide +kernel)
  have a4022 := h.atom 4022 (.const (.n 4540) (word 0 0 0)) (by decide +kernel)
  have a4023 := h.atom 4023 (.mul (.n 4541) (.n 4539) (.n 4540)) (by decide +kernel)
  have a4024 := h.atom 4024 (.add (.n 4542) (.n 4538) (.n 4541)) (by decide +kernel)
  have a4025 := h.atom 4025 (.load (.n 4543) (.n 14) 10) (by decide +kernel)
  have a4026 := h.atom 4026 (.const (.n 4544) (word 0 0 0)) (by decide +kernel)
  have a4027 := h.atom 4027 (.mul (.n 4545) (.n 4543) (.n 4544)) (by decide +kernel)
  have a4028 := h.atom 4028 (.add (.n 4546) (.n 4542) (.n 4545)) (by decide +kernel)
  have a4029 := h.atom 4029 (.load (.n 4547) (.n 14) 11) (by decide +kernel)
  have a4030 := h.atom 4030 (.const (.n 4548) (word 0 0 0)) (by decide +kernel)
  have a4031 := h.atom 4031 (.mul (.n 4549) (.n 4547) (.n 4548)) (by decide +kernel)
  have a4032 := h.atom 4032 (.add (.n 4550) (.n 4546) (.n 4549)) (by decide +kernel)
  have a4033 := h.atom 4033 (.load (.n 4551) (.n 14) 12) (by decide +kernel)
  have a4034 := h.atom 4034 (.const (.n 4552) (word 0 0 0)) (by decide +kernel)
  have a4035 := h.atom 4035 (.mul (.n 4553) (.n 4551) (.n 4552)) (by decide +kernel)
  have a4036 := h.atom 4036 (.add (.n 4554) (.n 4550) (.n 4553)) (by decide +kernel)
  have a4037 := h.atom 4037 (.load (.n 4555) (.n 14) 13) (by decide +kernel)
  have a4038 := h.atom 4038 (.const (.n 4556) (word 0 0 0)) (by decide +kernel)
  have a4039 := h.atom 4039 (.mul (.n 4557) (.n 4555) (.n 4556)) (by decide +kernel)
  have a4040 := h.atom 4040 (.add (.n 4558) (.n 4554) (.n 4557)) (by decide +kernel)
  have a4041 := h.atom 4041 (.add (.n 4559) (.n 4558) (.n 2639)) (by decide +kernel)
  have a4042 := h.atom 4042 (.add (.n 4560) (.n 15) (.n 4559)) (by decide +kernel)
  have a4043 := h.atom 4043 (.mul (.n 4561) (.n 2979) (.n 4560)) (by decide +kernel)
  have a4044 := h.atom 4044 (.add (.n 4562) (.n 4474) (.n 4561)) (by decide +kernel)
  have a4048 := h.atom 4048 (.add (.n 4568) (.n 4480) (.n 3051)) (by decide +kernel)
  have a4053 := h.atom 4053 (.add (.n 4575) (.n 4568) (.n 3066)) (by decide +kernel)
  have a4058 := h.atom 4058 (.add (.n 4582) (.n 4575) (.n 3081)) (by decide +kernel)
  have a4063 := h.atom 4063 (.add (.n 4589) (.n 4582) (.n 3096)) (by decide +kernel)
  have a4068 := h.atom 4068 (.add (.n 4596) (.n 4589) (.n 3111)) (by decide +kernel)
  have a4073 := h.atom 4073 (.add (.n 4603) (.n 4596) (.n 3130)) (by decide +kernel)
  have a4078 := h.atom 4078 (.add (.n 4610) (.n 4603) (.n 3149)) (by decide +kernel)
  have a4083 := h.atom 4083 (.add (.n 4617) (.n 4610) (.n 3168)) (by decide +kernel)
  have a4088 := h.atom 4088 (.add (.n 4624) (.n 4617) (.n 3187)) (by decide +kernel)
  have a4093 := h.atom 4093 (.add (.n 4631) (.n 4624) (.n 3206)) (by decide +kernel)
  have a4098 := h.atom 4098 (.add (.n 4638) (.n 4631) (.n 3225)) (by decide +kernel)
  have a4103 := h.atom 4103 (.add (.n 4645) (.n 4638) (.n 3244)) (by decide +kernel)
  have a4108 := h.atom 4108 (.add (.n 4652) (.n 4645) (.n 3263)) (by decide +kernel)
  have a4113 := h.atom 4113 (.add (.n 4659) (.n 4652) (.n 3282)) (by decide +kernel)
  have a4118 := h.atom 4118 (.add (.n 4666) (.n 4659) (.n 3301)) (by decide +kernel)
  have a4123 := h.atom 4123 (.add (.n 4673) (.n 4666) (.n 3320)) (by decide +kernel)
  have a4128 := h.atom 4128 (.add (.n 4680) (.n 4673) (.n 3339)) (by decide +kernel)
  have a4133 := h.atom 4133 (.add (.n 4687) (.n 4680) (.n 3358)) (by decide +kernel)
  have a4138 := h.atom 4138 (.add (.n 4694) (.n 4687) (.n 3377)) (by decide +kernel)
  have a4143 := h.atom 4143 (.add (.n 4701) (.n 4694) (.n 3396)) (by decide +kernel)
  have a4148 := h.atom 4148 (.add (.n 4708) (.n 4701) (.n 3415)) (by decide +kernel)
  have a4153 := h.atom 4153 (.add (.n 4715) (.n 4708) (.n 3434)) (by decide +kernel)
  have a4158 := h.atom 4158 (.add (.n 4722) (.n 4715) (.n 3453)) (by decide +kernel)
  have a4163 := h.atom 4163 (.add (.n 4729) (.n 4722) (.n 3472)) (by decide +kernel)
  have a4168 := h.atom 4168 (.add (.n 4736) (.n 4729) (.n 3491)) (by decide +kernel)
  have a4173 := h.atom 4173 (.add (.n 4743) (.n 4736) (.n 3510)) (by decide +kernel)
  have a4178 := h.atom 4178 (.add (.n 4750) (.n 4743) (.n 3529)) (by decide +kernel)
  have a4183 := h.atom 4183 (.add (.n 4757) (.n 4750) (.n 3548)) (by decide +kernel)
  have a4188 := h.atom 4188 (.add (.n 4764) (.n 4757) (.n 3567)) (by decide +kernel)
  have a4193 := h.atom 4193 (.add (.n 4771) (.n 4764) (.n 3586)) (by decide +kernel)
  have a4198 := h.atom 4198 (.add (.n 4778) (.n 4771) (.n 3605)) (by decide +kernel)
  have a4203 := h.atom 4203 (.add (.n 4785) (.n 4778) (.n 3624)) (by decide +kernel)
  have a4208 := h.atom 4208 (.add (.n 4792) (.n 4785) (.n 3643)) (by decide +kernel)
  have a4213 := h.atom 4213 (.add (.n 4799) (.n 4792) (.n 3662)) (by decide +kernel)
  have a4218 := h.atom 4218 (.add (.n 4806) (.n 4799) (.n 3681)) (by decide +kernel)
  have a4223 := h.atom 4223 (.add (.n 4813) (.n 4806) (.n 3700)) (by decide +kernel)
  have a4228 := h.atom 4228 (.add (.n 4820) (.n 4813) (.n 3719)) (by decide +kernel)
  have a4233 := h.atom 4233 (.add (.n 4827) (.n 4820) (.n 3738)) (by decide +kernel)
  have a4238 := h.atom 4238 (.add (.n 4834) (.n 4827) (.n 3757)) (by decide +kernel)
  have a4243 := h.atom 4243 (.add (.n 4841) (.n 4834) (.n 3776)) (by decide +kernel)
  have a4248 := h.atom 4248 (.add (.n 4848) (.n 4841) (.n 3795)) (by decide +kernel)
  have a4253 := h.atom 4253 (.add (.n 4855) (.n 4848) (.n 3814)) (by decide +kernel)
  have a4258 := h.atom 4258 (.add (.n 4862) (.n 4855) (.n 3833)) (by decide +kernel)
  have a4263 := h.atom 4263 (.add (.n 4869) (.n 4862) (.n 3852)) (by decide +kernel)
  have a4268 := h.atom 4268 (.add (.n 4876) (.n 4869) (.n 3871)) (by decide +kernel)
  have a4273 := h.atom 4273 (.add (.n 4883) (.n 4876) (.n 3890)) (by decide +kernel)
  have a4278 := h.atom 4278 (.add (.n 4890) (.n 4883) (.n 3909)) (by decide +kernel)
  have a4283 := h.atom 4283 (.add (.n 4897) (.n 4890) (.n 3928)) (by decide +kernel)
  have a4288 := h.atom 4288 (.add (.n 4904) (.n 4897) (.n 3947)) (by decide +kernel)
  have a4293 := h.atom 4293 (.add (.n 4911) (.n 4904) (.n 3966)) (by decide +kernel)
  have a4298 := h.atom 4298 (.add (.n 4918) (.n 4911) (.n 3985)) (by decide +kernel)
  have a4300 := h.atom 4300 (.add (.n 4920) (.n 4562) (.n 4406)) (by decide +kernel)
  have a4301 := h.atom 4301 (.const (.n 4921) (word 1 0 0)) (by decide +kernel)
  have a4302 := h.atom 4302 (.add (.n 4922) (.n 4921) (.n 4918)) (by decide +kernel)
  have a4303 := h.atom 4303 (.add (.n 4923) (.n 4920) (.n 4922)) (by decide +kernel)
  have a4304 := h.atom 4304 (.add (.n 4924) (.n 4923) (.n 28)) (by decide +kernel)
  have e3914 := tb_loadHolds_unique a3914 (hw 0 (by norm_num))
  have e3915 := tb_loadHolds_unique a3915 (hw 1 (by norm_num))
  have e3919 := tb_loadHolds_unique a3919 (hw 2 (by norm_num))
  have e3931 := tb_loadHolds_unique a3931 (hw 0 (by norm_num))
  have e3935 := tb_loadHolds_unique a3935 (hw 1 (by norm_num))
  have e3949 := tb_loadHolds_unique a3949 (hw 2 (by norm_num))
  have e3953 := tb_loadHolds_unique a3953 (hw 3 (by norm_num))
  have e3957 := tb_loadHolds_unique a3957 (hw 4 (by norm_num))
  have e3961 := tb_loadHolds_unique a3961 (hw 5 (by norm_num))
  have e3975 := tb_loadHolds_unique a3975 (hw 0 (by norm_num))
  have e3979 := tb_loadHolds_unique a3979 (hw 1 (by norm_num))
  have e3994 := tb_loadHolds_unique a3994 (hw 2 (by norm_num))
  have e3997 := tb_loadHolds_unique a3997 (hw 3 (by norm_num))
  have e4001 := tb_loadHolds_unique a4001 (hw 4 (by norm_num))
  have e4005 := tb_loadHolds_unique a4005 (hw 5 (by norm_num))
  have e4009 := tb_loadHolds_unique a4009 (hw 6 (by norm_num))
  have e4013 := tb_loadHolds_unique a4013 (hw 7 (by norm_num))
  have e4017 := tb_loadHolds_unique a4017 (hw 8 (by norm_num))
  have e4021 := tb_loadHolds_unique a4021 (hw 9 (by norm_num))
  have e4025 := tb_loadHolds_unique a4025 (hw 10 (by norm_num))
  have e4029 := tb_loadHolds_unique a4029 (hw 11 (by norm_num))
  have e4033 := tb_loadHolds_unique a4033 (hw 12 (by norm_num))
  have e4037 := tb_loadHolds_unique a4037 (hw 13 (by norm_num))
  simp only [Atom.Holds] at a3916 a3917 a3918 a3920 a3921 a3922 a3923 a3924 a3925 a3929
  simp only [Atom.Holds] at a3932 a3933 a3936 a3937 a3950 a3951 a3954 a3955 a3958 a3959
  simp only [Atom.Holds] at a3962 a3963 a3964 a3965 a3966 a3967 a3968 a3969 a3973 a3976
  simp only [Atom.Holds] at a3977 a3980 a3981 a3995 a3996 a3998 a3999 a4000 a4002 a4003
  simp only [Atom.Holds] at a4004 a4006 a4007 a4008 a4010 a4011 a4012 a4014 a4015 a4016
  simp only [Atom.Holds] at a4018 a4019 a4020 a4022 a4023 a4024 a4026 a4027 a4028 a4030
  simp only [Atom.Holds] at a4031 a4032 a4034 a4035 a4036 a4038 a4039 a4040 a4041 a4042
  simp only [Atom.Holds] at a4043 a4044 a4048 a4053 a4058 a4063 a4068 a4073 a4078 a4083
  simp only [Atom.Holds] at a4088 a4093 a4098 a4103 a4108 a4113 a4118 a4123 a4128 a4133
  simp only [Atom.Holds] at a4138 a4143 a4148 a4153 a4158 a4163 a4168 a4173 a4178 a4183
  simp only [Atom.Holds] at a4188 a4193 a4198 a4203 a4208 a4213 a4218 a4223 a4228 a4233
  simp only [Atom.Holds] at a4238 a4243 a4248 a4253 a4258 a4263 a4268 a4273 a4278 a4283
  simp only [Atom.Holds] at a4288 a4293 a4298 a4300 a4301 a4302 a4303 a4304
  simp only [e3914, e3915, a3916, a3917, a3918, e3919, a3920, a3921, a3922, a3923, a3924, a3925, a3929,
    e3931, a3932, a3933, e3935, a3936, a3937, e3949, a3950, a3951, e3953, a3954, a3955, e3957,
    a3958, a3959, e3961, a3962, a3963, a3964, a3965, a3966, a3967, a3968, a3969, a3973, e3975,
    a3976, a3977, e3979, a3980, a3981, e3994, a3995, a3996, e3997, a3998, a3999, a4000, e4001,
    a4002, a4003, a4004, e4005, a4006, a4007, a4008, e4009, a4010, a4011, a4012, e4013, a4014,
    a4015, a4016, e4017, a4018, a4019, a4020, e4021, a4022, a4023, a4024, e4025, a4026, a4027,
    a4028, e4029, a4030, a4031, a4032, e4033, a4034, a4035, a4036, e4037, a4038, a4039, a4040,
    a4041, a4042, a4043, a4044, a4048, a4053, a4058, a4063, a4068, a4073, a4078, a4083, a4088,
    a4093, a4098, a4103, a4108, a4113, a4118, a4123, a4128, a4133, a4138, a4143, a4148, a4153,
    a4158, a4163, a4168, a4173, a4178, a4183, a4188, a4193, a4198, a4203, a4208, a4213, a4218,
    a4223, a4228, a4233, a4238, a4243, a4248, a4253, a4258, a4263, a4268, a4273, a4278, a4283,
    a4288, a4293, a4298, a4300, a4301, a4302, a4303, a4304]
  simp only [vtPushPadData, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [tb_word_zero, tb_word_one, tb_word_gen, show (4 : ℕ) = 2 ^ 2 by norm_num,
    tb_word_two_pow (by norm_num)]
  ring

theorem vtPPullSels0 {rd : Reader} {σ : Val} (h : VtP rd σ) :
    [σ (.n 4569), σ (.n 4576), σ (.n 4583), σ (.n 4590), σ (.n 4597)] =
      [σ (.n 3051), σ (.n 3066), σ (.n 3081), σ (.n 3096), σ (.n 3111)] := by
  have a4049 := h.atom 4049 (.copy (.n 4569) (.n 3051)) (by decide +kernel)
  have a4054 := h.atom 4054 (.copy (.n 4576) (.n 3066)) (by decide +kernel)
  have a4059 := h.atom 4059 (.copy (.n 4583) (.n 3081)) (by decide +kernel)
  have a4064 := h.atom 4064 (.copy (.n 4590) (.n 3096)) (by decide +kernel)
  have a4069 := h.atom 4069 (.copy (.n 4597) (.n 3111)) (by decide +kernel)
  simp only [Atom.Holds] at a4049 a4054 a4059 a4064 a4069
  rw [a4049, a4054, a4059, a4064, a4069]

theorem vtPPullSels1 {rd : Reader} {σ : Val} (h : VtP rd σ) :
    [σ (.n 4604), σ (.n 4611), σ (.n 4618), σ (.n 4625), σ (.n 4632)] =
      [σ (.n 3130), σ (.n 3149), σ (.n 3168), σ (.n 3187), σ (.n 3206)] := by
  have a4074 := h.atom 4074 (.copy (.n 4604) (.n 3130)) (by decide +kernel)
  have a4079 := h.atom 4079 (.copy (.n 4611) (.n 3149)) (by decide +kernel)
  have a4084 := h.atom 4084 (.copy (.n 4618) (.n 3168)) (by decide +kernel)
  have a4089 := h.atom 4089 (.copy (.n 4625) (.n 3187)) (by decide +kernel)
  have a4094 := h.atom 4094 (.copy (.n 4632) (.n 3206)) (by decide +kernel)
  simp only [Atom.Holds] at a4074 a4079 a4084 a4089 a4094
  rw [a4074, a4079, a4084, a4089, a4094]

theorem vtPPullSels2 {rd : Reader} {σ : Val} (h : VtP rd σ) :
    [σ (.n 4639), σ (.n 4646), σ (.n 4653)] =
      [σ (.n 3225), σ (.n 3244), σ (.n 3263)] := by
  have a4099 := h.atom 4099 (.copy (.n 4639) (.n 3225)) (by decide +kernel)
  have a4104 := h.atom 4104 (.copy (.n 4646) (.n 3244)) (by decide +kernel)
  have a4109 := h.atom 4109 (.copy (.n 4653) (.n 3263)) (by decide +kernel)
  simp only [Atom.Holds] at a4099 a4104 a4109
  rw [a4099, a4104, a4109]

theorem vtPPullSels3 {rd : Reader} {σ : Val} (h : VtP rd σ) :
    [σ (.n 4660), σ (.n 4667), σ (.n 4674), σ (.n 4681), σ (.n 4688)] =
      [σ (.n 3282), σ (.n 3301), σ (.n 3320), σ (.n 3339), σ (.n 3358)] := by
  have a4114 := h.atom 4114 (.copy (.n 4660) (.n 3282)) (by decide +kernel)
  have a4119 := h.atom 4119 (.copy (.n 4667) (.n 3301)) (by decide +kernel)
  have a4124 := h.atom 4124 (.copy (.n 4674) (.n 3320)) (by decide +kernel)
  have a4129 := h.atom 4129 (.copy (.n 4681) (.n 3339)) (by decide +kernel)
  have a4134 := h.atom 4134 (.copy (.n 4688) (.n 3358)) (by decide +kernel)
  simp only [Atom.Holds] at a4114 a4119 a4124 a4129 a4134
  rw [a4114, a4119, a4124, a4129, a4134]

theorem vtPPullSels4 {rd : Reader} {σ : Val} (h : VtP rd σ) :
    [σ (.n 4695), σ (.n 4702), σ (.n 4709), σ (.n 4716), σ (.n 4723)] =
      [σ (.n 3377), σ (.n 3396), σ (.n 3415), σ (.n 3434), σ (.n 3453)] := by
  have a4139 := h.atom 4139 (.copy (.n 4695) (.n 3377)) (by decide +kernel)
  have a4144 := h.atom 4144 (.copy (.n 4702) (.n 3396)) (by decide +kernel)
  have a4149 := h.atom 4149 (.copy (.n 4709) (.n 3415)) (by decide +kernel)
  have a4154 := h.atom 4154 (.copy (.n 4716) (.n 3434)) (by decide +kernel)
  have a4159 := h.atom 4159 (.copy (.n 4723) (.n 3453)) (by decide +kernel)
  simp only [Atom.Holds] at a4139 a4144 a4149 a4154 a4159
  rw [a4139, a4144, a4149, a4154, a4159]

theorem vtPPullSels5 {rd : Reader} {σ : Val} (h : VtP rd σ) :
    [σ (.n 4730), σ (.n 4737), σ (.n 4744), σ (.n 4751), σ (.n 4758), σ (.n 4765), σ (.n 4772), σ (.n 4779), σ (.n 4786), σ (.n 4793), σ (.n 4800), σ (.n 4807), σ (.n 4814), σ (.n 4821), σ (.n 4828), σ (.n 4835), σ (.n 4842), σ (.n 4849), σ (.n 4856), σ (.n 4863), σ (.n 4870), σ (.n 4877), σ (.n 4884), σ (.n 4891), σ (.n 4898), σ (.n 4905), σ (.n 4912), σ (.n 4919)] =
      [σ (.n 3472), σ (.n 3491), σ (.n 3510), σ (.n 3529), σ (.n 3548), σ (.n 3567), σ (.n 3586), σ (.n 3605), σ (.n 3624), σ (.n 3643), σ (.n 3662), σ (.n 3681), σ (.n 3700), σ (.n 3719), σ (.n 3738), σ (.n 3757), σ (.n 3776), σ (.n 3795), σ (.n 3814), σ (.n 3833), σ (.n 3852), σ (.n 3871), σ (.n 3890), σ (.n 3909), σ (.n 3928), σ (.n 3947), σ (.n 3966), σ (.n 3985)] := by
  have a4164 := h.atom 4164 (.copy (.n 4730) (.n 3472)) (by decide +kernel)
  have a4169 := h.atom 4169 (.copy (.n 4737) (.n 3491)) (by decide +kernel)
  have a4174 := h.atom 4174 (.copy (.n 4744) (.n 3510)) (by decide +kernel)
  have a4179 := h.atom 4179 (.copy (.n 4751) (.n 3529)) (by decide +kernel)
  have a4184 := h.atom 4184 (.copy (.n 4758) (.n 3548)) (by decide +kernel)
  have a4189 := h.atom 4189 (.copy (.n 4765) (.n 3567)) (by decide +kernel)
  have a4194 := h.atom 4194 (.copy (.n 4772) (.n 3586)) (by decide +kernel)
  have a4199 := h.atom 4199 (.copy (.n 4779) (.n 3605)) (by decide +kernel)
  have a4204 := h.atom 4204 (.copy (.n 4786) (.n 3624)) (by decide +kernel)
  have a4209 := h.atom 4209 (.copy (.n 4793) (.n 3643)) (by decide +kernel)
  have a4214 := h.atom 4214 (.copy (.n 4800) (.n 3662)) (by decide +kernel)
  have a4219 := h.atom 4219 (.copy (.n 4807) (.n 3681)) (by decide +kernel)
  have a4224 := h.atom 4224 (.copy (.n 4814) (.n 3700)) (by decide +kernel)
  have a4229 := h.atom 4229 (.copy (.n 4821) (.n 3719)) (by decide +kernel)
  have a4234 := h.atom 4234 (.copy (.n 4828) (.n 3738)) (by decide +kernel)
  have a4239 := h.atom 4239 (.copy (.n 4835) (.n 3757)) (by decide +kernel)
  have a4244 := h.atom 4244 (.copy (.n 4842) (.n 3776)) (by decide +kernel)
  have a4249 := h.atom 4249 (.copy (.n 4849) (.n 3795)) (by decide +kernel)
  have a4254 := h.atom 4254 (.copy (.n 4856) (.n 3814)) (by decide +kernel)
  have a4259 := h.atom 4259 (.copy (.n 4863) (.n 3833)) (by decide +kernel)
  have a4264 := h.atom 4264 (.copy (.n 4870) (.n 3852)) (by decide +kernel)
  have a4269 := h.atom 4269 (.copy (.n 4877) (.n 3871)) (by decide +kernel)
  have a4274 := h.atom 4274 (.copy (.n 4884) (.n 3890)) (by decide +kernel)
  have a4279 := h.atom 4279 (.copy (.n 4891) (.n 3909)) (by decide +kernel)
  have a4284 := h.atom 4284 (.copy (.n 4898) (.n 3928)) (by decide +kernel)
  have a4289 := h.atom 4289 (.copy (.n 4905) (.n 3947)) (by decide +kernel)
  have a4294 := h.atom 4294 (.copy (.n 4912) (.n 3966)) (by decide +kernel)
  have a4299 := h.atom 4299 (.copy (.n 4919) (.n 3985)) (by decide +kernel)
  simp only [Atom.Holds] at a4164 a4169 a4174 a4179 a4184 a4189 a4194 a4199 a4204 a4209 a4214 a4219 a4224 a4229 a4234 a4239 a4244 a4249 a4254 a4259 a4264 a4269 a4274 a4279 a4284 a4289 a4294 a4299
  rw [a4164, a4169, a4174, a4179, a4184, a4189, a4194, a4199, a4204, a4209, a4214, a4219, a4224, a4229, a4234, a4239, a4244, a4249, a4254, a4259, a4264, a4269, a4274, a4279, a4284, a4289, a4294, a4299]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The count side's total.** -/
theorem vtP_count_total {rd : Reader} {σ : Val} (h : VtP rd σ) (W : ℕ → E) :
    σ (.n 5816) = vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W 1 vtCountPadData +
      (1 + σ (.n 5761)) + σ (.n 29) := by
  have a5098 := h.atom 5098 (.add (.n 5763) (.n 4938) (.n 4953)) (by decide +kernel)
  have a5099 := h.atom 5099 (.add (.n 5764) (.n 5763) (.n 4968)) (by decide +kernel)
  have a5100 := h.atom 5100 (.add (.n 5765) (.n 5764) (.n 4983)) (by decide +kernel)
  have a5101 := h.atom 5101 (.mul (.n 5766) (.n 2646) (.n 5765)) (by decide +kernel)
  have a5102 := h.atom 5102 (.add (.n 5767) (.n 5002) (.n 5021)) (by decide +kernel)
  have a5103 := h.atom 5103 (.add (.n 5768) (.n 5767) (.n 5040)) (by decide +kernel)
  have a5104 := h.atom 5104 (.add (.n 5769) (.n 5768) (.n 5059)) (by decide +kernel)
  have a5105 := h.atom 5105 (.mul (.n 5770) (.n 2660) (.n 5769)) (by decide +kernel)
  have a5106 := h.atom 5106 (.add (.n 5771) (.n 5766) (.n 5770)) (by decide +kernel)
  have a5107 := h.atom 5107 (.add (.n 5772) (.n 5078) (.n 5097)) (by decide +kernel)
  have a5108 := h.atom 5108 (.mul (.n 5773) (.n 2674) (.n 5772)) (by decide +kernel)
  have a5109 := h.atom 5109 (.add (.n 5774) (.n 5771) (.n 5773)) (by decide +kernel)
  have a5110 := h.atom 5110 (.add (.n 5775) (.n 5116) (.n 5135)) (by decide +kernel)
  have a5111 := h.atom 5111 (.add (.n 5776) (.n 5775) (.n 5154)) (by decide +kernel)
  have a5112 := h.atom 5112 (.add (.n 5777) (.n 5776) (.n 5173)) (by decide +kernel)
  have a5113 := h.atom 5113 (.mul (.n 5778) (.n 2688) (.n 5777)) (by decide +kernel)
  have a5114 := h.atom 5114 (.add (.n 5779) (.n 5774) (.n 5778)) (by decide +kernel)
  have a5115 := h.atom 5115 (.add (.n 5780) (.n 5192) (.n 5211)) (by decide +kernel)
  have a5116 := h.atom 5116 (.add (.n 5781) (.n 5780) (.n 5230)) (by decide +kernel)
  have a5117 := h.atom 5117 (.add (.n 5782) (.n 5781) (.n 5249)) (by decide +kernel)
  have a5118 := h.atom 5118 (.mul (.n 5783) (.n 2702) (.n 5782)) (by decide +kernel)
  have a5119 := h.atom 5119 (.add (.n 5784) (.n 5779) (.n 5783)) (by decide +kernel)
  have a5120 := h.atom 5120 (.add (.n 5785) (.n 5268) (.n 5287)) (by decide +kernel)
  have a5121 := h.atom 5121 (.add (.n 5786) (.n 5785) (.n 5306)) (by decide +kernel)
  have a5122 := h.atom 5122 (.add (.n 5787) (.n 5786) (.n 5325)) (by decide +kernel)
  have a5123 := h.atom 5123 (.add (.n 5788) (.n 5787) (.n 5344)) (by decide +kernel)
  have a5124 := h.atom 5124 (.add (.n 5789) (.n 5788) (.n 5363)) (by decide +kernel)
  have a5125 := h.atom 5125 (.add (.n 5790) (.n 5789) (.n 5382)) (by decide +kernel)
  have a5126 := h.atom 5126 (.add (.n 5791) (.n 5790) (.n 5401)) (by decide +kernel)
  have a5127 := h.atom 5127 (.add (.n 5792) (.n 5791) (.n 5420)) (by decide +kernel)
  have a5128 := h.atom 5128 (.add (.n 5793) (.n 5792) (.n 5439)) (by decide +kernel)
  have a5129 := h.atom 5129 (.add (.n 5794) (.n 5793) (.n 5458)) (by decide +kernel)
  have a5130 := h.atom 5130 (.add (.n 5795) (.n 5794) (.n 5477)) (by decide +kernel)
  have a5131 := h.atom 5131 (.add (.n 5796) (.n 5795) (.n 5496)) (by decide +kernel)
  have a5132 := h.atom 5132 (.add (.n 5797) (.n 5796) (.n 5515)) (by decide +kernel)
  have a5133 := h.atom 5133 (.add (.n 5798) (.n 5797) (.n 5534)) (by decide +kernel)
  have a5134 := h.atom 5134 (.add (.n 5799) (.n 5798) (.n 5553)) (by decide +kernel)
  have a5135 := h.atom 5135 (.add (.n 5800) (.n 5799) (.n 5572)) (by decide +kernel)
  have a5136 := h.atom 5136 (.add (.n 5801) (.n 5800) (.n 5591)) (by decide +kernel)
  have a5137 := h.atom 5137 (.add (.n 5802) (.n 5801) (.n 5610)) (by decide +kernel)
  have a5138 := h.atom 5138 (.add (.n 5803) (.n 5802) (.n 5629)) (by decide +kernel)
  have a5139 := h.atom 5139 (.add (.n 5804) (.n 5803) (.n 5648)) (by decide +kernel)
  have a5140 := h.atom 5140 (.add (.n 5805) (.n 5804) (.n 5667)) (by decide +kernel)
  have a5141 := h.atom 5141 (.add (.n 5806) (.n 5805) (.n 5686)) (by decide +kernel)
  have a5142 := h.atom 5142 (.add (.n 5807) (.n 5806) (.n 5705)) (by decide +kernel)
  have a5143 := h.atom 5143 (.add (.n 5808) (.n 5807) (.n 5724)) (by decide +kernel)
  have a5144 := h.atom 5144 (.add (.n 5809) (.n 5808) (.n 5743)) (by decide +kernel)
  have a5145 := h.atom 5145 (.add (.n 5810) (.n 5809) (.n 5762)) (by decide +kernel)
  have a5146 := h.atom 5146 (.mul (.n 5811) (.n 2716) (.n 5810)) (by decide +kernel)
  have a5147 := h.atom 5147 (.add (.n 5812) (.n 5784) (.n 5811)) (by decide +kernel)
  have a5148 := h.atom 5148 (.const (.n 5813) (word 1 0 0)) (by decide +kernel)
  have a5149 := h.atom 5149 (.add (.n 5814) (.n 5813) (.n 5761)) (by decide +kernel)
  have a5150 := h.atom 5150 (.add (.n 5815) (.n 5812) (.n 5814)) (by decide +kernel)
  have a5151 := h.atom 5151 (.add (.n 5816) (.n 5815) (.n 29)) (by decide +kernel)
  simp only [Atom.Holds] at a5098 a5099 a5100 a5101 a5102 a5103 a5104 a5105 a5106 a5107
  simp only [Atom.Holds] at a5108 a5109 a5110 a5111 a5112 a5113 a5114 a5115 a5116 a5117
  simp only [Atom.Holds] at a5118 a5119 a5120 a5121 a5122 a5123 a5124 a5125 a5126 a5127
  simp only [Atom.Holds] at a5128 a5129 a5130 a5131 a5132 a5133 a5134 a5135 a5136 a5137
  simp only [Atom.Holds] at a5138 a5139 a5140 a5141 a5142 a5143 a5144 a5145 a5146 a5147
  simp only [Atom.Holds] at a5148 a5149 a5150 a5151
  simp only [a5098, a5099, a5100, a5101, a5102, a5103, a5104, a5105, a5106, a5107, a5108, a5109, a5110,
    a5111, a5112, a5113, a5114, a5115, a5116, a5117, a5118, a5119, a5120, a5121, a5122, a5123,
    a5124, a5125, a5126, a5127, a5128, a5129, a5130, a5131, a5132, a5133, a5134, a5135, a5136,
    a5137, a5138, a5139, a5140, a5141, a5142, a5143, a5144, a5145, a5146, a5147, a5148, a5149,
    a5150, a5151]
  simp (config := { decide := true }) only [vtPadSum, vtPadTable, vtCountPadData, vtPadV,
    List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    ↓reduceIte, add_zero, mul_one]
  rw [tb_word_one]
  ring

end
end LeanVM.Guest.B1.Tables
