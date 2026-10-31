/-
  LeanVM.Guest.B1.Tables.Vt.PushFw

  `verify_tables`' push side's framework blocks: their fingerprints' accumulator, the three
  memory words read from the stream and pooled, and the index MLE values.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.PushPad

/-!
# The push side's framework blocks (G:2077-2125)

`vt_push_fw`: the accumulator after the state, memory and bytecode blocks is
`Σ_f eq_f·(β + fp_f)` with the state fingerprint `w0 + w1 + w2`, the memory one
`w0·g + w1·idx + w2 + w3·m0 + w4·m1 + w5·m2` and the bytecode one `w0·g² + w1·idx' + w2 + bv`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The push side's framework accumulator.** -/
theorem vt_push_fw {rd : Reader} {σ : Val} (h : VtH rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i)) :
    σ (.n 3036) = σ (.n 2870) * (σ (.n 15) + (W 0 + W 1 + W 2)) +
      σ (.n 2900) * (σ (.n 15) + (W 0 * gen + W 1 * σ (.n 2908) + W 2 + W 3 * σ (.n 2914) +
        W 4 * σ (.n 2927) + W 5 * σ (.n 2940))) +
      σ (.n 2975) * (σ (.n 15) + (W 0 * gen ^ 2 + W 1 * σ (.n 2983) + W 2 + σ (.n 2639))) := by
  have a2424 := h.atomAt 2424 (.load (.n 2874) (.n 14) 0) (by decide +kernel)
  have a2425 := h.atomAt 2425 (.load (.n 2875) (.n 14) 1) (by decide +kernel)
  have a2426 := h.atomAt 2426 (.add (.n 2876) (.n 2874) (.n 2875)) (by decide +kernel)
  have a2427 := h.atomAt 2427 (.load (.n 2877) (.n 14) 2) (by decide +kernel)
  have a2428 := h.atomAt 2428 (.add (.n 2878) (.n 2876) (.n 2877)) (by decide +kernel)
  have a2429 := h.atomAt 2429 (.const (.n 2879) (word 0 0 0)) (by decide +kernel)
  have a2430 := h.atomAt 2430 (.mul (.n 2880) (.n 2879) (.n 2639)) (by decide +kernel)
  have a2431 := h.atomAt 2431 (.add (.n 2881) (.n 2878) (.n 2880)) (by decide +kernel)
  have a2432 := h.atomAt 2432 (.add (.n 2882) (.n 15) (.n 2881)) (by decide +kernel)
  have a2433 := h.atomAt 2433 (.mul (.n 2883) (.n 2870) (.n 2882)) (by decide +kernel)
  have a2452 := h.atomAt 2452 (.load (.n 2905) (.n 14) 0) (by decide +kernel)
  have a2453 := h.atomAt 2453 (.const (.n 2906) (word 2 0 0)) (by decide +kernel)
  have a2454 := h.atomAt 2454 (.mul (.n 2907) (.n 2905) (.n 2906)) (by decide +kernel)
  have a2457 := h.atomAt 2457 (.load (.n 2909) (.n 14) 1) (by decide +kernel)
  have a2458 := h.atomAt 2458 (.mul (.n 2910) (.n 2909) (.n 2908)) (by decide +kernel)
  have a2459 := h.atomAt 2459 (.add (.n 2911) (.n 2907) (.n 2910)) (by decide +kernel)
  have a2460 := h.atomAt 2460 (.load (.n 2912) (.n 14) 2) (by decide +kernel)
  have a2461 := h.atomAt 2461 (.add (.n 2913) (.n 2911) (.n 2912)) (by decide +kernel)
  have a2473 := h.atomAt 2473 (.load (.n 2924) (.n 14) 3) (by decide +kernel)
  have a2474 := h.atomAt 2474 (.mul (.n 2925) (.n 2924) (.n 2914)) (by decide +kernel)
  have a2475 := h.atomAt 2475 (.add (.n 2926) (.n 2913) (.n 2925)) (by decide +kernel)
  have a2487 := h.atomAt 2487 (.load (.n 2937) (.n 14) 4) (by decide +kernel)
  have a2488 := h.atomAt 2488 (.mul (.n 2938) (.n 2937) (.n 2927)) (by decide +kernel)
  have a2489 := h.atomAt 2489 (.add (.n 2939) (.n 2926) (.n 2938)) (by decide +kernel)
  have a2501 := h.atomAt 2501 (.load (.n 2950) (.n 14) 5) (by decide +kernel)
  have a2502 := h.atomAt 2502 (.mul (.n 2951) (.n 2950) (.n 2940)) (by decide +kernel)
  have a2503 := h.atomAt 2503 (.add (.n 2952) (.n 2939) (.n 2951)) (by decide +kernel)
  have a2504 := h.atomAt 2504 (.const (.n 2953) (word 0 0 0)) (by decide +kernel)
  have a2505 := h.atomAt 2505 (.mul (.n 2954) (.n 2953) (.n 2639)) (by decide +kernel)
  have a2506 := h.atomAt 2506 (.add (.n 2955) (.n 2952) (.n 2954)) (by decide +kernel)
  have a2507 := h.atomAt 2507 (.add (.n 2956) (.n 15) (.n 2955)) (by decide +kernel)
  have a2508 := h.atomAt 2508 (.mul (.n 2957) (.n 2900) (.n 2956)) (by decide +kernel)
  have a2509 := h.atomAt 2509 (.add (.n 2958) (.n 2883) (.n 2957)) (by decide +kernel)
  have a2528 := h.atomAt 2528 (.load (.n 2980) (.n 14) 0) (by decide +kernel)
  have a2529 := h.atomAt 2529 (.const (.n 2981) (word 4 0 0)) (by decide +kernel)
  have a2530 := h.atomAt 2530 (.mul (.n 2982) (.n 2980) (.n 2981)) (by decide +kernel)
  have a2533 := h.atomAt 2533 (.load (.n 2984) (.n 14) 1) (by decide +kernel)
  have a2534 := h.atomAt 2534 (.mul (.n 2985) (.n 2984) (.n 2983)) (by decide +kernel)
  have a2535 := h.atomAt 2535 (.add (.n 2986) (.n 2982) (.n 2985)) (by decide +kernel)
  have a2536 := h.atomAt 2536 (.load (.n 2987) (.n 14) 2) (by decide +kernel)
  have a2537 := h.atomAt 2537 (.add (.n 2988) (.n 2986) (.n 2987)) (by decide +kernel)
  have a2538 := h.atomAt 2538 (.load (.n 2989) (.n 14) 3) (by decide +kernel)
  have a2539 := h.atomAt 2539 (.const (.n 2990) (word 0 0 0)) (by decide +kernel)
  have a2540 := h.atomAt 2540 (.mul (.n 2991) (.n 2989) (.n 2990)) (by decide +kernel)
  have a2541 := h.atomAt 2541 (.add (.n 2992) (.n 2988) (.n 2991)) (by decide +kernel)
  have a2542 := h.atomAt 2542 (.load (.n 2993) (.n 14) 4) (by decide +kernel)
  have a2543 := h.atomAt 2543 (.const (.n 2994) (word 0 0 0)) (by decide +kernel)
  have a2544 := h.atomAt 2544 (.mul (.n 2995) (.n 2993) (.n 2994)) (by decide +kernel)
  have a2545 := h.atomAt 2545 (.add (.n 2996) (.n 2992) (.n 2995)) (by decide +kernel)
  have a2546 := h.atomAt 2546 (.load (.n 2997) (.n 14) 5) (by decide +kernel)
  have a2547 := h.atomAt 2547 (.const (.n 2998) (word 0 0 0)) (by decide +kernel)
  have a2548 := h.atomAt 2548 (.mul (.n 2999) (.n 2997) (.n 2998)) (by decide +kernel)
  have a2549 := h.atomAt 2549 (.add (.n 3000) (.n 2996) (.n 2999)) (by decide +kernel)
  have a2550 := h.atomAt 2550 (.load (.n 3001) (.n 14) 6) (by decide +kernel)
  have a2551 := h.atomAt 2551 (.const (.n 3002) (word 0 0 0)) (by decide +kernel)
  have a2552 := h.atomAt 2552 (.mul (.n 3003) (.n 3001) (.n 3002)) (by decide +kernel)
  have a2553 := h.atomAt 2553 (.add (.n 3004) (.n 3000) (.n 3003)) (by decide +kernel)
  have a2554 := h.atomAt 2554 (.load (.n 3005) (.n 14) 7) (by decide +kernel)
  have a2555 := h.atomAt 2555 (.const (.n 3006) (word 0 0 0)) (by decide +kernel)
  have a2556 := h.atomAt 2556 (.mul (.n 3007) (.n 3005) (.n 3006)) (by decide +kernel)
  have a2557 := h.atomAt 2557 (.add (.n 3008) (.n 3004) (.n 3007)) (by decide +kernel)
  have a2558 := h.atomAt 2558 (.load (.n 3009) (.n 14) 8) (by decide +kernel)
  have a2559 := h.atomAt 2559 (.const (.n 3010) (word 0 0 0)) (by decide +kernel)
  have a2560 := h.atomAt 2560 (.mul (.n 3011) (.n 3009) (.n 3010)) (by decide +kernel)
  have a2561 := h.atomAt 2561 (.add (.n 3012) (.n 3008) (.n 3011)) (by decide +kernel)
  have a2562 := h.atomAt 2562 (.load (.n 3013) (.n 14) 9) (by decide +kernel)
  have a2563 := h.atomAt 2563 (.const (.n 3014) (word 0 0 0)) (by decide +kernel)
  have a2564 := h.atomAt 2564 (.mul (.n 3015) (.n 3013) (.n 3014)) (by decide +kernel)
  have a2565 := h.atomAt 2565 (.add (.n 3016) (.n 3012) (.n 3015)) (by decide +kernel)
  have a2566 := h.atomAt 2566 (.load (.n 3017) (.n 14) 10) (by decide +kernel)
  have a2567 := h.atomAt 2567 (.const (.n 3018) (word 0 0 0)) (by decide +kernel)
  have a2568 := h.atomAt 2568 (.mul (.n 3019) (.n 3017) (.n 3018)) (by decide +kernel)
  have a2569 := h.atomAt 2569 (.add (.n 3020) (.n 3016) (.n 3019)) (by decide +kernel)
  have a2570 := h.atomAt 2570 (.load (.n 3021) (.n 14) 11) (by decide +kernel)
  have a2571 := h.atomAt 2571 (.const (.n 3022) (word 0 0 0)) (by decide +kernel)
  have a2572 := h.atomAt 2572 (.mul (.n 3023) (.n 3021) (.n 3022)) (by decide +kernel)
  have a2573 := h.atomAt 2573 (.add (.n 3024) (.n 3020) (.n 3023)) (by decide +kernel)
  have a2574 := h.atomAt 2574 (.load (.n 3025) (.n 14) 12) (by decide +kernel)
  have a2575 := h.atomAt 2575 (.const (.n 3026) (word 0 0 0)) (by decide +kernel)
  have a2576 := h.atomAt 2576 (.mul (.n 3027) (.n 3025) (.n 3026)) (by decide +kernel)
  have a2577 := h.atomAt 2577 (.add (.n 3028) (.n 3024) (.n 3027)) (by decide +kernel)
  have a2578 := h.atomAt 2578 (.load (.n 3029) (.n 14) 13) (by decide +kernel)
  have a2579 := h.atomAt 2579 (.const (.n 3030) (word 0 0 0)) (by decide +kernel)
  have a2580 := h.atomAt 2580 (.mul (.n 3031) (.n 3029) (.n 3030)) (by decide +kernel)
  have a2581 := h.atomAt 2581 (.add (.n 3032) (.n 3028) (.n 3031)) (by decide +kernel)
  have a2582 := h.atomAt 2582 (.add (.n 3033) (.n 3032) (.n 2639)) (by decide +kernel)
  have a2583 := h.atomAt 2583 (.add (.n 3034) (.n 15) (.n 3033)) (by decide +kernel)
  have a2584 := h.atomAt 2584 (.mul (.n 3035) (.n 2975) (.n 3034)) (by decide +kernel)
  have a2585 := h.atomAt 2585 (.add (.n 3036) (.n 2958) (.n 3035)) (by decide +kernel)
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

end
end LeanVM.Guest.B1.Tables
