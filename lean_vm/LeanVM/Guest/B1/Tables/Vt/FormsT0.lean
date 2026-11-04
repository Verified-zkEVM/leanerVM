/-
  LeanVM.Guest.B1.Tables.Vt.FormsT0

  Table 0's forms on the three sides, from the guest's statements: each block's value from its
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
theorem vtB00_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2829) = σ (.n 952) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2825 [
    .atom (.load (.n 2819) (.n 13) 0),
    .atom (.const (.n 2820) (word 2 0 0)),
    .atom (.mul (.n 2821) (.n 2820) (.n 2625)),
    .atom (.load (.n 2822) (.n 13) 1),
    .atom (.mul (.n 2823) (.n 2822) (.n 2821)),
    .atom (.add (.n 2824) (.n 2819) (.n 2823)),
    .atom (.load (.n 2825) (.n 13) 2),
    .atom (.mul (.n 2826) (.n 2825) (.n 2636)),
    .atom (.add (.n 2827) (.n 2824) (.n 2826)),
    .atom (.add (.n 2828) (.n 14) (.n 2827)),
    .atom (.mul (.n 2829) (.n 952) (.n 2828))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2825, a2826, a2827, a2828, a2829, a2830, a2831, a2832, a2833, a2834, a2835, -⟩ := hs
  have e2825 := tb_loadHolds_unique a2825 (hw 0 (by norm_num))
  have e2828 := tb_loadHolds_unique a2828 (hw 1 (by norm_num))
  have e2831 := tb_loadHolds_unique a2831 (hw 2 (by norm_num))
  have v2625 : σ (.n 2625) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 0) (by norm_num)).2.2
  have v2636 : σ (.n 2636) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2
  have hB : σ (.n 2828) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v2636, v2625, a2834, a2833, a2832, e2831, a2830, a2829, e2828, a2827, a2826, e2825]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2835, hB]

set_option maxRecDepth 10000 in
theorem vtB00_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2862) = σ (.n 2829) + σ (.n 957) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([14], 2)], [([], 1)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2836 [
    .atom (.load (.n 2830) (.n 13) 0),
    .atom (.const (.n 2831) (word 4 0 0)),
    .atom (.mul (.n 2832) (.n 2830) (.n 2831)),
    .atom (.load (.n 2833) (.n 13) 1),
    .atom (.mul (.n 2834) (.n 2833) (.n 2625)),
    .atom (.add (.n 2835) (.n 2832) (.n 2834)),
    .atom (.const (.n 2836) (word 2 0 0)),
    .atom (.mul (.n 2837) (.n 2836) (.n 2818)),
    .atom (.load (.n 2838) (.n 13) 2),
    .atom (.mul (.n 2839) (.n 2838) (.n 2837)),
    .atom (.add (.n 2840) (.n 2835) (.n 2839)),
    .atom (.load (.n 2841) (.n 13) 3),
    .atom (.add (.n 2842) (.n 2840) (.n 2841)),
    .atom (.load (.n 2843) (.n 13) 4),
    .atom (.mul (.n 2844) (.n 2843) (.n 2647)),
    .atom (.add (.n 2845) (.n 2842) (.n 2844)),
    .atom (.load (.n 2846) (.n 13) 5),
    .atom (.mul (.n 2847) (.n 2846) (.n 2658)),
    .atom (.add (.n 2848) (.n 2845) (.n 2847)),
    .atom (.load (.n 2849) (.n 13) 6),
    .atom (.mul (.n 2850) (.n 2849) (.n 2682)),
    .atom (.add (.n 2851) (.n 2848) (.n 2850)),
    .atom (.load (.n 2852) (.n 13) 7),
    .atom (.const (.n 2853) (word 0 0 0)),
    .atom (.mul (.n 2854) (.n 2852) (.n 2853)),
    .atom (.add (.n 2855) (.n 2851) (.n 2854)),
    .atom (.load (.n 2856) (.n 13) 8),
    .atom (.const (.n 2857) (word 0 0 0)),
    .atom (.mul (.n 2858) (.n 2856) (.n 2857)),
    .atom (.add (.n 2859) (.n 2855) (.n 2858)),
    .atom (.add (.n 2860) (.n 14) (.n 2859)),
    .atom (.mul (.n 2861) (.n 957) (.n 2860)),
    .atom (.add (.n 2862) (.n 2829) (.n 2861))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2836, a2837, a2838, a2839, a2840, a2841, a2842, a2843, a2844, a2845, a2846, a2847, a2848, a2849,
    a2850, a2851, a2852, a2853, a2854, a2855, a2856, a2857, a2858, a2859, a2860, a2861, a2862,
    a2863, a2864, a2865, a2866, a2867, a2868, -⟩ := hs
  have e2836 := tb_loadHolds_unique a2836 (hw 0 (by norm_num))
  have e2839 := tb_loadHolds_unique a2839 (hw 1 (by norm_num))
  have e2844 := tb_loadHolds_unique a2844 (hw 2 (by norm_num))
  have e2847 := tb_loadHolds_unique a2847 (hw 3 (by norm_num))
  have e2849 := tb_loadHolds_unique a2849 (hw 4 (by norm_num))
  have e2852 := tb_loadHolds_unique a2852 (hw 5 (by norm_num))
  have e2855 := tb_loadHolds_unique a2855 (hw 6 (by norm_num))
  have e2858 := tb_loadHolds_unique a2858 (hw 7 (by norm_num))
  have e2862 := tb_loadHolds_unique a2862 (hw 8 (by norm_num))
  have v2625 : σ (.n 2625) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 0) (by norm_num)).2.2
  have v2647 : σ (.n 2647) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 2) (by norm_num)).2.2
  have v2658 : σ (.n 2658) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 3) (by norm_num)).2.2
  have v2682 : σ (.n 2682) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 4) (by norm_num)).2.2
  have v2818 : σ (.n 2818) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 14) (by norm_num)).2.2
  have hB : σ (.n 2860) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([14], 2)], [([], 1)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v2818, v2682, v2658, v2647, v2625, a2866, a2865, a2864, a2863, e2862, a2861, a2860, a2859,
      e2858, a2857, a2856, e2855, a2854, a2853, e2852, a2851, a2850, e2849, a2848, e2847,
      a2846, a2845, e2844, a2843, a2842, a2841, a2840, e2839, a2838, a2837, e2836]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a2868, a2867, hB]

set_option maxRecDepth 10000 in
theorem vtB00_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2886) = σ (.n 2862) + σ (.n 962) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([11], 2)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2869 [
    .atom (.load (.n 2863) (.n 13) 0),
    .atom (.const (.n 2864) (word 2 0 0)),
    .atom (.mul (.n 2865) (.n 2863) (.n 2864)),
    .atom (.mul (.n 2866) (.n 2636) (.n 2647)),
    .atom (.load (.n 2867) (.n 13) 1),
    .atom (.mul (.n 2868) (.n 2867) (.n 2866)),
    .atom (.add (.n 2869) (.n 2865) (.n 2868)),
    .atom (.const (.n 2870) (word 2 0 0)),
    .atom (.mul (.n 2871) (.n 2870) (.n 2772)),
    .atom (.load (.n 2872) (.n 13) 2),
    .atom (.mul (.n 2873) (.n 2872) (.n 2871)),
    .atom (.add (.n 2874) (.n 2869) (.n 2873)),
    .atom (.load (.n 2875) (.n 13) 3),
    .atom (.mul (.n 2876) (.n 2875) (.n 2693)),
    .atom (.add (.n 2877) (.n 2874) (.n 2876)),
    .atom (.load (.n 2878) (.n 13) 4),
    .atom (.mul (.n 2879) (.n 2878) (.n 2704)),
    .atom (.add (.n 2880) (.n 2877) (.n 2879)),
    .atom (.load (.n 2881) (.n 13) 5),
    .atom (.mul (.n 2882) (.n 2881) (.n 2715)),
    .atom (.add (.n 2883) (.n 2880) (.n 2882)),
    .atom (.add (.n 2884) (.n 14) (.n 2883)),
    .atom (.mul (.n 2885) (.n 962) (.n 2884)),
    .atom (.add (.n 2886) (.n 2862) (.n 2885))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2869, a2870, a2871, a2872, a2873, a2874, a2875, a2876, a2877, a2878, a2879, a2880, a2881, a2882,
    a2883, a2884, a2885, a2886, a2887, a2888, a2889, a2890, a2891, a2892, -⟩ := hs
  have e2869 := tb_loadHolds_unique a2869 (hw 0 (by norm_num))
  have e2873 := tb_loadHolds_unique a2873 (hw 1 (by norm_num))
  have e2878 := tb_loadHolds_unique a2878 (hw 2 (by norm_num))
  have e2881 := tb_loadHolds_unique a2881 (hw 3 (by norm_num))
  have e2884 := tb_loadHolds_unique a2884 (hw 4 (by norm_num))
  have e2887 := tb_loadHolds_unique a2887 (hw 5 (by norm_num))
  have v2636 : σ (.n 2636) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2
  have v2647 : σ (.n 2647) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 2) (by norm_num)).2.2
  have v2693 : σ (.n 2693) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 5) (by norm_num)).2.2
  have v2704 : σ (.n 2704) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 6) (by norm_num)).2.2
  have v2715 : σ (.n 2715) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 7) (by norm_num)).2.2
  have v2772 : σ (.n 2772) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 11) (by norm_num)).2.2
  have hB : σ (.n 2884) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([11], 2)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
    simp only [v2772, v2715, v2704, v2693, v2647, v2636, a2890, a2889, a2888, e2887, a2886, a2885, e2884,
      a2883, a2882, e2881, a2880, a2879, e2878, a2877, a2876, a2875, a2874, e2873, a2872,
      a2871, a2870, e2869]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2892, a2891, hB]

set_option maxRecDepth 10000 in
theorem vtB00_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2910) = σ (.n 2886) + σ (.n 967) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([12], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2893 [
    .atom (.load (.n 2887) (.n 13) 0),
    .atom (.const (.n 2888) (word 2 0 0)),
    .atom (.mul (.n 2889) (.n 2887) (.n 2888)),
    .atom (.mul (.n 2890) (.n 2636) (.n 2658)),
    .atom (.load (.n 2891) (.n 13) 1),
    .atom (.mul (.n 2892) (.n 2891) (.n 2890)),
    .atom (.add (.n 2893) (.n 2889) (.n 2892)),
    .atom (.const (.n 2894) (word 2 0 0)),
    .atom (.mul (.n 2895) (.n 2894) (.n 2796)),
    .atom (.load (.n 2896) (.n 13) 2),
    .atom (.mul (.n 2897) (.n 2896) (.n 2895)),
    .atom (.add (.n 2898) (.n 2893) (.n 2897)),
    .atom (.load (.n 2899) (.n 13) 3),
    .atom (.mul (.n 2900) (.n 2899) (.n 2739)),
    .atom (.add (.n 2901) (.n 2898) (.n 2900)),
    .atom (.load (.n 2902) (.n 13) 4),
    .atom (.mul (.n 2903) (.n 2902) (.n 2750)),
    .atom (.add (.n 2904) (.n 2901) (.n 2903)),
    .atom (.load (.n 2905) (.n 13) 5),
    .atom (.mul (.n 2906) (.n 2905) (.n 2761)),
    .atom (.add (.n 2907) (.n 2904) (.n 2906)),
    .atom (.add (.n 2908) (.n 14) (.n 2907)),
    .atom (.mul (.n 2909) (.n 967) (.n 2908)),
    .atom (.add (.n 2910) (.n 2886) (.n 2909))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2893, a2894, a2895, a2896, a2897, a2898, a2899, a2900, a2901, a2902, a2903, a2904, a2905, a2906,
    a2907, a2908, a2909, a2910, a2911, a2912, a2913, a2914, a2915, a2916, -⟩ := hs
  have e2893 := tb_loadHolds_unique a2893 (hw 0 (by norm_num))
  have e2897 := tb_loadHolds_unique a2897 (hw 1 (by norm_num))
  have e2902 := tb_loadHolds_unique a2902 (hw 2 (by norm_num))
  have e2905 := tb_loadHolds_unique a2905 (hw 3 (by norm_num))
  have e2908 := tb_loadHolds_unique a2908 (hw 4 (by norm_num))
  have e2911 := tb_loadHolds_unique a2911 (hw 5 (by norm_num))
  have v2636 : σ (.n 2636) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2
  have v2658 : σ (.n 2658) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 3) (by norm_num)).2.2
  have v2739 : σ (.n 2739) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 8) (by norm_num)).2.2
  have v2750 : σ (.n 2750) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 9) (by norm_num)).2.2
  have v2761 : σ (.n 2761) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 10) (by norm_num)).2.2
  have v2796 : σ (.n 2796) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 12) (by norm_num)).2.2
  have hB : σ (.n 2908) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([12], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
    simp only [v2796, v2761, v2750, v2739, v2658, v2636, a2914, a2913, a2912, e2911, a2910, a2909, e2908,
      a2907, a2906, e2905, a2904, a2903, e2902, a2901, a2900, a2899, a2898, e2897, a2896,
      a2895, a2894, e2893]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2916, a2915, hB]

set_option maxRecDepth 10000 in
theorem vtB00_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2937) = σ (.n 2910) + σ (.n 972) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([13], 2)], [([5], 1), ([8], 1)], [([6], 1), ([9], 1)], [([7], 1), ([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2917 [
    .atom (.load (.n 2911) (.n 13) 0),
    .atom (.const (.n 2912) (word 2 0 0)),
    .atom (.mul (.n 2913) (.n 2911) (.n 2912)),
    .atom (.mul (.n 2914) (.n 2636) (.n 2682)),
    .atom (.load (.n 2915) (.n 13) 1),
    .atom (.mul (.n 2916) (.n 2915) (.n 2914)),
    .atom (.add (.n 2917) (.n 2913) (.n 2916)),
    .atom (.const (.n 2918) (word 2 0 0)),
    .atom (.mul (.n 2919) (.n 2918) (.n 2807)),
    .atom (.load (.n 2920) (.n 13) 2),
    .atom (.mul (.n 2921) (.n 2920) (.n 2919)),
    .atom (.add (.n 2922) (.n 2917) (.n 2921)),
    .atom (.add (.n 2923) (.n 2693) (.n 2739)),
    .atom (.load (.n 2924) (.n 13) 3),
    .atom (.mul (.n 2925) (.n 2924) (.n 2923)),
    .atom (.add (.n 2926) (.n 2922) (.n 2925)),
    .atom (.add (.n 2927) (.n 2704) (.n 2750)),
    .atom (.load (.n 2928) (.n 13) 4),
    .atom (.mul (.n 2929) (.n 2928) (.n 2927)),
    .atom (.add (.n 2930) (.n 2926) (.n 2929)),
    .atom (.add (.n 2931) (.n 2715) (.n 2761)),
    .atom (.load (.n 2932) (.n 13) 5),
    .atom (.mul (.n 2933) (.n 2932) (.n 2931)),
    .atom (.add (.n 2934) (.n 2930) (.n 2933)),
    .atom (.add (.n 2935) (.n 14) (.n 2934)),
    .atom (.mul (.n 2936) (.n 972) (.n 2935)),
    .atom (.add (.n 2937) (.n 2910) (.n 2936))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2917, a2918, a2919, a2920, a2921, a2922, a2923, a2924, a2925, a2926, a2927, a2928, a2929, a2930,
    a2931, a2932, a2933, a2934, a2935, a2936, a2937, a2938, a2939, a2940, a2941, a2942, a2943, -⟩ := hs
  have e2917 := tb_loadHolds_unique a2917 (hw 0 (by norm_num))
  have e2921 := tb_loadHolds_unique a2921 (hw 1 (by norm_num))
  have e2926 := tb_loadHolds_unique a2926 (hw 2 (by norm_num))
  have e2930 := tb_loadHolds_unique a2930 (hw 3 (by norm_num))
  have e2934 := tb_loadHolds_unique a2934 (hw 4 (by norm_num))
  have e2938 := tb_loadHolds_unique a2938 (hw 5 (by norm_num))
  have v2636 : σ (.n 2636) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2
  have v2682 : σ (.n 2682) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 4) (by norm_num)).2.2
  have v2693 : σ (.n 2693) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 5) (by norm_num)).2.2
  have v2704 : σ (.n 2704) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 6) (by norm_num)).2.2
  have v2715 : σ (.n 2715) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 7) (by norm_num)).2.2
  have v2739 : σ (.n 2739) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 8) (by norm_num)).2.2
  have v2750 : σ (.n 2750) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 9) (by norm_num)).2.2
  have v2761 : σ (.n 2761) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 10) (by norm_num)).2.2
  have v2807 : σ (.n 2807) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 13) (by norm_num)).2.2
  have hB : σ (.n 2935) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([13], 2)], [([5], 1), ([8], 1)], [([6], 1), ([9], 1)], [([7], 1), ([10], 1)]] := by
    simp only [v2807, v2761, v2750, v2739, v2715, v2704, v2693, v2682, v2636, a2941, a2940, a2939, e2938,
      a2937, a2936, a2935, e2934, a2933, a2932, a2931, e2930, a2929, a2928, a2927, e2926,
      a2925, a2924, a2923, a2922, e2921, a2920, a2919, a2918, e2917]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2943, a2942, hB]

set_option maxRecDepth 10000 in
theorem vtSide00 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2937) =
      vtSideVal [σ (.n 952), σ (.n 957), σ (.n 962), σ (.n 967), σ (.n 972)]
        (σ (.n 14)) W ev vtBTerms00 := by
  rw [vtB00_4 h hw hev, vtB00_3 h hw hev, vtB00_2 h hw hev, vtB00_1 h hw hev, vtB00_0 h hw hev]
  simp only [vtSideVal, vtBTerms00, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD0_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2943) = σ (.n 1952) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2945 [
    .atom (.const (.n 2939) (word 3 0 0)),
    .atom (.mul (.n 2940) (.n 2939) (.n 2625)),
    .atom (.load (.n 2941) (.n 13) 1),
    .atom (.mul (.n 2942) (.n 2941) (.n 2940)),
    .atom (.mul (.n 2943) (.n 1952) (.n 2942))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2945, a2946, a2947, a2948, a2949, -⟩ := hs
  have e2947 := tb_loadHolds_unique a2947 (hw 1 (by norm_num))
  have v2625 : σ (.n 2625) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 0) (by norm_num)).2.2
  have hB : σ (.n 2942) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v2625, a2948, e2947, a2946, a2945]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2949, hB]

set_option maxRecDepth 10000 in
theorem vtD0_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2949) = σ (.n 2943) + σ (.n 1954) * vtSlots W ev 0
      [[], [], [([14], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2950 [
    .atom (.const (.n 2944) (word 3 0 0)),
    .atom (.mul (.n 2945) (.n 2944) (.n 2818)),
    .atom (.load (.n 2946) (.n 13) 2),
    .atom (.mul (.n 2947) (.n 2946) (.n 2945)),
    .atom (.mul (.n 2948) (.n 1954) (.n 2947)),
    .atom (.add (.n 2949) (.n 2943) (.n 2948))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2950, a2951, a2952, a2953, a2954, a2955, -⟩ := hs
  have e2952 := tb_loadHolds_unique a2952 (hw 2 (by norm_num))
  have v2818 : σ (.n 2818) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 14) (by norm_num)).2.2
  have hB : σ (.n 2947) = vtSlots W ev 0 [[], [], [([14], 3)], [], [], [], [], [], []] := by
    simp only [v2818, a2953, e2952, a2951, a2950]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2955, a2954, hB]

set_option maxRecDepth 10000 in
theorem vtD0_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2955) = σ (.n 2949) + σ (.n 1956) * vtSlots W ev 0
      [[], [], [([11], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2956 [
    .atom (.const (.n 2950) (word 3 0 0)),
    .atom (.mul (.n 2951) (.n 2950) (.n 2772)),
    .atom (.load (.n 2952) (.n 13) 2),
    .atom (.mul (.n 2953) (.n 2952) (.n 2951)),
    .atom (.mul (.n 2954) (.n 1956) (.n 2953)),
    .atom (.add (.n 2955) (.n 2949) (.n 2954))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2956, a2957, a2958, a2959, a2960, a2961, -⟩ := hs
  have e2958 := tb_loadHolds_unique a2958 (hw 2 (by norm_num))
  have v2772 : σ (.n 2772) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 11) (by norm_num)).2.2
  have hB : σ (.n 2953) = vtSlots W ev 0 [[], [], [([11], 3)], [], [], []] := by
    simp only [v2772, a2959, e2958, a2957, a2956]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2961, a2960, hB]

set_option maxRecDepth 10000 in
theorem vtD0_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2961) = σ (.n 2955) + σ (.n 1958) * vtSlots W ev 0
      [[], [], [([12], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2962 [
    .atom (.const (.n 2956) (word 3 0 0)),
    .atom (.mul (.n 2957) (.n 2956) (.n 2796)),
    .atom (.load (.n 2958) (.n 13) 2),
    .atom (.mul (.n 2959) (.n 2958) (.n 2957)),
    .atom (.mul (.n 2960) (.n 1958) (.n 2959)),
    .atom (.add (.n 2961) (.n 2955) (.n 2960))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2962, a2963, a2964, a2965, a2966, a2967, -⟩ := hs
  have e2964 := tb_loadHolds_unique a2964 (hw 2 (by norm_num))
  have v2796 : σ (.n 2796) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 12) (by norm_num)).2.2
  have hB : σ (.n 2959) = vtSlots W ev 0 [[], [], [([12], 3)], [], [], []] := by
    simp only [v2796, a2965, e2964, a2963, a2962]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2967, a2966, hB]

set_option maxRecDepth 10000 in
theorem vtD0_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2967) = σ (.n 2961) + σ (.n 1960) * vtSlots W ev 0
      [[], [], [([13], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2968 [
    .atom (.const (.n 2962) (word 3 0 0)),
    .atom (.mul (.n 2963) (.n 2962) (.n 2807)),
    .atom (.load (.n 2964) (.n 13) 2),
    .atom (.mul (.n 2965) (.n 2964) (.n 2963)),
    .atom (.mul (.n 2966) (.n 1960) (.n 2965)),
    .atom (.add (.n 2967) (.n 2961) (.n 2966))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2968, a2969, a2970, a2971, a2972, a2973, -⟩ := hs
  have e2970 := tb_loadHolds_unique a2970 (hw 2 (by norm_num))
  have v2807 : σ (.n 2807) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 13) (by norm_num)).2.2
  have hB : σ (.n 2965) = vtSlots W ev 0 [[], [], [([13], 3)], [], [], []] := by
    simp only [v2807, a2971, e2970, a2969, a2968]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2973, a2972, hB]

set_option maxRecDepth 10000 in
theorem vtSide10 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2968) =
      vtSideVal [σ (.n 1952), σ (.n 1954), σ (.n 1956), σ (.n 1958), σ (.n 1960)]
        (σ (.n 14)) W ev vtBTerms10 := by
  have hF0 : σ (.n 2937) =
      vtSideVal [σ (.n 1952), σ (.n 1954), σ (.n 1956), σ (.n 1958), σ (.n 1960)]
        (σ (.n 14)) W ev vtBTerms00 := by
    rw [vtPullSels0 h]; exact vtSide00 h hw hev
  have a2974 := h.atomAt 2974 (.add (.n 2968) (.n 2937) (.n 2967)) (by decide +kernel)
  simp only [Atom.Holds] at a2974
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull0, ← hF0, a2974, vtD0_4 h hw hev, vtD0_3 h hw hev, vtD0_2 h hw hev, vtD0_1 h hw hev, vtD0_0 h hw hev]
  simp only [vtDiffSum, vtDTerms0, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide20 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2977) =
      vtSideVal [σ (.n 2061), σ (.n 2066), σ (.n 2071), σ (.n 2076)]
        (0) (fun _ ↦ 1) ev vtBTerms20 := by
  obtain ⟨_, hs⟩ := h.sliceAt 2977 [
    .atom (.mul (.n 2971) (.n 2061) (.n 2772)),
    .atom (.mul (.n 2972) (.n 2066) (.n 2796)),
    .atom (.add (.n 2973) (.n 2971) (.n 2972)),
    .atom (.mul (.n 2974) (.n 2071) (.n 2807)),
    .atom (.add (.n 2975) (.n 2973) (.n 2974)),
    .atom (.mul (.n 2976) (.n 2076) (.n 2818)),
    .atom (.add (.n 2977) (.n 2975) (.n 2976))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2977, a2978, a2979, a2980, a2981, a2982, a2983, -⟩ := hs
  have v2772 : σ (.n 2772) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 11) (by norm_num)).2.2
  have v2796 : σ (.n 2796) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 12) (by norm_num)).2.2
  have v2807 : σ (.n 2807) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 13) (by norm_num)).2.2
  have v2818 : σ (.n 2818) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 14) (by norm_num)).2.2
  rw [a2983, a2981, a2979, a2977, a2978, a2980, a2982, v2772, v2796, v2807, v2818]
  simp only [vtSideVal, vtBTerms20, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
