/-
  LeanVM.Guest.Memory.GuestCntVM.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVM.Part00
public import LeanVM.Guest.Memory.GuestCntVM.Part01
public import LeanVM.Guest.Memory.GuestCntVM.Part02
public import LeanVM.Guest.Memory.GuestCntVM.Part03
public import LeanVM.Guest.Memory.GuestCntVM.Part04
public import LeanVM.Guest.Memory.GuestCntVM.Part05
public import LeanVM.Guest.Memory.GuestCntVM.Part06
public import LeanVM.Guest.Memory.GuestCntVM.Part07
public import LeanVM.Guest.Memory.GuestCntVM.Part08
public import LeanVM.Guest.Memory.GuestCntVM.Part09
public import LeanVM.Guest.Memory.GuestCntVM.Part10
public import LeanVM.Guest.Memory.GuestCntVM.Part11
public import LeanVM.Guest.Memory.GuestCntVM.Part12
public import LeanVM.Guest.Memory.GuestCntVM.Part13
public import LeanVM.Guest.Memory.GuestCntVM.Part14
public import LeanVM.Guest.Memory.GuestCntVM.Part15
public import LeanVM.Guest.Memory.GuestCntVM.Part16
public import LeanVM.Guest.Memory.GuestCntVM.Part17
public import LeanVM.Guest.Memory.GuestCntVM.Part18
public import LeanVM.Guest.Memory.GuestCntVM.Part19
public import LeanVM.Guest.Memory.GuestCntVM.Part20
public import LeanVM.Guest.Memory.GuestCntVM.Part21
public import LeanVM.Guest.Memory.GuestCntVM.Part22
public import LeanVM.Guest.Memory.GuestCntVM.Part23
public import LeanVM.Guest.Memory.GuestCntVM.Part24
public import LeanVM.Guest.Memory.GuestCntVM.Part25
public import LeanVM.Guest.Memory.GuestCntVM.Part26
public import LeanVM.Guest.Memory.GuestCntVM.Part27
public import LeanVM.Guest.Memory.GuestCntVM.Part28
public import LeanVM.Guest.Memory.GuestCntVM.Part29
public import LeanVM.Guest.Memory.GuestCntVM.Part30
public import LeanVM.Guest.Memory.GuestCntVM.Part31
public import LeanVM.Guest.Memory.GuestCntVM.Part32
public import LeanVM.Guest.Memory.GuestCntVM.Part33
public import LeanVM.Guest.Memory.GuestCntVM.Part34
public import LeanVM.Guest.Memory.GuestCntVM.Part35
public import LeanVM.Guest.Memory.GuestCntVM.Part36
public import LeanVM.Guest.Memory.GuestCntVM.Part37
public import LeanVM.Guest.Memory.GuestCntVM.Part38
public import LeanVM.Guest.Memory.GuestCntVM.Part39
public import LeanVM.Guest.Memory.GuestCntVM.Part40
public import LeanVM.Guest.Memory.GuestCntVM.Part41
public import LeanVM.Guest.Memory.GuestCntVM.Part42
public import LeanVM.Guest.Memory.GuestCntVM.Part43

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmchkIdx_307 : kvmchkIdx 307 = true := by
  have hb : blockB (kvmlookJ 307) (kvmomLookJ 307) false [(.n 347, 0), (.n 348, 25), (.n 396, 112), (.n 584, 0), (.n 585, 7), (.n 638, 56), (.n 826, 0), (.n 827, 4), (.n 878, 32), (.n 1066, 0), (.n 1067, 3), (.n 1120, 23), (.n 1206, 0), (.n 1207, 2), (.n 1258, 18), (.n 1922, 0), (.n 1923, 28), (.n 1936, 0), (.n 1937, 7), (.n 1950, 0), (.n 1951, 4), (.n 1964, 0), (.n 1965, 2), (.n 2307, 0), (.n 2308, 2)] Data.core307.params Data.core307.name ([], []) Data.core307.body = some (⟨60236, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core307.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_307_0.1 rfl kvmsplit_307_0.2.2,
      ← blockR_eq ((Data.core307.body.drop 0).take 1320), kvmsplit_307_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_307_1320.1 rfl kvmsplit_307_1320.2.2,
      ← blockR_eq ((Data.core307.body.drop 1320).take 1320), kvmsplit_307_1320.2.1]
    rw [← blockR_eq (Data.core307.body.drop 2640), kvmsplit_307_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core307) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_308 : kvmchkIdx 308 = true := by
  have hb : blockB (kvmlookJ 308) (kvmomLookJ 308) false [(.n 347, 0), (.n 348, 29), (.n 397, 112), (.n 585, 0), (.n 586, 7), (.n 639, 56), (.n 827, 0), (.n 828, 4), (.n 879, 32), (.n 1067, 0), (.n 1068, 3), (.n 1121, 23), (.n 1207, 0), (.n 1208, 2), (.n 1259, 18), (.n 1970, 0), (.n 1971, 28), (.n 2109, 0), (.n 2110, 7), (.n 2123, 0), (.n 2124, 4), (.n 2137, 0), (.n 2138, 2), (.n 2522, 0), (.n 2523, 2)] Data.core308.params Data.core308.name ([], []) Data.core308.body = some (⟨61666, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core308.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_308_0.1 rfl kvmsplit_308_0.2.2,
      ← blockR_eq ((Data.core308.body.drop 0).take 1320), kvmsplit_308_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_308_1320.1 rfl kvmsplit_308_1320.2.2,
      ← blockR_eq ((Data.core308.body.drop 1320).take 1320), kvmsplit_308_1320.2.1]
    rw [← blockR_eq (Data.core308.body.drop 2640), kvmsplit_308_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core308) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_309 : kvmchkIdx 309 = true := by
  have hb : blockB (kvmlookJ 309) (kvmomLookJ 309) false [(.n 347, 0), (.n 348, 29), (.n 397, 112), (.n 585, 0), (.n 586, 7), (.n 639, 56), (.n 827, 0), (.n 828, 4), (.n 879, 32), (.n 1067, 0), (.n 1068, 3), (.n 1121, 23), (.n 1309, 0), (.n 1310, 2), (.n 1361, 18), (.n 1447, 0), (.n 1448, 2), (.n 1499, 14), (.n 2230, 0), (.n 2231, 28), (.n 2375, 0), (.n 2376, 7), (.n 2389, 0), (.n 2390, 4), (.n 2403, 0), (.n 2404, 2), (.n 2830, 0), (.n 2831, 2), (.n 2914, 0), (.n 2915, 1)] Data.core309.params Data.core309.name ([], []) Data.core309.body = some (⟨63731, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core309.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvmsplit_309_0.1 rfl kvmsplit_309_0.2.2,
      ← blockR_eq ((Data.core309.body.drop 0).take 1111), kvmsplit_309_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvmsplit_309_1111.1 rfl kvmsplit_309_1111.2.2,
      ← blockR_eq ((Data.core309.body.drop 1111).take 1111), kvmsplit_309_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvmsplit_309_2222.1 rfl kvmsplit_309_2222.2.2,
      ← blockR_eq ((Data.core309.body.drop 2222).take 1111), kvmsplit_309_2222.2.1]
    rw [← blockR_eq (Data.core309.body.drop 3333), kvmsplit_309_3333]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core309) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_312 : kvmchkIdx 312 = true := by
  have hb : blockB (kvmlookJ 312) (kvmomLookJ 312) false [(.n 347, 0), (.n 348, 13), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 3), (.n 879, 28), (.n 1067, 0), (.n 1068, 2), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1827, 0), (.n 1828, 14), (.n 1841, 0), (.n 1842, 5), (.n 2270, 0), (.n 2271, 3), (.n 2520, 0), (.n 2521, 2), (.n 2709, 0), (.n 2710, 2)] Data.core312.params Data.core312.name ([], []) Data.core312.body = some (⟨35450, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core312.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_312_0.1 rfl kvmsplit_312_0.2.2,
      ← blockR_eq ((Data.core312.body.drop 0).take 1320), kvmsplit_312_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_312_1320.1 rfl kvmsplit_312_1320.2.2,
      ← blockR_eq ((Data.core312.body.drop 1320).take 1320), kvmsplit_312_1320.2.1]
    rw [← blockR_eq (Data.core312.body.drop 2640), kvmsplit_312_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core312) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_313 : kvmchkIdx 313 = true := by
  have hb : blockB (kvmlookJ 313) (kvmomLookJ 313) false [(.n 347, 0), (.n 348, 13), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 3), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1874, 0), (.n 1875, 14), (.n 1888, 0), (.n 1889, 5), (.n 2347, 0), (.n 2348, 3), (.n 2621, 0), (.n 2622, 2), (.n 2840, 0), (.n 2841, 2)] Data.core313.params Data.core313.name ([], []) Data.core313.body = some (⟨36170, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core313.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_313_0.1 rfl kvmsplit_313_0.2.2,
      ← blockR_eq ((Data.core313.body.drop 0).take 1320), kvmsplit_313_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_313_1320.1 rfl kvmsplit_313_1320.2.2,
      ← blockR_eq ((Data.core313.body.drop 1320).take 1320), kvmsplit_313_1320.2.1]
    rw [← blockR_eq (Data.core313.body.drop 2640), kvmsplit_313_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core313) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_314 : kvmchkIdx 314 = true := by
  have hb : blockB (kvmlookJ 314) (kvmomLookJ 314) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1921, 0), (.n 1922, 14), (.n 1935, 0), (.n 1936, 5), (.n 2424, 0), (.n 2425, 3), (.n 2722, 0), (.n 2723, 2), (.n 2971, 0), (.n 2972, 2)] Data.core314.params Data.core314.name ([], []) Data.core314.body = some (⟨36808, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core314.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_314_0.1 rfl kvmsplit_314_0.2.2,
      ← blockR_eq ((Data.core314.body.drop 0).take 1320), kvmsplit_314_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_314_1320.1 rfl kvmsplit_314_1320.2.2,
      ← blockR_eq ((Data.core314.body.drop 1320).take 1320), kvmsplit_314_1320.2.1]
    rw [← blockR_eq (Data.core314.body.drop 2640), kvmsplit_314_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core314) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_315 : kvmchkIdx 315 = true := by
  have hb : blockB (kvmlookJ 315) (kvmomLookJ 315) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 6), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1968, 0), (.n 1969, 14), (.n 1982, 0), (.n 1983, 5), (.n 2501, 0), (.n 2502, 3), (.n 2823, 0), (.n 2824, 2), (.n 3102, 0), (.n 3103, 2)] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨37281, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_315_0.1 rfl kvmsplit_315_0.2.2,
      ← blockR_eq ((Data.core315.body.drop 0).take 1320), kvmsplit_315_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_315_1320.1 rfl kvmsplit_315_1320.2.2,
      ← blockR_eq ((Data.core315.body.drop 1320).take 1320), kvmsplit_315_1320.2.1]
    rw [← blockR_eq (Data.core315.body.drop 2640), kvmsplit_315_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_316 : kvmchkIdx 316 = true := by
  have hb : blockB (kvmlookJ 316) (kvmomLookJ 316) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 6), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1308, 0), (.n 1309, 2), (.n 1359, 16), (.n 1445, 0), (.n 1446, 2), (.n 1497, 13), (.n 2228, 0), (.n 2229, 14), (.n 2242, 0), (.n 2243, 5), (.n 2791, 0), (.n 2792, 3), (.n 3137, 0), (.n 3138, 2), (.n 3446, 0), (.n 3447, 2), (.n 3460, 0), (.n 3461, 1)] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨39147, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvmsplit_316_0.1 rfl kvmsplit_316_0.2.2,
      ← blockR_eq ((Data.core316.body.drop 0).take 1111), kvmsplit_316_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvmsplit_316_1111.1 rfl kvmsplit_316_1111.2.2,
      ← blockR_eq ((Data.core316.body.drop 1111).take 1111), kvmsplit_316_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvmsplit_316_2222.1 rfl kvmsplit_316_2222.2.2,
      ← blockR_eq ((Data.core316.body.drop 2222).take 1111), kvmsplit_316_2222.2.1]
    rw [← blockR_eq (Data.core316.body.drop 3333), kvmsplit_316_3333]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_319 : kvmchkIdx 319 = true := by
  have hb : blockB (kvmlookJ 319) (kvmomLookJ 319) false [(.n 347, 0), (.n 348, 9), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 2), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1829, 0), (.n 1830, 9), (.n 2164, 0), (.n 2165, 4), (.n 2676, 0), (.n 2677, 3), (.n 2749, 0), (.n 2750, 2), (.n 2868, 0), (.n 2869, 1)] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨27280, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_319_0.1 rfl kvmsplit_319_0.2.2,
      ← blockR_eq ((Data.core319.body.drop 0).take 1320), kvmsplit_319_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_319_1320.1 rfl kvmsplit_319_1320.2.2,
      ← blockR_eq ((Data.core319.body.drop 1320).take 1320), kvmsplit_319_1320.2.1]
    rw [← blockR_eq (Data.core319.body.drop 2640), kvmsplit_319_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_320 : kvmchkIdx 320 = true := by
  have hb : blockB (kvmlookJ 320) (kvmomLookJ 320) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 2), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1876, 0), (.n 1877, 9), (.n 2229, 0), (.n 2230, 4), (.n 2777, 0), (.n 2778, 3), (.n 2856, 0), (.n 2857, 2), (.n 2993, 0), (.n 2994, 1)] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨27649, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_320_0.1 rfl kvmsplit_320_0.2.2,
      ← blockR_eq ((Data.core320.body.drop 0).take 1320), kvmsplit_320_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_320_1320.1 rfl kvmsplit_320_1320.2.2,
      ← blockR_eq ((Data.core320.body.drop 1320).take 1320), kvmsplit_320_1320.2.1]
    rw [← blockR_eq (Data.core320.body.drop 2640), kvmsplit_320_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_321 : kvmchkIdx 321 = true := by
  have hb : blockB (kvmlookJ 321) (kvmomLookJ 321) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1923, 0), (.n 1924, 9), (.n 2294, 0), (.n 2295, 4), (.n 2878, 0), (.n 2879, 3), (.n 2963, 0), (.n 2964, 2), (.n 3118, 0), (.n 3119, 1)] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨28039, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_321_0.1 rfl kvmsplit_321_0.2.2,
      ← blockR_eq ((Data.core321.body.drop 0).take 1320), kvmsplit_321_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_321_1320.1 rfl kvmsplit_321_1320.2.2,
      ← blockR_eq ((Data.core321.body.drop 1320).take 1320), kvmsplit_321_1320.2.1]
    rw [← blockR_eq (Data.core321.body.drop 2640), kvmsplit_321_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_322 : kvmchkIdx 322 = true := by
  have hb : blockB (kvmlookJ 322) (kvmomLookJ 322) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 4), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1970, 0), (.n 1971, 9), (.n 2359, 0), (.n 2360, 4), (.n 2979, 0), (.n 2980, 3), (.n 3070, 0), (.n 3071, 2), (.n 3243, 0), (.n 3244, 1)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨28433, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_322_0.1 rfl kvmsplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 1320), kvmsplit_322_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_322_1320.1 rfl kvmsplit_322_1320.2.2,
      ← blockR_eq ((Data.core322.body.drop 1320).take 1320), kvmsplit_322_1320.2.1]
    rw [← blockR_eq (Data.core322.body.drop 2640), kvmsplit_322_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_323 : kvmchkIdx 323 = true := by
  have hb : blockB (kvmlookJ 323) (kvmomLookJ 323) false [(.n 347, 0), (.n 348, 11), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 4), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1308, 0), (.n 1309, 2), (.n 1361, 15), (.n 1447, 0), (.n 1448, 2), (.n 1499, 13), (.n 2230, 0), (.n 2231, 9), (.n 2637, 0), (.n 2638, 4), (.n 3293, 0), (.n 3294, 3), (.n 3390, 0), (.n 3391, 2), (.n 3581, 0), (.n 3582, 1), (.n 3840, 0), (.n 3841, 1)] Data.core323.params Data.core323.name ([], []) Data.core323.body = some (⟨30394, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core323.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvmsplit_323_0.1 rfl kvmsplit_323_0.2.2,
      ← blockR_eq ((Data.core323.body.drop 0).take 1111), kvmsplit_323_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvmsplit_323_1111.1 rfl kvmsplit_323_1111.2.2,
      ← blockR_eq ((Data.core323.body.drop 1111).take 1111), kvmsplit_323_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvmsplit_323_2222.1 rfl kvmsplit_323_2222.2.2,
      ← blockR_eq ((Data.core323.body.drop 2222).take 1111), kvmsplit_323_2222.2.1]
    rw [← blockR_eq (Data.core323.body.drop 3333), kvmsplit_323_3333]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core323) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_326 : kvmchkIdx 326 = true := by
  have hb : blockB (kvmlookJ 326) (kvmomLookJ 326) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1824, 0), (.n 1825, 7), (.n 1838, 0), (.n 1839, 4), (.n 1852, 0), (.n 1853, 2), (.n 2279, 0), (.n 2280, 2), (.n 2363, 0), (.n 2364, 1)] Data.core326.params Data.core326.name ([], []) Data.core326.body = some (⟨22600, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core326.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_326_0.1 rfl kvmsplit_326_0.2.2,
      ← blockR_eq ((Data.core326.body.drop 0).take 1320), kvmsplit_326_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_326_1320.1 rfl kvmsplit_326_1320.2.2,
      ← blockR_eq ((Data.core326.body.drop 1320).take 1320), kvmsplit_326_1320.2.1]
    rw [← blockR_eq (Data.core326.body.drop 2640), kvmsplit_326_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core326) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_327 : kvmchkIdx 327 = true := by
  have hb : blockB (kvmlookJ 327) (kvmomLookJ 327) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1871, 0), (.n 1872, 7), (.n 1885, 0), (.n 1886, 4), (.n 1899, 0), (.n 1900, 2), (.n 2368, 0), (.n 2369, 2), (.n 2464, 0), (.n 2465, 1)] Data.core327.params Data.core327.name ([], []) Data.core327.body = some (⟨22727, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core327.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_327_0.1 rfl kvmsplit_327_0.2.2,
      ← blockR_eq ((Data.core327.body.drop 0).take 1320), kvmsplit_327_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_327_1320.1 rfl kvmsplit_327_1320.2.2,
      ← blockR_eq ((Data.core327.body.drop 1320).take 1320), kvmsplit_327_1320.2.1]
    rw [← blockR_eq (Data.core327.body.drop 2640), kvmsplit_327_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core327) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_328 : kvmchkIdx 328 = true := by
  have hb : blockB (kvmlookJ 328) (kvmomLookJ 328) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1918, 0), (.n 1919, 7), (.n 1932, 0), (.n 1933, 4), (.n 1946, 0), (.n 1947, 2), (.n 2457, 0), (.n 2458, 2), (.n 2565, 0), (.n 2566, 1)] Data.core328.params Data.core328.name ([], []) Data.core328.body = some (⟨22963, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core328.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_328_0.1 rfl kvmsplit_328_0.2.2,
      ← blockR_eq ((Data.core328.body.drop 0).take 1320), kvmsplit_328_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_328_1320.1 rfl kvmsplit_328_1320.2.2,
      ← blockR_eq ((Data.core328.body.drop 1320).take 1320), kvmsplit_328_1320.2.1]
    rw [← blockR_eq (Data.core328.body.drop 2640), kvmsplit_328_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core328) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_329 : kvmchkIdx 329 = true := by
  have hb : blockB (kvmlookJ 329) (kvmomLookJ 329) false [(.n 347, 0), (.n 348, 8), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 3), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1255, 15), (.n 1966, 0), (.n 1967, 7), (.n 1980, 0), (.n 1981, 4), (.n 1994, 0), (.n 1995, 2), (.n 2547, 0), (.n 2548, 2), (.n 2667, 0), (.n 2668, 1)] Data.core329.params Data.core329.name ([], []) Data.core329.body = some (⟨24061, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core329.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_329_0.1 rfl kvmsplit_329_0.2.2,
      ← blockR_eq ((Data.core329.body.drop 0).take 1320), kvmsplit_329_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_329_1320.1 rfl kvmsplit_329_1320.2.2,
      ← blockR_eq ((Data.core329.body.drop 1320).take 1320), kvmsplit_329_1320.2.1]
    rw [← blockR_eq (Data.core329.body.drop 2640), kvmsplit_329_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core329) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_330 : kvmchkIdx 330 = true := by
  have hb : blockB (kvmlookJ 330) (kvmomLookJ 330) false [(.n 347, 0), (.n 348, 8), (.n 394, 28), (.n 582, 0), (.n 583, 5), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 3), (.n 1116, 18), (.n 1304, 0), (.n 1305, 2), (.n 1357, 15), (.n 1443, 0), (.n 1444, 2), (.n 1494, 12), (.n 2225, 0), (.n 2226, 7), (.n 2239, 0), (.n 2240, 4), (.n 2253, 0), (.n 2254, 2), (.n 2848, 0), (.n 2849, 2), (.n 2980, 0), (.n 2981, 1), (.n 3239, 0), (.n 3240, 1)] Data.core330.params Data.core330.name ([], []) Data.core330.body = some (⟨25993, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core330.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvmsplit_330_0.1 rfl kvmsplit_330_0.2.2,
      ← blockR_eq ((Data.core330.body.drop 0).take 1111), kvmsplit_330_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvmsplit_330_1111.1 rfl kvmsplit_330_1111.2.2,
      ← blockR_eq ((Data.core330.body.drop 1111).take 1111), kvmsplit_330_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvmsplit_330_2222.1 rfl kvmsplit_330_2222.2.2,
      ← blockR_eq ((Data.core330.body.drop 2222).take 1111), kvmsplit_330_2222.2.1]
    rw [← blockR_eq (Data.core330.body.drop 3333), kvmsplit_330_3333]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core330) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvmchkIdx_all : ∀ j < 947, kvmchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 307
  · subst h1000; exact kvmchkIdx_307
  by_cases h1001 : j = 308
  · subst h1001; exact kvmchkIdx_308
  by_cases h1002 : j = 309
  · subst h1002; exact kvmchkIdx_309
  by_cases h1003 : j = 312
  · subst h1003; exact kvmchkIdx_312
  by_cases h1004 : j = 313
  · subst h1004; exact kvmchkIdx_313
  by_cases h1005 : j = 314
  · subst h1005; exact kvmchkIdx_314
  by_cases h1006 : j = 315
  · subst h1006; exact kvmchkIdx_315
  by_cases h1007 : j = 316
  · subst h1007; exact kvmchkIdx_316
  by_cases h1008 : j = 319
  · subst h1008; exact kvmchkIdx_319
  by_cases h1009 : j = 320
  · subst h1009; exact kvmchkIdx_320
  by_cases h1010 : j = 321
  · subst h1010; exact kvmchkIdx_321
  by_cases h1011 : j = 322
  · subst h1011; exact kvmchkIdx_322
  by_cases h1012 : j = 323
  · subst h1012; exact kvmchkIdx_323
  by_cases h1013 : j = 326
  · subst h1013; exact kvmchkIdx_326
  by_cases h1014 : j = 327
  · subst h1014; exact kvmchkIdx_327
  by_cases h1015 : j = 328
  · subst h1015; exact kvmchkIdx_328
  by_cases h1016 : j = 329
  · subst h1016; exact kvmchkIdx_329
  by_cases h1017 : j = 330
  · subst h1017; exact kvmchkIdx_330
  by_cases h0 : j < 11
  · exact kvmstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvmstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvmstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvmstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvmstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvmstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvmstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvmstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvmstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvmstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvmstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 304
  · exact kvmstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 305
  · exact kvmstaticRange_304.get (by omega) (by omega)
  by_cases h13 : j < 306
  · exact kvmstaticRange_305.get (by omega) (by omega)
  by_cases h14 : j < 307
  · exact kvmstaticRange_306.get (by omega) (by omega)
  by_cases h15 : j < 311
  · exact kvmstaticRange_310.get (by omega) (by omega)
  by_cases h16 : j < 312
  · exact kvmstaticRange_311.get (by omega) (by omega)
  by_cases h17 : j < 318
  · exact kvmstaticRange_317.get (by omega) (by omega)
  by_cases h18 : j < 319
  · exact kvmstaticRange_318.get (by omega) (by omega)
  by_cases h19 : j < 325
  · exact kvmstaticRange_324.get (by omega) (by omega)
  by_cases h20 : j < 326
  · exact kvmstaticRange_325.get (by omega) (by omega)
  by_cases h21 : j < 353
  · exact kvmstaticRange_331.get (by omega) (by omega)
  by_cases h22 : j < 383
  · exact kvmstaticRange_353.get (by omega) (by omega)
  by_cases h23 : j < 406
  · exact kvmstaticRange_383.get (by omega) (by omega)
  by_cases h24 : j < 436
  · exact kvmstaticRange_406.get (by omega) (by omega)
  by_cases h25 : j < 457
  · exact kvmstaticRange_436.get (by omega) (by omega)
  by_cases h26 : j < 478
  · exact kvmstaticRange_457.get (by omega) (by omega)
  by_cases h27 : j < 499
  · exact kvmstaticRange_478.get (by omega) (by omega)
  by_cases h28 : j < 518
  · exact kvmstaticRange_499.get (by omega) (by omega)
  by_cases h29 : j < 534
  · exact kvmstaticRange_518.get (by omega) (by omega)
  by_cases h30 : j < 551
  · exact kvmstaticRange_534.get (by omega) (by omega)
  by_cases h31 : j < 569
  · exact kvmstaticRange_551.get (by omega) (by omega)
  by_cases h32 : j < 588
  · exact kvmstaticRange_569.get (by omega) (by omega)
  by_cases h33 : j < 605
  · exact kvmstaticRange_588.get (by omega) (by omega)
  by_cases h34 : j < 624
  · exact kvmstaticRange_605.get (by omega) (by omega)
  by_cases h35 : j < 640
  · exact kvmstaticRange_624.get (by omega) (by omega)
  by_cases h36 : j < 655
  · exact kvmstaticRange_640.get (by omega) (by omega)
  by_cases h37 : j < 671
  · exact kvmstaticRange_655.get (by omega) (by omega)
  by_cases h38 : j < 687
  · exact kvmstaticRange_671.get (by omega) (by omega)
  by_cases h39 : j < 701
  · exact kvmstaticRange_687.get (by omega) (by omega)
  by_cases h40 : j < 719
  · exact kvmstaticRange_701.get (by omega) (by omega)
  by_cases h41 : j < 737
  · exact kvmstaticRange_719.get (by omega) (by omega)
  by_cases h42 : j < 755
  · exact kvmstaticRange_737.get (by omega) (by omega)
  by_cases h43 : j < 773
  · exact kvmstaticRange_755.get (by omega) (by omega)
  by_cases h44 : j < 791
  · exact kvmstaticRange_773.get (by omega) (by omega)
  by_cases h45 : j < 815
  · exact kvmstaticRange_791.get (by omega) (by omega)
  by_cases h46 : j < 839
  · exact kvmstaticRange_815.get (by omega) (by omega)
  by_cases h47 : j < 853
  · exact kvmstaticRange_839.get (by omega) (by omega)
  by_cases h48 : j < 859
  · exact kvmstaticRange_853.get (by omega) (by omega)
  by_cases h49 : j < 863
  · exact kvmstaticRange_859.get (by omega) (by omega)
  by_cases h50 : j < 867
  · exact kvmstaticRange_863.get (by omega) (by omega)
  by_cases h51 : j < 869
  · exact kvmstaticRange_867.get (by omega) (by omega)
  by_cases h52 : j < 873
  · exact kvmstaticRange_869.get (by omega) (by omega)
  by_cases h53 : j < 875
  · exact kvmstaticRange_873.get (by omega) (by omega)
  by_cases h54 : j < 879
  · exact kvmstaticRange_875.get (by omega) (by omega)
  by_cases h55 : j < 881
  · exact kvmstaticRange_879.get (by omega) (by omega)
  by_cases h56 : j < 885
  · exact kvmstaticRange_881.get (by omega) (by omega)
  by_cases h57 : j < 887
  · exact kvmstaticRange_885.get (by omega) (by omega)
  by_cases h58 : j < 891
  · exact kvmstaticRange_887.get (by omega) (by omega)
  by_cases h59 : j < 895
  · exact kvmstaticRange_891.get (by omega) (by omega)
  by_cases h60 : j < 897
  · exact kvmstaticRange_895.get (by omega) (by omega)
  by_cases h61 : j < 899
  · exact kvmstaticRange_897.get (by omega) (by omega)
  by_cases h62 : j < 901
  · exact kvmstaticRange_899.get (by omega) (by omega)
  by_cases h63 : j < 903
  · exact kvmstaticRange_901.get (by omega) (by omega)
  by_cases h64 : j < 905
  · exact kvmstaticRange_903.get (by omega) (by omega)
  by_cases h65 : j < 907
  · exact kvmstaticRange_905.get (by omega) (by omega)
  by_cases h66 : j < 909
  · exact kvmstaticRange_907.get (by omega) (by omega)
  by_cases h67 : j < 911
  · exact kvmstaticRange_909.get (by omega) (by omega)
  by_cases h68 : j < 913
  · exact kvmstaticRange_911.get (by omega) (by omega)
  by_cases h69 : j < 917
  · exact kvmstaticRange_913.get (by omega) (by omega)
  by_cases h70 : j < 918
  · exact kvmstaticRange_917.get (by omega) (by omega)
  by_cases h71 : j < 919
  · exact kvmstaticRange_918.get (by omega) (by omega)
  by_cases h72 : j < 920
  · exact kvmstaticRange_919.get (by omega) (by omega)
  by_cases h73 : j < 921
  · exact kvmstaticRange_920.get (by omega) (by omega)
  by_cases h74 : j < 922
  · exact kvmstaticRange_921.get (by omega) (by omega)
  by_cases h75 : j < 923
  · exact kvmstaticRange_922.get (by omega) (by omega)
  by_cases h76 : j < 925
  · exact kvmstaticRange_923.get (by omega) (by omega)
  by_cases h77 : j < 927
  · exact kvmstaticRange_925.get (by omega) (by omega)
  by_cases h78 : j < 931
  · exact kvmstaticRange_927.get (by omega) (by omega)
  by_cases h79 : j < 932
  · exact kvmstaticRange_931.get (by omega) (by omega)
  by_cases h80 : j < 933
  · exact kvmstaticRange_932.get (by omega) (by omega)
  by_cases h81 : j < 934
  · exact kvmstaticRange_933.get (by omega) (by omega)
  by_cases h82 : j < 935
  · exact kvmstaticRange_934.get (by omega) (by omega)
  by_cases h83 : j < 936
  · exact kvmstaticRange_935.get (by omega) (by omega)
  by_cases h84 : j < 938
  · exact kvmstaticRange_936.get (by omega) (by omega)
  by_cases h85 : j < 940
  · exact kvmstaticRange_938.get (by omega) (by omega)
  by_cases h86 : j < 942
  · exact kvmstaticRange_940.get (by omega) (by omega)
  by_cases h87 : j < 944
  · exact kvmstaticRange_942.get (by omega) (by omega)
  exact kvmstaticRange_944.get (by omega) (by omega)

end
end LeanVM.Guest
