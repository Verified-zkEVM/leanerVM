/-
  LeanVM.Guest.Memory.GuestCntVJ.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVJ.Part00
public import LeanVM.Guest.Memory.GuestCntVJ.Part01
public import LeanVM.Guest.Memory.GuestCntVJ.Part02
public import LeanVM.Guest.Memory.GuestCntVJ.Part03
public import LeanVM.Guest.Memory.GuestCntVJ.Part04
public import LeanVM.Guest.Memory.GuestCntVJ.Part05
public import LeanVM.Guest.Memory.GuestCntVJ.Part06
public import LeanVM.Guest.Memory.GuestCntVJ.Part07
public import LeanVM.Guest.Memory.GuestCntVJ.Part08
public import LeanVM.Guest.Memory.GuestCntVJ.Part09
public import LeanVM.Guest.Memory.GuestCntVJ.Part10
public import LeanVM.Guest.Memory.GuestCntVJ.Part11
public import LeanVM.Guest.Memory.GuestCntVJ.Part12
public import LeanVM.Guest.Memory.GuestCntVJ.Part13
public import LeanVM.Guest.Memory.GuestCntVJ.Part14
public import LeanVM.Guest.Memory.GuestCntVJ.Part15
public import LeanVM.Guest.Memory.GuestCntVJ.Part16
public import LeanVM.Guest.Memory.GuestCntVJ.Part17
public import LeanVM.Guest.Memory.GuestCntVJ.Part18
public import LeanVM.Guest.Memory.GuestCntVJ.Part19
public import LeanVM.Guest.Memory.GuestCntVJ.Part20
public import LeanVM.Guest.Memory.GuestCntVJ.Part21
public import LeanVM.Guest.Memory.GuestCntVJ.Part22
public import LeanVM.Guest.Memory.GuestCntVJ.Part23
public import LeanVM.Guest.Memory.GuestCntVJ.Part24
public import LeanVM.Guest.Memory.GuestCntVJ.Part25
public import LeanVM.Guest.Memory.GuestCntVJ.Part26
public import LeanVM.Guest.Memory.GuestCntVJ.Part27
public import LeanVM.Guest.Memory.GuestCntVJ.Part28
public import LeanVM.Guest.Memory.GuestCntVJ.Part29
public import LeanVM.Guest.Memory.GuestCntVJ.Part30
public import LeanVM.Guest.Memory.GuestCntVJ.Part31
public import LeanVM.Guest.Memory.GuestCntVJ.Part32
public import LeanVM.Guest.Memory.GuestCntVJ.Part33
public import LeanVM.Guest.Memory.GuestCntVJ.Part34
public import LeanVM.Guest.Memory.GuestCntVJ.Part35
public import LeanVM.Guest.Memory.GuestCntVJ.Part36
public import LeanVM.Guest.Memory.GuestCntVJ.Part37
public import LeanVM.Guest.Memory.GuestCntVJ.Part38
public import LeanVM.Guest.Memory.GuestCntVJ.Part39
public import LeanVM.Guest.Memory.GuestCntVJ.Part40
public import LeanVM.Guest.Memory.GuestCntVJ.Part41
public import LeanVM.Guest.Memory.GuestCntVJ.Part42
public import LeanVM.Guest.Memory.GuestCntVJ.Part43

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjchkIdx_307 : kvjchkIdx 307 = true := by
  have hb : blockB (kvjlookJ 307) (kvjomLookJ 307) false [(.n 347, 0), (.n 348, 25), (.n 396, 112), (.n 584, 0), (.n 585, 7), (.n 638, 56), (.n 826, 0), (.n 827, 4), (.n 878, 32), (.n 1066, 0), (.n 1067, 3), (.n 1120, 23), (.n 1206, 0), (.n 1207, 2), (.n 1258, 18), (.n 1922, 0), (.n 1923, 28), (.n 1936, 0), (.n 1937, 7), (.n 1950, 0), (.n 1951, 4), (.n 1964, 0), (.n 1965, 2), (.n 2307, 0), (.n 2308, 2)] Data.core307.params Data.core307.name ([], []) Data.core307.body = some (⟨14158, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core307.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_307_0.1 rfl kvjsplit_307_0.2.2,
      ← blockR_eq ((Data.core307.body.drop 0).take 1320), kvjsplit_307_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_307_1320.1 rfl kvjsplit_307_1320.2.2,
      ← blockR_eq ((Data.core307.body.drop 1320).take 1320), kvjsplit_307_1320.2.1]
    rw [← blockR_eq (Data.core307.body.drop 2640), kvjsplit_307_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core307) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_308 : kvjchkIdx 308 = true := by
  have hb : blockB (kvjlookJ 308) (kvjomLookJ 308) false [(.n 347, 0), (.n 348, 29), (.n 397, 112), (.n 585, 0), (.n 586, 7), (.n 639, 56), (.n 827, 0), (.n 828, 4), (.n 879, 32), (.n 1067, 0), (.n 1068, 3), (.n 1121, 23), (.n 1207, 0), (.n 1208, 2), (.n 1259, 18), (.n 1970, 0), (.n 1971, 28), (.n 2109, 0), (.n 2110, 7), (.n 2123, 0), (.n 2124, 4), (.n 2137, 0), (.n 2138, 2), (.n 2522, 0), (.n 2523, 2)] Data.core308.params Data.core308.name ([], []) Data.core308.body = some (⟨14276, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core308.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_308_0.1 rfl kvjsplit_308_0.2.2,
      ← blockR_eq ((Data.core308.body.drop 0).take 1320), kvjsplit_308_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_308_1320.1 rfl kvjsplit_308_1320.2.2,
      ← blockR_eq ((Data.core308.body.drop 1320).take 1320), kvjsplit_308_1320.2.1]
    rw [← blockR_eq (Data.core308.body.drop 2640), kvjsplit_308_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core308) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_309 : kvjchkIdx 309 = true := by
  have hb : blockB (kvjlookJ 309) (kvjomLookJ 309) false [(.n 347, 0), (.n 348, 29), (.n 397, 112), (.n 585, 0), (.n 586, 7), (.n 639, 56), (.n 827, 0), (.n 828, 4), (.n 879, 32), (.n 1067, 0), (.n 1068, 3), (.n 1121, 23), (.n 1309, 0), (.n 1310, 2), (.n 1361, 18), (.n 1447, 0), (.n 1448, 2), (.n 1499, 14), (.n 2230, 0), (.n 2231, 28), (.n 2375, 0), (.n 2376, 7), (.n 2389, 0), (.n 2390, 4), (.n 2403, 0), (.n 2404, 2), (.n 2830, 0), (.n 2831, 2), (.n 2914, 0), (.n 2915, 1)] Data.core309.params Data.core309.name ([], []) Data.core309.body = some (⟨14761, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core309.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvjsplit_309_0.1 rfl kvjsplit_309_0.2.2,
      ← blockR_eq ((Data.core309.body.drop 0).take 1111), kvjsplit_309_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvjsplit_309_1111.1 rfl kvjsplit_309_1111.2.2,
      ← blockR_eq ((Data.core309.body.drop 1111).take 1111), kvjsplit_309_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvjsplit_309_2222.1 rfl kvjsplit_309_2222.2.2,
      ← blockR_eq ((Data.core309.body.drop 2222).take 1111), kvjsplit_309_2222.2.1]
    rw [← blockR_eq (Data.core309.body.drop 3333), kvjsplit_309_3333]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core309) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_312 : kvjchkIdx 312 = true := by
  have hb : blockB (kvjlookJ 312) (kvjomLookJ 312) false [(.n 347, 0), (.n 348, 13), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 3), (.n 879, 28), (.n 1067, 0), (.n 1068, 2), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1827, 0), (.n 1828, 14), (.n 1841, 0), (.n 1842, 5), (.n 2270, 0), (.n 2271, 3), (.n 2520, 0), (.n 2521, 2), (.n 2709, 0), (.n 2710, 2)] Data.core312.params Data.core312.name ([], []) Data.core312.body = some (⟨8714, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core312.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_312_0.1 rfl kvjsplit_312_0.2.2,
      ← blockR_eq ((Data.core312.body.drop 0).take 1320), kvjsplit_312_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_312_1320.1 rfl kvjsplit_312_1320.2.2,
      ← blockR_eq ((Data.core312.body.drop 1320).take 1320), kvjsplit_312_1320.2.1]
    rw [← blockR_eq (Data.core312.body.drop 2640), kvjsplit_312_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core312) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_313 : kvjchkIdx 313 = true := by
  have hb : blockB (kvjlookJ 313) (kvjomLookJ 313) false [(.n 347, 0), (.n 348, 13), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 3), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1874, 0), (.n 1875, 14), (.n 1888, 0), (.n 1889, 5), (.n 2347, 0), (.n 2348, 3), (.n 2621, 0), (.n 2622, 2), (.n 2840, 0), (.n 2841, 2)] Data.core313.params Data.core313.name ([], []) Data.core313.body = some (⟨8805, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core313.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_313_0.1 rfl kvjsplit_313_0.2.2,
      ← blockR_eq ((Data.core313.body.drop 0).take 1320), kvjsplit_313_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_313_1320.1 rfl kvjsplit_313_1320.2.2,
      ← blockR_eq ((Data.core313.body.drop 1320).take 1320), kvjsplit_313_1320.2.1]
    rw [← blockR_eq (Data.core313.body.drop 2640), kvjsplit_313_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core313) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_314 : kvjchkIdx 314 = true := by
  have hb : blockB (kvjlookJ 314) (kvjomLookJ 314) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1921, 0), (.n 1922, 14), (.n 1935, 0), (.n 1936, 5), (.n 2424, 0), (.n 2425, 3), (.n 2722, 0), (.n 2723, 2), (.n 2971, 0), (.n 2972, 2)] Data.core314.params Data.core314.name ([], []) Data.core314.body = some (⟨8831, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core314.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_314_0.1 rfl kvjsplit_314_0.2.2,
      ← blockR_eq ((Data.core314.body.drop 0).take 1320), kvjsplit_314_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_314_1320.1 rfl kvjsplit_314_1320.2.2,
      ← blockR_eq ((Data.core314.body.drop 1320).take 1320), kvjsplit_314_1320.2.1]
    rw [← blockR_eq (Data.core314.body.drop 2640), kvjsplit_314_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core314) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_315 : kvjchkIdx 315 = true := by
  have hb : blockB (kvjlookJ 315) (kvjomLookJ 315) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 6), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1968, 0), (.n 1969, 14), (.n 1982, 0), (.n 1983, 5), (.n 2501, 0), (.n 2502, 3), (.n 2823, 0), (.n 2824, 2), (.n 3102, 0), (.n 3103, 2)] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨8860, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_315_0.1 rfl kvjsplit_315_0.2.2,
      ← blockR_eq ((Data.core315.body.drop 0).take 1320), kvjsplit_315_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_315_1320.1 rfl kvjsplit_315_1320.2.2,
      ← blockR_eq ((Data.core315.body.drop 1320).take 1320), kvjsplit_315_1320.2.1]
    rw [← blockR_eq (Data.core315.body.drop 2640), kvjsplit_315_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_316 : kvjchkIdx 316 = true := by
  have hb : blockB (kvjlookJ 316) (kvjomLookJ 316) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 6), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1308, 0), (.n 1309, 2), (.n 1359, 16), (.n 1445, 0), (.n 1446, 2), (.n 1497, 13), (.n 2228, 0), (.n 2229, 14), (.n 2242, 0), (.n 2243, 5), (.n 2791, 0), (.n 2792, 3), (.n 3137, 0), (.n 3138, 2), (.n 3446, 0), (.n 3447, 2), (.n 3460, 0), (.n 3461, 1)] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨9313, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvjsplit_316_0.1 rfl kvjsplit_316_0.2.2,
      ← blockR_eq ((Data.core316.body.drop 0).take 1111), kvjsplit_316_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvjsplit_316_1111.1 rfl kvjsplit_316_1111.2.2,
      ← blockR_eq ((Data.core316.body.drop 1111).take 1111), kvjsplit_316_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvjsplit_316_2222.1 rfl kvjsplit_316_2222.2.2,
      ← blockR_eq ((Data.core316.body.drop 2222).take 1111), kvjsplit_316_2222.2.1]
    rw [← blockR_eq (Data.core316.body.drop 3333), kvjsplit_316_3333]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_319 : kvjchkIdx 319 = true := by
  have hb : blockB (kvjlookJ 319) (kvjomLookJ 319) false [(.n 347, 0), (.n 348, 9), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 2), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1829, 0), (.n 1830, 9), (.n 2164, 0), (.n 2165, 4), (.n 2676, 0), (.n 2677, 3), (.n 2749, 0), (.n 2750, 2), (.n 2868, 0), (.n 2869, 1)] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨6894, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_319_0.1 rfl kvjsplit_319_0.2.2,
      ← blockR_eq ((Data.core319.body.drop 0).take 1320), kvjsplit_319_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_319_1320.1 rfl kvjsplit_319_1320.2.2,
      ← blockR_eq ((Data.core319.body.drop 1320).take 1320), kvjsplit_319_1320.2.1]
    rw [← blockR_eq (Data.core319.body.drop 2640), kvjsplit_319_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_320 : kvjchkIdx 320 = true := by
  have hb : blockB (kvjlookJ 320) (kvjomLookJ 320) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 2), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1876, 0), (.n 1877, 9), (.n 2229, 0), (.n 2230, 4), (.n 2777, 0), (.n 2778, 3), (.n 2856, 0), (.n 2857, 2), (.n 2993, 0), (.n 2994, 1)] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨6911, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_320_0.1 rfl kvjsplit_320_0.2.2,
      ← blockR_eq ((Data.core320.body.drop 0).take 1320), kvjsplit_320_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_320_1320.1 rfl kvjsplit_320_1320.2.2,
      ← blockR_eq ((Data.core320.body.drop 1320).take 1320), kvjsplit_320_1320.2.1]
    rw [← blockR_eq (Data.core320.body.drop 2640), kvjsplit_320_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_321 : kvjchkIdx 321 = true := by
  have hb : blockB (kvjlookJ 321) (kvjomLookJ 321) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1923, 0), (.n 1924, 9), (.n 2294, 0), (.n 2295, 4), (.n 2878, 0), (.n 2879, 3), (.n 2963, 0), (.n 2964, 2), (.n 3118, 0), (.n 3119, 1)] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨6932, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_321_0.1 rfl kvjsplit_321_0.2.2,
      ← blockR_eq ((Data.core321.body.drop 0).take 1320), kvjsplit_321_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_321_1320.1 rfl kvjsplit_321_1320.2.2,
      ← blockR_eq ((Data.core321.body.drop 1320).take 1320), kvjsplit_321_1320.2.1]
    rw [← blockR_eq (Data.core321.body.drop 2640), kvjsplit_321_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_322 : kvjchkIdx 322 = true := by
  have hb : blockB (kvjlookJ 322) (kvjomLookJ 322) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 4), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1970, 0), (.n 1971, 9), (.n 2359, 0), (.n 2360, 4), (.n 2979, 0), (.n 2980, 3), (.n 3070, 0), (.n 3071, 2), (.n 3243, 0), (.n 3244, 1)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨6961, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_322_0.1 rfl kvjsplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 1320), kvjsplit_322_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_322_1320.1 rfl kvjsplit_322_1320.2.2,
      ← blockR_eq ((Data.core322.body.drop 1320).take 1320), kvjsplit_322_1320.2.1]
    rw [← blockR_eq (Data.core322.body.drop 2640), kvjsplit_322_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_323 : kvjchkIdx 323 = true := by
  have hb : blockB (kvjlookJ 323) (kvjomLookJ 323) false [(.n 347, 0), (.n 348, 11), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 4), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1308, 0), (.n 1309, 2), (.n 1361, 15), (.n 1447, 0), (.n 1448, 2), (.n 1499, 13), (.n 2230, 0), (.n 2231, 9), (.n 2637, 0), (.n 2638, 4), (.n 3293, 0), (.n 3294, 3), (.n 3390, 0), (.n 3391, 2), (.n 3581, 0), (.n 3582, 1), (.n 3840, 0), (.n 3841, 1)] Data.core323.params Data.core323.name ([], []) Data.core323.body = some (⟨7419, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core323.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvjsplit_323_0.1 rfl kvjsplit_323_0.2.2,
      ← blockR_eq ((Data.core323.body.drop 0).take 1111), kvjsplit_323_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvjsplit_323_1111.1 rfl kvjsplit_323_1111.2.2,
      ← blockR_eq ((Data.core323.body.drop 1111).take 1111), kvjsplit_323_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvjsplit_323_2222.1 rfl kvjsplit_323_2222.2.2,
      ← blockR_eq ((Data.core323.body.drop 2222).take 1111), kvjsplit_323_2222.2.1]
    rw [← blockR_eq (Data.core323.body.drop 3333), kvjsplit_323_3333]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core323) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_326 : kvjchkIdx 326 = true := by
  have hb : blockB (kvjlookJ 326) (kvjomLookJ 326) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1824, 0), (.n 1825, 7), (.n 1838, 0), (.n 1839, 4), (.n 1852, 0), (.n 1853, 2), (.n 2279, 0), (.n 2280, 2), (.n 2363, 0), (.n 2364, 1)] Data.core326.params Data.core326.name ([], []) Data.core326.body = some (⟨5621, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core326.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_326_0.1 rfl kvjsplit_326_0.2.2,
      ← blockR_eq ((Data.core326.body.drop 0).take 1320), kvjsplit_326_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_326_1320.1 rfl kvjsplit_326_1320.2.2,
      ← blockR_eq ((Data.core326.body.drop 1320).take 1320), kvjsplit_326_1320.2.1]
    rw [← blockR_eq (Data.core326.body.drop 2640), kvjsplit_326_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core326) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_327 : kvjchkIdx 327 = true := by
  have hb : blockB (kvjlookJ 327) (kvjomLookJ 327) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1871, 0), (.n 1872, 7), (.n 1885, 0), (.n 1886, 4), (.n 1899, 0), (.n 1900, 2), (.n 2368, 0), (.n 2369, 2), (.n 2464, 0), (.n 2465, 1)] Data.core327.params Data.core327.name ([], []) Data.core327.body = some (⟨5633, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core327.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_327_0.1 rfl kvjsplit_327_0.2.2,
      ← blockR_eq ((Data.core327.body.drop 0).take 1320), kvjsplit_327_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_327_1320.1 rfl kvjsplit_327_1320.2.2,
      ← blockR_eq ((Data.core327.body.drop 1320).take 1320), kvjsplit_327_1320.2.1]
    rw [← blockR_eq (Data.core327.body.drop 2640), kvjsplit_327_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core327) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_328 : kvjchkIdx 328 = true := by
  have hb : blockB (kvjlookJ 328) (kvjomLookJ 328) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1918, 0), (.n 1919, 7), (.n 1932, 0), (.n 1933, 4), (.n 1946, 0), (.n 1947, 2), (.n 2457, 0), (.n 2458, 2), (.n 2565, 0), (.n 2566, 1)] Data.core328.params Data.core328.name ([], []) Data.core328.body = some (⟨5649, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core328.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_328_0.1 rfl kvjsplit_328_0.2.2,
      ← blockR_eq ((Data.core328.body.drop 0).take 1320), kvjsplit_328_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_328_1320.1 rfl kvjsplit_328_1320.2.2,
      ← blockR_eq ((Data.core328.body.drop 1320).take 1320), kvjsplit_328_1320.2.1]
    rw [← blockR_eq (Data.core328.body.drop 2640), kvjsplit_328_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core328) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_329 : kvjchkIdx 329 = true := by
  have hb : blockB (kvjlookJ 329) (kvjomLookJ 329) false [(.n 347, 0), (.n 348, 8), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 3), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1255, 15), (.n 1966, 0), (.n 1967, 7), (.n 1980, 0), (.n 1981, 4), (.n 1994, 0), (.n 1995, 2), (.n 2547, 0), (.n 2548, 2), (.n 2667, 0), (.n 2668, 1)] Data.core329.params Data.core329.name ([], []) Data.core329.body = some (⟨5891, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core329.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_329_0.1 rfl kvjsplit_329_0.2.2,
      ← blockR_eq ((Data.core329.body.drop 0).take 1320), kvjsplit_329_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_329_1320.1 rfl kvjsplit_329_1320.2.2,
      ← blockR_eq ((Data.core329.body.drop 1320).take 1320), kvjsplit_329_1320.2.1]
    rw [← blockR_eq (Data.core329.body.drop 2640), kvjsplit_329_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core329) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_330 : kvjchkIdx 330 = true := by
  have hb : blockB (kvjlookJ 330) (kvjomLookJ 330) false [(.n 347, 0), (.n 348, 8), (.n 394, 28), (.n 582, 0), (.n 583, 5), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 3), (.n 1116, 18), (.n 1304, 0), (.n 1305, 2), (.n 1357, 15), (.n 1443, 0), (.n 1444, 2), (.n 1494, 12), (.n 2225, 0), (.n 2226, 7), (.n 2239, 0), (.n 2240, 4), (.n 2253, 0), (.n 2254, 2), (.n 2848, 0), (.n 2849, 2), (.n 2980, 0), (.n 2981, 1), (.n 3239, 0), (.n 3240, 1)] Data.core330.params Data.core330.name ([], []) Data.core330.body = some (⟨6363, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core330.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvjsplit_330_0.1 rfl kvjsplit_330_0.2.2,
      ← blockR_eq ((Data.core330.body.drop 0).take 1111), kvjsplit_330_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvjsplit_330_1111.1 rfl kvjsplit_330_1111.2.2,
      ← blockR_eq ((Data.core330.body.drop 1111).take 1111), kvjsplit_330_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvjsplit_330_2222.1 rfl kvjsplit_330_2222.2.2,
      ← blockR_eq ((Data.core330.body.drop 2222).take 1111), kvjsplit_330_2222.2.1]
    rw [← blockR_eq (Data.core330.body.drop 3333), kvjsplit_330_3333]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core330) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvjchkIdx_all : ∀ j < 947, kvjchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 307
  · subst h1000; exact kvjchkIdx_307
  by_cases h1001 : j = 308
  · subst h1001; exact kvjchkIdx_308
  by_cases h1002 : j = 309
  · subst h1002; exact kvjchkIdx_309
  by_cases h1003 : j = 312
  · subst h1003; exact kvjchkIdx_312
  by_cases h1004 : j = 313
  · subst h1004; exact kvjchkIdx_313
  by_cases h1005 : j = 314
  · subst h1005; exact kvjchkIdx_314
  by_cases h1006 : j = 315
  · subst h1006; exact kvjchkIdx_315
  by_cases h1007 : j = 316
  · subst h1007; exact kvjchkIdx_316
  by_cases h1008 : j = 319
  · subst h1008; exact kvjchkIdx_319
  by_cases h1009 : j = 320
  · subst h1009; exact kvjchkIdx_320
  by_cases h1010 : j = 321
  · subst h1010; exact kvjchkIdx_321
  by_cases h1011 : j = 322
  · subst h1011; exact kvjchkIdx_322
  by_cases h1012 : j = 323
  · subst h1012; exact kvjchkIdx_323
  by_cases h1013 : j = 326
  · subst h1013; exact kvjchkIdx_326
  by_cases h1014 : j = 327
  · subst h1014; exact kvjchkIdx_327
  by_cases h1015 : j = 328
  · subst h1015; exact kvjchkIdx_328
  by_cases h1016 : j = 329
  · subst h1016; exact kvjchkIdx_329
  by_cases h1017 : j = 330
  · subst h1017; exact kvjchkIdx_330
  by_cases h0 : j < 11
  · exact kvjstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvjstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvjstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvjstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvjstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvjstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvjstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvjstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvjstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvjstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvjstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 304
  · exact kvjstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 305
  · exact kvjstaticRange_304.get (by omega) (by omega)
  by_cases h13 : j < 306
  · exact kvjstaticRange_305.get (by omega) (by omega)
  by_cases h14 : j < 307
  · exact kvjstaticRange_306.get (by omega) (by omega)
  by_cases h15 : j < 311
  · exact kvjstaticRange_310.get (by omega) (by omega)
  by_cases h16 : j < 312
  · exact kvjstaticRange_311.get (by omega) (by omega)
  by_cases h17 : j < 318
  · exact kvjstaticRange_317.get (by omega) (by omega)
  by_cases h18 : j < 319
  · exact kvjstaticRange_318.get (by omega) (by omega)
  by_cases h19 : j < 325
  · exact kvjstaticRange_324.get (by omega) (by omega)
  by_cases h20 : j < 326
  · exact kvjstaticRange_325.get (by omega) (by omega)
  by_cases h21 : j < 352
  · exact kvjstaticRange_331.get (by omega) (by omega)
  by_cases h22 : j < 374
  · exact kvjstaticRange_352.get (by omega) (by omega)
  by_cases h23 : j < 397
  · exact kvjstaticRange_374.get (by omega) (by omega)
  by_cases h24 : j < 411
  · exact kvjstaticRange_397.get (by omega) (by omega)
  by_cases h25 : j < 441
  · exact kvjstaticRange_411.get (by omega) (by omega)
  by_cases h26 : j < 462
  · exact kvjstaticRange_441.get (by omega) (by omega)
  by_cases h27 : j < 483
  · exact kvjstaticRange_462.get (by omega) (by omega)
  by_cases h28 : j < 503
  · exact kvjstaticRange_483.get (by omega) (by omega)
  by_cases h29 : j < 521
  · exact kvjstaticRange_503.get (by omega) (by omega)
  by_cases h30 : j < 537
  · exact kvjstaticRange_521.get (by omega) (by omega)
  by_cases h31 : j < 554
  · exact kvjstaticRange_537.get (by omega) (by omega)
  by_cases h32 : j < 572
  · exact kvjstaticRange_554.get (by omega) (by omega)
  by_cases h33 : j < 591
  · exact kvjstaticRange_572.get (by omega) (by omega)
  by_cases h34 : j < 607
  · exact kvjstaticRange_591.get (by omega) (by omega)
  by_cases h35 : j < 626
  · exact kvjstaticRange_607.get (by omega) (by omega)
  by_cases h36 : j < 642
  · exact kvjstaticRange_626.get (by omega) (by omega)
  by_cases h37 : j < 657
  · exact kvjstaticRange_642.get (by omega) (by omega)
  by_cases h38 : j < 673
  · exact kvjstaticRange_657.get (by omega) (by omega)
  by_cases h39 : j < 688
  · exact kvjstaticRange_673.get (by omega) (by omega)
  by_cases h40 : j < 704
  · exact kvjstaticRange_688.get (by omega) (by omega)
  by_cases h41 : j < 721
  · exact kvjstaticRange_704.get (by omega) (by omega)
  by_cases h42 : j < 739
  · exact kvjstaticRange_721.get (by omega) (by omega)
  by_cases h43 : j < 758
  · exact kvjstaticRange_739.get (by omega) (by omega)
  by_cases h44 : j < 774
  · exact kvjstaticRange_758.get (by omega) (by omega)
  by_cases h45 : j < 793
  · exact kvjstaticRange_774.get (by omega) (by omega)
  by_cases h46 : j < 817
  · exact kvjstaticRange_793.get (by omega) (by omega)
  by_cases h47 : j < 841
  · exact kvjstaticRange_817.get (by omega) (by omega)
  by_cases h48 : j < 853
  · exact kvjstaticRange_841.get (by omega) (by omega)
  by_cases h49 : j < 859
  · exact kvjstaticRange_853.get (by omega) (by omega)
  by_cases h50 : j < 863
  · exact kvjstaticRange_859.get (by omega) (by omega)
  by_cases h51 : j < 867
  · exact kvjstaticRange_863.get (by omega) (by omega)
  by_cases h52 : j < 869
  · exact kvjstaticRange_867.get (by omega) (by omega)
  by_cases h53 : j < 873
  · exact kvjstaticRange_869.get (by omega) (by omega)
  by_cases h54 : j < 875
  · exact kvjstaticRange_873.get (by omega) (by omega)
  by_cases h55 : j < 879
  · exact kvjstaticRange_875.get (by omega) (by omega)
  by_cases h56 : j < 881
  · exact kvjstaticRange_879.get (by omega) (by omega)
  by_cases h57 : j < 885
  · exact kvjstaticRange_881.get (by omega) (by omega)
  by_cases h58 : j < 887
  · exact kvjstaticRange_885.get (by omega) (by omega)
  by_cases h59 : j < 891
  · exact kvjstaticRange_887.get (by omega) (by omega)
  by_cases h60 : j < 895
  · exact kvjstaticRange_891.get (by omega) (by omega)
  by_cases h61 : j < 897
  · exact kvjstaticRange_895.get (by omega) (by omega)
  by_cases h62 : j < 899
  · exact kvjstaticRange_897.get (by omega) (by omega)
  by_cases h63 : j < 901
  · exact kvjstaticRange_899.get (by omega) (by omega)
  by_cases h64 : j < 903
  · exact kvjstaticRange_901.get (by omega) (by omega)
  by_cases h65 : j < 905
  · exact kvjstaticRange_903.get (by omega) (by omega)
  by_cases h66 : j < 907
  · exact kvjstaticRange_905.get (by omega) (by omega)
  by_cases h67 : j < 909
  · exact kvjstaticRange_907.get (by omega) (by omega)
  by_cases h68 : j < 911
  · exact kvjstaticRange_909.get (by omega) (by omega)
  by_cases h69 : j < 913
  · exact kvjstaticRange_911.get (by omega) (by omega)
  by_cases h70 : j < 917
  · exact kvjstaticRange_913.get (by omega) (by omega)
  by_cases h71 : j < 918
  · exact kvjstaticRange_917.get (by omega) (by omega)
  by_cases h72 : j < 919
  · exact kvjstaticRange_918.get (by omega) (by omega)
  by_cases h73 : j < 920
  · exact kvjstaticRange_919.get (by omega) (by omega)
  by_cases h74 : j < 921
  · exact kvjstaticRange_920.get (by omega) (by omega)
  by_cases h75 : j < 922
  · exact kvjstaticRange_921.get (by omega) (by omega)
  by_cases h76 : j < 923
  · exact kvjstaticRange_922.get (by omega) (by omega)
  by_cases h77 : j < 925
  · exact kvjstaticRange_923.get (by omega) (by omega)
  by_cases h78 : j < 927
  · exact kvjstaticRange_925.get (by omega) (by omega)
  by_cases h79 : j < 931
  · exact kvjstaticRange_927.get (by omega) (by omega)
  by_cases h80 : j < 932
  · exact kvjstaticRange_931.get (by omega) (by omega)
  by_cases h81 : j < 933
  · exact kvjstaticRange_932.get (by omega) (by omega)
  by_cases h82 : j < 934
  · exact kvjstaticRange_933.get (by omega) (by omega)
  by_cases h83 : j < 935
  · exact kvjstaticRange_934.get (by omega) (by omega)
  by_cases h84 : j < 936
  · exact kvjstaticRange_935.get (by omega) (by omega)
  by_cases h85 : j < 938
  · exact kvjstaticRange_936.get (by omega) (by omega)
  by_cases h86 : j < 940
  · exact kvjstaticRange_938.get (by omega) (by omega)
  by_cases h87 : j < 942
  · exact kvjstaticRange_940.get (by omega) (by omega)
  by_cases h88 : j < 944
  · exact kvjstaticRange_942.get (by omega) (by omega)
  exact kvjstaticRange_944.get (by omega) (by omega)

end
end LeanVM.Guest
