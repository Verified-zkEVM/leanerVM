/-
  LeanVM.Guest.Memory.GuestCntVD.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVD.Part00
public import LeanVM.Guest.Memory.GuestCntVD.Part01
public import LeanVM.Guest.Memory.GuestCntVD.Part02
public import LeanVM.Guest.Memory.GuestCntVD.Part03
public import LeanVM.Guest.Memory.GuestCntVD.Part04
public import LeanVM.Guest.Memory.GuestCntVD.Part05
public import LeanVM.Guest.Memory.GuestCntVD.Part06
public import LeanVM.Guest.Memory.GuestCntVD.Part07
public import LeanVM.Guest.Memory.GuestCntVD.Part08
public import LeanVM.Guest.Memory.GuestCntVD.Part09
public import LeanVM.Guest.Memory.GuestCntVD.Part10
public import LeanVM.Guest.Memory.GuestCntVD.Part11
public import LeanVM.Guest.Memory.GuestCntVD.Part12
public import LeanVM.Guest.Memory.GuestCntVD.Part13
public import LeanVM.Guest.Memory.GuestCntVD.Part14
public import LeanVM.Guest.Memory.GuestCntVD.Part15
public import LeanVM.Guest.Memory.GuestCntVD.Part16
public import LeanVM.Guest.Memory.GuestCntVD.Part17
public import LeanVM.Guest.Memory.GuestCntVD.Part18
public import LeanVM.Guest.Memory.GuestCntVD.Part19
public import LeanVM.Guest.Memory.GuestCntVD.Part20
public import LeanVM.Guest.Memory.GuestCntVD.Part21
public import LeanVM.Guest.Memory.GuestCntVD.Part22
public import LeanVM.Guest.Memory.GuestCntVD.Part23
public import LeanVM.Guest.Memory.GuestCntVD.Part24
public import LeanVM.Guest.Memory.GuestCntVD.Part25
public import LeanVM.Guest.Memory.GuestCntVD.Part26
public import LeanVM.Guest.Memory.GuestCntVD.Part27
public import LeanVM.Guest.Memory.GuestCntVD.Part28
public import LeanVM.Guest.Memory.GuestCntVD.Part29
public import LeanVM.Guest.Memory.GuestCntVD.Part30
public import LeanVM.Guest.Memory.GuestCntVD.Part31
public import LeanVM.Guest.Memory.GuestCntVD.Part32
public import LeanVM.Guest.Memory.GuestCntVD.Part33
public import LeanVM.Guest.Memory.GuestCntVD.Part34
public import LeanVM.Guest.Memory.GuestCntVD.Part35
public import LeanVM.Guest.Memory.GuestCntVD.Part36
public import LeanVM.Guest.Memory.GuestCntVD.Part37
public import LeanVM.Guest.Memory.GuestCntVD.Part38
public import LeanVM.Guest.Memory.GuestCntVD.Part39
public import LeanVM.Guest.Memory.GuestCntVD.Part40
public import LeanVM.Guest.Memory.GuestCntVD.Part41
public import LeanVM.Guest.Memory.GuestCntVD.Part42
public import LeanVM.Guest.Memory.GuestCntVD.Part43

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdchkIdx_307 : kvdchkIdx 307 = true := by
  have hb : blockB (kvdlookJ 307) (kvdomLookJ 307) false [(.n 347, 0), (.n 348, 25), (.n 396, 112), (.n 584, 0), (.n 585, 7), (.n 638, 56), (.n 826, 0), (.n 827, 4), (.n 878, 32), (.n 1066, 0), (.n 1067, 3), (.n 1120, 23), (.n 1206, 0), (.n 1207, 2), (.n 1258, 18), (.n 1922, 0), (.n 1923, 28), (.n 1936, 0), (.n 1937, 7), (.n 1950, 0), (.n 1951, 4), (.n 1964, 0), (.n 1965, 2), (.n 2307, 0), (.n 2308, 2)] Data.core307.params Data.core307.name ([], []) Data.core307.body = some (⟨19223, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core307.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_307_0.1 rfl kvdsplit_307_0.2.2,
      ← blockR_eq ((Data.core307.body.drop 0).take 1320), kvdsplit_307_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_307_1320.1 rfl kvdsplit_307_1320.2.2,
      ← blockR_eq ((Data.core307.body.drop 1320).take 1320), kvdsplit_307_1320.2.1]
    rw [← blockR_eq (Data.core307.body.drop 2640), kvdsplit_307_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core307) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_308 : kvdchkIdx 308 = true := by
  have hb : blockB (kvdlookJ 308) (kvdomLookJ 308) false [(.n 347, 0), (.n 348, 29), (.n 397, 112), (.n 585, 0), (.n 586, 7), (.n 639, 56), (.n 827, 0), (.n 828, 4), (.n 879, 32), (.n 1067, 0), (.n 1068, 3), (.n 1121, 23), (.n 1207, 0), (.n 1208, 2), (.n 1259, 18), (.n 1970, 0), (.n 1971, 28), (.n 2109, 0), (.n 2110, 7), (.n 2123, 0), (.n 2124, 4), (.n 2137, 0), (.n 2138, 2), (.n 2522, 0), (.n 2523, 2)] Data.core308.params Data.core308.name ([], []) Data.core308.body = some (⟨19750, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core308.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_308_0.1 rfl kvdsplit_308_0.2.2,
      ← blockR_eq ((Data.core308.body.drop 0).take 1320), kvdsplit_308_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_308_1320.1 rfl kvdsplit_308_1320.2.2,
      ← blockR_eq ((Data.core308.body.drop 1320).take 1320), kvdsplit_308_1320.2.1]
    rw [← blockR_eq (Data.core308.body.drop 2640), kvdsplit_308_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core308) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_309 : kvdchkIdx 309 = true := by
  have hb : blockB (kvdlookJ 309) (kvdomLookJ 309) false [(.n 347, 0), (.n 348, 29), (.n 397, 112), (.n 585, 0), (.n 586, 7), (.n 639, 56), (.n 827, 0), (.n 828, 4), (.n 879, 32), (.n 1067, 0), (.n 1068, 3), (.n 1121, 23), (.n 1309, 0), (.n 1310, 2), (.n 1361, 18), (.n 1447, 0), (.n 1448, 2), (.n 1499, 14), (.n 2230, 0), (.n 2231, 28), (.n 2375, 0), (.n 2376, 7), (.n 2389, 0), (.n 2390, 4), (.n 2403, 0), (.n 2404, 2), (.n 2830, 0), (.n 2831, 2), (.n 2914, 0), (.n 2915, 1)] Data.core309.params Data.core309.name ([], []) Data.core309.body = some (⟨20359, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core309.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvdsplit_309_0.1 rfl kvdsplit_309_0.2.2,
      ← blockR_eq ((Data.core309.body.drop 0).take 1111), kvdsplit_309_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvdsplit_309_1111.1 rfl kvdsplit_309_1111.2.2,
      ← blockR_eq ((Data.core309.body.drop 1111).take 1111), kvdsplit_309_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvdsplit_309_2222.1 rfl kvdsplit_309_2222.2.2,
      ← blockR_eq ((Data.core309.body.drop 2222).take 1111), kvdsplit_309_2222.2.1]
    rw [← blockR_eq (Data.core309.body.drop 3333), kvdsplit_309_3333]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core309) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_312 : kvdchkIdx 312 = true := by
  have hb : blockB (kvdlookJ 312) (kvdomLookJ 312) false [(.n 347, 0), (.n 348, 13), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 3), (.n 879, 28), (.n 1067, 0), (.n 1068, 2), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1827, 0), (.n 1828, 14), (.n 1841, 0), (.n 1842, 5), (.n 2270, 0), (.n 2271, 3), (.n 2520, 0), (.n 2521, 2), (.n 2709, 0), (.n 2710, 2)] Data.core312.params Data.core312.name ([], []) Data.core312.body = some (⟨12079, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core312.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_312_0.1 rfl kvdsplit_312_0.2.2,
      ← blockR_eq ((Data.core312.body.drop 0).take 1320), kvdsplit_312_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_312_1320.1 rfl kvdsplit_312_1320.2.2,
      ← blockR_eq ((Data.core312.body.drop 1320).take 1320), kvdsplit_312_1320.2.1]
    rw [← blockR_eq (Data.core312.body.drop 2640), kvdsplit_312_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core312) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_313 : kvdchkIdx 313 = true := by
  have hb : blockB (kvdlookJ 313) (kvdomLookJ 313) false [(.n 347, 0), (.n 348, 13), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 3), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1874, 0), (.n 1875, 14), (.n 1888, 0), (.n 1889, 5), (.n 2347, 0), (.n 2348, 3), (.n 2621, 0), (.n 2622, 2), (.n 2840, 0), (.n 2841, 2)] Data.core313.params Data.core313.name ([], []) Data.core313.body = some (⟨12381, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core313.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_313_0.1 rfl kvdsplit_313_0.2.2,
      ← blockR_eq ((Data.core313.body.drop 0).take 1320), kvdsplit_313_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_313_1320.1 rfl kvdsplit_313_1320.2.2,
      ← blockR_eq ((Data.core313.body.drop 1320).take 1320), kvdsplit_313_1320.2.1]
    rw [← blockR_eq (Data.core313.body.drop 2640), kvdsplit_313_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core313) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_314 : kvdchkIdx 314 = true := by
  have hb : blockB (kvdlookJ 314) (kvdomLookJ 314) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1921, 0), (.n 1922, 14), (.n 1935, 0), (.n 1936, 5), (.n 2424, 0), (.n 2425, 3), (.n 2722, 0), (.n 2723, 2), (.n 2971, 0), (.n 2972, 2)] Data.core314.params Data.core314.name ([], []) Data.core314.body = some (⟨12560, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core314.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_314_0.1 rfl kvdsplit_314_0.2.2,
      ← blockR_eq ((Data.core314.body.drop 0).take 1320), kvdsplit_314_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_314_1320.1 rfl kvdsplit_314_1320.2.2,
      ← blockR_eq ((Data.core314.body.drop 1320).take 1320), kvdsplit_314_1320.2.1]
    rw [← blockR_eq (Data.core314.body.drop 2640), kvdsplit_314_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core314) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_315 : kvdchkIdx 315 = true := by
  have hb : blockB (kvdlookJ 315) (kvdomLookJ 315) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 6), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1968, 0), (.n 1969, 14), (.n 1982, 0), (.n 1983, 5), (.n 2501, 0), (.n 2502, 3), (.n 2823, 0), (.n 2824, 2), (.n 3102, 0), (.n 3103, 2)] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨12663, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_315_0.1 rfl kvdsplit_315_0.2.2,
      ← blockR_eq ((Data.core315.body.drop 0).take 1320), kvdsplit_315_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_315_1320.1 rfl kvdsplit_315_1320.2.2,
      ← blockR_eq ((Data.core315.body.drop 1320).take 1320), kvdsplit_315_1320.2.1]
    rw [← blockR_eq (Data.core315.body.drop 2640), kvdsplit_315_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_316 : kvdchkIdx 316 = true := by
  have hb : blockB (kvdlookJ 316) (kvdomLookJ 316) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 6), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1308, 0), (.n 1309, 2), (.n 1359, 16), (.n 1445, 0), (.n 1446, 2), (.n 1497, 13), (.n 2228, 0), (.n 2229, 14), (.n 2242, 0), (.n 2243, 5), (.n 2791, 0), (.n 2792, 3), (.n 3137, 0), (.n 3138, 2), (.n 3446, 0), (.n 3447, 2), (.n 3460, 0), (.n 3461, 1)] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨13233, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvdsplit_316_0.1 rfl kvdsplit_316_0.2.2,
      ← blockR_eq ((Data.core316.body.drop 0).take 1111), kvdsplit_316_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvdsplit_316_1111.1 rfl kvdsplit_316_1111.2.2,
      ← blockR_eq ((Data.core316.body.drop 1111).take 1111), kvdsplit_316_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvdsplit_316_2222.1 rfl kvdsplit_316_2222.2.2,
      ← blockR_eq ((Data.core316.body.drop 2222).take 1111), kvdsplit_316_2222.2.1]
    rw [← blockR_eq (Data.core316.body.drop 3333), kvdsplit_316_3333]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_319 : kvdchkIdx 319 = true := by
  have hb : blockB (kvdlookJ 319) (kvdomLookJ 319) false [(.n 347, 0), (.n 348, 9), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 2), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1829, 0), (.n 1830, 9), (.n 2164, 0), (.n 2165, 4), (.n 2676, 0), (.n 2677, 3), (.n 2749, 0), (.n 2750, 2), (.n 2868, 0), (.n 2869, 1)] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨10159, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_319_0.1 rfl kvdsplit_319_0.2.2,
      ← blockR_eq ((Data.core319.body.drop 0).take 1320), kvdsplit_319_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_319_1320.1 rfl kvdsplit_319_1320.2.2,
      ← blockR_eq ((Data.core319.body.drop 1320).take 1320), kvdsplit_319_1320.2.1]
    rw [← blockR_eq (Data.core319.body.drop 2640), kvdsplit_319_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_320 : kvdchkIdx 320 = true := by
  have hb : blockB (kvdlookJ 320) (kvdomLookJ 320) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 2), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1876, 0), (.n 1877, 9), (.n 2229, 0), (.n 2230, 4), (.n 2777, 0), (.n 2778, 3), (.n 2856, 0), (.n 2857, 2), (.n 2993, 0), (.n 2994, 1)] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨10186, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_320_0.1 rfl kvdsplit_320_0.2.2,
      ← blockR_eq ((Data.core320.body.drop 0).take 1320), kvdsplit_320_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_320_1320.1 rfl kvdsplit_320_1320.2.2,
      ← blockR_eq ((Data.core320.body.drop 1320).take 1320), kvdsplit_320_1320.2.1]
    rw [← blockR_eq (Data.core320.body.drop 2640), kvdsplit_320_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_321 : kvdchkIdx 321 = true := by
  have hb : blockB (kvdlookJ 321) (kvdomLookJ 321) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1923, 0), (.n 1924, 9), (.n 2294, 0), (.n 2295, 4), (.n 2878, 0), (.n 2879, 3), (.n 2963, 0), (.n 2964, 2), (.n 3118, 0), (.n 3119, 1)] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨10298, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_321_0.1 rfl kvdsplit_321_0.2.2,
      ← blockR_eq ((Data.core321.body.drop 0).take 1320), kvdsplit_321_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_321_1320.1 rfl kvdsplit_321_1320.2.2,
      ← blockR_eq ((Data.core321.body.drop 1320).take 1320), kvdsplit_321_1320.2.1]
    rw [← blockR_eq (Data.core321.body.drop 2640), kvdsplit_321_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_322 : kvdchkIdx 322 = true := by
  have hb : blockB (kvdlookJ 322) (kvdomLookJ 322) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 4), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1970, 0), (.n 1971, 9), (.n 2359, 0), (.n 2360, 4), (.n 2979, 0), (.n 2980, 3), (.n 3070, 0), (.n 3071, 2), (.n 3243, 0), (.n 3244, 1)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨10370, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_322_0.1 rfl kvdsplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 1320), kvdsplit_322_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_322_1320.1 rfl kvdsplit_322_1320.2.2,
      ← blockR_eq ((Data.core322.body.drop 1320).take 1320), kvdsplit_322_1320.2.1]
    rw [← blockR_eq (Data.core322.body.drop 2640), kvdsplit_322_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_323 : kvdchkIdx 323 = true := by
  have hb : blockB (kvdlookJ 323) (kvdomLookJ 323) false [(.n 347, 0), (.n 348, 11), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 4), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1308, 0), (.n 1309, 2), (.n 1361, 15), (.n 1447, 0), (.n 1448, 2), (.n 1499, 13), (.n 2230, 0), (.n 2231, 9), (.n 2637, 0), (.n 2638, 4), (.n 3293, 0), (.n 3294, 3), (.n 3390, 0), (.n 3391, 2), (.n 3581, 0), (.n 3582, 1), (.n 3840, 0), (.n 3841, 1)] Data.core323.params Data.core323.name ([], []) Data.core323.body = some (⟨11115, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core323.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvdsplit_323_0.1 rfl kvdsplit_323_0.2.2,
      ← blockR_eq ((Data.core323.body.drop 0).take 1111), kvdsplit_323_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvdsplit_323_1111.1 rfl kvdsplit_323_1111.2.2,
      ← blockR_eq ((Data.core323.body.drop 1111).take 1111), kvdsplit_323_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvdsplit_323_2222.1 rfl kvdsplit_323_2222.2.2,
      ← blockR_eq ((Data.core323.body.drop 2222).take 1111), kvdsplit_323_2222.2.1]
    rw [← blockR_eq (Data.core323.body.drop 3333), kvdsplit_323_3333]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core323) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_326 : kvdchkIdx 326 = true := by
  have hb : blockB (kvdlookJ 326) (kvdomLookJ 326) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1824, 0), (.n 1825, 7), (.n 1838, 0), (.n 1839, 4), (.n 1852, 0), (.n 1853, 2), (.n 2279, 0), (.n 2280, 2), (.n 2363, 0), (.n 2364, 1)] Data.core326.params Data.core326.name ([], []) Data.core326.body = some (⟨8160, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core326.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_326_0.1 rfl kvdsplit_326_0.2.2,
      ← blockR_eq ((Data.core326.body.drop 0).take 1320), kvdsplit_326_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_326_1320.1 rfl kvdsplit_326_1320.2.2,
      ← blockR_eq ((Data.core326.body.drop 1320).take 1320), kvdsplit_326_1320.2.1]
    rw [← blockR_eq (Data.core326.body.drop 2640), kvdsplit_326_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core326) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_327 : kvdchkIdx 327 = true := by
  have hb : blockB (kvdlookJ 327) (kvdomLookJ 327) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1871, 0), (.n 1872, 7), (.n 1885, 0), (.n 1886, 4), (.n 1899, 0), (.n 1900, 2), (.n 2368, 0), (.n 2369, 2), (.n 2464, 0), (.n 2465, 1)] Data.core327.params Data.core327.name ([], []) Data.core327.body = some (⟨8061, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core327.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_327_0.1 rfl kvdsplit_327_0.2.2,
      ← blockR_eq ((Data.core327.body.drop 0).take 1320), kvdsplit_327_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_327_1320.1 rfl kvdsplit_327_1320.2.2,
      ← blockR_eq ((Data.core327.body.drop 1320).take 1320), kvdsplit_327_1320.2.1]
    rw [← blockR_eq (Data.core327.body.drop 2640), kvdsplit_327_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core327) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_328 : kvdchkIdx 328 = true := by
  have hb : blockB (kvdlookJ 328) (kvdomLookJ 328) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1918, 0), (.n 1919, 7), (.n 1932, 0), (.n 1933, 4), (.n 1946, 0), (.n 1947, 2), (.n 2457, 0), (.n 2458, 2), (.n 2565, 0), (.n 2566, 1)] Data.core328.params Data.core328.name ([], []) Data.core328.body = some (⟨8000, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core328.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_328_0.1 rfl kvdsplit_328_0.2.2,
      ← blockR_eq ((Data.core328.body.drop 0).take 1320), kvdsplit_328_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_328_1320.1 rfl kvdsplit_328_1320.2.2,
      ← blockR_eq ((Data.core328.body.drop 1320).take 1320), kvdsplit_328_1320.2.1]
    rw [← blockR_eq (Data.core328.body.drop 2640), kvdsplit_328_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core328) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_329 : kvdchkIdx 329 = true := by
  have hb : blockB (kvdlookJ 329) (kvdomLookJ 329) false [(.n 347, 0), (.n 348, 8), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 3), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1255, 15), (.n 1966, 0), (.n 1967, 7), (.n 1980, 0), (.n 1981, 4), (.n 1994, 0), (.n 1995, 2), (.n 2547, 0), (.n 2548, 2), (.n 2667, 0), (.n 2668, 1)] Data.core329.params Data.core329.name ([], []) Data.core329.body = some (⟨8743, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core329.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_329_0.1 rfl kvdsplit_329_0.2.2,
      ← blockR_eq ((Data.core329.body.drop 0).take 1320), kvdsplit_329_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_329_1320.1 rfl kvdsplit_329_1320.2.2,
      ← blockR_eq ((Data.core329.body.drop 1320).take 1320), kvdsplit_329_1320.2.1]
    rw [← blockR_eq (Data.core329.body.drop 2640), kvdsplit_329_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core329) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_330 : kvdchkIdx 330 = true := by
  have hb : blockB (kvdlookJ 330) (kvdomLookJ 330) false [(.n 347, 0), (.n 348, 8), (.n 394, 28), (.n 582, 0), (.n 583, 5), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 3), (.n 1116, 18), (.n 1304, 0), (.n 1305, 2), (.n 1357, 15), (.n 1443, 0), (.n 1444, 2), (.n 1494, 12), (.n 2225, 0), (.n 2226, 7), (.n 2239, 0), (.n 2240, 4), (.n 2253, 0), (.n 2254, 2), (.n 2848, 0), (.n 2849, 2), (.n 2980, 0), (.n 2981, 1), (.n 3239, 0), (.n 3240, 1)] Data.core330.params Data.core330.name ([], []) Data.core330.body = some (⟨9611, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core330.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvdsplit_330_0.1 rfl kvdsplit_330_0.2.2,
      ← blockR_eq ((Data.core330.body.drop 0).take 1111), kvdsplit_330_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvdsplit_330_1111.1 rfl kvdsplit_330_1111.2.2,
      ← blockR_eq ((Data.core330.body.drop 1111).take 1111), kvdsplit_330_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvdsplit_330_2222.1 rfl kvdsplit_330_2222.2.2,
      ← blockR_eq ((Data.core330.body.drop 2222).take 1111), kvdsplit_330_2222.2.1]
    rw [← blockR_eq (Data.core330.body.drop 3333), kvdsplit_330_3333]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core330) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvdchkIdx_all : ∀ j < 947, kvdchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 307
  · subst h1000; exact kvdchkIdx_307
  by_cases h1001 : j = 308
  · subst h1001; exact kvdchkIdx_308
  by_cases h1002 : j = 309
  · subst h1002; exact kvdchkIdx_309
  by_cases h1003 : j = 312
  · subst h1003; exact kvdchkIdx_312
  by_cases h1004 : j = 313
  · subst h1004; exact kvdchkIdx_313
  by_cases h1005 : j = 314
  · subst h1005; exact kvdchkIdx_314
  by_cases h1006 : j = 315
  · subst h1006; exact kvdchkIdx_315
  by_cases h1007 : j = 316
  · subst h1007; exact kvdchkIdx_316
  by_cases h1008 : j = 319
  · subst h1008; exact kvdchkIdx_319
  by_cases h1009 : j = 320
  · subst h1009; exact kvdchkIdx_320
  by_cases h1010 : j = 321
  · subst h1010; exact kvdchkIdx_321
  by_cases h1011 : j = 322
  · subst h1011; exact kvdchkIdx_322
  by_cases h1012 : j = 323
  · subst h1012; exact kvdchkIdx_323
  by_cases h1013 : j = 326
  · subst h1013; exact kvdchkIdx_326
  by_cases h1014 : j = 327
  · subst h1014; exact kvdchkIdx_327
  by_cases h1015 : j = 328
  · subst h1015; exact kvdchkIdx_328
  by_cases h1016 : j = 329
  · subst h1016; exact kvdchkIdx_329
  by_cases h1017 : j = 330
  · subst h1017; exact kvdchkIdx_330
  by_cases h0 : j < 11
  · exact kvdstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvdstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvdstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvdstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvdstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvdstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvdstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvdstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvdstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvdstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvdstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 304
  · exact kvdstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 305
  · exact kvdstaticRange_304.get (by omega) (by omega)
  by_cases h13 : j < 306
  · exact kvdstaticRange_305.get (by omega) (by omega)
  by_cases h14 : j < 307
  · exact kvdstaticRange_306.get (by omega) (by omega)
  by_cases h15 : j < 311
  · exact kvdstaticRange_310.get (by omega) (by omega)
  by_cases h16 : j < 312
  · exact kvdstaticRange_311.get (by omega) (by omega)
  by_cases h17 : j < 318
  · exact kvdstaticRange_317.get (by omega) (by omega)
  by_cases h18 : j < 319
  · exact kvdstaticRange_318.get (by omega) (by omega)
  by_cases h19 : j < 325
  · exact kvdstaticRange_324.get (by omega) (by omega)
  by_cases h20 : j < 326
  · exact kvdstaticRange_325.get (by omega) (by omega)
  by_cases h21 : j < 352
  · exact kvdstaticRange_331.get (by omega) (by omega)
  by_cases h22 : j < 374
  · exact kvdstaticRange_352.get (by omega) (by omega)
  by_cases h23 : j < 397
  · exact kvdstaticRange_374.get (by omega) (by omega)
  by_cases h24 : j < 411
  · exact kvdstaticRange_397.get (by omega) (by omega)
  by_cases h25 : j < 441
  · exact kvdstaticRange_411.get (by omega) (by omega)
  by_cases h26 : j < 462
  · exact kvdstaticRange_441.get (by omega) (by omega)
  by_cases h27 : j < 483
  · exact kvdstaticRange_462.get (by omega) (by omega)
  by_cases h28 : j < 503
  · exact kvdstaticRange_483.get (by omega) (by omega)
  by_cases h29 : j < 521
  · exact kvdstaticRange_503.get (by omega) (by omega)
  by_cases h30 : j < 537
  · exact kvdstaticRange_521.get (by omega) (by omega)
  by_cases h31 : j < 554
  · exact kvdstaticRange_537.get (by omega) (by omega)
  by_cases h32 : j < 572
  · exact kvdstaticRange_554.get (by omega) (by omega)
  by_cases h33 : j < 591
  · exact kvdstaticRange_572.get (by omega) (by omega)
  by_cases h34 : j < 607
  · exact kvdstaticRange_591.get (by omega) (by omega)
  by_cases h35 : j < 626
  · exact kvdstaticRange_607.get (by omega) (by omega)
  by_cases h36 : j < 642
  · exact kvdstaticRange_626.get (by omega) (by omega)
  by_cases h37 : j < 657
  · exact kvdstaticRange_642.get (by omega) (by omega)
  by_cases h38 : j < 673
  · exact kvdstaticRange_657.get (by omega) (by omega)
  by_cases h39 : j < 688
  · exact kvdstaticRange_673.get (by omega) (by omega)
  by_cases h40 : j < 704
  · exact kvdstaticRange_688.get (by omega) (by omega)
  by_cases h41 : j < 721
  · exact kvdstaticRange_704.get (by omega) (by omega)
  by_cases h42 : j < 739
  · exact kvdstaticRange_721.get (by omega) (by omega)
  by_cases h43 : j < 758
  · exact kvdstaticRange_739.get (by omega) (by omega)
  by_cases h44 : j < 774
  · exact kvdstaticRange_758.get (by omega) (by omega)
  by_cases h45 : j < 793
  · exact kvdstaticRange_774.get (by omega) (by omega)
  by_cases h46 : j < 817
  · exact kvdstaticRange_793.get (by omega) (by omega)
  by_cases h47 : j < 841
  · exact kvdstaticRange_817.get (by omega) (by omega)
  by_cases h48 : j < 853
  · exact kvdstaticRange_841.get (by omega) (by omega)
  by_cases h49 : j < 859
  · exact kvdstaticRange_853.get (by omega) (by omega)
  by_cases h50 : j < 863
  · exact kvdstaticRange_859.get (by omega) (by omega)
  by_cases h51 : j < 867
  · exact kvdstaticRange_863.get (by omega) (by omega)
  by_cases h52 : j < 869
  · exact kvdstaticRange_867.get (by omega) (by omega)
  by_cases h53 : j < 873
  · exact kvdstaticRange_869.get (by omega) (by omega)
  by_cases h54 : j < 875
  · exact kvdstaticRange_873.get (by omega) (by omega)
  by_cases h55 : j < 879
  · exact kvdstaticRange_875.get (by omega) (by omega)
  by_cases h56 : j < 881
  · exact kvdstaticRange_879.get (by omega) (by omega)
  by_cases h57 : j < 885
  · exact kvdstaticRange_881.get (by omega) (by omega)
  by_cases h58 : j < 887
  · exact kvdstaticRange_885.get (by omega) (by omega)
  by_cases h59 : j < 891
  · exact kvdstaticRange_887.get (by omega) (by omega)
  by_cases h60 : j < 895
  · exact kvdstaticRange_891.get (by omega) (by omega)
  by_cases h61 : j < 897
  · exact kvdstaticRange_895.get (by omega) (by omega)
  by_cases h62 : j < 899
  · exact kvdstaticRange_897.get (by omega) (by omega)
  by_cases h63 : j < 901
  · exact kvdstaticRange_899.get (by omega) (by omega)
  by_cases h64 : j < 903
  · exact kvdstaticRange_901.get (by omega) (by omega)
  by_cases h65 : j < 905
  · exact kvdstaticRange_903.get (by omega) (by omega)
  by_cases h66 : j < 907
  · exact kvdstaticRange_905.get (by omega) (by omega)
  by_cases h67 : j < 909
  · exact kvdstaticRange_907.get (by omega) (by omega)
  by_cases h68 : j < 911
  · exact kvdstaticRange_909.get (by omega) (by omega)
  by_cases h69 : j < 913
  · exact kvdstaticRange_911.get (by omega) (by omega)
  by_cases h70 : j < 917
  · exact kvdstaticRange_913.get (by omega) (by omega)
  by_cases h71 : j < 918
  · exact kvdstaticRange_917.get (by omega) (by omega)
  by_cases h72 : j < 919
  · exact kvdstaticRange_918.get (by omega) (by omega)
  by_cases h73 : j < 920
  · exact kvdstaticRange_919.get (by omega) (by omega)
  by_cases h74 : j < 921
  · exact kvdstaticRange_920.get (by omega) (by omega)
  by_cases h75 : j < 922
  · exact kvdstaticRange_921.get (by omega) (by omega)
  by_cases h76 : j < 923
  · exact kvdstaticRange_922.get (by omega) (by omega)
  by_cases h77 : j < 925
  · exact kvdstaticRange_923.get (by omega) (by omega)
  by_cases h78 : j < 927
  · exact kvdstaticRange_925.get (by omega) (by omega)
  by_cases h79 : j < 931
  · exact kvdstaticRange_927.get (by omega) (by omega)
  by_cases h80 : j < 932
  · exact kvdstaticRange_931.get (by omega) (by omega)
  by_cases h81 : j < 933
  · exact kvdstaticRange_932.get (by omega) (by omega)
  by_cases h82 : j < 934
  · exact kvdstaticRange_933.get (by omega) (by omega)
  by_cases h83 : j < 935
  · exact kvdstaticRange_934.get (by omega) (by omega)
  by_cases h84 : j < 936
  · exact kvdstaticRange_935.get (by omega) (by omega)
  by_cases h85 : j < 938
  · exact kvdstaticRange_936.get (by omega) (by omega)
  by_cases h86 : j < 940
  · exact kvdstaticRange_938.get (by omega) (by omega)
  by_cases h87 : j < 942
  · exact kvdstaticRange_940.get (by omega) (by omega)
  by_cases h88 : j < 944
  · exact kvdstaticRange_942.get (by omega) (by omega)
  exact kvdstaticRange_944.get (by omega) (by omega)

end
end LeanVM.Guest
