/-
  LeanVM.Guest.Memory.GuestCntVX.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVX.Part00
public import LeanVM.Guest.Memory.GuestCntVX.Part01
public import LeanVM.Guest.Memory.GuestCntVX.Part02
public import LeanVM.Guest.Memory.GuestCntVX.Part03
public import LeanVM.Guest.Memory.GuestCntVX.Part04
public import LeanVM.Guest.Memory.GuestCntVX.Part05
public import LeanVM.Guest.Memory.GuestCntVX.Part06
public import LeanVM.Guest.Memory.GuestCntVX.Part07
public import LeanVM.Guest.Memory.GuestCntVX.Part08
public import LeanVM.Guest.Memory.GuestCntVX.Part09
public import LeanVM.Guest.Memory.GuestCntVX.Part10
public import LeanVM.Guest.Memory.GuestCntVX.Part11
public import LeanVM.Guest.Memory.GuestCntVX.Part12
public import LeanVM.Guest.Memory.GuestCntVX.Part13
public import LeanVM.Guest.Memory.GuestCntVX.Part14
public import LeanVM.Guest.Memory.GuestCntVX.Part15
public import LeanVM.Guest.Memory.GuestCntVX.Part16
public import LeanVM.Guest.Memory.GuestCntVX.Part17
public import LeanVM.Guest.Memory.GuestCntVX.Part18
public import LeanVM.Guest.Memory.GuestCntVX.Part19
public import LeanVM.Guest.Memory.GuestCntVX.Part20
public import LeanVM.Guest.Memory.GuestCntVX.Part21

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxchkIdx_298 : kvxchkIdx 298 = true := by
  have hb : blockB (kvxlookJ 298) (kvxomLookJ 298) false [(.n 217, 0), (.n 218, 25), (.n 479, 112), (.n 666, 0), (.n 667, 6), (.n 767, 56), (.n 954, 0), (.n 955, 4), (.n 1031, 32), (.n 1218, 0), (.n 1219, 3), (.n 1286, 23), (.n 1371, 0), (.n 1372, 2), (.n 1433, 17), (.n 2048, 0), (.n 2049, 112), (.n 2061, 0), (.n 2062, 28), (.n 2074, 0), (.n 2075, 16), (.n 2087, 0), (.n 2088, 11), (.n 2142, 0), (.n 2143, 8)] Data.core298.params Data.core298.name ([], []) Data.core298.body = some (⟨64097, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core298.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvxsplit_298_0.1 rfl kvxsplit_298_0.2.2,
      ← blockR_eq ((Data.core298.body.drop 0).take 1320), kvxsplit_298_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvxsplit_298_1320.1 rfl kvxsplit_298_1320.2.2,
      ← blockR_eq ((Data.core298.body.drop 1320).take 1320), kvxsplit_298_1320.2.1]
    rw [← blockR_eq (Data.core298.body.drop 2640), kvxsplit_298_2640]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core298) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_299 : kvxchkIdx 299 = true := by
  have hb : blockB (kvxlookJ 299) (kvxomLookJ 299) false [(.n 217, 0), (.n 218, 25), (.n 479, 112), (.n 666, 0), (.n 667, 7), (.n 767, 56), (.n 954, 0), (.n 955, 4), (.n 1031, 32), (.n 1218, 0), (.n 1219, 3), (.n 1286, 23), (.n 1371, 0), (.n 1372, 2), (.n 1434, 18), (.n 2096, 0), (.n 2097, 112), (.n 2109, 0), (.n 2110, 28), (.n 2122, 0), (.n 2123, 16), (.n 2135, 0), (.n 2136, 11), (.n 2196, 0), (.n 2197, 9)] Data.core299.params Data.core299.name ([], []) Data.core299.body = some (⟨65504, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core299.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvxsplit_299_0.1 rfl kvxsplit_299_0.2.2,
      ← blockR_eq ((Data.core299.body.drop 0).take 1320), kvxsplit_299_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvxsplit_299_1320.1 rfl kvxsplit_299_1320.2.2,
      ← blockR_eq ((Data.core299.body.drop 1320).take 1320), kvxsplit_299_1320.2.1]
    rw [← blockR_eq (Data.core299.body.drop 2640), kvxsplit_299_2640]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core299) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_300 : kvxchkIdx 300 = true := by
  have hb : blockB (kvxlookJ 300) (kvxomLookJ 300) false [(.n 217, 0), (.n 218, 29), (.n 480, 112), (.n 667, 0), (.n 668, 7), (.n 768, 56), (.n 955, 0), (.n 956, 4), (.n 1032, 32), (.n 1219, 0), (.n 1220, 3), (.n 1287, 23), (.n 1372, 0), (.n 1373, 2), (.n 1435, 18), (.n 2144, 0), (.n 2145, 112), (.n 2283, 0), (.n 2284, 28), (.n 2296, 0), (.n 2297, 16), (.n 2309, 0), (.n 2310, 11), (.n 2376, 0), (.n 2377, 9)] Data.core300.params Data.core300.name ([], []) Data.core300.body = some (⟨67562, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core300.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvxsplit_300_0.1 rfl kvxsplit_300_0.2.2,
      ← blockR_eq ((Data.core300.body.drop 0).take 1320), kvxsplit_300_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvxsplit_300_1320.1 rfl kvxsplit_300_1320.2.2,
      ← blockR_eq ((Data.core300.body.drop 1320).take 1320), kvxsplit_300_1320.2.1]
    rw [← blockR_eq (Data.core300.body.drop 2640), kvxsplit_300_2640]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core300) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_301 : kvxchkIdx 301 = true := by
  have hb : blockB (kvxlookJ 301) (kvxomLookJ 301) false [(.n 217, 0), (.n 218, 29), (.n 480, 112), (.n 667, 0), (.n 668, 7), (.n 768, 56), (.n 955, 0), (.n 956, 4), (.n 1032, 32), (.n 1219, 0), (.n 1220, 3), (.n 1287, 23), (.n 1474, 0), (.n 1475, 2), (.n 1537, 18), (.n 1622, 0), (.n 1623, 2), (.n 1681, 14), (.n 2410, 0), (.n 2411, 112), (.n 2555, 0), (.n 2556, 28), (.n 2568, 0), (.n 2569, 16), (.n 2581, 0), (.n 2582, 11), (.n 2654, 0), (.n 2655, 9), (.n 2667, 0), (.n 2668, 7)] Data.core301.params Data.core301.name ([], []) Data.core301.body = some (⟨70379, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core301.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvxsplit_301_0.1 rfl kvxsplit_301_0.2.2,
      ← blockR_eq ((Data.core301.body.drop 0).take 1111), kvxsplit_301_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvxsplit_301_1111.1 rfl kvxsplit_301_1111.2.2,
      ← blockR_eq ((Data.core301.body.drop 1111).take 1111), kvxsplit_301_1111.2.1]
    rw [← blockR_eq (Data.core301.body.drop 2222), kvxsplit_301_2222]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core301) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_307 : kvxchkIdx 307 = true := by
  have hb : blockB (kvxlookJ 307) (kvxomLookJ 307) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1242, 0), (.n 1243, 2), (.n 1303, 16), (.n 2012, 0), (.n 2013, 56), (.n 2025, 0), (.n 2026, 22), (.n 2140, 0), (.n 2141, 14), (.n 2153, 0), (.n 2154, 10), (.n 2220, 0), (.n 2221, 8)] Data.core307.params Data.core307.name ([], []) Data.core307.body = some (⟨41044, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core307.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvxsplit_307_0.1 rfl kvxsplit_307_0.2.2,
      ← blockR_eq ((Data.core307.body.drop 0).take 1320), kvxsplit_307_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvxsplit_307_1320.1 rfl kvxsplit_307_1320.2.2,
      ← blockR_eq ((Data.core307.body.drop 1320).take 1320), kvxsplit_307_1320.2.1]
    rw [← blockR_eq (Data.core307.body.drop 2640), kvxsplit_307_2640]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core307) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_308 : kvxchkIdx 308 = true := by
  have hb : blockB (kvxlookJ 308) (kvxomLookJ 308) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1344, 0), (.n 1345, 2), (.n 1405, 16), (.n 1490, 0), (.n 1491, 2), (.n 1548, 13), (.n 2277, 0), (.n 2278, 56), (.n 2290, 0), (.n 2291, 22), (.n 2411, 0), (.n 2412, 14), (.n 2424, 0), (.n 2425, 10), (.n 2497, 0), (.n 2498, 8), (.n 2510, 0), (.n 2511, 6)] Data.core308.params Data.core308.name ([], []) Data.core308.body = some (⟨43376, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core308.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvxsplit_308_0.1 rfl kvxsplit_308_0.2.2,
      ← blockR_eq ((Data.core308.body.drop 0).take 1111), kvxsplit_308_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvxsplit_308_1111.1 rfl kvxsplit_308_1111.2.2,
      ← blockR_eq ((Data.core308.body.drop 1111).take 1111), kvxsplit_308_1111.2.1]
    rw [← blockR_eq (Data.core308.body.drop 2222), kvxsplit_308_2222]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core308) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_314 : kvxchkIdx 314 = true := by
  have hb : blockB (kvxlookJ 314) (kvxomLookJ 314) false [(.n 217, 0), (.n 218, 10), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1193, 0), (.n 1194, 2), (.n 1253, 15), (.n 1962, 0), (.n 1963, 37), (.n 2101, 0), (.n 2102, 19), (.n 2114, 0), (.n 2115, 12), (.n 2205, 0), (.n 2206, 9), (.n 2272, 0), (.n 2273, 7)] Data.core314.params Data.core314.name ([], []) Data.core314.body = some (⟨31572, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core314.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvxsplit_314_0.1 rfl kvxsplit_314_0.2.2,
      ← blockR_eq ((Data.core314.body.drop 0).take 1320), kvxsplit_314_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvxsplit_314_1320.1 rfl kvxsplit_314_1320.2.2,
      ← blockR_eq ((Data.core314.body.drop 1320).take 1320), kvxsplit_314_1320.2.1]
    rw [← blockR_eq (Data.core314.body.drop 2640), kvxsplit_314_2640]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core314) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_315 : kvxchkIdx 315 = true := by
  have hb : blockB (kvxlookJ 315) (kvxomLookJ 315) false [(.n 217, 0), (.n 218, 11), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1295, 0), (.n 1296, 2), (.n 1355, 15), (.n 1440, 0), (.n 1441, 2), (.n 1498, 13), (.n 2227, 0), (.n 2228, 37), (.n 2372, 0), (.n 2373, 19), (.n 2385, 0), (.n 2386, 12), (.n 2482, 0), (.n 2483, 9), (.n 2555, 0), (.n 2556, 7), (.n 2604, 0), (.n 2605, 6)] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨33960, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvxsplit_315_0.1 rfl kvxsplit_315_0.2.2,
      ← blockR_eq ((Data.core315.body.drop 0).take 1111), kvxsplit_315_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvxsplit_315_1111.1 rfl kvxsplit_315_1111.2.2,
      ← blockR_eq ((Data.core315.body.drop 1111).take 1111), kvxsplit_315_1111.2.1]
    rw [← blockR_eq (Data.core315.body.drop 2222), kvxsplit_315_2222]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_322 : kvxchkIdx 322 = true := by
  have hb : blockB (kvxlookJ 322) (kvxomLookJ 322) false [(.n 217, 0), (.n 218, 8), (.n 311, 28), (.n 498, 0), (.n 499, 5), (.n 575, 32), (.n 762, 0), (.n 763, 3), (.n 830, 23), (.n 1017, 0), (.n 1018, 3), (.n 1080, 18), (.n 1267, 0), (.n 1268, 2), (.n 1327, 15), (.n 1412, 0), (.n 1413, 2), (.n 1469, 12), (.n 2198, 0), (.n 2199, 28), (.n 2211, 0), (.n 2212, 16), (.n 2224, 0), (.n 2225, 11), (.n 2321, 0), (.n 2322, 9), (.n 2334, 0), (.n 2335, 7), (.n 2383, 0), (.n 2384, 6)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨28449, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvxsplit_322_0.1 rfl kvxsplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 1111), kvxsplit_322_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvxsplit_322_1111.1 rfl kvxsplit_322_1111.2.2,
      ← blockR_eq ((Data.core322.body.drop 1111).take 1111), kvxsplit_322_1111.2.1]
    rw [← blockR_eq (Data.core322.body.drop 2222), kvxsplit_322_2222]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvxchkIdx_all : ∀ j < 899, kvxchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 298
  · subst h1000; exact kvxchkIdx_298
  by_cases h1001 : j = 299
  · subst h1001; exact kvxchkIdx_299
  by_cases h1002 : j = 300
  · subst h1002; exact kvxchkIdx_300
  by_cases h1003 : j = 301
  · subst h1003; exact kvxchkIdx_301
  by_cases h1004 : j = 307
  · subst h1004; exact kvxchkIdx_307
  by_cases h1005 : j = 308
  · subst h1005; exact kvxchkIdx_308
  by_cases h1006 : j = 314
  · subst h1006; exact kvxchkIdx_314
  by_cases h1007 : j = 315
  · subst h1007; exact kvxchkIdx_315
  by_cases h1008 : j = 322
  · subst h1008; exact kvxchkIdx_322
  by_cases h0 : j < 10
  · exact kvxstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvxstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvxstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvxstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvxstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvxstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvxstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvxstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvxstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvxstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvxstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 296
  · exact kvxstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 297
  · exact kvxstaticRange_296.get (by omega) (by omega)
  by_cases h13 : j < 298
  · exact kvxstaticRange_297.get (by omega) (by omega)
  by_cases h14 : j < 304
  · exact kvxstaticRange_302.get (by omega) (by omega)
  by_cases h15 : j < 305
  · exact kvxstaticRange_304.get (by omega) (by omega)
  by_cases h16 : j < 306
  · exact kvxstaticRange_305.get (by omega) (by omega)
  by_cases h17 : j < 307
  · exact kvxstaticRange_306.get (by omega) (by omega)
  by_cases h18 : j < 311
  · exact kvxstaticRange_309.get (by omega) (by omega)
  by_cases h19 : j < 312
  · exact kvxstaticRange_311.get (by omega) (by omega)
  by_cases h20 : j < 313
  · exact kvxstaticRange_312.get (by omega) (by omega)
  by_cases h21 : j < 314
  · exact kvxstaticRange_313.get (by omega) (by omega)
  by_cases h22 : j < 318
  · exact kvxstaticRange_316.get (by omega) (by omega)
  by_cases h23 : j < 319
  · exact kvxstaticRange_318.get (by omega) (by omega)
  by_cases h24 : j < 320
  · exact kvxstaticRange_319.get (by omega) (by omega)
  by_cases h25 : j < 321
  · exact kvxstaticRange_320.get (by omega) (by omega)
  by_cases h26 : j < 322
  · exact kvxstaticRange_321.get (by omega) (by omega)
  by_cases h27 : j < 348
  · exact kvxstaticRange_323.get (by omega) (by omega)
  by_cases h28 : j < 371
  · exact kvxstaticRange_348.get (by omega) (by omega)
  by_cases h29 : j < 401
  · exact kvxstaticRange_371.get (by omega) (by omega)
  by_cases h30 : j < 425
  · exact kvxstaticRange_401.get (by omega) (by omega)
  by_cases h31 : j < 447
  · exact kvxstaticRange_425.get (by omega) (by omega)
  by_cases h32 : j < 470
  · exact kvxstaticRange_447.get (by omega) (by omega)
  by_cases h33 : j < 492
  · exact kvxstaticRange_470.get (by omega) (by omega)
  by_cases h34 : j < 513
  · exact kvxstaticRange_492.get (by omega) (by omega)
  by_cases h35 : j < 533
  · exact kvxstaticRange_513.get (by omega) (by omega)
  by_cases h36 : j < 554
  · exact kvxstaticRange_533.get (by omega) (by omega)
  by_cases h37 : j < 575
  · exact kvxstaticRange_554.get (by omega) (by omega)
  by_cases h38 : j < 596
  · exact kvxstaticRange_575.get (by omega) (by omega)
  by_cases h39 : j < 617
  · exact kvxstaticRange_596.get (by omega) (by omega)
  by_cases h40 : j < 637
  · exact kvxstaticRange_617.get (by omega) (by omega)
  by_cases h41 : j < 657
  · exact kvxstaticRange_637.get (by omega) (by omega)
  by_cases h42 : j < 677
  · exact kvxstaticRange_657.get (by omega) (by omega)
  by_cases h43 : j < 698
  · exact kvxstaticRange_677.get (by omega) (by omega)
  by_cases h44 : j < 719
  · exact kvxstaticRange_698.get (by omega) (by omega)
  by_cases h45 : j < 740
  · exact kvxstaticRange_719.get (by omega) (by omega)
  by_cases h46 : j < 761
  · exact kvxstaticRange_740.get (by omega) (by omega)
  by_cases h47 : j < 786
  · exact kvxstaticRange_761.get (by omega) (by omega)
  by_cases h48 : j < 810
  · exact kvxstaticRange_786.get (by omega) (by omega)
  by_cases h49 : j < 831
  · exact kvxstaticRange_810.get (by omega) (by omega)
  by_cases h50 : j < 844
  · exact kvxstaticRange_831.get (by omega) (by omega)
  by_cases h51 : j < 856
  · exact kvxstaticRange_844.get (by omega) (by omega)
  by_cases h52 : j < 865
  · exact kvxstaticRange_856.get (by omega) (by omega)
  by_cases h53 : j < 874
  · exact kvxstaticRange_865.get (by omega) (by omega)
  by_cases h54 : j < 880
  · exact kvxstaticRange_874.get (by omega) (by omega)
  by_cases h55 : j < 887
  · exact kvxstaticRange_880.get (by omega) (by omega)
  exact kvxstaticRange_887.get (by omega) (by omega)

end
end LeanVM.Guest
