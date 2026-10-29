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

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdchkIdx_298 : kvdchkIdx 298 = true := by
  have hb : blockB (kvdlookJ 298) (kvdomLookJ 298) false [(.n 217, 0), (.n 218, 25), (.n 479, 112), (.n 666, 0), (.n 667, 6), (.n 767, 56), (.n 954, 0), (.n 955, 4), (.n 1031, 32), (.n 1218, 0), (.n 1219, 3), (.n 1286, 23), (.n 1371, 0), (.n 1372, 2), (.n 1433, 17), (.n 2048, 0), (.n 2049, 112), (.n 2061, 0), (.n 2062, 28), (.n 2074, 0), (.n 2075, 16), (.n 2087, 0), (.n 2088, 11), (.n 2142, 0), (.n 2143, 8)] Data.core298.params Data.core298.name ([], []) Data.core298.body = some (⟨28392, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core298.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_298_0.1 rfl kvdsplit_298_0.2.2,
      ← blockR_eq ((Data.core298.body.drop 0).take 1320), kvdsplit_298_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_298_1320.1 rfl kvdsplit_298_1320.2.2,
      ← blockR_eq ((Data.core298.body.drop 1320).take 1320), kvdsplit_298_1320.2.1]
    rw [← blockR_eq (Data.core298.body.drop 2640), kvdsplit_298_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core298) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_299 : kvdchkIdx 299 = true := by
  have hb : blockB (kvdlookJ 299) (kvdomLookJ 299) false [(.n 217, 0), (.n 218, 25), (.n 479, 112), (.n 666, 0), (.n 667, 7), (.n 767, 56), (.n 954, 0), (.n 955, 4), (.n 1031, 32), (.n 1218, 0), (.n 1219, 3), (.n 1286, 23), (.n 1371, 0), (.n 1372, 2), (.n 1434, 18), (.n 2096, 0), (.n 2097, 112), (.n 2109, 0), (.n 2110, 28), (.n 2122, 0), (.n 2123, 16), (.n 2135, 0), (.n 2136, 11), (.n 2196, 0), (.n 2197, 9)] Data.core299.params Data.core299.name ([], []) Data.core299.body = some (⟨29735, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core299.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_299_0.1 rfl kvdsplit_299_0.2.2,
      ← blockR_eq ((Data.core299.body.drop 0).take 1320), kvdsplit_299_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_299_1320.1 rfl kvdsplit_299_1320.2.2,
      ← blockR_eq ((Data.core299.body.drop 1320).take 1320), kvdsplit_299_1320.2.1]
    rw [← blockR_eq (Data.core299.body.drop 2640), kvdsplit_299_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core299) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_300 : kvdchkIdx 300 = true := by
  have hb : blockB (kvdlookJ 300) (kvdomLookJ 300) false [(.n 217, 0), (.n 218, 29), (.n 480, 112), (.n 667, 0), (.n 668, 7), (.n 768, 56), (.n 955, 0), (.n 956, 4), (.n 1032, 32), (.n 1219, 0), (.n 1220, 3), (.n 1287, 23), (.n 1372, 0), (.n 1373, 2), (.n 1435, 18), (.n 2144, 0), (.n 2145, 112), (.n 2283, 0), (.n 2284, 28), (.n 2296, 0), (.n 2297, 16), (.n 2309, 0), (.n 2310, 11), (.n 2376, 0), (.n 2377, 9)] Data.core300.params Data.core300.name ([], []) Data.core300.body = some (⟨31168, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core300.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvdsplit_300_0.1 rfl kvdsplit_300_0.2.2,
      ← blockR_eq ((Data.core300.body.drop 0).take 1320), kvdsplit_300_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvdsplit_300_1320.1 rfl kvdsplit_300_1320.2.2,
      ← blockR_eq ((Data.core300.body.drop 1320).take 1320), kvdsplit_300_1320.2.1]
    rw [← blockR_eq (Data.core300.body.drop 2640), kvdsplit_300_2640]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core300) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_301 : kvdchkIdx 301 = true := by
  have hb : blockB (kvdlookJ 301) (kvdomLookJ 301) false [(.n 217, 0), (.n 218, 29), (.n 480, 112), (.n 667, 0), (.n 668, 7), (.n 768, 56), (.n 955, 0), (.n 956, 4), (.n 1032, 32), (.n 1219, 0), (.n 1220, 3), (.n 1287, 23), (.n 1474, 0), (.n 1475, 2), (.n 1537, 18), (.n 1622, 0), (.n 1623, 2), (.n 1681, 14), (.n 2410, 0), (.n 2411, 112), (.n 2555, 0), (.n 2556, 28), (.n 2568, 0), (.n 2569, 16), (.n 2581, 0), (.n 2582, 11), (.n 2654, 0), (.n 2655, 9), (.n 2667, 0), (.n 2668, 7)] Data.core301.params Data.core301.name ([], []) Data.core301.body = some (⟨33423, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core301.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvdsplit_301_0.1 rfl kvdsplit_301_0.2.2,
      ← blockR_eq ((Data.core301.body.drop 0).take 1111), kvdsplit_301_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvdsplit_301_1111.1 rfl kvdsplit_301_1111.2.2,
      ← blockR_eq ((Data.core301.body.drop 1111).take 1111), kvdsplit_301_1111.2.1]
    rw [← blockR_eq (Data.core301.body.drop 2222), kvdsplit_301_2222]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core301) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_307 : kvdchkIdx 307 = true := by
  have hb : blockB (kvdlookJ 307) (kvdomLookJ 307) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1242, 0), (.n 1243, 2), (.n 1303, 16), (.n 2012, 0), (.n 2013, 56), (.n 2025, 0), (.n 2026, 22), (.n 2140, 0), (.n 2141, 14), (.n 2153, 0), (.n 2154, 10), (.n 2220, 0), (.n 2221, 8)] Data.core307.params Data.core307.name ([], []) Data.core307.body = some (⟨20589, []⟩, []) := by
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
  have hb : blockB (kvdlookJ 308) (kvdomLookJ 308) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1344, 0), (.n 1345, 2), (.n 1405, 16), (.n 1490, 0), (.n 1491, 2), (.n 1548, 13), (.n 2277, 0), (.n 2278, 56), (.n 2290, 0), (.n 2291, 22), (.n 2411, 0), (.n 2412, 14), (.n 2424, 0), (.n 2425, 10), (.n 2497, 0), (.n 2498, 8), (.n 2510, 0), (.n 2511, 6)] Data.core308.params Data.core308.name ([], []) Data.core308.body = some (⟨22359, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core308.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvdsplit_308_0.1 rfl kvdsplit_308_0.2.2,
      ← blockR_eq ((Data.core308.body.drop 0).take 1111), kvdsplit_308_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvdsplit_308_1111.1 rfl kvdsplit_308_1111.2.2,
      ← blockR_eq ((Data.core308.body.drop 1111).take 1111), kvdsplit_308_1111.2.1]
    rw [← blockR_eq (Data.core308.body.drop 2222), kvdsplit_308_2222]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core308) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_314 : kvdchkIdx 314 = true := by
  have hb : blockB (kvdlookJ 314) (kvdomLookJ 314) false [(.n 217, 0), (.n 218, 10), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1193, 0), (.n 1194, 2), (.n 1253, 15), (.n 1962, 0), (.n 1963, 37), (.n 2101, 0), (.n 2102, 19), (.n 2114, 0), (.n 2115, 12), (.n 2205, 0), (.n 2206, 9), (.n 2272, 0), (.n 2273, 7)] Data.core314.params Data.core314.name ([], []) Data.core314.body = some (⟨16881, []⟩, []) := by
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
  have hb : blockB (kvdlookJ 315) (kvdomLookJ 315) false [(.n 217, 0), (.n 218, 11), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1295, 0), (.n 1296, 2), (.n 1355, 15), (.n 1440, 0), (.n 1441, 2), (.n 1498, 13), (.n 2227, 0), (.n 2228, 37), (.n 2372, 0), (.n 2373, 19), (.n 2385, 0), (.n 2386, 12), (.n 2482, 0), (.n 2483, 9), (.n 2555, 0), (.n 2556, 7), (.n 2604, 0), (.n 2605, 6)] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨18527, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvdsplit_315_0.1 rfl kvdsplit_315_0.2.2,
      ← blockR_eq ((Data.core315.body.drop 0).take 1111), kvdsplit_315_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvdsplit_315_1111.1 rfl kvdsplit_315_1111.2.2,
      ← blockR_eq ((Data.core315.body.drop 1111).take 1111), kvdsplit_315_1111.2.1]
    rw [← blockR_eq (Data.core315.body.drop 2222), kvdsplit_315_2222]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_322 : kvdchkIdx 322 = true := by
  have hb : blockB (kvdlookJ 322) (kvdomLookJ 322) false [(.n 217, 0), (.n 218, 8), (.n 311, 28), (.n 498, 0), (.n 499, 5), (.n 575, 32), (.n 762, 0), (.n 763, 3), (.n 830, 23), (.n 1017, 0), (.n 1018, 3), (.n 1080, 18), (.n 1267, 0), (.n 1268, 2), (.n 1327, 15), (.n 1412, 0), (.n 1413, 2), (.n 1469, 12), (.n 2198, 0), (.n 2199, 28), (.n 2211, 0), (.n 2212, 16), (.n 2224, 0), (.n 2225, 11), (.n 2321, 0), (.n 2322, 9), (.n 2334, 0), (.n 2335, 7), (.n 2383, 0), (.n 2384, 6)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨15950, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvdsplit_322_0.1 rfl kvdsplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 1111), kvdsplit_322_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvdsplit_322_1111.1 rfl kvdsplit_322_1111.2.2,
      ← blockR_eq ((Data.core322.body.drop 1111).take 1111), kvdsplit_322_1111.2.1]
    rw [← blockR_eq (Data.core322.body.drop 2222), kvdsplit_322_2222]
    rfl
  exact kvdchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvdchkIdx_all : ∀ j < 899, kvdchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 298
  · subst h1000; exact kvdchkIdx_298
  by_cases h1001 : j = 299
  · subst h1001; exact kvdchkIdx_299
  by_cases h1002 : j = 300
  · subst h1002; exact kvdchkIdx_300
  by_cases h1003 : j = 301
  · subst h1003; exact kvdchkIdx_301
  by_cases h1004 : j = 307
  · subst h1004; exact kvdchkIdx_307
  by_cases h1005 : j = 308
  · subst h1005; exact kvdchkIdx_308
  by_cases h1006 : j = 314
  · subst h1006; exact kvdchkIdx_314
  by_cases h1007 : j = 315
  · subst h1007; exact kvdchkIdx_315
  by_cases h1008 : j = 322
  · subst h1008; exact kvdchkIdx_322
  by_cases h0 : j < 10
  · exact kvdstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvdstaticRange_10.get (by omega) (by omega)
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
  by_cases h11 : j < 296
  · exact kvdstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 297
  · exact kvdstaticRange_296.get (by omega) (by omega)
  by_cases h13 : j < 298
  · exact kvdstaticRange_297.get (by omega) (by omega)
  by_cases h14 : j < 304
  · exact kvdstaticRange_302.get (by omega) (by omega)
  by_cases h15 : j < 305
  · exact kvdstaticRange_304.get (by omega) (by omega)
  by_cases h16 : j < 306
  · exact kvdstaticRange_305.get (by omega) (by omega)
  by_cases h17 : j < 307
  · exact kvdstaticRange_306.get (by omega) (by omega)
  by_cases h18 : j < 311
  · exact kvdstaticRange_309.get (by omega) (by omega)
  by_cases h19 : j < 312
  · exact kvdstaticRange_311.get (by omega) (by omega)
  by_cases h20 : j < 313
  · exact kvdstaticRange_312.get (by omega) (by omega)
  by_cases h21 : j < 314
  · exact kvdstaticRange_313.get (by omega) (by omega)
  by_cases h22 : j < 318
  · exact kvdstaticRange_316.get (by omega) (by omega)
  by_cases h23 : j < 319
  · exact kvdstaticRange_318.get (by omega) (by omega)
  by_cases h24 : j < 320
  · exact kvdstaticRange_319.get (by omega) (by omega)
  by_cases h25 : j < 321
  · exact kvdstaticRange_320.get (by omega) (by omega)
  by_cases h26 : j < 322
  · exact kvdstaticRange_321.get (by omega) (by omega)
  by_cases h27 : j < 348
  · exact kvdstaticRange_323.get (by omega) (by omega)
  by_cases h28 : j < 371
  · exact kvdstaticRange_348.get (by omega) (by omega)
  by_cases h29 : j < 401
  · exact kvdstaticRange_371.get (by omega) (by omega)
  by_cases h30 : j < 425
  · exact kvdstaticRange_401.get (by omega) (by omega)
  by_cases h31 : j < 447
  · exact kvdstaticRange_425.get (by omega) (by omega)
  by_cases h32 : j < 470
  · exact kvdstaticRange_447.get (by omega) (by omega)
  by_cases h33 : j < 492
  · exact kvdstaticRange_470.get (by omega) (by omega)
  by_cases h34 : j < 513
  · exact kvdstaticRange_492.get (by omega) (by omega)
  by_cases h35 : j < 533
  · exact kvdstaticRange_513.get (by omega) (by omega)
  by_cases h36 : j < 554
  · exact kvdstaticRange_533.get (by omega) (by omega)
  by_cases h37 : j < 575
  · exact kvdstaticRange_554.get (by omega) (by omega)
  by_cases h38 : j < 596
  · exact kvdstaticRange_575.get (by omega) (by omega)
  by_cases h39 : j < 617
  · exact kvdstaticRange_596.get (by omega) (by omega)
  by_cases h40 : j < 637
  · exact kvdstaticRange_617.get (by omega) (by omega)
  by_cases h41 : j < 657
  · exact kvdstaticRange_637.get (by omega) (by omega)
  by_cases h42 : j < 677
  · exact kvdstaticRange_657.get (by omega) (by omega)
  by_cases h43 : j < 698
  · exact kvdstaticRange_677.get (by omega) (by omega)
  by_cases h44 : j < 719
  · exact kvdstaticRange_698.get (by omega) (by omega)
  by_cases h45 : j < 740
  · exact kvdstaticRange_719.get (by omega) (by omega)
  by_cases h46 : j < 761
  · exact kvdstaticRange_740.get (by omega) (by omega)
  by_cases h47 : j < 786
  · exact kvdstaticRange_761.get (by omega) (by omega)
  by_cases h48 : j < 810
  · exact kvdstaticRange_786.get (by omega) (by omega)
  by_cases h49 : j < 831
  · exact kvdstaticRange_810.get (by omega) (by omega)
  by_cases h50 : j < 844
  · exact kvdstaticRange_831.get (by omega) (by omega)
  by_cases h51 : j < 856
  · exact kvdstaticRange_844.get (by omega) (by omega)
  by_cases h52 : j < 865
  · exact kvdstaticRange_856.get (by omega) (by omega)
  by_cases h53 : j < 874
  · exact kvdstaticRange_865.get (by omega) (by omega)
  by_cases h54 : j < 880
  · exact kvdstaticRange_874.get (by omega) (by omega)
  by_cases h55 : j < 887
  · exact kvdstaticRange_880.get (by omega) (by omega)
  exact kvdstaticRange_887.get (by omega) (by omega)

end
end LeanVM.Guest
