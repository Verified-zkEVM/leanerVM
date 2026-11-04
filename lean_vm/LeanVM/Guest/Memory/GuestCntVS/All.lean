/-
  LeanVM.Guest.Memory.GuestCntVS.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVS.Part00
public import LeanVM.Guest.Memory.GuestCntVS.Part01
public import LeanVM.Guest.Memory.GuestCntVS.Part02
public import LeanVM.Guest.Memory.GuestCntVS.Part03
public import LeanVM.Guest.Memory.GuestCntVS.Part04
public import LeanVM.Guest.Memory.GuestCntVS.Part05
public import LeanVM.Guest.Memory.GuestCntVS.Part06
public import LeanVM.Guest.Memory.GuestCntVS.Part07
public import LeanVM.Guest.Memory.GuestCntVS.Part08
public import LeanVM.Guest.Memory.GuestCntVS.Part09
public import LeanVM.Guest.Memory.GuestCntVS.Part10
public import LeanVM.Guest.Memory.GuestCntVS.Part11
public import LeanVM.Guest.Memory.GuestCntVS.Part12
public import LeanVM.Guest.Memory.GuestCntVS.Part13
public import LeanVM.Guest.Memory.GuestCntVS.Part14
public import LeanVM.Guest.Memory.GuestCntVS.Part15
public import LeanVM.Guest.Memory.GuestCntVS.Part16
public import LeanVM.Guest.Memory.GuestCntVS.Part17
public import LeanVM.Guest.Memory.GuestCntVS.Part18
public import LeanVM.Guest.Memory.GuestCntVS.Part19
public import LeanVM.Guest.Memory.GuestCntVS.Part20
public import LeanVM.Guest.Memory.GuestCntVS.Part21

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvschkIdx_297 : kvschkIdx 297 = true := by
  have hb : blockB (kvslookJ 297) (kvsomLookJ 297) false [(.n 217, 0), (.n 218, 25), (.n 479, 112), (.n 666, 0), (.n 667, 6), (.n 767, 56), (.n 954, 0), (.n 955, 4), (.n 1031, 32), (.n 1218, 0), (.n 1219, 3), (.n 1286, 23), (.n 1371, 0), (.n 1372, 2), (.n 1433, 17), (.n 2048, 0), (.n 2049, 112), (.n 2061, 0), (.n 2062, 28), (.n 2074, 0), (.n 2075, 16), (.n 2087, 0), (.n 2088, 11), (.n 2142, 0), (.n 2143, 8)] Data.core297.params Data.core297.name ([], []) Data.core297.body = some (⟨11624, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core297.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvssplit_297_0.1 rfl kvssplit_297_0.2.2,
      ← blockR_eq ((Data.core297.body.drop 0).take 1320), kvssplit_297_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvssplit_297_1320.1 rfl kvssplit_297_1320.2.2,
      ← blockR_eq ((Data.core297.body.drop 1320).take 1320), kvssplit_297_1320.2.1]
    rw [← blockR_eq (Data.core297.body.drop 2640), kvssplit_297_2640]
    rfl
  exact kvschkIdx_of_split (fn := Data.core297) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_298 : kvschkIdx 298 = true := by
  have hb : blockB (kvslookJ 298) (kvsomLookJ 298) false [(.n 217, 0), (.n 218, 25), (.n 479, 112), (.n 666, 0), (.n 667, 7), (.n 767, 56), (.n 954, 0), (.n 955, 4), (.n 1031, 32), (.n 1218, 0), (.n 1219, 3), (.n 1286, 23), (.n 1371, 0), (.n 1372, 2), (.n 1434, 18), (.n 2096, 0), (.n 2097, 112), (.n 2109, 0), (.n 2110, 28), (.n 2122, 0), (.n 2123, 16), (.n 2135, 0), (.n 2136, 11), (.n 2196, 0), (.n 2197, 9)] Data.core298.params Data.core298.name ([], []) Data.core298.body = some (⟨11743, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core298.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvssplit_298_0.1 rfl kvssplit_298_0.2.2,
      ← blockR_eq ((Data.core298.body.drop 0).take 1320), kvssplit_298_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvssplit_298_1320.1 rfl kvssplit_298_1320.2.2,
      ← blockR_eq ((Data.core298.body.drop 1320).take 1320), kvssplit_298_1320.2.1]
    rw [← blockR_eq (Data.core298.body.drop 2640), kvssplit_298_2640]
    rfl
  exact kvschkIdx_of_split (fn := Data.core298) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_299 : kvschkIdx 299 = true := by
  have hb : blockB (kvslookJ 299) (kvsomLookJ 299) false [(.n 217, 0), (.n 218, 29), (.n 480, 112), (.n 667, 0), (.n 668, 7), (.n 768, 56), (.n 955, 0), (.n 956, 4), (.n 1032, 32), (.n 1219, 0), (.n 1220, 3), (.n 1287, 23), (.n 1372, 0), (.n 1373, 2), (.n 1435, 18), (.n 2144, 0), (.n 2145, 112), (.n 2283, 0), (.n 2284, 28), (.n 2296, 0), (.n 2297, 16), (.n 2309, 0), (.n 2310, 11), (.n 2376, 0), (.n 2377, 9)] Data.core299.params Data.core299.name ([], []) Data.core299.body = some (⟨12492, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core299.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvssplit_299_0.1 rfl kvssplit_299_0.2.2,
      ← blockR_eq ((Data.core299.body.drop 0).take 1320), kvssplit_299_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvssplit_299_1320.1 rfl kvssplit_299_1320.2.2,
      ← blockR_eq ((Data.core299.body.drop 1320).take 1320), kvssplit_299_1320.2.1]
    rw [← blockR_eq (Data.core299.body.drop 2640), kvssplit_299_2640]
    rfl
  exact kvschkIdx_of_split (fn := Data.core299) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_300 : kvschkIdx 300 = true := by
  have hb : blockB (kvslookJ 300) (kvsomLookJ 300) false [(.n 217, 0), (.n 218, 29), (.n 480, 112), (.n 667, 0), (.n 668, 7), (.n 768, 56), (.n 955, 0), (.n 956, 4), (.n 1032, 32), (.n 1219, 0), (.n 1220, 3), (.n 1287, 23), (.n 1474, 0), (.n 1475, 2), (.n 1537, 18), (.n 1622, 0), (.n 1623, 2), (.n 1681, 14), (.n 2410, 0), (.n 2411, 112), (.n 2555, 0), (.n 2556, 28), (.n 2568, 0), (.n 2569, 16), (.n 2581, 0), (.n 2582, 11), (.n 2654, 0), (.n 2655, 9), (.n 2667, 0), (.n 2668, 7)] Data.core300.params Data.core300.name ([], []) Data.core300.body = some (⟨13036, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core300.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvssplit_300_0.1 rfl kvssplit_300_0.2.2,
      ← blockR_eq ((Data.core300.body.drop 0).take 1111), kvssplit_300_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvssplit_300_1111.1 rfl kvssplit_300_1111.2.2,
      ← blockR_eq ((Data.core300.body.drop 1111).take 1111), kvssplit_300_1111.2.1]
    rw [← blockR_eq (Data.core300.body.drop 2222), kvssplit_300_2222]
    rfl
  exact kvschkIdx_of_split (fn := Data.core300) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_306 : kvschkIdx 306 = true := by
  have hb : blockB (kvslookJ 306) (kvsomLookJ 306) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1242, 0), (.n 1243, 2), (.n 1303, 16), (.n 2012, 0), (.n 2013, 56), (.n 2025, 0), (.n 2026, 22), (.n 2140, 0), (.n 2141, 14), (.n 2153, 0), (.n 2154, 10), (.n 2220, 0), (.n 2221, 8)] Data.core306.params Data.core306.name ([], []) Data.core306.body = some (⟨8059, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core306.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvssplit_306_0.1 rfl kvssplit_306_0.2.2,
      ← blockR_eq ((Data.core306.body.drop 0).take 1320), kvssplit_306_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvssplit_306_1320.1 rfl kvssplit_306_1320.2.2,
      ← blockR_eq ((Data.core306.body.drop 1320).take 1320), kvssplit_306_1320.2.1]
    rw [← blockR_eq (Data.core306.body.drop 2640), kvssplit_306_2640]
    rfl
  exact kvschkIdx_of_split (fn := Data.core306) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_307 : kvschkIdx 307 = true := by
  have hb : blockB (kvslookJ 307) (kvsomLookJ 307) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1344, 0), (.n 1345, 2), (.n 1405, 16), (.n 1490, 0), (.n 1491, 2), (.n 1548, 13), (.n 2277, 0), (.n 2278, 56), (.n 2290, 0), (.n 2291, 22), (.n 2411, 0), (.n 2412, 14), (.n 2424, 0), (.n 2425, 10), (.n 2497, 0), (.n 2498, 8), (.n 2510, 0), (.n 2511, 6)] Data.core307.params Data.core307.name ([], []) Data.core307.body = some (⟨8538, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core307.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvssplit_307_0.1 rfl kvssplit_307_0.2.2,
      ← blockR_eq ((Data.core307.body.drop 0).take 1111), kvssplit_307_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvssplit_307_1111.1 rfl kvssplit_307_1111.2.2,
      ← blockR_eq ((Data.core307.body.drop 1111).take 1111), kvssplit_307_1111.2.1]
    rw [← blockR_eq (Data.core307.body.drop 2222), kvssplit_307_2222]
    rfl
  exact kvschkIdx_of_split (fn := Data.core307) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_313 : kvschkIdx 313 = true := by
  have hb : blockB (kvslookJ 313) (kvsomLookJ 313) false [(.n 217, 0), (.n 218, 10), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1193, 0), (.n 1194, 2), (.n 1253, 15), (.n 1962, 0), (.n 1963, 37), (.n 2101, 0), (.n 2102, 19), (.n 2114, 0), (.n 2115, 12), (.n 2205, 0), (.n 2206, 9), (.n 2272, 0), (.n 2273, 7)] Data.core313.params Data.core313.name ([], []) Data.core313.body = some (⟨6581, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core313.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvssplit_313_0.1 rfl kvssplit_313_0.2.2,
      ← blockR_eq ((Data.core313.body.drop 0).take 1320), kvssplit_313_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvssplit_313_1320.1 rfl kvssplit_313_1320.2.2,
      ← blockR_eq ((Data.core313.body.drop 1320).take 1320), kvssplit_313_1320.2.1]
    rw [← blockR_eq (Data.core313.body.drop 2640), kvssplit_313_2640]
    rfl
  exact kvschkIdx_of_split (fn := Data.core313) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_314 : kvschkIdx 314 = true := by
  have hb : blockB (kvslookJ 314) (kvsomLookJ 314) false [(.n 217, 0), (.n 218, 11), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1295, 0), (.n 1296, 2), (.n 1355, 15), (.n 1440, 0), (.n 1441, 2), (.n 1498, 13), (.n 2227, 0), (.n 2228, 37), (.n 2372, 0), (.n 2373, 19), (.n 2385, 0), (.n 2386, 12), (.n 2482, 0), (.n 2483, 9), (.n 2555, 0), (.n 2556, 7), (.n 2604, 0), (.n 2605, 6)] Data.core314.params Data.core314.name ([], []) Data.core314.body = some (⟨7332, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core314.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvssplit_314_0.1 rfl kvssplit_314_0.2.2,
      ← blockR_eq ((Data.core314.body.drop 0).take 1111), kvssplit_314_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvssplit_314_1111.1 rfl kvssplit_314_1111.2.2,
      ← blockR_eq ((Data.core314.body.drop 1111).take 1111), kvssplit_314_1111.2.1]
    rw [← blockR_eq (Data.core314.body.drop 2222), kvssplit_314_2222]
    rfl
  exact kvschkIdx_of_split (fn := Data.core314) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_321 : kvschkIdx 321 = true := by
  have hb : blockB (kvslookJ 321) (kvsomLookJ 321) false [(.n 217, 0), (.n 218, 8), (.n 311, 28), (.n 498, 0), (.n 499, 5), (.n 575, 32), (.n 762, 0), (.n 763, 3), (.n 830, 23), (.n 1017, 0), (.n 1018, 3), (.n 1080, 18), (.n 1267, 0), (.n 1268, 2), (.n 1327, 15), (.n 1412, 0), (.n 1413, 2), (.n 1469, 12), (.n 2198, 0), (.n 2199, 28), (.n 2211, 0), (.n 2212, 16), (.n 2224, 0), (.n 2225, 11), (.n 2321, 0), (.n 2322, 9), (.n 2334, 0), (.n 2335, 7), (.n 2383, 0), (.n 2384, 6)] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨6138, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvssplit_321_0.1 rfl kvssplit_321_0.2.2,
      ← blockR_eq ((Data.core321.body.drop 0).take 1111), kvssplit_321_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvssplit_321_1111.1 rfl kvssplit_321_1111.2.2,
      ← blockR_eq ((Data.core321.body.drop 1111).take 1111), kvssplit_321_1111.2.1]
    rw [← blockR_eq (Data.core321.body.drop 2222), kvssplit_321_2222]
    rfl
  exact kvschkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvschkIdx_all : ∀ j < 883, kvschkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 297
  · subst h1000; exact kvschkIdx_297
  by_cases h1001 : j = 298
  · subst h1001; exact kvschkIdx_298
  by_cases h1002 : j = 299
  · subst h1002; exact kvschkIdx_299
  by_cases h1003 : j = 300
  · subst h1003; exact kvschkIdx_300
  by_cases h1004 : j = 306
  · subst h1004; exact kvschkIdx_306
  by_cases h1005 : j = 307
  · subst h1005; exact kvschkIdx_307
  by_cases h1006 : j = 313
  · subst h1006; exact kvschkIdx_313
  by_cases h1007 : j = 314
  · subst h1007; exact kvschkIdx_314
  by_cases h1008 : j = 321
  · subst h1008; exact kvschkIdx_321
  by_cases h0 : j < 10
  · exact kvsstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvsstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvsstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvsstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvsstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvsstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvsstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvsstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvsstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvsstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvsstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 295
  · exact kvsstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 296
  · exact kvsstaticRange_295.get (by omega) (by omega)
  by_cases h13 : j < 297
  · exact kvsstaticRange_296.get (by omega) (by omega)
  by_cases h14 : j < 303
  · exact kvsstaticRange_301.get (by omega) (by omega)
  by_cases h15 : j < 304
  · exact kvsstaticRange_303.get (by omega) (by omega)
  by_cases h16 : j < 305
  · exact kvsstaticRange_304.get (by omega) (by omega)
  by_cases h17 : j < 306
  · exact kvsstaticRange_305.get (by omega) (by omega)
  by_cases h18 : j < 310
  · exact kvsstaticRange_308.get (by omega) (by omega)
  by_cases h19 : j < 311
  · exact kvsstaticRange_310.get (by omega) (by omega)
  by_cases h20 : j < 312
  · exact kvsstaticRange_311.get (by omega) (by omega)
  by_cases h21 : j < 313
  · exact kvsstaticRange_312.get (by omega) (by omega)
  by_cases h22 : j < 317
  · exact kvsstaticRange_315.get (by omega) (by omega)
  by_cases h23 : j < 318
  · exact kvsstaticRange_317.get (by omega) (by omega)
  by_cases h24 : j < 319
  · exact kvsstaticRange_318.get (by omega) (by omega)
  by_cases h25 : j < 320
  · exact kvsstaticRange_319.get (by omega) (by omega)
  by_cases h26 : j < 321
  · exact kvsstaticRange_320.get (by omega) (by omega)
  by_cases h27 : j < 347
  · exact kvsstaticRange_322.get (by omega) (by omega)
  by_cases h28 : j < 369
  · exact kvsstaticRange_347.get (by omega) (by omega)
  by_cases h29 : j < 384
  · exact kvsstaticRange_369.get (by omega) (by omega)
  by_cases h30 : j < 414
  · exact kvsstaticRange_384.get (by omega) (by omega)
  by_cases h31 : j < 436
  · exact kvsstaticRange_414.get (by omega) (by omega)
  by_cases h32 : j < 459
  · exact kvsstaticRange_436.get (by omega) (by omega)
  by_cases h33 : j < 481
  · exact kvsstaticRange_459.get (by omega) (by omega)
  by_cases h34 : j < 502
  · exact kvsstaticRange_481.get (by omega) (by omega)
  by_cases h35 : j < 522
  · exact kvsstaticRange_502.get (by omega) (by omega)
  by_cases h36 : j < 542
  · exact kvsstaticRange_522.get (by omega) (by omega)
  by_cases h37 : j < 563
  · exact kvsstaticRange_542.get (by omega) (by omega)
  by_cases h38 : j < 584
  · exact kvsstaticRange_563.get (by omega) (by omega)
  by_cases h39 : j < 605
  · exact kvsstaticRange_584.get (by omega) (by omega)
  by_cases h40 : j < 625
  · exact kvsstaticRange_605.get (by omega) (by omega)
  by_cases h41 : j < 645
  · exact kvsstaticRange_625.get (by omega) (by omega)
  by_cases h42 : j < 665
  · exact kvsstaticRange_645.get (by omega) (by omega)
  by_cases h43 : j < 686
  · exact kvsstaticRange_665.get (by omega) (by omega)
  by_cases h44 : j < 707
  · exact kvsstaticRange_686.get (by omega) (by omega)
  by_cases h45 : j < 728
  · exact kvsstaticRange_707.get (by omega) (by omega)
  by_cases h46 : j < 749
  · exact kvsstaticRange_728.get (by omega) (by omega)
  by_cases h47 : j < 771
  · exact kvsstaticRange_749.get (by omega) (by omega)
  by_cases h48 : j < 795
  · exact kvsstaticRange_771.get (by omega) (by omega)
  by_cases h49 : j < 817
  · exact kvsstaticRange_795.get (by omega) (by omega)
  by_cases h50 : j < 831
  · exact kvsstaticRange_817.get (by omega) (by omega)
  by_cases h51 : j < 843
  · exact kvsstaticRange_831.get (by omega) (by omega)
  by_cases h52 : j < 851
  · exact kvsstaticRange_843.get (by omega) (by omega)
  by_cases h53 : j < 860
  · exact kvsstaticRange_851.get (by omega) (by omega)
  by_cases h54 : j < 866
  · exact kvsstaticRange_860.get (by omega) (by omega)
  by_cases h55 : j < 874
  · exact kvsstaticRange_866.get (by omega) (by omega)
  by_cases h56 : j < 881
  · exact kvsstaticRange_874.get (by omega) (by omega)
  exact kvsstaticRange_881.get (by omega) (by omega)

end
end LeanVM.Guest
