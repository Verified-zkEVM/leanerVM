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

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmchkIdx_295 : kvmchkIdx 295 = true := by
  have hb : blockB (kvmlookJ 295) (kvmomLookJ 295) false [(.n 217, 0), (.n 218, 25), (.n 479, 112), (.n 666, 0), (.n 667, 6), (.n 767, 56), (.n 954, 0), (.n 955, 4), (.n 1031, 32), (.n 1218, 0), (.n 1219, 3), (.n 1286, 23), (.n 1371, 0), (.n 1372, 2), (.n 1433, 17), (.n 2048, 0), (.n 2049, 112), (.n 2061, 0), (.n 2062, 28), (.n 2074, 0), (.n 2075, 16), (.n 2087, 0), (.n 2088, 11), (.n 2142, 0), (.n 2143, 8)] Data.core292.params Data.core292.name ([], []) Data.core292.body = some (⟨77461, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core292.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_295_0.1 rfl kvmsplit_295_0.2.2,
      ← blockR_eq ((Data.core292.body.drop 0).take 1320), kvmsplit_295_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_295_1320.1 rfl kvmsplit_295_1320.2.2,
      ← blockR_eq ((Data.core292.body.drop 1320).take 1320), kvmsplit_295_1320.2.1]
    rw [← blockR_eq (Data.core292.body.drop 2640), kvmsplit_295_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core292) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_296 : kvmchkIdx 296 = true := by
  have hb : blockB (kvmlookJ 296) (kvmomLookJ 296) false [(.n 217, 0), (.n 218, 25), (.n 479, 112), (.n 666, 0), (.n 667, 7), (.n 767, 56), (.n 954, 0), (.n 955, 4), (.n 1031, 32), (.n 1218, 0), (.n 1219, 3), (.n 1286, 23), (.n 1371, 0), (.n 1372, 2), (.n 1434, 18), (.n 2096, 0), (.n 2097, 112), (.n 2109, 0), (.n 2110, 28), (.n 2122, 0), (.n 2123, 16), (.n 2135, 0), (.n 2136, 11), (.n 2196, 0), (.n 2197, 9)] Data.core293.params Data.core293.name ([], []) Data.core293.body = some (⟨79111, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core293.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_296_0.1 rfl kvmsplit_296_0.2.2,
      ← blockR_eq ((Data.core293.body.drop 0).take 1320), kvmsplit_296_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_296_1320.1 rfl kvmsplit_296_1320.2.2,
      ← blockR_eq ((Data.core293.body.drop 1320).take 1320), kvmsplit_296_1320.2.1]
    rw [← blockR_eq (Data.core293.body.drop 2640), kvmsplit_296_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core293) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_297 : kvmchkIdx 297 = true := by
  have hb : blockB (kvmlookJ 297) (kvmomLookJ 297) false [(.n 217, 0), (.n 218, 29), (.n 480, 112), (.n 667, 0), (.n 668, 7), (.n 768, 56), (.n 955, 0), (.n 956, 4), (.n 1032, 32), (.n 1219, 0), (.n 1220, 3), (.n 1287, 23), (.n 1372, 0), (.n 1373, 2), (.n 1435, 18), (.n 2144, 0), (.n 2145, 112), (.n 2283, 0), (.n 2284, 28), (.n 2296, 0), (.n 2297, 16), (.n 2309, 0), (.n 2310, 11), (.n 2376, 0), (.n 2377, 9)] Data.core294.params Data.core294.name ([], []) Data.core294.body = some (⟨81982, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core294.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_297_0.1 rfl kvmsplit_297_0.2.2,
      ← blockR_eq ((Data.core294.body.drop 0).take 1320), kvmsplit_297_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_297_1320.1 rfl kvmsplit_297_1320.2.2,
      ← blockR_eq ((Data.core294.body.drop 1320).take 1320), kvmsplit_297_1320.2.1]
    rw [← blockR_eq (Data.core294.body.drop 2640), kvmsplit_297_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core294) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_298 : kvmchkIdx 298 = true := by
  have hb : blockB (kvmlookJ 298) (kvmomLookJ 298) false [(.n 217, 0), (.n 218, 29), (.n 480, 112), (.n 667, 0), (.n 668, 7), (.n 768, 56), (.n 955, 0), (.n 956, 4), (.n 1032, 32), (.n 1219, 0), (.n 1220, 3), (.n 1287, 23), (.n 1474, 0), (.n 1475, 2), (.n 1537, 18), (.n 1622, 0), (.n 1623, 2), (.n 1681, 14), (.n 2410, 0), (.n 2411, 112), (.n 2555, 0), (.n 2556, 28), (.n 2568, 0), (.n 2569, 16), (.n 2581, 0), (.n 2582, 11), (.n 2654, 0), (.n 2655, 9), (.n 2667, 0), (.n 2668, 7)] Data.core295.params Data.core295.name ([], []) Data.core295.body = some (⟨85518, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core295.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvmsplit_298_0.1 rfl kvmsplit_298_0.2.2,
      ← blockR_eq ((Data.core295.body.drop 0).take 1111), kvmsplit_298_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvmsplit_298_1111.1 rfl kvmsplit_298_1111.2.2,
      ← blockR_eq ((Data.core295.body.drop 1111).take 1111), kvmsplit_298_1111.2.1]
    rw [← blockR_eq (Data.core295.body.drop 2222), kvmsplit_298_2222]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core295) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_304 : kvmchkIdx 304 = true := by
  have hb : blockB (kvmlookJ 304) (kvmomLookJ 304) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1242, 0), (.n 1243, 2), (.n 1303, 16), (.n 2012, 0), (.n 2013, 56), (.n 2025, 0), (.n 2026, 22), (.n 2140, 0), (.n 2141, 14), (.n 2153, 0), (.n 2154, 10), (.n 2220, 0), (.n 2221, 8)] Data.core301.params Data.core301.name ([], []) Data.core301.body = some (⟨50610, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core301.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_304_0.1 rfl kvmsplit_304_0.2.2,
      ← blockR_eq ((Data.core301.body.drop 0).take 1320), kvmsplit_304_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_304_1320.1 rfl kvmsplit_304_1320.2.2,
      ← blockR_eq ((Data.core301.body.drop 1320).take 1320), kvmsplit_304_1320.2.1]
    rw [← blockR_eq (Data.core301.body.drop 2640), kvmsplit_304_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core301) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_305 : kvmchkIdx 305 = true := by
  have hb : blockB (kvmlookJ 305) (kvmomLookJ 305) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1344, 0), (.n 1345, 2), (.n 1405, 16), (.n 1490, 0), (.n 1491, 2), (.n 1548, 13), (.n 2277, 0), (.n 2278, 56), (.n 2290, 0), (.n 2291, 22), (.n 2411, 0), (.n 2412, 14), (.n 2424, 0), (.n 2425, 10), (.n 2497, 0), (.n 2498, 8), (.n 2510, 0), (.n 2511, 6)] Data.core302.params Data.core302.name ([], []) Data.core302.body = some (⟨53645, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core302.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvmsplit_305_0.1 rfl kvmsplit_305_0.2.2,
      ← blockR_eq ((Data.core302.body.drop 0).take 1111), kvmsplit_305_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvmsplit_305_1111.1 rfl kvmsplit_305_1111.2.2,
      ← blockR_eq ((Data.core302.body.drop 1111).take 1111), kvmsplit_305_1111.2.1]
    rw [← blockR_eq (Data.core302.body.drop 2222), kvmsplit_305_2222]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core302) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_311 : kvmchkIdx 311 = true := by
  have hb : blockB (kvmlookJ 311) (kvmomLookJ 311) false [(.n 217, 0), (.n 218, 10), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1193, 0), (.n 1194, 2), (.n 1253, 15), (.n 1962, 0), (.n 1963, 37), (.n 2101, 0), (.n 2102, 19), (.n 2114, 0), (.n 2115, 12), (.n 2205, 0), (.n 2206, 9), (.n 2272, 0), (.n 2273, 7)] Data.core308.params Data.core308.name ([], []) Data.core308.body = some (⟨39542, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core308.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvmsplit_311_0.1 rfl kvmsplit_311_0.2.2,
      ← blockR_eq ((Data.core308.body.drop 0).take 1320), kvmsplit_311_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvmsplit_311_1320.1 rfl kvmsplit_311_1320.2.2,
      ← blockR_eq ((Data.core308.body.drop 1320).take 1320), kvmsplit_311_1320.2.1]
    rw [← blockR_eq (Data.core308.body.drop 2640), kvmsplit_311_2640]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core308) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_312 : kvmchkIdx 312 = true := by
  have hb : blockB (kvmlookJ 312) (kvmomLookJ 312) false [(.n 217, 0), (.n 218, 11), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1295, 0), (.n 1296, 2), (.n 1355, 15), (.n 1440, 0), (.n 1441, 2), (.n 1498, 13), (.n 2227, 0), (.n 2228, 37), (.n 2372, 0), (.n 2373, 19), (.n 2385, 0), (.n 2386, 12), (.n 2482, 0), (.n 2483, 9), (.n 2555, 0), (.n 2556, 7), (.n 2604, 0), (.n 2605, 6)] Data.core309.params Data.core309.name ([], []) Data.core309.body = some (⟨42861, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core309.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvmsplit_312_0.1 rfl kvmsplit_312_0.2.2,
      ← blockR_eq ((Data.core309.body.drop 0).take 1111), kvmsplit_312_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvmsplit_312_1111.1 rfl kvmsplit_312_1111.2.2,
      ← blockR_eq ((Data.core309.body.drop 1111).take 1111), kvmsplit_312_1111.2.1]
    rw [← blockR_eq (Data.core309.body.drop 2222), kvmsplit_312_2222]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core309) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_319 : kvmchkIdx 319 = true := by
  have hb : blockB (kvmlookJ 319) (kvmomLookJ 319) false [(.n 217, 0), (.n 218, 8), (.n 311, 28), (.n 498, 0), (.n 499, 5), (.n 575, 32), (.n 762, 0), (.n 763, 3), (.n 830, 23), (.n 1017, 0), (.n 1018, 3), (.n 1080, 18), (.n 1267, 0), (.n 1268, 2), (.n 1327, 15), (.n 1412, 0), (.n 1413, 2), (.n 1469, 12), (.n 2198, 0), (.n 2199, 28), (.n 2211, 0), (.n 2212, 16), (.n 2224, 0), (.n 2225, 11), (.n 2321, 0), (.n 2322, 9), (.n 2334, 0), (.n 2335, 7), (.n 2383, 0), (.n 2384, 6)] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨36117, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvmsplit_319_0.1 rfl kvmsplit_319_0.2.2,
      ← blockR_eq ((Data.core316.body.drop 0).take 1111), kvmsplit_319_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvmsplit_319_1111.1 rfl kvmsplit_319_1111.2.2,
      ← blockR_eq ((Data.core316.body.drop 1111).take 1111), kvmsplit_319_1111.2.1]
    rw [← blockR_eq (Data.core316.body.drop 2222), kvmsplit_319_2222]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvmchkIdx_all : ∀ j < 878, kvmchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 295
  · subst h1000; exact kvmchkIdx_295
  by_cases h1001 : j = 296
  · subst h1001; exact kvmchkIdx_296
  by_cases h1002 : j = 297
  · subst h1002; exact kvmchkIdx_297
  by_cases h1003 : j = 298
  · subst h1003; exact kvmchkIdx_298
  by_cases h1004 : j = 304
  · subst h1004; exact kvmchkIdx_304
  by_cases h1005 : j = 305
  · subst h1005; exact kvmchkIdx_305
  by_cases h1006 : j = 311
  · subst h1006; exact kvmchkIdx_311
  by_cases h1007 : j = 312
  · subst h1007; exact kvmchkIdx_312
  by_cases h1008 : j = 319
  · subst h1008; exact kvmchkIdx_319
  by_cases h0 : j < 10
  · exact kvmstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvmstaticRange_10.get (by omega) (by omega)
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
  by_cases h11 : j < 293
  · exact kvmstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 294
  · exact kvmstaticRange_293.get (by omega) (by omega)
  by_cases h13 : j < 295
  · exact kvmstaticRange_294.get (by omega) (by omega)
  by_cases h14 : j < 301
  · exact kvmstaticRange_299.get (by omega) (by omega)
  by_cases h15 : j < 302
  · exact kvmstaticRange_301.get (by omega) (by omega)
  by_cases h16 : j < 303
  · exact kvmstaticRange_302.get (by omega) (by omega)
  by_cases h17 : j < 304
  · exact kvmstaticRange_303.get (by omega) (by omega)
  by_cases h18 : j < 308
  · exact kvmstaticRange_306.get (by omega) (by omega)
  by_cases h19 : j < 309
  · exact kvmstaticRange_308.get (by omega) (by omega)
  by_cases h20 : j < 310
  · exact kvmstaticRange_309.get (by omega) (by omega)
  by_cases h21 : j < 311
  · exact kvmstaticRange_310.get (by omega) (by omega)
  by_cases h22 : j < 315
  · exact kvmstaticRange_313.get (by omega) (by omega)
  by_cases h23 : j < 316
  · exact kvmstaticRange_315.get (by omega) (by omega)
  by_cases h24 : j < 317
  · exact kvmstaticRange_316.get (by omega) (by omega)
  by_cases h25 : j < 318
  · exact kvmstaticRange_317.get (by omega) (by omega)
  by_cases h26 : j < 319
  · exact kvmstaticRange_318.get (by omega) (by omega)
  by_cases h27 : j < 345
  · exact kvmstaticRange_320.get (by omega) (by omega)
  by_cases h28 : j < 368
  · exact kvmstaticRange_345.get (by omega) (by omega)
  by_cases h29 : j < 393
  · exact kvmstaticRange_368.get (by omega) (by omega)
  by_cases h30 : j < 415
  · exact kvmstaticRange_393.get (by omega) (by omega)
  by_cases h31 : j < 438
  · exact kvmstaticRange_415.get (by omega) (by omega)
  by_cases h32 : j < 460
  · exact kvmstaticRange_438.get (by omega) (by omega)
  by_cases h33 : j < 481
  · exact kvmstaticRange_460.get (by omega) (by omega)
  by_cases h34 : j < 502
  · exact kvmstaticRange_481.get (by omega) (by omega)
  by_cases h35 : j < 522
  · exact kvmstaticRange_502.get (by omega) (by omega)
  by_cases h36 : j < 543
  · exact kvmstaticRange_522.get (by omega) (by omega)
  by_cases h37 : j < 564
  · exact kvmstaticRange_543.get (by omega) (by omega)
  by_cases h38 : j < 585
  · exact kvmstaticRange_564.get (by omega) (by omega)
  by_cases h39 : j < 605
  · exact kvmstaticRange_585.get (by omega) (by omega)
  by_cases h40 : j < 625
  · exact kvmstaticRange_605.get (by omega) (by omega)
  by_cases h41 : j < 645
  · exact kvmstaticRange_625.get (by omega) (by omega)
  by_cases h42 : j < 665
  · exact kvmstaticRange_645.get (by omega) (by omega)
  by_cases h43 : j < 686
  · exact kvmstaticRange_665.get (by omega) (by omega)
  by_cases h44 : j < 707
  · exact kvmstaticRange_686.get (by omega) (by omega)
  by_cases h45 : j < 728
  · exact kvmstaticRange_707.get (by omega) (by omega)
  by_cases h46 : j < 751
  · exact kvmstaticRange_728.get (by omega) (by omega)
  by_cases h47 : j < 775
  · exact kvmstaticRange_751.get (by omega) (by omega)
  by_cases h48 : j < 799
  · exact kvmstaticRange_775.get (by omega) (by omega)
  by_cases h49 : j < 816
  · exact kvmstaticRange_799.get (by omega) (by omega)
  by_cases h50 : j < 828
  · exact kvmstaticRange_816.get (by omega) (by omega)
  by_cases h51 : j < 839
  · exact kvmstaticRange_828.get (by omega) (by omega)
  by_cases h52 : j < 846
  · exact kvmstaticRange_839.get (by omega) (by omega)
  by_cases h53 : j < 855
  · exact kvmstaticRange_846.get (by omega) (by omega)
  by_cases h54 : j < 863
  · exact kvmstaticRange_855.get (by omega) (by omega)
  by_cases h55 : j < 868
  · exact kvmstaticRange_863.get (by omega) (by omega)
  exact kvmstaticRange_868.get (by omega) (by omega)

end
end LeanVM.Guest
