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
theorem kvschkIdx_298 : kvschkIdx 298 = true := by
  have hb : blockB (kvslookJ 298) (kvsomLookJ 298) false [(.n 217, 0), (.n 218, 25), (.n 479, 112), (.n 666, 0), (.n 667, 6), (.n 767, 56), (.n 954, 0), (.n 955, 4), (.n 1031, 32), (.n 1218, 0), (.n 1219, 3), (.n 1286, 23), (.n 1371, 0), (.n 1372, 2), (.n 1433, 17), (.n 2048, 0), (.n 2049, 112), (.n 2061, 0), (.n 2062, 28), (.n 2074, 0), (.n 2075, 16), (.n 2087, 0), (.n 2088, 11), (.n 2142, 0), (.n 2143, 8)] Data.core298.params Data.core298.name ([], []) Data.core298.body = some (⟨11624, []⟩, []) := by
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
  have hb : blockB (kvslookJ 299) (kvsomLookJ 299) false [(.n 217, 0), (.n 218, 25), (.n 479, 112), (.n 666, 0), (.n 667, 7), (.n 767, 56), (.n 954, 0), (.n 955, 4), (.n 1031, 32), (.n 1218, 0), (.n 1219, 3), (.n 1286, 23), (.n 1371, 0), (.n 1372, 2), (.n 1434, 18), (.n 2096, 0), (.n 2097, 112), (.n 2109, 0), (.n 2110, 28), (.n 2122, 0), (.n 2123, 16), (.n 2135, 0), (.n 2136, 11), (.n 2196, 0), (.n 2197, 9)] Data.core299.params Data.core299.name ([], []) Data.core299.body = some (⟨11743, []⟩, []) := by
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
  have hb : blockB (kvslookJ 300) (kvsomLookJ 300) false [(.n 217, 0), (.n 218, 29), (.n 480, 112), (.n 667, 0), (.n 668, 7), (.n 768, 56), (.n 955, 0), (.n 956, 4), (.n 1032, 32), (.n 1219, 0), (.n 1220, 3), (.n 1287, 23), (.n 1372, 0), (.n 1373, 2), (.n 1435, 18), (.n 2144, 0), (.n 2145, 112), (.n 2283, 0), (.n 2284, 28), (.n 2296, 0), (.n 2297, 16), (.n 2309, 0), (.n 2310, 11), (.n 2376, 0), (.n 2377, 9)] Data.core300.params Data.core300.name ([], []) Data.core300.body = some (⟨12492, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core300.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvssplit_300_0.1 rfl kvssplit_300_0.2.2,
      ← blockR_eq ((Data.core300.body.drop 0).take 1320), kvssplit_300_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvssplit_300_1320.1 rfl kvssplit_300_1320.2.2,
      ← blockR_eq ((Data.core300.body.drop 1320).take 1320), kvssplit_300_1320.2.1]
    rw [← blockR_eq (Data.core300.body.drop 2640), kvssplit_300_2640]
    rfl
  exact kvschkIdx_of_split (fn := Data.core300) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_301 : kvschkIdx 301 = true := by
  have hb : blockB (kvslookJ 301) (kvsomLookJ 301) false [(.n 217, 0), (.n 218, 29), (.n 480, 112), (.n 667, 0), (.n 668, 7), (.n 768, 56), (.n 955, 0), (.n 956, 4), (.n 1032, 32), (.n 1219, 0), (.n 1220, 3), (.n 1287, 23), (.n 1474, 0), (.n 1475, 2), (.n 1537, 18), (.n 1622, 0), (.n 1623, 2), (.n 1681, 14), (.n 2410, 0), (.n 2411, 112), (.n 2555, 0), (.n 2556, 28), (.n 2568, 0), (.n 2569, 16), (.n 2581, 0), (.n 2582, 11), (.n 2654, 0), (.n 2655, 9), (.n 2667, 0), (.n 2668, 7)] Data.core301.params Data.core301.name ([], []) Data.core301.body = some (⟨13036, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core301.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvssplit_301_0.1 rfl kvssplit_301_0.2.2,
      ← blockR_eq ((Data.core301.body.drop 0).take 1111), kvssplit_301_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvssplit_301_1111.1 rfl kvssplit_301_1111.2.2,
      ← blockR_eq ((Data.core301.body.drop 1111).take 1111), kvssplit_301_1111.2.1]
    rw [← blockR_eq (Data.core301.body.drop 2222), kvssplit_301_2222]
    rfl
  exact kvschkIdx_of_split (fn := Data.core301) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_307 : kvschkIdx 307 = true := by
  have hb : blockB (kvslookJ 307) (kvsomLookJ 307) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1242, 0), (.n 1243, 2), (.n 1303, 16), (.n 2012, 0), (.n 2013, 56), (.n 2025, 0), (.n 2026, 22), (.n 2140, 0), (.n 2141, 14), (.n 2153, 0), (.n 2154, 10), (.n 2220, 0), (.n 2221, 8)] Data.core307.params Data.core307.name ([], []) Data.core307.body = some (⟨8059, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core307.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvssplit_307_0.1 rfl kvssplit_307_0.2.2,
      ← blockR_eq ((Data.core307.body.drop 0).take 1320), kvssplit_307_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvssplit_307_1320.1 rfl kvssplit_307_1320.2.2,
      ← blockR_eq ((Data.core307.body.drop 1320).take 1320), kvssplit_307_1320.2.1]
    rw [← blockR_eq (Data.core307.body.drop 2640), kvssplit_307_2640]
    rfl
  exact kvschkIdx_of_split (fn := Data.core307) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_308 : kvschkIdx 308 = true := by
  have hb : blockB (kvslookJ 308) (kvsomLookJ 308) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1344, 0), (.n 1345, 2), (.n 1405, 16), (.n 1490, 0), (.n 1491, 2), (.n 1548, 13), (.n 2277, 0), (.n 2278, 56), (.n 2290, 0), (.n 2291, 22), (.n 2411, 0), (.n 2412, 14), (.n 2424, 0), (.n 2425, 10), (.n 2497, 0), (.n 2498, 8), (.n 2510, 0), (.n 2511, 6)] Data.core308.params Data.core308.name ([], []) Data.core308.body = some (⟨8538, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core308.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvssplit_308_0.1 rfl kvssplit_308_0.2.2,
      ← blockR_eq ((Data.core308.body.drop 0).take 1111), kvssplit_308_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvssplit_308_1111.1 rfl kvssplit_308_1111.2.2,
      ← blockR_eq ((Data.core308.body.drop 1111).take 1111), kvssplit_308_1111.2.1]
    rw [← blockR_eq (Data.core308.body.drop 2222), kvssplit_308_2222]
    rfl
  exact kvschkIdx_of_split (fn := Data.core308) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_314 : kvschkIdx 314 = true := by
  have hb : blockB (kvslookJ 314) (kvsomLookJ 314) false [(.n 217, 0), (.n 218, 10), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1193, 0), (.n 1194, 2), (.n 1253, 15), (.n 1962, 0), (.n 1963, 37), (.n 2101, 0), (.n 2102, 19), (.n 2114, 0), (.n 2115, 12), (.n 2205, 0), (.n 2206, 9), (.n 2272, 0), (.n 2273, 7)] Data.core314.params Data.core314.name ([], []) Data.core314.body = some (⟨6581, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core314.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvssplit_314_0.1 rfl kvssplit_314_0.2.2,
      ← blockR_eq ((Data.core314.body.drop 0).take 1320), kvssplit_314_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvssplit_314_1320.1 rfl kvssplit_314_1320.2.2,
      ← blockR_eq ((Data.core314.body.drop 1320).take 1320), kvssplit_314_1320.2.1]
    rw [← blockR_eq (Data.core314.body.drop 2640), kvssplit_314_2640]
    rfl
  exact kvschkIdx_of_split (fn := Data.core314) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_315 : kvschkIdx 315 = true := by
  have hb : blockB (kvslookJ 315) (kvsomLookJ 315) false [(.n 217, 0), (.n 218, 11), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1295, 0), (.n 1296, 2), (.n 1355, 15), (.n 1440, 0), (.n 1441, 2), (.n 1498, 13), (.n 2227, 0), (.n 2228, 37), (.n 2372, 0), (.n 2373, 19), (.n 2385, 0), (.n 2386, 12), (.n 2482, 0), (.n 2483, 9), (.n 2555, 0), (.n 2556, 7), (.n 2604, 0), (.n 2605, 6)] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨7332, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvssplit_315_0.1 rfl kvssplit_315_0.2.2,
      ← blockR_eq ((Data.core315.body.drop 0).take 1111), kvssplit_315_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvssplit_315_1111.1 rfl kvssplit_315_1111.2.2,
      ← blockR_eq ((Data.core315.body.drop 1111).take 1111), kvssplit_315_1111.2.1]
    rw [← blockR_eq (Data.core315.body.drop 2222), kvssplit_315_2222]
    rfl
  exact kvschkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_322 : kvschkIdx 322 = true := by
  have hb : blockB (kvslookJ 322) (kvsomLookJ 322) false [(.n 217, 0), (.n 218, 8), (.n 311, 28), (.n 498, 0), (.n 499, 5), (.n 575, 32), (.n 762, 0), (.n 763, 3), (.n 830, 23), (.n 1017, 0), (.n 1018, 3), (.n 1080, 18), (.n 1267, 0), (.n 1268, 2), (.n 1327, 15), (.n 1412, 0), (.n 1413, 2), (.n 1469, 12), (.n 2198, 0), (.n 2199, 28), (.n 2211, 0), (.n 2212, 16), (.n 2224, 0), (.n 2225, 11), (.n 2321, 0), (.n 2322, 9), (.n 2334, 0), (.n 2335, 7), (.n 2383, 0), (.n 2384, 6)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨6138, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvssplit_322_0.1 rfl kvssplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 1111), kvssplit_322_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvssplit_322_1111.1 rfl kvssplit_322_1111.2.2,
      ← blockR_eq ((Data.core322.body.drop 1111).take 1111), kvssplit_322_1111.2.1]
    rw [← blockR_eq (Data.core322.body.drop 2222), kvssplit_322_2222]
    rfl
  exact kvschkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvschkIdx_all : ∀ j < 899, kvschkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 298
  · subst h1000; exact kvschkIdx_298
  by_cases h1001 : j = 299
  · subst h1001; exact kvschkIdx_299
  by_cases h1002 : j = 300
  · subst h1002; exact kvschkIdx_300
  by_cases h1003 : j = 301
  · subst h1003; exact kvschkIdx_301
  by_cases h1004 : j = 307
  · subst h1004; exact kvschkIdx_307
  by_cases h1005 : j = 308
  · subst h1005; exact kvschkIdx_308
  by_cases h1006 : j = 314
  · subst h1006; exact kvschkIdx_314
  by_cases h1007 : j = 315
  · subst h1007; exact kvschkIdx_315
  by_cases h1008 : j = 322
  · subst h1008; exact kvschkIdx_322
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
  by_cases h11 : j < 296
  · exact kvsstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 297
  · exact kvsstaticRange_296.get (by omega) (by omega)
  by_cases h13 : j < 298
  · exact kvsstaticRange_297.get (by omega) (by omega)
  by_cases h14 : j < 304
  · exact kvsstaticRange_302.get (by omega) (by omega)
  by_cases h15 : j < 305
  · exact kvsstaticRange_304.get (by omega) (by omega)
  by_cases h16 : j < 306
  · exact kvsstaticRange_305.get (by omega) (by omega)
  by_cases h17 : j < 307
  · exact kvsstaticRange_306.get (by omega) (by omega)
  by_cases h18 : j < 311
  · exact kvsstaticRange_309.get (by omega) (by omega)
  by_cases h19 : j < 312
  · exact kvsstaticRange_311.get (by omega) (by omega)
  by_cases h20 : j < 313
  · exact kvsstaticRange_312.get (by omega) (by omega)
  by_cases h21 : j < 314
  · exact kvsstaticRange_313.get (by omega) (by omega)
  by_cases h22 : j < 318
  · exact kvsstaticRange_316.get (by omega) (by omega)
  by_cases h23 : j < 319
  · exact kvsstaticRange_318.get (by omega) (by omega)
  by_cases h24 : j < 320
  · exact kvsstaticRange_319.get (by omega) (by omega)
  by_cases h25 : j < 321
  · exact kvsstaticRange_320.get (by omega) (by omega)
  by_cases h26 : j < 322
  · exact kvsstaticRange_321.get (by omega) (by omega)
  by_cases h27 : j < 348
  · exact kvsstaticRange_323.get (by omega) (by omega)
  by_cases h28 : j < 371
  · exact kvsstaticRange_348.get (by omega) (by omega)
  by_cases h29 : j < 401
  · exact kvsstaticRange_371.get (by omega) (by omega)
  by_cases h30 : j < 425
  · exact kvsstaticRange_401.get (by omega) (by omega)
  by_cases h31 : j < 447
  · exact kvsstaticRange_425.get (by omega) (by omega)
  by_cases h32 : j < 470
  · exact kvsstaticRange_447.get (by omega) (by omega)
  by_cases h33 : j < 492
  · exact kvsstaticRange_470.get (by omega) (by omega)
  by_cases h34 : j < 513
  · exact kvsstaticRange_492.get (by omega) (by omega)
  by_cases h35 : j < 533
  · exact kvsstaticRange_513.get (by omega) (by omega)
  by_cases h36 : j < 554
  · exact kvsstaticRange_533.get (by omega) (by omega)
  by_cases h37 : j < 575
  · exact kvsstaticRange_554.get (by omega) (by omega)
  by_cases h38 : j < 596
  · exact kvsstaticRange_575.get (by omega) (by omega)
  by_cases h39 : j < 617
  · exact kvsstaticRange_596.get (by omega) (by omega)
  by_cases h40 : j < 637
  · exact kvsstaticRange_617.get (by omega) (by omega)
  by_cases h41 : j < 657
  · exact kvsstaticRange_637.get (by omega) (by omega)
  by_cases h42 : j < 677
  · exact kvsstaticRange_657.get (by omega) (by omega)
  by_cases h43 : j < 698
  · exact kvsstaticRange_677.get (by omega) (by omega)
  by_cases h44 : j < 719
  · exact kvsstaticRange_698.get (by omega) (by omega)
  by_cases h45 : j < 740
  · exact kvsstaticRange_719.get (by omega) (by omega)
  by_cases h46 : j < 761
  · exact kvsstaticRange_740.get (by omega) (by omega)
  by_cases h47 : j < 786
  · exact kvsstaticRange_761.get (by omega) (by omega)
  by_cases h48 : j < 810
  · exact kvsstaticRange_786.get (by omega) (by omega)
  by_cases h49 : j < 831
  · exact kvsstaticRange_810.get (by omega) (by omega)
  by_cases h50 : j < 844
  · exact kvsstaticRange_831.get (by omega) (by omega)
  by_cases h51 : j < 856
  · exact kvsstaticRange_844.get (by omega) (by omega)
  by_cases h52 : j < 865
  · exact kvsstaticRange_856.get (by omega) (by omega)
  by_cases h53 : j < 874
  · exact kvsstaticRange_865.get (by omega) (by omega)
  by_cases h54 : j < 880
  · exact kvsstaticRange_874.get (by omega) (by omega)
  by_cases h55 : j < 887
  · exact kvsstaticRange_880.get (by omega) (by omega)
  exact kvsstaticRange_887.get (by omega) (by omega)

end
end LeanVM.Guest
