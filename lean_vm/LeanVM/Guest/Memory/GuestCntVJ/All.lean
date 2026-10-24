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

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjchkIdx_298 : kvjchkIdx 298 = true := by
  have hb : blockB (kvjlookJ 298) (kvjomLookJ 298) false [(.n 217, 0), (.n 218, 25), (.n 479, 112), (.n 666, 0), (.n 667, 6), (.n 767, 56), (.n 954, 0), (.n 955, 4), (.n 1031, 32), (.n 1218, 0), (.n 1219, 3), (.n 1286, 23), (.n 1371, 0), (.n 1372, 2), (.n 1433, 17), (.n 2048, 0), (.n 2049, 112), (.n 2061, 0), (.n 2062, 28), (.n 2074, 0), (.n 2075, 16), (.n 2087, 0), (.n 2088, 11), (.n 2142, 0), (.n 2143, 8)] Data.core298.params Data.core298.name ([], []) Data.core298.body = some (⟨12341, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core298.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_298_0.1 rfl kvjsplit_298_0.2.2,
      ← blockR_eq ((Data.core298.body.drop 0).take 1320), kvjsplit_298_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_298_1320.1 rfl kvjsplit_298_1320.2.2,
      ← blockR_eq ((Data.core298.body.drop 1320).take 1320), kvjsplit_298_1320.2.1]
    rw [← blockR_eq (Data.core298.body.drop 2640), kvjsplit_298_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core298) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_299 : kvjchkIdx 299 = true := by
  have hb : blockB (kvjlookJ 299) (kvjomLookJ 299) false [(.n 217, 0), (.n 218, 25), (.n 479, 112), (.n 666, 0), (.n 667, 7), (.n 767, 56), (.n 954, 0), (.n 955, 4), (.n 1031, 32), (.n 1218, 0), (.n 1219, 3), (.n 1286, 23), (.n 1371, 0), (.n 1372, 2), (.n 1434, 18), (.n 2096, 0), (.n 2097, 112), (.n 2109, 0), (.n 2110, 28), (.n 2122, 0), (.n 2123, 16), (.n 2135, 0), (.n 2136, 11), (.n 2196, 0), (.n 2197, 9)] Data.core299.params Data.core299.name ([], []) Data.core299.body = some (⟨12392, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core299.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_299_0.1 rfl kvjsplit_299_0.2.2,
      ← blockR_eq ((Data.core299.body.drop 0).take 1320), kvjsplit_299_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_299_1320.1 rfl kvjsplit_299_1320.2.2,
      ← blockR_eq ((Data.core299.body.drop 1320).take 1320), kvjsplit_299_1320.2.1]
    rw [← blockR_eq (Data.core299.body.drop 2640), kvjsplit_299_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core299) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_300 : kvjchkIdx 300 = true := by
  have hb : blockB (kvjlookJ 300) (kvjomLookJ 300) false [(.n 217, 0), (.n 218, 29), (.n 480, 112), (.n 667, 0), (.n 668, 7), (.n 768, 56), (.n 955, 0), (.n 956, 4), (.n 1032, 32), (.n 1219, 0), (.n 1220, 3), (.n 1287, 23), (.n 1372, 0), (.n 1373, 2), (.n 1435, 18), (.n 2144, 0), (.n 2145, 112), (.n 2283, 0), (.n 2284, 28), (.n 2296, 0), (.n 2297, 16), (.n 2309, 0), (.n 2310, 11), (.n 2376, 0), (.n 2377, 9)] Data.core300.params Data.core300.name ([], []) Data.core300.body = some (⟨12470, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core300.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_300_0.1 rfl kvjsplit_300_0.2.2,
      ← blockR_eq ((Data.core300.body.drop 0).take 1320), kvjsplit_300_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_300_1320.1 rfl kvjsplit_300_1320.2.2,
      ← blockR_eq ((Data.core300.body.drop 1320).take 1320), kvjsplit_300_1320.2.1]
    rw [← blockR_eq (Data.core300.body.drop 2640), kvjsplit_300_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core300) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_301 : kvjchkIdx 301 = true := by
  have hb : blockB (kvjlookJ 301) (kvjomLookJ 301) false [(.n 217, 0), (.n 218, 29), (.n 480, 112), (.n 667, 0), (.n 668, 7), (.n 768, 56), (.n 955, 0), (.n 956, 4), (.n 1032, 32), (.n 1219, 0), (.n 1220, 3), (.n 1287, 23), (.n 1474, 0), (.n 1475, 2), (.n 1537, 18), (.n 1622, 0), (.n 1623, 2), (.n 1681, 14), (.n 2410, 0), (.n 2411, 112), (.n 2555, 0), (.n 2556, 28), (.n 2568, 0), (.n 2569, 16), (.n 2581, 0), (.n 2582, 11), (.n 2654, 0), (.n 2655, 9), (.n 2667, 0), (.n 2668, 7)] Data.core301.params Data.core301.name ([], []) Data.core301.body = some (⟨12885, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core301.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvjsplit_301_0.1 rfl kvjsplit_301_0.2.2,
      ← blockR_eq ((Data.core301.body.drop 0).take 1111), kvjsplit_301_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvjsplit_301_1111.1 rfl kvjsplit_301_1111.2.2,
      ← blockR_eq ((Data.core301.body.drop 1111).take 1111), kvjsplit_301_1111.2.1]
    rw [← blockR_eq (Data.core301.body.drop 2222), kvjsplit_301_2222]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core301) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_307 : kvjchkIdx 307 = true := by
  have hb : blockB (kvjlookJ 307) (kvjomLookJ 307) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1242, 0), (.n 1243, 2), (.n 1303, 16), (.n 2012, 0), (.n 2013, 56), (.n 2025, 0), (.n 2026, 22), (.n 2140, 0), (.n 2141, 14), (.n 2153, 0), (.n 2154, 10), (.n 2220, 0), (.n 2221, 8)] Data.core307.params Data.core307.name ([], []) Data.core307.body = some (⟨7748, []⟩, []) := by
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
  have hb : blockB (kvjlookJ 308) (kvjomLookJ 308) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1344, 0), (.n 1345, 2), (.n 1405, 16), (.n 1490, 0), (.n 1491, 2), (.n 1548, 13), (.n 2277, 0), (.n 2278, 56), (.n 2290, 0), (.n 2291, 22), (.n 2411, 0), (.n 2412, 14), (.n 2424, 0), (.n 2425, 10), (.n 2497, 0), (.n 2498, 8), (.n 2510, 0), (.n 2511, 6)] Data.core308.params Data.core308.name ([], []) Data.core308.body = some (⟨8135, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core308.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvjsplit_308_0.1 rfl kvjsplit_308_0.2.2,
      ← blockR_eq ((Data.core308.body.drop 0).take 1111), kvjsplit_308_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvjsplit_308_1111.1 rfl kvjsplit_308_1111.2.2,
      ← blockR_eq ((Data.core308.body.drop 1111).take 1111), kvjsplit_308_1111.2.1]
    rw [← blockR_eq (Data.core308.body.drop 2222), kvjsplit_308_2222]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core308) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_314 : kvjchkIdx 314 = true := by
  have hb : blockB (kvjlookJ 314) (kvjomLookJ 314) false [(.n 217, 0), (.n 218, 10), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1193, 0), (.n 1194, 2), (.n 1253, 15), (.n 1962, 0), (.n 1963, 37), (.n 2101, 0), (.n 2102, 19), (.n 2114, 0), (.n 2115, 12), (.n 2205, 0), (.n 2206, 9), (.n 2272, 0), (.n 2273, 7)] Data.core314.params Data.core314.name ([], []) Data.core314.body = some (⟨6111, []⟩, []) := by
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
  have hb : blockB (kvjlookJ 315) (kvjomLookJ 315) false [(.n 217, 0), (.n 218, 11), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1295, 0), (.n 1296, 2), (.n 1355, 15), (.n 1440, 0), (.n 1441, 2), (.n 1498, 13), (.n 2227, 0), (.n 2228, 37), (.n 2372, 0), (.n 2373, 19), (.n 2385, 0), (.n 2386, 12), (.n 2482, 0), (.n 2483, 9), (.n 2555, 0), (.n 2556, 7), (.n 2604, 0), (.n 2605, 6)] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨6503, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvjsplit_315_0.1 rfl kvjsplit_315_0.2.2,
      ← blockR_eq ((Data.core315.body.drop 0).take 1111), kvjsplit_315_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvjsplit_315_1111.1 rfl kvjsplit_315_1111.2.2,
      ← blockR_eq ((Data.core315.body.drop 1111).take 1111), kvjsplit_315_1111.2.1]
    rw [← blockR_eq (Data.core315.body.drop 2222), kvjsplit_315_2222]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_322 : kvjchkIdx 322 = true := by
  have hb : blockB (kvjlookJ 322) (kvjomLookJ 322) false [(.n 217, 0), (.n 218, 8), (.n 311, 28), (.n 498, 0), (.n 499, 5), (.n 575, 32), (.n 762, 0), (.n 763, 3), (.n 830, 23), (.n 1017, 0), (.n 1018, 3), (.n 1080, 18), (.n 1267, 0), (.n 1268, 2), (.n 1327, 15), (.n 1412, 0), (.n 1413, 2), (.n 1469, 12), (.n 2198, 0), (.n 2199, 28), (.n 2211, 0), (.n 2212, 16), (.n 2224, 0), (.n 2225, 11), (.n 2321, 0), (.n 2322, 9), (.n 2334, 0), (.n 2335, 7), (.n 2383, 0), (.n 2384, 6)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨5379, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvjsplit_322_0.1 rfl kvjsplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 1111), kvjsplit_322_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvjsplit_322_1111.1 rfl kvjsplit_322_1111.2.2,
      ← blockR_eq ((Data.core322.body.drop 1111).take 1111), kvjsplit_322_1111.2.1]
    rw [← blockR_eq (Data.core322.body.drop 2222), kvjsplit_322_2222]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvjchkIdx_all : ∀ j < 899, kvjchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 298
  · subst h1000; exact kvjchkIdx_298
  by_cases h1001 : j = 299
  · subst h1001; exact kvjchkIdx_299
  by_cases h1002 : j = 300
  · subst h1002; exact kvjchkIdx_300
  by_cases h1003 : j = 301
  · subst h1003; exact kvjchkIdx_301
  by_cases h1004 : j = 307
  · subst h1004; exact kvjchkIdx_307
  by_cases h1005 : j = 308
  · subst h1005; exact kvjchkIdx_308
  by_cases h1006 : j = 314
  · subst h1006; exact kvjchkIdx_314
  by_cases h1007 : j = 315
  · subst h1007; exact kvjchkIdx_315
  by_cases h1008 : j = 322
  · subst h1008; exact kvjchkIdx_322
  by_cases h0 : j < 10
  · exact kvjstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvjstaticRange_10.get (by omega) (by omega)
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
  by_cases h11 : j < 296
  · exact kvjstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 297
  · exact kvjstaticRange_296.get (by omega) (by omega)
  by_cases h13 : j < 298
  · exact kvjstaticRange_297.get (by omega) (by omega)
  by_cases h14 : j < 304
  · exact kvjstaticRange_302.get (by omega) (by omega)
  by_cases h15 : j < 305
  · exact kvjstaticRange_304.get (by omega) (by omega)
  by_cases h16 : j < 306
  · exact kvjstaticRange_305.get (by omega) (by omega)
  by_cases h17 : j < 307
  · exact kvjstaticRange_306.get (by omega) (by omega)
  by_cases h18 : j < 311
  · exact kvjstaticRange_309.get (by omega) (by omega)
  by_cases h19 : j < 312
  · exact kvjstaticRange_311.get (by omega) (by omega)
  by_cases h20 : j < 313
  · exact kvjstaticRange_312.get (by omega) (by omega)
  by_cases h21 : j < 314
  · exact kvjstaticRange_313.get (by omega) (by omega)
  by_cases h22 : j < 318
  · exact kvjstaticRange_316.get (by omega) (by omega)
  by_cases h23 : j < 319
  · exact kvjstaticRange_318.get (by omega) (by omega)
  by_cases h24 : j < 320
  · exact kvjstaticRange_319.get (by omega) (by omega)
  by_cases h25 : j < 321
  · exact kvjstaticRange_320.get (by omega) (by omega)
  by_cases h26 : j < 322
  · exact kvjstaticRange_321.get (by omega) (by omega)
  by_cases h27 : j < 353
  · exact kvjstaticRange_323.get (by omega) (by omega)
  by_cases h28 : j < 383
  · exact kvjstaticRange_353.get (by omega) (by omega)
  by_cases h29 : j < 413
  · exact kvjstaticRange_383.get (by omega) (by omega)
  by_cases h30 : j < 435
  · exact kvjstaticRange_413.get (by omega) (by omega)
  by_cases h31 : j < 457
  · exact kvjstaticRange_435.get (by omega) (by omega)
  by_cases h32 : j < 480
  · exact kvjstaticRange_457.get (by omega) (by omega)
  by_cases h33 : j < 501
  · exact kvjstaticRange_480.get (by omega) (by omega)
  by_cases h34 : j < 521
  · exact kvjstaticRange_501.get (by omega) (by omega)
  by_cases h35 : j < 541
  · exact kvjstaticRange_521.get (by omega) (by omega)
  by_cases h36 : j < 562
  · exact kvjstaticRange_541.get (by omega) (by omega)
  by_cases h37 : j < 583
  · exact kvjstaticRange_562.get (by omega) (by omega)
  by_cases h38 : j < 604
  · exact kvjstaticRange_583.get (by omega) (by omega)
  by_cases h39 : j < 624
  · exact kvjstaticRange_604.get (by omega) (by omega)
  by_cases h40 : j < 644
  · exact kvjstaticRange_624.get (by omega) (by omega)
  by_cases h41 : j < 664
  · exact kvjstaticRange_644.get (by omega) (by omega)
  by_cases h42 : j < 684
  · exact kvjstaticRange_664.get (by omega) (by omega)
  by_cases h43 : j < 705
  · exact kvjstaticRange_684.get (by omega) (by omega)
  by_cases h44 : j < 726
  · exact kvjstaticRange_705.get (by omega) (by omega)
  by_cases h45 : j < 747
  · exact kvjstaticRange_726.get (by omega) (by omega)
  by_cases h46 : j < 768
  · exact kvjstaticRange_747.get (by omega) (by omega)
  by_cases h47 : j < 798
  · exact kvjstaticRange_768.get (by omega) (by omega)
  by_cases h48 : j < 828
  · exact kvjstaticRange_798.get (by omega) (by omega)
  by_cases h49 : j < 843
  · exact kvjstaticRange_828.get (by omega) (by omega)
  by_cases h50 : j < 855
  · exact kvjstaticRange_843.get (by omega) (by omega)
  by_cases h51 : j < 863
  · exact kvjstaticRange_855.get (by omega) (by omega)
  by_cases h52 : j < 872
  · exact kvjstaticRange_863.get (by omega) (by omega)
  by_cases h53 : j < 878
  · exact kvjstaticRange_872.get (by omega) (by omega)
  by_cases h54 : j < 886
  · exact kvjstaticRange_878.get (by omega) (by omega)
  by_cases h55 : j < 893
  · exact kvjstaticRange_886.get (by omega) (by omega)
  exact kvjstaticRange_893.get (by omega) (by omega)

end
end LeanVM.Guest
