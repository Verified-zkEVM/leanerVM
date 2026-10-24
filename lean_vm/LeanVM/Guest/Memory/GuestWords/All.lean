/-
  LeanVM.Guest.Memory.GuestWords.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestWords.Part00
public import LeanVM.Guest.Memory.GuestWords.Part01
public import LeanVM.Guest.Memory.GuestWords.Part02
public import LeanVM.Guest.Memory.GuestWords.Part03
public import LeanVM.Guest.Memory.GuestWords.Part04
public import LeanVM.Guest.Memory.GuestWords.Part05
public import LeanVM.Guest.Memory.GuestWords.Part06
public import LeanVM.Guest.Memory.GuestWords.Part07
public import LeanVM.Guest.Memory.GuestWords.Part08
public import LeanVM.Guest.Memory.GuestWords.Part09
public import LeanVM.Guest.Memory.GuestWords.Part10
public import LeanVM.Guest.Memory.GuestWords.Part11
public import LeanVM.Guest.Memory.GuestWords.Part12
public import LeanVM.Guest.Memory.GuestWords.Part13
public import LeanVM.Guest.Memory.GuestWords.Part14
public import LeanVM.Guest.Memory.GuestWords.Part15
public import LeanVM.Guest.Memory.GuestWords.Part16
public import LeanVM.Guest.Memory.GuestWords.Part17
public import LeanVM.Guest.Memory.GuestWords.Part18
public import LeanVM.Guest.Memory.GuestWords.Part19
public import LeanVM.Guest.Memory.GuestWords.Part20
public import LeanVM.Guest.Memory.GuestWords.Part21
public import LeanVM.Guest.Memory.GuestWords.Part22
public import LeanVM.Guest.Memory.GuestWords.Part23
public import LeanVM.Guest.Memory.GuestWords.Part24
public import LeanVM.Guest.Memory.GuestWords.Part25
public import LeanVM.Guest.Memory.GuestWords.Part26
public import LeanVM.Guest.Memory.GuestWords.Part27
public import LeanVM.Guest.Memory.GuestWords.Part28
public import LeanVM.Guest.Memory.GuestWords.Part29
public import LeanVM.Guest.Memory.GuestWords.Part30
public import LeanVM.Guest.Memory.GuestWords.Part31
public import LeanVM.Guest.Memory.GuestWords.Part32
public import LeanVM.Guest.Memory.GuestWords.Part33
public import LeanVM.Guest.Memory.GuestWords.Part34
public import LeanVM.Guest.Memory.GuestWords.Part35
public import LeanVM.Guest.Memory.GuestWords.Part36
public import LeanVM.Guest.Memory.GuestWords.Part37
public import LeanVM.Guest.Memory.GuestWords.Part38
public import LeanVM.Guest.Memory.GuestWords.Part39
public import LeanVM.Guest.Memory.GuestWords.Part40
public import LeanVM.Guest.Memory.GuestWords.Part41

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wchkIdx_19 : wchkIdx 19 = true := by
  have hb : blockB (wlookJ 19) (womLookJ 19) true [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 533 533 wsplit_19_0.1 rfl wsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 533), wsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 533), wsplit_19_533]
    rfl
  exact wchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_20 : wchkIdx 20 = true := by
  have hb : blockB (wlookJ 20) (womLookJ 20) true [] Data.core20.params Data.core20.name ([], []) Data.core20.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core20.body)]
    rw [blockB_dropE _ _ _ 0 246 246 wsplit_20_0.1 rfl wsplit_20_0.2.2,
      ← blockR_eq ((Data.core20.body.drop 0).take 246), wsplit_20_0.2.1]
    rw [blockB_dropE _ _ _ 246 63 309 wsplit_20_246.1 rfl wsplit_20_246.2.2,
      ← blockR_eq ((Data.core20.body.drop 246).take 63), wsplit_20_246.2.1]
    rw [blockB_dropE _ _ _ 309 48 357 wsplit_20_309.1 rfl wsplit_20_309.2.2,
      ← blockR_eq ((Data.core20.body.drop 309).take 48), wsplit_20_309.2.1]
    rw [blockB_dropE _ _ _ 357 63 420 wsplit_20_357.1 rfl wsplit_20_357.2.2,
      ← blockR_eq ((Data.core20.body.drop 357).take 63), wsplit_20_357.2.1]
    rw [blockB_dropE _ _ _ 420 48 468 wsplit_20_420.1 rfl wsplit_20_420.2.2,
      ← blockR_eq ((Data.core20.body.drop 420).take 48), wsplit_20_420.2.1]
    rw [blockB_dropE _ _ _ 468 110 578 wsplit_20_468.1 rfl wsplit_20_468.2.2,
      ← blockR_eq ((Data.core20.body.drop 468).take 110), wsplit_20_468.2.1]
    rw [← blockR_eq (Data.core20.body.drop 578), wsplit_20_578]
    rfl
  exact wchkIdx_of_split (fn := Data.core20) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_295 : wchkIdx 295 = true := by
  have hb : blockB (wlookJ 295) (womLookJ 295) true [(.n 12, 1536), (.n 14, 384), (.n 16, 16), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 896), (.n 26, 353), (.n 28, 353), (.n 30, 88), (.n 32, 16), (.n 212, 110), (.n 217, 0), (.n 218, 21), (.n 475, 64), (.n 479, 112), (.n 661, 110), (.n 666, 0), (.n 667, 5), (.n 751, 64), (.n 767, 56), (.n 949, 110), (.n 954, 0), (.n 955, 3), (.n 1015, 64), (.n 1031, 32), (.n 1111, 110), (.n 1116, 0), (.n 1117, 2), (.n 1168, 64), (.n 1184, 23), (.n 1197, 5), (.n 1410, 88), (.n 1412, 4), (.n 1690, 5), (.n 1693, 225), (.n 1699, 0), (.n 1700, 112), (.n 1706, 225), (.n 1712, 0), (.n 1713, 28), (.n 1719, 225), (.n 1725, 0), (.n 1726, 16), (.n 1732, 225), (.n 1738, 0), (.n 1739, 11)] Data.core295.params Data.core295.name ([], []) Data.core295.body = some (⟨506986, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core295.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_295_0.1 rfl wsplit_295_0.2.2,
      ← blockR_eq ((Data.core295.body.drop 0).take 721), wsplit_295_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_295_721.1 rfl wsplit_295_721.2.2,
      ← blockR_eq ((Data.core295.body.drop 721).take 721), wsplit_295_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_295_1442.1 rfl wsplit_295_1442.2.2,
      ← blockR_eq ((Data.core295.body.drop 1442).take 721), wsplit_295_1442.2.1]
    rw [← blockR_eq (Data.core295.body.drop 2163), wsplit_295_2163]
    rfl
  exact wchkIdx_of_split (fn := Data.core295) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_296 : wchkIdx 296 = true := by
  have hb : blockB (wlookJ 296) (womLookJ 296) true [(.n 12, 1536), (.n 14, 384), (.n 16, 32), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 896), (.n 26, 356), (.n 28, 356), (.n 30, 88), (.n 32, 16), (.n 212, 120), (.n 217, 0), (.n 218, 23), (.n 475, 64), (.n 479, 112), (.n 661, 120), (.n 666, 0), (.n 667, 6), (.n 751, 64), (.n 767, 56), (.n 949, 120), (.n 954, 0), (.n 955, 3), (.n 1015, 64), (.n 1031, 32), (.n 1111, 120), (.n 1116, 0), (.n 1117, 2), (.n 1168, 64), (.n 1184, 23), (.n 1197, 5), (.n 1422, 88), (.n 1424, 4), (.n 1730, 5), (.n 1733, 225), (.n 1739, 0), (.n 1740, 112), (.n 1746, 225), (.n 1752, 0), (.n 1753, 28), (.n 1759, 225), (.n 1765, 0), (.n 1766, 16), (.n 1772, 225), (.n 1778, 0), (.n 1779, 11)] Data.core296.params Data.core296.name ([], []) Data.core296.body = some (⟨524041, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core296.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_296_0.1 rfl wsplit_296_0.2.2,
      ← blockR_eq ((Data.core296.body.drop 0).take 721), wsplit_296_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_296_721.1 rfl wsplit_296_721.2.2,
      ← blockR_eq ((Data.core296.body.drop 721).take 721), wsplit_296_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_296_1442.1 rfl wsplit_296_1442.2.2,
      ← blockR_eq ((Data.core296.body.drop 1442).take 721), wsplit_296_1442.2.1]
    rw [← blockR_eq (Data.core296.body.drop 2163), wsplit_296_2163]
    rfl
  exact wchkIdx_of_split (fn := Data.core296) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_297 : wchkIdx 297 = true := by
  have hb : blockB (wlookJ 297) (womLookJ 297) true [(.n 12, 1664), (.n 14, 416), (.n 16, 4), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 1120), (.n 26, 371), (.n 28, 371), (.n 30, 110), (.n 32, 20), (.n 212, 120), (.n 217, 0), (.n 218, 23), (.n 475, 64), (.n 479, 112), (.n 661, 120), (.n 666, 0), (.n 667, 6), (.n 751, 64), (.n 767, 56), (.n 949, 120), (.n 954, 0), (.n 955, 3), (.n 1015, 64), (.n 1031, 32), (.n 1213, 120), (.n 1218, 0), (.n 1219, 2), (.n 1270, 64), (.n 1286, 23), (.n 1366, 120), (.n 1371, 0), (.n 1372, 2), (.n 1417, 64), (.n 1433, 17), (.n 1446, 5), (.n 1643, 110), (.n 1645, 5), (.n 1992, 6), (.n 1995, 225), (.n 2001, 0), (.n 2002, 112), (.n 2008, 225), (.n 2014, 0), (.n 2015, 28), (.n 2021, 225), (.n 2027, 0), (.n 2028, 16), (.n 2034, 225), (.n 2040, 0), (.n 2041, 11), (.n 2083, 225), (.n 2089, 0), (.n 2090, 8)] Data.core297.params Data.core297.name ([], []) Data.core297.body = some (⟨561448, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core297.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_297_0.1 rfl wsplit_297_0.2.2,
      ← blockR_eq ((Data.core297.body.drop 0).take 619), wsplit_297_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_297_619.1 rfl wsplit_297_619.2.2,
      ← blockR_eq ((Data.core297.body.drop 619).take 619), wsplit_297_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_297_1238.1 rfl wsplit_297_1238.2.2,
      ← blockR_eq ((Data.core297.body.drop 1238).take 619), wsplit_297_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_297_1857.1 rfl wsplit_297_1857.2.2,
      ← blockR_eq ((Data.core297.body.drop 1857).take 619), wsplit_297_1857.2.1]
    rw [← blockR_eq (Data.core297.body.drop 2476), wsplit_297_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core297) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_298 : wchkIdx 298 = true := by
  have hb : blockB (wlookJ 298) (womLookJ 298) true [(.n 12, 1664), (.n 14, 416), (.n 16, 8), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 1120), (.n 26, 382), (.n 28, 382), (.n 30, 110), (.n 32, 20), (.n 212, 130), (.n 217, 0), (.n 218, 25), (.n 475, 64), (.n 479, 112), (.n 661, 130), (.n 666, 0), (.n 667, 6), (.n 751, 64), (.n 767, 56), (.n 949, 130), (.n 954, 0), (.n 955, 4), (.n 1015, 64), (.n 1031, 32), (.n 1213, 130), (.n 1218, 0), (.n 1219, 3), (.n 1270, 64), (.n 1286, 23), (.n 1366, 130), (.n 1371, 0), (.n 1372, 2), (.n 1417, 64), (.n 1433, 17), (.n 1446, 5), (.n 1655, 110), (.n 1657, 5), (.n 2039, 6), (.n 2042, 225), (.n 2048, 0), (.n 2049, 112), (.n 2055, 225), (.n 2061, 0), (.n 2062, 28), (.n 2068, 225), (.n 2074, 0), (.n 2075, 16), (.n 2081, 225), (.n 2087, 0), (.n 2088, 11), (.n 2136, 225), (.n 2142, 0), (.n 2143, 8)] Data.core298.params Data.core298.name ([], []) Data.core298.body = some (⟨579986, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core298.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_298_0.1 rfl wsplit_298_0.2.2,
      ← blockR_eq ((Data.core298.body.drop 0).take 619), wsplit_298_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_298_619.1 rfl wsplit_298_619.2.2,
      ← blockR_eq ((Data.core298.body.drop 619).take 619), wsplit_298_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_298_1238.1 rfl wsplit_298_1238.2.2,
      ← blockR_eq ((Data.core298.body.drop 1238).take 619), wsplit_298_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_298_1857.1 rfl wsplit_298_1857.2.2,
      ← blockR_eq ((Data.core298.body.drop 1857).take 619), wsplit_298_1857.2.1]
    rw [← blockR_eq (Data.core298.body.drop 2476), wsplit_298_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core298) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_299 : wchkIdx 299 = true := by
  have hb : blockB (wlookJ 299) (womLookJ 299) true [(.n 12, 1664), (.n 14, 416), (.n 16, 16), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 1120), (.n 26, 380), (.n 28, 380), (.n 30, 110), (.n 32, 20), (.n 212, 130), (.n 217, 0), (.n 218, 25), (.n 475, 64), (.n 479, 112), (.n 661, 130), (.n 666, 0), (.n 667, 7), (.n 751, 64), (.n 767, 56), (.n 949, 130), (.n 954, 0), (.n 955, 4), (.n 1015, 64), (.n 1031, 32), (.n 1213, 130), (.n 1218, 0), (.n 1219, 3), (.n 1270, 64), (.n 1286, 23), (.n 1366, 130), (.n 1371, 0), (.n 1372, 2), (.n 1418, 64), (.n 1434, 18), (.n 1447, 5), (.n 1668, 110), (.n 1670, 5), (.n 2087, 6), (.n 2090, 225), (.n 2096, 0), (.n 2097, 112), (.n 2103, 225), (.n 2109, 0), (.n 2110, 28), (.n 2116, 225), (.n 2122, 0), (.n 2123, 16), (.n 2129, 225), (.n 2135, 0), (.n 2136, 11), (.n 2190, 225), (.n 2196, 0), (.n 2197, 9)] Data.core299.params Data.core299.name ([], []) Data.core299.body = some (⟨597182, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core299.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_299_0.1 rfl wsplit_299_0.2.2,
      ← blockR_eq ((Data.core299.body.drop 0).take 619), wsplit_299_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_299_619.1 rfl wsplit_299_619.2.2,
      ← blockR_eq ((Data.core299.body.drop 619).take 619), wsplit_299_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_299_1238.1 rfl wsplit_299_1238.2.2,
      ← blockR_eq ((Data.core299.body.drop 1238).take 619), wsplit_299_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_299_1857.1 rfl wsplit_299_1857.2.2,
      ← blockR_eq ((Data.core299.body.drop 1857).take 619), wsplit_299_1857.2.1]
    rw [← blockR_eq (Data.core299.body.drop 2476), wsplit_299_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core299) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_300 : wchkIdx 300 = true := by
  have hb : blockB (wlookJ 300) (womLookJ 300) true [(.n 12, 1664), (.n 14, 416), (.n 16, 32), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 1125), (.n 26, 381), (.n 28, 381), (.n 30, 110), (.n 32, 20), (.n 212, 150), (.n 217, 0), (.n 218, 29), (.n 476, 64), (.n 480, 112), (.n 662, 150), (.n 667, 0), (.n 668, 7), (.n 752, 64), (.n 768, 56), (.n 950, 150), (.n 955, 0), (.n 956, 4), (.n 1016, 64), (.n 1032, 32), (.n 1214, 150), (.n 1219, 0), (.n 1220, 3), (.n 1271, 64), (.n 1287, 23), (.n 1367, 150), (.n 1372, 0), (.n 1373, 2), (.n 1419, 64), (.n 1435, 18), (.n 1448, 5), (.n 1681, 110), (.n 1683, 5), (.n 2135, 6), (.n 2138, 226), (.n 2144, 0), (.n 2145, 112), (.n 2277, 226), (.n 2283, 0), (.n 2284, 28), (.n 2290, 226), (.n 2296, 0), (.n 2297, 16), (.n 2303, 226), (.n 2309, 0), (.n 2310, 11), (.n 2370, 226), (.n 2376, 0), (.n 2377, 9)] Data.core300.params Data.core300.name ([], []) Data.core300.body = some (⟨616778, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core300.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_300_0.1 rfl wsplit_300_0.2.2,
      ← blockR_eq ((Data.core300.body.drop 0).take 619), wsplit_300_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_300_619.1 rfl wsplit_300_619.2.2,
      ← blockR_eq ((Data.core300.body.drop 619).take 619), wsplit_300_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_300_1238.1 rfl wsplit_300_1238.2.2,
      ← blockR_eq ((Data.core300.body.drop 1238).take 619), wsplit_300_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_300_1857.1 rfl wsplit_300_1857.2.2,
      ← blockR_eq ((Data.core300.body.drop 1857).take 619), wsplit_300_1857.2.1]
    rw [← blockR_eq (Data.core300.body.drop 2476), wsplit_300_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core300) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_301 : wchkIdx 301 = true := by
  have hb : blockB (wlookJ 301) (womLookJ 301) true [(.n 12, 1728), (.n 14, 432), (.n 16, 4), (.n 18, 12), (.n 20, 26), (.n 22, 6), (.n 24, 1350), (.n 26, 391), (.n 28, 391), (.n 30, 132), (.n 32, 24), (.n 212, 150), (.n 217, 0), (.n 218, 29), (.n 476, 64), (.n 480, 112), (.n 662, 150), (.n 667, 0), (.n 668, 7), (.n 752, 64), (.n 768, 56), (.n 950, 150), (.n 955, 0), (.n 956, 4), (.n 1016, 64), (.n 1032, 32), (.n 1214, 150), (.n 1219, 0), (.n 1220, 3), (.n 1271, 64), (.n 1287, 23), (.n 1469, 150), (.n 1474, 0), (.n 1475, 2), (.n 1521, 64), (.n 1537, 18), (.n 1617, 150), (.n 1622, 0), (.n 1623, 2), (.n 1665, 64), (.n 1681, 14), (.n 1694, 5), (.n 1899, 132), (.n 1901, 6), (.n 2401, 7), (.n 2404, 226), (.n 2410, 0), (.n 2411, 112), (.n 2549, 226), (.n 2555, 0), (.n 2556, 28), (.n 2562, 226), (.n 2568, 0), (.n 2569, 16), (.n 2575, 226), (.n 2581, 0), (.n 2582, 11), (.n 2648, 226), (.n 2654, 0), (.n 2655, 9), (.n 2661, 226), (.n 2667, 0), (.n 2668, 7)] Data.core301.params Data.core301.name ([], []) Data.core301.body = some (⟨652971, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core301.body)]
    rw [blockB_dropE _ _ _ 0 542 542 wsplit_301_0.1 rfl wsplit_301_0.2.2,
      ← blockR_eq ((Data.core301.body.drop 0).take 542), wsplit_301_0.2.1]
    rw [blockB_dropE _ _ _ 542 542 1084 wsplit_301_542.1 rfl wsplit_301_542.2.2,
      ← blockR_eq ((Data.core301.body.drop 542).take 542), wsplit_301_542.2.1]
    rw [blockB_dropE _ _ _ 1084 542 1626 wsplit_301_1084.1 rfl wsplit_301_1084.2.2,
      ← blockR_eq ((Data.core301.body.drop 1084).take 542), wsplit_301_1084.2.1]
    rw [blockB_dropE _ _ _ 1626 542 2168 wsplit_301_1626.1 rfl wsplit_301_1626.2.2,
      ← blockR_eq ((Data.core301.body.drop 1626).take 542), wsplit_301_1626.2.1]
    rw [blockB_dropE _ _ _ 2168 542 2710 wsplit_301_2168.1 rfl wsplit_301_2168.2.2,
      ← blockR_eq ((Data.core301.body.drop 2168).take 542), wsplit_301_2168.2.1]
    rw [blockB_dropE _ _ _ 2710 542 3252 wsplit_301_2710.1 rfl wsplit_301_2710.2.2,
      ← blockR_eq ((Data.core301.body.drop 2710).take 542), wsplit_301_2710.2.1]
    rw [← blockR_eq (Data.core301.body.drop 3252), wsplit_301_3252]
    rfl
  exact wchkIdx_of_split (fn := Data.core301) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_302 : wchkIdx 302 = true := by
  have hb : blockB (wlookJ 302) (womLookJ 302) true [(.n 12, 1024), (.n 14, 256), (.n 16, 16), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 448), (.n 26, 235), (.n 28, 235), (.n 30, 88), (.n 32, 16), (.n 212, 65), (.n 217, 0), (.n 218, 12), (.n 363, 64), (.n 367, 56), (.n 549, 65), (.n 554, 0), (.n 555, 5), (.n 628, 64), (.n 644, 45), (.n 826, 65), (.n 831, 0), (.n 832, 3), (.n 888, 64), (.n 904, 28), (.n 984, 65), (.n 989, 0), (.n 990, 2), (.n 1039, 64), (.n 1055, 21), (.n 1068, 5), (.n 1281, 88), (.n 1283, 4), (.n 1561, 5), (.n 1564, 113), (.n 1570, 0), (.n 1571, 56), (.n 1577, 113), (.n 1583, 0), (.n 1584, 22), (.n 1662, 113), (.n 1668, 0), (.n 1669, 14), (.n 1675, 113), (.n 1681, 0), (.n 1682, 10)] Data.core302.params Data.core302.name ([], []) Data.core302.body = some (⟨320890, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core302.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_302_0.1 rfl wsplit_302_0.2.2,
      ← blockR_eq ((Data.core302.body.drop 0).take 721), wsplit_302_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_302_721.1 rfl wsplit_302_721.2.2,
      ← blockR_eq ((Data.core302.body.drop 721).take 721), wsplit_302_721.2.1]
    rw [← blockR_eq (Data.core302.body.drop 1442), wsplit_302_1442]
    rfl
  exact wchkIdx_of_split (fn := Data.core302) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_303 : wchkIdx 303 = true := by
  have hb : blockB (wlookJ 303) (womLookJ 303) true [(.n 12, 1024), (.n 14, 256), (.n 16, 32), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 448), (.n 26, 227), (.n 28, 227), (.n 30, 88), (.n 32, 16), (.n 212, 65), (.n 217, 0), (.n 218, 12), (.n 363, 64), (.n 367, 56), (.n 549, 65), (.n 554, 0), (.n 555, 5), (.n 628, 64), (.n 644, 45), (.n 826, 65), (.n 831, 0), (.n 832, 3), (.n 888, 64), (.n 904, 28), (.n 984, 65), (.n 989, 0), (.n 990, 2), (.n 1039, 64), (.n 1055, 21), (.n 1068, 5), (.n 1293, 88), (.n 1295, 4), (.n 1601, 5), (.n 1604, 113), (.n 1610, 0), (.n 1611, 56), (.n 1617, 113), (.n 1623, 0), (.n 1624, 22), (.n 1708, 113), (.n 1714, 0), (.n 1715, 14), (.n 1721, 113), (.n 1727, 0), (.n 1728, 10)] Data.core303.params Data.core303.name ([], []) Data.core303.body = some (⟨329984, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core303.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_303_0.1 rfl wsplit_303_0.2.2,
      ← blockR_eq ((Data.core303.body.drop 0).take 721), wsplit_303_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_303_721.1 rfl wsplit_303_721.2.2,
      ← blockR_eq ((Data.core303.body.drop 721).take 721), wsplit_303_721.2.1]
    rw [← blockR_eq (Data.core303.body.drop 1442), wsplit_303_1442]
    rfl
  exact wchkIdx_of_split (fn := Data.core303) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_304 : wchkIdx 304 = true := by
  have hb : blockB (wlookJ 304) (womLookJ 304) true [(.n 12, 1088), (.n 14, 272), (.n 16, 4), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 560), (.n 26, 243), (.n 28, 243), (.n 30, 110), (.n 32, 20), (.n 212, 70), (.n 217, 0), (.n 218, 13), (.n 363, 64), (.n 367, 56), (.n 549, 70), (.n 554, 0), (.n 555, 5), (.n 628, 64), (.n 644, 45), (.n 826, 70), (.n 831, 0), (.n 832, 3), (.n 888, 64), (.n 904, 28), (.n 1086, 70), (.n 1091, 0), (.n 1092, 2), (.n 1141, 64), (.n 1157, 21), (.n 1237, 70), (.n 1242, 0), (.n 1243, 2), (.n 1287, 64), (.n 1303, 16), (.n 1316, 5), (.n 1513, 110), (.n 1515, 5), (.n 1862, 6), (.n 1865, 113), (.n 1871, 0), (.n 1872, 56), (.n 1878, 113), (.n 1884, 0), (.n 1885, 22), (.n 1975, 113), (.n 1981, 0), (.n 1982, 14), (.n 1988, 113), (.n 1994, 0), (.n 1995, 10), (.n 2037, 113), (.n 2043, 0), (.n 2044, 8)] Data.core304.params Data.core304.name ([], []) Data.core304.body = some (⟨362162, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core304.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_304_0.1 rfl wsplit_304_0.2.2,
      ← blockR_eq ((Data.core304.body.drop 0).take 619), wsplit_304_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_304_619.1 rfl wsplit_304_619.2.2,
      ← blockR_eq ((Data.core304.body.drop 619).take 619), wsplit_304_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_304_1238.1 rfl wsplit_304_1238.2.2,
      ← blockR_eq ((Data.core304.body.drop 1238).take 619), wsplit_304_1238.2.1]
    rw [← blockR_eq (Data.core304.body.drop 1857), wsplit_304_1857]
    rfl
  exact wchkIdx_of_split (fn := Data.core304) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_305 : wchkIdx 305 = true := by
  have hb : blockB (wlookJ 305) (womLookJ 305) true [(.n 12, 1088), (.n 14, 272), (.n 16, 8), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 560), (.n 26, 244), (.n 28, 244), (.n 30, 110), (.n 32, 20), (.n 212, 70), (.n 217, 0), (.n 218, 13), (.n 363, 64), (.n 367, 56), (.n 549, 70), (.n 554, 0), (.n 555, 5), (.n 628, 64), (.n 644, 45), (.n 826, 70), (.n 831, 0), (.n 832, 3), (.n 888, 64), (.n 904, 28), (.n 1086, 70), (.n 1091, 0), (.n 1092, 3), (.n 1141, 64), (.n 1157, 21), (.n 1237, 70), (.n 1242, 0), (.n 1243, 2), (.n 1287, 64), (.n 1303, 16), (.n 1316, 5), (.n 1525, 110), (.n 1527, 5), (.n 1909, 6), (.n 1912, 113), (.n 1918, 0), (.n 1919, 56), (.n 1925, 113), (.n 1931, 0), (.n 1932, 22), (.n 2028, 113), (.n 2034, 0), (.n 2035, 14), (.n 2041, 113), (.n 2047, 0), (.n 2048, 10), (.n 2096, 113), (.n 2102, 0), (.n 2103, 8)] Data.core305.params Data.core305.name ([], []) Data.core305.body = some (⟨372618, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core305.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_305_0.1 rfl wsplit_305_0.2.2,
      ← blockR_eq ((Data.core305.body.drop 0).take 619), wsplit_305_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_305_619.1 rfl wsplit_305_619.2.2,
      ← blockR_eq ((Data.core305.body.drop 619).take 619), wsplit_305_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_305_1238.1 rfl wsplit_305_1238.2.2,
      ← blockR_eq ((Data.core305.body.drop 1238).take 619), wsplit_305_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_305_1857.1 rfl wsplit_305_1857.2.2,
      ← blockR_eq ((Data.core305.body.drop 1857).take 619), wsplit_305_1857.2.1]
    rw [← blockR_eq (Data.core305.body.drop 2476), wsplit_305_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core305) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_306 : wchkIdx 306 = true := by
  have hb : blockB (wlookJ 306) (womLookJ 306) true [(.n 12, 1088), (.n 14, 272), (.n 16, 16), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 560), (.n 26, 243), (.n 28, 243), (.n 30, 110), (.n 32, 20), (.n 212, 75), (.n 217, 0), (.n 218, 14), (.n 363, 64), (.n 367, 56), (.n 549, 75), (.n 554, 0), (.n 555, 5), (.n 628, 64), (.n 644, 45), (.n 826, 75), (.n 831, 0), (.n 832, 4), (.n 888, 64), (.n 904, 28), (.n 1086, 75), (.n 1091, 0), (.n 1092, 3), (.n 1141, 64), (.n 1157, 21), (.n 1237, 75), (.n 1242, 0), (.n 1243, 2), (.n 1287, 64), (.n 1303, 16), (.n 1316, 5), (.n 1537, 110), (.n 1539, 5), (.n 1956, 6), (.n 1959, 113), (.n 1965, 0), (.n 1966, 56), (.n 1972, 113), (.n 1978, 0), (.n 1979, 22), (.n 2081, 113), (.n 2087, 0), (.n 2088, 14), (.n 2094, 113), (.n 2100, 0), (.n 2101, 10), (.n 2155, 113), (.n 2161, 0), (.n 2162, 8)] Data.core306.params Data.core306.name ([], []) Data.core306.body = some (⟨384053, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core306.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_306_0.1 rfl wsplit_306_0.2.2,
      ← blockR_eq ((Data.core306.body.drop 0).take 619), wsplit_306_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_306_619.1 rfl wsplit_306_619.2.2,
      ← blockR_eq ((Data.core306.body.drop 619).take 619), wsplit_306_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_306_1238.1 rfl wsplit_306_1238.2.2,
      ← blockR_eq ((Data.core306.body.drop 1238).take 619), wsplit_306_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_306_1857.1 rfl wsplit_306_1857.2.2,
      ← blockR_eq ((Data.core306.body.drop 1857).take 619), wsplit_306_1857.2.1]
    rw [← blockR_eq (Data.core306.body.drop 2476), wsplit_306_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core306) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_307 : wchkIdx 307 = true := by
  have hb : blockB (wlookJ 307) (womLookJ 307) true [(.n 12, 1088), (.n 14, 272), (.n 16, 32), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 560), (.n 26, 243), (.n 28, 243), (.n 30, 110), (.n 32, 20), (.n 212, 75), (.n 217, 0), (.n 218, 14), (.n 363, 64), (.n 367, 56), (.n 549, 75), (.n 554, 0), (.n 555, 6), (.n 628, 64), (.n 644, 45), (.n 826, 75), (.n 831, 0), (.n 832, 4), (.n 888, 64), (.n 904, 28), (.n 1086, 75), (.n 1091, 0), (.n 1092, 3), (.n 1141, 64), (.n 1157, 21), (.n 1237, 75), (.n 1242, 0), (.n 1243, 2), (.n 1287, 64), (.n 1303, 16), (.n 1316, 5), (.n 1549, 110), (.n 1551, 5), (.n 2003, 6), (.n 2006, 113), (.n 2012, 0), (.n 2013, 56), (.n 2019, 113), (.n 2025, 0), (.n 2026, 22), (.n 2134, 113), (.n 2140, 0), (.n 2141, 14), (.n 2147, 113), (.n 2153, 0), (.n 2154, 10), (.n 2214, 113), (.n 2220, 0), (.n 2221, 8)] Data.core307.params Data.core307.name ([], []) Data.core307.body = some (⟨394702, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core307.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_307_0.1 rfl wsplit_307_0.2.2,
      ← blockR_eq ((Data.core307.body.drop 0).take 619), wsplit_307_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_307_619.1 rfl wsplit_307_619.2.2,
      ← blockR_eq ((Data.core307.body.drop 619).take 619), wsplit_307_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_307_1238.1 rfl wsplit_307_1238.2.2,
      ← blockR_eq ((Data.core307.body.drop 1238).take 619), wsplit_307_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_307_1857.1 rfl wsplit_307_1857.2.2,
      ← blockR_eq ((Data.core307.body.drop 1857).take 619), wsplit_307_1857.2.1]
    rw [← blockR_eq (Data.core307.body.drop 2476), wsplit_307_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core307) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_308 : wchkIdx 308 = true := by
  have hb : blockB (wlookJ 308) (womLookJ 308) true [(.n 12, 1152), (.n 14, 288), (.n 16, 4), (.n 18, 12), (.n 20, 26), (.n 22, 6), (.n 24, 672), (.n 26, 257), (.n 28, 257), (.n 30, 132), (.n 32, 24), (.n 212, 75), (.n 217, 0), (.n 218, 14), (.n 363, 64), (.n 367, 56), (.n 549, 75), (.n 554, 0), (.n 555, 6), (.n 628, 64), (.n 644, 45), (.n 826, 75), (.n 831, 0), (.n 832, 4), (.n 888, 64), (.n 904, 28), (.n 1086, 75), (.n 1091, 0), (.n 1092, 3), (.n 1141, 64), (.n 1157, 21), (.n 1339, 75), (.n 1344, 0), (.n 1345, 2), (.n 1389, 64), (.n 1405, 16), (.n 1485, 75), (.n 1490, 0), (.n 1491, 2), (.n 1532, 64), (.n 1548, 13), (.n 1561, 5), (.n 1766, 132), (.n 1768, 6), (.n 2268, 7), (.n 2271, 113), (.n 2277, 0), (.n 2278, 56), (.n 2284, 113), (.n 2290, 0), (.n 2291, 22), (.n 2405, 113), (.n 2411, 0), (.n 2412, 14), (.n 2418, 113), (.n 2424, 0), (.n 2425, 10), (.n 2491, 113), (.n 2497, 0), (.n 2498, 8), (.n 2504, 113), (.n 2510, 0), (.n 2511, 6)] Data.core308.params Data.core308.name ([], []) Data.core308.body = some (⟨424212, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core308.body)]
    rw [blockB_dropE _ _ _ 0 542 542 wsplit_308_0.1 rfl wsplit_308_0.2.2,
      ← blockR_eq ((Data.core308.body.drop 0).take 542), wsplit_308_0.2.1]
    rw [blockB_dropE _ _ _ 542 542 1084 wsplit_308_542.1 rfl wsplit_308_542.2.2,
      ← blockR_eq ((Data.core308.body.drop 542).take 542), wsplit_308_542.2.1]
    rw [blockB_dropE _ _ _ 1084 542 1626 wsplit_308_1084.1 rfl wsplit_308_1084.2.2,
      ← blockR_eq ((Data.core308.body.drop 1084).take 542), wsplit_308_1084.2.1]
    rw [blockB_dropE _ _ _ 1626 542 2168 wsplit_308_1626.1 rfl wsplit_308_1626.2.2,
      ← blockR_eq ((Data.core308.body.drop 1626).take 542), wsplit_308_1626.2.1]
    rw [blockB_dropE _ _ _ 2168 542 2710 wsplit_308_2168.1 rfl wsplit_308_2168.2.2,
      ← blockR_eq ((Data.core308.body.drop 2168).take 542), wsplit_308_2168.2.1]
    rw [← blockR_eq (Data.core308.body.drop 2710), wsplit_308_2710]
    rfl
  exact wchkIdx_of_split (fn := Data.core308) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_309 : wchkIdx 309 = true := by
  have hb : blockB (wlookJ 309) (womLookJ 309) true [(.n 12, 1024), (.n 14, 256), (.n 16, 16), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 300), (.n 26, 177), (.n 28, 177), (.n 30, 88), (.n 32, 16), (.n 212, 45), (.n 217, 0), (.n 218, 8), (.n 326, 64), (.n 330, 37), (.n 512, 45), (.n 517, 0), (.n 518, 4), (.n 584, 64), (.n 600, 38), (.n 782, 45), (.n 787, 0), (.n 788, 3), (.n 841, 64), (.n 857, 25), (.n 937, 45), (.n 942, 0), (.n 943, 2), (.n 990, 64), (.n 1006, 19), (.n 1019, 5), (.n 1232, 88), (.n 1234, 4), (.n 1512, 5), (.n 1515, 76), (.n 1521, 0), (.n 1522, 37), (.n 1624, 76), (.n 1630, 0), (.n 1631, 19), (.n 1637, 76), (.n 1643, 0), (.n 1644, 12), (.n 1698, 76), (.n 1704, 0), (.n 1705, 9)] Data.core309.params Data.core309.name ([], []) Data.core309.body = some (⟨249662, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core309.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_309_0.1 rfl wsplit_309_0.2.2,
      ← blockR_eq ((Data.core309.body.drop 0).take 721), wsplit_309_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_309_721.1 rfl wsplit_309_721.2.2,
      ← blockR_eq ((Data.core309.body.drop 721).take 721), wsplit_309_721.2.1]
    rw [← blockR_eq (Data.core309.body.drop 1442), wsplit_309_1442]
    rfl
  exact wchkIdx_of_split (fn := Data.core309) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_310 : wchkIdx 310 = true := by
  have hb : blockB (wlookJ 310) (womLookJ 310) true [(.n 12, 1024), (.n 14, 256), (.n 16, 32), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 300), (.n 26, 173), (.n 28, 173), (.n 30, 88), (.n 32, 16), (.n 212, 50), (.n 217, 0), (.n 218, 9), (.n 326, 64), (.n 330, 37), (.n 512, 50), (.n 517, 0), (.n 518, 4), (.n 584, 64), (.n 600, 38), (.n 782, 50), (.n 787, 0), (.n 788, 3), (.n 841, 64), (.n 857, 25), (.n 937, 50), (.n 942, 0), (.n 943, 2), (.n 990, 64), (.n 1006, 19), (.n 1019, 5), (.n 1244, 88), (.n 1246, 4), (.n 1552, 5), (.n 1555, 76), (.n 1561, 0), (.n 1562, 37), (.n 1670, 76), (.n 1676, 0), (.n 1677, 19), (.n 1683, 76), (.n 1689, 0), (.n 1690, 12), (.n 1750, 76), (.n 1756, 0), (.n 1757, 9)] Data.core310.params Data.core310.name ([], []) Data.core310.body = some (⟨257646, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core310.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_310_0.1 rfl wsplit_310_0.2.2,
      ← blockR_eq ((Data.core310.body.drop 0).take 721), wsplit_310_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_310_721.1 rfl wsplit_310_721.2.2,
      ← blockR_eq ((Data.core310.body.drop 721).take 721), wsplit_310_721.2.1]
    rw [← blockR_eq (Data.core310.body.drop 1442), wsplit_310_1442]
    rfl
  exact wchkIdx_of_split (fn := Data.core310) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_311 : wchkIdx 311 = true := by
  have hb : blockB (wlookJ 311) (womLookJ 311) true [(.n 12, 1088), (.n 14, 272), (.n 16, 4), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 375), (.n 26, 198), (.n 28, 198), (.n 30, 110), (.n 32, 20), (.n 212, 50), (.n 217, 0), (.n 218, 9), (.n 326, 64), (.n 330, 37), (.n 512, 50), (.n 517, 0), (.n 518, 5), (.n 584, 64), (.n 600, 38), (.n 782, 50), (.n 787, 0), (.n 788, 3), (.n 841, 64), (.n 857, 25), (.n 1039, 50), (.n 1044, 0), (.n 1045, 2), (.n 1092, 64), (.n 1108, 19), (.n 1188, 50), (.n 1193, 0), (.n 1194, 2), (.n 1237, 64), (.n 1253, 15), (.n 1266, 5), (.n 1463, 110), (.n 1465, 5), (.n 1812, 6), (.n 1815, 76), (.n 1821, 0), (.n 1822, 37), (.n 1936, 76), (.n 1942, 0), (.n 1943, 19), (.n 1949, 76), (.n 1955, 0), (.n 1956, 12), (.n 2022, 76), (.n 2028, 0), (.n 2029, 9), (.n 2071, 76), (.n 2077, 0), (.n 2078, 7)] Data.core311.params Data.core311.name ([], []) Data.core311.body = some (⟨286748, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core311.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_311_0.1 rfl wsplit_311_0.2.2,
      ← blockR_eq ((Data.core311.body.drop 0).take 619), wsplit_311_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_311_619.1 rfl wsplit_311_619.2.2,
      ← blockR_eq ((Data.core311.body.drop 619).take 619), wsplit_311_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_311_1238.1 rfl wsplit_311_1238.2.2,
      ← blockR_eq ((Data.core311.body.drop 1238).take 619), wsplit_311_1238.2.1]
    rw [← blockR_eq (Data.core311.body.drop 1857), wsplit_311_1857]
    rfl
  exact wchkIdx_of_split (fn := Data.core311) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_312 : wchkIdx 312 = true := by
  have hb : blockB (wlookJ 312) (womLookJ 312) true [(.n 12, 1088), (.n 14, 272), (.n 16, 8), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 375), (.n 26, 192), (.n 28, 192), (.n 30, 110), (.n 32, 20), (.n 212, 55), (.n 217, 0), (.n 218, 10), (.n 326, 64), (.n 330, 37), (.n 512, 55), (.n 517, 0), (.n 518, 5), (.n 584, 64), (.n 600, 38), (.n 782, 55), (.n 787, 0), (.n 788, 3), (.n 841, 64), (.n 857, 25), (.n 1039, 55), (.n 1044, 0), (.n 1045, 2), (.n 1092, 64), (.n 1108, 19), (.n 1188, 55), (.n 1193, 0), (.n 1194, 2), (.n 1237, 64), (.n 1253, 15), (.n 1266, 5), (.n 1475, 110), (.n 1477, 5), (.n 1859, 6), (.n 1862, 76), (.n 1868, 0), (.n 1869, 37), (.n 1989, 76), (.n 1995, 0), (.n 1996, 19), (.n 2002, 76), (.n 2008, 0), (.n 2009, 12), (.n 2081, 76), (.n 2087, 0), (.n 2088, 9), (.n 2136, 76), (.n 2142, 0), (.n 2143, 7)] Data.core312.params Data.core312.name ([], []) Data.core312.body = some (⟨295205, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core312.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_312_0.1 rfl wsplit_312_0.2.2,
      ← blockR_eq ((Data.core312.body.drop 0).take 619), wsplit_312_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_312_619.1 rfl wsplit_312_619.2.2,
      ← blockR_eq ((Data.core312.body.drop 619).take 619), wsplit_312_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_312_1238.1 rfl wsplit_312_1238.2.2,
      ← blockR_eq ((Data.core312.body.drop 1238).take 619), wsplit_312_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_312_1857.1 rfl wsplit_312_1857.2.2,
      ← blockR_eq ((Data.core312.body.drop 1857).take 619), wsplit_312_1857.2.1]
    rw [← blockR_eq (Data.core312.body.drop 2476), wsplit_312_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core312) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_313 : wchkIdx 313 = true := by
  have hb : blockB (wlookJ 313) (womLookJ 313) true [(.n 12, 1088), (.n 14, 272), (.n 16, 16), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 375), (.n 26, 194), (.n 28, 194), (.n 30, 110), (.n 32, 20), (.n 212, 55), (.n 217, 0), (.n 218, 10), (.n 326, 64), (.n 330, 37), (.n 512, 55), (.n 517, 0), (.n 518, 5), (.n 584, 64), (.n 600, 38), (.n 782, 55), (.n 787, 0), (.n 788, 3), (.n 841, 64), (.n 857, 25), (.n 1039, 55), (.n 1044, 0), (.n 1045, 3), (.n 1092, 64), (.n 1108, 19), (.n 1188, 55), (.n 1193, 0), (.n 1194, 2), (.n 1237, 64), (.n 1253, 15), (.n 1266, 5), (.n 1487, 110), (.n 1489, 5), (.n 1906, 6), (.n 1909, 76), (.n 1915, 0), (.n 1916, 37), (.n 2042, 76), (.n 2048, 0), (.n 2049, 19), (.n 2055, 76), (.n 2061, 0), (.n 2062, 12), (.n 2140, 76), (.n 2146, 0), (.n 2147, 9), (.n 2201, 76), (.n 2207, 0), (.n 2208, 7)] Data.core313.params Data.core313.name ([], []) Data.core313.body = some (⟨303614, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core313.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_313_0.1 rfl wsplit_313_0.2.2,
      ← blockR_eq ((Data.core313.body.drop 0).take 619), wsplit_313_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_313_619.1 rfl wsplit_313_619.2.2,
      ← blockR_eq ((Data.core313.body.drop 619).take 619), wsplit_313_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_313_1238.1 rfl wsplit_313_1238.2.2,
      ← blockR_eq ((Data.core313.body.drop 1238).take 619), wsplit_313_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_313_1857.1 rfl wsplit_313_1857.2.2,
      ← blockR_eq ((Data.core313.body.drop 1857).take 619), wsplit_313_1857.2.1]
    rw [← blockR_eq (Data.core313.body.drop 2476), wsplit_313_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core313) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_314 : wchkIdx 314 = true := by
  have hb : blockB (wlookJ 314) (womLookJ 314) true [(.n 12, 1088), (.n 14, 272), (.n 16, 32), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 375), (.n 26, 197), (.n 28, 197), (.n 30, 110), (.n 32, 20), (.n 212, 55), (.n 217, 0), (.n 218, 10), (.n 326, 64), (.n 330, 37), (.n 512, 55), (.n 517, 0), (.n 518, 5), (.n 584, 64), (.n 600, 38), (.n 782, 55), (.n 787, 0), (.n 788, 4), (.n 841, 64), (.n 857, 25), (.n 1039, 55), (.n 1044, 0), (.n 1045, 3), (.n 1092, 64), (.n 1108, 19), (.n 1188, 55), (.n 1193, 0), (.n 1194, 2), (.n 1237, 64), (.n 1253, 15), (.n 1266, 5), (.n 1499, 110), (.n 1501, 5), (.n 1953, 6), (.n 1956, 76), (.n 1962, 0), (.n 1963, 37), (.n 2095, 76), (.n 2101, 0), (.n 2102, 19), (.n 2108, 76), (.n 2114, 0), (.n 2115, 12), (.n 2199, 76), (.n 2205, 0), (.n 2206, 9), (.n 2266, 76), (.n 2272, 0), (.n 2273, 7)] Data.core314.params Data.core314.name ([], []) Data.core314.body = some (⟨312122, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core314.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_314_0.1 rfl wsplit_314_0.2.2,
      ← blockR_eq ((Data.core314.body.drop 0).take 619), wsplit_314_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_314_619.1 rfl wsplit_314_619.2.2,
      ← blockR_eq ((Data.core314.body.drop 619).take 619), wsplit_314_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_314_1238.1 rfl wsplit_314_1238.2.2,
      ← blockR_eq ((Data.core314.body.drop 1238).take 619), wsplit_314_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_314_1857.1 rfl wsplit_314_1857.2.2,
      ← blockR_eq ((Data.core314.body.drop 1857).take 619), wsplit_314_1857.2.1]
    rw [← blockR_eq (Data.core314.body.drop 2476), wsplit_314_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core314) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_315 : wchkIdx 315 = true := by
  have hb : blockB (wlookJ 315) (womLookJ 315) true [(.n 12, 1152), (.n 14, 288), (.n 16, 4), (.n 18, 12), (.n 20, 26), (.n 22, 6), (.n 24, 450), (.n 26, 209), (.n 28, 209), (.n 30, 132), (.n 32, 24), (.n 212, 60), (.n 217, 0), (.n 218, 11), (.n 326, 64), (.n 330, 37), (.n 512, 60), (.n 517, 0), (.n 518, 5), (.n 584, 64), (.n 600, 38), (.n 782, 60), (.n 787, 0), (.n 788, 4), (.n 841, 64), (.n 857, 25), (.n 1039, 60), (.n 1044, 0), (.n 1045, 3), (.n 1092, 64), (.n 1108, 19), (.n 1290, 60), (.n 1295, 0), (.n 1296, 2), (.n 1339, 64), (.n 1355, 15), (.n 1435, 60), (.n 1440, 0), (.n 1441, 2), (.n 1482, 64), (.n 1498, 13), (.n 1511, 5), (.n 1716, 132), (.n 1718, 6), (.n 2218, 7), (.n 2221, 76), (.n 2227, 0), (.n 2228, 37), (.n 2366, 76), (.n 2372, 0), (.n 2373, 19), (.n 2379, 76), (.n 2385, 0), (.n 2386, 12), (.n 2476, 76), (.n 2482, 0), (.n 2483, 9), (.n 2549, 76), (.n 2555, 0), (.n 2556, 7), (.n 2598, 76), (.n 2604, 0), (.n 2605, 6)] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨340908, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [blockB_dropE _ _ _ 0 542 542 wsplit_315_0.1 rfl wsplit_315_0.2.2,
      ← blockR_eq ((Data.core315.body.drop 0).take 542), wsplit_315_0.2.1]
    rw [blockB_dropE _ _ _ 542 542 1084 wsplit_315_542.1 rfl wsplit_315_542.2.2,
      ← blockR_eq ((Data.core315.body.drop 542).take 542), wsplit_315_542.2.1]
    rw [blockB_dropE _ _ _ 1084 542 1626 wsplit_315_1084.1 rfl wsplit_315_1084.2.2,
      ← blockR_eq ((Data.core315.body.drop 1084).take 542), wsplit_315_1084.2.1]
    rw [blockB_dropE _ _ _ 1626 542 2168 wsplit_315_1626.1 rfl wsplit_315_1626.2.2,
      ← blockR_eq ((Data.core315.body.drop 1626).take 542), wsplit_315_1626.2.1]
    rw [blockB_dropE _ _ _ 2168 542 2710 wsplit_315_2168.1 rfl wsplit_315_2168.2.2,
      ← blockR_eq ((Data.core315.body.drop 2168).take 542), wsplit_315_2168.2.1]
    rw [← blockR_eq (Data.core315.body.drop 2710), wsplit_315_2710]
    rfl
  exact wchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_316 : wchkIdx 316 = true := by
  have hb : blockB (wlookJ 316) (womLookJ 316) true [(.n 12, 640), (.n 14, 160), (.n 16, 16), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 224), (.n 26, 155), (.n 28, 155), (.n 30, 88), (.n 32, 16), (.n 212, 40), (.n 217, 0), (.n 218, 7), (.n 307, 64), (.n 311, 28), (.n 493, 40), (.n 498, 0), (.n 499, 4), (.n 559, 64), (.n 575, 32), (.n 757, 40), (.n 762, 0), (.n 763, 3), (.n 814, 64), (.n 830, 23), (.n 910, 40), (.n 915, 0), (.n 916, 2), (.n 962, 64), (.n 978, 18), (.n 991, 5), (.n 1204, 88), (.n 1206, 4), (.n 1484, 5), (.n 1487, 57), (.n 1493, 0), (.n 1494, 28), (.n 1500, 57), (.n 1506, 0), (.n 1507, 16), (.n 1513, 57), (.n 1519, 0), (.n 1520, 11), (.n 1574, 57), (.n 1580, 0), (.n 1581, 9)] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨212616, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_316_0.1 rfl wsplit_316_0.2.2,
      ← blockR_eq ((Data.core316.body.drop 0).take 721), wsplit_316_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_316_721.1 rfl wsplit_316_721.2.2,
      ← blockR_eq ((Data.core316.body.drop 721).take 721), wsplit_316_721.2.1]
    rw [← blockR_eq (Data.core316.body.drop 1442), wsplit_316_1442]
    rfl
  exact wchkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_317 : wchkIdx 317 = true := by
  have hb : blockB (wlookJ 317) (womLookJ 317) true [(.n 12, 640), (.n 14, 160), (.n 16, 32), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 224), (.n 26, 149), (.n 28, 149), (.n 30, 88), (.n 32, 16), (.n 212, 40), (.n 217, 0), (.n 218, 7), (.n 307, 64), (.n 311, 28), (.n 493, 40), (.n 498, 0), (.n 499, 4), (.n 559, 64), (.n 575, 32), (.n 757, 40), (.n 762, 0), (.n 763, 3), (.n 814, 64), (.n 830, 23), (.n 910, 40), (.n 915, 0), (.n 916, 2), (.n 962, 64), (.n 978, 18), (.n 991, 5), (.n 1216, 88), (.n 1218, 4), (.n 1524, 5), (.n 1527, 57), (.n 1533, 0), (.n 1534, 28), (.n 1540, 57), (.n 1546, 0), (.n 1547, 16), (.n 1553, 57), (.n 1559, 0), (.n 1560, 11), (.n 1620, 57), (.n 1626, 0), (.n 1627, 9)] Data.core317.params Data.core317.name ([], []) Data.core317.body = some (⟨218559, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core317.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_317_0.1 rfl wsplit_317_0.2.2,
      ← blockR_eq ((Data.core317.body.drop 0).take 721), wsplit_317_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_317_721.1 rfl wsplit_317_721.2.2,
      ← blockR_eq ((Data.core317.body.drop 721).take 721), wsplit_317_721.2.1]
    rw [← blockR_eq (Data.core317.body.drop 1442), wsplit_317_1442]
    rfl
  exact wchkIdx_of_split (fn := Data.core317) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_318 : wchkIdx 318 = true := by
  have hb : blockB (wlookJ 318) (womLookJ 318) true [(.n 12, 704), (.n 14, 176), (.n 16, 4), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 280), (.n 26, 159), (.n 28, 159), (.n 30, 110), (.n 32, 20), (.n 212, 40), (.n 217, 0), (.n 218, 7), (.n 307, 64), (.n 311, 28), (.n 493, 40), (.n 498, 0), (.n 499, 4), (.n 559, 64), (.n 575, 32), (.n 757, 40), (.n 762, 0), (.n 763, 3), (.n 814, 64), (.n 830, 23), (.n 1012, 40), (.n 1017, 0), (.n 1018, 2), (.n 1064, 64), (.n 1080, 18), (.n 1160, 40), (.n 1165, 0), (.n 1166, 2), (.n 1208, 64), (.n 1224, 14), (.n 1237, 5), (.n 1434, 110), (.n 1436, 5), (.n 1783, 6), (.n 1786, 57), (.n 1792, 0), (.n 1793, 28), (.n 1799, 57), (.n 1805, 0), (.n 1806, 16), (.n 1812, 57), (.n 1818, 0), (.n 1819, 11), (.n 1885, 57), (.n 1891, 0), (.n 1892, 9), (.n 1898, 57), (.n 1904, 0), (.n 1905, 7)] Data.core318.params Data.core318.name ([], []) Data.core318.body = some (⟨245003, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core318.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_318_0.1 rfl wsplit_318_0.2.2,
      ← blockR_eq ((Data.core318.body.drop 0).take 619), wsplit_318_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_318_619.1 rfl wsplit_318_619.2.2,
      ← blockR_eq ((Data.core318.body.drop 619).take 619), wsplit_318_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_318_1238.1 rfl wsplit_318_1238.2.2,
      ← blockR_eq ((Data.core318.body.drop 1238).take 619), wsplit_318_1238.2.1]
    rw [← blockR_eq (Data.core318.body.drop 1857), wsplit_318_1857]
    rfl
  exact wchkIdx_of_split (fn := Data.core318) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_319 : wchkIdx 319 = true := by
  have hb : blockB (wlookJ 319) (womLookJ 319) true [(.n 12, 704), (.n 14, 176), (.n 16, 8), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 280), (.n 26, 153), (.n 28, 153), (.n 30, 110), (.n 32, 20), (.n 212, 40), (.n 217, 0), (.n 218, 7), (.n 307, 64), (.n 311, 28), (.n 493, 40), (.n 498, 0), (.n 499, 4), (.n 559, 64), (.n 575, 32), (.n 757, 40), (.n 762, 0), (.n 763, 3), (.n 814, 64), (.n 830, 23), (.n 1012, 40), (.n 1017, 0), (.n 1018, 2), (.n 1064, 64), (.n 1080, 18), (.n 1160, 40), (.n 1165, 0), (.n 1166, 2), (.n 1208, 64), (.n 1224, 14), (.n 1237, 5), (.n 1446, 110), (.n 1448, 5), (.n 1830, 6), (.n 1833, 57), (.n 1839, 0), (.n 1840, 28), (.n 1846, 57), (.n 1852, 0), (.n 1853, 16), (.n 1859, 57), (.n 1865, 0), (.n 1866, 11), (.n 1938, 57), (.n 1944, 0), (.n 1945, 9), (.n 1951, 57), (.n 1957, 0), (.n 1958, 7)] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨251389, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_319_0.1 rfl wsplit_319_0.2.2,
      ← blockR_eq ((Data.core319.body.drop 0).take 619), wsplit_319_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_319_619.1 rfl wsplit_319_619.2.2,
      ← blockR_eq ((Data.core319.body.drop 619).take 619), wsplit_319_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_319_1238.1 rfl wsplit_319_1238.2.2,
      ← blockR_eq ((Data.core319.body.drop 1238).take 619), wsplit_319_1238.2.1]
    rw [← blockR_eq (Data.core319.body.drop 1857), wsplit_319_1857]
    rfl
  exact wchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_320 : wchkIdx 320 = true := by
  have hb : blockB (wlookJ 320) (womLookJ 320) true [(.n 12, 704), (.n 14, 176), (.n 16, 16), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 280), (.n 26, 148), (.n 28, 148), (.n 30, 110), (.n 32, 20), (.n 212, 40), (.n 217, 0), (.n 218, 7), (.n 307, 64), (.n 311, 28), (.n 493, 40), (.n 498, 0), (.n 499, 4), (.n 559, 64), (.n 575, 32), (.n 757, 40), (.n 762, 0), (.n 763, 3), (.n 814, 64), (.n 830, 23), (.n 1012, 40), (.n 1017, 0), (.n 1018, 2), (.n 1064, 64), (.n 1080, 18), (.n 1160, 40), (.n 1165, 0), (.n 1166, 2), (.n 1208, 64), (.n 1224, 14), (.n 1237, 5), (.n 1458, 110), (.n 1460, 5), (.n 1877, 6), (.n 1880, 57), (.n 1886, 0), (.n 1887, 28), (.n 1893, 57), (.n 1899, 0), (.n 1900, 16), (.n 1906, 57), (.n 1912, 0), (.n 1913, 11), (.n 1991, 57), (.n 1997, 0), (.n 1998, 9), (.n 2004, 57), (.n 2010, 0), (.n 2011, 7)] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨257831, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_320_0.1 rfl wsplit_320_0.2.2,
      ← blockR_eq ((Data.core320.body.drop 0).take 619), wsplit_320_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_320_619.1 rfl wsplit_320_619.2.2,
      ← blockR_eq ((Data.core320.body.drop 619).take 619), wsplit_320_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_320_1238.1 rfl wsplit_320_1238.2.2,
      ← blockR_eq ((Data.core320.body.drop 1238).take 619), wsplit_320_1238.2.1]
    rw [← blockR_eq (Data.core320.body.drop 1857), wsplit_320_1857]
    rfl
  exact wchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_321 : wchkIdx 321 = true := by
  have hb : blockB (wlookJ 321) (womLookJ 321) true [(.n 12, 704), (.n 14, 176), (.n 16, 32), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 280), (.n 26, 154), (.n 28, 154), (.n 30, 110), (.n 32, 20), (.n 212, 45), (.n 217, 0), (.n 218, 8), (.n 307, 64), (.n 311, 28), (.n 493, 45), (.n 498, 0), (.n 499, 4), (.n 559, 64), (.n 575, 32), (.n 757, 45), (.n 762, 0), (.n 763, 3), (.n 814, 64), (.n 830, 23), (.n 1012, 45), (.n 1017, 0), (.n 1018, 3), (.n 1064, 64), (.n 1080, 18), (.n 1160, 45), (.n 1165, 0), (.n 1166, 2), (.n 1209, 64), (.n 1225, 15), (.n 1238, 5), (.n 1471, 110), (.n 1473, 5), (.n 1925, 6), (.n 1928, 57), (.n 1934, 0), (.n 1935, 28), (.n 1941, 57), (.n 1947, 0), (.n 1948, 16), (.n 1954, 57), (.n 1960, 0), (.n 1961, 11), (.n 2045, 57), (.n 2051, 0), (.n 2052, 9), (.n 2058, 57), (.n 2064, 0), (.n 2065, 7)] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨267474, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_321_0.1 rfl wsplit_321_0.2.2,
      ← blockR_eq ((Data.core321.body.drop 0).take 619), wsplit_321_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_321_619.1 rfl wsplit_321_619.2.2,
      ← blockR_eq ((Data.core321.body.drop 619).take 619), wsplit_321_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_321_1238.1 rfl wsplit_321_1238.2.2,
      ← blockR_eq ((Data.core321.body.drop 1238).take 619), wsplit_321_1238.2.1]
    rw [← blockR_eq (Data.core321.body.drop 1857), wsplit_321_1857]
    rfl
  exact wchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_322 : wchkIdx 322 = true := by
  have hb : blockB (wlookJ 322) (womLookJ 322) true [(.n 12, 768), (.n 14, 192), (.n 16, 4), (.n 18, 12), (.n 20, 26), (.n 22, 6), (.n 24, 336), (.n 26, 173), (.n 28, 173), (.n 30, 132), (.n 32, 24), (.n 212, 45), (.n 217, 0), (.n 218, 8), (.n 307, 64), (.n 311, 28), (.n 493, 45), (.n 498, 0), (.n 499, 5), (.n 559, 64), (.n 575, 32), (.n 757, 45), (.n 762, 0), (.n 763, 3), (.n 814, 64), (.n 830, 23), (.n 1012, 45), (.n 1017, 0), (.n 1018, 3), (.n 1064, 64), (.n 1080, 18), (.n 1262, 45), (.n 1267, 0), (.n 1268, 2), (.n 1311, 64), (.n 1327, 15), (.n 1407, 45), (.n 1412, 0), (.n 1413, 2), (.n 1453, 64), (.n 1469, 12), (.n 1482, 5), (.n 1687, 132), (.n 1689, 6), (.n 2189, 7), (.n 2192, 57), (.n 2198, 0), (.n 2199, 28), (.n 2205, 57), (.n 2211, 0), (.n 2212, 16), (.n 2218, 57), (.n 2224, 0), (.n 2225, 11), (.n 2315, 57), (.n 2321, 0), (.n 2322, 9), (.n 2328, 57), (.n 2334, 0), (.n 2335, 7), (.n 2377, 57), (.n 2383, 0), (.n 2384, 6)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨294016, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 542 542 wsplit_322_0.1 rfl wsplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 542), wsplit_322_0.2.1]
    rw [blockB_dropE _ _ _ 542 542 1084 wsplit_322_542.1 rfl wsplit_322_542.2.2,
      ← blockR_eq ((Data.core322.body.drop 542).take 542), wsplit_322_542.2.1]
    rw [blockB_dropE _ _ _ 1084 542 1626 wsplit_322_1084.1 rfl wsplit_322_1084.2.2,
      ← blockR_eq ((Data.core322.body.drop 1084).take 542), wsplit_322_1084.2.1]
    rw [blockB_dropE _ _ _ 1626 542 2168 wsplit_322_1626.1 rfl wsplit_322_1626.2.2,
      ← blockR_eq ((Data.core322.body.drop 1626).take 542), wsplit_322_1626.2.1]
    rw [blockB_dropE _ _ _ 2168 542 2710 wsplit_322_2168.1 rfl wsplit_322_2168.2.2,
      ← blockR_eq ((Data.core322.body.drop 2168).take 542), wsplit_322_2168.2.1]
    rw [← blockR_eq (Data.core322.body.drop 2710), wsplit_322_2710]
    rfl
  exact wchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem wchkIdx_all : ∀ j < 899, wchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact wchkIdx_19
  by_cases h1001 : j = 20
  · subst h1001; exact wchkIdx_20
  by_cases h1002 : j = 295
  · subst h1002; exact wchkIdx_295
  by_cases h1003 : j = 296
  · subst h1003; exact wchkIdx_296
  by_cases h1004 : j = 297
  · subst h1004; exact wchkIdx_297
  by_cases h1005 : j = 298
  · subst h1005; exact wchkIdx_298
  by_cases h1006 : j = 299
  · subst h1006; exact wchkIdx_299
  by_cases h1007 : j = 300
  · subst h1007; exact wchkIdx_300
  by_cases h1008 : j = 301
  · subst h1008; exact wchkIdx_301
  by_cases h1009 : j = 302
  · subst h1009; exact wchkIdx_302
  by_cases h1010 : j = 303
  · subst h1010; exact wchkIdx_303
  by_cases h1011 : j = 304
  · subst h1011; exact wchkIdx_304
  by_cases h1012 : j = 305
  · subst h1012; exact wchkIdx_305
  by_cases h1013 : j = 306
  · subst h1013; exact wchkIdx_306
  by_cases h1014 : j = 307
  · subst h1014; exact wchkIdx_307
  by_cases h1015 : j = 308
  · subst h1015; exact wchkIdx_308
  by_cases h1016 : j = 309
  · subst h1016; exact wchkIdx_309
  by_cases h1017 : j = 310
  · subst h1017; exact wchkIdx_310
  by_cases h1018 : j = 311
  · subst h1018; exact wchkIdx_311
  by_cases h1019 : j = 312
  · subst h1019; exact wchkIdx_312
  by_cases h1020 : j = 313
  · subst h1020; exact wchkIdx_313
  by_cases h1021 : j = 314
  · subst h1021; exact wchkIdx_314
  by_cases h1022 : j = 315
  · subst h1022; exact wchkIdx_315
  by_cases h1023 : j = 316
  · subst h1023; exact wchkIdx_316
  by_cases h1024 : j = 317
  · subst h1024; exact wchkIdx_317
  by_cases h1025 : j = 318
  · subst h1025; exact wchkIdx_318
  by_cases h1026 : j = 319
  · subst h1026; exact wchkIdx_319
  by_cases h1027 : j = 320
  · subst h1027; exact wchkIdx_320
  by_cases h1028 : j = 321
  · subst h1028; exact wchkIdx_321
  by_cases h1029 : j = 322
  · subst h1029; exact wchkIdx_322
  by_cases h0 : j < 10
  · exact wstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 17
  · exact wstaticRange_10.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact wstaticRange_17.get (by omega) (by omega)
  by_cases h3 : j < 43
  · exact wstaticRange_21.get (by omega) (by omega)
  by_cases h4 : j < 69
  · exact wstaticRange_43.get (by omega) (by omega)
  by_cases h5 : j < 95
  · exact wstaticRange_69.get (by omega) (by omega)
  by_cases h6 : j < 120
  · exact wstaticRange_95.get (by omega) (by omega)
  by_cases h7 : j < 147
  · exact wstaticRange_120.get (by omega) (by omega)
  by_cases h8 : j < 173
  · exact wstaticRange_147.get (by omega) (by omega)
  by_cases h9 : j < 198
  · exact wstaticRange_173.get (by omega) (by omega)
  by_cases h10 : j < 224
  · exact wstaticRange_198.get (by omega) (by omega)
  by_cases h11 : j < 248
  · exact wstaticRange_224.get (by omega) (by omega)
  by_cases h12 : j < 261
  · exact wstaticRange_248.get (by omega) (by omega)
  by_cases h13 : j < 285
  · exact wstaticRange_261.get (by omega) (by omega)
  by_cases h14 : j < 295
  · exact wstaticRange_285.get (by omega) (by omega)
  by_cases h15 : j < 348
  · exact wstaticRange_323.get (by omega) (by omega)
  by_cases h16 : j < 371
  · exact wstaticRange_348.get (by omega) (by omega)
  by_cases h17 : j < 391
  · exact wstaticRange_371.get (by omega) (by omega)
  by_cases h18 : j < 412
  · exact wstaticRange_391.get (by omega) (by omega)
  by_cases h19 : j < 432
  · exact wstaticRange_412.get (by omega) (by omega)
  by_cases h20 : j < 454
  · exact wstaticRange_432.get (by omega) (by omega)
  by_cases h21 : j < 477
  · exact wstaticRange_454.get (by omega) (by omega)
  by_cases h22 : j < 499
  · exact wstaticRange_477.get (by omega) (by omega)
  by_cases h23 : j < 520
  · exact wstaticRange_499.get (by omega) (by omega)
  by_cases h24 : j < 540
  · exact wstaticRange_520.get (by omega) (by omega)
  by_cases h25 : j < 561
  · exact wstaticRange_540.get (by omega) (by omega)
  by_cases h26 : j < 582
  · exact wstaticRange_561.get (by omega) (by omega)
  by_cases h27 : j < 603
  · exact wstaticRange_582.get (by omega) (by omega)
  by_cases h28 : j < 623
  · exact wstaticRange_603.get (by omega) (by omega)
  by_cases h29 : j < 643
  · exact wstaticRange_623.get (by omega) (by omega)
  by_cases h30 : j < 663
  · exact wstaticRange_643.get (by omega) (by omega)
  by_cases h31 : j < 683
  · exact wstaticRange_663.get (by omega) (by omega)
  by_cases h32 : j < 704
  · exact wstaticRange_683.get (by omega) (by omega)
  by_cases h33 : j < 725
  · exact wstaticRange_704.get (by omega) (by omega)
  by_cases h34 : j < 746
  · exact wstaticRange_725.get (by omega) (by omega)
  by_cases h35 : j < 767
  · exact wstaticRange_746.get (by omega) (by omega)
  by_cases h36 : j < 793
  · exact wstaticRange_767.get (by omega) (by omega)
  by_cases h37 : j < 817
  · exact wstaticRange_793.get (by omega) (by omega)
  by_cases h38 : j < 835
  · exact wstaticRange_817.get (by omega) (by omega)
  by_cases h39 : j < 847
  · exact wstaticRange_835.get (by omega) (by omega)
  by_cases h40 : j < 858
  · exact wstaticRange_847.get (by omega) (by omega)
  by_cases h41 : j < 865
  · exact wstaticRange_858.get (by omega) (by omega)
  by_cases h42 : j < 874
  · exact wstaticRange_865.get (by omega) (by omega)
  by_cases h43 : j < 880
  · exact wstaticRange_874.get (by omega) (by omega)
  by_cases h44 : j < 887
  · exact wstaticRange_880.get (by omega) (by omega)
  exact wstaticRange_887.get (by omega) (by omega)

end
end LeanVM.Guest
