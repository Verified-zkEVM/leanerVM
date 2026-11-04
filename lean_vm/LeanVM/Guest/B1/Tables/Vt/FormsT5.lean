/-
  LeanVM.Guest.B1.Tables.Vt.FormsT5

  Table 5's forms on the three sides: the blocks' selectors times their values.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsT5a
public import LeanVM.Guest.B1.Tables.Vt.FormsT5b

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtSide05 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6583) =
      vtSideVal [σ (.n 1143), σ (.n 1152), σ (.n 1161), σ (.n 1170), σ (.n 1179), σ (.n 1188), σ (.n 1197),
        σ (.n 1206), σ (.n 1215), σ (.n 1224), σ (.n 1233), σ (.n 1242), σ (.n 1251),
        σ (.n 1260), σ (.n 1269), σ (.n 1278), σ (.n 1287), σ (.n 1296), σ (.n 1305),
        σ (.n 1314), σ (.n 1323), σ (.n 1332), σ (.n 1341), σ (.n 1350), σ (.n 1359),
        σ (.n 1368), σ (.n 1377), σ (.n 1386)]
        (σ (.n 14)) W ev vtBTerms05 := by
  rw [vtB05_27 h hw hev, vtB05_26 h hw hev, vtB05_25 h hw hev, vtB05_24 h hw hev, vtB05_23 h hw hev,
    vtB05_22 h hw hev, vtB05_21 h hw hev, vtB05_20 h hw hev, vtB05_19 h hw hev,
    vtB05_18 h hw hev, vtB05_17 h hw hev, vtB05_16 h hw hev, vtB05_15 h hw hev,
    vtB05_14 h hw hev, vtB05_13 h hw hev, vtB05_12 h hw hev, vtB05_11 h hw hev,
    vtB05_10 h hw hev, vtB05_9 h hw hev, vtB05_8 h hw hev, vtB05_7 h hw hev, vtB05_6 h hw hev,
    vtB05_5 h hw hev, vtB05_4 h hw hev, vtB05_3 h hw hev, vtB05_2 h hw hev, vtB05_1 h hw hev,
    vtB05_0 h hw hev]
  simp only [vtSideVal, vtBTerms05, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide15 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6752) =
      vtSideVal [σ (.n 1998), σ (.n 2000), σ (.n 2002), σ (.n 2004), σ (.n 2006), σ (.n 2008), σ (.n 2010),
        σ (.n 2012), σ (.n 2014), σ (.n 2016), σ (.n 2018), σ (.n 2020), σ (.n 2022),
        σ (.n 2024), σ (.n 2026), σ (.n 2028), σ (.n 2030), σ (.n 2032), σ (.n 2034),
        σ (.n 2036), σ (.n 2038), σ (.n 2040), σ (.n 2042), σ (.n 2044), σ (.n 2046),
        σ (.n 2048), σ (.n 2050), σ (.n 2052)]
        (σ (.n 14)) W ev vtBTerms15 := by
  have hF0 : σ (.n 6583) =
      vtSideVal [σ (.n 1998), σ (.n 2000), σ (.n 2002), σ (.n 2004), σ (.n 2006), σ (.n 2008), σ (.n 2010),
        σ (.n 2012), σ (.n 2014), σ (.n 2016), σ (.n 2018), σ (.n 2020), σ (.n 2022),
        σ (.n 2024), σ (.n 2026), σ (.n 2028), σ (.n 2030), σ (.n 2032), σ (.n 2034),
        σ (.n 2036), σ (.n 2038), σ (.n 2040), σ (.n 2042), σ (.n 2044), σ (.n 2046),
        σ (.n 2048), σ (.n 2050), σ (.n 2052)]
        (σ (.n 14)) W ev vtBTerms05 := by
    rw [vtPullSels5 h]; exact vtSide05 h hw hev
  have a6184 := h.atomAt 6184 (.add (.n 6752) (.n 6583) (.n 6751)) (by decide +kernel)
  simp only [Atom.Holds] at a6184
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull5, ← hF0, a6184, vtD5_27 h hw hev, vtD5_26 h hw hev, vtD5_25 h hw hev, vtD5_24 h hw hev, vtD5_23 h hw hev,
    vtD5_22 h hw hev, vtD5_21 h hw hev, vtD5_20 h hw hev, vtD5_19 h hw hev, vtD5_18 h hw hev,
    vtD5_17 h hw hev, vtD5_16 h hw hev, vtD5_15 h hw hev, vtD5_14 h hw hev, vtD5_13 h hw hev,
    vtD5_12 h hw hev, vtD5_11 h hw hev, vtD5_10 h hw hev, vtD5_9 h hw hev, vtD5_8 h hw hev,
    vtD5_7 h hw hev, vtD5_6 h hw hev, vtD5_5 h hw hev, vtD5_4 h hw hev, vtD5_3 h hw hev,
    vtD5_2 h hw hev, vtD5_1 h hw hev, vtD5_0 h hw hev]
  simp only [vtDiffSum, vtDTerms5, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide25 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6807) =
      vtSideVal [σ (.n 2211), σ (.n 2220), σ (.n 2229), σ (.n 2238), σ (.n 2247), σ (.n 2256), σ (.n 2265),
        σ (.n 2274), σ (.n 2283), σ (.n 2292), σ (.n 2301), σ (.n 2310), σ (.n 2319),
        σ (.n 2328), σ (.n 2337), σ (.n 2346), σ (.n 2355), σ (.n 2364), σ (.n 2373),
        σ (.n 2382), σ (.n 2391), σ (.n 2400), σ (.n 2409), σ (.n 2418), σ (.n 2427),
        σ (.n 2436), σ (.n 2445)]
        (0) (fun _ ↦ 1) ev vtBTerms25 := by
  obtain ⟨_, hs⟩ := h.sliceAt 6187 [
    .atom (.mul (.n 6755) (.n 2211) (.n 5322)),
    .atom (.mul (.n 6756) (.n 2220) (.n 5333)),
    .atom (.add (.n 6757) (.n 6755) (.n 6756)),
    .atom (.mul (.n 6758) (.n 2229) (.n 5357)),
    .atom (.add (.n 6759) (.n 6757) (.n 6758)),
    .atom (.mul (.n 6760) (.n 2238) (.n 5368)),
    .atom (.add (.n 6761) (.n 6759) (.n 6760)),
    .atom (.mul (.n 6762) (.n 2247) (.n 5379)),
    .atom (.add (.n 6763) (.n 6761) (.n 6762)),
    .atom (.mul (.n 6764) (.n 2256) (.n 5390)),
    .atom (.add (.n 6765) (.n 6763) (.n 6764)),
    .atom (.mul (.n 6766) (.n 2265) (.n 5414)),
    .atom (.add (.n 6767) (.n 6765) (.n 6766)),
    .atom (.mul (.n 6768) (.n 2274) (.n 5425)),
    .atom (.add (.n 6769) (.n 6767) (.n 6768)),
    .atom (.mul (.n 6770) (.n 2283) (.n 5436)),
    .atom (.add (.n 6771) (.n 6769) (.n 6770)),
    .atom (.mul (.n 6772) (.n 2292) (.n 5447)),
    .atom (.add (.n 6773) (.n 6771) (.n 6772)),
    .atom (.mul (.n 6774) (.n 2301) (.n 5471)),
    .atom (.add (.n 6775) (.n 6773) (.n 6774)),
    .atom (.mul (.n 6776) (.n 2310) (.n 5482)),
    .atom (.add (.n 6777) (.n 6775) (.n 6776)),
    .atom (.mul (.n 6778) (.n 2319) (.n 5493)),
    .atom (.add (.n 6779) (.n 6777) (.n 6778)),
    .atom (.mul (.n 6780) (.n 2328) (.n 5504)),
    .atom (.add (.n 6781) (.n 6779) (.n 6780)),
    .atom (.mul (.n 6782) (.n 2337) (.n 5528)),
    .atom (.add (.n 6783) (.n 6781) (.n 6782)),
    .atom (.mul (.n 6784) (.n 2346) (.n 5539)),
    .atom (.add (.n 6785) (.n 6783) (.n 6784)),
    .atom (.mul (.n 6786) (.n 2355) (.n 5550)),
    .atom (.add (.n 6787) (.n 6785) (.n 6786)),
    .atom (.mul (.n 6788) (.n 2364) (.n 5561)),
    .atom (.add (.n 6789) (.n 6787) (.n 6788)),
    .atom (.mul (.n 6790) (.n 2373) (.n 5585)),
    .atom (.add (.n 6791) (.n 6789) (.n 6790)),
    .atom (.mul (.n 6792) (.n 2382) (.n 5596)),
    .atom (.add (.n 6793) (.n 6791) (.n 6792)),
    .atom (.mul (.n 6794) (.n 2391) (.n 5607)),
    .atom (.add (.n 6795) (.n 6793) (.n 6794)),
    .atom (.mul (.n 6796) (.n 2400) (.n 5618)),
    .atom (.add (.n 6797) (.n 6795) (.n 6796)),
    .atom (.mul (.n 6798) (.n 2409) (.n 5642)),
    .atom (.add (.n 6799) (.n 6797) (.n 6798)),
    .atom (.mul (.n 6800) (.n 2418) (.n 5653)),
    .atom (.add (.n 6801) (.n 6799) (.n 6800)),
    .atom (.mul (.n 6802) (.n 2427) (.n 5664)),
    .atom (.add (.n 6803) (.n 6801) (.n 6802)),
    .atom (.mul (.n 6804) (.n 2436) (.n 5675)),
    .atom (.add (.n 6805) (.n 6803) (.n 6804)),
    .atom (.mul (.n 6806) (.n 2445) (.n 5699)),
    .atom (.add (.n 6807) (.n 6805) (.n 6806))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6187, a6188, a6189, a6190, a6191, a6192, a6193, a6194, a6195, a6196, a6197, a6198, a6199, a6200,
    a6201, a6202, a6203, a6204, a6205, a6206, a6207, a6208, a6209, a6210, a6211, a6212, a6213,
    a6214, a6215, a6216, a6217, a6218, a6219, a6220, a6221, a6222, a6223, a6224, a6225, a6226,
    a6227, a6228, a6229, a6230, a6231, a6232, a6233, a6234, a6235, a6236, a6237, a6238, a6239, -⟩ := hs
  have v5322 : σ (.n 5322) = ev 63 := by
    rw [← hev 63 (by norm_num)]; exact (vt_eval h (k := 130) (by norm_num)).2.2
  have v5333 : σ (.n 5333) = ev 64 := by
    rw [← hev 64 (by norm_num)]; exact (vt_eval h (k := 131) (by norm_num)).2.2
  have v5357 : σ (.n 5357) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_eval h (k := 132) (by norm_num)).2.2
  have v5368 : σ (.n 5368) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_eval h (k := 133) (by norm_num)).2.2
  have v5379 : σ (.n 5379) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_eval h (k := 134) (by norm_num)).2.2
  have v5390 : σ (.n 5390) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_eval h (k := 135) (by norm_num)).2.2
  have v5414 : σ (.n 5414) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_eval h (k := 136) (by norm_num)).2.2
  have v5425 : σ (.n 5425) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_eval h (k := 137) (by norm_num)).2.2
  have v5436 : σ (.n 5436) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_eval h (k := 138) (by norm_num)).2.2
  have v5447 : σ (.n 5447) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_eval h (k := 139) (by norm_num)).2.2
  have v5471 : σ (.n 5471) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_eval h (k := 140) (by norm_num)).2.2
  have v5482 : σ (.n 5482) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_eval h (k := 141) (by norm_num)).2.2
  have v5493 : σ (.n 5493) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_eval h (k := 142) (by norm_num)).2.2
  have v5504 : σ (.n 5504) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_eval h (k := 143) (by norm_num)).2.2
  have v5528 : σ (.n 5528) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_eval h (k := 144) (by norm_num)).2.2
  have v5539 : σ (.n 5539) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_eval h (k := 145) (by norm_num)).2.2
  have v5550 : σ (.n 5550) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_eval h (k := 146) (by norm_num)).2.2
  have v5561 : σ (.n 5561) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_eval h (k := 147) (by norm_num)).2.2
  have v5585 : σ (.n 5585) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_eval h (k := 148) (by norm_num)).2.2
  have v5596 : σ (.n 5596) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_eval h (k := 149) (by norm_num)).2.2
  have v5607 : σ (.n 5607) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_eval h (k := 150) (by norm_num)).2.2
  have v5618 : σ (.n 5618) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_eval h (k := 151) (by norm_num)).2.2
  have v5642 : σ (.n 5642) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_eval h (k := 152) (by norm_num)).2.2
  have v5653 : σ (.n 5653) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_eval h (k := 153) (by norm_num)).2.2
  have v5664 : σ (.n 5664) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_eval h (k := 154) (by norm_num)).2.2
  have v5675 : σ (.n 5675) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_eval h (k := 155) (by norm_num)).2.2
  have v5699 : σ (.n 5699) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_eval h (k := 156) (by norm_num)).2.2
  rw [a6239, a6237, a6235, a6233, a6231, a6229, a6227, a6225, a6223, a6221, a6219, a6217, a6215, a6213,
    a6211, a6209, a6207, a6205, a6203, a6201, a6199, a6197, a6195, a6193, a6191, a6189, a6187,
    a6188, a6190, a6192, a6194, a6196, a6198, a6200, a6202, a6204, a6206, a6208, a6210, a6212,
    a6214, a6216, a6218, a6220, a6222, a6224, a6226, a6228, a6230, a6232, a6234, a6236, a6238,
    v5322, v5333, v5357, v5368, v5379, v5390, v5414, v5425, v5436, v5447, v5471, v5482, v5493,
    v5504, v5528, v5539, v5550, v5561, v5585, v5596, v5607, v5618, v5642, v5653, v5664, v5675,
    v5699]
  simp only [vtSideVal, vtBTerms25, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
