/-
  LeanVM.Guest.B1.Tables.VtC.FForms2

  `Vt/FormsT2.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT2

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB02_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 7021) = σ (.n 3225) * vtBlockVal (σ (.n 15)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6262 [
    .atom (.load (.n 7011) (.n 14) 0),
    .atom (.const (.n 7012) (word 2 0 0)),
    .atom (.mul (.n 7013) (.n 7012) (.n 6907)),
    .atom (.load (.n 7014) (.n 14) 1),
    .atom (.mul (.n 7015) (.n 7014) (.n 7013)),
    .atom (.add (.n 7016) (.n 7011) (.n 7015)),
    .atom (.load (.n 7017) (.n 14) 2),
    .atom (.mul (.n 7018) (.n 7017) (.n 6918)),
    .atom (.add (.n 7019) (.n 7016) (.n 7018)),
    .atom (.add (.n 7020) (.n 15) (.n 7019)),
    .atom (.mul (.n 7021) (.n 3225) (.n 7020))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6262, a6263, a6264, a6265, a6266, a6267, a6268, a6269, a6270, a6271, a6272, -⟩ := hs
  have e6262 := tb_loadHolds_unique a6262 (hw 0 (by norm_num))
  have e6265 := tb_loadHolds_unique a6265 (hw 1 (by norm_num))
  have e6268 := tb_loadHolds_unique a6268 (hw 2 (by norm_num))
  have v6907 : σ (.n 6907) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 30) (by norm_num)).2.2.1
  have v6918 : σ (.n 6918) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 31) (by norm_num)).2.2.1
  have hB : σ (.n 7020) = vtBlockVal (σ (.n 15)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v6918, v6907, a6271, a6270, a6269, e6268, a6267, a6266, e6265, a6264, a6263, e6262]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6272, hB]

set_option maxRecDepth 10000 in
theorem vtB02_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 7055) = σ (.n 7021) + σ (.n 3244) * vtBlockVal (σ (.n 15)) W ev
      [[([], 4)], [([0], 1)], [([7], 2)], [([], 4)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 6273 [
    .atom (.load (.n 7022) (.n 14) 0),
    .atom (.const (.n 7023) (word 4 0 0)),
    .atom (.mul (.n 7024) (.n 7022) (.n 7023)),
    .atom (.load (.n 7025) (.n 14) 1),
    .atom (.mul (.n 7026) (.n 7025) (.n 6907)),
    .atom (.add (.n 7027) (.n 7024) (.n 7026)),
    .atom (.const (.n 7028) (word 2 0 0)),
    .atom (.mul (.n 7029) (.n 7028) (.n 7010)),
    .atom (.load (.n 7030) (.n 14) 2),
    .atom (.mul (.n 7031) (.n 7030) (.n 7029)),
    .atom (.add (.n 7032) (.n 7027) (.n 7031)),
    .atom (.load (.n 7033) (.n 14) 3),
    .atom (.const (.n 7034) (word 4 0 0)),
    .atom (.mul (.n 7035) (.n 7033) (.n 7034)),
    .atom (.add (.n 7036) (.n 7032) (.n 7035)),
    .atom (.load (.n 7037) (.n 14) 4),
    .atom (.mul (.n 7038) (.n 7037) (.n 6942)),
    .atom (.add (.n 7039) (.n 7036) (.n 7038)),
    .atom (.load (.n 7040) (.n 14) 5),
    .atom (.mul (.n 7041) (.n 7040) (.n 6953)),
    .atom (.add (.n 7042) (.n 7039) (.n 7041)),
    .atom (.load (.n 7043) (.n 14) 6),
    .atom (.mul (.n 7044) (.n 7043) (.n 6964)),
    .atom (.add (.n 7045) (.n 7042) (.n 7044)),
    .atom (.load (.n 7046) (.n 14) 7),
    .atom (.mul (.n 7047) (.n 7046) (.n 6975)),
    .atom (.add (.n 7048) (.n 7045) (.n 7047)),
    .atom (.load (.n 7049) (.n 14) 8),
    .atom (.const (.n 7050) (word 0 0 0)),
    .atom (.mul (.n 7051) (.n 7049) (.n 7050)),
    .atom (.add (.n 7052) (.n 7048) (.n 7051)),
    .atom (.add (.n 7053) (.n 15) (.n 7052)),
    .atom (.mul (.n 7054) (.n 3244) (.n 7053)),
    .atom (.add (.n 7055) (.n 7021) (.n 7054))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6273, a6274, a6275, a6276, a6277, a6278, a6279, a6280, a6281, a6282, a6283, a6284, a6285, a6286,
    a6287, a6288, a6289, a6290, a6291, a6292, a6293, a6294, a6295, a6296, a6297, a6298, a6299,
    a6300, a6301, a6302, a6303, a6304, a6305, a6306, -⟩ := hs
  have e6273 := tb_loadHolds_unique a6273 (hw 0 (by norm_num))
  have e6276 := tb_loadHolds_unique a6276 (hw 1 (by norm_num))
  have e6281 := tb_loadHolds_unique a6281 (hw 2 (by norm_num))
  have e6284 := tb_loadHolds_unique a6284 (hw 3 (by norm_num))
  have e6288 := tb_loadHolds_unique a6288 (hw 4 (by norm_num))
  have e6291 := tb_loadHolds_unique a6291 (hw 5 (by norm_num))
  have e6294 := tb_loadHolds_unique a6294 (hw 6 (by norm_num))
  have e6297 := tb_loadHolds_unique a6297 (hw 7 (by norm_num))
  have e6300 := tb_loadHolds_unique a6300 (hw 8 (by norm_num))
  have v6907 : σ (.n 6907) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 30) (by norm_num)).2.2.1
  have v6942 : σ (.n 6942) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 32) (by norm_num)).2.2.1
  have v6953 : σ (.n 6953) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 33) (by norm_num)).2.2.1
  have v6964 : σ (.n 6964) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 34) (by norm_num)).2.2.1
  have v6975 : σ (.n 6975) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 35) (by norm_num)).2.2.1
  have v7010 : σ (.n 7010) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 37) (by norm_num)).2.2.1
  have hB : σ (.n 7053) = vtBlockVal (σ (.n 15)) W ev [[([], 4)], [([0], 1)], [([7], 2)], [([], 4)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([], 0)]] := by
    simp only [v7010, v6975, v6964, v6953, v6942, v6907, a6304, a6303, a6302, a6301, e6300, a6299, a6298,
      e6297, a6296, a6295, e6294, a6293, a6292, e6291, a6290, a6289, e6288, a6287, a6286,
      a6285, e6284, a6283, a6282, e6281, a6280, a6279, a6278, a6277, e6276, a6275, a6274,
      e6273]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a6306, a6305, hB]

set_option maxRecDepth 10000 in
theorem vtB02_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 7079) = σ (.n 7055) + σ (.n 3263) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 2], 1)], [([6], 2)], [([3], 1)], [([4], 1)], [([5], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6307 [
    .atom (.load (.n 7056) (.n 14) 0),
    .atom (.const (.n 7057) (word 2 0 0)),
    .atom (.mul (.n 7058) (.n 7056) (.n 7057)),
    .atom (.mul (.n 7059) (.n 6918) (.n 6942)),
    .atom (.load (.n 7060) (.n 14) 1),
    .atom (.mul (.n 7061) (.n 7060) (.n 7059)),
    .atom (.add (.n 7062) (.n 7058) (.n 7061)),
    .atom (.const (.n 7063) (word 2 0 0)),
    .atom (.mul (.n 7064) (.n 7063) (.n 6999)),
    .atom (.load (.n 7065) (.n 14) 2),
    .atom (.mul (.n 7066) (.n 7065) (.n 7064)),
    .atom (.add (.n 7067) (.n 7062) (.n 7066)),
    .atom (.load (.n 7068) (.n 14) 3),
    .atom (.mul (.n 7069) (.n 7068) (.n 6953)),
    .atom (.add (.n 7070) (.n 7067) (.n 7069)),
    .atom (.load (.n 7071) (.n 14) 4),
    .atom (.mul (.n 7072) (.n 7071) (.n 6964)),
    .atom (.add (.n 7073) (.n 7070) (.n 7072)),
    .atom (.load (.n 7074) (.n 14) 5),
    .atom (.mul (.n 7075) (.n 7074) (.n 6975)),
    .atom (.add (.n 7076) (.n 7073) (.n 7075)),
    .atom (.add (.n 7077) (.n 15) (.n 7076)),
    .atom (.mul (.n 7078) (.n 3263) (.n 7077)),
    .atom (.add (.n 7079) (.n 7055) (.n 7078))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6307, a6308, a6309, a6310, a6311, a6312, a6313, a6314, a6315, a6316, a6317, a6318, a6319, a6320,
    a6321, a6322, a6323, a6324, a6325, a6326, a6327, a6328, a6329, a6330, -⟩ := hs
  have e6307 := tb_loadHolds_unique a6307 (hw 0 (by norm_num))
  have e6311 := tb_loadHolds_unique a6311 (hw 1 (by norm_num))
  have e6316 := tb_loadHolds_unique a6316 (hw 2 (by norm_num))
  have e6319 := tb_loadHolds_unique a6319 (hw 3 (by norm_num))
  have e6322 := tb_loadHolds_unique a6322 (hw 4 (by norm_num))
  have e6325 := tb_loadHolds_unique a6325 (hw 5 (by norm_num))
  have v6918 : σ (.n 6918) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 31) (by norm_num)).2.2.1
  have v6942 : σ (.n 6942) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 32) (by norm_num)).2.2.1
  have v6953 : σ (.n 6953) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 33) (by norm_num)).2.2.1
  have v6964 : σ (.n 6964) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 34) (by norm_num)).2.2.1
  have v6975 : σ (.n 6975) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 35) (by norm_num)).2.2.1
  have v6999 : σ (.n 6999) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 36) (by norm_num)).2.2.1
  have hB : σ (.n 7077) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 2], 1)], [([6], 2)], [([3], 1)], [([4], 1)], [([5], 1)]] := by
    simp only [v6999, v6975, v6964, v6953, v6942, v6918, a6328, a6327, a6326, e6325, a6324, a6323, e6322,
      a6321, a6320, e6319, a6318, a6317, e6316, a6315, a6314, a6313, a6312, e6311, a6310,
      a6309, a6308, e6307]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6330, a6329, hB]

set_option maxRecDepth 10000 in
theorem vtSide02F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 7079) =
      vtSideVal [σ (.n 3225), σ (.n 3244), σ (.n 3263)]
        (σ (.n 15)) W ev vtBTerms02 := by
  rw [vtB02_2F h hw hev, vtB02_1F h hw hev, vtB02_0F h hw hev]
  simp only [vtSideVal, vtBTerms02, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtB12_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 7089) = σ (.n 4639) * vtBlockVal (σ (.n 15)) W ev
      [[([], 1)], [([0], 1)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6332 [
    .atom (.load (.n 7081) (.n 14) 0),
    .atom (.load (.n 7082) (.n 14) 1),
    .atom (.mul (.n 7083) (.n 7082) (.n 6907)),
    .atom (.add (.n 7084) (.n 7081) (.n 7083)),
    .atom (.load (.n 7085) (.n 14) 2),
    .atom (.mul (.n 7086) (.n 7085) (.n 6918)),
    .atom (.add (.n 7087) (.n 7084) (.n 7086)),
    .atom (.add (.n 7088) (.n 15) (.n 7087)),
    .atom (.mul (.n 7089) (.n 4639) (.n 7088))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6332, a6333, a6334, a6335, a6336, a6337, a6338, a6339, a6340, -⟩ := hs
  have e6332 := tb_loadHolds_unique a6332 (hw 0 (by norm_num))
  have e6333 := tb_loadHolds_unique a6333 (hw 1 (by norm_num))
  have e6336 := tb_loadHolds_unique a6336 (hw 2 (by norm_num))
  have v6907 : σ (.n 6907) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 30) (by norm_num)).2.2.1
  have v6918 : σ (.n 6918) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 31) (by norm_num)).2.2.1
  have hB : σ (.n 7088) = vtBlockVal (σ (.n 15)) W ev [[([], 1)], [([0], 1)], [([1], 1)]] := by
    simp only [v6918, v6907, a6339, a6338, a6337, e6336, a6335, a6334, e6333, e6332]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
    ring
  rw [a6340, hB]

set_option maxRecDepth 10000 in
theorem vtB12_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 7121) = σ (.n 7089) + σ (.n 4646) * vtBlockVal (σ (.n 15)) W ev
      [[([], 4)], [([0], 1)], [([7], 1)], [([], 4)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 6341 [
    .atom (.load (.n 7090) (.n 14) 0),
    .atom (.const (.n 7091) (word 4 0 0)),
    .atom (.mul (.n 7092) (.n 7090) (.n 7091)),
    .atom (.load (.n 7093) (.n 14) 1),
    .atom (.mul (.n 7094) (.n 7093) (.n 6907)),
    .atom (.add (.n 7095) (.n 7092) (.n 7094)),
    .atom (.load (.n 7096) (.n 14) 2),
    .atom (.mul (.n 7097) (.n 7096) (.n 7010)),
    .atom (.add (.n 7098) (.n 7095) (.n 7097)),
    .atom (.load (.n 7099) (.n 14) 3),
    .atom (.const (.n 7100) (word 4 0 0)),
    .atom (.mul (.n 7101) (.n 7099) (.n 7100)),
    .atom (.add (.n 7102) (.n 7098) (.n 7101)),
    .atom (.load (.n 7103) (.n 14) 4),
    .atom (.mul (.n 7104) (.n 7103) (.n 6942)),
    .atom (.add (.n 7105) (.n 7102) (.n 7104)),
    .atom (.load (.n 7106) (.n 14) 5),
    .atom (.mul (.n 7107) (.n 7106) (.n 6953)),
    .atom (.add (.n 7108) (.n 7105) (.n 7107)),
    .atom (.load (.n 7109) (.n 14) 6),
    .atom (.mul (.n 7110) (.n 7109) (.n 6964)),
    .atom (.add (.n 7111) (.n 7108) (.n 7110)),
    .atom (.load (.n 7112) (.n 14) 7),
    .atom (.mul (.n 7113) (.n 7112) (.n 6975)),
    .atom (.add (.n 7114) (.n 7111) (.n 7113)),
    .atom (.load (.n 7115) (.n 14) 8),
    .atom (.const (.n 7116) (word 0 0 0)),
    .atom (.mul (.n 7117) (.n 7115) (.n 7116)),
    .atom (.add (.n 7118) (.n 7114) (.n 7117)),
    .atom (.add (.n 7119) (.n 15) (.n 7118)),
    .atom (.mul (.n 7120) (.n 4646) (.n 7119)),
    .atom (.add (.n 7121) (.n 7089) (.n 7120))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6341, a6342, a6343, a6344, a6345, a6346, a6347, a6348, a6349, a6350, a6351, a6352, a6353, a6354,
    a6355, a6356, a6357, a6358, a6359, a6360, a6361, a6362, a6363, a6364, a6365, a6366, a6367,
    a6368, a6369, a6370, a6371, a6372, -⟩ := hs
  have e6341 := tb_loadHolds_unique a6341 (hw 0 (by norm_num))
  have e6344 := tb_loadHolds_unique a6344 (hw 1 (by norm_num))
  have e6347 := tb_loadHolds_unique a6347 (hw 2 (by norm_num))
  have e6350 := tb_loadHolds_unique a6350 (hw 3 (by norm_num))
  have e6354 := tb_loadHolds_unique a6354 (hw 4 (by norm_num))
  have e6357 := tb_loadHolds_unique a6357 (hw 5 (by norm_num))
  have e6360 := tb_loadHolds_unique a6360 (hw 6 (by norm_num))
  have e6363 := tb_loadHolds_unique a6363 (hw 7 (by norm_num))
  have e6366 := tb_loadHolds_unique a6366 (hw 8 (by norm_num))
  have v6907 : σ (.n 6907) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 30) (by norm_num)).2.2.1
  have v6942 : σ (.n 6942) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 32) (by norm_num)).2.2.1
  have v6953 : σ (.n 6953) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 33) (by norm_num)).2.2.1
  have v6964 : σ (.n 6964) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 34) (by norm_num)).2.2.1
  have v6975 : σ (.n 6975) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 35) (by norm_num)).2.2.1
  have v7010 : σ (.n 7010) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 37) (by norm_num)).2.2.1
  have hB : σ (.n 7119) = vtBlockVal (σ (.n 15)) W ev [[([], 4)], [([0], 1)], [([7], 1)], [([], 4)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([], 0)]] := by
    simp only [v7010, v6975, v6964, v6953, v6942, v6907, a6370, a6369, a6368, a6367, e6366, a6365, a6364,
      e6363, a6362, a6361, e6360, a6359, a6358, e6357, a6356, a6355, e6354, a6353, a6352,
      a6351, e6350, a6349, a6348, e6347, a6346, a6345, e6344, a6343, a6342, e6341]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a6372, a6371, hB]

set_option maxRecDepth 10000 in
theorem vtB12_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 7143) = σ (.n 7121) + σ (.n 4653) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 2], 1)], [([6], 1)], [([3], 1)], [([4], 1)], [([5], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6373 [
    .atom (.load (.n 7122) (.n 14) 0),
    .atom (.const (.n 7123) (word 2 0 0)),
    .atom (.mul (.n 7124) (.n 7122) (.n 7123)),
    .atom (.mul (.n 7125) (.n 6918) (.n 6942)),
    .atom (.load (.n 7126) (.n 14) 1),
    .atom (.mul (.n 7127) (.n 7126) (.n 7125)),
    .atom (.add (.n 7128) (.n 7124) (.n 7127)),
    .atom (.load (.n 7129) (.n 14) 2),
    .atom (.mul (.n 7130) (.n 7129) (.n 6999)),
    .atom (.add (.n 7131) (.n 7128) (.n 7130)),
    .atom (.load (.n 7132) (.n 14) 3),
    .atom (.mul (.n 7133) (.n 7132) (.n 6953)),
    .atom (.add (.n 7134) (.n 7131) (.n 7133)),
    .atom (.load (.n 7135) (.n 14) 4),
    .atom (.mul (.n 7136) (.n 7135) (.n 6964)),
    .atom (.add (.n 7137) (.n 7134) (.n 7136)),
    .atom (.load (.n 7138) (.n 14) 5),
    .atom (.mul (.n 7139) (.n 7138) (.n 6975)),
    .atom (.add (.n 7140) (.n 7137) (.n 7139)),
    .atom (.add (.n 7141) (.n 15) (.n 7140)),
    .atom (.mul (.n 7142) (.n 4653) (.n 7141)),
    .atom (.add (.n 7143) (.n 7121) (.n 7142))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6373, a6374, a6375, a6376, a6377, a6378, a6379, a6380, a6381, a6382, a6383, a6384, a6385, a6386,
    a6387, a6388, a6389, a6390, a6391, a6392, a6393, a6394, -⟩ := hs
  have e6373 := tb_loadHolds_unique a6373 (hw 0 (by norm_num))
  have e6377 := tb_loadHolds_unique a6377 (hw 1 (by norm_num))
  have e6380 := tb_loadHolds_unique a6380 (hw 2 (by norm_num))
  have e6383 := tb_loadHolds_unique a6383 (hw 3 (by norm_num))
  have e6386 := tb_loadHolds_unique a6386 (hw 4 (by norm_num))
  have e6389 := tb_loadHolds_unique a6389 (hw 5 (by norm_num))
  have v6918 : σ (.n 6918) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 31) (by norm_num)).2.2.1
  have v6942 : σ (.n 6942) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 32) (by norm_num)).2.2.1
  have v6953 : σ (.n 6953) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 33) (by norm_num)).2.2.1
  have v6964 : σ (.n 6964) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 34) (by norm_num)).2.2.1
  have v6975 : σ (.n 6975) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 35) (by norm_num)).2.2.1
  have v6999 : σ (.n 6999) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 36) (by norm_num)).2.2.1
  have hB : σ (.n 7141) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 2], 1)], [([6], 1)], [([3], 1)], [([4], 1)], [([5], 1)]] := by
    simp only [v6999, v6975, v6964, v6953, v6942, v6918, a6392, a6391, a6390, e6389, a6388, a6387, e6386,
      a6385, a6384, e6383, a6382, a6381, e6380, a6379, a6378, e6377, a6376, a6375, a6374,
      e6373]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6394, a6393, hB]

set_option maxRecDepth 10000 in
theorem vtSide12F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 7143) =
      vtSideVal [σ (.n 4639), σ (.n 4646), σ (.n 4653)]
        (σ (.n 15)) W ev vtBTerms12 := by
  rw [vtB12_2F h hw hev, vtB12_1F h hw hev, vtB12_0F h hw hev]
  simp only [vtSideVal, vtBTerms12, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide22F {rd : Reader} {σ : Val} (h : VtF rd σ) {ev : ℕ → E}
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 7148) =
      vtSideVal [σ (.n 5078), σ (.n 5097)]
        (0) (fun _ ↦ 1) ev vtBTerms22 := by
  obtain ⟨_, hs⟩ := h.slice 6397 [
    .atom (.mul (.n 7146) (.n 5078) (.n 6999)),
    .atom (.mul (.n 7147) (.n 5097) (.n 7010)),
    .atom (.add (.n 7148) (.n 7146) (.n 7147))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6397, a6398, a6399, -⟩ := hs
  have v6999 : σ (.n 6999) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 36) (by norm_num)).2.2.1
  have v7010 : σ (.n 7010) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 37) (by norm_num)).2.2.1
  rw [a6399, a6397, a6398, v6999, v7010]
  simp only [vtSideVal, vtBTerms22, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero]

end
end LeanVM.Guest.B1.Tables
