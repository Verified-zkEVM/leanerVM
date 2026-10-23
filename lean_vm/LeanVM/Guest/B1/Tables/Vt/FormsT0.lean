/-
  LeanVM.Guest.B1.Tables.Vt.FormsT0

  Table 0's forms on the three sides, from the guest's statements: each block's value from its
  baked terms, the table's form the blocks' selectors times their values.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsVal
public import LeanVM.Guest.B1.Tables.Vt.Pi

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB00_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6153) = σ (.n 3051) * vtBlockVal (σ (.n 15)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 5443 [
    .atom (.load (.n 6143) (.n 14) 0),
    .atom (.const (.n 6144) (word 2 0 0)),
    .atom (.mul (.n 6145) (.n 6144) (.n 5949)),
    .atom (.load (.n 6146) (.n 14) 1),
    .atom (.mul (.n 6147) (.n 6146) (.n 6145)),
    .atom (.add (.n 6148) (.n 6143) (.n 6147)),
    .atom (.load (.n 6149) (.n 14) 2),
    .atom (.mul (.n 6150) (.n 6149) (.n 5960)),
    .atom (.add (.n 6151) (.n 6148) (.n 6150)),
    .atom (.add (.n 6152) (.n 15) (.n 6151)),
    .atom (.mul (.n 6153) (.n 3051) (.n 6152))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5443, a5444, a5445, a5446, a5447, a5448, a5449, a5450, a5451, a5452, a5453, -⟩ := hs
  have e5443 := tb_loadHolds_unique a5443 (hw 0 (by norm_num))
  have e5446 := tb_loadHolds_unique a5446 (hw 1 (by norm_num))
  have e5449 := tb_loadHolds_unique a5449 (hw 2 (by norm_num))
  have v5949 : σ (.n 5949) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 0) (by norm_num)).2.2.1
  have v5960 : σ (.n 5960) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2.1
  have hB : σ (.n 6152) = vtBlockVal (σ (.n 15)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v5960, v5949, a5452, a5451, a5450, e5449, a5448, a5447, e5446, a5445, a5444, e5443]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5453, hB]

set_option maxRecDepth 10000 in
theorem vtB00_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6186) = σ (.n 6153) + σ (.n 3066) * vtBlockVal (σ (.n 15)) W ev
      [[([], 4)], [([0], 1)], [([14], 2)], [([], 1)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 5454 [
    .atom (.load (.n 6154) (.n 14) 0),
    .atom (.const (.n 6155) (word 4 0 0)),
    .atom (.mul (.n 6156) (.n 6154) (.n 6155)),
    .atom (.load (.n 6157) (.n 14) 1),
    .atom (.mul (.n 6158) (.n 6157) (.n 5949)),
    .atom (.add (.n 6159) (.n 6156) (.n 6158)),
    .atom (.const (.n 6160) (word 2 0 0)),
    .atom (.mul (.n 6161) (.n 6160) (.n 6142)),
    .atom (.load (.n 6162) (.n 14) 2),
    .atom (.mul (.n 6163) (.n 6162) (.n 6161)),
    .atom (.add (.n 6164) (.n 6159) (.n 6163)),
    .atom (.load (.n 6165) (.n 14) 3),
    .atom (.add (.n 6166) (.n 6164) (.n 6165)),
    .atom (.load (.n 6167) (.n 14) 4),
    .atom (.mul (.n 6168) (.n 6167) (.n 5971)),
    .atom (.add (.n 6169) (.n 6166) (.n 6168)),
    .atom (.load (.n 6170) (.n 14) 5),
    .atom (.mul (.n 6171) (.n 6170) (.n 5982)),
    .atom (.add (.n 6172) (.n 6169) (.n 6171)),
    .atom (.load (.n 6173) (.n 14) 6),
    .atom (.mul (.n 6174) (.n 6173) (.n 6006)),
    .atom (.add (.n 6175) (.n 6172) (.n 6174)),
    .atom (.load (.n 6176) (.n 14) 7),
    .atom (.const (.n 6177) (word 0 0 0)),
    .atom (.mul (.n 6178) (.n 6176) (.n 6177)),
    .atom (.add (.n 6179) (.n 6175) (.n 6178)),
    .atom (.load (.n 6180) (.n 14) 8),
    .atom (.const (.n 6181) (word 0 0 0)),
    .atom (.mul (.n 6182) (.n 6180) (.n 6181)),
    .atom (.add (.n 6183) (.n 6179) (.n 6182)),
    .atom (.add (.n 6184) (.n 15) (.n 6183)),
    .atom (.mul (.n 6185) (.n 3066) (.n 6184)),
    .atom (.add (.n 6186) (.n 6153) (.n 6185))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5454, a5455, a5456, a5457, a5458, a5459, a5460, a5461, a5462, a5463, a5464, a5465, a5466, a5467,
    a5468, a5469, a5470, a5471, a5472, a5473, a5474, a5475, a5476, a5477, a5478, a5479, a5480,
    a5481, a5482, a5483, a5484, a5485, a5486, -⟩ := hs
  have e5454 := tb_loadHolds_unique a5454 (hw 0 (by norm_num))
  have e5457 := tb_loadHolds_unique a5457 (hw 1 (by norm_num))
  have e5462 := tb_loadHolds_unique a5462 (hw 2 (by norm_num))
  have e5465 := tb_loadHolds_unique a5465 (hw 3 (by norm_num))
  have e5467 := tb_loadHolds_unique a5467 (hw 4 (by norm_num))
  have e5470 := tb_loadHolds_unique a5470 (hw 5 (by norm_num))
  have e5473 := tb_loadHolds_unique a5473 (hw 6 (by norm_num))
  have e5476 := tb_loadHolds_unique a5476 (hw 7 (by norm_num))
  have e5480 := tb_loadHolds_unique a5480 (hw 8 (by norm_num))
  have v5949 : σ (.n 5949) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 0) (by norm_num)).2.2.1
  have v5971 : σ (.n 5971) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 2) (by norm_num)).2.2.1
  have v5982 : σ (.n 5982) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 3) (by norm_num)).2.2.1
  have v6006 : σ (.n 6006) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 4) (by norm_num)).2.2.1
  have v6142 : σ (.n 6142) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 14) (by norm_num)).2.2.1
  have hB : σ (.n 6184) = vtBlockVal (σ (.n 15)) W ev [[([], 4)], [([0], 1)], [([14], 2)], [([], 1)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v6142, v6006, v5982, v5971, v5949, a5484, a5483, a5482, a5481, e5480, a5479, a5478, a5477,
      e5476, a5475, a5474, e5473, a5472, a5471, e5470, a5469, a5468, e5467, a5466, e5465,
      a5464, a5463, e5462, a5461, a5460, a5459, a5458, e5457, a5456, a5455, e5454]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5486, a5485, hB]

set_option maxRecDepth 10000 in
theorem vtB00_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6210) = σ (.n 6186) + σ (.n 3081) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 2], 1)], [([11], 2)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 5487 [
    .atom (.load (.n 6187) (.n 14) 0),
    .atom (.const (.n 6188) (word 2 0 0)),
    .atom (.mul (.n 6189) (.n 6187) (.n 6188)),
    .atom (.mul (.n 6190) (.n 5960) (.n 5971)),
    .atom (.load (.n 6191) (.n 14) 1),
    .atom (.mul (.n 6192) (.n 6191) (.n 6190)),
    .atom (.add (.n 6193) (.n 6189) (.n 6192)),
    .atom (.const (.n 6194) (word 2 0 0)),
    .atom (.mul (.n 6195) (.n 6194) (.n 6096)),
    .atom (.load (.n 6196) (.n 14) 2),
    .atom (.mul (.n 6197) (.n 6196) (.n 6195)),
    .atom (.add (.n 6198) (.n 6193) (.n 6197)),
    .atom (.load (.n 6199) (.n 14) 3),
    .atom (.mul (.n 6200) (.n 6199) (.n 6017)),
    .atom (.add (.n 6201) (.n 6198) (.n 6200)),
    .atom (.load (.n 6202) (.n 14) 4),
    .atom (.mul (.n 6203) (.n 6202) (.n 6028)),
    .atom (.add (.n 6204) (.n 6201) (.n 6203)),
    .atom (.load (.n 6205) (.n 14) 5),
    .atom (.mul (.n 6206) (.n 6205) (.n 6039)),
    .atom (.add (.n 6207) (.n 6204) (.n 6206)),
    .atom (.add (.n 6208) (.n 15) (.n 6207)),
    .atom (.mul (.n 6209) (.n 3081) (.n 6208)),
    .atom (.add (.n 6210) (.n 6186) (.n 6209))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5487, a5488, a5489, a5490, a5491, a5492, a5493, a5494, a5495, a5496, a5497, a5498, a5499, a5500,
    a5501, a5502, a5503, a5504, a5505, a5506, a5507, a5508, a5509, a5510, -⟩ := hs
  have e5487 := tb_loadHolds_unique a5487 (hw 0 (by norm_num))
  have e5491 := tb_loadHolds_unique a5491 (hw 1 (by norm_num))
  have e5496 := tb_loadHolds_unique a5496 (hw 2 (by norm_num))
  have e5499 := tb_loadHolds_unique a5499 (hw 3 (by norm_num))
  have e5502 := tb_loadHolds_unique a5502 (hw 4 (by norm_num))
  have e5505 := tb_loadHolds_unique a5505 (hw 5 (by norm_num))
  have v5960 : σ (.n 5960) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2.1
  have v5971 : σ (.n 5971) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 2) (by norm_num)).2.2.1
  have v6017 : σ (.n 6017) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 5) (by norm_num)).2.2.1
  have v6028 : σ (.n 6028) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 6) (by norm_num)).2.2.1
  have v6039 : σ (.n 6039) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 7) (by norm_num)).2.2.1
  have v6096 : σ (.n 6096) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 11) (by norm_num)).2.2.1
  have hB : σ (.n 6208) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 2], 1)], [([11], 2)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
    simp only [v6096, v6039, v6028, v6017, v5971, v5960, a5508, a5507, a5506, e5505, a5504, a5503, e5502,
      a5501, a5500, e5499, a5498, a5497, e5496, a5495, a5494, a5493, a5492, e5491, a5490,
      a5489, a5488, e5487]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5510, a5509, hB]

set_option maxRecDepth 10000 in
theorem vtB00_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6234) = σ (.n 6210) + σ (.n 3096) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 3], 1)], [([12], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 5511 [
    .atom (.load (.n 6211) (.n 14) 0),
    .atom (.const (.n 6212) (word 2 0 0)),
    .atom (.mul (.n 6213) (.n 6211) (.n 6212)),
    .atom (.mul (.n 6214) (.n 5960) (.n 5982)),
    .atom (.load (.n 6215) (.n 14) 1),
    .atom (.mul (.n 6216) (.n 6215) (.n 6214)),
    .atom (.add (.n 6217) (.n 6213) (.n 6216)),
    .atom (.const (.n 6218) (word 2 0 0)),
    .atom (.mul (.n 6219) (.n 6218) (.n 6120)),
    .atom (.load (.n 6220) (.n 14) 2),
    .atom (.mul (.n 6221) (.n 6220) (.n 6219)),
    .atom (.add (.n 6222) (.n 6217) (.n 6221)),
    .atom (.load (.n 6223) (.n 14) 3),
    .atom (.mul (.n 6224) (.n 6223) (.n 6063)),
    .atom (.add (.n 6225) (.n 6222) (.n 6224)),
    .atom (.load (.n 6226) (.n 14) 4),
    .atom (.mul (.n 6227) (.n 6226) (.n 6074)),
    .atom (.add (.n 6228) (.n 6225) (.n 6227)),
    .atom (.load (.n 6229) (.n 14) 5),
    .atom (.mul (.n 6230) (.n 6229) (.n 6085)),
    .atom (.add (.n 6231) (.n 6228) (.n 6230)),
    .atom (.add (.n 6232) (.n 15) (.n 6231)),
    .atom (.mul (.n 6233) (.n 3096) (.n 6232)),
    .atom (.add (.n 6234) (.n 6210) (.n 6233))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5511, a5512, a5513, a5514, a5515, a5516, a5517, a5518, a5519, a5520, a5521, a5522, a5523, a5524,
    a5525, a5526, a5527, a5528, a5529, a5530, a5531, a5532, a5533, a5534, -⟩ := hs
  have e5511 := tb_loadHolds_unique a5511 (hw 0 (by norm_num))
  have e5515 := tb_loadHolds_unique a5515 (hw 1 (by norm_num))
  have e5520 := tb_loadHolds_unique a5520 (hw 2 (by norm_num))
  have e5523 := tb_loadHolds_unique a5523 (hw 3 (by norm_num))
  have e5526 := tb_loadHolds_unique a5526 (hw 4 (by norm_num))
  have e5529 := tb_loadHolds_unique a5529 (hw 5 (by norm_num))
  have v5960 : σ (.n 5960) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2.1
  have v5982 : σ (.n 5982) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 3) (by norm_num)).2.2.1
  have v6063 : σ (.n 6063) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 8) (by norm_num)).2.2.1
  have v6074 : σ (.n 6074) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 9) (by norm_num)).2.2.1
  have v6085 : σ (.n 6085) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 10) (by norm_num)).2.2.1
  have v6120 : σ (.n 6120) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 12) (by norm_num)).2.2.1
  have hB : σ (.n 6232) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 3], 1)], [([12], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
    simp only [v6120, v6085, v6074, v6063, v5982, v5960, a5532, a5531, a5530, e5529, a5528, a5527, e5526,
      a5525, a5524, e5523, a5522, a5521, e5520, a5519, a5518, a5517, a5516, e5515, a5514,
      a5513, a5512, e5511]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5534, a5533, hB]

set_option maxRecDepth 10000 in
theorem vtB00_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6261) = σ (.n 6234) + σ (.n 3111) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 4], 1)], [([13], 2)], [([5], 1), ([8], 1)], [([6], 1), ([9], 1)], [([7], 1), ([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 5535 [
    .atom (.load (.n 6235) (.n 14) 0),
    .atom (.const (.n 6236) (word 2 0 0)),
    .atom (.mul (.n 6237) (.n 6235) (.n 6236)),
    .atom (.mul (.n 6238) (.n 5960) (.n 6006)),
    .atom (.load (.n 6239) (.n 14) 1),
    .atom (.mul (.n 6240) (.n 6239) (.n 6238)),
    .atom (.add (.n 6241) (.n 6237) (.n 6240)),
    .atom (.const (.n 6242) (word 2 0 0)),
    .atom (.mul (.n 6243) (.n 6242) (.n 6131)),
    .atom (.load (.n 6244) (.n 14) 2),
    .atom (.mul (.n 6245) (.n 6244) (.n 6243)),
    .atom (.add (.n 6246) (.n 6241) (.n 6245)),
    .atom (.add (.n 6247) (.n 6017) (.n 6063)),
    .atom (.load (.n 6248) (.n 14) 3),
    .atom (.mul (.n 6249) (.n 6248) (.n 6247)),
    .atom (.add (.n 6250) (.n 6246) (.n 6249)),
    .atom (.add (.n 6251) (.n 6028) (.n 6074)),
    .atom (.load (.n 6252) (.n 14) 4),
    .atom (.mul (.n 6253) (.n 6252) (.n 6251)),
    .atom (.add (.n 6254) (.n 6250) (.n 6253)),
    .atom (.add (.n 6255) (.n 6039) (.n 6085)),
    .atom (.load (.n 6256) (.n 14) 5),
    .atom (.mul (.n 6257) (.n 6256) (.n 6255)),
    .atom (.add (.n 6258) (.n 6254) (.n 6257)),
    .atom (.add (.n 6259) (.n 15) (.n 6258)),
    .atom (.mul (.n 6260) (.n 3111) (.n 6259)),
    .atom (.add (.n 6261) (.n 6234) (.n 6260))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5535, a5536, a5537, a5538, a5539, a5540, a5541, a5542, a5543, a5544, a5545, a5546, a5547, a5548,
    a5549, a5550, a5551, a5552, a5553, a5554, a5555, a5556, a5557, a5558, a5559, a5560, a5561, -⟩ := hs
  have e5535 := tb_loadHolds_unique a5535 (hw 0 (by norm_num))
  have e5539 := tb_loadHolds_unique a5539 (hw 1 (by norm_num))
  have e5544 := tb_loadHolds_unique a5544 (hw 2 (by norm_num))
  have e5548 := tb_loadHolds_unique a5548 (hw 3 (by norm_num))
  have e5552 := tb_loadHolds_unique a5552 (hw 4 (by norm_num))
  have e5556 := tb_loadHolds_unique a5556 (hw 5 (by norm_num))
  have v5960 : σ (.n 5960) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2.1
  have v6006 : σ (.n 6006) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 4) (by norm_num)).2.2.1
  have v6017 : σ (.n 6017) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 5) (by norm_num)).2.2.1
  have v6028 : σ (.n 6028) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 6) (by norm_num)).2.2.1
  have v6039 : σ (.n 6039) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 7) (by norm_num)).2.2.1
  have v6063 : σ (.n 6063) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 8) (by norm_num)).2.2.1
  have v6074 : σ (.n 6074) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 9) (by norm_num)).2.2.1
  have v6085 : σ (.n 6085) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 10) (by norm_num)).2.2.1
  have v6131 : σ (.n 6131) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 13) (by norm_num)).2.2.1
  have hB : σ (.n 6259) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 4], 1)], [([13], 2)], [([5], 1), ([8], 1)], [([6], 1), ([9], 1)], [([7], 1), ([10], 1)]] := by
    simp only [v6131, v6085, v6074, v6063, v6039, v6028, v6017, v6006, v5960, a5559, a5558, a5557, e5556,
      a5555, a5554, a5553, e5552, a5551, a5550, a5549, e5548, a5547, a5546, a5545, e5544,
      a5543, a5542, a5541, a5540, e5539, a5538, a5537, a5536, e5535]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5561, a5560, hB]

set_option maxRecDepth 10000 in
theorem vtSide00 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6261) =
      vtSideVal [σ (.n 3051), σ (.n 3066), σ (.n 3081), σ (.n 3096), σ (.n 3111)]
        (σ (.n 15)) W ev vtBTerms00 := by
  rw [vtB00_4 h hw hev, vtB00_3 h hw hev, vtB00_2 h hw hev, vtB00_1 h hw hev, vtB00_0 h hw hev]
  simp only [vtSideVal, vtBTerms00, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtB10_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6271) = σ (.n 4569) * vtBlockVal (σ (.n 15)) W ev
      [[([], 1)], [([0], 1)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 5563 [
    .atom (.load (.n 6263) (.n 14) 0),
    .atom (.load (.n 6264) (.n 14) 1),
    .atom (.mul (.n 6265) (.n 6264) (.n 5949)),
    .atom (.add (.n 6266) (.n 6263) (.n 6265)),
    .atom (.load (.n 6267) (.n 14) 2),
    .atom (.mul (.n 6268) (.n 6267) (.n 5960)),
    .atom (.add (.n 6269) (.n 6266) (.n 6268)),
    .atom (.add (.n 6270) (.n 15) (.n 6269)),
    .atom (.mul (.n 6271) (.n 4569) (.n 6270))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5563, a5564, a5565, a5566, a5567, a5568, a5569, a5570, a5571, -⟩ := hs
  have e5563 := tb_loadHolds_unique a5563 (hw 0 (by norm_num))
  have e5564 := tb_loadHolds_unique a5564 (hw 1 (by norm_num))
  have e5567 := tb_loadHolds_unique a5567 (hw 2 (by norm_num))
  have v5949 : σ (.n 5949) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 0) (by norm_num)).2.2.1
  have v5960 : σ (.n 5960) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2.1
  have hB : σ (.n 6270) = vtBlockVal (σ (.n 15)) W ev [[([], 1)], [([0], 1)], [([1], 1)]] := by
    simp only [v5960, v5949, a5570, a5569, a5568, e5567, a5566, a5565, e5564, e5563]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
    ring
  rw [a5571, hB]

set_option maxRecDepth 10000 in
theorem vtB10_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6302) = σ (.n 6271) + σ (.n 4576) * vtBlockVal (σ (.n 15)) W ev
      [[([], 4)], [([0], 1)], [([14], 1)], [([], 1)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 5572 [
    .atom (.load (.n 6272) (.n 14) 0),
    .atom (.const (.n 6273) (word 4 0 0)),
    .atom (.mul (.n 6274) (.n 6272) (.n 6273)),
    .atom (.load (.n 6275) (.n 14) 1),
    .atom (.mul (.n 6276) (.n 6275) (.n 5949)),
    .atom (.add (.n 6277) (.n 6274) (.n 6276)),
    .atom (.load (.n 6278) (.n 14) 2),
    .atom (.mul (.n 6279) (.n 6278) (.n 6142)),
    .atom (.add (.n 6280) (.n 6277) (.n 6279)),
    .atom (.load (.n 6281) (.n 14) 3),
    .atom (.add (.n 6282) (.n 6280) (.n 6281)),
    .atom (.load (.n 6283) (.n 14) 4),
    .atom (.mul (.n 6284) (.n 6283) (.n 5971)),
    .atom (.add (.n 6285) (.n 6282) (.n 6284)),
    .atom (.load (.n 6286) (.n 14) 5),
    .atom (.mul (.n 6287) (.n 6286) (.n 5982)),
    .atom (.add (.n 6288) (.n 6285) (.n 6287)),
    .atom (.load (.n 6289) (.n 14) 6),
    .atom (.mul (.n 6290) (.n 6289) (.n 6006)),
    .atom (.add (.n 6291) (.n 6288) (.n 6290)),
    .atom (.load (.n 6292) (.n 14) 7),
    .atom (.const (.n 6293) (word 0 0 0)),
    .atom (.mul (.n 6294) (.n 6292) (.n 6293)),
    .atom (.add (.n 6295) (.n 6291) (.n 6294)),
    .atom (.load (.n 6296) (.n 14) 8),
    .atom (.const (.n 6297) (word 0 0 0)),
    .atom (.mul (.n 6298) (.n 6296) (.n 6297)),
    .atom (.add (.n 6299) (.n 6295) (.n 6298)),
    .atom (.add (.n 6300) (.n 15) (.n 6299)),
    .atom (.mul (.n 6301) (.n 4576) (.n 6300)),
    .atom (.add (.n 6302) (.n 6271) (.n 6301))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5572, a5573, a5574, a5575, a5576, a5577, a5578, a5579, a5580, a5581, a5582, a5583, a5584, a5585,
    a5586, a5587, a5588, a5589, a5590, a5591, a5592, a5593, a5594, a5595, a5596, a5597, a5598,
    a5599, a5600, a5601, a5602, -⟩ := hs
  have e5572 := tb_loadHolds_unique a5572 (hw 0 (by norm_num))
  have e5575 := tb_loadHolds_unique a5575 (hw 1 (by norm_num))
  have e5578 := tb_loadHolds_unique a5578 (hw 2 (by norm_num))
  have e5581 := tb_loadHolds_unique a5581 (hw 3 (by norm_num))
  have e5583 := tb_loadHolds_unique a5583 (hw 4 (by norm_num))
  have e5586 := tb_loadHolds_unique a5586 (hw 5 (by norm_num))
  have e5589 := tb_loadHolds_unique a5589 (hw 6 (by norm_num))
  have e5592 := tb_loadHolds_unique a5592 (hw 7 (by norm_num))
  have e5596 := tb_loadHolds_unique a5596 (hw 8 (by norm_num))
  have v5949 : σ (.n 5949) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 0) (by norm_num)).2.2.1
  have v5971 : σ (.n 5971) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 2) (by norm_num)).2.2.1
  have v5982 : σ (.n 5982) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 3) (by norm_num)).2.2.1
  have v6006 : σ (.n 6006) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 4) (by norm_num)).2.2.1
  have v6142 : σ (.n 6142) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 14) (by norm_num)).2.2.1
  have hB : σ (.n 6300) = vtBlockVal (σ (.n 15)) W ev [[([], 4)], [([0], 1)], [([14], 1)], [([], 1)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v6142, v6006, v5982, v5971, v5949, a5600, a5599, a5598, a5597, e5596, a5595, a5594, a5593,
      e5592, a5591, a5590, e5589, a5588, a5587, e5586, a5585, a5584, e5583, a5582, e5581,
      a5580, a5579, e5578, a5577, a5576, e5575, a5574, a5573, e5572]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5602, a5601, hB]

set_option maxRecDepth 10000 in
theorem vtB10_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6324) = σ (.n 6302) + σ (.n 4583) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 2], 1)], [([11], 1)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 5603 [
    .atom (.load (.n 6303) (.n 14) 0),
    .atom (.const (.n 6304) (word 2 0 0)),
    .atom (.mul (.n 6305) (.n 6303) (.n 6304)),
    .atom (.mul (.n 6306) (.n 5960) (.n 5971)),
    .atom (.load (.n 6307) (.n 14) 1),
    .atom (.mul (.n 6308) (.n 6307) (.n 6306)),
    .atom (.add (.n 6309) (.n 6305) (.n 6308)),
    .atom (.load (.n 6310) (.n 14) 2),
    .atom (.mul (.n 6311) (.n 6310) (.n 6096)),
    .atom (.add (.n 6312) (.n 6309) (.n 6311)),
    .atom (.load (.n 6313) (.n 14) 3),
    .atom (.mul (.n 6314) (.n 6313) (.n 6017)),
    .atom (.add (.n 6315) (.n 6312) (.n 6314)),
    .atom (.load (.n 6316) (.n 14) 4),
    .atom (.mul (.n 6317) (.n 6316) (.n 6028)),
    .atom (.add (.n 6318) (.n 6315) (.n 6317)),
    .atom (.load (.n 6319) (.n 14) 5),
    .atom (.mul (.n 6320) (.n 6319) (.n 6039)),
    .atom (.add (.n 6321) (.n 6318) (.n 6320)),
    .atom (.add (.n 6322) (.n 15) (.n 6321)),
    .atom (.mul (.n 6323) (.n 4583) (.n 6322)),
    .atom (.add (.n 6324) (.n 6302) (.n 6323))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5603, a5604, a5605, a5606, a5607, a5608, a5609, a5610, a5611, a5612, a5613, a5614, a5615, a5616,
    a5617, a5618, a5619, a5620, a5621, a5622, a5623, a5624, -⟩ := hs
  have e5603 := tb_loadHolds_unique a5603 (hw 0 (by norm_num))
  have e5607 := tb_loadHolds_unique a5607 (hw 1 (by norm_num))
  have e5610 := tb_loadHolds_unique a5610 (hw 2 (by norm_num))
  have e5613 := tb_loadHolds_unique a5613 (hw 3 (by norm_num))
  have e5616 := tb_loadHolds_unique a5616 (hw 4 (by norm_num))
  have e5619 := tb_loadHolds_unique a5619 (hw 5 (by norm_num))
  have v5960 : σ (.n 5960) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2.1
  have v5971 : σ (.n 5971) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 2) (by norm_num)).2.2.1
  have v6017 : σ (.n 6017) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 5) (by norm_num)).2.2.1
  have v6028 : σ (.n 6028) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 6) (by norm_num)).2.2.1
  have v6039 : σ (.n 6039) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 7) (by norm_num)).2.2.1
  have v6096 : σ (.n 6096) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 11) (by norm_num)).2.2.1
  have hB : σ (.n 6322) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 2], 1)], [([11], 1)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
    simp only [v6096, v6039, v6028, v6017, v5971, v5960, a5622, a5621, a5620, e5619, a5618, a5617, e5616,
      a5615, a5614, e5613, a5612, a5611, e5610, a5609, a5608, e5607, a5606, a5605, a5604,
      e5603]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5624, a5623, hB]

set_option maxRecDepth 10000 in
theorem vtB10_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6346) = σ (.n 6324) + σ (.n 4590) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 3], 1)], [([12], 1)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 5625 [
    .atom (.load (.n 6325) (.n 14) 0),
    .atom (.const (.n 6326) (word 2 0 0)),
    .atom (.mul (.n 6327) (.n 6325) (.n 6326)),
    .atom (.mul (.n 6328) (.n 5960) (.n 5982)),
    .atom (.load (.n 6329) (.n 14) 1),
    .atom (.mul (.n 6330) (.n 6329) (.n 6328)),
    .atom (.add (.n 6331) (.n 6327) (.n 6330)),
    .atom (.load (.n 6332) (.n 14) 2),
    .atom (.mul (.n 6333) (.n 6332) (.n 6120)),
    .atom (.add (.n 6334) (.n 6331) (.n 6333)),
    .atom (.load (.n 6335) (.n 14) 3),
    .atom (.mul (.n 6336) (.n 6335) (.n 6063)),
    .atom (.add (.n 6337) (.n 6334) (.n 6336)),
    .atom (.load (.n 6338) (.n 14) 4),
    .atom (.mul (.n 6339) (.n 6338) (.n 6074)),
    .atom (.add (.n 6340) (.n 6337) (.n 6339)),
    .atom (.load (.n 6341) (.n 14) 5),
    .atom (.mul (.n 6342) (.n 6341) (.n 6085)),
    .atom (.add (.n 6343) (.n 6340) (.n 6342)),
    .atom (.add (.n 6344) (.n 15) (.n 6343)),
    .atom (.mul (.n 6345) (.n 4590) (.n 6344)),
    .atom (.add (.n 6346) (.n 6324) (.n 6345))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5625, a5626, a5627, a5628, a5629, a5630, a5631, a5632, a5633, a5634, a5635, a5636, a5637, a5638,
    a5639, a5640, a5641, a5642, a5643, a5644, a5645, a5646, -⟩ := hs
  have e5625 := tb_loadHolds_unique a5625 (hw 0 (by norm_num))
  have e5629 := tb_loadHolds_unique a5629 (hw 1 (by norm_num))
  have e5632 := tb_loadHolds_unique a5632 (hw 2 (by norm_num))
  have e5635 := tb_loadHolds_unique a5635 (hw 3 (by norm_num))
  have e5638 := tb_loadHolds_unique a5638 (hw 4 (by norm_num))
  have e5641 := tb_loadHolds_unique a5641 (hw 5 (by norm_num))
  have v5960 : σ (.n 5960) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2.1
  have v5982 : σ (.n 5982) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 3) (by norm_num)).2.2.1
  have v6063 : σ (.n 6063) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 8) (by norm_num)).2.2.1
  have v6074 : σ (.n 6074) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 9) (by norm_num)).2.2.1
  have v6085 : σ (.n 6085) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 10) (by norm_num)).2.2.1
  have v6120 : σ (.n 6120) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 12) (by norm_num)).2.2.1
  have hB : σ (.n 6344) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 3], 1)], [([12], 1)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
    simp only [v6120, v6085, v6074, v6063, v5982, v5960, a5644, a5643, a5642, e5641, a5640, a5639, e5638,
      a5637, a5636, e5635, a5634, a5633, e5632, a5631, a5630, e5629, a5628, a5627, a5626,
      e5625]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5646, a5645, hB]

set_option maxRecDepth 10000 in
theorem vtB10_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6371) = σ (.n 6346) + σ (.n 4597) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 4], 1)], [([13], 1)], [([5], 1), ([8], 1)], [([6], 1), ([9], 1)], [([7], 1), ([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 5647 [
    .atom (.load (.n 6347) (.n 14) 0),
    .atom (.const (.n 6348) (word 2 0 0)),
    .atom (.mul (.n 6349) (.n 6347) (.n 6348)),
    .atom (.mul (.n 6350) (.n 5960) (.n 6006)),
    .atom (.load (.n 6351) (.n 14) 1),
    .atom (.mul (.n 6352) (.n 6351) (.n 6350)),
    .atom (.add (.n 6353) (.n 6349) (.n 6352)),
    .atom (.load (.n 6354) (.n 14) 2),
    .atom (.mul (.n 6355) (.n 6354) (.n 6131)),
    .atom (.add (.n 6356) (.n 6353) (.n 6355)),
    .atom (.add (.n 6357) (.n 6017) (.n 6063)),
    .atom (.load (.n 6358) (.n 14) 3),
    .atom (.mul (.n 6359) (.n 6358) (.n 6357)),
    .atom (.add (.n 6360) (.n 6356) (.n 6359)),
    .atom (.add (.n 6361) (.n 6028) (.n 6074)),
    .atom (.load (.n 6362) (.n 14) 4),
    .atom (.mul (.n 6363) (.n 6362) (.n 6361)),
    .atom (.add (.n 6364) (.n 6360) (.n 6363)),
    .atom (.add (.n 6365) (.n 6039) (.n 6085)),
    .atom (.load (.n 6366) (.n 14) 5),
    .atom (.mul (.n 6367) (.n 6366) (.n 6365)),
    .atom (.add (.n 6368) (.n 6364) (.n 6367)),
    .atom (.add (.n 6369) (.n 15) (.n 6368)),
    .atom (.mul (.n 6370) (.n 4597) (.n 6369)),
    .atom (.add (.n 6371) (.n 6346) (.n 6370))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5647, a5648, a5649, a5650, a5651, a5652, a5653, a5654, a5655, a5656, a5657, a5658, a5659, a5660,
    a5661, a5662, a5663, a5664, a5665, a5666, a5667, a5668, a5669, a5670, a5671, -⟩ := hs
  have e5647 := tb_loadHolds_unique a5647 (hw 0 (by norm_num))
  have e5651 := tb_loadHolds_unique a5651 (hw 1 (by norm_num))
  have e5654 := tb_loadHolds_unique a5654 (hw 2 (by norm_num))
  have e5658 := tb_loadHolds_unique a5658 (hw 3 (by norm_num))
  have e5662 := tb_loadHolds_unique a5662 (hw 4 (by norm_num))
  have e5666 := tb_loadHolds_unique a5666 (hw 5 (by norm_num))
  have v5960 : σ (.n 5960) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2.1
  have v6006 : σ (.n 6006) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 4) (by norm_num)).2.2.1
  have v6017 : σ (.n 6017) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 5) (by norm_num)).2.2.1
  have v6028 : σ (.n 6028) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 6) (by norm_num)).2.2.1
  have v6039 : σ (.n 6039) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 7) (by norm_num)).2.2.1
  have v6063 : σ (.n 6063) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 8) (by norm_num)).2.2.1
  have v6074 : σ (.n 6074) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 9) (by norm_num)).2.2.1
  have v6085 : σ (.n 6085) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 10) (by norm_num)).2.2.1
  have v6131 : σ (.n 6131) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 13) (by norm_num)).2.2.1
  have hB : σ (.n 6369) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 4], 1)], [([13], 1)], [([5], 1), ([8], 1)], [([6], 1), ([9], 1)], [([7], 1), ([10], 1)]] := by
    simp only [v6131, v6085, v6074, v6063, v6039, v6028, v6017, v6006, v5960, a5669, a5668, a5667, e5666,
      a5665, a5664, a5663, e5662, a5661, a5660, a5659, e5658, a5657, a5656, a5655, e5654,
      a5653, a5652, e5651, a5650, a5649, a5648, e5647]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5671, a5670, hB]

set_option maxRecDepth 10000 in
theorem vtSide10 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6371) =
      vtSideVal [σ (.n 4569), σ (.n 4576), σ (.n 4583), σ (.n 4590), σ (.n 4597)]
        (σ (.n 15)) W ev vtBTerms10 := by
  rw [vtB10_4 h hw hev, vtB10_3 h hw hev, vtB10_2 h hw hev, vtB10_1 h hw hev, vtB10_0 h hw hev]
  simp only [vtSideVal, vtBTerms10, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide20 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 6380) =
      vtSideVal [σ (.n 4938), σ (.n 4953), σ (.n 4968), σ (.n 4983)]
        (0) (fun _ ↦ 1) ev vtBTerms20 := by
  obtain ⟨_, hs⟩ := h.slice 5674 [
    .atom (.mul (.n 6374) (.n 4938) (.n 6096)),
    .atom (.mul (.n 6375) (.n 4953) (.n 6120)),
    .atom (.add (.n 6376) (.n 6374) (.n 6375)),
    .atom (.mul (.n 6377) (.n 4968) (.n 6131)),
    .atom (.add (.n 6378) (.n 6376) (.n 6377)),
    .atom (.mul (.n 6379) (.n 4983) (.n 6142)),
    .atom (.add (.n 6380) (.n 6378) (.n 6379))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5674, a5675, a5676, a5677, a5678, a5679, a5680, -⟩ := hs
  have v6096 : σ (.n 6096) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 11) (by norm_num)).2.2.1
  have v6120 : σ (.n 6120) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 12) (by norm_num)).2.2.1
  have v6131 : σ (.n 6131) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 13) (by norm_num)).2.2.1
  have v6142 : σ (.n 6142) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 14) (by norm_num)).2.2.1
  rw [a5680, a5678, a5676, a5674, a5675, a5677, a5679, v6096, v6120, v6131, v6142]
  simp only [vtSideVal, vtBTerms20, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
