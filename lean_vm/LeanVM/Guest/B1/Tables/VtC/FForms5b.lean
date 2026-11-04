/-
  LeanVM.Guest.B1.Tables.VtC.FForms5b

  `Vt/FormsT5b.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT5b

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtD5_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6589) = σ (.n 1998) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6017 [
    .atom (.const (.n 6585) (word 3 0 0)),
    .atom (.mul (.n 6586) (.n 6585) (.n 4421)),
    .atom (.load (.n 6587) (.n 13) 1),
    .atom (.mul (.n 6588) (.n 6587) (.n 6586)),
    .atom (.mul (.n 6589) (.n 1998) (.n 6588))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6017, a6018, a6019, a6020, a6021, -⟩ := hs
  have e6019 := tb_loadHolds_unique a6019 (hw 1 (by norm_num))
  have v4421 : σ (.n 4421) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 67) (by norm_num)).2.2
  have hB : σ (.n 6588) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v4421, a6020, e6019, a6018, a6017]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6021, hB]

set_option maxRecDepth 10000 in
theorem vtD5_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6595) = σ (.n 6589) + σ (.n 2000) * vtSlots W ev 0
      [[], [], [([89], 3)], [], [], [], [], [], [], [], [], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6022 [
    .atom (.const (.n 6590) (word 3 0 0)),
    .atom (.mul (.n 6591) (.n 6590) (.n 5699)),
    .atom (.load (.n 6592) (.n 13) 2),
    .atom (.mul (.n 6593) (.n 6592) (.n 6591)),
    .atom (.mul (.n 6594) (.n 2000) (.n 6593)),
    .atom (.add (.n 6595) (.n 6589) (.n 6594))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6022, a6023, a6024, a6025, a6026, a6027, -⟩ := hs
  have e6024 := tb_loadHolds_unique a6024 (hw 2 (by norm_num))
  have v5699 : σ (.n 5699) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_evalF h (k := 156) (by norm_num)).2.2
  have hB : σ (.n 6593) = vtSlots W ev 0 [[], [], [([89], 3)], [], [], [], [], [], [], [], [], [], [], []] := by
    simp only [v5699, a6025, e6024, a6023, a6022]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6027, a6026, hB]

set_option maxRecDepth 10000 in
theorem vtD5_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6601) = σ (.n 6595) + σ (.n 2002) * vtSlots W ev 0
      [[], [], [([63], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6028 [
    .atom (.const (.n 6596) (word 3 0 0)),
    .atom (.mul (.n 6597) (.n 6596) (.n 5322)),
    .atom (.load (.n 6598) (.n 13) 2),
    .atom (.mul (.n 6599) (.n 6598) (.n 6597)),
    .atom (.mul (.n 6600) (.n 2002) (.n 6599)),
    .atom (.add (.n 6601) (.n 6595) (.n 6600))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6028, a6029, a6030, a6031, a6032, a6033, -⟩ := hs
  have e6030 := tb_loadHolds_unique a6030 (hw 2 (by norm_num))
  have v5322 : σ (.n 5322) = ev 63 := by
    rw [← hev 63 (by norm_num)]; exact (vt_evalF h (k := 130) (by norm_num)).2.2
  have hB : σ (.n 6599) = vtSlots W ev 0 [[], [], [([63], 3)], [], [], []] := by
    simp only [v5322, a6031, e6030, a6029, a6028]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6033, a6032, hB]

set_option maxRecDepth 10000 in
theorem vtD5_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6607) = σ (.n 6601) + σ (.n 2004) * vtSlots W ev 0
      [[], [], [([64], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6034 [
    .atom (.const (.n 6602) (word 3 0 0)),
    .atom (.mul (.n 6603) (.n 6602) (.n 5333)),
    .atom (.load (.n 6604) (.n 13) 2),
    .atom (.mul (.n 6605) (.n 6604) (.n 6603)),
    .atom (.mul (.n 6606) (.n 2004) (.n 6605)),
    .atom (.add (.n 6607) (.n 6601) (.n 6606))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6034, a6035, a6036, a6037, a6038, a6039, -⟩ := hs
  have e6036 := tb_loadHolds_unique a6036 (hw 2 (by norm_num))
  have v5333 : σ (.n 5333) = ev 64 := by
    rw [← hev 64 (by norm_num)]; exact (vt_evalF h (k := 131) (by norm_num)).2.2
  have hB : σ (.n 6605) = vtSlots W ev 0 [[], [], [([64], 3)], [], [], []] := by
    simp only [v5333, a6037, e6036, a6035, a6034]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6039, a6038, hB]

set_option maxRecDepth 10000 in
theorem vtD5_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6613) = σ (.n 6607) + σ (.n 2006) * vtSlots W ev 0
      [[], [], [([65], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6040 [
    .atom (.const (.n 6608) (word 3 0 0)),
    .atom (.mul (.n 6609) (.n 6608) (.n 5357)),
    .atom (.load (.n 6610) (.n 13) 2),
    .atom (.mul (.n 6611) (.n 6610) (.n 6609)),
    .atom (.mul (.n 6612) (.n 2006) (.n 6611)),
    .atom (.add (.n 6613) (.n 6607) (.n 6612))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6040, a6041, a6042, a6043, a6044, a6045, -⟩ := hs
  have e6042 := tb_loadHolds_unique a6042 (hw 2 (by norm_num))
  have v5357 : σ (.n 5357) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_evalF h (k := 132) (by norm_num)).2.2
  have hB : σ (.n 6611) = vtSlots W ev 0 [[], [], [([65], 3)], [], [], []] := by
    simp only [v5357, a6043, e6042, a6041, a6040]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6045, a6044, hB]

set_option maxRecDepth 10000 in
theorem vtD5_5F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6619) = σ (.n 6613) + σ (.n 2008) * vtSlots W ev 0
      [[], [], [([66], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6046 [
    .atom (.const (.n 6614) (word 3 0 0)),
    .atom (.mul (.n 6615) (.n 6614) (.n 5368)),
    .atom (.load (.n 6616) (.n 13) 2),
    .atom (.mul (.n 6617) (.n 6616) (.n 6615)),
    .atom (.mul (.n 6618) (.n 2008) (.n 6617)),
    .atom (.add (.n 6619) (.n 6613) (.n 6618))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6046, a6047, a6048, a6049, a6050, a6051, -⟩ := hs
  have e6048 := tb_loadHolds_unique a6048 (hw 2 (by norm_num))
  have v5368 : σ (.n 5368) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_evalF h (k := 133) (by norm_num)).2.2
  have hB : σ (.n 6617) = vtSlots W ev 0 [[], [], [([66], 3)], [], [], []] := by
    simp only [v5368, a6049, e6048, a6047, a6046]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6051, a6050, hB]

set_option maxRecDepth 10000 in
theorem vtD5_6F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6625) = σ (.n 6619) + σ (.n 2010) * vtSlots W ev 0
      [[], [], [([67], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6052 [
    .atom (.const (.n 6620) (word 3 0 0)),
    .atom (.mul (.n 6621) (.n 6620) (.n 5379)),
    .atom (.load (.n 6622) (.n 13) 2),
    .atom (.mul (.n 6623) (.n 6622) (.n 6621)),
    .atom (.mul (.n 6624) (.n 2010) (.n 6623)),
    .atom (.add (.n 6625) (.n 6619) (.n 6624))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6052, a6053, a6054, a6055, a6056, a6057, -⟩ := hs
  have e6054 := tb_loadHolds_unique a6054 (hw 2 (by norm_num))
  have v5379 : σ (.n 5379) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_evalF h (k := 134) (by norm_num)).2.2
  have hB : σ (.n 6623) = vtSlots W ev 0 [[], [], [([67], 3)], [], [], []] := by
    simp only [v5379, a6055, e6054, a6053, a6052]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6057, a6056, hB]

set_option maxRecDepth 10000 in
theorem vtD5_7F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6631) = σ (.n 6625) + σ (.n 2012) * vtSlots W ev 0
      [[], [], [([68], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6058 [
    .atom (.const (.n 6626) (word 3 0 0)),
    .atom (.mul (.n 6627) (.n 6626) (.n 5390)),
    .atom (.load (.n 6628) (.n 13) 2),
    .atom (.mul (.n 6629) (.n 6628) (.n 6627)),
    .atom (.mul (.n 6630) (.n 2012) (.n 6629)),
    .atom (.add (.n 6631) (.n 6625) (.n 6630))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6058, a6059, a6060, a6061, a6062, a6063, -⟩ := hs
  have e6060 := tb_loadHolds_unique a6060 (hw 2 (by norm_num))
  have v5390 : σ (.n 5390) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_evalF h (k := 135) (by norm_num)).2.2
  have hB : σ (.n 6629) = vtSlots W ev 0 [[], [], [([68], 3)], [], [], []] := by
    simp only [v5390, a6061, e6060, a6059, a6058]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6063, a6062, hB]

set_option maxRecDepth 10000 in
theorem vtD5_8F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6637) = σ (.n 6631) + σ (.n 2014) * vtSlots W ev 0
      [[], [], [([69], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6064 [
    .atom (.const (.n 6632) (word 3 0 0)),
    .atom (.mul (.n 6633) (.n 6632) (.n 5414)),
    .atom (.load (.n 6634) (.n 13) 2),
    .atom (.mul (.n 6635) (.n 6634) (.n 6633)),
    .atom (.mul (.n 6636) (.n 2014) (.n 6635)),
    .atom (.add (.n 6637) (.n 6631) (.n 6636))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6064, a6065, a6066, a6067, a6068, a6069, -⟩ := hs
  have e6066 := tb_loadHolds_unique a6066 (hw 2 (by norm_num))
  have v5414 : σ (.n 5414) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_evalF h (k := 136) (by norm_num)).2.2
  have hB : σ (.n 6635) = vtSlots W ev 0 [[], [], [([69], 3)], [], [], []] := by
    simp only [v5414, a6067, e6066, a6065, a6064]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6069, a6068, hB]

set_option maxRecDepth 10000 in
theorem vtD5_9F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6643) = σ (.n 6637) + σ (.n 2016) * vtSlots W ev 0
      [[], [], [([70], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6070 [
    .atom (.const (.n 6638) (word 3 0 0)),
    .atom (.mul (.n 6639) (.n 6638) (.n 5425)),
    .atom (.load (.n 6640) (.n 13) 2),
    .atom (.mul (.n 6641) (.n 6640) (.n 6639)),
    .atom (.mul (.n 6642) (.n 2016) (.n 6641)),
    .atom (.add (.n 6643) (.n 6637) (.n 6642))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6070, a6071, a6072, a6073, a6074, a6075, -⟩ := hs
  have e6072 := tb_loadHolds_unique a6072 (hw 2 (by norm_num))
  have v5425 : σ (.n 5425) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_evalF h (k := 137) (by norm_num)).2.2
  have hB : σ (.n 6641) = vtSlots W ev 0 [[], [], [([70], 3)], [], [], []] := by
    simp only [v5425, a6073, e6072, a6071, a6070]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6075, a6074, hB]

set_option maxRecDepth 10000 in
theorem vtD5_10F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6649) = σ (.n 6643) + σ (.n 2018) * vtSlots W ev 0
      [[], [], [([71], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6076 [
    .atom (.const (.n 6644) (word 3 0 0)),
    .atom (.mul (.n 6645) (.n 6644) (.n 5436)),
    .atom (.load (.n 6646) (.n 13) 2),
    .atom (.mul (.n 6647) (.n 6646) (.n 6645)),
    .atom (.mul (.n 6648) (.n 2018) (.n 6647)),
    .atom (.add (.n 6649) (.n 6643) (.n 6648))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6076, a6077, a6078, a6079, a6080, a6081, -⟩ := hs
  have e6078 := tb_loadHolds_unique a6078 (hw 2 (by norm_num))
  have v5436 : σ (.n 5436) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_evalF h (k := 138) (by norm_num)).2.2
  have hB : σ (.n 6647) = vtSlots W ev 0 [[], [], [([71], 3)], [], [], []] := by
    simp only [v5436, a6079, e6078, a6077, a6076]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6081, a6080, hB]

set_option maxRecDepth 10000 in
theorem vtD5_11F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6655) = σ (.n 6649) + σ (.n 2020) * vtSlots W ev 0
      [[], [], [([72], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6082 [
    .atom (.const (.n 6650) (word 3 0 0)),
    .atom (.mul (.n 6651) (.n 6650) (.n 5447)),
    .atom (.load (.n 6652) (.n 13) 2),
    .atom (.mul (.n 6653) (.n 6652) (.n 6651)),
    .atom (.mul (.n 6654) (.n 2020) (.n 6653)),
    .atom (.add (.n 6655) (.n 6649) (.n 6654))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6082, a6083, a6084, a6085, a6086, a6087, -⟩ := hs
  have e6084 := tb_loadHolds_unique a6084 (hw 2 (by norm_num))
  have v5447 : σ (.n 5447) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_evalF h (k := 139) (by norm_num)).2.2
  have hB : σ (.n 6653) = vtSlots W ev 0 [[], [], [([72], 3)], [], [], []] := by
    simp only [v5447, a6085, e6084, a6083, a6082]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6087, a6086, hB]

set_option maxRecDepth 10000 in
theorem vtD5_12F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6661) = σ (.n 6655) + σ (.n 2022) * vtSlots W ev 0
      [[], [], [([73], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6088 [
    .atom (.const (.n 6656) (word 3 0 0)),
    .atom (.mul (.n 6657) (.n 6656) (.n 5471)),
    .atom (.load (.n 6658) (.n 13) 2),
    .atom (.mul (.n 6659) (.n 6658) (.n 6657)),
    .atom (.mul (.n 6660) (.n 2022) (.n 6659)),
    .atom (.add (.n 6661) (.n 6655) (.n 6660))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6088, a6089, a6090, a6091, a6092, a6093, -⟩ := hs
  have e6090 := tb_loadHolds_unique a6090 (hw 2 (by norm_num))
  have v5471 : σ (.n 5471) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_evalF h (k := 140) (by norm_num)).2.2
  have hB : σ (.n 6659) = vtSlots W ev 0 [[], [], [([73], 3)], [], [], []] := by
    simp only [v5471, a6091, e6090, a6089, a6088]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6093, a6092, hB]

set_option maxRecDepth 10000 in
theorem vtD5_13F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6667) = σ (.n 6661) + σ (.n 2024) * vtSlots W ev 0
      [[], [], [([74], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6094 [
    .atom (.const (.n 6662) (word 3 0 0)),
    .atom (.mul (.n 6663) (.n 6662) (.n 5482)),
    .atom (.load (.n 6664) (.n 13) 2),
    .atom (.mul (.n 6665) (.n 6664) (.n 6663)),
    .atom (.mul (.n 6666) (.n 2024) (.n 6665)),
    .atom (.add (.n 6667) (.n 6661) (.n 6666))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6094, a6095, a6096, a6097, a6098, a6099, -⟩ := hs
  have e6096 := tb_loadHolds_unique a6096 (hw 2 (by norm_num))
  have v5482 : σ (.n 5482) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_evalF h (k := 141) (by norm_num)).2.2
  have hB : σ (.n 6665) = vtSlots W ev 0 [[], [], [([74], 3)], [], [], []] := by
    simp only [v5482, a6097, e6096, a6095, a6094]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6099, a6098, hB]

set_option maxRecDepth 10000 in
theorem vtD5_14F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6673) = σ (.n 6667) + σ (.n 2026) * vtSlots W ev 0
      [[], [], [([75], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6100 [
    .atom (.const (.n 6668) (word 3 0 0)),
    .atom (.mul (.n 6669) (.n 6668) (.n 5493)),
    .atom (.load (.n 6670) (.n 13) 2),
    .atom (.mul (.n 6671) (.n 6670) (.n 6669)),
    .atom (.mul (.n 6672) (.n 2026) (.n 6671)),
    .atom (.add (.n 6673) (.n 6667) (.n 6672))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6100, a6101, a6102, a6103, a6104, a6105, -⟩ := hs
  have e6102 := tb_loadHolds_unique a6102 (hw 2 (by norm_num))
  have v5493 : σ (.n 5493) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_evalF h (k := 142) (by norm_num)).2.2
  have hB : σ (.n 6671) = vtSlots W ev 0 [[], [], [([75], 3)], [], [], []] := by
    simp only [v5493, a6103, e6102, a6101, a6100]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6105, a6104, hB]

set_option maxRecDepth 10000 in
theorem vtD5_15F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6679) = σ (.n 6673) + σ (.n 2028) * vtSlots W ev 0
      [[], [], [([76], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6106 [
    .atom (.const (.n 6674) (word 3 0 0)),
    .atom (.mul (.n 6675) (.n 6674) (.n 5504)),
    .atom (.load (.n 6676) (.n 13) 2),
    .atom (.mul (.n 6677) (.n 6676) (.n 6675)),
    .atom (.mul (.n 6678) (.n 2028) (.n 6677)),
    .atom (.add (.n 6679) (.n 6673) (.n 6678))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6106, a6107, a6108, a6109, a6110, a6111, -⟩ := hs
  have e6108 := tb_loadHolds_unique a6108 (hw 2 (by norm_num))
  have v5504 : σ (.n 5504) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_evalF h (k := 143) (by norm_num)).2.2
  have hB : σ (.n 6677) = vtSlots W ev 0 [[], [], [([76], 3)], [], [], []] := by
    simp only [v5504, a6109, e6108, a6107, a6106]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6111, a6110, hB]

set_option maxRecDepth 10000 in
theorem vtD5_16F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6685) = σ (.n 6679) + σ (.n 2030) * vtSlots W ev 0
      [[], [], [([77], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6112 [
    .atom (.const (.n 6680) (word 3 0 0)),
    .atom (.mul (.n 6681) (.n 6680) (.n 5528)),
    .atom (.load (.n 6682) (.n 13) 2),
    .atom (.mul (.n 6683) (.n 6682) (.n 6681)),
    .atom (.mul (.n 6684) (.n 2030) (.n 6683)),
    .atom (.add (.n 6685) (.n 6679) (.n 6684))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6112, a6113, a6114, a6115, a6116, a6117, -⟩ := hs
  have e6114 := tb_loadHolds_unique a6114 (hw 2 (by norm_num))
  have v5528 : σ (.n 5528) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_evalF h (k := 144) (by norm_num)).2.2
  have hB : σ (.n 6683) = vtSlots W ev 0 [[], [], [([77], 3)], [], [], []] := by
    simp only [v5528, a6115, e6114, a6113, a6112]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6117, a6116, hB]

set_option maxRecDepth 10000 in
theorem vtD5_17F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6691) = σ (.n 6685) + σ (.n 2032) * vtSlots W ev 0
      [[], [], [([78], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6118 [
    .atom (.const (.n 6686) (word 3 0 0)),
    .atom (.mul (.n 6687) (.n 6686) (.n 5539)),
    .atom (.load (.n 6688) (.n 13) 2),
    .atom (.mul (.n 6689) (.n 6688) (.n 6687)),
    .atom (.mul (.n 6690) (.n 2032) (.n 6689)),
    .atom (.add (.n 6691) (.n 6685) (.n 6690))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6118, a6119, a6120, a6121, a6122, a6123, -⟩ := hs
  have e6120 := tb_loadHolds_unique a6120 (hw 2 (by norm_num))
  have v5539 : σ (.n 5539) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_evalF h (k := 145) (by norm_num)).2.2
  have hB : σ (.n 6689) = vtSlots W ev 0 [[], [], [([78], 3)], [], [], []] := by
    simp only [v5539, a6121, e6120, a6119, a6118]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6123, a6122, hB]

set_option maxRecDepth 10000 in
theorem vtD5_18F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6697) = σ (.n 6691) + σ (.n 2034) * vtSlots W ev 0
      [[], [], [([79], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6124 [
    .atom (.const (.n 6692) (word 3 0 0)),
    .atom (.mul (.n 6693) (.n 6692) (.n 5550)),
    .atom (.load (.n 6694) (.n 13) 2),
    .atom (.mul (.n 6695) (.n 6694) (.n 6693)),
    .atom (.mul (.n 6696) (.n 2034) (.n 6695)),
    .atom (.add (.n 6697) (.n 6691) (.n 6696))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6124, a6125, a6126, a6127, a6128, a6129, -⟩ := hs
  have e6126 := tb_loadHolds_unique a6126 (hw 2 (by norm_num))
  have v5550 : σ (.n 5550) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_evalF h (k := 146) (by norm_num)).2.2
  have hB : σ (.n 6695) = vtSlots W ev 0 [[], [], [([79], 3)], [], [], []] := by
    simp only [v5550, a6127, e6126, a6125, a6124]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6129, a6128, hB]

set_option maxRecDepth 10000 in
theorem vtD5_19F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6703) = σ (.n 6697) + σ (.n 2036) * vtSlots W ev 0
      [[], [], [([80], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6130 [
    .atom (.const (.n 6698) (word 3 0 0)),
    .atom (.mul (.n 6699) (.n 6698) (.n 5561)),
    .atom (.load (.n 6700) (.n 13) 2),
    .atom (.mul (.n 6701) (.n 6700) (.n 6699)),
    .atom (.mul (.n 6702) (.n 2036) (.n 6701)),
    .atom (.add (.n 6703) (.n 6697) (.n 6702))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6130, a6131, a6132, a6133, a6134, a6135, -⟩ := hs
  have e6132 := tb_loadHolds_unique a6132 (hw 2 (by norm_num))
  have v5561 : σ (.n 5561) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_evalF h (k := 147) (by norm_num)).2.2
  have hB : σ (.n 6701) = vtSlots W ev 0 [[], [], [([80], 3)], [], [], []] := by
    simp only [v5561, a6133, e6132, a6131, a6130]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6135, a6134, hB]

set_option maxRecDepth 10000 in
theorem vtD5_20F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6709) = σ (.n 6703) + σ (.n 2038) * vtSlots W ev 0
      [[], [], [([81], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6136 [
    .atom (.const (.n 6704) (word 3 0 0)),
    .atom (.mul (.n 6705) (.n 6704) (.n 5585)),
    .atom (.load (.n 6706) (.n 13) 2),
    .atom (.mul (.n 6707) (.n 6706) (.n 6705)),
    .atom (.mul (.n 6708) (.n 2038) (.n 6707)),
    .atom (.add (.n 6709) (.n 6703) (.n 6708))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6136, a6137, a6138, a6139, a6140, a6141, -⟩ := hs
  have e6138 := tb_loadHolds_unique a6138 (hw 2 (by norm_num))
  have v5585 : σ (.n 5585) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_evalF h (k := 148) (by norm_num)).2.2
  have hB : σ (.n 6707) = vtSlots W ev 0 [[], [], [([81], 3)], [], [], []] := by
    simp only [v5585, a6139, e6138, a6137, a6136]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6141, a6140, hB]

set_option maxRecDepth 10000 in
theorem vtD5_21F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6715) = σ (.n 6709) + σ (.n 2040) * vtSlots W ev 0
      [[], [], [([82], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6142 [
    .atom (.const (.n 6710) (word 3 0 0)),
    .atom (.mul (.n 6711) (.n 6710) (.n 5596)),
    .atom (.load (.n 6712) (.n 13) 2),
    .atom (.mul (.n 6713) (.n 6712) (.n 6711)),
    .atom (.mul (.n 6714) (.n 2040) (.n 6713)),
    .atom (.add (.n 6715) (.n 6709) (.n 6714))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6142, a6143, a6144, a6145, a6146, a6147, -⟩ := hs
  have e6144 := tb_loadHolds_unique a6144 (hw 2 (by norm_num))
  have v5596 : σ (.n 5596) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_evalF h (k := 149) (by norm_num)).2.2
  have hB : σ (.n 6713) = vtSlots W ev 0 [[], [], [([82], 3)], [], [], []] := by
    simp only [v5596, a6145, e6144, a6143, a6142]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6147, a6146, hB]

set_option maxRecDepth 10000 in
theorem vtD5_22F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6721) = σ (.n 6715) + σ (.n 2042) * vtSlots W ev 0
      [[], [], [([83], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6148 [
    .atom (.const (.n 6716) (word 3 0 0)),
    .atom (.mul (.n 6717) (.n 6716) (.n 5607)),
    .atom (.load (.n 6718) (.n 13) 2),
    .atom (.mul (.n 6719) (.n 6718) (.n 6717)),
    .atom (.mul (.n 6720) (.n 2042) (.n 6719)),
    .atom (.add (.n 6721) (.n 6715) (.n 6720))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6148, a6149, a6150, a6151, a6152, a6153, -⟩ := hs
  have e6150 := tb_loadHolds_unique a6150 (hw 2 (by norm_num))
  have v5607 : σ (.n 5607) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_evalF h (k := 150) (by norm_num)).2.2
  have hB : σ (.n 6719) = vtSlots W ev 0 [[], [], [([83], 3)], [], [], []] := by
    simp only [v5607, a6151, e6150, a6149, a6148]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6153, a6152, hB]

set_option maxRecDepth 10000 in
theorem vtD5_23F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6727) = σ (.n 6721) + σ (.n 2044) * vtSlots W ev 0
      [[], [], [([84], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6154 [
    .atom (.const (.n 6722) (word 3 0 0)),
    .atom (.mul (.n 6723) (.n 6722) (.n 5618)),
    .atom (.load (.n 6724) (.n 13) 2),
    .atom (.mul (.n 6725) (.n 6724) (.n 6723)),
    .atom (.mul (.n 6726) (.n 2044) (.n 6725)),
    .atom (.add (.n 6727) (.n 6721) (.n 6726))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6154, a6155, a6156, a6157, a6158, a6159, -⟩ := hs
  have e6156 := tb_loadHolds_unique a6156 (hw 2 (by norm_num))
  have v5618 : σ (.n 5618) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_evalF h (k := 151) (by norm_num)).2.2
  have hB : σ (.n 6725) = vtSlots W ev 0 [[], [], [([84], 3)], [], [], []] := by
    simp only [v5618, a6157, e6156, a6155, a6154]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6159, a6158, hB]

set_option maxRecDepth 10000 in
theorem vtD5_24F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6733) = σ (.n 6727) + σ (.n 2046) * vtSlots W ev 0
      [[], [], [([85], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6160 [
    .atom (.const (.n 6728) (word 3 0 0)),
    .atom (.mul (.n 6729) (.n 6728) (.n 5642)),
    .atom (.load (.n 6730) (.n 13) 2),
    .atom (.mul (.n 6731) (.n 6730) (.n 6729)),
    .atom (.mul (.n 6732) (.n 2046) (.n 6731)),
    .atom (.add (.n 6733) (.n 6727) (.n 6732))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6160, a6161, a6162, a6163, a6164, a6165, -⟩ := hs
  have e6162 := tb_loadHolds_unique a6162 (hw 2 (by norm_num))
  have v5642 : σ (.n 5642) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_evalF h (k := 152) (by norm_num)).2.2
  have hB : σ (.n 6731) = vtSlots W ev 0 [[], [], [([85], 3)], [], [], []] := by
    simp only [v5642, a6163, e6162, a6161, a6160]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6165, a6164, hB]

set_option maxRecDepth 10000 in
theorem vtD5_25F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6739) = σ (.n 6733) + σ (.n 2048) * vtSlots W ev 0
      [[], [], [([86], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6166 [
    .atom (.const (.n 6734) (word 3 0 0)),
    .atom (.mul (.n 6735) (.n 6734) (.n 5653)),
    .atom (.load (.n 6736) (.n 13) 2),
    .atom (.mul (.n 6737) (.n 6736) (.n 6735)),
    .atom (.mul (.n 6738) (.n 2048) (.n 6737)),
    .atom (.add (.n 6739) (.n 6733) (.n 6738))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6166, a6167, a6168, a6169, a6170, a6171, -⟩ := hs
  have e6168 := tb_loadHolds_unique a6168 (hw 2 (by norm_num))
  have v5653 : σ (.n 5653) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_evalF h (k := 153) (by norm_num)).2.2
  have hB : σ (.n 6737) = vtSlots W ev 0 [[], [], [([86], 3)], [], [], []] := by
    simp only [v5653, a6169, e6168, a6167, a6166]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6171, a6170, hB]

set_option maxRecDepth 10000 in
theorem vtD5_26F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6745) = σ (.n 6739) + σ (.n 2050) * vtSlots W ev 0
      [[], [], [([87], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6172 [
    .atom (.const (.n 6740) (word 3 0 0)),
    .atom (.mul (.n 6741) (.n 6740) (.n 5664)),
    .atom (.load (.n 6742) (.n 13) 2),
    .atom (.mul (.n 6743) (.n 6742) (.n 6741)),
    .atom (.mul (.n 6744) (.n 2050) (.n 6743)),
    .atom (.add (.n 6745) (.n 6739) (.n 6744))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6172, a6173, a6174, a6175, a6176, a6177, -⟩ := hs
  have e6174 := tb_loadHolds_unique a6174 (hw 2 (by norm_num))
  have v5664 : σ (.n 5664) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_evalF h (k := 154) (by norm_num)).2.2
  have hB : σ (.n 6743) = vtSlots W ev 0 [[], [], [([87], 3)], [], [], []] := by
    simp only [v5664, a6175, e6174, a6173, a6172]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6177, a6176, hB]

set_option maxRecDepth 10000 in
theorem vtD5_27F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6751) = σ (.n 6745) + σ (.n 2052) * vtSlots W ev 0
      [[], [], [([88], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6178 [
    .atom (.const (.n 6746) (word 3 0 0)),
    .atom (.mul (.n 6747) (.n 6746) (.n 5675)),
    .atom (.load (.n 6748) (.n 13) 2),
    .atom (.mul (.n 6749) (.n 6748) (.n 6747)),
    .atom (.mul (.n 6750) (.n 2052) (.n 6749)),
    .atom (.add (.n 6751) (.n 6745) (.n 6750))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6178, a6179, a6180, a6181, a6182, a6183, -⟩ := hs
  have e6180 := tb_loadHolds_unique a6180 (hw 2 (by norm_num))
  have v5675 : σ (.n 5675) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_evalF h (k := 155) (by norm_num)).2.2
  have hB : σ (.n 6749) = vtSlots W ev 0 [[], [], [([88], 3)], [], [], []] := by
    simp only [v5675, a6181, e6180, a6179, a6178]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6183, a6182, hB]

end
end LeanVM.Guest.B1.Tables
