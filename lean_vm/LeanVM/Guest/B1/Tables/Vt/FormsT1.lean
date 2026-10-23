/-
  LeanVM.Guest.B1.Tables.Vt.FormsT1

  Table 1's forms on the three sides, from the guest's statements: each block's value from its
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
theorem vtB01_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6618) = σ (.n 3130) * vtBlockVal (σ (.n 15)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 5875 [
    .atom (.load (.n 6608) (.n 14) 0),
    .atom (.const (.n 6609) (word 2 0 0)),
    .atom (.mul (.n 6610) (.n 6609) (.n 6401)),
    .atom (.load (.n 6611) (.n 14) 1),
    .atom (.mul (.n 6612) (.n 6611) (.n 6610)),
    .atom (.add (.n 6613) (.n 6608) (.n 6612)),
    .atom (.load (.n 6614) (.n 14) 2),
    .atom (.mul (.n 6615) (.n 6614) (.n 6425)),
    .atom (.add (.n 6616) (.n 6613) (.n 6615)),
    .atom (.add (.n 6617) (.n 15) (.n 6616)),
    .atom (.mul (.n 6618) (.n 3130) (.n 6617))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5875, a5876, a5877, a5878, a5879, a5880, a5881, a5882, a5883, a5884, a5885, -⟩ := hs
  have e5875 := tb_loadHolds_unique a5875 (hw 0 (by norm_num))
  have e5878 := tb_loadHolds_unique a5878 (hw 1 (by norm_num))
  have e5881 := tb_loadHolds_unique a5881 (hw 2 (by norm_num))
  have v6401 : σ (.n 6401) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 15) (by norm_num)).2.2.1
  have v6425 : σ (.n 6425) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2.1
  have hB : σ (.n 6617) = vtBlockVal (σ (.n 15)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v6425, v6401, a5884, a5883, a5882, e5881, a5880, a5879, e5878, a5877, a5876, e5875]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5885, hB]

set_option maxRecDepth 10000 in
theorem vtB01_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6653) = σ (.n 6618) + σ (.n 3149) * vtBlockVal (σ (.n 15)) W ev
      [[([], 4)], [([0], 1)], [([14], 2)], [([], 2)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 5886 [
    .atom (.load (.n 6619) (.n 14) 0),
    .atom (.const (.n 6620) (word 4 0 0)),
    .atom (.mul (.n 6621) (.n 6619) (.n 6620)),
    .atom (.load (.n 6622) (.n 14) 1),
    .atom (.mul (.n 6623) (.n 6622) (.n 6401)),
    .atom (.add (.n 6624) (.n 6621) (.n 6623)),
    .atom (.const (.n 6625) (word 2 0 0)),
    .atom (.mul (.n 6626) (.n 6625) (.n 6607)),
    .atom (.load (.n 6627) (.n 14) 2),
    .atom (.mul (.n 6628) (.n 6627) (.n 6626)),
    .atom (.add (.n 6629) (.n 6624) (.n 6628)),
    .atom (.load (.n 6630) (.n 14) 3),
    .atom (.const (.n 6631) (word 2 0 0)),
    .atom (.mul (.n 6632) (.n 6630) (.n 6631)),
    .atom (.add (.n 6633) (.n 6629) (.n 6632)),
    .atom (.load (.n 6634) (.n 14) 4),
    .atom (.mul (.n 6635) (.n 6634) (.n 6436)),
    .atom (.add (.n 6636) (.n 6633) (.n 6635)),
    .atom (.load (.n 6637) (.n 14) 5),
    .atom (.mul (.n 6638) (.n 6637) (.n 6447)),
    .atom (.add (.n 6639) (.n 6636) (.n 6638)),
    .atom (.load (.n 6640) (.n 14) 6),
    .atom (.mul (.n 6641) (.n 6640) (.n 6458)),
    .atom (.add (.n 6642) (.n 6639) (.n 6641)),
    .atom (.load (.n 6643) (.n 14) 7),
    .atom (.const (.n 6644) (word 0 0 0)),
    .atom (.mul (.n 6645) (.n 6643) (.n 6644)),
    .atom (.add (.n 6646) (.n 6642) (.n 6645)),
    .atom (.load (.n 6647) (.n 14) 8),
    .atom (.const (.n 6648) (word 0 0 0)),
    .atom (.mul (.n 6649) (.n 6647) (.n 6648)),
    .atom (.add (.n 6650) (.n 6646) (.n 6649)),
    .atom (.add (.n 6651) (.n 15) (.n 6650)),
    .atom (.mul (.n 6652) (.n 3149) (.n 6651)),
    .atom (.add (.n 6653) (.n 6618) (.n 6652))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5886, a5887, a5888, a5889, a5890, a5891, a5892, a5893, a5894, a5895, a5896, a5897, a5898, a5899,
    a5900, a5901, a5902, a5903, a5904, a5905, a5906, a5907, a5908, a5909, a5910, a5911, a5912,
    a5913, a5914, a5915, a5916, a5917, a5918, a5919, a5920, -⟩ := hs
  have e5886 := tb_loadHolds_unique a5886 (hw 0 (by norm_num))
  have e5889 := tb_loadHolds_unique a5889 (hw 1 (by norm_num))
  have e5894 := tb_loadHolds_unique a5894 (hw 2 (by norm_num))
  have e5897 := tb_loadHolds_unique a5897 (hw 3 (by norm_num))
  have e5901 := tb_loadHolds_unique a5901 (hw 4 (by norm_num))
  have e5904 := tb_loadHolds_unique a5904 (hw 5 (by norm_num))
  have e5907 := tb_loadHolds_unique a5907 (hw 6 (by norm_num))
  have e5910 := tb_loadHolds_unique a5910 (hw 7 (by norm_num))
  have e5914 := tb_loadHolds_unique a5914 (hw 8 (by norm_num))
  have v6401 : σ (.n 6401) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 15) (by norm_num)).2.2.1
  have v6436 : σ (.n 6436) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 17) (by norm_num)).2.2.1
  have v6447 : σ (.n 6447) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 18) (by norm_num)).2.2.1
  have v6458 : σ (.n 6458) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 19) (by norm_num)).2.2.1
  have v6607 : σ (.n 6607) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 29) (by norm_num)).2.2.1
  have hB : σ (.n 6651) = vtBlockVal (σ (.n 15)) W ev [[([], 4)], [([0], 1)], [([14], 2)], [([], 2)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v6607, v6458, v6447, v6436, v6401, a5918, a5917, a5916, a5915, e5914, a5913, a5912, a5911,
      e5910, a5909, a5908, e5907, a5906, a5905, e5904, a5903, a5902, e5901, a5900, a5899,
      a5898, e5897, a5896, a5895, e5894, a5893, a5892, a5891, a5890, e5889, a5888, a5887,
      e5886]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5920, a5919, hB]

set_option maxRecDepth 10000 in
theorem vtB01_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6677) = σ (.n 6653) + σ (.n 3168) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 2], 1)], [([11], 2)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 5921 [
    .atom (.load (.n 6654) (.n 14) 0),
    .atom (.const (.n 6655) (word 2 0 0)),
    .atom (.mul (.n 6656) (.n 6654) (.n 6655)),
    .atom (.mul (.n 6657) (.n 6425) (.n 6436)),
    .atom (.load (.n 6658) (.n 14) 1),
    .atom (.mul (.n 6659) (.n 6658) (.n 6657)),
    .atom (.add (.n 6660) (.n 6656) (.n 6659)),
    .atom (.const (.n 6661) (word 2 0 0)),
    .atom (.mul (.n 6662) (.n 6661) (.n 6561)),
    .atom (.load (.n 6663) (.n 14) 2),
    .atom (.mul (.n 6664) (.n 6663) (.n 6662)),
    .atom (.add (.n 6665) (.n 6660) (.n 6664)),
    .atom (.load (.n 6666) (.n 14) 3),
    .atom (.mul (.n 6667) (.n 6666) (.n 6482)),
    .atom (.add (.n 6668) (.n 6665) (.n 6667)),
    .atom (.load (.n 6669) (.n 14) 4),
    .atom (.mul (.n 6670) (.n 6669) (.n 6493)),
    .atom (.add (.n 6671) (.n 6668) (.n 6670)),
    .atom (.load (.n 6672) (.n 14) 5),
    .atom (.mul (.n 6673) (.n 6672) (.n 6504)),
    .atom (.add (.n 6674) (.n 6671) (.n 6673)),
    .atom (.add (.n 6675) (.n 15) (.n 6674)),
    .atom (.mul (.n 6676) (.n 3168) (.n 6675)),
    .atom (.add (.n 6677) (.n 6653) (.n 6676))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5921, a5922, a5923, a5924, a5925, a5926, a5927, a5928, a5929, a5930, a5931, a5932, a5933, a5934,
    a5935, a5936, a5937, a5938, a5939, a5940, a5941, a5942, a5943, a5944, -⟩ := hs
  have e5921 := tb_loadHolds_unique a5921 (hw 0 (by norm_num))
  have e5925 := tb_loadHolds_unique a5925 (hw 1 (by norm_num))
  have e5930 := tb_loadHolds_unique a5930 (hw 2 (by norm_num))
  have e5933 := tb_loadHolds_unique a5933 (hw 3 (by norm_num))
  have e5936 := tb_loadHolds_unique a5936 (hw 4 (by norm_num))
  have e5939 := tb_loadHolds_unique a5939 (hw 5 (by norm_num))
  have v6425 : σ (.n 6425) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2.1
  have v6436 : σ (.n 6436) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 17) (by norm_num)).2.2.1
  have v6482 : σ (.n 6482) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 20) (by norm_num)).2.2.1
  have v6493 : σ (.n 6493) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 21) (by norm_num)).2.2.1
  have v6504 : σ (.n 6504) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 22) (by norm_num)).2.2.1
  have v6561 : σ (.n 6561) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 26) (by norm_num)).2.2.1
  have hB : σ (.n 6675) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 2], 1)], [([11], 2)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
    simp only [v6561, v6504, v6493, v6482, v6436, v6425, a5942, a5941, a5940, e5939, a5938, a5937, e5936,
      a5935, a5934, e5933, a5932, a5931, e5930, a5929, a5928, a5927, a5926, e5925, a5924,
      a5923, a5922, e5921]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5944, a5943, hB]

set_option maxRecDepth 10000 in
theorem vtB01_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6701) = σ (.n 6677) + σ (.n 3187) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 3], 1)], [([12], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 5945 [
    .atom (.load (.n 6678) (.n 14) 0),
    .atom (.const (.n 6679) (word 2 0 0)),
    .atom (.mul (.n 6680) (.n 6678) (.n 6679)),
    .atom (.mul (.n 6681) (.n 6425) (.n 6447)),
    .atom (.load (.n 6682) (.n 14) 1),
    .atom (.mul (.n 6683) (.n 6682) (.n 6681)),
    .atom (.add (.n 6684) (.n 6680) (.n 6683)),
    .atom (.const (.n 6685) (word 2 0 0)),
    .atom (.mul (.n 6686) (.n 6685) (.n 6572)),
    .atom (.load (.n 6687) (.n 14) 2),
    .atom (.mul (.n 6688) (.n 6687) (.n 6686)),
    .atom (.add (.n 6689) (.n 6684) (.n 6688)),
    .atom (.load (.n 6690) (.n 14) 3),
    .atom (.mul (.n 6691) (.n 6690) (.n 6515)),
    .atom (.add (.n 6692) (.n 6689) (.n 6691)),
    .atom (.load (.n 6693) (.n 14) 4),
    .atom (.mul (.n 6694) (.n 6693) (.n 6539)),
    .atom (.add (.n 6695) (.n 6692) (.n 6694)),
    .atom (.load (.n 6696) (.n 14) 5),
    .atom (.mul (.n 6697) (.n 6696) (.n 6550)),
    .atom (.add (.n 6698) (.n 6695) (.n 6697)),
    .atom (.add (.n 6699) (.n 15) (.n 6698)),
    .atom (.mul (.n 6700) (.n 3187) (.n 6699)),
    .atom (.add (.n 6701) (.n 6677) (.n 6700))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5945, a5946, a5947, a5948, a5949, a5950, a5951, a5952, a5953, a5954, a5955, a5956, a5957, a5958,
    a5959, a5960, a5961, a5962, a5963, a5964, a5965, a5966, a5967, a5968, -⟩ := hs
  have e5945 := tb_loadHolds_unique a5945 (hw 0 (by norm_num))
  have e5949 := tb_loadHolds_unique a5949 (hw 1 (by norm_num))
  have e5954 := tb_loadHolds_unique a5954 (hw 2 (by norm_num))
  have e5957 := tb_loadHolds_unique a5957 (hw 3 (by norm_num))
  have e5960 := tb_loadHolds_unique a5960 (hw 4 (by norm_num))
  have e5963 := tb_loadHolds_unique a5963 (hw 5 (by norm_num))
  have v6425 : σ (.n 6425) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2.1
  have v6447 : σ (.n 6447) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 18) (by norm_num)).2.2.1
  have v6515 : σ (.n 6515) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 23) (by norm_num)).2.2.1
  have v6539 : σ (.n 6539) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 24) (by norm_num)).2.2.1
  have v6550 : σ (.n 6550) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 25) (by norm_num)).2.2.1
  have v6572 : σ (.n 6572) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 27) (by norm_num)).2.2.1
  have hB : σ (.n 6699) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 3], 1)], [([12], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
    simp only [v6572, v6550, v6539, v6515, v6447, v6425, a5966, a5965, a5964, e5963, a5962, a5961, e5960,
      a5959, a5958, e5957, a5956, a5955, e5954, a5953, a5952, a5951, a5950, e5949, a5948,
      a5947, a5946, e5945]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5968, a5967, hB]

set_option maxRecDepth 10000 in
theorem vtB01_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6746) = σ (.n 6701) + σ (.n 3206) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 4], 1)], [([13], 2)], [([5, 8], 1), ([6, 10], 1), ([7, 9], 1)], [([5, 9], 1), ([6, 8], 1), ([6, 10], 1), ([7, 9], 1), ([7, 10], 1)], [([5, 10], 1), ([6, 9], 1), ([7, 8], 1), ([7, 10], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 5969 [
    .atom (.load (.n 6702) (.n 14) 0),
    .atom (.const (.n 6703) (word 2 0 0)),
    .atom (.mul (.n 6704) (.n 6702) (.n 6703)),
    .atom (.mul (.n 6705) (.n 6425) (.n 6458)),
    .atom (.load (.n 6706) (.n 14) 1),
    .atom (.mul (.n 6707) (.n 6706) (.n 6705)),
    .atom (.add (.n 6708) (.n 6704) (.n 6707)),
    .atom (.const (.n 6709) (word 2 0 0)),
    .atom (.mul (.n 6710) (.n 6709) (.n 6596)),
    .atom (.load (.n 6711) (.n 14) 2),
    .atom (.mul (.n 6712) (.n 6711) (.n 6710)),
    .atom (.add (.n 6713) (.n 6708) (.n 6712)),
    .atom (.mul (.n 6714) (.n 6482) (.n 6515)),
    .atom (.mul (.n 6715) (.n 6493) (.n 6550)),
    .atom (.add (.n 6716) (.n 6714) (.n 6715)),
    .atom (.mul (.n 6717) (.n 6504) (.n 6539)),
    .atom (.add (.n 6718) (.n 6716) (.n 6717)),
    .atom (.load (.n 6719) (.n 14) 3),
    .atom (.mul (.n 6720) (.n 6719) (.n 6718)),
    .atom (.add (.n 6721) (.n 6713) (.n 6720)),
    .atom (.mul (.n 6722) (.n 6482) (.n 6539)),
    .atom (.mul (.n 6723) (.n 6493) (.n 6515)),
    .atom (.add (.n 6724) (.n 6722) (.n 6723)),
    .atom (.mul (.n 6725) (.n 6493) (.n 6550)),
    .atom (.add (.n 6726) (.n 6724) (.n 6725)),
    .atom (.mul (.n 6727) (.n 6504) (.n 6539)),
    .atom (.add (.n 6728) (.n 6726) (.n 6727)),
    .atom (.mul (.n 6729) (.n 6504) (.n 6550)),
    .atom (.add (.n 6730) (.n 6728) (.n 6729)),
    .atom (.load (.n 6731) (.n 14) 4),
    .atom (.mul (.n 6732) (.n 6731) (.n 6730)),
    .atom (.add (.n 6733) (.n 6721) (.n 6732)),
    .atom (.mul (.n 6734) (.n 6482) (.n 6550)),
    .atom (.mul (.n 6735) (.n 6493) (.n 6539)),
    .atom (.add (.n 6736) (.n 6734) (.n 6735)),
    .atom (.mul (.n 6737) (.n 6504) (.n 6515)),
    .atom (.add (.n 6738) (.n 6736) (.n 6737)),
    .atom (.mul (.n 6739) (.n 6504) (.n 6550)),
    .atom (.add (.n 6740) (.n 6738) (.n 6739)),
    .atom (.load (.n 6741) (.n 14) 5),
    .atom (.mul (.n 6742) (.n 6741) (.n 6740)),
    .atom (.add (.n 6743) (.n 6733) (.n 6742)),
    .atom (.add (.n 6744) (.n 15) (.n 6743)),
    .atom (.mul (.n 6745) (.n 3206) (.n 6744)),
    .atom (.add (.n 6746) (.n 6701) (.n 6745))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5969, a5970, a5971, a5972, a5973, a5974, a5975, a5976, a5977, a5978, a5979, a5980, a5981, a5982,
    a5983, a5984, a5985, a5986, a5987, a5988, a5989, a5990, a5991, a5992, a5993, a5994, a5995,
    a5996, a5997, a5998, a5999, a6000, a6001, a6002, a6003, a6004, a6005, a6006, a6007, a6008,
    a6009, a6010, a6011, a6012, a6013, -⟩ := hs
  have e5969 := tb_loadHolds_unique a5969 (hw 0 (by norm_num))
  have e5973 := tb_loadHolds_unique a5973 (hw 1 (by norm_num))
  have e5978 := tb_loadHolds_unique a5978 (hw 2 (by norm_num))
  have e5986 := tb_loadHolds_unique a5986 (hw 3 (by norm_num))
  have e5998 := tb_loadHolds_unique a5998 (hw 4 (by norm_num))
  have e6008 := tb_loadHolds_unique a6008 (hw 5 (by norm_num))
  have v6425 : σ (.n 6425) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2.1
  have v6458 : σ (.n 6458) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 19) (by norm_num)).2.2.1
  have v6482 : σ (.n 6482) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 20) (by norm_num)).2.2.1
  have v6493 : σ (.n 6493) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 21) (by norm_num)).2.2.1
  have v6504 : σ (.n 6504) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 22) (by norm_num)).2.2.1
  have v6515 : σ (.n 6515) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 23) (by norm_num)).2.2.1
  have v6539 : σ (.n 6539) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 24) (by norm_num)).2.2.1
  have v6550 : σ (.n 6550) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 25) (by norm_num)).2.2.1
  have v6596 : σ (.n 6596) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 28) (by norm_num)).2.2.1
  have hB : σ (.n 6744) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 4], 1)], [([13], 2)], [([5, 8], 1), ([6, 10], 1), ([7, 9], 1)], [([5, 9], 1), ([6, 8], 1), ([6, 10], 1), ([7, 9], 1), ([7, 10], 1)], [([5, 10], 1), ([6, 9], 1), ([7, 8], 1), ([7, 10], 1)]] := by
    simp only [v6596, v6550, v6539, v6515, v6504, v6493, v6482, v6458, v6425, a6011, a6010, a6009, e6008,
      a6007, a6006, a6005, a6004, a6003, a6002, a6001, a6000, a5999, e5998, a5997, a5996,
      a5995, a5994, a5993, a5992, a5991, a5990, a5989, a5988, a5987, e5986, a5985, a5984,
      a5983, a5982, a5981, a5980, a5979, e5978, a5977, a5976, a5975, a5974, e5973, a5972,
      a5971, a5970, e5969]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6013, a6012, hB]

set_option maxRecDepth 10000 in
theorem vtSide01 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6746) =
      vtSideVal [σ (.n 3130), σ (.n 3149), σ (.n 3168), σ (.n 3187), σ (.n 3206)]
        (σ (.n 15)) W ev vtBTerms01 := by
  rw [vtB01_4 h hw hev, vtB01_3 h hw hev, vtB01_2 h hw hev, vtB01_1 h hw hev, vtB01_0 h hw hev]
  simp only [vtSideVal, vtBTerms01, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtB11_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6756) = σ (.n 4604) * vtBlockVal (σ (.n 15)) W ev
      [[([], 1)], [([0], 1)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6015 [
    .atom (.load (.n 6748) (.n 14) 0),
    .atom (.load (.n 6749) (.n 14) 1),
    .atom (.mul (.n 6750) (.n 6749) (.n 6401)),
    .atom (.add (.n 6751) (.n 6748) (.n 6750)),
    .atom (.load (.n 6752) (.n 14) 2),
    .atom (.mul (.n 6753) (.n 6752) (.n 6425)),
    .atom (.add (.n 6754) (.n 6751) (.n 6753)),
    .atom (.add (.n 6755) (.n 15) (.n 6754)),
    .atom (.mul (.n 6756) (.n 4604) (.n 6755))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6015, a6016, a6017, a6018, a6019, a6020, a6021, a6022, a6023, -⟩ := hs
  have e6015 := tb_loadHolds_unique a6015 (hw 0 (by norm_num))
  have e6016 := tb_loadHolds_unique a6016 (hw 1 (by norm_num))
  have e6019 := tb_loadHolds_unique a6019 (hw 2 (by norm_num))
  have v6401 : σ (.n 6401) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 15) (by norm_num)).2.2.1
  have v6425 : σ (.n 6425) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2.1
  have hB : σ (.n 6755) = vtBlockVal (σ (.n 15)) W ev [[([], 1)], [([0], 1)], [([1], 1)]] := by
    simp only [v6425, v6401, a6022, a6021, a6020, e6019, a6018, a6017, e6016, e6015]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
    ring
  rw [a6023, hB]

set_option maxRecDepth 10000 in
theorem vtB11_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6789) = σ (.n 6756) + σ (.n 4611) * vtBlockVal (σ (.n 15)) W ev
      [[([], 4)], [([0], 1)], [([14], 1)], [([], 2)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 6024 [
    .atom (.load (.n 6757) (.n 14) 0),
    .atom (.const (.n 6758) (word 4 0 0)),
    .atom (.mul (.n 6759) (.n 6757) (.n 6758)),
    .atom (.load (.n 6760) (.n 14) 1),
    .atom (.mul (.n 6761) (.n 6760) (.n 6401)),
    .atom (.add (.n 6762) (.n 6759) (.n 6761)),
    .atom (.load (.n 6763) (.n 14) 2),
    .atom (.mul (.n 6764) (.n 6763) (.n 6607)),
    .atom (.add (.n 6765) (.n 6762) (.n 6764)),
    .atom (.load (.n 6766) (.n 14) 3),
    .atom (.const (.n 6767) (word 2 0 0)),
    .atom (.mul (.n 6768) (.n 6766) (.n 6767)),
    .atom (.add (.n 6769) (.n 6765) (.n 6768)),
    .atom (.load (.n 6770) (.n 14) 4),
    .atom (.mul (.n 6771) (.n 6770) (.n 6436)),
    .atom (.add (.n 6772) (.n 6769) (.n 6771)),
    .atom (.load (.n 6773) (.n 14) 5),
    .atom (.mul (.n 6774) (.n 6773) (.n 6447)),
    .atom (.add (.n 6775) (.n 6772) (.n 6774)),
    .atom (.load (.n 6776) (.n 14) 6),
    .atom (.mul (.n 6777) (.n 6776) (.n 6458)),
    .atom (.add (.n 6778) (.n 6775) (.n 6777)),
    .atom (.load (.n 6779) (.n 14) 7),
    .atom (.const (.n 6780) (word 0 0 0)),
    .atom (.mul (.n 6781) (.n 6779) (.n 6780)),
    .atom (.add (.n 6782) (.n 6778) (.n 6781)),
    .atom (.load (.n 6783) (.n 14) 8),
    .atom (.const (.n 6784) (word 0 0 0)),
    .atom (.mul (.n 6785) (.n 6783) (.n 6784)),
    .atom (.add (.n 6786) (.n 6782) (.n 6785)),
    .atom (.add (.n 6787) (.n 15) (.n 6786)),
    .atom (.mul (.n 6788) (.n 4611) (.n 6787)),
    .atom (.add (.n 6789) (.n 6756) (.n 6788))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6024, a6025, a6026, a6027, a6028, a6029, a6030, a6031, a6032, a6033, a6034, a6035, a6036, a6037,
    a6038, a6039, a6040, a6041, a6042, a6043, a6044, a6045, a6046, a6047, a6048, a6049, a6050,
    a6051, a6052, a6053, a6054, a6055, a6056, -⟩ := hs
  have e6024 := tb_loadHolds_unique a6024 (hw 0 (by norm_num))
  have e6027 := tb_loadHolds_unique a6027 (hw 1 (by norm_num))
  have e6030 := tb_loadHolds_unique a6030 (hw 2 (by norm_num))
  have e6033 := tb_loadHolds_unique a6033 (hw 3 (by norm_num))
  have e6037 := tb_loadHolds_unique a6037 (hw 4 (by norm_num))
  have e6040 := tb_loadHolds_unique a6040 (hw 5 (by norm_num))
  have e6043 := tb_loadHolds_unique a6043 (hw 6 (by norm_num))
  have e6046 := tb_loadHolds_unique a6046 (hw 7 (by norm_num))
  have e6050 := tb_loadHolds_unique a6050 (hw 8 (by norm_num))
  have v6401 : σ (.n 6401) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 15) (by norm_num)).2.2.1
  have v6436 : σ (.n 6436) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 17) (by norm_num)).2.2.1
  have v6447 : σ (.n 6447) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 18) (by norm_num)).2.2.1
  have v6458 : σ (.n 6458) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 19) (by norm_num)).2.2.1
  have v6607 : σ (.n 6607) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 29) (by norm_num)).2.2.1
  have hB : σ (.n 6787) = vtBlockVal (σ (.n 15)) W ev [[([], 4)], [([0], 1)], [([14], 1)], [([], 2)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v6607, v6458, v6447, v6436, v6401, a6054, a6053, a6052, a6051, e6050, a6049, a6048, a6047,
      e6046, a6045, a6044, e6043, a6042, a6041, e6040, a6039, a6038, e6037, a6036, a6035,
      a6034, e6033, a6032, a6031, e6030, a6029, a6028, e6027, a6026, a6025, e6024]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a6056, a6055, hB]

set_option maxRecDepth 10000 in
theorem vtB11_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6811) = σ (.n 6789) + σ (.n 4618) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 2], 1)], [([11], 1)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6057 [
    .atom (.load (.n 6790) (.n 14) 0),
    .atom (.const (.n 6791) (word 2 0 0)),
    .atom (.mul (.n 6792) (.n 6790) (.n 6791)),
    .atom (.mul (.n 6793) (.n 6425) (.n 6436)),
    .atom (.load (.n 6794) (.n 14) 1),
    .atom (.mul (.n 6795) (.n 6794) (.n 6793)),
    .atom (.add (.n 6796) (.n 6792) (.n 6795)),
    .atom (.load (.n 6797) (.n 14) 2),
    .atom (.mul (.n 6798) (.n 6797) (.n 6561)),
    .atom (.add (.n 6799) (.n 6796) (.n 6798)),
    .atom (.load (.n 6800) (.n 14) 3),
    .atom (.mul (.n 6801) (.n 6800) (.n 6482)),
    .atom (.add (.n 6802) (.n 6799) (.n 6801)),
    .atom (.load (.n 6803) (.n 14) 4),
    .atom (.mul (.n 6804) (.n 6803) (.n 6493)),
    .atom (.add (.n 6805) (.n 6802) (.n 6804)),
    .atom (.load (.n 6806) (.n 14) 5),
    .atom (.mul (.n 6807) (.n 6806) (.n 6504)),
    .atom (.add (.n 6808) (.n 6805) (.n 6807)),
    .atom (.add (.n 6809) (.n 15) (.n 6808)),
    .atom (.mul (.n 6810) (.n 4618) (.n 6809)),
    .atom (.add (.n 6811) (.n 6789) (.n 6810))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6057, a6058, a6059, a6060, a6061, a6062, a6063, a6064, a6065, a6066, a6067, a6068, a6069, a6070,
    a6071, a6072, a6073, a6074, a6075, a6076, a6077, a6078, -⟩ := hs
  have e6057 := tb_loadHolds_unique a6057 (hw 0 (by norm_num))
  have e6061 := tb_loadHolds_unique a6061 (hw 1 (by norm_num))
  have e6064 := tb_loadHolds_unique a6064 (hw 2 (by norm_num))
  have e6067 := tb_loadHolds_unique a6067 (hw 3 (by norm_num))
  have e6070 := tb_loadHolds_unique a6070 (hw 4 (by norm_num))
  have e6073 := tb_loadHolds_unique a6073 (hw 5 (by norm_num))
  have v6425 : σ (.n 6425) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2.1
  have v6436 : σ (.n 6436) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 17) (by norm_num)).2.2.1
  have v6482 : σ (.n 6482) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 20) (by norm_num)).2.2.1
  have v6493 : σ (.n 6493) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 21) (by norm_num)).2.2.1
  have v6504 : σ (.n 6504) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 22) (by norm_num)).2.2.1
  have v6561 : σ (.n 6561) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 26) (by norm_num)).2.2.1
  have hB : σ (.n 6809) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 2], 1)], [([11], 1)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
    simp only [v6561, v6504, v6493, v6482, v6436, v6425, a6076, a6075, a6074, e6073, a6072, a6071, e6070,
      a6069, a6068, e6067, a6066, a6065, e6064, a6063, a6062, e6061, a6060, a6059, a6058,
      e6057]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6078, a6077, hB]

set_option maxRecDepth 10000 in
theorem vtB11_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6833) = σ (.n 6811) + σ (.n 4625) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 3], 1)], [([12], 1)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6079 [
    .atom (.load (.n 6812) (.n 14) 0),
    .atom (.const (.n 6813) (word 2 0 0)),
    .atom (.mul (.n 6814) (.n 6812) (.n 6813)),
    .atom (.mul (.n 6815) (.n 6425) (.n 6447)),
    .atom (.load (.n 6816) (.n 14) 1),
    .atom (.mul (.n 6817) (.n 6816) (.n 6815)),
    .atom (.add (.n 6818) (.n 6814) (.n 6817)),
    .atom (.load (.n 6819) (.n 14) 2),
    .atom (.mul (.n 6820) (.n 6819) (.n 6572)),
    .atom (.add (.n 6821) (.n 6818) (.n 6820)),
    .atom (.load (.n 6822) (.n 14) 3),
    .atom (.mul (.n 6823) (.n 6822) (.n 6515)),
    .atom (.add (.n 6824) (.n 6821) (.n 6823)),
    .atom (.load (.n 6825) (.n 14) 4),
    .atom (.mul (.n 6826) (.n 6825) (.n 6539)),
    .atom (.add (.n 6827) (.n 6824) (.n 6826)),
    .atom (.load (.n 6828) (.n 14) 5),
    .atom (.mul (.n 6829) (.n 6828) (.n 6550)),
    .atom (.add (.n 6830) (.n 6827) (.n 6829)),
    .atom (.add (.n 6831) (.n 15) (.n 6830)),
    .atom (.mul (.n 6832) (.n 4625) (.n 6831)),
    .atom (.add (.n 6833) (.n 6811) (.n 6832))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6079, a6080, a6081, a6082, a6083, a6084, a6085, a6086, a6087, a6088, a6089, a6090, a6091, a6092,
    a6093, a6094, a6095, a6096, a6097, a6098, a6099, a6100, -⟩ := hs
  have e6079 := tb_loadHolds_unique a6079 (hw 0 (by norm_num))
  have e6083 := tb_loadHolds_unique a6083 (hw 1 (by norm_num))
  have e6086 := tb_loadHolds_unique a6086 (hw 2 (by norm_num))
  have e6089 := tb_loadHolds_unique a6089 (hw 3 (by norm_num))
  have e6092 := tb_loadHolds_unique a6092 (hw 4 (by norm_num))
  have e6095 := tb_loadHolds_unique a6095 (hw 5 (by norm_num))
  have v6425 : σ (.n 6425) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2.1
  have v6447 : σ (.n 6447) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 18) (by norm_num)).2.2.1
  have v6515 : σ (.n 6515) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 23) (by norm_num)).2.2.1
  have v6539 : σ (.n 6539) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 24) (by norm_num)).2.2.1
  have v6550 : σ (.n 6550) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 25) (by norm_num)).2.2.1
  have v6572 : σ (.n 6572) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 27) (by norm_num)).2.2.1
  have hB : σ (.n 6831) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 3], 1)], [([12], 1)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
    simp only [v6572, v6550, v6539, v6515, v6447, v6425, a6098, a6097, a6096, e6095, a6094, a6093, e6092,
      a6091, a6090, e6089, a6088, a6087, e6086, a6085, a6084, e6083, a6082, a6081, a6080,
      e6079]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6100, a6099, hB]

set_option maxRecDepth 10000 in
theorem vtB11_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6876) = σ (.n 6833) + σ (.n 4632) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 4], 1)], [([13], 1)], [([5, 8], 1), ([6, 10], 1), ([7, 9], 1)], [([5, 9], 1), ([6, 8], 1), ([6, 10], 1), ([7, 9], 1), ([7, 10], 1)], [([5, 10], 1), ([6, 9], 1), ([7, 8], 1), ([7, 10], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6101 [
    .atom (.load (.n 6834) (.n 14) 0),
    .atom (.const (.n 6835) (word 2 0 0)),
    .atom (.mul (.n 6836) (.n 6834) (.n 6835)),
    .atom (.mul (.n 6837) (.n 6425) (.n 6458)),
    .atom (.load (.n 6838) (.n 14) 1),
    .atom (.mul (.n 6839) (.n 6838) (.n 6837)),
    .atom (.add (.n 6840) (.n 6836) (.n 6839)),
    .atom (.load (.n 6841) (.n 14) 2),
    .atom (.mul (.n 6842) (.n 6841) (.n 6596)),
    .atom (.add (.n 6843) (.n 6840) (.n 6842)),
    .atom (.mul (.n 6844) (.n 6482) (.n 6515)),
    .atom (.mul (.n 6845) (.n 6493) (.n 6550)),
    .atom (.add (.n 6846) (.n 6844) (.n 6845)),
    .atom (.mul (.n 6847) (.n 6504) (.n 6539)),
    .atom (.add (.n 6848) (.n 6846) (.n 6847)),
    .atom (.load (.n 6849) (.n 14) 3),
    .atom (.mul (.n 6850) (.n 6849) (.n 6848)),
    .atom (.add (.n 6851) (.n 6843) (.n 6850)),
    .atom (.mul (.n 6852) (.n 6482) (.n 6539)),
    .atom (.mul (.n 6853) (.n 6493) (.n 6515)),
    .atom (.add (.n 6854) (.n 6852) (.n 6853)),
    .atom (.mul (.n 6855) (.n 6493) (.n 6550)),
    .atom (.add (.n 6856) (.n 6854) (.n 6855)),
    .atom (.mul (.n 6857) (.n 6504) (.n 6539)),
    .atom (.add (.n 6858) (.n 6856) (.n 6857)),
    .atom (.mul (.n 6859) (.n 6504) (.n 6550)),
    .atom (.add (.n 6860) (.n 6858) (.n 6859)),
    .atom (.load (.n 6861) (.n 14) 4),
    .atom (.mul (.n 6862) (.n 6861) (.n 6860)),
    .atom (.add (.n 6863) (.n 6851) (.n 6862)),
    .atom (.mul (.n 6864) (.n 6482) (.n 6550)),
    .atom (.mul (.n 6865) (.n 6493) (.n 6539)),
    .atom (.add (.n 6866) (.n 6864) (.n 6865)),
    .atom (.mul (.n 6867) (.n 6504) (.n 6515)),
    .atom (.add (.n 6868) (.n 6866) (.n 6867)),
    .atom (.mul (.n 6869) (.n 6504) (.n 6550)),
    .atom (.add (.n 6870) (.n 6868) (.n 6869)),
    .atom (.load (.n 6871) (.n 14) 5),
    .atom (.mul (.n 6872) (.n 6871) (.n 6870)),
    .atom (.add (.n 6873) (.n 6863) (.n 6872)),
    .atom (.add (.n 6874) (.n 15) (.n 6873)),
    .atom (.mul (.n 6875) (.n 4632) (.n 6874)),
    .atom (.add (.n 6876) (.n 6833) (.n 6875))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6101, a6102, a6103, a6104, a6105, a6106, a6107, a6108, a6109, a6110, a6111, a6112, a6113, a6114,
    a6115, a6116, a6117, a6118, a6119, a6120, a6121, a6122, a6123, a6124, a6125, a6126, a6127,
    a6128, a6129, a6130, a6131, a6132, a6133, a6134, a6135, a6136, a6137, a6138, a6139, a6140,
    a6141, a6142, a6143, -⟩ := hs
  have e6101 := tb_loadHolds_unique a6101 (hw 0 (by norm_num))
  have e6105 := tb_loadHolds_unique a6105 (hw 1 (by norm_num))
  have e6108 := tb_loadHolds_unique a6108 (hw 2 (by norm_num))
  have e6116 := tb_loadHolds_unique a6116 (hw 3 (by norm_num))
  have e6128 := tb_loadHolds_unique a6128 (hw 4 (by norm_num))
  have e6138 := tb_loadHolds_unique a6138 (hw 5 (by norm_num))
  have v6425 : σ (.n 6425) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2.1
  have v6458 : σ (.n 6458) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 19) (by norm_num)).2.2.1
  have v6482 : σ (.n 6482) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 20) (by norm_num)).2.2.1
  have v6493 : σ (.n 6493) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 21) (by norm_num)).2.2.1
  have v6504 : σ (.n 6504) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 22) (by norm_num)).2.2.1
  have v6515 : σ (.n 6515) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 23) (by norm_num)).2.2.1
  have v6539 : σ (.n 6539) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 24) (by norm_num)).2.2.1
  have v6550 : σ (.n 6550) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 25) (by norm_num)).2.2.1
  have v6596 : σ (.n 6596) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 28) (by norm_num)).2.2.1
  have hB : σ (.n 6874) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 4], 1)], [([13], 1)], [([5, 8], 1), ([6, 10], 1), ([7, 9], 1)], [([5, 9], 1), ([6, 8], 1), ([6, 10], 1), ([7, 9], 1), ([7, 10], 1)], [([5, 10], 1), ([6, 9], 1), ([7, 8], 1), ([7, 10], 1)]] := by
    simp only [v6596, v6550, v6539, v6515, v6504, v6493, v6482, v6458, v6425, a6141, a6140, a6139, e6138,
      a6137, a6136, a6135, a6134, a6133, a6132, a6131, a6130, a6129, e6128, a6127, a6126,
      a6125, a6124, a6123, a6122, a6121, a6120, a6119, a6118, a6117, e6116, a6115, a6114,
      a6113, a6112, a6111, a6110, a6109, e6108, a6107, a6106, e6105, a6104, a6103, a6102,
      e6101]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6143, a6142, hB]

set_option maxRecDepth 10000 in
theorem vtSide11 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6876) =
      vtSideVal [σ (.n 4604), σ (.n 4611), σ (.n 4618), σ (.n 4625), σ (.n 4632)]
        (σ (.n 15)) W ev vtBTerms11 := by
  rw [vtB11_4 h hw hev, vtB11_3 h hw hev, vtB11_2 h hw hev, vtB11_1 h hw hev, vtB11_0 h hw hev]
  simp only [vtSideVal, vtBTerms11, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide21 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 6885) =
      vtSideVal [σ (.n 5002), σ (.n 5021), σ (.n 5040), σ (.n 5059)]
        (0) (fun _ ↦ 1) ev vtBTerms21 := by
  obtain ⟨_, hs⟩ := h.slice 6146 [
    .atom (.mul (.n 6879) (.n 5002) (.n 6561)),
    .atom (.mul (.n 6880) (.n 5021) (.n 6572)),
    .atom (.add (.n 6881) (.n 6879) (.n 6880)),
    .atom (.mul (.n 6882) (.n 5040) (.n 6596)),
    .atom (.add (.n 6883) (.n 6881) (.n 6882)),
    .atom (.mul (.n 6884) (.n 5059) (.n 6607)),
    .atom (.add (.n 6885) (.n 6883) (.n 6884))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6146, a6147, a6148, a6149, a6150, a6151, a6152, -⟩ := hs
  have v6561 : σ (.n 6561) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 26) (by norm_num)).2.2.1
  have v6572 : σ (.n 6572) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 27) (by norm_num)).2.2.1
  have v6596 : σ (.n 6596) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 28) (by norm_num)).2.2.1
  have v6607 : σ (.n 6607) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 29) (by norm_num)).2.2.1
  rw [a6152, a6150, a6148, a6146, a6147, a6149, a6151, v6561, v6572, v6596, v6607]
  simp only [vtSideVal, vtBTerms21, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
