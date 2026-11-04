/-
  LeanVM.Guest.B1.Tables.Vt.FormsT5a

  Table 5's blocks' values on the push side, from the guest's statements.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsDiff
public import LeanVM.Guest.B1.Tables.Vt.PullSels
public import LeanVM.Guest.B1.Tables.Vt.Pi

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB05_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5710) = σ (.n 1143) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5132 [
    .atom (.load (.n 5700) (.n 13) 0),
    .atom (.const (.n 5701) (word 2 0 0)),
    .atom (.mul (.n 5702) (.n 5701) (.n 4421)),
    .atom (.load (.n 5703) (.n 13) 1),
    .atom (.mul (.n 5704) (.n 5703) (.n 5702)),
    .atom (.add (.n 5705) (.n 5700) (.n 5704)),
    .atom (.load (.n 5706) (.n 13) 2),
    .atom (.mul (.n 5707) (.n 5706) (.n 4445)),
    .atom (.add (.n 5708) (.n 5705) (.n 5707)),
    .atom (.add (.n 5709) (.n 14) (.n 5708)),
    .atom (.mul (.n 5710) (.n 1143) (.n 5709))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5132, a5133, a5134, a5135, a5136, a5137, a5138, a5139, a5140, a5141, a5142, -⟩ := hs
  have e5132 := tb_loadHolds_unique a5132 (hw 0 (by norm_num))
  have e5135 := tb_loadHolds_unique a5135 (hw 1 (by norm_num))
  have e5138 := tb_loadHolds_unique a5138 (hw 2 (by norm_num))
  have v4421 : σ (.n 4421) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have hB : σ (.n 5709) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v4445, v4421, a5141, a5140, a5139, e5138, a5137, a5136, e5135, a5134, a5133, e5132]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5142, hB]

set_option maxRecDepth 10000 in
theorem vtB05_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5758) = σ (.n 5710) + σ (.n 1152) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([89], 2)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5143 [
    .atom (.load (.n 5711) (.n 13) 0),
    .atom (.const (.n 5712) (word 4 0 0)),
    .atom (.mul (.n 5713) (.n 5711) (.n 5712)),
    .atom (.load (.n 5714) (.n 13) 1),
    .atom (.mul (.n 5715) (.n 5714) (.n 4421)),
    .atom (.add (.n 5716) (.n 5713) (.n 5715)),
    .atom (.const (.n 5717) (word 2 0 0)),
    .atom (.mul (.n 5718) (.n 5717) (.n 5699)),
    .atom (.load (.n 5719) (.n 13) 2),
    .atom (.mul (.n 5720) (.n 5719) (.n 5718)),
    .atom (.add (.n 5721) (.n 5716) (.n 5720)),
    .atom (.load (.n 5722) (.n 13) 3),
    .atom (.const (.n 5723) (word 32 0 0)),
    .atom (.mul (.n 5724) (.n 5722) (.n 5723)),
    .atom (.add (.n 5725) (.n 5721) (.n 5724)),
    .atom (.load (.n 5726) (.n 13) 4),
    .atom (.mul (.n 5727) (.n 5726) (.n 4456)),
    .atom (.add (.n 5728) (.n 5725) (.n 5727)),
    .atom (.load (.n 5729) (.n 13) 5),
    .atom (.mul (.n 5730) (.n 5729) (.n 4467)),
    .atom (.add (.n 5731) (.n 5728) (.n 5730)),
    .atom (.load (.n 5732) (.n 13) 6),
    .atom (.mul (.n 5733) (.n 5732) (.n 4478)),
    .atom (.add (.n 5734) (.n 5731) (.n 5733)),
    .atom (.load (.n 5735) (.n 13) 7),
    .atom (.mul (.n 5736) (.n 5735) (.n 4502)),
    .atom (.add (.n 5737) (.n 5734) (.n 5736)),
    .atom (.load (.n 5738) (.n 13) 8),
    .atom (.mul (.n 5739) (.n 5738) (.n 4513)),
    .atom (.add (.n 5740) (.n 5737) (.n 5739)),
    .atom (.load (.n 5741) (.n 13) 9),
    .atom (.mul (.n 5742) (.n 5741) (.n 4524)),
    .atom (.add (.n 5743) (.n 5740) (.n 5742)),
    .atom (.load (.n 5744) (.n 13) 10),
    .atom (.mul (.n 5745) (.n 5744) (.n 4535)),
    .atom (.add (.n 5746) (.n 5743) (.n 5745)),
    .atom (.load (.n 5747) (.n 13) 11),
    .atom (.mul (.n 5748) (.n 5747) (.n 4559)),
    .atom (.add (.n 5749) (.n 5746) (.n 5748)),
    .atom (.load (.n 5750) (.n 13) 12),
    .atom (.mul (.n 5751) (.n 5750) (.n 4570)),
    .atom (.add (.n 5752) (.n 5749) (.n 5751)),
    .atom (.load (.n 5753) (.n 13) 13),
    .atom (.mul (.n 5754) (.n 5753) (.n 4581)),
    .atom (.add (.n 5755) (.n 5752) (.n 5754)),
    .atom (.add (.n 5756) (.n 14) (.n 5755)),
    .atom (.mul (.n 5757) (.n 1152) (.n 5756)),
    .atom (.add (.n 5758) (.n 5710) (.n 5757))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5143, a5144, a5145, a5146, a5147, a5148, a5149, a5150, a5151, a5152, a5153, a5154, a5155, a5156,
    a5157, a5158, a5159, a5160, a5161, a5162, a5163, a5164, a5165, a5166, a5167, a5168, a5169,
    a5170, a5171, a5172, a5173, a5174, a5175, a5176, a5177, a5178, a5179, a5180, a5181, a5182,
    a5183, a5184, a5185, a5186, a5187, a5188, a5189, a5190, -⟩ := hs
  have e5143 := tb_loadHolds_unique a5143 (hw 0 (by norm_num))
  have e5146 := tb_loadHolds_unique a5146 (hw 1 (by norm_num))
  have e5151 := tb_loadHolds_unique a5151 (hw 2 (by norm_num))
  have e5154 := tb_loadHolds_unique a5154 (hw 3 (by norm_num))
  have e5158 := tb_loadHolds_unique a5158 (hw 4 (by norm_num))
  have e5161 := tb_loadHolds_unique a5161 (hw 5 (by norm_num))
  have e5164 := tb_loadHolds_unique a5164 (hw 6 (by norm_num))
  have e5167 := tb_loadHolds_unique a5167 (hw 7 (by norm_num))
  have e5170 := tb_loadHolds_unique a5170 (hw 8 (by norm_num))
  have e5173 := tb_loadHolds_unique a5173 (hw 9 (by norm_num))
  have e5176 := tb_loadHolds_unique a5176 (hw 10 (by norm_num))
  have e5179 := tb_loadHolds_unique a5179 (hw 11 (by norm_num))
  have e5182 := tb_loadHolds_unique a5182 (hw 12 (by norm_num))
  have e5185 := tb_loadHolds_unique a5185 (hw 13 (by norm_num))
  have v4421 : σ (.n 4421) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have v4456 : σ (.n 4456) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 69) (by norm_num)).2.2
  have v4467 : σ (.n 4467) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4478 : σ (.n 4478) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4502 : σ (.n 4502) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4513 : σ (.n 4513) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 73) (by norm_num)).2.2
  have v4524 : σ (.n 4524) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4535 : σ (.n 4535) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 75) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v4570 : σ (.n 4570) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4581 : σ (.n 4581) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 78) (by norm_num)).2.2
  have v5699 : σ (.n 5699) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_eval h (k := 156) (by norm_num)).2.2
  have hB : σ (.n 5756) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([89], 2)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)]] := by
    simp only [v5699, v4581, v4570, v4559, v4535, v4524, v4513, v4502, v4478, v4467, v4456, v4421, a5188,
      a5187, a5186, e5185, a5184, a5183, e5182, a5181, a5180, e5179, a5178, a5177, e5176,
      a5175, a5174, e5173, a5172, a5171, e5170, a5169, a5168, e5167, a5166, a5165, e5164,
      a5163, a5162, e5161, a5160, a5159, e5158, a5157, a5156, a5155, e5154, a5153, a5152,
      e5151, a5150, a5149, a5148, a5147, e5146, a5145, a5144, e5143]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5190, a5189, hB]

set_option maxRecDepth 10000 in
theorem vtB05_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5791) = σ (.n 5758) + σ (.n 1161) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([63], 2)], [([13], 1), ([10, 13], 1), ([10, 12], 1)], [([14], 1), ([10, 14], 1), ([10, 13], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5191 [
    .atom (.load (.n 5759) (.n 13) 0),
    .atom (.const (.n 5760) (word 2 0 0)),
    .atom (.mul (.n 5761) (.n 5759) (.n 5760)),
    .atom (.mul (.n 5762) (.n 4445) (.n 4456)),
    .atom (.load (.n 5763) (.n 13) 1),
    .atom (.mul (.n 5764) (.n 5763) (.n 5762)),
    .atom (.add (.n 5765) (.n 5761) (.n 5764)),
    .atom (.const (.n 5766) (word 2 0 0)),
    .atom (.mul (.n 5767) (.n 5766) (.n 5322)),
    .atom (.load (.n 5768) (.n 13) 2),
    .atom (.mul (.n 5769) (.n 5768) (.n 5767)),
    .atom (.add (.n 5770) (.n 5765) (.n 5769)),
    .atom (.mul (.n 5771) (.n 4570) (.n 4616)),
    .atom (.add (.n 5772) (.n 4616) (.n 5771)),
    .atom (.mul (.n 5773) (.n 4570) (.n 4592)),
    .atom (.add (.n 5774) (.n 5772) (.n 5773)),
    .atom (.load (.n 5775) (.n 13) 3),
    .atom (.mul (.n 5776) (.n 5775) (.n 5774)),
    .atom (.add (.n 5777) (.n 5770) (.n 5776)),
    .atom (.mul (.n 5778) (.n 4570) (.n 4627)),
    .atom (.add (.n 5779) (.n 4627) (.n 5778)),
    .atom (.mul (.n 5780) (.n 4570) (.n 4616)),
    .atom (.add (.n 5781) (.n 5779) (.n 5780)),
    .atom (.load (.n 5782) (.n 13) 4),
    .atom (.mul (.n 5783) (.n 5782) (.n 5781)),
    .atom (.add (.n 5784) (.n 5777) (.n 5783)),
    .atom (.load (.n 5785) (.n 13) 5),
    .atom (.const (.n 5786) (word 0 0 0)),
    .atom (.mul (.n 5787) (.n 5785) (.n 5786)),
    .atom (.add (.n 5788) (.n 5784) (.n 5787)),
    .atom (.add (.n 5789) (.n 14) (.n 5788)),
    .atom (.mul (.n 5790) (.n 1161) (.n 5789)),
    .atom (.add (.n 5791) (.n 5758) (.n 5790))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5191, a5192, a5193, a5194, a5195, a5196, a5197, a5198, a5199, a5200, a5201, a5202, a5203, a5204,
    a5205, a5206, a5207, a5208, a5209, a5210, a5211, a5212, a5213, a5214, a5215, a5216, a5217,
    a5218, a5219, a5220, a5221, a5222, a5223, -⟩ := hs
  have e5191 := tb_loadHolds_unique a5191 (hw 0 (by norm_num))
  have e5195 := tb_loadHolds_unique a5195 (hw 1 (by norm_num))
  have e5200 := tb_loadHolds_unique a5200 (hw 2 (by norm_num))
  have e5207 := tb_loadHolds_unique a5207 (hw 3 (by norm_num))
  have e5214 := tb_loadHolds_unique a5214 (hw 4 (by norm_num))
  have e5217 := tb_loadHolds_unique a5217 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4456 : σ (.n 4456) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 69) (by norm_num)).2.2
  have v4570 : σ (.n 4570) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4592 : σ (.n 4592) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 79) (by norm_num)).2.2
  have v4616 : σ (.n 4616) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v4627 : σ (.n 4627) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 81) (by norm_num)).2.2
  have v5322 : σ (.n 5322) = ev 63 := by
    rw [← hev 63 (by norm_num)]; exact (vt_eval h (k := 130) (by norm_num)).2.2
  have hB : σ (.n 5789) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([63], 2)], [([13], 1), ([10, 13], 1), ([10, 12], 1)], [([14], 1), ([10, 14], 1), ([10, 13], 1)], [([], 0)]] := by
    simp only [v5322, v4627, v4616, v4592, v4570, v4456, v4445, a5221, a5220, a5219, a5218, e5217, a5216,
      a5215, e5214, a5213, a5212, a5211, a5210, a5209, a5208, e5207, a5206, a5205, a5204,
      a5203, a5202, a5201, e5200, a5199, a5198, a5197, a5196, e5195, a5194, a5193, a5192,
      e5191]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5223, a5222, hB]

set_option maxRecDepth 10000 in
theorem vtB05_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5824) = σ (.n 5791) + σ (.n 1170) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([64], 2)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5224 [
    .atom (.load (.n 5792) (.n 13) 0),
    .atom (.const (.n 5793) (word 2 0 0)),
    .atom (.mul (.n 5794) (.n 5792) (.n 5793)),
    .atom (.mul (.n 5795) (.n 4445) (.n 4467)),
    .atom (.load (.n 5796) (.n 13) 1),
    .atom (.mul (.n 5797) (.n 5796) (.n 5795)),
    .atom (.add (.n 5798) (.n 5794) (.n 5797)),
    .atom (.const (.n 5799) (word 2 0 0)),
    .atom (.mul (.n 5800) (.n 5799) (.n 5333)),
    .atom (.load (.n 5801) (.n 13) 2),
    .atom (.mul (.n 5802) (.n 5801) (.n 5800)),
    .atom (.add (.n 5803) (.n 5798) (.n 5802)),
    .atom (.mul (.n 5804) (.n 4570) (.n 4638)),
    .atom (.add (.n 5805) (.n 4638) (.n 5804)),
    .atom (.mul (.n 5806) (.n 4570) (.n 4627)),
    .atom (.add (.n 5807) (.n 5805) (.n 5806)),
    .atom (.load (.n 5808) (.n 13) 3),
    .atom (.mul (.n 5809) (.n 5808) (.n 5807)),
    .atom (.add (.n 5810) (.n 5803) (.n 5809)),
    .atom (.mul (.n 5811) (.n 4570) (.n 4649)),
    .atom (.add (.n 5812) (.n 4649) (.n 5811)),
    .atom (.mul (.n 5813) (.n 4570) (.n 4638)),
    .atom (.add (.n 5814) (.n 5812) (.n 5813)),
    .atom (.load (.n 5815) (.n 13) 4),
    .atom (.mul (.n 5816) (.n 5815) (.n 5814)),
    .atom (.add (.n 5817) (.n 5810) (.n 5816)),
    .atom (.load (.n 5818) (.n 13) 5),
    .atom (.const (.n 5819) (word 0 0 0)),
    .atom (.mul (.n 5820) (.n 5818) (.n 5819)),
    .atom (.add (.n 5821) (.n 5817) (.n 5820)),
    .atom (.add (.n 5822) (.n 14) (.n 5821)),
    .atom (.mul (.n 5823) (.n 1170) (.n 5822)),
    .atom (.add (.n 5824) (.n 5791) (.n 5823))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5224, a5225, a5226, a5227, a5228, a5229, a5230, a5231, a5232, a5233, a5234, a5235, a5236, a5237,
    a5238, a5239, a5240, a5241, a5242, a5243, a5244, a5245, a5246, a5247, a5248, a5249, a5250,
    a5251, a5252, a5253, a5254, a5255, a5256, -⟩ := hs
  have e5224 := tb_loadHolds_unique a5224 (hw 0 (by norm_num))
  have e5228 := tb_loadHolds_unique a5228 (hw 1 (by norm_num))
  have e5233 := tb_loadHolds_unique a5233 (hw 2 (by norm_num))
  have e5240 := tb_loadHolds_unique a5240 (hw 3 (by norm_num))
  have e5247 := tb_loadHolds_unique a5247 (hw 4 (by norm_num))
  have e5250 := tb_loadHolds_unique a5250 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4467 : σ (.n 4467) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4570 : σ (.n 4570) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4627 : σ (.n 4627) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 81) (by norm_num)).2.2
  have v4638 : σ (.n 4638) = ev 15 := by
    rw [← hev 15 (by norm_num)]; exact (vt_eval h (k := 82) (by norm_num)).2.2
  have v4649 : σ (.n 4649) = ev 16 := by
    rw [← hev 16 (by norm_num)]; exact (vt_eval h (k := 83) (by norm_num)).2.2
  have v5333 : σ (.n 5333) = ev 64 := by
    rw [← hev 64 (by norm_num)]; exact (vt_eval h (k := 131) (by norm_num)).2.2
  have hB : σ (.n 5822) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([64], 2)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)], [([], 0)]] := by
    simp only [v5333, v4649, v4638, v4627, v4570, v4467, v4445, a5254, a5253, a5252, a5251, e5250, a5249,
      a5248, e5247, a5246, a5245, a5244, a5243, a5242, a5241, e5240, a5239, a5238, a5237,
      a5236, a5235, a5234, e5233, a5232, a5231, a5230, a5229, e5228, a5227, a5226, a5225,
      e5224]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5256, a5255, hB]

set_option maxRecDepth 10000 in
theorem vtB05_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5857) = σ (.n 5824) + σ (.n 1179) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([65], 2)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5257 [
    .atom (.load (.n 5825) (.n 13) 0),
    .atom (.const (.n 5826) (word 2 0 0)),
    .atom (.mul (.n 5827) (.n 5825) (.n 5826)),
    .atom (.mul (.n 5828) (.n 4445) (.n 4478)),
    .atom (.load (.n 5829) (.n 13) 1),
    .atom (.mul (.n 5830) (.n 5829) (.n 5828)),
    .atom (.add (.n 5831) (.n 5827) (.n 5830)),
    .atom (.const (.n 5832) (word 2 0 0)),
    .atom (.mul (.n 5833) (.n 5832) (.n 5357)),
    .atom (.load (.n 5834) (.n 13) 2),
    .atom (.mul (.n 5835) (.n 5834) (.n 5833)),
    .atom (.add (.n 5836) (.n 5831) (.n 5835)),
    .atom (.mul (.n 5837) (.n 4570) (.n 4673)),
    .atom (.add (.n 5838) (.n 4673) (.n 5837)),
    .atom (.mul (.n 5839) (.n 4570) (.n 4649)),
    .atom (.add (.n 5840) (.n 5838) (.n 5839)),
    .atom (.load (.n 5841) (.n 13) 3),
    .atom (.mul (.n 5842) (.n 5841) (.n 5840)),
    .atom (.add (.n 5843) (.n 5836) (.n 5842)),
    .atom (.mul (.n 5844) (.n 4570) (.n 4684)),
    .atom (.add (.n 5845) (.n 4684) (.n 5844)),
    .atom (.mul (.n 5846) (.n 4570) (.n 4673)),
    .atom (.add (.n 5847) (.n 5845) (.n 5846)),
    .atom (.load (.n 5848) (.n 13) 4),
    .atom (.mul (.n 5849) (.n 5848) (.n 5847)),
    .atom (.add (.n 5850) (.n 5843) (.n 5849)),
    .atom (.load (.n 5851) (.n 13) 5),
    .atom (.const (.n 5852) (word 0 0 0)),
    .atom (.mul (.n 5853) (.n 5851) (.n 5852)),
    .atom (.add (.n 5854) (.n 5850) (.n 5853)),
    .atom (.add (.n 5855) (.n 14) (.n 5854)),
    .atom (.mul (.n 5856) (.n 1179) (.n 5855)),
    .atom (.add (.n 5857) (.n 5824) (.n 5856))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5257, a5258, a5259, a5260, a5261, a5262, a5263, a5264, a5265, a5266, a5267, a5268, a5269, a5270,
    a5271, a5272, a5273, a5274, a5275, a5276, a5277, a5278, a5279, a5280, a5281, a5282, a5283,
    a5284, a5285, a5286, a5287, a5288, a5289, -⟩ := hs
  have e5257 := tb_loadHolds_unique a5257 (hw 0 (by norm_num))
  have e5261 := tb_loadHolds_unique a5261 (hw 1 (by norm_num))
  have e5266 := tb_loadHolds_unique a5266 (hw 2 (by norm_num))
  have e5273 := tb_loadHolds_unique a5273 (hw 3 (by norm_num))
  have e5280 := tb_loadHolds_unique a5280 (hw 4 (by norm_num))
  have e5283 := tb_loadHolds_unique a5283 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4478 : σ (.n 4478) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4570 : σ (.n 4570) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4649 : σ (.n 4649) = ev 16 := by
    rw [← hev 16 (by norm_num)]; exact (vt_eval h (k := 83) (by norm_num)).2.2
  have v4673 : σ (.n 4673) = ev 17 := by
    rw [← hev 17 (by norm_num)]; exact (vt_eval h (k := 84) (by norm_num)).2.2
  have v4684 : σ (.n 4684) = ev 18 := by
    rw [← hev 18 (by norm_num)]; exact (vt_eval h (k := 85) (by norm_num)).2.2
  have v5357 : σ (.n 5357) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_eval h (k := 132) (by norm_num)).2.2
  have hB : σ (.n 5855) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([65], 2)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)], [([], 0)]] := by
    simp only [v5357, v4684, v4673, v4649, v4570, v4478, v4445, a5287, a5286, a5285, a5284, e5283, a5282,
      a5281, e5280, a5279, a5278, a5277, a5276, a5275, a5274, e5273, a5272, a5271, a5270,
      a5269, a5268, a5267, e5266, a5265, a5264, a5263, a5262, e5261, a5260, a5259, a5258,
      e5257]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5289, a5288, hB]

set_option maxRecDepth 10000 in
theorem vtB05_5 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5890) = σ (.n 5857) + σ (.n 1188) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 5], 1)], [([66], 2)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5290 [
    .atom (.load (.n 5858) (.n 13) 0),
    .atom (.const (.n 5859) (word 2 0 0)),
    .atom (.mul (.n 5860) (.n 5858) (.n 5859)),
    .atom (.mul (.n 5861) (.n 4445) (.n 4502)),
    .atom (.load (.n 5862) (.n 13) 1),
    .atom (.mul (.n 5863) (.n 5862) (.n 5861)),
    .atom (.add (.n 5864) (.n 5860) (.n 5863)),
    .atom (.const (.n 5865) (word 2 0 0)),
    .atom (.mul (.n 5866) (.n 5865) (.n 5368)),
    .atom (.load (.n 5867) (.n 13) 2),
    .atom (.mul (.n 5868) (.n 5867) (.n 5866)),
    .atom (.add (.n 5869) (.n 5864) (.n 5868)),
    .atom (.mul (.n 5870) (.n 4570) (.n 4695)),
    .atom (.add (.n 5871) (.n 4695) (.n 5870)),
    .atom (.mul (.n 5872) (.n 4570) (.n 4684)),
    .atom (.add (.n 5873) (.n 5871) (.n 5872)),
    .atom (.load (.n 5874) (.n 13) 3),
    .atom (.mul (.n 5875) (.n 5874) (.n 5873)),
    .atom (.add (.n 5876) (.n 5869) (.n 5875)),
    .atom (.mul (.n 5877) (.n 4570) (.n 4706)),
    .atom (.add (.n 5878) (.n 4706) (.n 5877)),
    .atom (.mul (.n 5879) (.n 4570) (.n 4695)),
    .atom (.add (.n 5880) (.n 5878) (.n 5879)),
    .atom (.load (.n 5881) (.n 13) 4),
    .atom (.mul (.n 5882) (.n 5881) (.n 5880)),
    .atom (.add (.n 5883) (.n 5876) (.n 5882)),
    .atom (.load (.n 5884) (.n 13) 5),
    .atom (.const (.n 5885) (word 0 0 0)),
    .atom (.mul (.n 5886) (.n 5884) (.n 5885)),
    .atom (.add (.n 5887) (.n 5883) (.n 5886)),
    .atom (.add (.n 5888) (.n 14) (.n 5887)),
    .atom (.mul (.n 5889) (.n 1188) (.n 5888)),
    .atom (.add (.n 5890) (.n 5857) (.n 5889))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5290, a5291, a5292, a5293, a5294, a5295, a5296, a5297, a5298, a5299, a5300, a5301, a5302, a5303,
    a5304, a5305, a5306, a5307, a5308, a5309, a5310, a5311, a5312, a5313, a5314, a5315, a5316,
    a5317, a5318, a5319, a5320, a5321, a5322, -⟩ := hs
  have e5290 := tb_loadHolds_unique a5290 (hw 0 (by norm_num))
  have e5294 := tb_loadHolds_unique a5294 (hw 1 (by norm_num))
  have e5299 := tb_loadHolds_unique a5299 (hw 2 (by norm_num))
  have e5306 := tb_loadHolds_unique a5306 (hw 3 (by norm_num))
  have e5313 := tb_loadHolds_unique a5313 (hw 4 (by norm_num))
  have e5316 := tb_loadHolds_unique a5316 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4502 : σ (.n 4502) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4570 : σ (.n 4570) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4684 : σ (.n 4684) = ev 18 := by
    rw [← hev 18 (by norm_num)]; exact (vt_eval h (k := 85) (by norm_num)).2.2
  have v4695 : σ (.n 4695) = ev 19 := by
    rw [← hev 19 (by norm_num)]; exact (vt_eval h (k := 86) (by norm_num)).2.2
  have v4706 : σ (.n 4706) = ev 20 := by
    rw [← hev 20 (by norm_num)]; exact (vt_eval h (k := 87) (by norm_num)).2.2
  have v5368 : σ (.n 5368) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_eval h (k := 133) (by norm_num)).2.2
  have hB : σ (.n 5888) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 5], 1)], [([66], 2)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)], [([], 0)]] := by
    simp only [v5368, v4706, v4695, v4684, v4570, v4502, v4445, a5320, a5319, a5318, a5317, e5316, a5315,
      a5314, e5313, a5312, a5311, a5310, a5309, a5308, a5307, e5306, a5305, a5304, a5303,
      a5302, a5301, a5300, e5299, a5298, a5297, a5296, a5295, e5294, a5293, a5292, a5291,
      e5290]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5322, a5321, hB]

set_option maxRecDepth 10000 in
theorem vtB05_6 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5923) = σ (.n 5890) + σ (.n 1197) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 1)], [([67], 2)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5323 [
    .atom (.load (.n 5891) (.n 13) 0),
    .atom (.const (.n 5892) (word 2 0 0)),
    .atom (.mul (.n 5893) (.n 5891) (.n 5892)),
    .atom (.mul (.n 5894) (.n 4445) (.n 4513)),
    .atom (.load (.n 5895) (.n 13) 1),
    .atom (.mul (.n 5896) (.n 5895) (.n 5894)),
    .atom (.add (.n 5897) (.n 5893) (.n 5896)),
    .atom (.const (.n 5898) (word 2 0 0)),
    .atom (.mul (.n 5899) (.n 5898) (.n 5379)),
    .atom (.load (.n 5900) (.n 13) 2),
    .atom (.mul (.n 5901) (.n 5900) (.n 5899)),
    .atom (.add (.n 5902) (.n 5897) (.n 5901)),
    .atom (.mul (.n 5903) (.n 4570) (.n 4730)),
    .atom (.add (.n 5904) (.n 4730) (.n 5903)),
    .atom (.mul (.n 5905) (.n 4570) (.n 4706)),
    .atom (.add (.n 5906) (.n 5904) (.n 5905)),
    .atom (.load (.n 5907) (.n 13) 3),
    .atom (.mul (.n 5908) (.n 5907) (.n 5906)),
    .atom (.add (.n 5909) (.n 5902) (.n 5908)),
    .atom (.mul (.n 5910) (.n 4570) (.n 4741)),
    .atom (.add (.n 5911) (.n 4741) (.n 5910)),
    .atom (.mul (.n 5912) (.n 4570) (.n 4730)),
    .atom (.add (.n 5913) (.n 5911) (.n 5912)),
    .atom (.load (.n 5914) (.n 13) 4),
    .atom (.mul (.n 5915) (.n 5914) (.n 5913)),
    .atom (.add (.n 5916) (.n 5909) (.n 5915)),
    .atom (.load (.n 5917) (.n 13) 5),
    .atom (.const (.n 5918) (word 0 0 0)),
    .atom (.mul (.n 5919) (.n 5917) (.n 5918)),
    .atom (.add (.n 5920) (.n 5916) (.n 5919)),
    .atom (.add (.n 5921) (.n 14) (.n 5920)),
    .atom (.mul (.n 5922) (.n 1197) (.n 5921)),
    .atom (.add (.n 5923) (.n 5890) (.n 5922))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5323, a5324, a5325, a5326, a5327, a5328, a5329, a5330, a5331, a5332, a5333, a5334, a5335, a5336,
    a5337, a5338, a5339, a5340, a5341, a5342, a5343, a5344, a5345, a5346, a5347, a5348, a5349,
    a5350, a5351, a5352, a5353, a5354, a5355, -⟩ := hs
  have e5323 := tb_loadHolds_unique a5323 (hw 0 (by norm_num))
  have e5327 := tb_loadHolds_unique a5327 (hw 1 (by norm_num))
  have e5332 := tb_loadHolds_unique a5332 (hw 2 (by norm_num))
  have e5339 := tb_loadHolds_unique a5339 (hw 3 (by norm_num))
  have e5346 := tb_loadHolds_unique a5346 (hw 4 (by norm_num))
  have e5349 := tb_loadHolds_unique a5349 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4513 : σ (.n 4513) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 73) (by norm_num)).2.2
  have v4570 : σ (.n 4570) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4706 : σ (.n 4706) = ev 20 := by
    rw [← hev 20 (by norm_num)]; exact (vt_eval h (k := 87) (by norm_num)).2.2
  have v4730 : σ (.n 4730) = ev 21 := by
    rw [← hev 21 (by norm_num)]; exact (vt_eval h (k := 88) (by norm_num)).2.2
  have v4741 : σ (.n 4741) = ev 22 := by
    rw [← hev 22 (by norm_num)]; exact (vt_eval h (k := 89) (by norm_num)).2.2
  have v5379 : σ (.n 5379) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_eval h (k := 134) (by norm_num)).2.2
  have hB : σ (.n 5921) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 1)], [([67], 2)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)], [([], 0)]] := by
    simp only [v5379, v4741, v4730, v4706, v4570, v4513, v4445, a5353, a5352, a5351, a5350, e5349, a5348,
      a5347, e5346, a5345, a5344, a5343, a5342, a5341, a5340, e5339, a5338, a5337, a5336,
      a5335, a5334, a5333, e5332, a5331, a5330, a5329, a5328, e5327, a5326, a5325, a5324,
      e5323]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5355, a5354, hB]

set_option maxRecDepth 10000 in
theorem vtB05_7 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5958) = σ (.n 5923) + σ (.n 1206) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 2)], [([68], 2)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5356 [
    .atom (.load (.n 5924) (.n 13) 0),
    .atom (.const (.n 5925) (word 2 0 0)),
    .atom (.mul (.n 5926) (.n 5924) (.n 5925)),
    .atom (.const (.n 5927) (word 2 0 0)),
    .atom (.mul (.n 5928) (.n 4445) (.n 4513)),
    .atom (.mul (.n 5929) (.n 5927) (.n 5928)),
    .atom (.load (.n 5930) (.n 13) 1),
    .atom (.mul (.n 5931) (.n 5930) (.n 5929)),
    .atom (.add (.n 5932) (.n 5926) (.n 5931)),
    .atom (.const (.n 5933) (word 2 0 0)),
    .atom (.mul (.n 5934) (.n 5933) (.n 5390)),
    .atom (.load (.n 5935) (.n 13) 2),
    .atom (.mul (.n 5936) (.n 5935) (.n 5934)),
    .atom (.add (.n 5937) (.n 5932) (.n 5936)),
    .atom (.mul (.n 5938) (.n 4570) (.n 4752)),
    .atom (.add (.n 5939) (.n 4752) (.n 5938)),
    .atom (.mul (.n 5940) (.n 4570) (.n 4741)),
    .atom (.add (.n 5941) (.n 5939) (.n 5940)),
    .atom (.load (.n 5942) (.n 13) 3),
    .atom (.mul (.n 5943) (.n 5942) (.n 5941)),
    .atom (.add (.n 5944) (.n 5937) (.n 5943)),
    .atom (.mul (.n 5945) (.n 4570) (.n 4763)),
    .atom (.add (.n 5946) (.n 4763) (.n 5945)),
    .atom (.mul (.n 5947) (.n 4570) (.n 4752)),
    .atom (.add (.n 5948) (.n 5946) (.n 5947)),
    .atom (.load (.n 5949) (.n 13) 4),
    .atom (.mul (.n 5950) (.n 5949) (.n 5948)),
    .atom (.add (.n 5951) (.n 5944) (.n 5950)),
    .atom (.load (.n 5952) (.n 13) 5),
    .atom (.const (.n 5953) (word 0 0 0)),
    .atom (.mul (.n 5954) (.n 5952) (.n 5953)),
    .atom (.add (.n 5955) (.n 5951) (.n 5954)),
    .atom (.add (.n 5956) (.n 14) (.n 5955)),
    .atom (.mul (.n 5957) (.n 1206) (.n 5956)),
    .atom (.add (.n 5958) (.n 5923) (.n 5957))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5356, a5357, a5358, a5359, a5360, a5361, a5362, a5363, a5364, a5365, a5366, a5367, a5368, a5369,
    a5370, a5371, a5372, a5373, a5374, a5375, a5376, a5377, a5378, a5379, a5380, a5381, a5382,
    a5383, a5384, a5385, a5386, a5387, a5388, a5389, a5390, -⟩ := hs
  have e5356 := tb_loadHolds_unique a5356 (hw 0 (by norm_num))
  have e5362 := tb_loadHolds_unique a5362 (hw 1 (by norm_num))
  have e5367 := tb_loadHolds_unique a5367 (hw 2 (by norm_num))
  have e5374 := tb_loadHolds_unique a5374 (hw 3 (by norm_num))
  have e5381 := tb_loadHolds_unique a5381 (hw 4 (by norm_num))
  have e5384 := tb_loadHolds_unique a5384 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4513 : σ (.n 4513) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 73) (by norm_num)).2.2
  have v4570 : σ (.n 4570) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4741 : σ (.n 4741) = ev 22 := by
    rw [← hev 22 (by norm_num)]; exact (vt_eval h (k := 89) (by norm_num)).2.2
  have v4752 : σ (.n 4752) = ev 23 := by
    rw [← hev 23 (by norm_num)]; exact (vt_eval h (k := 90) (by norm_num)).2.2
  have v4763 : σ (.n 4763) = ev 24 := by
    rw [← hev 24 (by norm_num)]; exact (vt_eval h (k := 91) (by norm_num)).2.2
  have v5390 : σ (.n 5390) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_eval h (k := 135) (by norm_num)).2.2
  have hB : σ (.n 5956) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 2)], [([68], 2)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)], [([], 0)]] := by
    simp only [v5390, v4763, v4752, v4741, v4570, v4513, v4445, a5388, a5387, a5386, a5385, e5384, a5383,
      a5382, e5381, a5380, a5379, a5378, a5377, a5376, a5375, e5374, a5373, a5372, a5371,
      a5370, a5369, a5368, e5367, a5366, a5365, a5364, a5363, e5362, a5361, a5360, a5359,
      a5358, a5357, e5356]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5390, a5389, hB]

set_option maxRecDepth 10000 in
theorem vtB05_8 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5993) = σ (.n 5958) + σ (.n 1215) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 4)], [([69], 2)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5391 [
    .atom (.load (.n 5959) (.n 13) 0),
    .atom (.const (.n 5960) (word 2 0 0)),
    .atom (.mul (.n 5961) (.n 5959) (.n 5960)),
    .atom (.const (.n 5962) (word 4 0 0)),
    .atom (.mul (.n 5963) (.n 4445) (.n 4513)),
    .atom (.mul (.n 5964) (.n 5962) (.n 5963)),
    .atom (.load (.n 5965) (.n 13) 1),
    .atom (.mul (.n 5966) (.n 5965) (.n 5964)),
    .atom (.add (.n 5967) (.n 5961) (.n 5966)),
    .atom (.const (.n 5968) (word 2 0 0)),
    .atom (.mul (.n 5969) (.n 5968) (.n 5414)),
    .atom (.load (.n 5970) (.n 13) 2),
    .atom (.mul (.n 5971) (.n 5970) (.n 5969)),
    .atom (.add (.n 5972) (.n 5967) (.n 5971)),
    .atom (.mul (.n 5973) (.n 4570) (.n 4787)),
    .atom (.add (.n 5974) (.n 4787) (.n 5973)),
    .atom (.mul (.n 5975) (.n 4570) (.n 4763)),
    .atom (.add (.n 5976) (.n 5974) (.n 5975)),
    .atom (.load (.n 5977) (.n 13) 3),
    .atom (.mul (.n 5978) (.n 5977) (.n 5976)),
    .atom (.add (.n 5979) (.n 5972) (.n 5978)),
    .atom (.mul (.n 5980) (.n 4570) (.n 4798)),
    .atom (.add (.n 5981) (.n 4798) (.n 5980)),
    .atom (.mul (.n 5982) (.n 4570) (.n 4787)),
    .atom (.add (.n 5983) (.n 5981) (.n 5982)),
    .atom (.load (.n 5984) (.n 13) 4),
    .atom (.mul (.n 5985) (.n 5984) (.n 5983)),
    .atom (.add (.n 5986) (.n 5979) (.n 5985)),
    .atom (.load (.n 5987) (.n 13) 5),
    .atom (.const (.n 5988) (word 0 0 0)),
    .atom (.mul (.n 5989) (.n 5987) (.n 5988)),
    .atom (.add (.n 5990) (.n 5986) (.n 5989)),
    .atom (.add (.n 5991) (.n 14) (.n 5990)),
    .atom (.mul (.n 5992) (.n 1215) (.n 5991)),
    .atom (.add (.n 5993) (.n 5958) (.n 5992))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5391, a5392, a5393, a5394, a5395, a5396, a5397, a5398, a5399, a5400, a5401, a5402, a5403, a5404,
    a5405, a5406, a5407, a5408, a5409, a5410, a5411, a5412, a5413, a5414, a5415, a5416, a5417,
    a5418, a5419, a5420, a5421, a5422, a5423, a5424, a5425, -⟩ := hs
  have e5391 := tb_loadHolds_unique a5391 (hw 0 (by norm_num))
  have e5397 := tb_loadHolds_unique a5397 (hw 1 (by norm_num))
  have e5402 := tb_loadHolds_unique a5402 (hw 2 (by norm_num))
  have e5409 := tb_loadHolds_unique a5409 (hw 3 (by norm_num))
  have e5416 := tb_loadHolds_unique a5416 (hw 4 (by norm_num))
  have e5419 := tb_loadHolds_unique a5419 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4513 : σ (.n 4513) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 73) (by norm_num)).2.2
  have v4570 : σ (.n 4570) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4763 : σ (.n 4763) = ev 24 := by
    rw [← hev 24 (by norm_num)]; exact (vt_eval h (k := 91) (by norm_num)).2.2
  have v4787 : σ (.n 4787) = ev 25 := by
    rw [← hev 25 (by norm_num)]; exact (vt_eval h (k := 92) (by norm_num)).2.2
  have v4798 : σ (.n 4798) = ev 26 := by
    rw [← hev 26 (by norm_num)]; exact (vt_eval h (k := 93) (by norm_num)).2.2
  have v5414 : σ (.n 5414) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_eval h (k := 136) (by norm_num)).2.2
  have hB : σ (.n 5991) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 4)], [([69], 2)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)], [([], 0)]] := by
    simp only [v5414, v4798, v4787, v4763, v4570, v4513, v4445, a5423, a5422, a5421, a5420, e5419, a5418,
      a5417, e5416, a5415, a5414, a5413, a5412, a5411, a5410, e5409, a5408, a5407, a5406,
      a5405, a5404, a5403, e5402, a5401, a5400, a5399, a5398, e5397, a5396, a5395, a5394,
      a5393, a5392, e5391]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5425, a5424, hB]

set_option maxRecDepth 10000 in
theorem vtB05_9 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6028) = σ (.n 5993) + σ (.n 1224) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 8)], [([70], 2)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5426 [
    .atom (.load (.n 5994) (.n 13) 0),
    .atom (.const (.n 5995) (word 2 0 0)),
    .atom (.mul (.n 5996) (.n 5994) (.n 5995)),
    .atom (.const (.n 5997) (word 8 0 0)),
    .atom (.mul (.n 5998) (.n 4445) (.n 4513)),
    .atom (.mul (.n 5999) (.n 5997) (.n 5998)),
    .atom (.load (.n 6000) (.n 13) 1),
    .atom (.mul (.n 6001) (.n 6000) (.n 5999)),
    .atom (.add (.n 6002) (.n 5996) (.n 6001)),
    .atom (.const (.n 6003) (word 2 0 0)),
    .atom (.mul (.n 6004) (.n 6003) (.n 5425)),
    .atom (.load (.n 6005) (.n 13) 2),
    .atom (.mul (.n 6006) (.n 6005) (.n 6004)),
    .atom (.add (.n 6007) (.n 6002) (.n 6006)),
    .atom (.mul (.n 6008) (.n 4570) (.n 4809)),
    .atom (.add (.n 6009) (.n 4809) (.n 6008)),
    .atom (.mul (.n 6010) (.n 4570) (.n 4798)),
    .atom (.add (.n 6011) (.n 6009) (.n 6010)),
    .atom (.load (.n 6012) (.n 13) 3),
    .atom (.mul (.n 6013) (.n 6012) (.n 6011)),
    .atom (.add (.n 6014) (.n 6007) (.n 6013)),
    .atom (.mul (.n 6015) (.n 4570) (.n 4820)),
    .atom (.add (.n 6016) (.n 4820) (.n 6015)),
    .atom (.mul (.n 6017) (.n 4570) (.n 4809)),
    .atom (.add (.n 6018) (.n 6016) (.n 6017)),
    .atom (.load (.n 6019) (.n 13) 4),
    .atom (.mul (.n 6020) (.n 6019) (.n 6018)),
    .atom (.add (.n 6021) (.n 6014) (.n 6020)),
    .atom (.load (.n 6022) (.n 13) 5),
    .atom (.const (.n 6023) (word 0 0 0)),
    .atom (.mul (.n 6024) (.n 6022) (.n 6023)),
    .atom (.add (.n 6025) (.n 6021) (.n 6024)),
    .atom (.add (.n 6026) (.n 14) (.n 6025)),
    .atom (.mul (.n 6027) (.n 1224) (.n 6026)),
    .atom (.add (.n 6028) (.n 5993) (.n 6027))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5426, a5427, a5428, a5429, a5430, a5431, a5432, a5433, a5434, a5435, a5436, a5437, a5438, a5439,
    a5440, a5441, a5442, a5443, a5444, a5445, a5446, a5447, a5448, a5449, a5450, a5451, a5452,
    a5453, a5454, a5455, a5456, a5457, a5458, a5459, a5460, -⟩ := hs
  have e5426 := tb_loadHolds_unique a5426 (hw 0 (by norm_num))
  have e5432 := tb_loadHolds_unique a5432 (hw 1 (by norm_num))
  have e5437 := tb_loadHolds_unique a5437 (hw 2 (by norm_num))
  have e5444 := tb_loadHolds_unique a5444 (hw 3 (by norm_num))
  have e5451 := tb_loadHolds_unique a5451 (hw 4 (by norm_num))
  have e5454 := tb_loadHolds_unique a5454 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4513 : σ (.n 4513) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 73) (by norm_num)).2.2
  have v4570 : σ (.n 4570) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4798 : σ (.n 4798) = ev 26 := by
    rw [← hev 26 (by norm_num)]; exact (vt_eval h (k := 93) (by norm_num)).2.2
  have v4809 : σ (.n 4809) = ev 27 := by
    rw [← hev 27 (by norm_num)]; exact (vt_eval h (k := 94) (by norm_num)).2.2
  have v4820 : σ (.n 4820) = ev 28 := by
    rw [← hev 28 (by norm_num)]; exact (vt_eval h (k := 95) (by norm_num)).2.2
  have v5425 : σ (.n 5425) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_eval h (k := 137) (by norm_num)).2.2
  have hB : σ (.n 6026) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 8)], [([70], 2)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)], [([], 0)]] := by
    simp only [v5425, v4820, v4809, v4798, v4570, v4513, v4445, a5458, a5457, a5456, a5455, e5454, a5453,
      a5452, e5451, a5450, a5449, a5448, a5447, a5446, a5445, e5444, a5443, a5442, a5441,
      a5440, a5439, a5438, e5437, a5436, a5435, a5434, a5433, e5432, a5431, a5430, a5429,
      a5428, a5427, e5426]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5460, a5459, hB]

set_option maxRecDepth 10000 in
theorem vtB05_10 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6061) = σ (.n 6028) + σ (.n 1233) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 7], 1)], [([71], 2)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([12], 1), ([10, 12], 1), ([10, 29], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5461 [
    .atom (.load (.n 6029) (.n 13) 0),
    .atom (.const (.n 6030) (word 2 0 0)),
    .atom (.mul (.n 6031) (.n 6029) (.n 6030)),
    .atom (.mul (.n 6032) (.n 4445) (.n 4524)),
    .atom (.load (.n 6033) (.n 13) 1),
    .atom (.mul (.n 6034) (.n 6033) (.n 6032)),
    .atom (.add (.n 6035) (.n 6031) (.n 6034)),
    .atom (.const (.n 6036) (word 2 0 0)),
    .atom (.mul (.n 6037) (.n 6036) (.n 5436)),
    .atom (.load (.n 6038) (.n 13) 2),
    .atom (.mul (.n 6039) (.n 6038) (.n 6037)),
    .atom (.add (.n 6040) (.n 6035) (.n 6039)),
    .atom (.mul (.n 6041) (.n 4570) (.n 4844)),
    .atom (.add (.n 6042) (.n 4844) (.n 6041)),
    .atom (.mul (.n 6043) (.n 4570) (.n 4820)),
    .atom (.add (.n 6044) (.n 6042) (.n 6043)),
    .atom (.load (.n 6045) (.n 13) 3),
    .atom (.mul (.n 6046) (.n 6045) (.n 6044)),
    .atom (.add (.n 6047) (.n 6040) (.n 6046)),
    .atom (.mul (.n 6048) (.n 4570) (.n 4592)),
    .atom (.add (.n 6049) (.n 4592) (.n 6048)),
    .atom (.mul (.n 6050) (.n 4570) (.n 4844)),
    .atom (.add (.n 6051) (.n 6049) (.n 6050)),
    .atom (.load (.n 6052) (.n 13) 4),
    .atom (.mul (.n 6053) (.n 6052) (.n 6051)),
    .atom (.add (.n 6054) (.n 6047) (.n 6053)),
    .atom (.load (.n 6055) (.n 13) 5),
    .atom (.const (.n 6056) (word 0 0 0)),
    .atom (.mul (.n 6057) (.n 6055) (.n 6056)),
    .atom (.add (.n 6058) (.n 6054) (.n 6057)),
    .atom (.add (.n 6059) (.n 14) (.n 6058)),
    .atom (.mul (.n 6060) (.n 1233) (.n 6059)),
    .atom (.add (.n 6061) (.n 6028) (.n 6060))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5461, a5462, a5463, a5464, a5465, a5466, a5467, a5468, a5469, a5470, a5471, a5472, a5473, a5474,
    a5475, a5476, a5477, a5478, a5479, a5480, a5481, a5482, a5483, a5484, a5485, a5486, a5487,
    a5488, a5489, a5490, a5491, a5492, a5493, -⟩ := hs
  have e5461 := tb_loadHolds_unique a5461 (hw 0 (by norm_num))
  have e5465 := tb_loadHolds_unique a5465 (hw 1 (by norm_num))
  have e5470 := tb_loadHolds_unique a5470 (hw 2 (by norm_num))
  have e5477 := tb_loadHolds_unique a5477 (hw 3 (by norm_num))
  have e5484 := tb_loadHolds_unique a5484 (hw 4 (by norm_num))
  have e5487 := tb_loadHolds_unique a5487 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4524 : σ (.n 4524) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4570 : σ (.n 4570) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4592 : σ (.n 4592) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 79) (by norm_num)).2.2
  have v4820 : σ (.n 4820) = ev 28 := by
    rw [← hev 28 (by norm_num)]; exact (vt_eval h (k := 95) (by norm_num)).2.2
  have v4844 : σ (.n 4844) = ev 29 := by
    rw [← hev 29 (by norm_num)]; exact (vt_eval h (k := 96) (by norm_num)).2.2
  have v5436 : σ (.n 5436) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_eval h (k := 138) (by norm_num)).2.2
  have hB : σ (.n 6059) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 7], 1)], [([71], 2)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([12], 1), ([10, 12], 1), ([10, 29], 1)], [([], 0)]] := by
    simp only [v5436, v4844, v4820, v4592, v4570, v4524, v4445, a5491, a5490, a5489, a5488, e5487, a5486,
      a5485, e5484, a5483, a5482, a5481, a5480, a5479, a5478, e5477, a5476, a5475, a5474,
      a5473, a5472, a5471, e5470, a5469, a5468, a5467, a5466, e5465, a5464, a5463, a5462,
      e5461]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5493, a5492, hB]

set_option maxRecDepth 10000 in
theorem vtB05_11 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6086) = σ (.n 6061) + σ (.n 1242) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 1)], [([72], 2)], [([30], 1)], [([31], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5494 [
    .atom (.load (.n 6062) (.n 13) 0),
    .atom (.const (.n 6063) (word 2 0 0)),
    .atom (.mul (.n 6064) (.n 6062) (.n 6063)),
    .atom (.mul (.n 6065) (.n 4445) (.n 4535)),
    .atom (.load (.n 6066) (.n 13) 1),
    .atom (.mul (.n 6067) (.n 6066) (.n 6065)),
    .atom (.add (.n 6068) (.n 6064) (.n 6067)),
    .atom (.const (.n 6069) (word 2 0 0)),
    .atom (.mul (.n 6070) (.n 6069) (.n 5447)),
    .atom (.load (.n 6071) (.n 13) 2),
    .atom (.mul (.n 6072) (.n 6071) (.n 6070)),
    .atom (.add (.n 6073) (.n 6068) (.n 6072)),
    .atom (.load (.n 6074) (.n 13) 3),
    .atom (.mul (.n 6075) (.n 6074) (.n 4855)),
    .atom (.add (.n 6076) (.n 6073) (.n 6075)),
    .atom (.load (.n 6077) (.n 13) 4),
    .atom (.mul (.n 6078) (.n 6077) (.n 4866)),
    .atom (.add (.n 6079) (.n 6076) (.n 6078)),
    .atom (.load (.n 6080) (.n 13) 5),
    .atom (.const (.n 6081) (word 0 0 0)),
    .atom (.mul (.n 6082) (.n 6080) (.n 6081)),
    .atom (.add (.n 6083) (.n 6079) (.n 6082)),
    .atom (.add (.n 6084) (.n 14) (.n 6083)),
    .atom (.mul (.n 6085) (.n 1242) (.n 6084)),
    .atom (.add (.n 6086) (.n 6061) (.n 6085))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5494, a5495, a5496, a5497, a5498, a5499, a5500, a5501, a5502, a5503, a5504, a5505, a5506, a5507,
    a5508, a5509, a5510, a5511, a5512, a5513, a5514, a5515, a5516, a5517, a5518, -⟩ := hs
  have e5494 := tb_loadHolds_unique a5494 (hw 0 (by norm_num))
  have e5498 := tb_loadHolds_unique a5498 (hw 1 (by norm_num))
  have e5503 := tb_loadHolds_unique a5503 (hw 2 (by norm_num))
  have e5506 := tb_loadHolds_unique a5506 (hw 3 (by norm_num))
  have e5509 := tb_loadHolds_unique a5509 (hw 4 (by norm_num))
  have e5512 := tb_loadHolds_unique a5512 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4535 : σ (.n 4535) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 75) (by norm_num)).2.2
  have v4855 : σ (.n 4855) = ev 30 := by
    rw [← hev 30 (by norm_num)]; exact (vt_eval h (k := 97) (by norm_num)).2.2
  have v4866 : σ (.n 4866) = ev 31 := by
    rw [← hev 31 (by norm_num)]; exact (vt_eval h (k := 98) (by norm_num)).2.2
  have v5447 : σ (.n 5447) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_eval h (k := 139) (by norm_num)).2.2
  have hB : σ (.n 6084) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 1)], [([72], 2)], [([30], 1)], [([31], 1)], [([], 0)]] := by
    simp only [v5447, v4866, v4855, v4535, v4445, a5516, a5515, a5514, a5513, e5512, a5511, a5510, e5509,
      a5508, a5507, e5506, a5505, a5504, e5503, a5502, a5501, a5500, a5499, e5498, a5497,
      a5496, a5495, e5494]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5518, a5517, hB]

set_option maxRecDepth 10000 in
theorem vtB05_12 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6113) = σ (.n 6086) + σ (.n 1251) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 2)], [([73], 2)], [([32], 1)], [([33], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5519 [
    .atom (.load (.n 6087) (.n 13) 0),
    .atom (.const (.n 6088) (word 2 0 0)),
    .atom (.mul (.n 6089) (.n 6087) (.n 6088)),
    .atom (.const (.n 6090) (word 2 0 0)),
    .atom (.mul (.n 6091) (.n 4445) (.n 4535)),
    .atom (.mul (.n 6092) (.n 6090) (.n 6091)),
    .atom (.load (.n 6093) (.n 13) 1),
    .atom (.mul (.n 6094) (.n 6093) (.n 6092)),
    .atom (.add (.n 6095) (.n 6089) (.n 6094)),
    .atom (.const (.n 6096) (word 2 0 0)),
    .atom (.mul (.n 6097) (.n 6096) (.n 5471)),
    .atom (.load (.n 6098) (.n 13) 2),
    .atom (.mul (.n 6099) (.n 6098) (.n 6097)),
    .atom (.add (.n 6100) (.n 6095) (.n 6099)),
    .atom (.load (.n 6101) (.n 13) 3),
    .atom (.mul (.n 6102) (.n 6101) (.n 4877)),
    .atom (.add (.n 6103) (.n 6100) (.n 6102)),
    .atom (.load (.n 6104) (.n 13) 4),
    .atom (.mul (.n 6105) (.n 6104) (.n 4901)),
    .atom (.add (.n 6106) (.n 6103) (.n 6105)),
    .atom (.load (.n 6107) (.n 13) 5),
    .atom (.const (.n 6108) (word 0 0 0)),
    .atom (.mul (.n 6109) (.n 6107) (.n 6108)),
    .atom (.add (.n 6110) (.n 6106) (.n 6109)),
    .atom (.add (.n 6111) (.n 14) (.n 6110)),
    .atom (.mul (.n 6112) (.n 1251) (.n 6111)),
    .atom (.add (.n 6113) (.n 6086) (.n 6112))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5519, a5520, a5521, a5522, a5523, a5524, a5525, a5526, a5527, a5528, a5529, a5530, a5531, a5532,
    a5533, a5534, a5535, a5536, a5537, a5538, a5539, a5540, a5541, a5542, a5543, a5544, a5545, -⟩ := hs
  have e5519 := tb_loadHolds_unique a5519 (hw 0 (by norm_num))
  have e5525 := tb_loadHolds_unique a5525 (hw 1 (by norm_num))
  have e5530 := tb_loadHolds_unique a5530 (hw 2 (by norm_num))
  have e5533 := tb_loadHolds_unique a5533 (hw 3 (by norm_num))
  have e5536 := tb_loadHolds_unique a5536 (hw 4 (by norm_num))
  have e5539 := tb_loadHolds_unique a5539 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4535 : σ (.n 4535) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 75) (by norm_num)).2.2
  have v4877 : σ (.n 4877) = ev 32 := by
    rw [← hev 32 (by norm_num)]; exact (vt_eval h (k := 99) (by norm_num)).2.2
  have v4901 : σ (.n 4901) = ev 33 := by
    rw [← hev 33 (by norm_num)]; exact (vt_eval h (k := 100) (by norm_num)).2.2
  have v5471 : σ (.n 5471) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_eval h (k := 140) (by norm_num)).2.2
  have hB : σ (.n 6111) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 2)], [([73], 2)], [([32], 1)], [([33], 1)], [([], 0)]] := by
    simp only [v5471, v4901, v4877, v4535, v4445, a5543, a5542, a5541, a5540, e5539, a5538, a5537, e5536,
      a5535, a5534, e5533, a5532, a5531, e5530, a5529, a5528, a5527, a5526, e5525, a5524,
      a5523, a5522, a5521, a5520, e5519]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5545, a5544, hB]

set_option maxRecDepth 10000 in
theorem vtB05_13 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6140) = σ (.n 6113) + σ (.n 1260) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 4)], [([74], 2)], [([34], 1)], [([35], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5546 [
    .atom (.load (.n 6114) (.n 13) 0),
    .atom (.const (.n 6115) (word 2 0 0)),
    .atom (.mul (.n 6116) (.n 6114) (.n 6115)),
    .atom (.const (.n 6117) (word 4 0 0)),
    .atom (.mul (.n 6118) (.n 4445) (.n 4535)),
    .atom (.mul (.n 6119) (.n 6117) (.n 6118)),
    .atom (.load (.n 6120) (.n 13) 1),
    .atom (.mul (.n 6121) (.n 6120) (.n 6119)),
    .atom (.add (.n 6122) (.n 6116) (.n 6121)),
    .atom (.const (.n 6123) (word 2 0 0)),
    .atom (.mul (.n 6124) (.n 6123) (.n 5482)),
    .atom (.load (.n 6125) (.n 13) 2),
    .atom (.mul (.n 6126) (.n 6125) (.n 6124)),
    .atom (.add (.n 6127) (.n 6122) (.n 6126)),
    .atom (.load (.n 6128) (.n 13) 3),
    .atom (.mul (.n 6129) (.n 6128) (.n 4912)),
    .atom (.add (.n 6130) (.n 6127) (.n 6129)),
    .atom (.load (.n 6131) (.n 13) 4),
    .atom (.mul (.n 6132) (.n 6131) (.n 4923)),
    .atom (.add (.n 6133) (.n 6130) (.n 6132)),
    .atom (.load (.n 6134) (.n 13) 5),
    .atom (.const (.n 6135) (word 0 0 0)),
    .atom (.mul (.n 6136) (.n 6134) (.n 6135)),
    .atom (.add (.n 6137) (.n 6133) (.n 6136)),
    .atom (.add (.n 6138) (.n 14) (.n 6137)),
    .atom (.mul (.n 6139) (.n 1260) (.n 6138)),
    .atom (.add (.n 6140) (.n 6113) (.n 6139))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5546, a5547, a5548, a5549, a5550, a5551, a5552, a5553, a5554, a5555, a5556, a5557, a5558, a5559,
    a5560, a5561, a5562, a5563, a5564, a5565, a5566, a5567, a5568, a5569, a5570, a5571, a5572, -⟩ := hs
  have e5546 := tb_loadHolds_unique a5546 (hw 0 (by norm_num))
  have e5552 := tb_loadHolds_unique a5552 (hw 1 (by norm_num))
  have e5557 := tb_loadHolds_unique a5557 (hw 2 (by norm_num))
  have e5560 := tb_loadHolds_unique a5560 (hw 3 (by norm_num))
  have e5563 := tb_loadHolds_unique a5563 (hw 4 (by norm_num))
  have e5566 := tb_loadHolds_unique a5566 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4535 : σ (.n 4535) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 75) (by norm_num)).2.2
  have v4912 : σ (.n 4912) = ev 34 := by
    rw [← hev 34 (by norm_num)]; exact (vt_eval h (k := 101) (by norm_num)).2.2
  have v4923 : σ (.n 4923) = ev 35 := by
    rw [← hev 35 (by norm_num)]; exact (vt_eval h (k := 102) (by norm_num)).2.2
  have v5482 : σ (.n 5482) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_eval h (k := 141) (by norm_num)).2.2
  have hB : σ (.n 6138) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 4)], [([74], 2)], [([34], 1)], [([35], 1)], [([], 0)]] := by
    simp only [v5482, v4923, v4912, v4535, v4445, a5570, a5569, a5568, a5567, e5566, a5565, a5564, e5563,
      a5562, a5561, e5560, a5559, a5558, e5557, a5556, a5555, a5554, a5553, e5552, a5551,
      a5550, a5549, a5548, a5547, e5546]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5572, a5571, hB]

set_option maxRecDepth 10000 in
theorem vtB05_14 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6167) = σ (.n 6140) + σ (.n 1269) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 8)], [([75], 2)], [([36], 1)], [([37], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5573 [
    .atom (.load (.n 6141) (.n 13) 0),
    .atom (.const (.n 6142) (word 2 0 0)),
    .atom (.mul (.n 6143) (.n 6141) (.n 6142)),
    .atom (.const (.n 6144) (word 8 0 0)),
    .atom (.mul (.n 6145) (.n 4445) (.n 4535)),
    .atom (.mul (.n 6146) (.n 6144) (.n 6145)),
    .atom (.load (.n 6147) (.n 13) 1),
    .atom (.mul (.n 6148) (.n 6147) (.n 6146)),
    .atom (.add (.n 6149) (.n 6143) (.n 6148)),
    .atom (.const (.n 6150) (word 2 0 0)),
    .atom (.mul (.n 6151) (.n 6150) (.n 5493)),
    .atom (.load (.n 6152) (.n 13) 2),
    .atom (.mul (.n 6153) (.n 6152) (.n 6151)),
    .atom (.add (.n 6154) (.n 6149) (.n 6153)),
    .atom (.load (.n 6155) (.n 13) 3),
    .atom (.mul (.n 6156) (.n 6155) (.n 4934)),
    .atom (.add (.n 6157) (.n 6154) (.n 6156)),
    .atom (.load (.n 6158) (.n 13) 4),
    .atom (.mul (.n 6159) (.n 6158) (.n 4958)),
    .atom (.add (.n 6160) (.n 6157) (.n 6159)),
    .atom (.load (.n 6161) (.n 13) 5),
    .atom (.const (.n 6162) (word 0 0 0)),
    .atom (.mul (.n 6163) (.n 6161) (.n 6162)),
    .atom (.add (.n 6164) (.n 6160) (.n 6163)),
    .atom (.add (.n 6165) (.n 14) (.n 6164)),
    .atom (.mul (.n 6166) (.n 1269) (.n 6165)),
    .atom (.add (.n 6167) (.n 6140) (.n 6166))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5573, a5574, a5575, a5576, a5577, a5578, a5579, a5580, a5581, a5582, a5583, a5584, a5585, a5586,
    a5587, a5588, a5589, a5590, a5591, a5592, a5593, a5594, a5595, a5596, a5597, a5598, a5599, -⟩ := hs
  have e5573 := tb_loadHolds_unique a5573 (hw 0 (by norm_num))
  have e5579 := tb_loadHolds_unique a5579 (hw 1 (by norm_num))
  have e5584 := tb_loadHolds_unique a5584 (hw 2 (by norm_num))
  have e5587 := tb_loadHolds_unique a5587 (hw 3 (by norm_num))
  have e5590 := tb_loadHolds_unique a5590 (hw 4 (by norm_num))
  have e5593 := tb_loadHolds_unique a5593 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4535 : σ (.n 4535) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 75) (by norm_num)).2.2
  have v4934 : σ (.n 4934) = ev 36 := by
    rw [← hev 36 (by norm_num)]; exact (vt_eval h (k := 103) (by norm_num)).2.2
  have v4958 : σ (.n 4958) = ev 37 := by
    rw [← hev 37 (by norm_num)]; exact (vt_eval h (k := 104) (by norm_num)).2.2
  have v5493 : σ (.n 5493) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_eval h (k := 142) (by norm_num)).2.2
  have hB : σ (.n 6165) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 8)], [([75], 2)], [([36], 1)], [([37], 1)], [([], 0)]] := by
    simp only [v5493, v4958, v4934, v4535, v4445, a5597, a5596, a5595, a5594, e5593, a5592, a5591, e5590,
      a5589, a5588, e5587, a5586, a5585, e5584, a5583, a5582, a5581, a5580, e5579, a5578,
      a5577, a5576, a5575, a5574, e5573]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5599, a5598, hB]

set_option maxRecDepth 10000 in
theorem vtB05_15 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6198) = σ (.n 6167) + σ (.n 1278) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 1)], [([76], 2)], [([38], 1), ([11, 38], 1)], [([39], 1), ([11, 39], 1), ([11, 38], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5600 [
    .atom (.load (.n 6168) (.n 13) 0),
    .atom (.const (.n 6169) (word 2 0 0)),
    .atom (.mul (.n 6170) (.n 6168) (.n 6169)),
    .atom (.mul (.n 6171) (.n 4445) (.n 4559)),
    .atom (.load (.n 6172) (.n 13) 1),
    .atom (.mul (.n 6173) (.n 6172) (.n 6171)),
    .atom (.add (.n 6174) (.n 6170) (.n 6173)),
    .atom (.const (.n 6175) (word 2 0 0)),
    .atom (.mul (.n 6176) (.n 6175) (.n 5504)),
    .atom (.load (.n 6177) (.n 13) 2),
    .atom (.mul (.n 6178) (.n 6177) (.n 6176)),
    .atom (.add (.n 6179) (.n 6174) (.n 6178)),
    .atom (.mul (.n 6180) (.n 4581) (.n 4969)),
    .atom (.add (.n 6181) (.n 4969) (.n 6180)),
    .atom (.load (.n 6182) (.n 13) 3),
    .atom (.mul (.n 6183) (.n 6182) (.n 6181)),
    .atom (.add (.n 6184) (.n 6179) (.n 6183)),
    .atom (.mul (.n 6185) (.n 4581) (.n 4980)),
    .atom (.add (.n 6186) (.n 4980) (.n 6185)),
    .atom (.mul (.n 6187) (.n 4581) (.n 4969)),
    .atom (.add (.n 6188) (.n 6186) (.n 6187)),
    .atom (.load (.n 6189) (.n 13) 4),
    .atom (.mul (.n 6190) (.n 6189) (.n 6188)),
    .atom (.add (.n 6191) (.n 6184) (.n 6190)),
    .atom (.load (.n 6192) (.n 13) 5),
    .atom (.const (.n 6193) (word 0 0 0)),
    .atom (.mul (.n 6194) (.n 6192) (.n 6193)),
    .atom (.add (.n 6195) (.n 6191) (.n 6194)),
    .atom (.add (.n 6196) (.n 14) (.n 6195)),
    .atom (.mul (.n 6197) (.n 1278) (.n 6196)),
    .atom (.add (.n 6198) (.n 6167) (.n 6197))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5600, a5601, a5602, a5603, a5604, a5605, a5606, a5607, a5608, a5609, a5610, a5611, a5612, a5613,
    a5614, a5615, a5616, a5617, a5618, a5619, a5620, a5621, a5622, a5623, a5624, a5625, a5626,
    a5627, a5628, a5629, a5630, -⟩ := hs
  have e5600 := tb_loadHolds_unique a5600 (hw 0 (by norm_num))
  have e5604 := tb_loadHolds_unique a5604 (hw 1 (by norm_num))
  have e5609 := tb_loadHolds_unique a5609 (hw 2 (by norm_num))
  have e5614 := tb_loadHolds_unique a5614 (hw 3 (by norm_num))
  have e5621 := tb_loadHolds_unique a5621 (hw 4 (by norm_num))
  have e5624 := tb_loadHolds_unique a5624 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v4581 : σ (.n 4581) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 78) (by norm_num)).2.2
  have v4969 : σ (.n 4969) = ev 38 := by
    rw [← hev 38 (by norm_num)]; exact (vt_eval h (k := 105) (by norm_num)).2.2
  have v4980 : σ (.n 4980) = ev 39 := by
    rw [← hev 39 (by norm_num)]; exact (vt_eval h (k := 106) (by norm_num)).2.2
  have v5504 : σ (.n 5504) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_eval h (k := 143) (by norm_num)).2.2
  have hB : σ (.n 6196) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 1)], [([76], 2)], [([38], 1), ([11, 38], 1)], [([39], 1), ([11, 39], 1), ([11, 38], 1)], [([], 0)]] := by
    simp only [v5504, v4980, v4969, v4581, v4559, v4445, a5628, a5627, a5626, a5625, e5624, a5623, a5622,
      e5621, a5620, a5619, a5618, a5617, a5616, a5615, e5614, a5613, a5612, a5611, a5610,
      e5609, a5608, a5607, a5606, a5605, e5604, a5603, a5602, a5601, e5600]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5630, a5629, hB]

set_option maxRecDepth 10000 in
theorem vtB05_16 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6233) = σ (.n 6198) + σ (.n 1287) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 2)], [([77], 2)], [([40], 1), ([11, 40], 1), ([11, 39], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5631 [
    .atom (.load (.n 6199) (.n 13) 0),
    .atom (.const (.n 6200) (word 2 0 0)),
    .atom (.mul (.n 6201) (.n 6199) (.n 6200)),
    .atom (.const (.n 6202) (word 2 0 0)),
    .atom (.mul (.n 6203) (.n 4445) (.n 4559)),
    .atom (.mul (.n 6204) (.n 6202) (.n 6203)),
    .atom (.load (.n 6205) (.n 13) 1),
    .atom (.mul (.n 6206) (.n 6205) (.n 6204)),
    .atom (.add (.n 6207) (.n 6201) (.n 6206)),
    .atom (.const (.n 6208) (word 2 0 0)),
    .atom (.mul (.n 6209) (.n 6208) (.n 5528)),
    .atom (.load (.n 6210) (.n 13) 2),
    .atom (.mul (.n 6211) (.n 6210) (.n 6209)),
    .atom (.add (.n 6212) (.n 6207) (.n 6211)),
    .atom (.mul (.n 6213) (.n 4581) (.n 4991)),
    .atom (.add (.n 6214) (.n 4991) (.n 6213)),
    .atom (.mul (.n 6215) (.n 4581) (.n 4980)),
    .atom (.add (.n 6216) (.n 6214) (.n 6215)),
    .atom (.load (.n 6217) (.n 13) 3),
    .atom (.mul (.n 6218) (.n 6217) (.n 6216)),
    .atom (.add (.n 6219) (.n 6212) (.n 6218)),
    .atom (.mul (.n 6220) (.n 4581) (.n 5015)),
    .atom (.add (.n 6221) (.n 5015) (.n 6220)),
    .atom (.mul (.n 6222) (.n 4581) (.n 4991)),
    .atom (.add (.n 6223) (.n 6221) (.n 6222)),
    .atom (.load (.n 6224) (.n 13) 4),
    .atom (.mul (.n 6225) (.n 6224) (.n 6223)),
    .atom (.add (.n 6226) (.n 6219) (.n 6225)),
    .atom (.load (.n 6227) (.n 13) 5),
    .atom (.const (.n 6228) (word 0 0 0)),
    .atom (.mul (.n 6229) (.n 6227) (.n 6228)),
    .atom (.add (.n 6230) (.n 6226) (.n 6229)),
    .atom (.add (.n 6231) (.n 14) (.n 6230)),
    .atom (.mul (.n 6232) (.n 1287) (.n 6231)),
    .atom (.add (.n 6233) (.n 6198) (.n 6232))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5631, a5632, a5633, a5634, a5635, a5636, a5637, a5638, a5639, a5640, a5641, a5642, a5643, a5644,
    a5645, a5646, a5647, a5648, a5649, a5650, a5651, a5652, a5653, a5654, a5655, a5656, a5657,
    a5658, a5659, a5660, a5661, a5662, a5663, a5664, a5665, -⟩ := hs
  have e5631 := tb_loadHolds_unique a5631 (hw 0 (by norm_num))
  have e5637 := tb_loadHolds_unique a5637 (hw 1 (by norm_num))
  have e5642 := tb_loadHolds_unique a5642 (hw 2 (by norm_num))
  have e5649 := tb_loadHolds_unique a5649 (hw 3 (by norm_num))
  have e5656 := tb_loadHolds_unique a5656 (hw 4 (by norm_num))
  have e5659 := tb_loadHolds_unique a5659 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v4581 : σ (.n 4581) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 78) (by norm_num)).2.2
  have v4980 : σ (.n 4980) = ev 39 := by
    rw [← hev 39 (by norm_num)]; exact (vt_eval h (k := 106) (by norm_num)).2.2
  have v4991 : σ (.n 4991) = ev 40 := by
    rw [← hev 40 (by norm_num)]; exact (vt_eval h (k := 107) (by norm_num)).2.2
  have v5015 : σ (.n 5015) = ev 41 := by
    rw [← hev 41 (by norm_num)]; exact (vt_eval h (k := 108) (by norm_num)).2.2
  have v5528 : σ (.n 5528) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_eval h (k := 144) (by norm_num)).2.2
  have hB : σ (.n 6231) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 2)], [([77], 2)], [([40], 1), ([11, 40], 1), ([11, 39], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)], [([], 0)]] := by
    simp only [v5528, v5015, v4991, v4980, v4581, v4559, v4445, a5663, a5662, a5661, a5660, e5659, a5658,
      a5657, e5656, a5655, a5654, a5653, a5652, a5651, a5650, e5649, a5648, a5647, a5646,
      a5645, a5644, a5643, e5642, a5641, a5640, a5639, a5638, e5637, a5636, a5635, a5634,
      a5633, a5632, e5631]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5665, a5664, hB]

set_option maxRecDepth 10000 in
theorem vtB05_17 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6268) = σ (.n 6233) + σ (.n 1296) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 4)], [([78], 2)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5666 [
    .atom (.load (.n 6234) (.n 13) 0),
    .atom (.const (.n 6235) (word 2 0 0)),
    .atom (.mul (.n 6236) (.n 6234) (.n 6235)),
    .atom (.const (.n 6237) (word 4 0 0)),
    .atom (.mul (.n 6238) (.n 4445) (.n 4559)),
    .atom (.mul (.n 6239) (.n 6237) (.n 6238)),
    .atom (.load (.n 6240) (.n 13) 1),
    .atom (.mul (.n 6241) (.n 6240) (.n 6239)),
    .atom (.add (.n 6242) (.n 6236) (.n 6241)),
    .atom (.const (.n 6243) (word 2 0 0)),
    .atom (.mul (.n 6244) (.n 6243) (.n 5539)),
    .atom (.load (.n 6245) (.n 13) 2),
    .atom (.mul (.n 6246) (.n 6245) (.n 6244)),
    .atom (.add (.n 6247) (.n 6242) (.n 6246)),
    .atom (.mul (.n 6248) (.n 4581) (.n 5026)),
    .atom (.add (.n 6249) (.n 5026) (.n 6248)),
    .atom (.mul (.n 6250) (.n 4581) (.n 5015)),
    .atom (.add (.n 6251) (.n 6249) (.n 6250)),
    .atom (.load (.n 6252) (.n 13) 3),
    .atom (.mul (.n 6253) (.n 6252) (.n 6251)),
    .atom (.add (.n 6254) (.n 6247) (.n 6253)),
    .atom (.mul (.n 6255) (.n 4581) (.n 5037)),
    .atom (.add (.n 6256) (.n 5037) (.n 6255)),
    .atom (.mul (.n 6257) (.n 4581) (.n 5026)),
    .atom (.add (.n 6258) (.n 6256) (.n 6257)),
    .atom (.load (.n 6259) (.n 13) 4),
    .atom (.mul (.n 6260) (.n 6259) (.n 6258)),
    .atom (.add (.n 6261) (.n 6254) (.n 6260)),
    .atom (.load (.n 6262) (.n 13) 5),
    .atom (.const (.n 6263) (word 0 0 0)),
    .atom (.mul (.n 6264) (.n 6262) (.n 6263)),
    .atom (.add (.n 6265) (.n 6261) (.n 6264)),
    .atom (.add (.n 6266) (.n 14) (.n 6265)),
    .atom (.mul (.n 6267) (.n 1296) (.n 6266)),
    .atom (.add (.n 6268) (.n 6233) (.n 6267))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5666, a5667, a5668, a5669, a5670, a5671, a5672, a5673, a5674, a5675, a5676, a5677, a5678, a5679,
    a5680, a5681, a5682, a5683, a5684, a5685, a5686, a5687, a5688, a5689, a5690, a5691, a5692,
    a5693, a5694, a5695, a5696, a5697, a5698, a5699, a5700, -⟩ := hs
  have e5666 := tb_loadHolds_unique a5666 (hw 0 (by norm_num))
  have e5672 := tb_loadHolds_unique a5672 (hw 1 (by norm_num))
  have e5677 := tb_loadHolds_unique a5677 (hw 2 (by norm_num))
  have e5684 := tb_loadHolds_unique a5684 (hw 3 (by norm_num))
  have e5691 := tb_loadHolds_unique a5691 (hw 4 (by norm_num))
  have e5694 := tb_loadHolds_unique a5694 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v4581 : σ (.n 4581) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 78) (by norm_num)).2.2
  have v5015 : σ (.n 5015) = ev 41 := by
    rw [← hev 41 (by norm_num)]; exact (vt_eval h (k := 108) (by norm_num)).2.2
  have v5026 : σ (.n 5026) = ev 42 := by
    rw [← hev 42 (by norm_num)]; exact (vt_eval h (k := 109) (by norm_num)).2.2
  have v5037 : σ (.n 5037) = ev 43 := by
    rw [← hev 43 (by norm_num)]; exact (vt_eval h (k := 110) (by norm_num)).2.2
  have v5539 : σ (.n 5539) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_eval h (k := 145) (by norm_num)).2.2
  have hB : σ (.n 6266) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 4)], [([78], 2)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)], [([], 0)]] := by
    simp only [v5539, v5037, v5026, v5015, v4581, v4559, v4445, a5698, a5697, a5696, a5695, e5694, a5693,
      a5692, e5691, a5690, a5689, a5688, a5687, a5686, a5685, e5684, a5683, a5682, a5681,
      a5680, a5679, a5678, e5677, a5676, a5675, a5674, a5673, e5672, a5671, a5670, a5669,
      a5668, a5667, e5666]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5700, a5699, hB]

set_option maxRecDepth 10000 in
theorem vtB05_18 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6303) = σ (.n 6268) + σ (.n 1305) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 8)], [([79], 2)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5701 [
    .atom (.load (.n 6269) (.n 13) 0),
    .atom (.const (.n 6270) (word 2 0 0)),
    .atom (.mul (.n 6271) (.n 6269) (.n 6270)),
    .atom (.const (.n 6272) (word 8 0 0)),
    .atom (.mul (.n 6273) (.n 4445) (.n 4559)),
    .atom (.mul (.n 6274) (.n 6272) (.n 6273)),
    .atom (.load (.n 6275) (.n 13) 1),
    .atom (.mul (.n 6276) (.n 6275) (.n 6274)),
    .atom (.add (.n 6277) (.n 6271) (.n 6276)),
    .atom (.const (.n 6278) (word 2 0 0)),
    .atom (.mul (.n 6279) (.n 6278) (.n 5550)),
    .atom (.load (.n 6280) (.n 13) 2),
    .atom (.mul (.n 6281) (.n 6280) (.n 6279)),
    .atom (.add (.n 6282) (.n 6277) (.n 6281)),
    .atom (.mul (.n 6283) (.n 4581) (.n 5048)),
    .atom (.add (.n 6284) (.n 5048) (.n 6283)),
    .atom (.mul (.n 6285) (.n 4581) (.n 5037)),
    .atom (.add (.n 6286) (.n 6284) (.n 6285)),
    .atom (.load (.n 6287) (.n 13) 3),
    .atom (.mul (.n 6288) (.n 6287) (.n 6286)),
    .atom (.add (.n 6289) (.n 6282) (.n 6288)),
    .atom (.mul (.n 6290) (.n 4581) (.n 5072)),
    .atom (.add (.n 6291) (.n 5072) (.n 6290)),
    .atom (.mul (.n 6292) (.n 4581) (.n 5048)),
    .atom (.add (.n 6293) (.n 6291) (.n 6292)),
    .atom (.load (.n 6294) (.n 13) 4),
    .atom (.mul (.n 6295) (.n 6294) (.n 6293)),
    .atom (.add (.n 6296) (.n 6289) (.n 6295)),
    .atom (.load (.n 6297) (.n 13) 5),
    .atom (.const (.n 6298) (word 0 0 0)),
    .atom (.mul (.n 6299) (.n 6297) (.n 6298)),
    .atom (.add (.n 6300) (.n 6296) (.n 6299)),
    .atom (.add (.n 6301) (.n 14) (.n 6300)),
    .atom (.mul (.n 6302) (.n 1305) (.n 6301)),
    .atom (.add (.n 6303) (.n 6268) (.n 6302))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5701, a5702, a5703, a5704, a5705, a5706, a5707, a5708, a5709, a5710, a5711, a5712, a5713, a5714,
    a5715, a5716, a5717, a5718, a5719, a5720, a5721, a5722, a5723, a5724, a5725, a5726, a5727,
    a5728, a5729, a5730, a5731, a5732, a5733, a5734, a5735, -⟩ := hs
  have e5701 := tb_loadHolds_unique a5701 (hw 0 (by norm_num))
  have e5707 := tb_loadHolds_unique a5707 (hw 1 (by norm_num))
  have e5712 := tb_loadHolds_unique a5712 (hw 2 (by norm_num))
  have e5719 := tb_loadHolds_unique a5719 (hw 3 (by norm_num))
  have e5726 := tb_loadHolds_unique a5726 (hw 4 (by norm_num))
  have e5729 := tb_loadHolds_unique a5729 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v4581 : σ (.n 4581) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 78) (by norm_num)).2.2
  have v5037 : σ (.n 5037) = ev 43 := by
    rw [← hev 43 (by norm_num)]; exact (vt_eval h (k := 110) (by norm_num)).2.2
  have v5048 : σ (.n 5048) = ev 44 := by
    rw [← hev 44 (by norm_num)]; exact (vt_eval h (k := 111) (by norm_num)).2.2
  have v5072 : σ (.n 5072) = ev 45 := by
    rw [← hev 45 (by norm_num)]; exact (vt_eval h (k := 112) (by norm_num)).2.2
  have v5550 : σ (.n 5550) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_eval h (k := 146) (by norm_num)).2.2
  have hB : σ (.n 6301) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 8)], [([79], 2)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)], [([], 0)]] := by
    simp only [v5550, v5072, v5048, v5037, v4581, v4559, v4445, a5733, a5732, a5731, a5730, e5729, a5728,
      a5727, e5726, a5725, a5724, a5723, a5722, a5721, a5720, e5719, a5718, a5717, a5716,
      a5715, a5714, a5713, e5712, a5711, a5710, a5709, a5708, e5707, a5706, a5705, a5704,
      a5703, a5702, e5701]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5735, a5734, hB]

set_option maxRecDepth 10000 in
theorem vtB05_19 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6338) = σ (.n 6303) + σ (.n 1314) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 16)], [([80], 2)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5736 [
    .atom (.load (.n 6304) (.n 13) 0),
    .atom (.const (.n 6305) (word 2 0 0)),
    .atom (.mul (.n 6306) (.n 6304) (.n 6305)),
    .atom (.const (.n 6307) (word 16 0 0)),
    .atom (.mul (.n 6308) (.n 4445) (.n 4559)),
    .atom (.mul (.n 6309) (.n 6307) (.n 6308)),
    .atom (.load (.n 6310) (.n 13) 1),
    .atom (.mul (.n 6311) (.n 6310) (.n 6309)),
    .atom (.add (.n 6312) (.n 6306) (.n 6311)),
    .atom (.const (.n 6313) (word 2 0 0)),
    .atom (.mul (.n 6314) (.n 6313) (.n 5561)),
    .atom (.load (.n 6315) (.n 13) 2),
    .atom (.mul (.n 6316) (.n 6315) (.n 6314)),
    .atom (.add (.n 6317) (.n 6312) (.n 6316)),
    .atom (.mul (.n 6318) (.n 4581) (.n 5083)),
    .atom (.add (.n 6319) (.n 5083) (.n 6318)),
    .atom (.mul (.n 6320) (.n 4581) (.n 5072)),
    .atom (.add (.n 6321) (.n 6319) (.n 6320)),
    .atom (.load (.n 6322) (.n 13) 3),
    .atom (.mul (.n 6323) (.n 6322) (.n 6321)),
    .atom (.add (.n 6324) (.n 6317) (.n 6323)),
    .atom (.mul (.n 6325) (.n 4581) (.n 5094)),
    .atom (.add (.n 6326) (.n 5094) (.n 6325)),
    .atom (.mul (.n 6327) (.n 4581) (.n 5083)),
    .atom (.add (.n 6328) (.n 6326) (.n 6327)),
    .atom (.load (.n 6329) (.n 13) 4),
    .atom (.mul (.n 6330) (.n 6329) (.n 6328)),
    .atom (.add (.n 6331) (.n 6324) (.n 6330)),
    .atom (.load (.n 6332) (.n 13) 5),
    .atom (.const (.n 6333) (word 0 0 0)),
    .atom (.mul (.n 6334) (.n 6332) (.n 6333)),
    .atom (.add (.n 6335) (.n 6331) (.n 6334)),
    .atom (.add (.n 6336) (.n 14) (.n 6335)),
    .atom (.mul (.n 6337) (.n 1314) (.n 6336)),
    .atom (.add (.n 6338) (.n 6303) (.n 6337))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5736, a5737, a5738, a5739, a5740, a5741, a5742, a5743, a5744, a5745, a5746, a5747, a5748, a5749,
    a5750, a5751, a5752, a5753, a5754, a5755, a5756, a5757, a5758, a5759, a5760, a5761, a5762,
    a5763, a5764, a5765, a5766, a5767, a5768, a5769, a5770, -⟩ := hs
  have e5736 := tb_loadHolds_unique a5736 (hw 0 (by norm_num))
  have e5742 := tb_loadHolds_unique a5742 (hw 1 (by norm_num))
  have e5747 := tb_loadHolds_unique a5747 (hw 2 (by norm_num))
  have e5754 := tb_loadHolds_unique a5754 (hw 3 (by norm_num))
  have e5761 := tb_loadHolds_unique a5761 (hw 4 (by norm_num))
  have e5764 := tb_loadHolds_unique a5764 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v4581 : σ (.n 4581) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 78) (by norm_num)).2.2
  have v5072 : σ (.n 5072) = ev 45 := by
    rw [← hev 45 (by norm_num)]; exact (vt_eval h (k := 112) (by norm_num)).2.2
  have v5083 : σ (.n 5083) = ev 46 := by
    rw [← hev 46 (by norm_num)]; exact (vt_eval h (k := 113) (by norm_num)).2.2
  have v5094 : σ (.n 5094) = ev 47 := by
    rw [← hev 47 (by norm_num)]; exact (vt_eval h (k := 114) (by norm_num)).2.2
  have v5561 : σ (.n 5561) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_eval h (k := 147) (by norm_num)).2.2
  have hB : σ (.n 6336) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 16)], [([80], 2)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)], [([], 0)]] := by
    simp only [v5561, v5094, v5083, v5072, v4581, v4559, v4445, a5768, a5767, a5766, a5765, e5764, a5763,
      a5762, e5761, a5760, a5759, a5758, a5757, a5756, a5755, e5754, a5753, a5752, a5751,
      a5750, a5749, a5748, e5747, a5746, a5745, a5744, a5743, e5742, a5741, a5740, a5739,
      a5738, a5737, e5736]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5770, a5769, hB]

set_option maxRecDepth 10000 in
theorem vtB05_20 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6373) = σ (.n 6338) + σ (.n 1323) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 32)], [([81], 2)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5771 [
    .atom (.load (.n 6339) (.n 13) 0),
    .atom (.const (.n 6340) (word 2 0 0)),
    .atom (.mul (.n 6341) (.n 6339) (.n 6340)),
    .atom (.const (.n 6342) (word 32 0 0)),
    .atom (.mul (.n 6343) (.n 4445) (.n 4559)),
    .atom (.mul (.n 6344) (.n 6342) (.n 6343)),
    .atom (.load (.n 6345) (.n 13) 1),
    .atom (.mul (.n 6346) (.n 6345) (.n 6344)),
    .atom (.add (.n 6347) (.n 6341) (.n 6346)),
    .atom (.const (.n 6348) (word 2 0 0)),
    .atom (.mul (.n 6349) (.n 6348) (.n 5585)),
    .atom (.load (.n 6350) (.n 13) 2),
    .atom (.mul (.n 6351) (.n 6350) (.n 6349)),
    .atom (.add (.n 6352) (.n 6347) (.n 6351)),
    .atom (.mul (.n 6353) (.n 4581) (.n 5105)),
    .atom (.add (.n 6354) (.n 5105) (.n 6353)),
    .atom (.mul (.n 6355) (.n 4581) (.n 5094)),
    .atom (.add (.n 6356) (.n 6354) (.n 6355)),
    .atom (.load (.n 6357) (.n 13) 3),
    .atom (.mul (.n 6358) (.n 6357) (.n 6356)),
    .atom (.add (.n 6359) (.n 6352) (.n 6358)),
    .atom (.mul (.n 6360) (.n 4581) (.n 5129)),
    .atom (.add (.n 6361) (.n 5129) (.n 6360)),
    .atom (.mul (.n 6362) (.n 4581) (.n 5105)),
    .atom (.add (.n 6363) (.n 6361) (.n 6362)),
    .atom (.load (.n 6364) (.n 13) 4),
    .atom (.mul (.n 6365) (.n 6364) (.n 6363)),
    .atom (.add (.n 6366) (.n 6359) (.n 6365)),
    .atom (.load (.n 6367) (.n 13) 5),
    .atom (.const (.n 6368) (word 0 0 0)),
    .atom (.mul (.n 6369) (.n 6367) (.n 6368)),
    .atom (.add (.n 6370) (.n 6366) (.n 6369)),
    .atom (.add (.n 6371) (.n 14) (.n 6370)),
    .atom (.mul (.n 6372) (.n 1323) (.n 6371)),
    .atom (.add (.n 6373) (.n 6338) (.n 6372))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5771, a5772, a5773, a5774, a5775, a5776, a5777, a5778, a5779, a5780, a5781, a5782, a5783, a5784,
    a5785, a5786, a5787, a5788, a5789, a5790, a5791, a5792, a5793, a5794, a5795, a5796, a5797,
    a5798, a5799, a5800, a5801, a5802, a5803, a5804, a5805, -⟩ := hs
  have e5771 := tb_loadHolds_unique a5771 (hw 0 (by norm_num))
  have e5777 := tb_loadHolds_unique a5777 (hw 1 (by norm_num))
  have e5782 := tb_loadHolds_unique a5782 (hw 2 (by norm_num))
  have e5789 := tb_loadHolds_unique a5789 (hw 3 (by norm_num))
  have e5796 := tb_loadHolds_unique a5796 (hw 4 (by norm_num))
  have e5799 := tb_loadHolds_unique a5799 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v4581 : σ (.n 4581) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 78) (by norm_num)).2.2
  have v5094 : σ (.n 5094) = ev 47 := by
    rw [← hev 47 (by norm_num)]; exact (vt_eval h (k := 114) (by norm_num)).2.2
  have v5105 : σ (.n 5105) = ev 48 := by
    rw [← hev 48 (by norm_num)]; exact (vt_eval h (k := 115) (by norm_num)).2.2
  have v5129 : σ (.n 5129) = ev 49 := by
    rw [← hev 49 (by norm_num)]; exact (vt_eval h (k := 116) (by norm_num)).2.2
  have v5585 : σ (.n 5585) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_eval h (k := 148) (by norm_num)).2.2
  have hB : σ (.n 6371) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 32)], [([81], 2)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)], [([], 0)]] := by
    simp only [v5585, v5129, v5105, v5094, v4581, v4559, v4445, a5803, a5802, a5801, a5800, e5799, a5798,
      a5797, e5796, a5795, a5794, a5793, a5792, a5791, a5790, e5789, a5788, a5787, a5786,
      a5785, a5784, a5783, e5782, a5781, a5780, a5779, a5778, e5777, a5776, a5775, a5774,
      a5773, a5772, e5771]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5805, a5804, hB]

set_option maxRecDepth 10000 in
theorem vtB05_21 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6408) = σ (.n 6373) + σ (.n 1332) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 64)], [([82], 2)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5806 [
    .atom (.load (.n 6374) (.n 13) 0),
    .atom (.const (.n 6375) (word 2 0 0)),
    .atom (.mul (.n 6376) (.n 6374) (.n 6375)),
    .atom (.const (.n 6377) (word 64 0 0)),
    .atom (.mul (.n 6378) (.n 4445) (.n 4559)),
    .atom (.mul (.n 6379) (.n 6377) (.n 6378)),
    .atom (.load (.n 6380) (.n 13) 1),
    .atom (.mul (.n 6381) (.n 6380) (.n 6379)),
    .atom (.add (.n 6382) (.n 6376) (.n 6381)),
    .atom (.const (.n 6383) (word 2 0 0)),
    .atom (.mul (.n 6384) (.n 6383) (.n 5596)),
    .atom (.load (.n 6385) (.n 13) 2),
    .atom (.mul (.n 6386) (.n 6385) (.n 6384)),
    .atom (.add (.n 6387) (.n 6382) (.n 6386)),
    .atom (.mul (.n 6388) (.n 4581) (.n 5140)),
    .atom (.add (.n 6389) (.n 5140) (.n 6388)),
    .atom (.mul (.n 6390) (.n 4581) (.n 5129)),
    .atom (.add (.n 6391) (.n 6389) (.n 6390)),
    .atom (.load (.n 6392) (.n 13) 3),
    .atom (.mul (.n 6393) (.n 6392) (.n 6391)),
    .atom (.add (.n 6394) (.n 6387) (.n 6393)),
    .atom (.mul (.n 6395) (.n 4581) (.n 5151)),
    .atom (.add (.n 6396) (.n 5151) (.n 6395)),
    .atom (.mul (.n 6397) (.n 4581) (.n 5140)),
    .atom (.add (.n 6398) (.n 6396) (.n 6397)),
    .atom (.load (.n 6399) (.n 13) 4),
    .atom (.mul (.n 6400) (.n 6399) (.n 6398)),
    .atom (.add (.n 6401) (.n 6394) (.n 6400)),
    .atom (.load (.n 6402) (.n 13) 5),
    .atom (.const (.n 6403) (word 0 0 0)),
    .atom (.mul (.n 6404) (.n 6402) (.n 6403)),
    .atom (.add (.n 6405) (.n 6401) (.n 6404)),
    .atom (.add (.n 6406) (.n 14) (.n 6405)),
    .atom (.mul (.n 6407) (.n 1332) (.n 6406)),
    .atom (.add (.n 6408) (.n 6373) (.n 6407))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5806, a5807, a5808, a5809, a5810, a5811, a5812, a5813, a5814, a5815, a5816, a5817, a5818, a5819,
    a5820, a5821, a5822, a5823, a5824, a5825, a5826, a5827, a5828, a5829, a5830, a5831, a5832,
    a5833, a5834, a5835, a5836, a5837, a5838, a5839, a5840, -⟩ := hs
  have e5806 := tb_loadHolds_unique a5806 (hw 0 (by norm_num))
  have e5812 := tb_loadHolds_unique a5812 (hw 1 (by norm_num))
  have e5817 := tb_loadHolds_unique a5817 (hw 2 (by norm_num))
  have e5824 := tb_loadHolds_unique a5824 (hw 3 (by norm_num))
  have e5831 := tb_loadHolds_unique a5831 (hw 4 (by norm_num))
  have e5834 := tb_loadHolds_unique a5834 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v4581 : σ (.n 4581) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 78) (by norm_num)).2.2
  have v5129 : σ (.n 5129) = ev 49 := by
    rw [← hev 49 (by norm_num)]; exact (vt_eval h (k := 116) (by norm_num)).2.2
  have v5140 : σ (.n 5140) = ev 50 := by
    rw [← hev 50 (by norm_num)]; exact (vt_eval h (k := 117) (by norm_num)).2.2
  have v5151 : σ (.n 5151) = ev 51 := by
    rw [← hev 51 (by norm_num)]; exact (vt_eval h (k := 118) (by norm_num)).2.2
  have v5596 : σ (.n 5596) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_eval h (k := 149) (by norm_num)).2.2
  have hB : σ (.n 6406) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 64)], [([82], 2)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)], [([], 0)]] := by
    simp only [v5596, v5151, v5140, v5129, v4581, v4559, v4445, a5838, a5837, a5836, a5835, e5834, a5833,
      a5832, e5831, a5830, a5829, a5828, a5827, a5826, a5825, e5824, a5823, a5822, a5821,
      a5820, a5819, a5818, e5817, a5816, a5815, a5814, a5813, e5812, a5811, a5810, a5809,
      a5808, a5807, e5806]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5840, a5839, hB]

set_option maxRecDepth 10000 in
theorem vtB05_22 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6443) = σ (.n 6408) + σ (.n 1341) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 128)], [([83], 2)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5841 [
    .atom (.load (.n 6409) (.n 13) 0),
    .atom (.const (.n 6410) (word 2 0 0)),
    .atom (.mul (.n 6411) (.n 6409) (.n 6410)),
    .atom (.const (.n 6412) (word 128 0 0)),
    .atom (.mul (.n 6413) (.n 4445) (.n 4559)),
    .atom (.mul (.n 6414) (.n 6412) (.n 6413)),
    .atom (.load (.n 6415) (.n 13) 1),
    .atom (.mul (.n 6416) (.n 6415) (.n 6414)),
    .atom (.add (.n 6417) (.n 6411) (.n 6416)),
    .atom (.const (.n 6418) (word 2 0 0)),
    .atom (.mul (.n 6419) (.n 6418) (.n 5607)),
    .atom (.load (.n 6420) (.n 13) 2),
    .atom (.mul (.n 6421) (.n 6420) (.n 6419)),
    .atom (.add (.n 6422) (.n 6417) (.n 6421)),
    .atom (.mul (.n 6423) (.n 4581) (.n 5162)),
    .atom (.add (.n 6424) (.n 5162) (.n 6423)),
    .atom (.mul (.n 6425) (.n 4581) (.n 5151)),
    .atom (.add (.n 6426) (.n 6424) (.n 6425)),
    .atom (.load (.n 6427) (.n 13) 3),
    .atom (.mul (.n 6428) (.n 6427) (.n 6426)),
    .atom (.add (.n 6429) (.n 6422) (.n 6428)),
    .atom (.mul (.n 6430) (.n 4581) (.n 5186)),
    .atom (.add (.n 6431) (.n 5186) (.n 6430)),
    .atom (.mul (.n 6432) (.n 4581) (.n 5162)),
    .atom (.add (.n 6433) (.n 6431) (.n 6432)),
    .atom (.load (.n 6434) (.n 13) 4),
    .atom (.mul (.n 6435) (.n 6434) (.n 6433)),
    .atom (.add (.n 6436) (.n 6429) (.n 6435)),
    .atom (.load (.n 6437) (.n 13) 5),
    .atom (.const (.n 6438) (word 0 0 0)),
    .atom (.mul (.n 6439) (.n 6437) (.n 6438)),
    .atom (.add (.n 6440) (.n 6436) (.n 6439)),
    .atom (.add (.n 6441) (.n 14) (.n 6440)),
    .atom (.mul (.n 6442) (.n 1341) (.n 6441)),
    .atom (.add (.n 6443) (.n 6408) (.n 6442))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5841, a5842, a5843, a5844, a5845, a5846, a5847, a5848, a5849, a5850, a5851, a5852, a5853, a5854,
    a5855, a5856, a5857, a5858, a5859, a5860, a5861, a5862, a5863, a5864, a5865, a5866, a5867,
    a5868, a5869, a5870, a5871, a5872, a5873, a5874, a5875, -⟩ := hs
  have e5841 := tb_loadHolds_unique a5841 (hw 0 (by norm_num))
  have e5847 := tb_loadHolds_unique a5847 (hw 1 (by norm_num))
  have e5852 := tb_loadHolds_unique a5852 (hw 2 (by norm_num))
  have e5859 := tb_loadHolds_unique a5859 (hw 3 (by norm_num))
  have e5866 := tb_loadHolds_unique a5866 (hw 4 (by norm_num))
  have e5869 := tb_loadHolds_unique a5869 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v4581 : σ (.n 4581) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 78) (by norm_num)).2.2
  have v5151 : σ (.n 5151) = ev 51 := by
    rw [← hev 51 (by norm_num)]; exact (vt_eval h (k := 118) (by norm_num)).2.2
  have v5162 : σ (.n 5162) = ev 52 := by
    rw [← hev 52 (by norm_num)]; exact (vt_eval h (k := 119) (by norm_num)).2.2
  have v5186 : σ (.n 5186) = ev 53 := by
    rw [← hev 53 (by norm_num)]; exact (vt_eval h (k := 120) (by norm_num)).2.2
  have v5607 : σ (.n 5607) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_eval h (k := 150) (by norm_num)).2.2
  have hB : σ (.n 6441) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 128)], [([83], 2)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)], [([], 0)]] := by
    simp only [v5607, v5186, v5162, v5151, v4581, v4559, v4445, a5873, a5872, a5871, a5870, e5869, a5868,
      a5867, e5866, a5865, a5864, a5863, a5862, a5861, a5860, e5859, a5858, a5857, a5856,
      a5855, a5854, a5853, e5852, a5851, a5850, a5849, a5848, e5847, a5846, a5845, a5844,
      a5843, a5842, e5841]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5875, a5874, hB]

set_option maxRecDepth 10000 in
theorem vtB05_23 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6475) = σ (.n 6443) + σ (.n 1350) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 256)], [([84], 2)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([11, 54], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5876 [
    .atom (.load (.n 6444) (.n 13) 0),
    .atom (.const (.n 6445) (word 2 0 0)),
    .atom (.mul (.n 6446) (.n 6444) (.n 6445)),
    .atom (.const (.n 6447) (word 256 0 0)),
    .atom (.mul (.n 6448) (.n 4445) (.n 4559)),
    .atom (.mul (.n 6449) (.n 6447) (.n 6448)),
    .atom (.load (.n 6450) (.n 13) 1),
    .atom (.mul (.n 6451) (.n 6450) (.n 6449)),
    .atom (.add (.n 6452) (.n 6446) (.n 6451)),
    .atom (.const (.n 6453) (word 2 0 0)),
    .atom (.mul (.n 6454) (.n 6453) (.n 5618)),
    .atom (.load (.n 6455) (.n 13) 2),
    .atom (.mul (.n 6456) (.n 6455) (.n 6454)),
    .atom (.add (.n 6457) (.n 6452) (.n 6456)),
    .atom (.mul (.n 6458) (.n 4581) (.n 5197)),
    .atom (.add (.n 6459) (.n 5197) (.n 6458)),
    .atom (.mul (.n 6460) (.n 4581) (.n 5186)),
    .atom (.add (.n 6461) (.n 6459) (.n 6460)),
    .atom (.load (.n 6462) (.n 13) 3),
    .atom (.mul (.n 6463) (.n 6462) (.n 6461)),
    .atom (.add (.n 6464) (.n 6457) (.n 6463)),
    .atom (.mul (.n 6465) (.n 4581) (.n 5197)),
    .atom (.load (.n 6466) (.n 13) 4),
    .atom (.mul (.n 6467) (.n 6466) (.n 6465)),
    .atom (.add (.n 6468) (.n 6464) (.n 6467)),
    .atom (.load (.n 6469) (.n 13) 5),
    .atom (.const (.n 6470) (word 0 0 0)),
    .atom (.mul (.n 6471) (.n 6469) (.n 6470)),
    .atom (.add (.n 6472) (.n 6468) (.n 6471)),
    .atom (.add (.n 6473) (.n 14) (.n 6472)),
    .atom (.mul (.n 6474) (.n 1350) (.n 6473)),
    .atom (.add (.n 6475) (.n 6443) (.n 6474))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5876, a5877, a5878, a5879, a5880, a5881, a5882, a5883, a5884, a5885, a5886, a5887, a5888, a5889,
    a5890, a5891, a5892, a5893, a5894, a5895, a5896, a5897, a5898, a5899, a5900, a5901, a5902,
    a5903, a5904, a5905, a5906, a5907, -⟩ := hs
  have e5876 := tb_loadHolds_unique a5876 (hw 0 (by norm_num))
  have e5882 := tb_loadHolds_unique a5882 (hw 1 (by norm_num))
  have e5887 := tb_loadHolds_unique a5887 (hw 2 (by norm_num))
  have e5894 := tb_loadHolds_unique a5894 (hw 3 (by norm_num))
  have e5898 := tb_loadHolds_unique a5898 (hw 4 (by norm_num))
  have e5901 := tb_loadHolds_unique a5901 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v4581 : σ (.n 4581) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 78) (by norm_num)).2.2
  have v5186 : σ (.n 5186) = ev 53 := by
    rw [← hev 53 (by norm_num)]; exact (vt_eval h (k := 120) (by norm_num)).2.2
  have v5197 : σ (.n 5197) = ev 54 := by
    rw [← hev 54 (by norm_num)]; exact (vt_eval h (k := 121) (by norm_num)).2.2
  have v5618 : σ (.n 5618) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_eval h (k := 151) (by norm_num)).2.2
  have hB : σ (.n 6473) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 256)], [([84], 2)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([11, 54], 1)], [([], 0)]] := by
    simp only [v5618, v5197, v5186, v4581, v4559, v4445, a5905, a5904, a5903, a5902, e5901, a5900, a5899,
      e5898, a5897, a5896, a5895, e5894, a5893, a5892, a5891, a5890, a5889, a5888, e5887,
      a5886, a5885, a5884, a5883, e5882, a5881, a5880, a5879, a5878, a5877, e5876]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5907, a5906, hB]

set_option maxRecDepth 10000 in
theorem vtB05_24 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6502) = σ (.n 6475) + σ (.n 1359) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 512)], [([85], 2)], [([55], 1)], [([56], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5908 [
    .atom (.load (.n 6476) (.n 13) 0),
    .atom (.const (.n 6477) (word 2 0 0)),
    .atom (.mul (.n 6478) (.n 6476) (.n 6477)),
    .atom (.const (.n 6479) (word 512 0 0)),
    .atom (.mul (.n 6480) (.n 4445) (.n 4559)),
    .atom (.mul (.n 6481) (.n 6479) (.n 6480)),
    .atom (.load (.n 6482) (.n 13) 1),
    .atom (.mul (.n 6483) (.n 6482) (.n 6481)),
    .atom (.add (.n 6484) (.n 6478) (.n 6483)),
    .atom (.const (.n 6485) (word 2 0 0)),
    .atom (.mul (.n 6486) (.n 6485) (.n 5642)),
    .atom (.load (.n 6487) (.n 13) 2),
    .atom (.mul (.n 6488) (.n 6487) (.n 6486)),
    .atom (.add (.n 6489) (.n 6484) (.n 6488)),
    .atom (.load (.n 6490) (.n 13) 3),
    .atom (.mul (.n 6491) (.n 6490) (.n 5208)),
    .atom (.add (.n 6492) (.n 6489) (.n 6491)),
    .atom (.load (.n 6493) (.n 13) 4),
    .atom (.mul (.n 6494) (.n 6493) (.n 5219)),
    .atom (.add (.n 6495) (.n 6492) (.n 6494)),
    .atom (.load (.n 6496) (.n 13) 5),
    .atom (.const (.n 6497) (word 0 0 0)),
    .atom (.mul (.n 6498) (.n 6496) (.n 6497)),
    .atom (.add (.n 6499) (.n 6495) (.n 6498)),
    .atom (.add (.n 6500) (.n 14) (.n 6499)),
    .atom (.mul (.n 6501) (.n 1359) (.n 6500)),
    .atom (.add (.n 6502) (.n 6475) (.n 6501))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5908, a5909, a5910, a5911, a5912, a5913, a5914, a5915, a5916, a5917, a5918, a5919, a5920, a5921,
    a5922, a5923, a5924, a5925, a5926, a5927, a5928, a5929, a5930, a5931, a5932, a5933, a5934, -⟩ := hs
  have e5908 := tb_loadHolds_unique a5908 (hw 0 (by norm_num))
  have e5914 := tb_loadHolds_unique a5914 (hw 1 (by norm_num))
  have e5919 := tb_loadHolds_unique a5919 (hw 2 (by norm_num))
  have e5922 := tb_loadHolds_unique a5922 (hw 3 (by norm_num))
  have e5925 := tb_loadHolds_unique a5925 (hw 4 (by norm_num))
  have e5928 := tb_loadHolds_unique a5928 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v5208 : σ (.n 5208) = ev 55 := by
    rw [← hev 55 (by norm_num)]; exact (vt_eval h (k := 122) (by norm_num)).2.2
  have v5219 : σ (.n 5219) = ev 56 := by
    rw [← hev 56 (by norm_num)]; exact (vt_eval h (k := 123) (by norm_num)).2.2
  have v5642 : σ (.n 5642) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_eval h (k := 152) (by norm_num)).2.2
  have hB : σ (.n 6500) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 512)], [([85], 2)], [([55], 1)], [([56], 1)], [([], 0)]] := by
    simp only [v5642, v5219, v5208, v4559, v4445, a5932, a5931, a5930, a5929, e5928, a5927, a5926, e5925,
      a5924, a5923, e5922, a5921, a5920, e5919, a5918, a5917, a5916, a5915, e5914, a5913,
      a5912, a5911, a5910, a5909, e5908]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5934, a5933, hB]

set_option maxRecDepth 10000 in
theorem vtB05_25 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6529) = σ (.n 6502) + σ (.n 1368) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 1024)], [([86], 2)], [([57], 1)], [([58], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5935 [
    .atom (.load (.n 6503) (.n 13) 0),
    .atom (.const (.n 6504) (word 2 0 0)),
    .atom (.mul (.n 6505) (.n 6503) (.n 6504)),
    .atom (.const (.n 6506) (word 1024 0 0)),
    .atom (.mul (.n 6507) (.n 4445) (.n 4559)),
    .atom (.mul (.n 6508) (.n 6506) (.n 6507)),
    .atom (.load (.n 6509) (.n 13) 1),
    .atom (.mul (.n 6510) (.n 6509) (.n 6508)),
    .atom (.add (.n 6511) (.n 6505) (.n 6510)),
    .atom (.const (.n 6512) (word 2 0 0)),
    .atom (.mul (.n 6513) (.n 6512) (.n 5653)),
    .atom (.load (.n 6514) (.n 13) 2),
    .atom (.mul (.n 6515) (.n 6514) (.n 6513)),
    .atom (.add (.n 6516) (.n 6511) (.n 6515)),
    .atom (.load (.n 6517) (.n 13) 3),
    .atom (.mul (.n 6518) (.n 6517) (.n 5243)),
    .atom (.add (.n 6519) (.n 6516) (.n 6518)),
    .atom (.load (.n 6520) (.n 13) 4),
    .atom (.mul (.n 6521) (.n 6520) (.n 5254)),
    .atom (.add (.n 6522) (.n 6519) (.n 6521)),
    .atom (.load (.n 6523) (.n 13) 5),
    .atom (.const (.n 6524) (word 0 0 0)),
    .atom (.mul (.n 6525) (.n 6523) (.n 6524)),
    .atom (.add (.n 6526) (.n 6522) (.n 6525)),
    .atom (.add (.n 6527) (.n 14) (.n 6526)),
    .atom (.mul (.n 6528) (.n 1368) (.n 6527)),
    .atom (.add (.n 6529) (.n 6502) (.n 6528))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5935, a5936, a5937, a5938, a5939, a5940, a5941, a5942, a5943, a5944, a5945, a5946, a5947, a5948,
    a5949, a5950, a5951, a5952, a5953, a5954, a5955, a5956, a5957, a5958, a5959, a5960, a5961, -⟩ := hs
  have e5935 := tb_loadHolds_unique a5935 (hw 0 (by norm_num))
  have e5941 := tb_loadHolds_unique a5941 (hw 1 (by norm_num))
  have e5946 := tb_loadHolds_unique a5946 (hw 2 (by norm_num))
  have e5949 := tb_loadHolds_unique a5949 (hw 3 (by norm_num))
  have e5952 := tb_loadHolds_unique a5952 (hw 4 (by norm_num))
  have e5955 := tb_loadHolds_unique a5955 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v5243 : σ (.n 5243) = ev 57 := by
    rw [← hev 57 (by norm_num)]; exact (vt_eval h (k := 124) (by norm_num)).2.2
  have v5254 : σ (.n 5254) = ev 58 := by
    rw [← hev 58 (by norm_num)]; exact (vt_eval h (k := 125) (by norm_num)).2.2
  have v5653 : σ (.n 5653) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_eval h (k := 153) (by norm_num)).2.2
  have hB : σ (.n 6527) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 1024)], [([86], 2)], [([57], 1)], [([58], 1)], [([], 0)]] := by
    simp only [v5653, v5254, v5243, v4559, v4445, a5959, a5958, a5957, a5956, e5955, a5954, a5953, e5952,
      a5951, a5950, e5949, a5948, a5947, e5946, a5945, a5944, a5943, a5942, e5941, a5940,
      a5939, a5938, a5937, a5936, e5935]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5961, a5960, hB]

set_option maxRecDepth 10000 in
theorem vtB05_26 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6556) = σ (.n 6529) + σ (.n 1377) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 2048)], [([87], 2)], [([59], 1)], [([60], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5962 [
    .atom (.load (.n 6530) (.n 13) 0),
    .atom (.const (.n 6531) (word 2 0 0)),
    .atom (.mul (.n 6532) (.n 6530) (.n 6531)),
    .atom (.const (.n 6533) (word 2048 0 0)),
    .atom (.mul (.n 6534) (.n 4445) (.n 4559)),
    .atom (.mul (.n 6535) (.n 6533) (.n 6534)),
    .atom (.load (.n 6536) (.n 13) 1),
    .atom (.mul (.n 6537) (.n 6536) (.n 6535)),
    .atom (.add (.n 6538) (.n 6532) (.n 6537)),
    .atom (.const (.n 6539) (word 2 0 0)),
    .atom (.mul (.n 6540) (.n 6539) (.n 5664)),
    .atom (.load (.n 6541) (.n 13) 2),
    .atom (.mul (.n 6542) (.n 6541) (.n 6540)),
    .atom (.add (.n 6543) (.n 6538) (.n 6542)),
    .atom (.load (.n 6544) (.n 13) 3),
    .atom (.mul (.n 6545) (.n 6544) (.n 5265)),
    .atom (.add (.n 6546) (.n 6543) (.n 6545)),
    .atom (.load (.n 6547) (.n 13) 4),
    .atom (.mul (.n 6548) (.n 6547) (.n 5276)),
    .atom (.add (.n 6549) (.n 6546) (.n 6548)),
    .atom (.load (.n 6550) (.n 13) 5),
    .atom (.const (.n 6551) (word 0 0 0)),
    .atom (.mul (.n 6552) (.n 6550) (.n 6551)),
    .atom (.add (.n 6553) (.n 6549) (.n 6552)),
    .atom (.add (.n 6554) (.n 14) (.n 6553)),
    .atom (.mul (.n 6555) (.n 1377) (.n 6554)),
    .atom (.add (.n 6556) (.n 6529) (.n 6555))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5962, a5963, a5964, a5965, a5966, a5967, a5968, a5969, a5970, a5971, a5972, a5973, a5974, a5975,
    a5976, a5977, a5978, a5979, a5980, a5981, a5982, a5983, a5984, a5985, a5986, a5987, a5988, -⟩ := hs
  have e5962 := tb_loadHolds_unique a5962 (hw 0 (by norm_num))
  have e5968 := tb_loadHolds_unique a5968 (hw 1 (by norm_num))
  have e5973 := tb_loadHolds_unique a5973 (hw 2 (by norm_num))
  have e5976 := tb_loadHolds_unique a5976 (hw 3 (by norm_num))
  have e5979 := tb_loadHolds_unique a5979 (hw 4 (by norm_num))
  have e5982 := tb_loadHolds_unique a5982 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v5265 : σ (.n 5265) = ev 59 := by
    rw [← hev 59 (by norm_num)]; exact (vt_eval h (k := 126) (by norm_num)).2.2
  have v5276 : σ (.n 5276) = ev 60 := by
    rw [← hev 60 (by norm_num)]; exact (vt_eval h (k := 127) (by norm_num)).2.2
  have v5664 : σ (.n 5664) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_eval h (k := 154) (by norm_num)).2.2
  have hB : σ (.n 6554) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 2048)], [([87], 2)], [([59], 1)], [([60], 1)], [([], 0)]] := by
    simp only [v5664, v5276, v5265, v4559, v4445, a5986, a5985, a5984, a5983, e5982, a5981, a5980, e5979,
      a5978, a5977, e5976, a5975, a5974, e5973, a5972, a5971, a5970, a5969, e5968, a5967,
      a5966, a5965, a5964, a5963, e5962]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5988, a5987, hB]

set_option maxRecDepth 10000 in
theorem vtB05_27 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6583) = σ (.n 6556) + σ (.n 1386) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 4096)], [([88], 2)], [([61], 1)], [([62], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5989 [
    .atom (.load (.n 6557) (.n 13) 0),
    .atom (.const (.n 6558) (word 2 0 0)),
    .atom (.mul (.n 6559) (.n 6557) (.n 6558)),
    .atom (.const (.n 6560) (word 4096 0 0)),
    .atom (.mul (.n 6561) (.n 4445) (.n 4559)),
    .atom (.mul (.n 6562) (.n 6560) (.n 6561)),
    .atom (.load (.n 6563) (.n 13) 1),
    .atom (.mul (.n 6564) (.n 6563) (.n 6562)),
    .atom (.add (.n 6565) (.n 6559) (.n 6564)),
    .atom (.const (.n 6566) (word 2 0 0)),
    .atom (.mul (.n 6567) (.n 6566) (.n 5675)),
    .atom (.load (.n 6568) (.n 13) 2),
    .atom (.mul (.n 6569) (.n 6568) (.n 6567)),
    .atom (.add (.n 6570) (.n 6565) (.n 6569)),
    .atom (.load (.n 6571) (.n 13) 3),
    .atom (.mul (.n 6572) (.n 6571) (.n 5300)),
    .atom (.add (.n 6573) (.n 6570) (.n 6572)),
    .atom (.load (.n 6574) (.n 13) 4),
    .atom (.mul (.n 6575) (.n 6574) (.n 5311)),
    .atom (.add (.n 6576) (.n 6573) (.n 6575)),
    .atom (.load (.n 6577) (.n 13) 5),
    .atom (.const (.n 6578) (word 0 0 0)),
    .atom (.mul (.n 6579) (.n 6577) (.n 6578)),
    .atom (.add (.n 6580) (.n 6576) (.n 6579)),
    .atom (.add (.n 6581) (.n 14) (.n 6580)),
    .atom (.mul (.n 6582) (.n 1386) (.n 6581)),
    .atom (.add (.n 6583) (.n 6556) (.n 6582))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5989, a5990, a5991, a5992, a5993, a5994, a5995, a5996, a5997, a5998, a5999, a6000, a6001, a6002,
    a6003, a6004, a6005, a6006, a6007, a6008, a6009, a6010, a6011, a6012, a6013, a6014, a6015, -⟩ := hs
  have e5989 := tb_loadHolds_unique a5989 (hw 0 (by norm_num))
  have e5995 := tb_loadHolds_unique a5995 (hw 1 (by norm_num))
  have e6000 := tb_loadHolds_unique a6000 (hw 2 (by norm_num))
  have e6003 := tb_loadHolds_unique a6003 (hw 3 (by norm_num))
  have e6006 := tb_loadHolds_unique a6006 (hw 4 (by norm_num))
  have e6009 := tb_loadHolds_unique a6009 (hw 5 (by norm_num))
  have v4445 : σ (.n 4445) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4559 : σ (.n 4559) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v5300 : σ (.n 5300) = ev 61 := by
    rw [← hev 61 (by norm_num)]; exact (vt_eval h (k := 128) (by norm_num)).2.2
  have v5311 : σ (.n 5311) = ev 62 := by
    rw [← hev 62 (by norm_num)]; exact (vt_eval h (k := 129) (by norm_num)).2.2
  have v5675 : σ (.n 5675) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_eval h (k := 155) (by norm_num)).2.2
  have hB : σ (.n 6581) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 4096)], [([88], 2)], [([61], 1)], [([62], 1)], [([], 0)]] := by
    simp only [v5675, v5311, v5300, v4559, v4445, a6013, a6012, a6011, a6010, e6009, a6008, a6007, e6006,
      a6005, a6004, e6003, a6002, a6001, e6000, a5999, a5998, a5997, a5996, e5995, a5994,
      a5993, a5992, a5991, a5990, e5989]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a6015, a6014, hB]

end
end LeanVM.Guest.B1.Tables
