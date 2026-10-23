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
theorem vtB15_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10313) = σ (.n 4730) * vtBlockVal (σ (.n 15)) W ev
      [[([], 1)], [([0], 1)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 9315 [
    .atom (.load (.n 10305) (.n 14) 0),
    .atom (.load (.n 10306) (.n 14) 1),
    .atom (.mul (.n 10307) (.n 10306) (.n 8141)),
    .atom (.add (.n 10308) (.n 10305) (.n 10307)),
    .atom (.load (.n 10309) (.n 14) 2),
    .atom (.mul (.n 10310) (.n 10309) (.n 8165)),
    .atom (.add (.n 10311) (.n 10308) (.n 10310)),
    .atom (.add (.n 10312) (.n 15) (.n 10311)),
    .atom (.mul (.n 10313) (.n 4730) (.n 10312))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9315, a9316, a9317, a9318, a9319, a9320, a9321, a9322, a9323, -⟩ := hs
  have e9315 := tb_loadHolds_unique a9315 (hw 0 (by norm_num))
  have e9316 := tb_loadHolds_unique a9316 (hw 1 (by norm_num))
  have e9319 := tb_loadHolds_unique a9319 (hw 2 (by norm_num))
  have v8141 : σ (.n 8141) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 67) (by norm_num)).2.2.1
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have hB : σ (.n 10312) = vtBlockVal (σ (.n 15)) W ev [[([], 1)], [([0], 1)], [([1], 1)]] := by
    simp only [v8165, v8141, a9322, a9321, a9320, e9319, a9318, a9317, e9316, e9315]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
    ring
  rw [a9323, hB]

set_option maxRecDepth 10000 in
theorem vtB15_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10359) = σ (.n 10313) + σ (.n 4737) * vtBlockVal (σ (.n 15)) W ev
      [[([], 4)], [([0], 1)], [([89], 1)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 9324 [
    .atom (.load (.n 10314) (.n 14) 0),
    .atom (.const (.n 10315) (word 4 0 0)),
    .atom (.mul (.n 10316) (.n 10314) (.n 10315)),
    .atom (.load (.n 10317) (.n 14) 1),
    .atom (.mul (.n 10318) (.n 10317) (.n 8141)),
    .atom (.add (.n 10319) (.n 10316) (.n 10318)),
    .atom (.load (.n 10320) (.n 14) 2),
    .atom (.mul (.n 10321) (.n 10320) (.n 9419)),
    .atom (.add (.n 10322) (.n 10319) (.n 10321)),
    .atom (.load (.n 10323) (.n 14) 3),
    .atom (.const (.n 10324) (word 32 0 0)),
    .atom (.mul (.n 10325) (.n 10323) (.n 10324)),
    .atom (.add (.n 10326) (.n 10322) (.n 10325)),
    .atom (.load (.n 10327) (.n 14) 4),
    .atom (.mul (.n 10328) (.n 10327) (.n 8176)),
    .atom (.add (.n 10329) (.n 10326) (.n 10328)),
    .atom (.load (.n 10330) (.n 14) 5),
    .atom (.mul (.n 10331) (.n 10330) (.n 8187)),
    .atom (.add (.n 10332) (.n 10329) (.n 10331)),
    .atom (.load (.n 10333) (.n 14) 6),
    .atom (.mul (.n 10334) (.n 10333) (.n 8198)),
    .atom (.add (.n 10335) (.n 10332) (.n 10334)),
    .atom (.load (.n 10336) (.n 14) 7),
    .atom (.mul (.n 10337) (.n 10336) (.n 8222)),
    .atom (.add (.n 10338) (.n 10335) (.n 10337)),
    .atom (.load (.n 10339) (.n 14) 8),
    .atom (.mul (.n 10340) (.n 10339) (.n 8233)),
    .atom (.add (.n 10341) (.n 10338) (.n 10340)),
    .atom (.load (.n 10342) (.n 14) 9),
    .atom (.mul (.n 10343) (.n 10342) (.n 8244)),
    .atom (.add (.n 10344) (.n 10341) (.n 10343)),
    .atom (.load (.n 10345) (.n 14) 10),
    .atom (.mul (.n 10346) (.n 10345) (.n 8255)),
    .atom (.add (.n 10347) (.n 10344) (.n 10346)),
    .atom (.load (.n 10348) (.n 14) 11),
    .atom (.mul (.n 10349) (.n 10348) (.n 8279)),
    .atom (.add (.n 10350) (.n 10347) (.n 10349)),
    .atom (.load (.n 10351) (.n 14) 12),
    .atom (.mul (.n 10352) (.n 10351) (.n 8290)),
    .atom (.add (.n 10353) (.n 10350) (.n 10352)),
    .atom (.load (.n 10354) (.n 14) 13),
    .atom (.mul (.n 10355) (.n 10354) (.n 8301)),
    .atom (.add (.n 10356) (.n 10353) (.n 10355)),
    .atom (.add (.n 10357) (.n 15) (.n 10356)),
    .atom (.mul (.n 10358) (.n 4737) (.n 10357)),
    .atom (.add (.n 10359) (.n 10313) (.n 10358))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9324, a9325, a9326, a9327, a9328, a9329, a9330, a9331, a9332, a9333, a9334, a9335, a9336, a9337,
    a9338, a9339, a9340, a9341, a9342, a9343, a9344, a9345, a9346, a9347, a9348, a9349, a9350,
    a9351, a9352, a9353, a9354, a9355, a9356, a9357, a9358, a9359, a9360, a9361, a9362, a9363,
    a9364, a9365, a9366, a9367, a9368, a9369, -⟩ := hs
  have e9324 := tb_loadHolds_unique a9324 (hw 0 (by norm_num))
  have e9327 := tb_loadHolds_unique a9327 (hw 1 (by norm_num))
  have e9330 := tb_loadHolds_unique a9330 (hw 2 (by norm_num))
  have e9333 := tb_loadHolds_unique a9333 (hw 3 (by norm_num))
  have e9337 := tb_loadHolds_unique a9337 (hw 4 (by norm_num))
  have e9340 := tb_loadHolds_unique a9340 (hw 5 (by norm_num))
  have e9343 := tb_loadHolds_unique a9343 (hw 6 (by norm_num))
  have e9346 := tb_loadHolds_unique a9346 (hw 7 (by norm_num))
  have e9349 := tb_loadHolds_unique a9349 (hw 8 (by norm_num))
  have e9352 := tb_loadHolds_unique a9352 (hw 9 (by norm_num))
  have e9355 := tb_loadHolds_unique a9355 (hw 10 (by norm_num))
  have e9358 := tb_loadHolds_unique a9358 (hw 11 (by norm_num))
  have e9361 := tb_loadHolds_unique a9361 (hw 12 (by norm_num))
  have e9364 := tb_loadHolds_unique a9364 (hw 13 (by norm_num))
  have v8141 : σ (.n 8141) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 67) (by norm_num)).2.2.1
  have v8176 : σ (.n 8176) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 69) (by norm_num)).2.2.1
  have v8187 : σ (.n 8187) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2.1
  have v8198 : σ (.n 8198) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2.1
  have v8222 : σ (.n 8222) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2.1
  have v8233 : σ (.n 8233) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2.1
  have v8244 : σ (.n 8244) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2.1
  have v8255 : σ (.n 8255) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 75) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8290 : σ (.n 8290) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2.1
  have v8301 : σ (.n 8301) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2.1
  have v9419 : σ (.n 9419) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_evalF h (k := 156) (by norm_num)).2.2.1
  have hB : σ (.n 10357) = vtBlockVal (σ (.n 15)) W ev [[([], 4)], [([0], 1)], [([89], 1)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)]] := by
    simp only [v9419, v8301, v8290, v8279, v8255, v8244, v8233, v8222, v8198, v8187, v8176, v8141, a9367,
      a9366, a9365, e9364, a9363, a9362, e9361, a9360, a9359, e9358, a9357, a9356, e9355,
      a9354, a9353, e9352, a9351, a9350, e9349, a9348, a9347, e9346, a9345, a9344, e9343,
      a9342, a9341, e9340, a9339, a9338, e9337, a9336, a9335, a9334, e9333, a9332, a9331,
      e9330, a9329, a9328, e9327, a9326, a9325, e9324]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a9369, a9368, hB]

set_option maxRecDepth 10000 in
theorem vtB15_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10390) = σ (.n 10359) + σ (.n 4744) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 2], 1)], [([63], 1)], [([13], 1), ([10, 13], 1), ([10, 12], 1)], [([14], 1), ([10, 14], 1), ([10, 13], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9370 [
    .atom (.load (.n 10360) (.n 14) 0),
    .atom (.const (.n 10361) (word 2 0 0)),
    .atom (.mul (.n 10362) (.n 10360) (.n 10361)),
    .atom (.mul (.n 10363) (.n 8165) (.n 8176)),
    .atom (.load (.n 10364) (.n 14) 1),
    .atom (.mul (.n 10365) (.n 10364) (.n 10363)),
    .atom (.add (.n 10366) (.n 10362) (.n 10365)),
    .atom (.load (.n 10367) (.n 14) 2),
    .atom (.mul (.n 10368) (.n 10367) (.n 9042)),
    .atom (.add (.n 10369) (.n 10366) (.n 10368)),
    .atom (.mul (.n 10370) (.n 8290) (.n 8336)),
    .atom (.add (.n 10371) (.n 8336) (.n 10370)),
    .atom (.mul (.n 10372) (.n 8290) (.n 8312)),
    .atom (.add (.n 10373) (.n 10371) (.n 10372)),
    .atom (.load (.n 10374) (.n 14) 3),
    .atom (.mul (.n 10375) (.n 10374) (.n 10373)),
    .atom (.add (.n 10376) (.n 10369) (.n 10375)),
    .atom (.mul (.n 10377) (.n 8290) (.n 8347)),
    .atom (.add (.n 10378) (.n 8347) (.n 10377)),
    .atom (.mul (.n 10379) (.n 8290) (.n 8336)),
    .atom (.add (.n 10380) (.n 10378) (.n 10379)),
    .atom (.load (.n 10381) (.n 14) 4),
    .atom (.mul (.n 10382) (.n 10381) (.n 10380)),
    .atom (.add (.n 10383) (.n 10376) (.n 10382)),
    .atom (.load (.n 10384) (.n 14) 5),
    .atom (.const (.n 10385) (word 0 0 0)),
    .atom (.mul (.n 10386) (.n 10384) (.n 10385)),
    .atom (.add (.n 10387) (.n 10383) (.n 10386)),
    .atom (.add (.n 10388) (.n 15) (.n 10387)),
    .atom (.mul (.n 10389) (.n 4744) (.n 10388)),
    .atom (.add (.n 10390) (.n 10359) (.n 10389))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9370, a9371, a9372, a9373, a9374, a9375, a9376, a9377, a9378, a9379, a9380, a9381, a9382, a9383,
    a9384, a9385, a9386, a9387, a9388, a9389, a9390, a9391, a9392, a9393, a9394, a9395, a9396,
    a9397, a9398, a9399, a9400, -⟩ := hs
  have e9370 := tb_loadHolds_unique a9370 (hw 0 (by norm_num))
  have e9374 := tb_loadHolds_unique a9374 (hw 1 (by norm_num))
  have e9377 := tb_loadHolds_unique a9377 (hw 2 (by norm_num))
  have e9384 := tb_loadHolds_unique a9384 (hw 3 (by norm_num))
  have e9391 := tb_loadHolds_unique a9391 (hw 4 (by norm_num))
  have e9394 := tb_loadHolds_unique a9394 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8176 : σ (.n 8176) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 69) (by norm_num)).2.2.1
  have v8290 : σ (.n 8290) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2.1
  have v8312 : σ (.n 8312) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 79) (by norm_num)).2.2.1
  have v8336 : σ (.n 8336) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2.1
  have v8347 : σ (.n 8347) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_evalF h (k := 81) (by norm_num)).2.2.1
  have v9042 : σ (.n 9042) = ev 63 := by
    rw [← hev 63 (by norm_num)]; exact (vt_evalF h (k := 130) (by norm_num)).2.2.1
  have hB : σ (.n 10388) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 2], 1)], [([63], 1)], [([13], 1), ([10, 13], 1), ([10, 12], 1)], [([14], 1), ([10, 14], 1), ([10, 13], 1)], [([], 0)]] := by
    simp only [v9042, v8347, v8336, v8312, v8290, v8176, v8165, a9398, a9397, a9396, a9395, e9394, a9393,
      a9392, e9391, a9390, a9389, a9388, a9387, a9386, a9385, e9384, a9383, a9382, a9381,
      a9380, a9379, a9378, e9377, a9376, a9375, e9374, a9373, a9372, a9371, e9370]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9400, a9399, hB]

set_option maxRecDepth 10000 in
theorem vtB15_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10421) = σ (.n 10390) + σ (.n 4751) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 3], 1)], [([64], 1)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9401 [
    .atom (.load (.n 10391) (.n 14) 0),
    .atom (.const (.n 10392) (word 2 0 0)),
    .atom (.mul (.n 10393) (.n 10391) (.n 10392)),
    .atom (.mul (.n 10394) (.n 8165) (.n 8187)),
    .atom (.load (.n 10395) (.n 14) 1),
    .atom (.mul (.n 10396) (.n 10395) (.n 10394)),
    .atom (.add (.n 10397) (.n 10393) (.n 10396)),
    .atom (.load (.n 10398) (.n 14) 2),
    .atom (.mul (.n 10399) (.n 10398) (.n 9053)),
    .atom (.add (.n 10400) (.n 10397) (.n 10399)),
    .atom (.mul (.n 10401) (.n 8290) (.n 8358)),
    .atom (.add (.n 10402) (.n 8358) (.n 10401)),
    .atom (.mul (.n 10403) (.n 8290) (.n 8347)),
    .atom (.add (.n 10404) (.n 10402) (.n 10403)),
    .atom (.load (.n 10405) (.n 14) 3),
    .atom (.mul (.n 10406) (.n 10405) (.n 10404)),
    .atom (.add (.n 10407) (.n 10400) (.n 10406)),
    .atom (.mul (.n 10408) (.n 8290) (.n 8369)),
    .atom (.add (.n 10409) (.n 8369) (.n 10408)),
    .atom (.mul (.n 10410) (.n 8290) (.n 8358)),
    .atom (.add (.n 10411) (.n 10409) (.n 10410)),
    .atom (.load (.n 10412) (.n 14) 4),
    .atom (.mul (.n 10413) (.n 10412) (.n 10411)),
    .atom (.add (.n 10414) (.n 10407) (.n 10413)),
    .atom (.load (.n 10415) (.n 14) 5),
    .atom (.const (.n 10416) (word 0 0 0)),
    .atom (.mul (.n 10417) (.n 10415) (.n 10416)),
    .atom (.add (.n 10418) (.n 10414) (.n 10417)),
    .atom (.add (.n 10419) (.n 15) (.n 10418)),
    .atom (.mul (.n 10420) (.n 4751) (.n 10419)),
    .atom (.add (.n 10421) (.n 10390) (.n 10420))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9401, a9402, a9403, a9404, a9405, a9406, a9407, a9408, a9409, a9410, a9411, a9412, a9413, a9414,
    a9415, a9416, a9417, a9418, a9419, a9420, a9421, a9422, a9423, a9424, a9425, a9426, a9427,
    a9428, a9429, a9430, a9431, -⟩ := hs
  have e9401 := tb_loadHolds_unique a9401 (hw 0 (by norm_num))
  have e9405 := tb_loadHolds_unique a9405 (hw 1 (by norm_num))
  have e9408 := tb_loadHolds_unique a9408 (hw 2 (by norm_num))
  have e9415 := tb_loadHolds_unique a9415 (hw 3 (by norm_num))
  have e9422 := tb_loadHolds_unique a9422 (hw 4 (by norm_num))
  have e9425 := tb_loadHolds_unique a9425 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8187 : σ (.n 8187) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2.1
  have v8290 : σ (.n 8290) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2.1
  have v8347 : σ (.n 8347) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_evalF h (k := 81) (by norm_num)).2.2.1
  have v8358 : σ (.n 8358) = ev 15 := by
    rw [← hev 15 (by norm_num)]; exact (vt_evalF h (k := 82) (by norm_num)).2.2.1
  have v8369 : σ (.n 8369) = ev 16 := by
    rw [← hev 16 (by norm_num)]; exact (vt_evalF h (k := 83) (by norm_num)).2.2.1
  have v9053 : σ (.n 9053) = ev 64 := by
    rw [← hev 64 (by norm_num)]; exact (vt_evalF h (k := 131) (by norm_num)).2.2.1
  have hB : σ (.n 10419) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 3], 1)], [([64], 1)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)], [([], 0)]] := by
    simp only [v9053, v8369, v8358, v8347, v8290, v8187, v8165, a9429, a9428, a9427, a9426, e9425, a9424,
      a9423, e9422, a9421, a9420, a9419, a9418, a9417, a9416, e9415, a9414, a9413, a9412,
      a9411, a9410, a9409, e9408, a9407, a9406, e9405, a9404, a9403, a9402, e9401]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9431, a9430, hB]

set_option maxRecDepth 10000 in
theorem vtB15_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10452) = σ (.n 10421) + σ (.n 4758) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 4], 1)], [([65], 1)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9432 [
    .atom (.load (.n 10422) (.n 14) 0),
    .atom (.const (.n 10423) (word 2 0 0)),
    .atom (.mul (.n 10424) (.n 10422) (.n 10423)),
    .atom (.mul (.n 10425) (.n 8165) (.n 8198)),
    .atom (.load (.n 10426) (.n 14) 1),
    .atom (.mul (.n 10427) (.n 10426) (.n 10425)),
    .atom (.add (.n 10428) (.n 10424) (.n 10427)),
    .atom (.load (.n 10429) (.n 14) 2),
    .atom (.mul (.n 10430) (.n 10429) (.n 9077)),
    .atom (.add (.n 10431) (.n 10428) (.n 10430)),
    .atom (.mul (.n 10432) (.n 8290) (.n 8393)),
    .atom (.add (.n 10433) (.n 8393) (.n 10432)),
    .atom (.mul (.n 10434) (.n 8290) (.n 8369)),
    .atom (.add (.n 10435) (.n 10433) (.n 10434)),
    .atom (.load (.n 10436) (.n 14) 3),
    .atom (.mul (.n 10437) (.n 10436) (.n 10435)),
    .atom (.add (.n 10438) (.n 10431) (.n 10437)),
    .atom (.mul (.n 10439) (.n 8290) (.n 8404)),
    .atom (.add (.n 10440) (.n 8404) (.n 10439)),
    .atom (.mul (.n 10441) (.n 8290) (.n 8393)),
    .atom (.add (.n 10442) (.n 10440) (.n 10441)),
    .atom (.load (.n 10443) (.n 14) 4),
    .atom (.mul (.n 10444) (.n 10443) (.n 10442)),
    .atom (.add (.n 10445) (.n 10438) (.n 10444)),
    .atom (.load (.n 10446) (.n 14) 5),
    .atom (.const (.n 10447) (word 0 0 0)),
    .atom (.mul (.n 10448) (.n 10446) (.n 10447)),
    .atom (.add (.n 10449) (.n 10445) (.n 10448)),
    .atom (.add (.n 10450) (.n 15) (.n 10449)),
    .atom (.mul (.n 10451) (.n 4758) (.n 10450)),
    .atom (.add (.n 10452) (.n 10421) (.n 10451))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9432, a9433, a9434, a9435, a9436, a9437, a9438, a9439, a9440, a9441, a9442, a9443, a9444, a9445,
    a9446, a9447, a9448, a9449, a9450, a9451, a9452, a9453, a9454, a9455, a9456, a9457, a9458,
    a9459, a9460, a9461, a9462, -⟩ := hs
  have e9432 := tb_loadHolds_unique a9432 (hw 0 (by norm_num))
  have e9436 := tb_loadHolds_unique a9436 (hw 1 (by norm_num))
  have e9439 := tb_loadHolds_unique a9439 (hw 2 (by norm_num))
  have e9446 := tb_loadHolds_unique a9446 (hw 3 (by norm_num))
  have e9453 := tb_loadHolds_unique a9453 (hw 4 (by norm_num))
  have e9456 := tb_loadHolds_unique a9456 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8198 : σ (.n 8198) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2.1
  have v8290 : σ (.n 8290) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2.1
  have v8369 : σ (.n 8369) = ev 16 := by
    rw [← hev 16 (by norm_num)]; exact (vt_evalF h (k := 83) (by norm_num)).2.2.1
  have v8393 : σ (.n 8393) = ev 17 := by
    rw [← hev 17 (by norm_num)]; exact (vt_evalF h (k := 84) (by norm_num)).2.2.1
  have v8404 : σ (.n 8404) = ev 18 := by
    rw [← hev 18 (by norm_num)]; exact (vt_evalF h (k := 85) (by norm_num)).2.2.1
  have v9077 : σ (.n 9077) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_evalF h (k := 132) (by norm_num)).2.2.1
  have hB : σ (.n 10450) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 4], 1)], [([65], 1)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)], [([], 0)]] := by
    simp only [v9077, v8404, v8393, v8369, v8290, v8198, v8165, a9460, a9459, a9458, a9457, e9456, a9455,
      a9454, e9453, a9452, a9451, a9450, a9449, a9448, a9447, e9446, a9445, a9444, a9443,
      a9442, a9441, a9440, e9439, a9438, a9437, e9436, a9435, a9434, a9433, e9432]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9462, a9461, hB]

set_option maxRecDepth 10000 in
theorem vtB15_5F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10483) = σ (.n 10452) + σ (.n 4765) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 5], 1)], [([66], 1)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9463 [
    .atom (.load (.n 10453) (.n 14) 0),
    .atom (.const (.n 10454) (word 2 0 0)),
    .atom (.mul (.n 10455) (.n 10453) (.n 10454)),
    .atom (.mul (.n 10456) (.n 8165) (.n 8222)),
    .atom (.load (.n 10457) (.n 14) 1),
    .atom (.mul (.n 10458) (.n 10457) (.n 10456)),
    .atom (.add (.n 10459) (.n 10455) (.n 10458)),
    .atom (.load (.n 10460) (.n 14) 2),
    .atom (.mul (.n 10461) (.n 10460) (.n 9088)),
    .atom (.add (.n 10462) (.n 10459) (.n 10461)),
    .atom (.mul (.n 10463) (.n 8290) (.n 8415)),
    .atom (.add (.n 10464) (.n 8415) (.n 10463)),
    .atom (.mul (.n 10465) (.n 8290) (.n 8404)),
    .atom (.add (.n 10466) (.n 10464) (.n 10465)),
    .atom (.load (.n 10467) (.n 14) 3),
    .atom (.mul (.n 10468) (.n 10467) (.n 10466)),
    .atom (.add (.n 10469) (.n 10462) (.n 10468)),
    .atom (.mul (.n 10470) (.n 8290) (.n 8426)),
    .atom (.add (.n 10471) (.n 8426) (.n 10470)),
    .atom (.mul (.n 10472) (.n 8290) (.n 8415)),
    .atom (.add (.n 10473) (.n 10471) (.n 10472)),
    .atom (.load (.n 10474) (.n 14) 4),
    .atom (.mul (.n 10475) (.n 10474) (.n 10473)),
    .atom (.add (.n 10476) (.n 10469) (.n 10475)),
    .atom (.load (.n 10477) (.n 14) 5),
    .atom (.const (.n 10478) (word 0 0 0)),
    .atom (.mul (.n 10479) (.n 10477) (.n 10478)),
    .atom (.add (.n 10480) (.n 10476) (.n 10479)),
    .atom (.add (.n 10481) (.n 15) (.n 10480)),
    .atom (.mul (.n 10482) (.n 4765) (.n 10481)),
    .atom (.add (.n 10483) (.n 10452) (.n 10482))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9463, a9464, a9465, a9466, a9467, a9468, a9469, a9470, a9471, a9472, a9473, a9474, a9475, a9476,
    a9477, a9478, a9479, a9480, a9481, a9482, a9483, a9484, a9485, a9486, a9487, a9488, a9489,
    a9490, a9491, a9492, a9493, -⟩ := hs
  have e9463 := tb_loadHolds_unique a9463 (hw 0 (by norm_num))
  have e9467 := tb_loadHolds_unique a9467 (hw 1 (by norm_num))
  have e9470 := tb_loadHolds_unique a9470 (hw 2 (by norm_num))
  have e9477 := tb_loadHolds_unique a9477 (hw 3 (by norm_num))
  have e9484 := tb_loadHolds_unique a9484 (hw 4 (by norm_num))
  have e9487 := tb_loadHolds_unique a9487 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8222 : σ (.n 8222) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2.1
  have v8290 : σ (.n 8290) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2.1
  have v8404 : σ (.n 8404) = ev 18 := by
    rw [← hev 18 (by norm_num)]; exact (vt_evalF h (k := 85) (by norm_num)).2.2.1
  have v8415 : σ (.n 8415) = ev 19 := by
    rw [← hev 19 (by norm_num)]; exact (vt_evalF h (k := 86) (by norm_num)).2.2.1
  have v8426 : σ (.n 8426) = ev 20 := by
    rw [← hev 20 (by norm_num)]; exact (vt_evalF h (k := 87) (by norm_num)).2.2.1
  have v9088 : σ (.n 9088) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_evalF h (k := 133) (by norm_num)).2.2.1
  have hB : σ (.n 10481) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 5], 1)], [([66], 1)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)], [([], 0)]] := by
    simp only [v9088, v8426, v8415, v8404, v8290, v8222, v8165, a9491, a9490, a9489, a9488, e9487, a9486,
      a9485, e9484, a9483, a9482, a9481, a9480, a9479, a9478, e9477, a9476, a9475, a9474,
      a9473, a9472, a9471, e9470, a9469, a9468, e9467, a9466, a9465, a9464, e9463]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9493, a9492, hB]

set_option maxRecDepth 10000 in
theorem vtB15_6F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10514) = σ (.n 10483) + σ (.n 4772) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 6], 1)], [([67], 1)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9494 [
    .atom (.load (.n 10484) (.n 14) 0),
    .atom (.const (.n 10485) (word 2 0 0)),
    .atom (.mul (.n 10486) (.n 10484) (.n 10485)),
    .atom (.mul (.n 10487) (.n 8165) (.n 8233)),
    .atom (.load (.n 10488) (.n 14) 1),
    .atom (.mul (.n 10489) (.n 10488) (.n 10487)),
    .atom (.add (.n 10490) (.n 10486) (.n 10489)),
    .atom (.load (.n 10491) (.n 14) 2),
    .atom (.mul (.n 10492) (.n 10491) (.n 9099)),
    .atom (.add (.n 10493) (.n 10490) (.n 10492)),
    .atom (.mul (.n 10494) (.n 8290) (.n 8450)),
    .atom (.add (.n 10495) (.n 8450) (.n 10494)),
    .atom (.mul (.n 10496) (.n 8290) (.n 8426)),
    .atom (.add (.n 10497) (.n 10495) (.n 10496)),
    .atom (.load (.n 10498) (.n 14) 3),
    .atom (.mul (.n 10499) (.n 10498) (.n 10497)),
    .atom (.add (.n 10500) (.n 10493) (.n 10499)),
    .atom (.mul (.n 10501) (.n 8290) (.n 8461)),
    .atom (.add (.n 10502) (.n 8461) (.n 10501)),
    .atom (.mul (.n 10503) (.n 8290) (.n 8450)),
    .atom (.add (.n 10504) (.n 10502) (.n 10503)),
    .atom (.load (.n 10505) (.n 14) 4),
    .atom (.mul (.n 10506) (.n 10505) (.n 10504)),
    .atom (.add (.n 10507) (.n 10500) (.n 10506)),
    .atom (.load (.n 10508) (.n 14) 5),
    .atom (.const (.n 10509) (word 0 0 0)),
    .atom (.mul (.n 10510) (.n 10508) (.n 10509)),
    .atom (.add (.n 10511) (.n 10507) (.n 10510)),
    .atom (.add (.n 10512) (.n 15) (.n 10511)),
    .atom (.mul (.n 10513) (.n 4772) (.n 10512)),
    .atom (.add (.n 10514) (.n 10483) (.n 10513))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9494, a9495, a9496, a9497, a9498, a9499, a9500, a9501, a9502, a9503, a9504, a9505, a9506, a9507,
    a9508, a9509, a9510, a9511, a9512, a9513, a9514, a9515, a9516, a9517, a9518, a9519, a9520,
    a9521, a9522, a9523, a9524, -⟩ := hs
  have e9494 := tb_loadHolds_unique a9494 (hw 0 (by norm_num))
  have e9498 := tb_loadHolds_unique a9498 (hw 1 (by norm_num))
  have e9501 := tb_loadHolds_unique a9501 (hw 2 (by norm_num))
  have e9508 := tb_loadHolds_unique a9508 (hw 3 (by norm_num))
  have e9515 := tb_loadHolds_unique a9515 (hw 4 (by norm_num))
  have e9518 := tb_loadHolds_unique a9518 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8233 : σ (.n 8233) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2.1
  have v8290 : σ (.n 8290) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2.1
  have v8426 : σ (.n 8426) = ev 20 := by
    rw [← hev 20 (by norm_num)]; exact (vt_evalF h (k := 87) (by norm_num)).2.2.1
  have v8450 : σ (.n 8450) = ev 21 := by
    rw [← hev 21 (by norm_num)]; exact (vt_evalF h (k := 88) (by norm_num)).2.2.1
  have v8461 : σ (.n 8461) = ev 22 := by
    rw [← hev 22 (by norm_num)]; exact (vt_evalF h (k := 89) (by norm_num)).2.2.1
  have v9099 : σ (.n 9099) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_evalF h (k := 134) (by norm_num)).2.2.1
  have hB : σ (.n 10512) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 6], 1)], [([67], 1)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)], [([], 0)]] := by
    simp only [v9099, v8461, v8450, v8426, v8290, v8233, v8165, a9522, a9521, a9520, a9519, e9518, a9517,
      a9516, e9515, a9514, a9513, a9512, a9511, a9510, a9509, e9508, a9507, a9506, a9505,
      a9504, a9503, a9502, e9501, a9500, a9499, e9498, a9497, a9496, a9495, e9494]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9524, a9523, hB]

set_option maxRecDepth 10000 in
theorem vtB15_7F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10547) = σ (.n 10514) + σ (.n 4779) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 6], 2)], [([68], 1)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9525 [
    .atom (.load (.n 10515) (.n 14) 0),
    .atom (.const (.n 10516) (word 2 0 0)),
    .atom (.mul (.n 10517) (.n 10515) (.n 10516)),
    .atom (.const (.n 10518) (word 2 0 0)),
    .atom (.mul (.n 10519) (.n 8165) (.n 8233)),
    .atom (.mul (.n 10520) (.n 10518) (.n 10519)),
    .atom (.load (.n 10521) (.n 14) 1),
    .atom (.mul (.n 10522) (.n 10521) (.n 10520)),
    .atom (.add (.n 10523) (.n 10517) (.n 10522)),
    .atom (.load (.n 10524) (.n 14) 2),
    .atom (.mul (.n 10525) (.n 10524) (.n 9110)),
    .atom (.add (.n 10526) (.n 10523) (.n 10525)),
    .atom (.mul (.n 10527) (.n 8290) (.n 8472)),
    .atom (.add (.n 10528) (.n 8472) (.n 10527)),
    .atom (.mul (.n 10529) (.n 8290) (.n 8461)),
    .atom (.add (.n 10530) (.n 10528) (.n 10529)),
    .atom (.load (.n 10531) (.n 14) 3),
    .atom (.mul (.n 10532) (.n 10531) (.n 10530)),
    .atom (.add (.n 10533) (.n 10526) (.n 10532)),
    .atom (.mul (.n 10534) (.n 8290) (.n 8483)),
    .atom (.add (.n 10535) (.n 8483) (.n 10534)),
    .atom (.mul (.n 10536) (.n 8290) (.n 8472)),
    .atom (.add (.n 10537) (.n 10535) (.n 10536)),
    .atom (.load (.n 10538) (.n 14) 4),
    .atom (.mul (.n 10539) (.n 10538) (.n 10537)),
    .atom (.add (.n 10540) (.n 10533) (.n 10539)),
    .atom (.load (.n 10541) (.n 14) 5),
    .atom (.const (.n 10542) (word 0 0 0)),
    .atom (.mul (.n 10543) (.n 10541) (.n 10542)),
    .atom (.add (.n 10544) (.n 10540) (.n 10543)),
    .atom (.add (.n 10545) (.n 15) (.n 10544)),
    .atom (.mul (.n 10546) (.n 4779) (.n 10545)),
    .atom (.add (.n 10547) (.n 10514) (.n 10546))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9525, a9526, a9527, a9528, a9529, a9530, a9531, a9532, a9533, a9534, a9535, a9536, a9537, a9538,
    a9539, a9540, a9541, a9542, a9543, a9544, a9545, a9546, a9547, a9548, a9549, a9550, a9551,
    a9552, a9553, a9554, a9555, a9556, a9557, -⟩ := hs
  have e9525 := tb_loadHolds_unique a9525 (hw 0 (by norm_num))
  have e9531 := tb_loadHolds_unique a9531 (hw 1 (by norm_num))
  have e9534 := tb_loadHolds_unique a9534 (hw 2 (by norm_num))
  have e9541 := tb_loadHolds_unique a9541 (hw 3 (by norm_num))
  have e9548 := tb_loadHolds_unique a9548 (hw 4 (by norm_num))
  have e9551 := tb_loadHolds_unique a9551 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8233 : σ (.n 8233) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2.1
  have v8290 : σ (.n 8290) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2.1
  have v8461 : σ (.n 8461) = ev 22 := by
    rw [← hev 22 (by norm_num)]; exact (vt_evalF h (k := 89) (by norm_num)).2.2.1
  have v8472 : σ (.n 8472) = ev 23 := by
    rw [← hev 23 (by norm_num)]; exact (vt_evalF h (k := 90) (by norm_num)).2.2.1
  have v8483 : σ (.n 8483) = ev 24 := by
    rw [← hev 24 (by norm_num)]; exact (vt_evalF h (k := 91) (by norm_num)).2.2.1
  have v9110 : σ (.n 9110) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_evalF h (k := 135) (by norm_num)).2.2.1
  have hB : σ (.n 10545) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 6], 2)], [([68], 1)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)], [([], 0)]] := by
    simp only [v9110, v8483, v8472, v8461, v8290, v8233, v8165, a9555, a9554, a9553, a9552, e9551, a9550,
      a9549, e9548, a9547, a9546, a9545, a9544, a9543, a9542, e9541, a9540, a9539, a9538,
      a9537, a9536, a9535, e9534, a9533, a9532, e9531, a9530, a9529, a9528, a9527, a9526,
      e9525]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9557, a9556, hB]

set_option maxRecDepth 10000 in
theorem vtB15_8F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10580) = σ (.n 10547) + σ (.n 4786) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 6], 4)], [([69], 1)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9558 [
    .atom (.load (.n 10548) (.n 14) 0),
    .atom (.const (.n 10549) (word 2 0 0)),
    .atom (.mul (.n 10550) (.n 10548) (.n 10549)),
    .atom (.const (.n 10551) (word 4 0 0)),
    .atom (.mul (.n 10552) (.n 8165) (.n 8233)),
    .atom (.mul (.n 10553) (.n 10551) (.n 10552)),
    .atom (.load (.n 10554) (.n 14) 1),
    .atom (.mul (.n 10555) (.n 10554) (.n 10553)),
    .atom (.add (.n 10556) (.n 10550) (.n 10555)),
    .atom (.load (.n 10557) (.n 14) 2),
    .atom (.mul (.n 10558) (.n 10557) (.n 9134)),
    .atom (.add (.n 10559) (.n 10556) (.n 10558)),
    .atom (.mul (.n 10560) (.n 8290) (.n 8507)),
    .atom (.add (.n 10561) (.n 8507) (.n 10560)),
    .atom (.mul (.n 10562) (.n 8290) (.n 8483)),
    .atom (.add (.n 10563) (.n 10561) (.n 10562)),
    .atom (.load (.n 10564) (.n 14) 3),
    .atom (.mul (.n 10565) (.n 10564) (.n 10563)),
    .atom (.add (.n 10566) (.n 10559) (.n 10565)),
    .atom (.mul (.n 10567) (.n 8290) (.n 8518)),
    .atom (.add (.n 10568) (.n 8518) (.n 10567)),
    .atom (.mul (.n 10569) (.n 8290) (.n 8507)),
    .atom (.add (.n 10570) (.n 10568) (.n 10569)),
    .atom (.load (.n 10571) (.n 14) 4),
    .atom (.mul (.n 10572) (.n 10571) (.n 10570)),
    .atom (.add (.n 10573) (.n 10566) (.n 10572)),
    .atom (.load (.n 10574) (.n 14) 5),
    .atom (.const (.n 10575) (word 0 0 0)),
    .atom (.mul (.n 10576) (.n 10574) (.n 10575)),
    .atom (.add (.n 10577) (.n 10573) (.n 10576)),
    .atom (.add (.n 10578) (.n 15) (.n 10577)),
    .atom (.mul (.n 10579) (.n 4786) (.n 10578)),
    .atom (.add (.n 10580) (.n 10547) (.n 10579))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9558, a9559, a9560, a9561, a9562, a9563, a9564, a9565, a9566, a9567, a9568, a9569, a9570, a9571,
    a9572, a9573, a9574, a9575, a9576, a9577, a9578, a9579, a9580, a9581, a9582, a9583, a9584,
    a9585, a9586, a9587, a9588, a9589, a9590, -⟩ := hs
  have e9558 := tb_loadHolds_unique a9558 (hw 0 (by norm_num))
  have e9564 := tb_loadHolds_unique a9564 (hw 1 (by norm_num))
  have e9567 := tb_loadHolds_unique a9567 (hw 2 (by norm_num))
  have e9574 := tb_loadHolds_unique a9574 (hw 3 (by norm_num))
  have e9581 := tb_loadHolds_unique a9581 (hw 4 (by norm_num))
  have e9584 := tb_loadHolds_unique a9584 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8233 : σ (.n 8233) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2.1
  have v8290 : σ (.n 8290) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2.1
  have v8483 : σ (.n 8483) = ev 24 := by
    rw [← hev 24 (by norm_num)]; exact (vt_evalF h (k := 91) (by norm_num)).2.2.1
  have v8507 : σ (.n 8507) = ev 25 := by
    rw [← hev 25 (by norm_num)]; exact (vt_evalF h (k := 92) (by norm_num)).2.2.1
  have v8518 : σ (.n 8518) = ev 26 := by
    rw [← hev 26 (by norm_num)]; exact (vt_evalF h (k := 93) (by norm_num)).2.2.1
  have v9134 : σ (.n 9134) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_evalF h (k := 136) (by norm_num)).2.2.1
  have hB : σ (.n 10578) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 6], 4)], [([69], 1)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)], [([], 0)]] := by
    simp only [v9134, v8518, v8507, v8483, v8290, v8233, v8165, a9588, a9587, a9586, a9585, e9584, a9583,
      a9582, e9581, a9580, a9579, a9578, a9577, a9576, a9575, e9574, a9573, a9572, a9571,
      a9570, a9569, a9568, e9567, a9566, a9565, e9564, a9563, a9562, a9561, a9560, a9559,
      e9558]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9590, a9589, hB]

set_option maxRecDepth 10000 in
theorem vtB15_9F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10613) = σ (.n 10580) + σ (.n 4793) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 6], 8)], [([70], 1)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9591 [
    .atom (.load (.n 10581) (.n 14) 0),
    .atom (.const (.n 10582) (word 2 0 0)),
    .atom (.mul (.n 10583) (.n 10581) (.n 10582)),
    .atom (.const (.n 10584) (word 8 0 0)),
    .atom (.mul (.n 10585) (.n 8165) (.n 8233)),
    .atom (.mul (.n 10586) (.n 10584) (.n 10585)),
    .atom (.load (.n 10587) (.n 14) 1),
    .atom (.mul (.n 10588) (.n 10587) (.n 10586)),
    .atom (.add (.n 10589) (.n 10583) (.n 10588)),
    .atom (.load (.n 10590) (.n 14) 2),
    .atom (.mul (.n 10591) (.n 10590) (.n 9145)),
    .atom (.add (.n 10592) (.n 10589) (.n 10591)),
    .atom (.mul (.n 10593) (.n 8290) (.n 8529)),
    .atom (.add (.n 10594) (.n 8529) (.n 10593)),
    .atom (.mul (.n 10595) (.n 8290) (.n 8518)),
    .atom (.add (.n 10596) (.n 10594) (.n 10595)),
    .atom (.load (.n 10597) (.n 14) 3),
    .atom (.mul (.n 10598) (.n 10597) (.n 10596)),
    .atom (.add (.n 10599) (.n 10592) (.n 10598)),
    .atom (.mul (.n 10600) (.n 8290) (.n 8540)),
    .atom (.add (.n 10601) (.n 8540) (.n 10600)),
    .atom (.mul (.n 10602) (.n 8290) (.n 8529)),
    .atom (.add (.n 10603) (.n 10601) (.n 10602)),
    .atom (.load (.n 10604) (.n 14) 4),
    .atom (.mul (.n 10605) (.n 10604) (.n 10603)),
    .atom (.add (.n 10606) (.n 10599) (.n 10605)),
    .atom (.load (.n 10607) (.n 14) 5),
    .atom (.const (.n 10608) (word 0 0 0)),
    .atom (.mul (.n 10609) (.n 10607) (.n 10608)),
    .atom (.add (.n 10610) (.n 10606) (.n 10609)),
    .atom (.add (.n 10611) (.n 15) (.n 10610)),
    .atom (.mul (.n 10612) (.n 4793) (.n 10611)),
    .atom (.add (.n 10613) (.n 10580) (.n 10612))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9591, a9592, a9593, a9594, a9595, a9596, a9597, a9598, a9599, a9600, a9601, a9602, a9603, a9604,
    a9605, a9606, a9607, a9608, a9609, a9610, a9611, a9612, a9613, a9614, a9615, a9616, a9617,
    a9618, a9619, a9620, a9621, a9622, a9623, -⟩ := hs
  have e9591 := tb_loadHolds_unique a9591 (hw 0 (by norm_num))
  have e9597 := tb_loadHolds_unique a9597 (hw 1 (by norm_num))
  have e9600 := tb_loadHolds_unique a9600 (hw 2 (by norm_num))
  have e9607 := tb_loadHolds_unique a9607 (hw 3 (by norm_num))
  have e9614 := tb_loadHolds_unique a9614 (hw 4 (by norm_num))
  have e9617 := tb_loadHolds_unique a9617 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8233 : σ (.n 8233) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2.1
  have v8290 : σ (.n 8290) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2.1
  have v8518 : σ (.n 8518) = ev 26 := by
    rw [← hev 26 (by norm_num)]; exact (vt_evalF h (k := 93) (by norm_num)).2.2.1
  have v8529 : σ (.n 8529) = ev 27 := by
    rw [← hev 27 (by norm_num)]; exact (vt_evalF h (k := 94) (by norm_num)).2.2.1
  have v8540 : σ (.n 8540) = ev 28 := by
    rw [← hev 28 (by norm_num)]; exact (vt_evalF h (k := 95) (by norm_num)).2.2.1
  have v9145 : σ (.n 9145) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_evalF h (k := 137) (by norm_num)).2.2.1
  have hB : σ (.n 10611) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 6], 8)], [([70], 1)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)], [([], 0)]] := by
    simp only [v9145, v8540, v8529, v8518, v8290, v8233, v8165, a9621, a9620, a9619, a9618, e9617, a9616,
      a9615, e9614, a9613, a9612, a9611, a9610, a9609, a9608, e9607, a9606, a9605, a9604,
      a9603, a9602, a9601, e9600, a9599, a9598, e9597, a9596, a9595, a9594, a9593, a9592,
      e9591]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9623, a9622, hB]

set_option maxRecDepth 10000 in
theorem vtB15_10F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10644) = σ (.n 10613) + σ (.n 4800) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 7], 1)], [([71], 1)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([12], 1), ([10, 12], 1), ([10, 29], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9624 [
    .atom (.load (.n 10614) (.n 14) 0),
    .atom (.const (.n 10615) (word 2 0 0)),
    .atom (.mul (.n 10616) (.n 10614) (.n 10615)),
    .atom (.mul (.n 10617) (.n 8165) (.n 8244)),
    .atom (.load (.n 10618) (.n 14) 1),
    .atom (.mul (.n 10619) (.n 10618) (.n 10617)),
    .atom (.add (.n 10620) (.n 10616) (.n 10619)),
    .atom (.load (.n 10621) (.n 14) 2),
    .atom (.mul (.n 10622) (.n 10621) (.n 9156)),
    .atom (.add (.n 10623) (.n 10620) (.n 10622)),
    .atom (.mul (.n 10624) (.n 8290) (.n 8564)),
    .atom (.add (.n 10625) (.n 8564) (.n 10624)),
    .atom (.mul (.n 10626) (.n 8290) (.n 8540)),
    .atom (.add (.n 10627) (.n 10625) (.n 10626)),
    .atom (.load (.n 10628) (.n 14) 3),
    .atom (.mul (.n 10629) (.n 10628) (.n 10627)),
    .atom (.add (.n 10630) (.n 10623) (.n 10629)),
    .atom (.mul (.n 10631) (.n 8290) (.n 8312)),
    .atom (.add (.n 10632) (.n 8312) (.n 10631)),
    .atom (.mul (.n 10633) (.n 8290) (.n 8564)),
    .atom (.add (.n 10634) (.n 10632) (.n 10633)),
    .atom (.load (.n 10635) (.n 14) 4),
    .atom (.mul (.n 10636) (.n 10635) (.n 10634)),
    .atom (.add (.n 10637) (.n 10630) (.n 10636)),
    .atom (.load (.n 10638) (.n 14) 5),
    .atom (.const (.n 10639) (word 0 0 0)),
    .atom (.mul (.n 10640) (.n 10638) (.n 10639)),
    .atom (.add (.n 10641) (.n 10637) (.n 10640)),
    .atom (.add (.n 10642) (.n 15) (.n 10641)),
    .atom (.mul (.n 10643) (.n 4800) (.n 10642)),
    .atom (.add (.n 10644) (.n 10613) (.n 10643))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9624, a9625, a9626, a9627, a9628, a9629, a9630, a9631, a9632, a9633, a9634, a9635, a9636, a9637,
    a9638, a9639, a9640, a9641, a9642, a9643, a9644, a9645, a9646, a9647, a9648, a9649, a9650,
    a9651, a9652, a9653, a9654, -⟩ := hs
  have e9624 := tb_loadHolds_unique a9624 (hw 0 (by norm_num))
  have e9628 := tb_loadHolds_unique a9628 (hw 1 (by norm_num))
  have e9631 := tb_loadHolds_unique a9631 (hw 2 (by norm_num))
  have e9638 := tb_loadHolds_unique a9638 (hw 3 (by norm_num))
  have e9645 := tb_loadHolds_unique a9645 (hw 4 (by norm_num))
  have e9648 := tb_loadHolds_unique a9648 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8244 : σ (.n 8244) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2.1
  have v8290 : σ (.n 8290) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2.1
  have v8312 : σ (.n 8312) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 79) (by norm_num)).2.2.1
  have v8540 : σ (.n 8540) = ev 28 := by
    rw [← hev 28 (by norm_num)]; exact (vt_evalF h (k := 95) (by norm_num)).2.2.1
  have v8564 : σ (.n 8564) = ev 29 := by
    rw [← hev 29 (by norm_num)]; exact (vt_evalF h (k := 96) (by norm_num)).2.2.1
  have v9156 : σ (.n 9156) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_evalF h (k := 138) (by norm_num)).2.2.1
  have hB : σ (.n 10642) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 7], 1)], [([71], 1)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([12], 1), ([10, 12], 1), ([10, 29], 1)], [([], 0)]] := by
    simp only [v9156, v8564, v8540, v8312, v8290, v8244, v8165, a9652, a9651, a9650, a9649, e9648, a9647,
      a9646, e9645, a9644, a9643, a9642, a9641, a9640, a9639, e9638, a9637, a9636, a9635,
      a9634, a9633, a9632, e9631, a9630, a9629, e9628, a9627, a9626, a9625, e9624]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9654, a9653, hB]

set_option maxRecDepth 10000 in
theorem vtB15_11F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10667) = σ (.n 10644) + σ (.n 4807) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 8], 1)], [([72], 1)], [([30], 1)], [([31], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9655 [
    .atom (.load (.n 10645) (.n 14) 0),
    .atom (.const (.n 10646) (word 2 0 0)),
    .atom (.mul (.n 10647) (.n 10645) (.n 10646)),
    .atom (.mul (.n 10648) (.n 8165) (.n 8255)),
    .atom (.load (.n 10649) (.n 14) 1),
    .atom (.mul (.n 10650) (.n 10649) (.n 10648)),
    .atom (.add (.n 10651) (.n 10647) (.n 10650)),
    .atom (.load (.n 10652) (.n 14) 2),
    .atom (.mul (.n 10653) (.n 10652) (.n 9167)),
    .atom (.add (.n 10654) (.n 10651) (.n 10653)),
    .atom (.load (.n 10655) (.n 14) 3),
    .atom (.mul (.n 10656) (.n 10655) (.n 8575)),
    .atom (.add (.n 10657) (.n 10654) (.n 10656)),
    .atom (.load (.n 10658) (.n 14) 4),
    .atom (.mul (.n 10659) (.n 10658) (.n 8586)),
    .atom (.add (.n 10660) (.n 10657) (.n 10659)),
    .atom (.load (.n 10661) (.n 14) 5),
    .atom (.const (.n 10662) (word 0 0 0)),
    .atom (.mul (.n 10663) (.n 10661) (.n 10662)),
    .atom (.add (.n 10664) (.n 10660) (.n 10663)),
    .atom (.add (.n 10665) (.n 15) (.n 10664)),
    .atom (.mul (.n 10666) (.n 4807) (.n 10665)),
    .atom (.add (.n 10667) (.n 10644) (.n 10666))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9655, a9656, a9657, a9658, a9659, a9660, a9661, a9662, a9663, a9664, a9665, a9666, a9667, a9668,
    a9669, a9670, a9671, a9672, a9673, a9674, a9675, a9676, a9677, -⟩ := hs
  have e9655 := tb_loadHolds_unique a9655 (hw 0 (by norm_num))
  have e9659 := tb_loadHolds_unique a9659 (hw 1 (by norm_num))
  have e9662 := tb_loadHolds_unique a9662 (hw 2 (by norm_num))
  have e9665 := tb_loadHolds_unique a9665 (hw 3 (by norm_num))
  have e9668 := tb_loadHolds_unique a9668 (hw 4 (by norm_num))
  have e9671 := tb_loadHolds_unique a9671 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8255 : σ (.n 8255) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 75) (by norm_num)).2.2.1
  have v8575 : σ (.n 8575) = ev 30 := by
    rw [← hev 30 (by norm_num)]; exact (vt_evalF h (k := 97) (by norm_num)).2.2.1
  have v8586 : σ (.n 8586) = ev 31 := by
    rw [← hev 31 (by norm_num)]; exact (vt_evalF h (k := 98) (by norm_num)).2.2.1
  have v9167 : σ (.n 9167) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_evalF h (k := 139) (by norm_num)).2.2.1
  have hB : σ (.n 10665) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 8], 1)], [([72], 1)], [([30], 1)], [([31], 1)], [([], 0)]] := by
    simp only [v9167, v8586, v8575, v8255, v8165, a9675, a9674, a9673, a9672, e9671, a9670, a9669, e9668,
      a9667, a9666, e9665, a9664, a9663, e9662, a9661, a9660, e9659, a9658, a9657, a9656,
      e9655]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9677, a9676, hB]

set_option maxRecDepth 10000 in
theorem vtB15_12F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10692) = σ (.n 10667) + σ (.n 4814) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 8], 2)], [([73], 1)], [([32], 1)], [([33], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9678 [
    .atom (.load (.n 10668) (.n 14) 0),
    .atom (.const (.n 10669) (word 2 0 0)),
    .atom (.mul (.n 10670) (.n 10668) (.n 10669)),
    .atom (.const (.n 10671) (word 2 0 0)),
    .atom (.mul (.n 10672) (.n 8165) (.n 8255)),
    .atom (.mul (.n 10673) (.n 10671) (.n 10672)),
    .atom (.load (.n 10674) (.n 14) 1),
    .atom (.mul (.n 10675) (.n 10674) (.n 10673)),
    .atom (.add (.n 10676) (.n 10670) (.n 10675)),
    .atom (.load (.n 10677) (.n 14) 2),
    .atom (.mul (.n 10678) (.n 10677) (.n 9191)),
    .atom (.add (.n 10679) (.n 10676) (.n 10678)),
    .atom (.load (.n 10680) (.n 14) 3),
    .atom (.mul (.n 10681) (.n 10680) (.n 8597)),
    .atom (.add (.n 10682) (.n 10679) (.n 10681)),
    .atom (.load (.n 10683) (.n 14) 4),
    .atom (.mul (.n 10684) (.n 10683) (.n 8621)),
    .atom (.add (.n 10685) (.n 10682) (.n 10684)),
    .atom (.load (.n 10686) (.n 14) 5),
    .atom (.const (.n 10687) (word 0 0 0)),
    .atom (.mul (.n 10688) (.n 10686) (.n 10687)),
    .atom (.add (.n 10689) (.n 10685) (.n 10688)),
    .atom (.add (.n 10690) (.n 15) (.n 10689)),
    .atom (.mul (.n 10691) (.n 4814) (.n 10690)),
    .atom (.add (.n 10692) (.n 10667) (.n 10691))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9678, a9679, a9680, a9681, a9682, a9683, a9684, a9685, a9686, a9687, a9688, a9689, a9690, a9691,
    a9692, a9693, a9694, a9695, a9696, a9697, a9698, a9699, a9700, a9701, a9702, -⟩ := hs
  have e9678 := tb_loadHolds_unique a9678 (hw 0 (by norm_num))
  have e9684 := tb_loadHolds_unique a9684 (hw 1 (by norm_num))
  have e9687 := tb_loadHolds_unique a9687 (hw 2 (by norm_num))
  have e9690 := tb_loadHolds_unique a9690 (hw 3 (by norm_num))
  have e9693 := tb_loadHolds_unique a9693 (hw 4 (by norm_num))
  have e9696 := tb_loadHolds_unique a9696 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8255 : σ (.n 8255) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 75) (by norm_num)).2.2.1
  have v8597 : σ (.n 8597) = ev 32 := by
    rw [← hev 32 (by norm_num)]; exact (vt_evalF h (k := 99) (by norm_num)).2.2.1
  have v8621 : σ (.n 8621) = ev 33 := by
    rw [← hev 33 (by norm_num)]; exact (vt_evalF h (k := 100) (by norm_num)).2.2.1
  have v9191 : σ (.n 9191) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_evalF h (k := 140) (by norm_num)).2.2.1
  have hB : σ (.n 10690) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 8], 2)], [([73], 1)], [([32], 1)], [([33], 1)], [([], 0)]] := by
    simp only [v9191, v8621, v8597, v8255, v8165, a9700, a9699, a9698, a9697, e9696, a9695, a9694, e9693,
      a9692, a9691, e9690, a9689, a9688, e9687, a9686, a9685, e9684, a9683, a9682, a9681,
      a9680, a9679, e9678]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9702, a9701, hB]

set_option maxRecDepth 10000 in
theorem vtB15_13F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10717) = σ (.n 10692) + σ (.n 4821) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 8], 4)], [([74], 1)], [([34], 1)], [([35], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9703 [
    .atom (.load (.n 10693) (.n 14) 0),
    .atom (.const (.n 10694) (word 2 0 0)),
    .atom (.mul (.n 10695) (.n 10693) (.n 10694)),
    .atom (.const (.n 10696) (word 4 0 0)),
    .atom (.mul (.n 10697) (.n 8165) (.n 8255)),
    .atom (.mul (.n 10698) (.n 10696) (.n 10697)),
    .atom (.load (.n 10699) (.n 14) 1),
    .atom (.mul (.n 10700) (.n 10699) (.n 10698)),
    .atom (.add (.n 10701) (.n 10695) (.n 10700)),
    .atom (.load (.n 10702) (.n 14) 2),
    .atom (.mul (.n 10703) (.n 10702) (.n 9202)),
    .atom (.add (.n 10704) (.n 10701) (.n 10703)),
    .atom (.load (.n 10705) (.n 14) 3),
    .atom (.mul (.n 10706) (.n 10705) (.n 8632)),
    .atom (.add (.n 10707) (.n 10704) (.n 10706)),
    .atom (.load (.n 10708) (.n 14) 4),
    .atom (.mul (.n 10709) (.n 10708) (.n 8643)),
    .atom (.add (.n 10710) (.n 10707) (.n 10709)),
    .atom (.load (.n 10711) (.n 14) 5),
    .atom (.const (.n 10712) (word 0 0 0)),
    .atom (.mul (.n 10713) (.n 10711) (.n 10712)),
    .atom (.add (.n 10714) (.n 10710) (.n 10713)),
    .atom (.add (.n 10715) (.n 15) (.n 10714)),
    .atom (.mul (.n 10716) (.n 4821) (.n 10715)),
    .atom (.add (.n 10717) (.n 10692) (.n 10716))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9703, a9704, a9705, a9706, a9707, a9708, a9709, a9710, a9711, a9712, a9713, a9714, a9715, a9716,
    a9717, a9718, a9719, a9720, a9721, a9722, a9723, a9724, a9725, a9726, a9727, -⟩ := hs
  have e9703 := tb_loadHolds_unique a9703 (hw 0 (by norm_num))
  have e9709 := tb_loadHolds_unique a9709 (hw 1 (by norm_num))
  have e9712 := tb_loadHolds_unique a9712 (hw 2 (by norm_num))
  have e9715 := tb_loadHolds_unique a9715 (hw 3 (by norm_num))
  have e9718 := tb_loadHolds_unique a9718 (hw 4 (by norm_num))
  have e9721 := tb_loadHolds_unique a9721 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8255 : σ (.n 8255) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 75) (by norm_num)).2.2.1
  have v8632 : σ (.n 8632) = ev 34 := by
    rw [← hev 34 (by norm_num)]; exact (vt_evalF h (k := 101) (by norm_num)).2.2.1
  have v8643 : σ (.n 8643) = ev 35 := by
    rw [← hev 35 (by norm_num)]; exact (vt_evalF h (k := 102) (by norm_num)).2.2.1
  have v9202 : σ (.n 9202) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_evalF h (k := 141) (by norm_num)).2.2.1
  have hB : σ (.n 10715) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 8], 4)], [([74], 1)], [([34], 1)], [([35], 1)], [([], 0)]] := by
    simp only [v9202, v8643, v8632, v8255, v8165, a9725, a9724, a9723, a9722, e9721, a9720, a9719, e9718,
      a9717, a9716, e9715, a9714, a9713, e9712, a9711, a9710, e9709, a9708, a9707, a9706,
      a9705, a9704, e9703]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9727, a9726, hB]

set_option maxRecDepth 10000 in
theorem vtB15_14F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10742) = σ (.n 10717) + σ (.n 4828) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 8], 8)], [([75], 1)], [([36], 1)], [([37], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9728 [
    .atom (.load (.n 10718) (.n 14) 0),
    .atom (.const (.n 10719) (word 2 0 0)),
    .atom (.mul (.n 10720) (.n 10718) (.n 10719)),
    .atom (.const (.n 10721) (word 8 0 0)),
    .atom (.mul (.n 10722) (.n 8165) (.n 8255)),
    .atom (.mul (.n 10723) (.n 10721) (.n 10722)),
    .atom (.load (.n 10724) (.n 14) 1),
    .atom (.mul (.n 10725) (.n 10724) (.n 10723)),
    .atom (.add (.n 10726) (.n 10720) (.n 10725)),
    .atom (.load (.n 10727) (.n 14) 2),
    .atom (.mul (.n 10728) (.n 10727) (.n 9213)),
    .atom (.add (.n 10729) (.n 10726) (.n 10728)),
    .atom (.load (.n 10730) (.n 14) 3),
    .atom (.mul (.n 10731) (.n 10730) (.n 8654)),
    .atom (.add (.n 10732) (.n 10729) (.n 10731)),
    .atom (.load (.n 10733) (.n 14) 4),
    .atom (.mul (.n 10734) (.n 10733) (.n 8678)),
    .atom (.add (.n 10735) (.n 10732) (.n 10734)),
    .atom (.load (.n 10736) (.n 14) 5),
    .atom (.const (.n 10737) (word 0 0 0)),
    .atom (.mul (.n 10738) (.n 10736) (.n 10737)),
    .atom (.add (.n 10739) (.n 10735) (.n 10738)),
    .atom (.add (.n 10740) (.n 15) (.n 10739)),
    .atom (.mul (.n 10741) (.n 4828) (.n 10740)),
    .atom (.add (.n 10742) (.n 10717) (.n 10741))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9728, a9729, a9730, a9731, a9732, a9733, a9734, a9735, a9736, a9737, a9738, a9739, a9740, a9741,
    a9742, a9743, a9744, a9745, a9746, a9747, a9748, a9749, a9750, a9751, a9752, -⟩ := hs
  have e9728 := tb_loadHolds_unique a9728 (hw 0 (by norm_num))
  have e9734 := tb_loadHolds_unique a9734 (hw 1 (by norm_num))
  have e9737 := tb_loadHolds_unique a9737 (hw 2 (by norm_num))
  have e9740 := tb_loadHolds_unique a9740 (hw 3 (by norm_num))
  have e9743 := tb_loadHolds_unique a9743 (hw 4 (by norm_num))
  have e9746 := tb_loadHolds_unique a9746 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8255 : σ (.n 8255) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 75) (by norm_num)).2.2.1
  have v8654 : σ (.n 8654) = ev 36 := by
    rw [← hev 36 (by norm_num)]; exact (vt_evalF h (k := 103) (by norm_num)).2.2.1
  have v8678 : σ (.n 8678) = ev 37 := by
    rw [← hev 37 (by norm_num)]; exact (vt_evalF h (k := 104) (by norm_num)).2.2.1
  have v9213 : σ (.n 9213) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_evalF h (k := 142) (by norm_num)).2.2.1
  have hB : σ (.n 10740) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 8], 8)], [([75], 1)], [([36], 1)], [([37], 1)], [([], 0)]] := by
    simp only [v9213, v8678, v8654, v8255, v8165, a9750, a9749, a9748, a9747, e9746, a9745, a9744, e9743,
      a9742, a9741, e9740, a9739, a9738, e9737, a9736, a9735, e9734, a9733, a9732, a9731,
      a9730, a9729, e9728]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9752, a9751, hB]

set_option maxRecDepth 10000 in
theorem vtB15_15F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10771) = σ (.n 10742) + σ (.n 4835) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 1)], [([76], 1)], [([38], 1), ([11, 38], 1)], [([39], 1), ([11, 39], 1), ([11, 38], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9753 [
    .atom (.load (.n 10743) (.n 14) 0),
    .atom (.const (.n 10744) (word 2 0 0)),
    .atom (.mul (.n 10745) (.n 10743) (.n 10744)),
    .atom (.mul (.n 10746) (.n 8165) (.n 8279)),
    .atom (.load (.n 10747) (.n 14) 1),
    .atom (.mul (.n 10748) (.n 10747) (.n 10746)),
    .atom (.add (.n 10749) (.n 10745) (.n 10748)),
    .atom (.load (.n 10750) (.n 14) 2),
    .atom (.mul (.n 10751) (.n 10750) (.n 9224)),
    .atom (.add (.n 10752) (.n 10749) (.n 10751)),
    .atom (.mul (.n 10753) (.n 8301) (.n 8689)),
    .atom (.add (.n 10754) (.n 8689) (.n 10753)),
    .atom (.load (.n 10755) (.n 14) 3),
    .atom (.mul (.n 10756) (.n 10755) (.n 10754)),
    .atom (.add (.n 10757) (.n 10752) (.n 10756)),
    .atom (.mul (.n 10758) (.n 8301) (.n 8700)),
    .atom (.add (.n 10759) (.n 8700) (.n 10758)),
    .atom (.mul (.n 10760) (.n 8301) (.n 8689)),
    .atom (.add (.n 10761) (.n 10759) (.n 10760)),
    .atom (.load (.n 10762) (.n 14) 4),
    .atom (.mul (.n 10763) (.n 10762) (.n 10761)),
    .atom (.add (.n 10764) (.n 10757) (.n 10763)),
    .atom (.load (.n 10765) (.n 14) 5),
    .atom (.const (.n 10766) (word 0 0 0)),
    .atom (.mul (.n 10767) (.n 10765) (.n 10766)),
    .atom (.add (.n 10768) (.n 10764) (.n 10767)),
    .atom (.add (.n 10769) (.n 15) (.n 10768)),
    .atom (.mul (.n 10770) (.n 4835) (.n 10769)),
    .atom (.add (.n 10771) (.n 10742) (.n 10770))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9753, a9754, a9755, a9756, a9757, a9758, a9759, a9760, a9761, a9762, a9763, a9764, a9765, a9766,
    a9767, a9768, a9769, a9770, a9771, a9772, a9773, a9774, a9775, a9776, a9777, a9778, a9779,
    a9780, a9781, -⟩ := hs
  have e9753 := tb_loadHolds_unique a9753 (hw 0 (by norm_num))
  have e9757 := tb_loadHolds_unique a9757 (hw 1 (by norm_num))
  have e9760 := tb_loadHolds_unique a9760 (hw 2 (by norm_num))
  have e9765 := tb_loadHolds_unique a9765 (hw 3 (by norm_num))
  have e9772 := tb_loadHolds_unique a9772 (hw 4 (by norm_num))
  have e9775 := tb_loadHolds_unique a9775 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8301 : σ (.n 8301) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2.1
  have v8689 : σ (.n 8689) = ev 38 := by
    rw [← hev 38 (by norm_num)]; exact (vt_evalF h (k := 105) (by norm_num)).2.2.1
  have v8700 : σ (.n 8700) = ev 39 := by
    rw [← hev 39 (by norm_num)]; exact (vt_evalF h (k := 106) (by norm_num)).2.2.1
  have v9224 : σ (.n 9224) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_evalF h (k := 143) (by norm_num)).2.2.1
  have hB : σ (.n 10769) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 1)], [([76], 1)], [([38], 1), ([11, 38], 1)], [([39], 1), ([11, 39], 1), ([11, 38], 1)], [([], 0)]] := by
    simp only [v9224, v8700, v8689, v8301, v8279, v8165, a9779, a9778, a9777, a9776, e9775, a9774, a9773,
      e9772, a9771, a9770, a9769, a9768, a9767, a9766, e9765, a9764, a9763, a9762, a9761,
      e9760, a9759, a9758, e9757, a9756, a9755, a9754, e9753]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9781, a9780, hB]

set_option maxRecDepth 10000 in
theorem vtB15_16F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10804) = σ (.n 10771) + σ (.n 4842) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 2)], [([77], 1)], [([40], 1), ([11, 40], 1), ([11, 39], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9782 [
    .atom (.load (.n 10772) (.n 14) 0),
    .atom (.const (.n 10773) (word 2 0 0)),
    .atom (.mul (.n 10774) (.n 10772) (.n 10773)),
    .atom (.const (.n 10775) (word 2 0 0)),
    .atom (.mul (.n 10776) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10777) (.n 10775) (.n 10776)),
    .atom (.load (.n 10778) (.n 14) 1),
    .atom (.mul (.n 10779) (.n 10778) (.n 10777)),
    .atom (.add (.n 10780) (.n 10774) (.n 10779)),
    .atom (.load (.n 10781) (.n 14) 2),
    .atom (.mul (.n 10782) (.n 10781) (.n 9248)),
    .atom (.add (.n 10783) (.n 10780) (.n 10782)),
    .atom (.mul (.n 10784) (.n 8301) (.n 8711)),
    .atom (.add (.n 10785) (.n 8711) (.n 10784)),
    .atom (.mul (.n 10786) (.n 8301) (.n 8700)),
    .atom (.add (.n 10787) (.n 10785) (.n 10786)),
    .atom (.load (.n 10788) (.n 14) 3),
    .atom (.mul (.n 10789) (.n 10788) (.n 10787)),
    .atom (.add (.n 10790) (.n 10783) (.n 10789)),
    .atom (.mul (.n 10791) (.n 8301) (.n 8735)),
    .atom (.add (.n 10792) (.n 8735) (.n 10791)),
    .atom (.mul (.n 10793) (.n 8301) (.n 8711)),
    .atom (.add (.n 10794) (.n 10792) (.n 10793)),
    .atom (.load (.n 10795) (.n 14) 4),
    .atom (.mul (.n 10796) (.n 10795) (.n 10794)),
    .atom (.add (.n 10797) (.n 10790) (.n 10796)),
    .atom (.load (.n 10798) (.n 14) 5),
    .atom (.const (.n 10799) (word 0 0 0)),
    .atom (.mul (.n 10800) (.n 10798) (.n 10799)),
    .atom (.add (.n 10801) (.n 10797) (.n 10800)),
    .atom (.add (.n 10802) (.n 15) (.n 10801)),
    .atom (.mul (.n 10803) (.n 4842) (.n 10802)),
    .atom (.add (.n 10804) (.n 10771) (.n 10803))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9782, a9783, a9784, a9785, a9786, a9787, a9788, a9789, a9790, a9791, a9792, a9793, a9794, a9795,
    a9796, a9797, a9798, a9799, a9800, a9801, a9802, a9803, a9804, a9805, a9806, a9807, a9808,
    a9809, a9810, a9811, a9812, a9813, a9814, -⟩ := hs
  have e9782 := tb_loadHolds_unique a9782 (hw 0 (by norm_num))
  have e9788 := tb_loadHolds_unique a9788 (hw 1 (by norm_num))
  have e9791 := tb_loadHolds_unique a9791 (hw 2 (by norm_num))
  have e9798 := tb_loadHolds_unique a9798 (hw 3 (by norm_num))
  have e9805 := tb_loadHolds_unique a9805 (hw 4 (by norm_num))
  have e9808 := tb_loadHolds_unique a9808 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8301 : σ (.n 8301) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2.1
  have v8700 : σ (.n 8700) = ev 39 := by
    rw [← hev 39 (by norm_num)]; exact (vt_evalF h (k := 106) (by norm_num)).2.2.1
  have v8711 : σ (.n 8711) = ev 40 := by
    rw [← hev 40 (by norm_num)]; exact (vt_evalF h (k := 107) (by norm_num)).2.2.1
  have v8735 : σ (.n 8735) = ev 41 := by
    rw [← hev 41 (by norm_num)]; exact (vt_evalF h (k := 108) (by norm_num)).2.2.1
  have v9248 : σ (.n 9248) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_evalF h (k := 144) (by norm_num)).2.2.1
  have hB : σ (.n 10802) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 2)], [([77], 1)], [([40], 1), ([11, 40], 1), ([11, 39], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)], [([], 0)]] := by
    simp only [v9248, v8735, v8711, v8700, v8301, v8279, v8165, a9812, a9811, a9810, a9809, e9808, a9807,
      a9806, e9805, a9804, a9803, a9802, a9801, a9800, a9799, e9798, a9797, a9796, a9795,
      a9794, a9793, a9792, e9791, a9790, a9789, e9788, a9787, a9786, a9785, a9784, a9783,
      e9782]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9814, a9813, hB]

set_option maxRecDepth 10000 in
theorem vtB15_17F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10837) = σ (.n 10804) + σ (.n 4849) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 4)], [([78], 1)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9815 [
    .atom (.load (.n 10805) (.n 14) 0),
    .atom (.const (.n 10806) (word 2 0 0)),
    .atom (.mul (.n 10807) (.n 10805) (.n 10806)),
    .atom (.const (.n 10808) (word 4 0 0)),
    .atom (.mul (.n 10809) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10810) (.n 10808) (.n 10809)),
    .atom (.load (.n 10811) (.n 14) 1),
    .atom (.mul (.n 10812) (.n 10811) (.n 10810)),
    .atom (.add (.n 10813) (.n 10807) (.n 10812)),
    .atom (.load (.n 10814) (.n 14) 2),
    .atom (.mul (.n 10815) (.n 10814) (.n 9259)),
    .atom (.add (.n 10816) (.n 10813) (.n 10815)),
    .atom (.mul (.n 10817) (.n 8301) (.n 8746)),
    .atom (.add (.n 10818) (.n 8746) (.n 10817)),
    .atom (.mul (.n 10819) (.n 8301) (.n 8735)),
    .atom (.add (.n 10820) (.n 10818) (.n 10819)),
    .atom (.load (.n 10821) (.n 14) 3),
    .atom (.mul (.n 10822) (.n 10821) (.n 10820)),
    .atom (.add (.n 10823) (.n 10816) (.n 10822)),
    .atom (.mul (.n 10824) (.n 8301) (.n 8757)),
    .atom (.add (.n 10825) (.n 8757) (.n 10824)),
    .atom (.mul (.n 10826) (.n 8301) (.n 8746)),
    .atom (.add (.n 10827) (.n 10825) (.n 10826)),
    .atom (.load (.n 10828) (.n 14) 4),
    .atom (.mul (.n 10829) (.n 10828) (.n 10827)),
    .atom (.add (.n 10830) (.n 10823) (.n 10829)),
    .atom (.load (.n 10831) (.n 14) 5),
    .atom (.const (.n 10832) (word 0 0 0)),
    .atom (.mul (.n 10833) (.n 10831) (.n 10832)),
    .atom (.add (.n 10834) (.n 10830) (.n 10833)),
    .atom (.add (.n 10835) (.n 15) (.n 10834)),
    .atom (.mul (.n 10836) (.n 4849) (.n 10835)),
    .atom (.add (.n 10837) (.n 10804) (.n 10836))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9815, a9816, a9817, a9818, a9819, a9820, a9821, a9822, a9823, a9824, a9825, a9826, a9827, a9828,
    a9829, a9830, a9831, a9832, a9833, a9834, a9835, a9836, a9837, a9838, a9839, a9840, a9841,
    a9842, a9843, a9844, a9845, a9846, a9847, -⟩ := hs
  have e9815 := tb_loadHolds_unique a9815 (hw 0 (by norm_num))
  have e9821 := tb_loadHolds_unique a9821 (hw 1 (by norm_num))
  have e9824 := tb_loadHolds_unique a9824 (hw 2 (by norm_num))
  have e9831 := tb_loadHolds_unique a9831 (hw 3 (by norm_num))
  have e9838 := tb_loadHolds_unique a9838 (hw 4 (by norm_num))
  have e9841 := tb_loadHolds_unique a9841 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8301 : σ (.n 8301) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2.1
  have v8735 : σ (.n 8735) = ev 41 := by
    rw [← hev 41 (by norm_num)]; exact (vt_evalF h (k := 108) (by norm_num)).2.2.1
  have v8746 : σ (.n 8746) = ev 42 := by
    rw [← hev 42 (by norm_num)]; exact (vt_evalF h (k := 109) (by norm_num)).2.2.1
  have v8757 : σ (.n 8757) = ev 43 := by
    rw [← hev 43 (by norm_num)]; exact (vt_evalF h (k := 110) (by norm_num)).2.2.1
  have v9259 : σ (.n 9259) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_evalF h (k := 145) (by norm_num)).2.2.1
  have hB : σ (.n 10835) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 4)], [([78], 1)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)], [([], 0)]] := by
    simp only [v9259, v8757, v8746, v8735, v8301, v8279, v8165, a9845, a9844, a9843, a9842, e9841, a9840,
      a9839, e9838, a9837, a9836, a9835, a9834, a9833, a9832, e9831, a9830, a9829, a9828,
      a9827, a9826, a9825, e9824, a9823, a9822, e9821, a9820, a9819, a9818, a9817, a9816,
      e9815]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9847, a9846, hB]

set_option maxRecDepth 10000 in
theorem vtB15_18F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10870) = σ (.n 10837) + σ (.n 4856) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 8)], [([79], 1)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9848 [
    .atom (.load (.n 10838) (.n 14) 0),
    .atom (.const (.n 10839) (word 2 0 0)),
    .atom (.mul (.n 10840) (.n 10838) (.n 10839)),
    .atom (.const (.n 10841) (word 8 0 0)),
    .atom (.mul (.n 10842) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10843) (.n 10841) (.n 10842)),
    .atom (.load (.n 10844) (.n 14) 1),
    .atom (.mul (.n 10845) (.n 10844) (.n 10843)),
    .atom (.add (.n 10846) (.n 10840) (.n 10845)),
    .atom (.load (.n 10847) (.n 14) 2),
    .atom (.mul (.n 10848) (.n 10847) (.n 9270)),
    .atom (.add (.n 10849) (.n 10846) (.n 10848)),
    .atom (.mul (.n 10850) (.n 8301) (.n 8768)),
    .atom (.add (.n 10851) (.n 8768) (.n 10850)),
    .atom (.mul (.n 10852) (.n 8301) (.n 8757)),
    .atom (.add (.n 10853) (.n 10851) (.n 10852)),
    .atom (.load (.n 10854) (.n 14) 3),
    .atom (.mul (.n 10855) (.n 10854) (.n 10853)),
    .atom (.add (.n 10856) (.n 10849) (.n 10855)),
    .atom (.mul (.n 10857) (.n 8301) (.n 8792)),
    .atom (.add (.n 10858) (.n 8792) (.n 10857)),
    .atom (.mul (.n 10859) (.n 8301) (.n 8768)),
    .atom (.add (.n 10860) (.n 10858) (.n 10859)),
    .atom (.load (.n 10861) (.n 14) 4),
    .atom (.mul (.n 10862) (.n 10861) (.n 10860)),
    .atom (.add (.n 10863) (.n 10856) (.n 10862)),
    .atom (.load (.n 10864) (.n 14) 5),
    .atom (.const (.n 10865) (word 0 0 0)),
    .atom (.mul (.n 10866) (.n 10864) (.n 10865)),
    .atom (.add (.n 10867) (.n 10863) (.n 10866)),
    .atom (.add (.n 10868) (.n 15) (.n 10867)),
    .atom (.mul (.n 10869) (.n 4856) (.n 10868)),
    .atom (.add (.n 10870) (.n 10837) (.n 10869))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9848, a9849, a9850, a9851, a9852, a9853, a9854, a9855, a9856, a9857, a9858, a9859, a9860, a9861,
    a9862, a9863, a9864, a9865, a9866, a9867, a9868, a9869, a9870, a9871, a9872, a9873, a9874,
    a9875, a9876, a9877, a9878, a9879, a9880, -⟩ := hs
  have e9848 := tb_loadHolds_unique a9848 (hw 0 (by norm_num))
  have e9854 := tb_loadHolds_unique a9854 (hw 1 (by norm_num))
  have e9857 := tb_loadHolds_unique a9857 (hw 2 (by norm_num))
  have e9864 := tb_loadHolds_unique a9864 (hw 3 (by norm_num))
  have e9871 := tb_loadHolds_unique a9871 (hw 4 (by norm_num))
  have e9874 := tb_loadHolds_unique a9874 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8301 : σ (.n 8301) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2.1
  have v8757 : σ (.n 8757) = ev 43 := by
    rw [← hev 43 (by norm_num)]; exact (vt_evalF h (k := 110) (by norm_num)).2.2.1
  have v8768 : σ (.n 8768) = ev 44 := by
    rw [← hev 44 (by norm_num)]; exact (vt_evalF h (k := 111) (by norm_num)).2.2.1
  have v8792 : σ (.n 8792) = ev 45 := by
    rw [← hev 45 (by norm_num)]; exact (vt_evalF h (k := 112) (by norm_num)).2.2.1
  have v9270 : σ (.n 9270) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_evalF h (k := 146) (by norm_num)).2.2.1
  have hB : σ (.n 10868) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 8)], [([79], 1)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)], [([], 0)]] := by
    simp only [v9270, v8792, v8768, v8757, v8301, v8279, v8165, a9878, a9877, a9876, a9875, e9874, a9873,
      a9872, e9871, a9870, a9869, a9868, a9867, a9866, a9865, e9864, a9863, a9862, a9861,
      a9860, a9859, a9858, e9857, a9856, a9855, e9854, a9853, a9852, a9851, a9850, a9849,
      e9848]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9880, a9879, hB]

set_option maxRecDepth 10000 in
theorem vtB15_19F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10903) = σ (.n 10870) + σ (.n 4863) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 16)], [([80], 1)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9881 [
    .atom (.load (.n 10871) (.n 14) 0),
    .atom (.const (.n 10872) (word 2 0 0)),
    .atom (.mul (.n 10873) (.n 10871) (.n 10872)),
    .atom (.const (.n 10874) (word 16 0 0)),
    .atom (.mul (.n 10875) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10876) (.n 10874) (.n 10875)),
    .atom (.load (.n 10877) (.n 14) 1),
    .atom (.mul (.n 10878) (.n 10877) (.n 10876)),
    .atom (.add (.n 10879) (.n 10873) (.n 10878)),
    .atom (.load (.n 10880) (.n 14) 2),
    .atom (.mul (.n 10881) (.n 10880) (.n 9281)),
    .atom (.add (.n 10882) (.n 10879) (.n 10881)),
    .atom (.mul (.n 10883) (.n 8301) (.n 8803)),
    .atom (.add (.n 10884) (.n 8803) (.n 10883)),
    .atom (.mul (.n 10885) (.n 8301) (.n 8792)),
    .atom (.add (.n 10886) (.n 10884) (.n 10885)),
    .atom (.load (.n 10887) (.n 14) 3),
    .atom (.mul (.n 10888) (.n 10887) (.n 10886)),
    .atom (.add (.n 10889) (.n 10882) (.n 10888)),
    .atom (.mul (.n 10890) (.n 8301) (.n 8814)),
    .atom (.add (.n 10891) (.n 8814) (.n 10890)),
    .atom (.mul (.n 10892) (.n 8301) (.n 8803)),
    .atom (.add (.n 10893) (.n 10891) (.n 10892)),
    .atom (.load (.n 10894) (.n 14) 4),
    .atom (.mul (.n 10895) (.n 10894) (.n 10893)),
    .atom (.add (.n 10896) (.n 10889) (.n 10895)),
    .atom (.load (.n 10897) (.n 14) 5),
    .atom (.const (.n 10898) (word 0 0 0)),
    .atom (.mul (.n 10899) (.n 10897) (.n 10898)),
    .atom (.add (.n 10900) (.n 10896) (.n 10899)),
    .atom (.add (.n 10901) (.n 15) (.n 10900)),
    .atom (.mul (.n 10902) (.n 4863) (.n 10901)),
    .atom (.add (.n 10903) (.n 10870) (.n 10902))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9881, a9882, a9883, a9884, a9885, a9886, a9887, a9888, a9889, a9890, a9891, a9892, a9893, a9894,
    a9895, a9896, a9897, a9898, a9899, a9900, a9901, a9902, a9903, a9904, a9905, a9906, a9907,
    a9908, a9909, a9910, a9911, a9912, a9913, -⟩ := hs
  have e9881 := tb_loadHolds_unique a9881 (hw 0 (by norm_num))
  have e9887 := tb_loadHolds_unique a9887 (hw 1 (by norm_num))
  have e9890 := tb_loadHolds_unique a9890 (hw 2 (by norm_num))
  have e9897 := tb_loadHolds_unique a9897 (hw 3 (by norm_num))
  have e9904 := tb_loadHolds_unique a9904 (hw 4 (by norm_num))
  have e9907 := tb_loadHolds_unique a9907 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8301 : σ (.n 8301) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2.1
  have v8792 : σ (.n 8792) = ev 45 := by
    rw [← hev 45 (by norm_num)]; exact (vt_evalF h (k := 112) (by norm_num)).2.2.1
  have v8803 : σ (.n 8803) = ev 46 := by
    rw [← hev 46 (by norm_num)]; exact (vt_evalF h (k := 113) (by norm_num)).2.2.1
  have v8814 : σ (.n 8814) = ev 47 := by
    rw [← hev 47 (by norm_num)]; exact (vt_evalF h (k := 114) (by norm_num)).2.2.1
  have v9281 : σ (.n 9281) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_evalF h (k := 147) (by norm_num)).2.2.1
  have hB : σ (.n 10901) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 16)], [([80], 1)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)], [([], 0)]] := by
    simp only [v9281, v8814, v8803, v8792, v8301, v8279, v8165, a9911, a9910, a9909, a9908, e9907, a9906,
      a9905, e9904, a9903, a9902, a9901, a9900, a9899, a9898, e9897, a9896, a9895, a9894,
      a9893, a9892, a9891, e9890, a9889, a9888, e9887, a9886, a9885, a9884, a9883, a9882,
      e9881]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9913, a9912, hB]

set_option maxRecDepth 10000 in
theorem vtB15_20F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10936) = σ (.n 10903) + σ (.n 4870) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 32)], [([81], 1)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9914 [
    .atom (.load (.n 10904) (.n 14) 0),
    .atom (.const (.n 10905) (word 2 0 0)),
    .atom (.mul (.n 10906) (.n 10904) (.n 10905)),
    .atom (.const (.n 10907) (word 32 0 0)),
    .atom (.mul (.n 10908) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10909) (.n 10907) (.n 10908)),
    .atom (.load (.n 10910) (.n 14) 1),
    .atom (.mul (.n 10911) (.n 10910) (.n 10909)),
    .atom (.add (.n 10912) (.n 10906) (.n 10911)),
    .atom (.load (.n 10913) (.n 14) 2),
    .atom (.mul (.n 10914) (.n 10913) (.n 9305)),
    .atom (.add (.n 10915) (.n 10912) (.n 10914)),
    .atom (.mul (.n 10916) (.n 8301) (.n 8825)),
    .atom (.add (.n 10917) (.n 8825) (.n 10916)),
    .atom (.mul (.n 10918) (.n 8301) (.n 8814)),
    .atom (.add (.n 10919) (.n 10917) (.n 10918)),
    .atom (.load (.n 10920) (.n 14) 3),
    .atom (.mul (.n 10921) (.n 10920) (.n 10919)),
    .atom (.add (.n 10922) (.n 10915) (.n 10921)),
    .atom (.mul (.n 10923) (.n 8301) (.n 8849)),
    .atom (.add (.n 10924) (.n 8849) (.n 10923)),
    .atom (.mul (.n 10925) (.n 8301) (.n 8825)),
    .atom (.add (.n 10926) (.n 10924) (.n 10925)),
    .atom (.load (.n 10927) (.n 14) 4),
    .atom (.mul (.n 10928) (.n 10927) (.n 10926)),
    .atom (.add (.n 10929) (.n 10922) (.n 10928)),
    .atom (.load (.n 10930) (.n 14) 5),
    .atom (.const (.n 10931) (word 0 0 0)),
    .atom (.mul (.n 10932) (.n 10930) (.n 10931)),
    .atom (.add (.n 10933) (.n 10929) (.n 10932)),
    .atom (.add (.n 10934) (.n 15) (.n 10933)),
    .atom (.mul (.n 10935) (.n 4870) (.n 10934)),
    .atom (.add (.n 10936) (.n 10903) (.n 10935))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9914, a9915, a9916, a9917, a9918, a9919, a9920, a9921, a9922, a9923, a9924, a9925, a9926, a9927,
    a9928, a9929, a9930, a9931, a9932, a9933, a9934, a9935, a9936, a9937, a9938, a9939, a9940,
    a9941, a9942, a9943, a9944, a9945, a9946, -⟩ := hs
  have e9914 := tb_loadHolds_unique a9914 (hw 0 (by norm_num))
  have e9920 := tb_loadHolds_unique a9920 (hw 1 (by norm_num))
  have e9923 := tb_loadHolds_unique a9923 (hw 2 (by norm_num))
  have e9930 := tb_loadHolds_unique a9930 (hw 3 (by norm_num))
  have e9937 := tb_loadHolds_unique a9937 (hw 4 (by norm_num))
  have e9940 := tb_loadHolds_unique a9940 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8301 : σ (.n 8301) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2.1
  have v8814 : σ (.n 8814) = ev 47 := by
    rw [← hev 47 (by norm_num)]; exact (vt_evalF h (k := 114) (by norm_num)).2.2.1
  have v8825 : σ (.n 8825) = ev 48 := by
    rw [← hev 48 (by norm_num)]; exact (vt_evalF h (k := 115) (by norm_num)).2.2.1
  have v8849 : σ (.n 8849) = ev 49 := by
    rw [← hev 49 (by norm_num)]; exact (vt_evalF h (k := 116) (by norm_num)).2.2.1
  have v9305 : σ (.n 9305) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_evalF h (k := 148) (by norm_num)).2.2.1
  have hB : σ (.n 10934) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 32)], [([81], 1)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)], [([], 0)]] := by
    simp only [v9305, v8849, v8825, v8814, v8301, v8279, v8165, a9944, a9943, a9942, a9941, e9940, a9939,
      a9938, e9937, a9936, a9935, a9934, a9933, a9932, a9931, e9930, a9929, a9928, a9927,
      a9926, a9925, a9924, e9923, a9922, a9921, e9920, a9919, a9918, a9917, a9916, a9915,
      e9914]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9946, a9945, hB]

set_option maxRecDepth 10000 in
theorem vtB15_21F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10969) = σ (.n 10936) + σ (.n 4877) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 64)], [([82], 1)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9947 [
    .atom (.load (.n 10937) (.n 14) 0),
    .atom (.const (.n 10938) (word 2 0 0)),
    .atom (.mul (.n 10939) (.n 10937) (.n 10938)),
    .atom (.const (.n 10940) (word 64 0 0)),
    .atom (.mul (.n 10941) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10942) (.n 10940) (.n 10941)),
    .atom (.load (.n 10943) (.n 14) 1),
    .atom (.mul (.n 10944) (.n 10943) (.n 10942)),
    .atom (.add (.n 10945) (.n 10939) (.n 10944)),
    .atom (.load (.n 10946) (.n 14) 2),
    .atom (.mul (.n 10947) (.n 10946) (.n 9316)),
    .atom (.add (.n 10948) (.n 10945) (.n 10947)),
    .atom (.mul (.n 10949) (.n 8301) (.n 8860)),
    .atom (.add (.n 10950) (.n 8860) (.n 10949)),
    .atom (.mul (.n 10951) (.n 8301) (.n 8849)),
    .atom (.add (.n 10952) (.n 10950) (.n 10951)),
    .atom (.load (.n 10953) (.n 14) 3),
    .atom (.mul (.n 10954) (.n 10953) (.n 10952)),
    .atom (.add (.n 10955) (.n 10948) (.n 10954)),
    .atom (.mul (.n 10956) (.n 8301) (.n 8871)),
    .atom (.add (.n 10957) (.n 8871) (.n 10956)),
    .atom (.mul (.n 10958) (.n 8301) (.n 8860)),
    .atom (.add (.n 10959) (.n 10957) (.n 10958)),
    .atom (.load (.n 10960) (.n 14) 4),
    .atom (.mul (.n 10961) (.n 10960) (.n 10959)),
    .atom (.add (.n 10962) (.n 10955) (.n 10961)),
    .atom (.load (.n 10963) (.n 14) 5),
    .atom (.const (.n 10964) (word 0 0 0)),
    .atom (.mul (.n 10965) (.n 10963) (.n 10964)),
    .atom (.add (.n 10966) (.n 10962) (.n 10965)),
    .atom (.add (.n 10967) (.n 15) (.n 10966)),
    .atom (.mul (.n 10968) (.n 4877) (.n 10967)),
    .atom (.add (.n 10969) (.n 10936) (.n 10968))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9947, a9948, a9949, a9950, a9951, a9952, a9953, a9954, a9955, a9956, a9957, a9958, a9959, a9960,
    a9961, a9962, a9963, a9964, a9965, a9966, a9967, a9968, a9969, a9970, a9971, a9972, a9973,
    a9974, a9975, a9976, a9977, a9978, a9979, -⟩ := hs
  have e9947 := tb_loadHolds_unique a9947 (hw 0 (by norm_num))
  have e9953 := tb_loadHolds_unique a9953 (hw 1 (by norm_num))
  have e9956 := tb_loadHolds_unique a9956 (hw 2 (by norm_num))
  have e9963 := tb_loadHolds_unique a9963 (hw 3 (by norm_num))
  have e9970 := tb_loadHolds_unique a9970 (hw 4 (by norm_num))
  have e9973 := tb_loadHolds_unique a9973 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8301 : σ (.n 8301) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2.1
  have v8849 : σ (.n 8849) = ev 49 := by
    rw [← hev 49 (by norm_num)]; exact (vt_evalF h (k := 116) (by norm_num)).2.2.1
  have v8860 : σ (.n 8860) = ev 50 := by
    rw [← hev 50 (by norm_num)]; exact (vt_evalF h (k := 117) (by norm_num)).2.2.1
  have v8871 : σ (.n 8871) = ev 51 := by
    rw [← hev 51 (by norm_num)]; exact (vt_evalF h (k := 118) (by norm_num)).2.2.1
  have v9316 : σ (.n 9316) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_evalF h (k := 149) (by norm_num)).2.2.1
  have hB : σ (.n 10967) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 64)], [([82], 1)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)], [([], 0)]] := by
    simp only [v9316, v8871, v8860, v8849, v8301, v8279, v8165, a9977, a9976, a9975, a9974, e9973, a9972,
      a9971, e9970, a9969, a9968, a9967, a9966, a9965, a9964, e9963, a9962, a9961, a9960,
      a9959, a9958, a9957, e9956, a9955, a9954, e9953, a9952, a9951, a9950, a9949, a9948,
      e9947]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9979, a9978, hB]

set_option maxRecDepth 10000 in
theorem vtB15_22F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 11002) = σ (.n 10969) + σ (.n 4884) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 128)], [([83], 1)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9980 [
    .atom (.load (.n 10970) (.n 14) 0),
    .atom (.const (.n 10971) (word 2 0 0)),
    .atom (.mul (.n 10972) (.n 10970) (.n 10971)),
    .atom (.const (.n 10973) (word 128 0 0)),
    .atom (.mul (.n 10974) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10975) (.n 10973) (.n 10974)),
    .atom (.load (.n 10976) (.n 14) 1),
    .atom (.mul (.n 10977) (.n 10976) (.n 10975)),
    .atom (.add (.n 10978) (.n 10972) (.n 10977)),
    .atom (.load (.n 10979) (.n 14) 2),
    .atom (.mul (.n 10980) (.n 10979) (.n 9327)),
    .atom (.add (.n 10981) (.n 10978) (.n 10980)),
    .atom (.mul (.n 10982) (.n 8301) (.n 8882)),
    .atom (.add (.n 10983) (.n 8882) (.n 10982)),
    .atom (.mul (.n 10984) (.n 8301) (.n 8871)),
    .atom (.add (.n 10985) (.n 10983) (.n 10984)),
    .atom (.load (.n 10986) (.n 14) 3),
    .atom (.mul (.n 10987) (.n 10986) (.n 10985)),
    .atom (.add (.n 10988) (.n 10981) (.n 10987)),
    .atom (.mul (.n 10989) (.n 8301) (.n 8906)),
    .atom (.add (.n 10990) (.n 8906) (.n 10989)),
    .atom (.mul (.n 10991) (.n 8301) (.n 8882)),
    .atom (.add (.n 10992) (.n 10990) (.n 10991)),
    .atom (.load (.n 10993) (.n 14) 4),
    .atom (.mul (.n 10994) (.n 10993) (.n 10992)),
    .atom (.add (.n 10995) (.n 10988) (.n 10994)),
    .atom (.load (.n 10996) (.n 14) 5),
    .atom (.const (.n 10997) (word 0 0 0)),
    .atom (.mul (.n 10998) (.n 10996) (.n 10997)),
    .atom (.add (.n 10999) (.n 10995) (.n 10998)),
    .atom (.add (.n 11000) (.n 15) (.n 10999)),
    .atom (.mul (.n 11001) (.n 4884) (.n 11000)),
    .atom (.add (.n 11002) (.n 10969) (.n 11001))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9980, a9981, a9982, a9983, a9984, a9985, a9986, a9987, a9988, a9989, a9990, a9991, a9992, a9993,
    a9994, a9995, a9996, a9997, a9998, a9999, a10000, a10001, a10002, a10003, a10004, a10005,
    a10006, a10007, a10008, a10009, a10010, a10011, a10012, -⟩ := hs
  have e9980 := tb_loadHolds_unique a9980 (hw 0 (by norm_num))
  have e9986 := tb_loadHolds_unique a9986 (hw 1 (by norm_num))
  have e9989 := tb_loadHolds_unique a9989 (hw 2 (by norm_num))
  have e9996 := tb_loadHolds_unique a9996 (hw 3 (by norm_num))
  have e10003 := tb_loadHolds_unique a10003 (hw 4 (by norm_num))
  have e10006 := tb_loadHolds_unique a10006 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8301 : σ (.n 8301) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2.1
  have v8871 : σ (.n 8871) = ev 51 := by
    rw [← hev 51 (by norm_num)]; exact (vt_evalF h (k := 118) (by norm_num)).2.2.1
  have v8882 : σ (.n 8882) = ev 52 := by
    rw [← hev 52 (by norm_num)]; exact (vt_evalF h (k := 119) (by norm_num)).2.2.1
  have v8906 : σ (.n 8906) = ev 53 := by
    rw [← hev 53 (by norm_num)]; exact (vt_evalF h (k := 120) (by norm_num)).2.2.1
  have v9327 : σ (.n 9327) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_evalF h (k := 150) (by norm_num)).2.2.1
  have hB : σ (.n 11000) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 128)], [([83], 1)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)], [([], 0)]] := by
    simp only [v9327, v8906, v8882, v8871, v8301, v8279, v8165, a10010, a10009, a10008, a10007, e10006,
      a10005, a10004, e10003, a10002, a10001, a10000, a9999, a9998, a9997, e9996, a9995, a9994,
      a9993, a9992, a9991, a9990, e9989, a9988, a9987, e9986, a9985, a9984, a9983, a9982,
      a9981, e9980]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a10012, a10011, hB]

set_option maxRecDepth 10000 in
theorem vtB15_23F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 11032) = σ (.n 11002) + σ (.n 4891) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 256)], [([84], 1)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([11, 54], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 10013 [
    .atom (.load (.n 11003) (.n 14) 0),
    .atom (.const (.n 11004) (word 2 0 0)),
    .atom (.mul (.n 11005) (.n 11003) (.n 11004)),
    .atom (.const (.n 11006) (word 256 0 0)),
    .atom (.mul (.n 11007) (.n 8165) (.n 8279)),
    .atom (.mul (.n 11008) (.n 11006) (.n 11007)),
    .atom (.load (.n 11009) (.n 14) 1),
    .atom (.mul (.n 11010) (.n 11009) (.n 11008)),
    .atom (.add (.n 11011) (.n 11005) (.n 11010)),
    .atom (.load (.n 11012) (.n 14) 2),
    .atom (.mul (.n 11013) (.n 11012) (.n 9338)),
    .atom (.add (.n 11014) (.n 11011) (.n 11013)),
    .atom (.mul (.n 11015) (.n 8301) (.n 8917)),
    .atom (.add (.n 11016) (.n 8917) (.n 11015)),
    .atom (.mul (.n 11017) (.n 8301) (.n 8906)),
    .atom (.add (.n 11018) (.n 11016) (.n 11017)),
    .atom (.load (.n 11019) (.n 14) 3),
    .atom (.mul (.n 11020) (.n 11019) (.n 11018)),
    .atom (.add (.n 11021) (.n 11014) (.n 11020)),
    .atom (.mul (.n 11022) (.n 8301) (.n 8917)),
    .atom (.load (.n 11023) (.n 14) 4),
    .atom (.mul (.n 11024) (.n 11023) (.n 11022)),
    .atom (.add (.n 11025) (.n 11021) (.n 11024)),
    .atom (.load (.n 11026) (.n 14) 5),
    .atom (.const (.n 11027) (word 0 0 0)),
    .atom (.mul (.n 11028) (.n 11026) (.n 11027)),
    .atom (.add (.n 11029) (.n 11025) (.n 11028)),
    .atom (.add (.n 11030) (.n 15) (.n 11029)),
    .atom (.mul (.n 11031) (.n 4891) (.n 11030)),
    .atom (.add (.n 11032) (.n 11002) (.n 11031))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a10013, a10014, a10015, a10016, a10017, a10018, a10019, a10020, a10021, a10022, a10023, a10024,
    a10025, a10026, a10027, a10028, a10029, a10030, a10031, a10032, a10033, a10034, a10035,
    a10036, a10037, a10038, a10039, a10040, a10041, a10042, -⟩ := hs
  have e10013 := tb_loadHolds_unique a10013 (hw 0 (by norm_num))
  have e10019 := tb_loadHolds_unique a10019 (hw 1 (by norm_num))
  have e10022 := tb_loadHolds_unique a10022 (hw 2 (by norm_num))
  have e10029 := tb_loadHolds_unique a10029 (hw 3 (by norm_num))
  have e10033 := tb_loadHolds_unique a10033 (hw 4 (by norm_num))
  have e10036 := tb_loadHolds_unique a10036 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8301 : σ (.n 8301) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2.1
  have v8906 : σ (.n 8906) = ev 53 := by
    rw [← hev 53 (by norm_num)]; exact (vt_evalF h (k := 120) (by norm_num)).2.2.1
  have v8917 : σ (.n 8917) = ev 54 := by
    rw [← hev 54 (by norm_num)]; exact (vt_evalF h (k := 121) (by norm_num)).2.2.1
  have v9338 : σ (.n 9338) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_evalF h (k := 151) (by norm_num)).2.2.1
  have hB : σ (.n 11030) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 256)], [([84], 1)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([11, 54], 1)], [([], 0)]] := by
    simp only [v9338, v8917, v8906, v8301, v8279, v8165, a10040, a10039, a10038, a10037, e10036, a10035,
      a10034, e10033, a10032, a10031, a10030, e10029, a10028, a10027, a10026, a10025, a10024,
      a10023, e10022, a10021, a10020, e10019, a10018, a10017, a10016, a10015, a10014, e10013]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a10042, a10041, hB]

set_option maxRecDepth 10000 in
theorem vtB15_24F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 11057) = σ (.n 11032) + σ (.n 4898) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 512)], [([85], 1)], [([55], 1)], [([56], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 10043 [
    .atom (.load (.n 11033) (.n 14) 0),
    .atom (.const (.n 11034) (word 2 0 0)),
    .atom (.mul (.n 11035) (.n 11033) (.n 11034)),
    .atom (.const (.n 11036) (word 512 0 0)),
    .atom (.mul (.n 11037) (.n 8165) (.n 8279)),
    .atom (.mul (.n 11038) (.n 11036) (.n 11037)),
    .atom (.load (.n 11039) (.n 14) 1),
    .atom (.mul (.n 11040) (.n 11039) (.n 11038)),
    .atom (.add (.n 11041) (.n 11035) (.n 11040)),
    .atom (.load (.n 11042) (.n 14) 2),
    .atom (.mul (.n 11043) (.n 11042) (.n 9362)),
    .atom (.add (.n 11044) (.n 11041) (.n 11043)),
    .atom (.load (.n 11045) (.n 14) 3),
    .atom (.mul (.n 11046) (.n 11045) (.n 8928)),
    .atom (.add (.n 11047) (.n 11044) (.n 11046)),
    .atom (.load (.n 11048) (.n 14) 4),
    .atom (.mul (.n 11049) (.n 11048) (.n 8939)),
    .atom (.add (.n 11050) (.n 11047) (.n 11049)),
    .atom (.load (.n 11051) (.n 14) 5),
    .atom (.const (.n 11052) (word 0 0 0)),
    .atom (.mul (.n 11053) (.n 11051) (.n 11052)),
    .atom (.add (.n 11054) (.n 11050) (.n 11053)),
    .atom (.add (.n 11055) (.n 15) (.n 11054)),
    .atom (.mul (.n 11056) (.n 4898) (.n 11055)),
    .atom (.add (.n 11057) (.n 11032) (.n 11056))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a10043, a10044, a10045, a10046, a10047, a10048, a10049, a10050, a10051, a10052, a10053, a10054,
    a10055, a10056, a10057, a10058, a10059, a10060, a10061, a10062, a10063, a10064, a10065,
    a10066, a10067, -⟩ := hs
  have e10043 := tb_loadHolds_unique a10043 (hw 0 (by norm_num))
  have e10049 := tb_loadHolds_unique a10049 (hw 1 (by norm_num))
  have e10052 := tb_loadHolds_unique a10052 (hw 2 (by norm_num))
  have e10055 := tb_loadHolds_unique a10055 (hw 3 (by norm_num))
  have e10058 := tb_loadHolds_unique a10058 (hw 4 (by norm_num))
  have e10061 := tb_loadHolds_unique a10061 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8928 : σ (.n 8928) = ev 55 := by
    rw [← hev 55 (by norm_num)]; exact (vt_evalF h (k := 122) (by norm_num)).2.2.1
  have v8939 : σ (.n 8939) = ev 56 := by
    rw [← hev 56 (by norm_num)]; exact (vt_evalF h (k := 123) (by norm_num)).2.2.1
  have v9362 : σ (.n 9362) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_evalF h (k := 152) (by norm_num)).2.2.1
  have hB : σ (.n 11055) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 512)], [([85], 1)], [([55], 1)], [([56], 1)], [([], 0)]] := by
    simp only [v9362, v8939, v8928, v8279, v8165, a10065, a10064, a10063, a10062, e10061, a10060, a10059,
      e10058, a10057, a10056, e10055, a10054, a10053, e10052, a10051, a10050, e10049, a10048,
      a10047, a10046, a10045, a10044, e10043]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a10067, a10066, hB]

set_option maxRecDepth 10000 in
theorem vtB15_25F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 11082) = σ (.n 11057) + σ (.n 4905) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 1024)], [([86], 1)], [([57], 1)], [([58], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 10068 [
    .atom (.load (.n 11058) (.n 14) 0),
    .atom (.const (.n 11059) (word 2 0 0)),
    .atom (.mul (.n 11060) (.n 11058) (.n 11059)),
    .atom (.const (.n 11061) (word 1024 0 0)),
    .atom (.mul (.n 11062) (.n 8165) (.n 8279)),
    .atom (.mul (.n 11063) (.n 11061) (.n 11062)),
    .atom (.load (.n 11064) (.n 14) 1),
    .atom (.mul (.n 11065) (.n 11064) (.n 11063)),
    .atom (.add (.n 11066) (.n 11060) (.n 11065)),
    .atom (.load (.n 11067) (.n 14) 2),
    .atom (.mul (.n 11068) (.n 11067) (.n 9373)),
    .atom (.add (.n 11069) (.n 11066) (.n 11068)),
    .atom (.load (.n 11070) (.n 14) 3),
    .atom (.mul (.n 11071) (.n 11070) (.n 8963)),
    .atom (.add (.n 11072) (.n 11069) (.n 11071)),
    .atom (.load (.n 11073) (.n 14) 4),
    .atom (.mul (.n 11074) (.n 11073) (.n 8974)),
    .atom (.add (.n 11075) (.n 11072) (.n 11074)),
    .atom (.load (.n 11076) (.n 14) 5),
    .atom (.const (.n 11077) (word 0 0 0)),
    .atom (.mul (.n 11078) (.n 11076) (.n 11077)),
    .atom (.add (.n 11079) (.n 11075) (.n 11078)),
    .atom (.add (.n 11080) (.n 15) (.n 11079)),
    .atom (.mul (.n 11081) (.n 4905) (.n 11080)),
    .atom (.add (.n 11082) (.n 11057) (.n 11081))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a10068, a10069, a10070, a10071, a10072, a10073, a10074, a10075, a10076, a10077, a10078, a10079,
    a10080, a10081, a10082, a10083, a10084, a10085, a10086, a10087, a10088, a10089, a10090,
    a10091, a10092, -⟩ := hs
  have e10068 := tb_loadHolds_unique a10068 (hw 0 (by norm_num))
  have e10074 := tb_loadHolds_unique a10074 (hw 1 (by norm_num))
  have e10077 := tb_loadHolds_unique a10077 (hw 2 (by norm_num))
  have e10080 := tb_loadHolds_unique a10080 (hw 3 (by norm_num))
  have e10083 := tb_loadHolds_unique a10083 (hw 4 (by norm_num))
  have e10086 := tb_loadHolds_unique a10086 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8963 : σ (.n 8963) = ev 57 := by
    rw [← hev 57 (by norm_num)]; exact (vt_evalF h (k := 124) (by norm_num)).2.2.1
  have v8974 : σ (.n 8974) = ev 58 := by
    rw [← hev 58 (by norm_num)]; exact (vt_evalF h (k := 125) (by norm_num)).2.2.1
  have v9373 : σ (.n 9373) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_evalF h (k := 153) (by norm_num)).2.2.1
  have hB : σ (.n 11080) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 1024)], [([86], 1)], [([57], 1)], [([58], 1)], [([], 0)]] := by
    simp only [v9373, v8974, v8963, v8279, v8165, a10090, a10089, a10088, a10087, e10086, a10085, a10084,
      e10083, a10082, a10081, e10080, a10079, a10078, e10077, a10076, a10075, e10074, a10073,
      a10072, a10071, a10070, a10069, e10068]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a10092, a10091, hB]

set_option maxRecDepth 10000 in
theorem vtB15_26F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 11107) = σ (.n 11082) + σ (.n 4912) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 2048)], [([87], 1)], [([59], 1)], [([60], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 10093 [
    .atom (.load (.n 11083) (.n 14) 0),
    .atom (.const (.n 11084) (word 2 0 0)),
    .atom (.mul (.n 11085) (.n 11083) (.n 11084)),
    .atom (.const (.n 11086) (word 2048 0 0)),
    .atom (.mul (.n 11087) (.n 8165) (.n 8279)),
    .atom (.mul (.n 11088) (.n 11086) (.n 11087)),
    .atom (.load (.n 11089) (.n 14) 1),
    .atom (.mul (.n 11090) (.n 11089) (.n 11088)),
    .atom (.add (.n 11091) (.n 11085) (.n 11090)),
    .atom (.load (.n 11092) (.n 14) 2),
    .atom (.mul (.n 11093) (.n 11092) (.n 9384)),
    .atom (.add (.n 11094) (.n 11091) (.n 11093)),
    .atom (.load (.n 11095) (.n 14) 3),
    .atom (.mul (.n 11096) (.n 11095) (.n 8985)),
    .atom (.add (.n 11097) (.n 11094) (.n 11096)),
    .atom (.load (.n 11098) (.n 14) 4),
    .atom (.mul (.n 11099) (.n 11098) (.n 8996)),
    .atom (.add (.n 11100) (.n 11097) (.n 11099)),
    .atom (.load (.n 11101) (.n 14) 5),
    .atom (.const (.n 11102) (word 0 0 0)),
    .atom (.mul (.n 11103) (.n 11101) (.n 11102)),
    .atom (.add (.n 11104) (.n 11100) (.n 11103)),
    .atom (.add (.n 11105) (.n 15) (.n 11104)),
    .atom (.mul (.n 11106) (.n 4912) (.n 11105)),
    .atom (.add (.n 11107) (.n 11082) (.n 11106))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a10093, a10094, a10095, a10096, a10097, a10098, a10099, a10100, a10101, a10102, a10103, a10104,
    a10105, a10106, a10107, a10108, a10109, a10110, a10111, a10112, a10113, a10114, a10115,
    a10116, a10117, -⟩ := hs
  have e10093 := tb_loadHolds_unique a10093 (hw 0 (by norm_num))
  have e10099 := tb_loadHolds_unique a10099 (hw 1 (by norm_num))
  have e10102 := tb_loadHolds_unique a10102 (hw 2 (by norm_num))
  have e10105 := tb_loadHolds_unique a10105 (hw 3 (by norm_num))
  have e10108 := tb_loadHolds_unique a10108 (hw 4 (by norm_num))
  have e10111 := tb_loadHolds_unique a10111 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v8985 : σ (.n 8985) = ev 59 := by
    rw [← hev 59 (by norm_num)]; exact (vt_evalF h (k := 126) (by norm_num)).2.2.1
  have v8996 : σ (.n 8996) = ev 60 := by
    rw [← hev 60 (by norm_num)]; exact (vt_evalF h (k := 127) (by norm_num)).2.2.1
  have v9384 : σ (.n 9384) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_evalF h (k := 154) (by norm_num)).2.2.1
  have hB : σ (.n 11105) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 2048)], [([87], 1)], [([59], 1)], [([60], 1)], [([], 0)]] := by
    simp only [v9384, v8996, v8985, v8279, v8165, a10115, a10114, a10113, a10112, e10111, a10110, a10109,
      e10108, a10107, a10106, e10105, a10104, a10103, e10102, a10101, a10100, e10099, a10098,
      a10097, a10096, a10095, a10094, e10093]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a10117, a10116, hB]

set_option maxRecDepth 10000 in
theorem vtB15_27F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 11132) = σ (.n 11107) + σ (.n 4919) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 4096)], [([88], 1)], [([61], 1)], [([62], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 10118 [
    .atom (.load (.n 11108) (.n 14) 0),
    .atom (.const (.n 11109) (word 2 0 0)),
    .atom (.mul (.n 11110) (.n 11108) (.n 11109)),
    .atom (.const (.n 11111) (word 4096 0 0)),
    .atom (.mul (.n 11112) (.n 8165) (.n 8279)),
    .atom (.mul (.n 11113) (.n 11111) (.n 11112)),
    .atom (.load (.n 11114) (.n 14) 1),
    .atom (.mul (.n 11115) (.n 11114) (.n 11113)),
    .atom (.add (.n 11116) (.n 11110) (.n 11115)),
    .atom (.load (.n 11117) (.n 14) 2),
    .atom (.mul (.n 11118) (.n 11117) (.n 9395)),
    .atom (.add (.n 11119) (.n 11116) (.n 11118)),
    .atom (.load (.n 11120) (.n 14) 3),
    .atom (.mul (.n 11121) (.n 11120) (.n 9020)),
    .atom (.add (.n 11122) (.n 11119) (.n 11121)),
    .atom (.load (.n 11123) (.n 14) 4),
    .atom (.mul (.n 11124) (.n 11123) (.n 9031)),
    .atom (.add (.n 11125) (.n 11122) (.n 11124)),
    .atom (.load (.n 11126) (.n 14) 5),
    .atom (.const (.n 11127) (word 0 0 0)),
    .atom (.mul (.n 11128) (.n 11126) (.n 11127)),
    .atom (.add (.n 11129) (.n 11125) (.n 11128)),
    .atom (.add (.n 11130) (.n 15) (.n 11129)),
    .atom (.mul (.n 11131) (.n 4919) (.n 11130)),
    .atom (.add (.n 11132) (.n 11107) (.n 11131))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a10118, a10119, a10120, a10121, a10122, a10123, a10124, a10125, a10126, a10127, a10128, a10129,
    a10130, a10131, a10132, a10133, a10134, a10135, a10136, a10137, a10138, a10139, a10140,
    a10141, a10142, -⟩ := hs
  have e10118 := tb_loadHolds_unique a10118 (hw 0 (by norm_num))
  have e10124 := tb_loadHolds_unique a10124 (hw 1 (by norm_num))
  have e10127 := tb_loadHolds_unique a10127 (hw 2 (by norm_num))
  have e10130 := tb_loadHolds_unique a10130 (hw 3 (by norm_num))
  have e10133 := tb_loadHolds_unique a10133 (hw 4 (by norm_num))
  have e10136 := tb_loadHolds_unique a10136 (hw 5 (by norm_num))
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have v8279 : σ (.n 8279) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2.1
  have v9020 : σ (.n 9020) = ev 61 := by
    rw [← hev 61 (by norm_num)]; exact (vt_evalF h (k := 128) (by norm_num)).2.2.1
  have v9031 : σ (.n 9031) = ev 62 := by
    rw [← hev 62 (by norm_num)]; exact (vt_evalF h (k := 129) (by norm_num)).2.2.1
  have v9395 : σ (.n 9395) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_evalF h (k := 155) (by norm_num)).2.2.1
  have hB : σ (.n 11130) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 4096)], [([88], 1)], [([61], 1)], [([62], 1)], [([], 0)]] := by
    simp only [v9395, v9031, v9020, v8279, v8165, a10140, a10139, a10138, a10137, e10136, a10135, a10134,
      e10133, a10132, a10131, e10130, a10129, a10128, e10127, a10126, a10125, e10124, a10123,
      a10122, a10121, a10120, a10119, e10118]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a10142, a10141, hB]

end
end LeanVM.Guest.B1.Tables
