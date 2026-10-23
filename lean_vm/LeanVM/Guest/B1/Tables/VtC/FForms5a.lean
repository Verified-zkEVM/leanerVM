/-
  LeanVM.Guest.B1.Tables.VtC.FForms5a

  `Vt/FormsT5a.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT5a

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB05_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9430) = σ (.n 3472) * vtBlockVal (σ (.n 15)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 8430 [
    .atom (.load (.n 9420) (.n 14) 0),
    .atom (.const (.n 9421) (word 2 0 0)),
    .atom (.mul (.n 9422) (.n 9421) (.n 8141)),
    .atom (.load (.n 9423) (.n 14) 1),
    .atom (.mul (.n 9424) (.n 9423) (.n 9422)),
    .atom (.add (.n 9425) (.n 9420) (.n 9424)),
    .atom (.load (.n 9426) (.n 14) 2),
    .atom (.mul (.n 9427) (.n 9426) (.n 8165)),
    .atom (.add (.n 9428) (.n 9425) (.n 9427)),
    .atom (.add (.n 9429) (.n 15) (.n 9428)),
    .atom (.mul (.n 9430) (.n 3472) (.n 9429))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8430, a8431, a8432, a8433, a8434, a8435, a8436, a8437, a8438, a8439, a8440, -⟩ := hs
  have e8430 := tb_loadHolds_unique a8430 (hw 0 (by norm_num))
  have e8433 := tb_loadHolds_unique a8433 (hw 1 (by norm_num))
  have e8436 := tb_loadHolds_unique a8436 (hw 2 (by norm_num))
  have v8141 : σ (.n 8141) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 67) (by norm_num)).2.2.1
  have v8165 : σ (.n 8165) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2.1
  have hB : σ (.n 9429) = vtBlockVal (σ (.n 15)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v8165, v8141, a8439, a8438, a8437, e8436, a8435, a8434, e8433, a8432, a8431, e8430]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a8440, hB]

set_option maxRecDepth 10000 in
theorem vtB05_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9478) = σ (.n 9430) + σ (.n 3491) * vtBlockVal (σ (.n 15)) W ev
      [[([], 4)], [([0], 1)], [([89], 2)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 8441 [
    .atom (.load (.n 9431) (.n 14) 0),
    .atom (.const (.n 9432) (word 4 0 0)),
    .atom (.mul (.n 9433) (.n 9431) (.n 9432)),
    .atom (.load (.n 9434) (.n 14) 1),
    .atom (.mul (.n 9435) (.n 9434) (.n 8141)),
    .atom (.add (.n 9436) (.n 9433) (.n 9435)),
    .atom (.const (.n 9437) (word 2 0 0)),
    .atom (.mul (.n 9438) (.n 9437) (.n 9419)),
    .atom (.load (.n 9439) (.n 14) 2),
    .atom (.mul (.n 9440) (.n 9439) (.n 9438)),
    .atom (.add (.n 9441) (.n 9436) (.n 9440)),
    .atom (.load (.n 9442) (.n 14) 3),
    .atom (.const (.n 9443) (word 32 0 0)),
    .atom (.mul (.n 9444) (.n 9442) (.n 9443)),
    .atom (.add (.n 9445) (.n 9441) (.n 9444)),
    .atom (.load (.n 9446) (.n 14) 4),
    .atom (.mul (.n 9447) (.n 9446) (.n 8176)),
    .atom (.add (.n 9448) (.n 9445) (.n 9447)),
    .atom (.load (.n 9449) (.n 14) 5),
    .atom (.mul (.n 9450) (.n 9449) (.n 8187)),
    .atom (.add (.n 9451) (.n 9448) (.n 9450)),
    .atom (.load (.n 9452) (.n 14) 6),
    .atom (.mul (.n 9453) (.n 9452) (.n 8198)),
    .atom (.add (.n 9454) (.n 9451) (.n 9453)),
    .atom (.load (.n 9455) (.n 14) 7),
    .atom (.mul (.n 9456) (.n 9455) (.n 8222)),
    .atom (.add (.n 9457) (.n 9454) (.n 9456)),
    .atom (.load (.n 9458) (.n 14) 8),
    .atom (.mul (.n 9459) (.n 9458) (.n 8233)),
    .atom (.add (.n 9460) (.n 9457) (.n 9459)),
    .atom (.load (.n 9461) (.n 14) 9),
    .atom (.mul (.n 9462) (.n 9461) (.n 8244)),
    .atom (.add (.n 9463) (.n 9460) (.n 9462)),
    .atom (.load (.n 9464) (.n 14) 10),
    .atom (.mul (.n 9465) (.n 9464) (.n 8255)),
    .atom (.add (.n 9466) (.n 9463) (.n 9465)),
    .atom (.load (.n 9467) (.n 14) 11),
    .atom (.mul (.n 9468) (.n 9467) (.n 8279)),
    .atom (.add (.n 9469) (.n 9466) (.n 9468)),
    .atom (.load (.n 9470) (.n 14) 12),
    .atom (.mul (.n 9471) (.n 9470) (.n 8290)),
    .atom (.add (.n 9472) (.n 9469) (.n 9471)),
    .atom (.load (.n 9473) (.n 14) 13),
    .atom (.mul (.n 9474) (.n 9473) (.n 8301)),
    .atom (.add (.n 9475) (.n 9472) (.n 9474)),
    .atom (.add (.n 9476) (.n 15) (.n 9475)),
    .atom (.mul (.n 9477) (.n 3491) (.n 9476)),
    .atom (.add (.n 9478) (.n 9430) (.n 9477))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8441, a8442, a8443, a8444, a8445, a8446, a8447, a8448, a8449, a8450, a8451, a8452, a8453, a8454,
    a8455, a8456, a8457, a8458, a8459, a8460, a8461, a8462, a8463, a8464, a8465, a8466, a8467,
    a8468, a8469, a8470, a8471, a8472, a8473, a8474, a8475, a8476, a8477, a8478, a8479, a8480,
    a8481, a8482, a8483, a8484, a8485, a8486, a8487, a8488, -⟩ := hs
  have e8441 := tb_loadHolds_unique a8441 (hw 0 (by norm_num))
  have e8444 := tb_loadHolds_unique a8444 (hw 1 (by norm_num))
  have e8449 := tb_loadHolds_unique a8449 (hw 2 (by norm_num))
  have e8452 := tb_loadHolds_unique a8452 (hw 3 (by norm_num))
  have e8456 := tb_loadHolds_unique a8456 (hw 4 (by norm_num))
  have e8459 := tb_loadHolds_unique a8459 (hw 5 (by norm_num))
  have e8462 := tb_loadHolds_unique a8462 (hw 6 (by norm_num))
  have e8465 := tb_loadHolds_unique a8465 (hw 7 (by norm_num))
  have e8468 := tb_loadHolds_unique a8468 (hw 8 (by norm_num))
  have e8471 := tb_loadHolds_unique a8471 (hw 9 (by norm_num))
  have e8474 := tb_loadHolds_unique a8474 (hw 10 (by norm_num))
  have e8477 := tb_loadHolds_unique a8477 (hw 11 (by norm_num))
  have e8480 := tb_loadHolds_unique a8480 (hw 12 (by norm_num))
  have e8483 := tb_loadHolds_unique a8483 (hw 13 (by norm_num))
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
  have hB : σ (.n 9476) = vtBlockVal (σ (.n 15)) W ev [[([], 4)], [([0], 1)], [([89], 2)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)]] := by
    simp only [v9419, v8301, v8290, v8279, v8255, v8244, v8233, v8222, v8198, v8187, v8176, v8141, a8486,
      a8485, a8484, e8483, a8482, a8481, e8480, a8479, a8478, e8477, a8476, a8475, e8474,
      a8473, a8472, e8471, a8470, a8469, e8468, a8467, a8466, e8465, a8464, a8463, e8462,
      a8461, a8460, e8459, a8458, a8457, e8456, a8455, a8454, a8453, e8452, a8451, a8450,
      e8449, a8448, a8447, a8446, a8445, e8444, a8443, a8442, e8441]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a8488, a8487, hB]

set_option maxRecDepth 10000 in
theorem vtB05_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9511) = σ (.n 9478) + σ (.n 3510) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 2], 1)], [([63], 2)], [([13], 1), ([10, 13], 1), ([10, 12], 1)], [([14], 1), ([10, 14], 1), ([10, 13], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8489 [
    .atom (.load (.n 9479) (.n 14) 0),
    .atom (.const (.n 9480) (word 2 0 0)),
    .atom (.mul (.n 9481) (.n 9479) (.n 9480)),
    .atom (.mul (.n 9482) (.n 8165) (.n 8176)),
    .atom (.load (.n 9483) (.n 14) 1),
    .atom (.mul (.n 9484) (.n 9483) (.n 9482)),
    .atom (.add (.n 9485) (.n 9481) (.n 9484)),
    .atom (.const (.n 9486) (word 2 0 0)),
    .atom (.mul (.n 9487) (.n 9486) (.n 9042)),
    .atom (.load (.n 9488) (.n 14) 2),
    .atom (.mul (.n 9489) (.n 9488) (.n 9487)),
    .atom (.add (.n 9490) (.n 9485) (.n 9489)),
    .atom (.mul (.n 9491) (.n 8290) (.n 8336)),
    .atom (.add (.n 9492) (.n 8336) (.n 9491)),
    .atom (.mul (.n 9493) (.n 8290) (.n 8312)),
    .atom (.add (.n 9494) (.n 9492) (.n 9493)),
    .atom (.load (.n 9495) (.n 14) 3),
    .atom (.mul (.n 9496) (.n 9495) (.n 9494)),
    .atom (.add (.n 9497) (.n 9490) (.n 9496)),
    .atom (.mul (.n 9498) (.n 8290) (.n 8347)),
    .atom (.add (.n 9499) (.n 8347) (.n 9498)),
    .atom (.mul (.n 9500) (.n 8290) (.n 8336)),
    .atom (.add (.n 9501) (.n 9499) (.n 9500)),
    .atom (.load (.n 9502) (.n 14) 4),
    .atom (.mul (.n 9503) (.n 9502) (.n 9501)),
    .atom (.add (.n 9504) (.n 9497) (.n 9503)),
    .atom (.load (.n 9505) (.n 14) 5),
    .atom (.const (.n 9506) (word 0 0 0)),
    .atom (.mul (.n 9507) (.n 9505) (.n 9506)),
    .atom (.add (.n 9508) (.n 9504) (.n 9507)),
    .atom (.add (.n 9509) (.n 15) (.n 9508)),
    .atom (.mul (.n 9510) (.n 3510) (.n 9509)),
    .atom (.add (.n 9511) (.n 9478) (.n 9510))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8489, a8490, a8491, a8492, a8493, a8494, a8495, a8496, a8497, a8498, a8499, a8500, a8501, a8502,
    a8503, a8504, a8505, a8506, a8507, a8508, a8509, a8510, a8511, a8512, a8513, a8514, a8515,
    a8516, a8517, a8518, a8519, a8520, a8521, -⟩ := hs
  have e8489 := tb_loadHolds_unique a8489 (hw 0 (by norm_num))
  have e8493 := tb_loadHolds_unique a8493 (hw 1 (by norm_num))
  have e8498 := tb_loadHolds_unique a8498 (hw 2 (by norm_num))
  have e8505 := tb_loadHolds_unique a8505 (hw 3 (by norm_num))
  have e8512 := tb_loadHolds_unique a8512 (hw 4 (by norm_num))
  have e8515 := tb_loadHolds_unique a8515 (hw 5 (by norm_num))
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
  have hB : σ (.n 9509) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 2], 1)], [([63], 2)], [([13], 1), ([10, 13], 1), ([10, 12], 1)], [([14], 1), ([10, 14], 1), ([10, 13], 1)], [([], 0)]] := by
    simp only [v9042, v8347, v8336, v8312, v8290, v8176, v8165, a8519, a8518, a8517, a8516, e8515, a8514,
      a8513, e8512, a8511, a8510, a8509, a8508, a8507, a8506, e8505, a8504, a8503, a8502,
      a8501, a8500, a8499, e8498, a8497, a8496, a8495, a8494, e8493, a8492, a8491, a8490,
      e8489]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8521, a8520, hB]

set_option maxRecDepth 10000 in
theorem vtB05_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9544) = σ (.n 9511) + σ (.n 3529) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 3], 1)], [([64], 2)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8522 [
    .atom (.load (.n 9512) (.n 14) 0),
    .atom (.const (.n 9513) (word 2 0 0)),
    .atom (.mul (.n 9514) (.n 9512) (.n 9513)),
    .atom (.mul (.n 9515) (.n 8165) (.n 8187)),
    .atom (.load (.n 9516) (.n 14) 1),
    .atom (.mul (.n 9517) (.n 9516) (.n 9515)),
    .atom (.add (.n 9518) (.n 9514) (.n 9517)),
    .atom (.const (.n 9519) (word 2 0 0)),
    .atom (.mul (.n 9520) (.n 9519) (.n 9053)),
    .atom (.load (.n 9521) (.n 14) 2),
    .atom (.mul (.n 9522) (.n 9521) (.n 9520)),
    .atom (.add (.n 9523) (.n 9518) (.n 9522)),
    .atom (.mul (.n 9524) (.n 8290) (.n 8358)),
    .atom (.add (.n 9525) (.n 8358) (.n 9524)),
    .atom (.mul (.n 9526) (.n 8290) (.n 8347)),
    .atom (.add (.n 9527) (.n 9525) (.n 9526)),
    .atom (.load (.n 9528) (.n 14) 3),
    .atom (.mul (.n 9529) (.n 9528) (.n 9527)),
    .atom (.add (.n 9530) (.n 9523) (.n 9529)),
    .atom (.mul (.n 9531) (.n 8290) (.n 8369)),
    .atom (.add (.n 9532) (.n 8369) (.n 9531)),
    .atom (.mul (.n 9533) (.n 8290) (.n 8358)),
    .atom (.add (.n 9534) (.n 9532) (.n 9533)),
    .atom (.load (.n 9535) (.n 14) 4),
    .atom (.mul (.n 9536) (.n 9535) (.n 9534)),
    .atom (.add (.n 9537) (.n 9530) (.n 9536)),
    .atom (.load (.n 9538) (.n 14) 5),
    .atom (.const (.n 9539) (word 0 0 0)),
    .atom (.mul (.n 9540) (.n 9538) (.n 9539)),
    .atom (.add (.n 9541) (.n 9537) (.n 9540)),
    .atom (.add (.n 9542) (.n 15) (.n 9541)),
    .atom (.mul (.n 9543) (.n 3529) (.n 9542)),
    .atom (.add (.n 9544) (.n 9511) (.n 9543))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8522, a8523, a8524, a8525, a8526, a8527, a8528, a8529, a8530, a8531, a8532, a8533, a8534, a8535,
    a8536, a8537, a8538, a8539, a8540, a8541, a8542, a8543, a8544, a8545, a8546, a8547, a8548,
    a8549, a8550, a8551, a8552, a8553, a8554, -⟩ := hs
  have e8522 := tb_loadHolds_unique a8522 (hw 0 (by norm_num))
  have e8526 := tb_loadHolds_unique a8526 (hw 1 (by norm_num))
  have e8531 := tb_loadHolds_unique a8531 (hw 2 (by norm_num))
  have e8538 := tb_loadHolds_unique a8538 (hw 3 (by norm_num))
  have e8545 := tb_loadHolds_unique a8545 (hw 4 (by norm_num))
  have e8548 := tb_loadHolds_unique a8548 (hw 5 (by norm_num))
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
  have hB : σ (.n 9542) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 3], 1)], [([64], 2)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)], [([], 0)]] := by
    simp only [v9053, v8369, v8358, v8347, v8290, v8187, v8165, a8552, a8551, a8550, a8549, e8548, a8547,
      a8546, e8545, a8544, a8543, a8542, a8541, a8540, a8539, e8538, a8537, a8536, a8535,
      a8534, a8533, a8532, e8531, a8530, a8529, a8528, a8527, e8526, a8525, a8524, a8523,
      e8522]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8554, a8553, hB]

set_option maxRecDepth 10000 in
theorem vtB05_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9577) = σ (.n 9544) + σ (.n 3548) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 4], 1)], [([65], 2)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8555 [
    .atom (.load (.n 9545) (.n 14) 0),
    .atom (.const (.n 9546) (word 2 0 0)),
    .atom (.mul (.n 9547) (.n 9545) (.n 9546)),
    .atom (.mul (.n 9548) (.n 8165) (.n 8198)),
    .atom (.load (.n 9549) (.n 14) 1),
    .atom (.mul (.n 9550) (.n 9549) (.n 9548)),
    .atom (.add (.n 9551) (.n 9547) (.n 9550)),
    .atom (.const (.n 9552) (word 2 0 0)),
    .atom (.mul (.n 9553) (.n 9552) (.n 9077)),
    .atom (.load (.n 9554) (.n 14) 2),
    .atom (.mul (.n 9555) (.n 9554) (.n 9553)),
    .atom (.add (.n 9556) (.n 9551) (.n 9555)),
    .atom (.mul (.n 9557) (.n 8290) (.n 8393)),
    .atom (.add (.n 9558) (.n 8393) (.n 9557)),
    .atom (.mul (.n 9559) (.n 8290) (.n 8369)),
    .atom (.add (.n 9560) (.n 9558) (.n 9559)),
    .atom (.load (.n 9561) (.n 14) 3),
    .atom (.mul (.n 9562) (.n 9561) (.n 9560)),
    .atom (.add (.n 9563) (.n 9556) (.n 9562)),
    .atom (.mul (.n 9564) (.n 8290) (.n 8404)),
    .atom (.add (.n 9565) (.n 8404) (.n 9564)),
    .atom (.mul (.n 9566) (.n 8290) (.n 8393)),
    .atom (.add (.n 9567) (.n 9565) (.n 9566)),
    .atom (.load (.n 9568) (.n 14) 4),
    .atom (.mul (.n 9569) (.n 9568) (.n 9567)),
    .atom (.add (.n 9570) (.n 9563) (.n 9569)),
    .atom (.load (.n 9571) (.n 14) 5),
    .atom (.const (.n 9572) (word 0 0 0)),
    .atom (.mul (.n 9573) (.n 9571) (.n 9572)),
    .atom (.add (.n 9574) (.n 9570) (.n 9573)),
    .atom (.add (.n 9575) (.n 15) (.n 9574)),
    .atom (.mul (.n 9576) (.n 3548) (.n 9575)),
    .atom (.add (.n 9577) (.n 9544) (.n 9576))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8555, a8556, a8557, a8558, a8559, a8560, a8561, a8562, a8563, a8564, a8565, a8566, a8567, a8568,
    a8569, a8570, a8571, a8572, a8573, a8574, a8575, a8576, a8577, a8578, a8579, a8580, a8581,
    a8582, a8583, a8584, a8585, a8586, a8587, -⟩ := hs
  have e8555 := tb_loadHolds_unique a8555 (hw 0 (by norm_num))
  have e8559 := tb_loadHolds_unique a8559 (hw 1 (by norm_num))
  have e8564 := tb_loadHolds_unique a8564 (hw 2 (by norm_num))
  have e8571 := tb_loadHolds_unique a8571 (hw 3 (by norm_num))
  have e8578 := tb_loadHolds_unique a8578 (hw 4 (by norm_num))
  have e8581 := tb_loadHolds_unique a8581 (hw 5 (by norm_num))
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
  have hB : σ (.n 9575) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 4], 1)], [([65], 2)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)], [([], 0)]] := by
    simp only [v9077, v8404, v8393, v8369, v8290, v8198, v8165, a8585, a8584, a8583, a8582, e8581, a8580,
      a8579, e8578, a8577, a8576, a8575, a8574, a8573, a8572, e8571, a8570, a8569, a8568,
      a8567, a8566, a8565, e8564, a8563, a8562, a8561, a8560, e8559, a8558, a8557, a8556,
      e8555]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8587, a8586, hB]

set_option maxRecDepth 10000 in
theorem vtB05_5F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9610) = σ (.n 9577) + σ (.n 3567) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 5], 1)], [([66], 2)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8588 [
    .atom (.load (.n 9578) (.n 14) 0),
    .atom (.const (.n 9579) (word 2 0 0)),
    .atom (.mul (.n 9580) (.n 9578) (.n 9579)),
    .atom (.mul (.n 9581) (.n 8165) (.n 8222)),
    .atom (.load (.n 9582) (.n 14) 1),
    .atom (.mul (.n 9583) (.n 9582) (.n 9581)),
    .atom (.add (.n 9584) (.n 9580) (.n 9583)),
    .atom (.const (.n 9585) (word 2 0 0)),
    .atom (.mul (.n 9586) (.n 9585) (.n 9088)),
    .atom (.load (.n 9587) (.n 14) 2),
    .atom (.mul (.n 9588) (.n 9587) (.n 9586)),
    .atom (.add (.n 9589) (.n 9584) (.n 9588)),
    .atom (.mul (.n 9590) (.n 8290) (.n 8415)),
    .atom (.add (.n 9591) (.n 8415) (.n 9590)),
    .atom (.mul (.n 9592) (.n 8290) (.n 8404)),
    .atom (.add (.n 9593) (.n 9591) (.n 9592)),
    .atom (.load (.n 9594) (.n 14) 3),
    .atom (.mul (.n 9595) (.n 9594) (.n 9593)),
    .atom (.add (.n 9596) (.n 9589) (.n 9595)),
    .atom (.mul (.n 9597) (.n 8290) (.n 8426)),
    .atom (.add (.n 9598) (.n 8426) (.n 9597)),
    .atom (.mul (.n 9599) (.n 8290) (.n 8415)),
    .atom (.add (.n 9600) (.n 9598) (.n 9599)),
    .atom (.load (.n 9601) (.n 14) 4),
    .atom (.mul (.n 9602) (.n 9601) (.n 9600)),
    .atom (.add (.n 9603) (.n 9596) (.n 9602)),
    .atom (.load (.n 9604) (.n 14) 5),
    .atom (.const (.n 9605) (word 0 0 0)),
    .atom (.mul (.n 9606) (.n 9604) (.n 9605)),
    .atom (.add (.n 9607) (.n 9603) (.n 9606)),
    .atom (.add (.n 9608) (.n 15) (.n 9607)),
    .atom (.mul (.n 9609) (.n 3567) (.n 9608)),
    .atom (.add (.n 9610) (.n 9577) (.n 9609))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8588, a8589, a8590, a8591, a8592, a8593, a8594, a8595, a8596, a8597, a8598, a8599, a8600, a8601,
    a8602, a8603, a8604, a8605, a8606, a8607, a8608, a8609, a8610, a8611, a8612, a8613, a8614,
    a8615, a8616, a8617, a8618, a8619, a8620, -⟩ := hs
  have e8588 := tb_loadHolds_unique a8588 (hw 0 (by norm_num))
  have e8592 := tb_loadHolds_unique a8592 (hw 1 (by norm_num))
  have e8597 := tb_loadHolds_unique a8597 (hw 2 (by norm_num))
  have e8604 := tb_loadHolds_unique a8604 (hw 3 (by norm_num))
  have e8611 := tb_loadHolds_unique a8611 (hw 4 (by norm_num))
  have e8614 := tb_loadHolds_unique a8614 (hw 5 (by norm_num))
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
  have hB : σ (.n 9608) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 5], 1)], [([66], 2)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)], [([], 0)]] := by
    simp only [v9088, v8426, v8415, v8404, v8290, v8222, v8165, a8618, a8617, a8616, a8615, e8614, a8613,
      a8612, e8611, a8610, a8609, a8608, a8607, a8606, a8605, e8604, a8603, a8602, a8601,
      a8600, a8599, a8598, e8597, a8596, a8595, a8594, a8593, e8592, a8591, a8590, a8589,
      e8588]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8620, a8619, hB]

set_option maxRecDepth 10000 in
theorem vtB05_6F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9643) = σ (.n 9610) + σ (.n 3586) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 6], 1)], [([67], 2)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8621 [
    .atom (.load (.n 9611) (.n 14) 0),
    .atom (.const (.n 9612) (word 2 0 0)),
    .atom (.mul (.n 9613) (.n 9611) (.n 9612)),
    .atom (.mul (.n 9614) (.n 8165) (.n 8233)),
    .atom (.load (.n 9615) (.n 14) 1),
    .atom (.mul (.n 9616) (.n 9615) (.n 9614)),
    .atom (.add (.n 9617) (.n 9613) (.n 9616)),
    .atom (.const (.n 9618) (word 2 0 0)),
    .atom (.mul (.n 9619) (.n 9618) (.n 9099)),
    .atom (.load (.n 9620) (.n 14) 2),
    .atom (.mul (.n 9621) (.n 9620) (.n 9619)),
    .atom (.add (.n 9622) (.n 9617) (.n 9621)),
    .atom (.mul (.n 9623) (.n 8290) (.n 8450)),
    .atom (.add (.n 9624) (.n 8450) (.n 9623)),
    .atom (.mul (.n 9625) (.n 8290) (.n 8426)),
    .atom (.add (.n 9626) (.n 9624) (.n 9625)),
    .atom (.load (.n 9627) (.n 14) 3),
    .atom (.mul (.n 9628) (.n 9627) (.n 9626)),
    .atom (.add (.n 9629) (.n 9622) (.n 9628)),
    .atom (.mul (.n 9630) (.n 8290) (.n 8461)),
    .atom (.add (.n 9631) (.n 8461) (.n 9630)),
    .atom (.mul (.n 9632) (.n 8290) (.n 8450)),
    .atom (.add (.n 9633) (.n 9631) (.n 9632)),
    .atom (.load (.n 9634) (.n 14) 4),
    .atom (.mul (.n 9635) (.n 9634) (.n 9633)),
    .atom (.add (.n 9636) (.n 9629) (.n 9635)),
    .atom (.load (.n 9637) (.n 14) 5),
    .atom (.const (.n 9638) (word 0 0 0)),
    .atom (.mul (.n 9639) (.n 9637) (.n 9638)),
    .atom (.add (.n 9640) (.n 9636) (.n 9639)),
    .atom (.add (.n 9641) (.n 15) (.n 9640)),
    .atom (.mul (.n 9642) (.n 3586) (.n 9641)),
    .atom (.add (.n 9643) (.n 9610) (.n 9642))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8621, a8622, a8623, a8624, a8625, a8626, a8627, a8628, a8629, a8630, a8631, a8632, a8633, a8634,
    a8635, a8636, a8637, a8638, a8639, a8640, a8641, a8642, a8643, a8644, a8645, a8646, a8647,
    a8648, a8649, a8650, a8651, a8652, a8653, -⟩ := hs
  have e8621 := tb_loadHolds_unique a8621 (hw 0 (by norm_num))
  have e8625 := tb_loadHolds_unique a8625 (hw 1 (by norm_num))
  have e8630 := tb_loadHolds_unique a8630 (hw 2 (by norm_num))
  have e8637 := tb_loadHolds_unique a8637 (hw 3 (by norm_num))
  have e8644 := tb_loadHolds_unique a8644 (hw 4 (by norm_num))
  have e8647 := tb_loadHolds_unique a8647 (hw 5 (by norm_num))
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
  have hB : σ (.n 9641) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 6], 1)], [([67], 2)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)], [([], 0)]] := by
    simp only [v9099, v8461, v8450, v8426, v8290, v8233, v8165, a8651, a8650, a8649, a8648, e8647, a8646,
      a8645, e8644, a8643, a8642, a8641, a8640, a8639, a8638, e8637, a8636, a8635, a8634,
      a8633, a8632, a8631, e8630, a8629, a8628, a8627, a8626, e8625, a8624, a8623, a8622,
      e8621]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8653, a8652, hB]

set_option maxRecDepth 10000 in
theorem vtB05_7F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9678) = σ (.n 9643) + σ (.n 3605) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 6], 2)], [([68], 2)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8654 [
    .atom (.load (.n 9644) (.n 14) 0),
    .atom (.const (.n 9645) (word 2 0 0)),
    .atom (.mul (.n 9646) (.n 9644) (.n 9645)),
    .atom (.const (.n 9647) (word 2 0 0)),
    .atom (.mul (.n 9648) (.n 8165) (.n 8233)),
    .atom (.mul (.n 9649) (.n 9647) (.n 9648)),
    .atom (.load (.n 9650) (.n 14) 1),
    .atom (.mul (.n 9651) (.n 9650) (.n 9649)),
    .atom (.add (.n 9652) (.n 9646) (.n 9651)),
    .atom (.const (.n 9653) (word 2 0 0)),
    .atom (.mul (.n 9654) (.n 9653) (.n 9110)),
    .atom (.load (.n 9655) (.n 14) 2),
    .atom (.mul (.n 9656) (.n 9655) (.n 9654)),
    .atom (.add (.n 9657) (.n 9652) (.n 9656)),
    .atom (.mul (.n 9658) (.n 8290) (.n 8472)),
    .atom (.add (.n 9659) (.n 8472) (.n 9658)),
    .atom (.mul (.n 9660) (.n 8290) (.n 8461)),
    .atom (.add (.n 9661) (.n 9659) (.n 9660)),
    .atom (.load (.n 9662) (.n 14) 3),
    .atom (.mul (.n 9663) (.n 9662) (.n 9661)),
    .atom (.add (.n 9664) (.n 9657) (.n 9663)),
    .atom (.mul (.n 9665) (.n 8290) (.n 8483)),
    .atom (.add (.n 9666) (.n 8483) (.n 9665)),
    .atom (.mul (.n 9667) (.n 8290) (.n 8472)),
    .atom (.add (.n 9668) (.n 9666) (.n 9667)),
    .atom (.load (.n 9669) (.n 14) 4),
    .atom (.mul (.n 9670) (.n 9669) (.n 9668)),
    .atom (.add (.n 9671) (.n 9664) (.n 9670)),
    .atom (.load (.n 9672) (.n 14) 5),
    .atom (.const (.n 9673) (word 0 0 0)),
    .atom (.mul (.n 9674) (.n 9672) (.n 9673)),
    .atom (.add (.n 9675) (.n 9671) (.n 9674)),
    .atom (.add (.n 9676) (.n 15) (.n 9675)),
    .atom (.mul (.n 9677) (.n 3605) (.n 9676)),
    .atom (.add (.n 9678) (.n 9643) (.n 9677))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8654, a8655, a8656, a8657, a8658, a8659, a8660, a8661, a8662, a8663, a8664, a8665, a8666, a8667,
    a8668, a8669, a8670, a8671, a8672, a8673, a8674, a8675, a8676, a8677, a8678, a8679, a8680,
    a8681, a8682, a8683, a8684, a8685, a8686, a8687, a8688, -⟩ := hs
  have e8654 := tb_loadHolds_unique a8654 (hw 0 (by norm_num))
  have e8660 := tb_loadHolds_unique a8660 (hw 1 (by norm_num))
  have e8665 := tb_loadHolds_unique a8665 (hw 2 (by norm_num))
  have e8672 := tb_loadHolds_unique a8672 (hw 3 (by norm_num))
  have e8679 := tb_loadHolds_unique a8679 (hw 4 (by norm_num))
  have e8682 := tb_loadHolds_unique a8682 (hw 5 (by norm_num))
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
  have hB : σ (.n 9676) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 6], 2)], [([68], 2)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)], [([], 0)]] := by
    simp only [v9110, v8483, v8472, v8461, v8290, v8233, v8165, a8686, a8685, a8684, a8683, e8682, a8681,
      a8680, e8679, a8678, a8677, a8676, a8675, a8674, a8673, e8672, a8671, a8670, a8669,
      a8668, a8667, a8666, e8665, a8664, a8663, a8662, a8661, e8660, a8659, a8658, a8657,
      a8656, a8655, e8654]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8688, a8687, hB]

set_option maxRecDepth 10000 in
theorem vtB05_8F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9713) = σ (.n 9678) + σ (.n 3624) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 6], 4)], [([69], 2)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8689 [
    .atom (.load (.n 9679) (.n 14) 0),
    .atom (.const (.n 9680) (word 2 0 0)),
    .atom (.mul (.n 9681) (.n 9679) (.n 9680)),
    .atom (.const (.n 9682) (word 4 0 0)),
    .atom (.mul (.n 9683) (.n 8165) (.n 8233)),
    .atom (.mul (.n 9684) (.n 9682) (.n 9683)),
    .atom (.load (.n 9685) (.n 14) 1),
    .atom (.mul (.n 9686) (.n 9685) (.n 9684)),
    .atom (.add (.n 9687) (.n 9681) (.n 9686)),
    .atom (.const (.n 9688) (word 2 0 0)),
    .atom (.mul (.n 9689) (.n 9688) (.n 9134)),
    .atom (.load (.n 9690) (.n 14) 2),
    .atom (.mul (.n 9691) (.n 9690) (.n 9689)),
    .atom (.add (.n 9692) (.n 9687) (.n 9691)),
    .atom (.mul (.n 9693) (.n 8290) (.n 8507)),
    .atom (.add (.n 9694) (.n 8507) (.n 9693)),
    .atom (.mul (.n 9695) (.n 8290) (.n 8483)),
    .atom (.add (.n 9696) (.n 9694) (.n 9695)),
    .atom (.load (.n 9697) (.n 14) 3),
    .atom (.mul (.n 9698) (.n 9697) (.n 9696)),
    .atom (.add (.n 9699) (.n 9692) (.n 9698)),
    .atom (.mul (.n 9700) (.n 8290) (.n 8518)),
    .atom (.add (.n 9701) (.n 8518) (.n 9700)),
    .atom (.mul (.n 9702) (.n 8290) (.n 8507)),
    .atom (.add (.n 9703) (.n 9701) (.n 9702)),
    .atom (.load (.n 9704) (.n 14) 4),
    .atom (.mul (.n 9705) (.n 9704) (.n 9703)),
    .atom (.add (.n 9706) (.n 9699) (.n 9705)),
    .atom (.load (.n 9707) (.n 14) 5),
    .atom (.const (.n 9708) (word 0 0 0)),
    .atom (.mul (.n 9709) (.n 9707) (.n 9708)),
    .atom (.add (.n 9710) (.n 9706) (.n 9709)),
    .atom (.add (.n 9711) (.n 15) (.n 9710)),
    .atom (.mul (.n 9712) (.n 3624) (.n 9711)),
    .atom (.add (.n 9713) (.n 9678) (.n 9712))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8689, a8690, a8691, a8692, a8693, a8694, a8695, a8696, a8697, a8698, a8699, a8700, a8701, a8702,
    a8703, a8704, a8705, a8706, a8707, a8708, a8709, a8710, a8711, a8712, a8713, a8714, a8715,
    a8716, a8717, a8718, a8719, a8720, a8721, a8722, a8723, -⟩ := hs
  have e8689 := tb_loadHolds_unique a8689 (hw 0 (by norm_num))
  have e8695 := tb_loadHolds_unique a8695 (hw 1 (by norm_num))
  have e8700 := tb_loadHolds_unique a8700 (hw 2 (by norm_num))
  have e8707 := tb_loadHolds_unique a8707 (hw 3 (by norm_num))
  have e8714 := tb_loadHolds_unique a8714 (hw 4 (by norm_num))
  have e8717 := tb_loadHolds_unique a8717 (hw 5 (by norm_num))
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
  have hB : σ (.n 9711) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 6], 4)], [([69], 2)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)], [([], 0)]] := by
    simp only [v9134, v8518, v8507, v8483, v8290, v8233, v8165, a8721, a8720, a8719, a8718, e8717, a8716,
      a8715, e8714, a8713, a8712, a8711, a8710, a8709, a8708, e8707, a8706, a8705, a8704,
      a8703, a8702, a8701, e8700, a8699, a8698, a8697, a8696, e8695, a8694, a8693, a8692,
      a8691, a8690, e8689]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8723, a8722, hB]

set_option maxRecDepth 10000 in
theorem vtB05_9F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9748) = σ (.n 9713) + σ (.n 3643) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 6], 8)], [([70], 2)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8724 [
    .atom (.load (.n 9714) (.n 14) 0),
    .atom (.const (.n 9715) (word 2 0 0)),
    .atom (.mul (.n 9716) (.n 9714) (.n 9715)),
    .atom (.const (.n 9717) (word 8 0 0)),
    .atom (.mul (.n 9718) (.n 8165) (.n 8233)),
    .atom (.mul (.n 9719) (.n 9717) (.n 9718)),
    .atom (.load (.n 9720) (.n 14) 1),
    .atom (.mul (.n 9721) (.n 9720) (.n 9719)),
    .atom (.add (.n 9722) (.n 9716) (.n 9721)),
    .atom (.const (.n 9723) (word 2 0 0)),
    .atom (.mul (.n 9724) (.n 9723) (.n 9145)),
    .atom (.load (.n 9725) (.n 14) 2),
    .atom (.mul (.n 9726) (.n 9725) (.n 9724)),
    .atom (.add (.n 9727) (.n 9722) (.n 9726)),
    .atom (.mul (.n 9728) (.n 8290) (.n 8529)),
    .atom (.add (.n 9729) (.n 8529) (.n 9728)),
    .atom (.mul (.n 9730) (.n 8290) (.n 8518)),
    .atom (.add (.n 9731) (.n 9729) (.n 9730)),
    .atom (.load (.n 9732) (.n 14) 3),
    .atom (.mul (.n 9733) (.n 9732) (.n 9731)),
    .atom (.add (.n 9734) (.n 9727) (.n 9733)),
    .atom (.mul (.n 9735) (.n 8290) (.n 8540)),
    .atom (.add (.n 9736) (.n 8540) (.n 9735)),
    .atom (.mul (.n 9737) (.n 8290) (.n 8529)),
    .atom (.add (.n 9738) (.n 9736) (.n 9737)),
    .atom (.load (.n 9739) (.n 14) 4),
    .atom (.mul (.n 9740) (.n 9739) (.n 9738)),
    .atom (.add (.n 9741) (.n 9734) (.n 9740)),
    .atom (.load (.n 9742) (.n 14) 5),
    .atom (.const (.n 9743) (word 0 0 0)),
    .atom (.mul (.n 9744) (.n 9742) (.n 9743)),
    .atom (.add (.n 9745) (.n 9741) (.n 9744)),
    .atom (.add (.n 9746) (.n 15) (.n 9745)),
    .atom (.mul (.n 9747) (.n 3643) (.n 9746)),
    .atom (.add (.n 9748) (.n 9713) (.n 9747))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8724, a8725, a8726, a8727, a8728, a8729, a8730, a8731, a8732, a8733, a8734, a8735, a8736, a8737,
    a8738, a8739, a8740, a8741, a8742, a8743, a8744, a8745, a8746, a8747, a8748, a8749, a8750,
    a8751, a8752, a8753, a8754, a8755, a8756, a8757, a8758, -⟩ := hs
  have e8724 := tb_loadHolds_unique a8724 (hw 0 (by norm_num))
  have e8730 := tb_loadHolds_unique a8730 (hw 1 (by norm_num))
  have e8735 := tb_loadHolds_unique a8735 (hw 2 (by norm_num))
  have e8742 := tb_loadHolds_unique a8742 (hw 3 (by norm_num))
  have e8749 := tb_loadHolds_unique a8749 (hw 4 (by norm_num))
  have e8752 := tb_loadHolds_unique a8752 (hw 5 (by norm_num))
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
  have hB : σ (.n 9746) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 6], 8)], [([70], 2)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)], [([], 0)]] := by
    simp only [v9145, v8540, v8529, v8518, v8290, v8233, v8165, a8756, a8755, a8754, a8753, e8752, a8751,
      a8750, e8749, a8748, a8747, a8746, a8745, a8744, a8743, e8742, a8741, a8740, a8739,
      a8738, a8737, a8736, e8735, a8734, a8733, a8732, a8731, e8730, a8729, a8728, a8727,
      a8726, a8725, e8724]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8758, a8757, hB]

set_option maxRecDepth 10000 in
theorem vtB05_10F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9781) = σ (.n 9748) + σ (.n 3662) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 7], 1)], [([71], 2)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([12], 1), ([10, 12], 1), ([10, 29], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8759 [
    .atom (.load (.n 9749) (.n 14) 0),
    .atom (.const (.n 9750) (word 2 0 0)),
    .atom (.mul (.n 9751) (.n 9749) (.n 9750)),
    .atom (.mul (.n 9752) (.n 8165) (.n 8244)),
    .atom (.load (.n 9753) (.n 14) 1),
    .atom (.mul (.n 9754) (.n 9753) (.n 9752)),
    .atom (.add (.n 9755) (.n 9751) (.n 9754)),
    .atom (.const (.n 9756) (word 2 0 0)),
    .atom (.mul (.n 9757) (.n 9756) (.n 9156)),
    .atom (.load (.n 9758) (.n 14) 2),
    .atom (.mul (.n 9759) (.n 9758) (.n 9757)),
    .atom (.add (.n 9760) (.n 9755) (.n 9759)),
    .atom (.mul (.n 9761) (.n 8290) (.n 8564)),
    .atom (.add (.n 9762) (.n 8564) (.n 9761)),
    .atom (.mul (.n 9763) (.n 8290) (.n 8540)),
    .atom (.add (.n 9764) (.n 9762) (.n 9763)),
    .atom (.load (.n 9765) (.n 14) 3),
    .atom (.mul (.n 9766) (.n 9765) (.n 9764)),
    .atom (.add (.n 9767) (.n 9760) (.n 9766)),
    .atom (.mul (.n 9768) (.n 8290) (.n 8312)),
    .atom (.add (.n 9769) (.n 8312) (.n 9768)),
    .atom (.mul (.n 9770) (.n 8290) (.n 8564)),
    .atom (.add (.n 9771) (.n 9769) (.n 9770)),
    .atom (.load (.n 9772) (.n 14) 4),
    .atom (.mul (.n 9773) (.n 9772) (.n 9771)),
    .atom (.add (.n 9774) (.n 9767) (.n 9773)),
    .atom (.load (.n 9775) (.n 14) 5),
    .atom (.const (.n 9776) (word 0 0 0)),
    .atom (.mul (.n 9777) (.n 9775) (.n 9776)),
    .atom (.add (.n 9778) (.n 9774) (.n 9777)),
    .atom (.add (.n 9779) (.n 15) (.n 9778)),
    .atom (.mul (.n 9780) (.n 3662) (.n 9779)),
    .atom (.add (.n 9781) (.n 9748) (.n 9780))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8759, a8760, a8761, a8762, a8763, a8764, a8765, a8766, a8767, a8768, a8769, a8770, a8771, a8772,
    a8773, a8774, a8775, a8776, a8777, a8778, a8779, a8780, a8781, a8782, a8783, a8784, a8785,
    a8786, a8787, a8788, a8789, a8790, a8791, -⟩ := hs
  have e8759 := tb_loadHolds_unique a8759 (hw 0 (by norm_num))
  have e8763 := tb_loadHolds_unique a8763 (hw 1 (by norm_num))
  have e8768 := tb_loadHolds_unique a8768 (hw 2 (by norm_num))
  have e8775 := tb_loadHolds_unique a8775 (hw 3 (by norm_num))
  have e8782 := tb_loadHolds_unique a8782 (hw 4 (by norm_num))
  have e8785 := tb_loadHolds_unique a8785 (hw 5 (by norm_num))
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
  have hB : σ (.n 9779) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 7], 1)], [([71], 2)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([12], 1), ([10, 12], 1), ([10, 29], 1)], [([], 0)]] := by
    simp only [v9156, v8564, v8540, v8312, v8290, v8244, v8165, a8789, a8788, a8787, a8786, e8785, a8784,
      a8783, e8782, a8781, a8780, a8779, a8778, a8777, a8776, e8775, a8774, a8773, a8772,
      a8771, a8770, a8769, e8768, a8767, a8766, a8765, a8764, e8763, a8762, a8761, a8760,
      e8759]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8791, a8790, hB]

set_option maxRecDepth 10000 in
theorem vtB05_11F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9806) = σ (.n 9781) + σ (.n 3681) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 8], 1)], [([72], 2)], [([30], 1)], [([31], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8792 [
    .atom (.load (.n 9782) (.n 14) 0),
    .atom (.const (.n 9783) (word 2 0 0)),
    .atom (.mul (.n 9784) (.n 9782) (.n 9783)),
    .atom (.mul (.n 9785) (.n 8165) (.n 8255)),
    .atom (.load (.n 9786) (.n 14) 1),
    .atom (.mul (.n 9787) (.n 9786) (.n 9785)),
    .atom (.add (.n 9788) (.n 9784) (.n 9787)),
    .atom (.const (.n 9789) (word 2 0 0)),
    .atom (.mul (.n 9790) (.n 9789) (.n 9167)),
    .atom (.load (.n 9791) (.n 14) 2),
    .atom (.mul (.n 9792) (.n 9791) (.n 9790)),
    .atom (.add (.n 9793) (.n 9788) (.n 9792)),
    .atom (.load (.n 9794) (.n 14) 3),
    .atom (.mul (.n 9795) (.n 9794) (.n 8575)),
    .atom (.add (.n 9796) (.n 9793) (.n 9795)),
    .atom (.load (.n 9797) (.n 14) 4),
    .atom (.mul (.n 9798) (.n 9797) (.n 8586)),
    .atom (.add (.n 9799) (.n 9796) (.n 9798)),
    .atom (.load (.n 9800) (.n 14) 5),
    .atom (.const (.n 9801) (word 0 0 0)),
    .atom (.mul (.n 9802) (.n 9800) (.n 9801)),
    .atom (.add (.n 9803) (.n 9799) (.n 9802)),
    .atom (.add (.n 9804) (.n 15) (.n 9803)),
    .atom (.mul (.n 9805) (.n 3681) (.n 9804)),
    .atom (.add (.n 9806) (.n 9781) (.n 9805))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8792, a8793, a8794, a8795, a8796, a8797, a8798, a8799, a8800, a8801, a8802, a8803, a8804, a8805,
    a8806, a8807, a8808, a8809, a8810, a8811, a8812, a8813, a8814, a8815, a8816, -⟩ := hs
  have e8792 := tb_loadHolds_unique a8792 (hw 0 (by norm_num))
  have e8796 := tb_loadHolds_unique a8796 (hw 1 (by norm_num))
  have e8801 := tb_loadHolds_unique a8801 (hw 2 (by norm_num))
  have e8804 := tb_loadHolds_unique a8804 (hw 3 (by norm_num))
  have e8807 := tb_loadHolds_unique a8807 (hw 4 (by norm_num))
  have e8810 := tb_loadHolds_unique a8810 (hw 5 (by norm_num))
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
  have hB : σ (.n 9804) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 8], 1)], [([72], 2)], [([30], 1)], [([31], 1)], [([], 0)]] := by
    simp only [v9167, v8586, v8575, v8255, v8165, a8814, a8813, a8812, a8811, e8810, a8809, a8808, e8807,
      a8806, a8805, e8804, a8803, a8802, e8801, a8800, a8799, a8798, a8797, e8796, a8795,
      a8794, a8793, e8792]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8816, a8815, hB]

set_option maxRecDepth 10000 in
theorem vtB05_12F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9833) = σ (.n 9806) + σ (.n 3700) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 8], 2)], [([73], 2)], [([32], 1)], [([33], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8817 [
    .atom (.load (.n 9807) (.n 14) 0),
    .atom (.const (.n 9808) (word 2 0 0)),
    .atom (.mul (.n 9809) (.n 9807) (.n 9808)),
    .atom (.const (.n 9810) (word 2 0 0)),
    .atom (.mul (.n 9811) (.n 8165) (.n 8255)),
    .atom (.mul (.n 9812) (.n 9810) (.n 9811)),
    .atom (.load (.n 9813) (.n 14) 1),
    .atom (.mul (.n 9814) (.n 9813) (.n 9812)),
    .atom (.add (.n 9815) (.n 9809) (.n 9814)),
    .atom (.const (.n 9816) (word 2 0 0)),
    .atom (.mul (.n 9817) (.n 9816) (.n 9191)),
    .atom (.load (.n 9818) (.n 14) 2),
    .atom (.mul (.n 9819) (.n 9818) (.n 9817)),
    .atom (.add (.n 9820) (.n 9815) (.n 9819)),
    .atom (.load (.n 9821) (.n 14) 3),
    .atom (.mul (.n 9822) (.n 9821) (.n 8597)),
    .atom (.add (.n 9823) (.n 9820) (.n 9822)),
    .atom (.load (.n 9824) (.n 14) 4),
    .atom (.mul (.n 9825) (.n 9824) (.n 8621)),
    .atom (.add (.n 9826) (.n 9823) (.n 9825)),
    .atom (.load (.n 9827) (.n 14) 5),
    .atom (.const (.n 9828) (word 0 0 0)),
    .atom (.mul (.n 9829) (.n 9827) (.n 9828)),
    .atom (.add (.n 9830) (.n 9826) (.n 9829)),
    .atom (.add (.n 9831) (.n 15) (.n 9830)),
    .atom (.mul (.n 9832) (.n 3700) (.n 9831)),
    .atom (.add (.n 9833) (.n 9806) (.n 9832))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8817, a8818, a8819, a8820, a8821, a8822, a8823, a8824, a8825, a8826, a8827, a8828, a8829, a8830,
    a8831, a8832, a8833, a8834, a8835, a8836, a8837, a8838, a8839, a8840, a8841, a8842, a8843, -⟩ := hs
  have e8817 := tb_loadHolds_unique a8817 (hw 0 (by norm_num))
  have e8823 := tb_loadHolds_unique a8823 (hw 1 (by norm_num))
  have e8828 := tb_loadHolds_unique a8828 (hw 2 (by norm_num))
  have e8831 := tb_loadHolds_unique a8831 (hw 3 (by norm_num))
  have e8834 := tb_loadHolds_unique a8834 (hw 4 (by norm_num))
  have e8837 := tb_loadHolds_unique a8837 (hw 5 (by norm_num))
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
  have hB : σ (.n 9831) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 8], 2)], [([73], 2)], [([32], 1)], [([33], 1)], [([], 0)]] := by
    simp only [v9191, v8621, v8597, v8255, v8165, a8841, a8840, a8839, a8838, e8837, a8836, a8835, e8834,
      a8833, a8832, e8831, a8830, a8829, e8828, a8827, a8826, a8825, a8824, e8823, a8822,
      a8821, a8820, a8819, a8818, e8817]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8843, a8842, hB]

set_option maxRecDepth 10000 in
theorem vtB05_13F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9860) = σ (.n 9833) + σ (.n 3719) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 8], 4)], [([74], 2)], [([34], 1)], [([35], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8844 [
    .atom (.load (.n 9834) (.n 14) 0),
    .atom (.const (.n 9835) (word 2 0 0)),
    .atom (.mul (.n 9836) (.n 9834) (.n 9835)),
    .atom (.const (.n 9837) (word 4 0 0)),
    .atom (.mul (.n 9838) (.n 8165) (.n 8255)),
    .atom (.mul (.n 9839) (.n 9837) (.n 9838)),
    .atom (.load (.n 9840) (.n 14) 1),
    .atom (.mul (.n 9841) (.n 9840) (.n 9839)),
    .atom (.add (.n 9842) (.n 9836) (.n 9841)),
    .atom (.const (.n 9843) (word 2 0 0)),
    .atom (.mul (.n 9844) (.n 9843) (.n 9202)),
    .atom (.load (.n 9845) (.n 14) 2),
    .atom (.mul (.n 9846) (.n 9845) (.n 9844)),
    .atom (.add (.n 9847) (.n 9842) (.n 9846)),
    .atom (.load (.n 9848) (.n 14) 3),
    .atom (.mul (.n 9849) (.n 9848) (.n 8632)),
    .atom (.add (.n 9850) (.n 9847) (.n 9849)),
    .atom (.load (.n 9851) (.n 14) 4),
    .atom (.mul (.n 9852) (.n 9851) (.n 8643)),
    .atom (.add (.n 9853) (.n 9850) (.n 9852)),
    .atom (.load (.n 9854) (.n 14) 5),
    .atom (.const (.n 9855) (word 0 0 0)),
    .atom (.mul (.n 9856) (.n 9854) (.n 9855)),
    .atom (.add (.n 9857) (.n 9853) (.n 9856)),
    .atom (.add (.n 9858) (.n 15) (.n 9857)),
    .atom (.mul (.n 9859) (.n 3719) (.n 9858)),
    .atom (.add (.n 9860) (.n 9833) (.n 9859))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8844, a8845, a8846, a8847, a8848, a8849, a8850, a8851, a8852, a8853, a8854, a8855, a8856, a8857,
    a8858, a8859, a8860, a8861, a8862, a8863, a8864, a8865, a8866, a8867, a8868, a8869, a8870, -⟩ := hs
  have e8844 := tb_loadHolds_unique a8844 (hw 0 (by norm_num))
  have e8850 := tb_loadHolds_unique a8850 (hw 1 (by norm_num))
  have e8855 := tb_loadHolds_unique a8855 (hw 2 (by norm_num))
  have e8858 := tb_loadHolds_unique a8858 (hw 3 (by norm_num))
  have e8861 := tb_loadHolds_unique a8861 (hw 4 (by norm_num))
  have e8864 := tb_loadHolds_unique a8864 (hw 5 (by norm_num))
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
  have hB : σ (.n 9858) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 8], 4)], [([74], 2)], [([34], 1)], [([35], 1)], [([], 0)]] := by
    simp only [v9202, v8643, v8632, v8255, v8165, a8868, a8867, a8866, a8865, e8864, a8863, a8862, e8861,
      a8860, a8859, e8858, a8857, a8856, e8855, a8854, a8853, a8852, a8851, e8850, a8849,
      a8848, a8847, a8846, a8845, e8844]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8870, a8869, hB]

set_option maxRecDepth 10000 in
theorem vtB05_14F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9887) = σ (.n 9860) + σ (.n 3738) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 8], 8)], [([75], 2)], [([36], 1)], [([37], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8871 [
    .atom (.load (.n 9861) (.n 14) 0),
    .atom (.const (.n 9862) (word 2 0 0)),
    .atom (.mul (.n 9863) (.n 9861) (.n 9862)),
    .atom (.const (.n 9864) (word 8 0 0)),
    .atom (.mul (.n 9865) (.n 8165) (.n 8255)),
    .atom (.mul (.n 9866) (.n 9864) (.n 9865)),
    .atom (.load (.n 9867) (.n 14) 1),
    .atom (.mul (.n 9868) (.n 9867) (.n 9866)),
    .atom (.add (.n 9869) (.n 9863) (.n 9868)),
    .atom (.const (.n 9870) (word 2 0 0)),
    .atom (.mul (.n 9871) (.n 9870) (.n 9213)),
    .atom (.load (.n 9872) (.n 14) 2),
    .atom (.mul (.n 9873) (.n 9872) (.n 9871)),
    .atom (.add (.n 9874) (.n 9869) (.n 9873)),
    .atom (.load (.n 9875) (.n 14) 3),
    .atom (.mul (.n 9876) (.n 9875) (.n 8654)),
    .atom (.add (.n 9877) (.n 9874) (.n 9876)),
    .atom (.load (.n 9878) (.n 14) 4),
    .atom (.mul (.n 9879) (.n 9878) (.n 8678)),
    .atom (.add (.n 9880) (.n 9877) (.n 9879)),
    .atom (.load (.n 9881) (.n 14) 5),
    .atom (.const (.n 9882) (word 0 0 0)),
    .atom (.mul (.n 9883) (.n 9881) (.n 9882)),
    .atom (.add (.n 9884) (.n 9880) (.n 9883)),
    .atom (.add (.n 9885) (.n 15) (.n 9884)),
    .atom (.mul (.n 9886) (.n 3738) (.n 9885)),
    .atom (.add (.n 9887) (.n 9860) (.n 9886))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8871, a8872, a8873, a8874, a8875, a8876, a8877, a8878, a8879, a8880, a8881, a8882, a8883, a8884,
    a8885, a8886, a8887, a8888, a8889, a8890, a8891, a8892, a8893, a8894, a8895, a8896, a8897, -⟩ := hs
  have e8871 := tb_loadHolds_unique a8871 (hw 0 (by norm_num))
  have e8877 := tb_loadHolds_unique a8877 (hw 1 (by norm_num))
  have e8882 := tb_loadHolds_unique a8882 (hw 2 (by norm_num))
  have e8885 := tb_loadHolds_unique a8885 (hw 3 (by norm_num))
  have e8888 := tb_loadHolds_unique a8888 (hw 4 (by norm_num))
  have e8891 := tb_loadHolds_unique a8891 (hw 5 (by norm_num))
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
  have hB : σ (.n 9885) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 8], 8)], [([75], 2)], [([36], 1)], [([37], 1)], [([], 0)]] := by
    simp only [v9213, v8678, v8654, v8255, v8165, a8895, a8894, a8893, a8892, e8891, a8890, a8889, e8888,
      a8887, a8886, e8885, a8884, a8883, e8882, a8881, a8880, a8879, a8878, e8877, a8876,
      a8875, a8874, a8873, a8872, e8871]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8897, a8896, hB]

set_option maxRecDepth 10000 in
theorem vtB05_15F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9918) = σ (.n 9887) + σ (.n 3757) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 1)], [([76], 2)], [([38], 1), ([11, 38], 1)], [([39], 1), ([11, 39], 1), ([11, 38], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8898 [
    .atom (.load (.n 9888) (.n 14) 0),
    .atom (.const (.n 9889) (word 2 0 0)),
    .atom (.mul (.n 9890) (.n 9888) (.n 9889)),
    .atom (.mul (.n 9891) (.n 8165) (.n 8279)),
    .atom (.load (.n 9892) (.n 14) 1),
    .atom (.mul (.n 9893) (.n 9892) (.n 9891)),
    .atom (.add (.n 9894) (.n 9890) (.n 9893)),
    .atom (.const (.n 9895) (word 2 0 0)),
    .atom (.mul (.n 9896) (.n 9895) (.n 9224)),
    .atom (.load (.n 9897) (.n 14) 2),
    .atom (.mul (.n 9898) (.n 9897) (.n 9896)),
    .atom (.add (.n 9899) (.n 9894) (.n 9898)),
    .atom (.mul (.n 9900) (.n 8301) (.n 8689)),
    .atom (.add (.n 9901) (.n 8689) (.n 9900)),
    .atom (.load (.n 9902) (.n 14) 3),
    .atom (.mul (.n 9903) (.n 9902) (.n 9901)),
    .atom (.add (.n 9904) (.n 9899) (.n 9903)),
    .atom (.mul (.n 9905) (.n 8301) (.n 8700)),
    .atom (.add (.n 9906) (.n 8700) (.n 9905)),
    .atom (.mul (.n 9907) (.n 8301) (.n 8689)),
    .atom (.add (.n 9908) (.n 9906) (.n 9907)),
    .atom (.load (.n 9909) (.n 14) 4),
    .atom (.mul (.n 9910) (.n 9909) (.n 9908)),
    .atom (.add (.n 9911) (.n 9904) (.n 9910)),
    .atom (.load (.n 9912) (.n 14) 5),
    .atom (.const (.n 9913) (word 0 0 0)),
    .atom (.mul (.n 9914) (.n 9912) (.n 9913)),
    .atom (.add (.n 9915) (.n 9911) (.n 9914)),
    .atom (.add (.n 9916) (.n 15) (.n 9915)),
    .atom (.mul (.n 9917) (.n 3757) (.n 9916)),
    .atom (.add (.n 9918) (.n 9887) (.n 9917))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8898, a8899, a8900, a8901, a8902, a8903, a8904, a8905, a8906, a8907, a8908, a8909, a8910, a8911,
    a8912, a8913, a8914, a8915, a8916, a8917, a8918, a8919, a8920, a8921, a8922, a8923, a8924,
    a8925, a8926, a8927, a8928, -⟩ := hs
  have e8898 := tb_loadHolds_unique a8898 (hw 0 (by norm_num))
  have e8902 := tb_loadHolds_unique a8902 (hw 1 (by norm_num))
  have e8907 := tb_loadHolds_unique a8907 (hw 2 (by norm_num))
  have e8912 := tb_loadHolds_unique a8912 (hw 3 (by norm_num))
  have e8919 := tb_loadHolds_unique a8919 (hw 4 (by norm_num))
  have e8922 := tb_loadHolds_unique a8922 (hw 5 (by norm_num))
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
  have hB : σ (.n 9916) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 1)], [([76], 2)], [([38], 1), ([11, 38], 1)], [([39], 1), ([11, 39], 1), ([11, 38], 1)], [([], 0)]] := by
    simp only [v9224, v8700, v8689, v8301, v8279, v8165, a8926, a8925, a8924, a8923, e8922, a8921, a8920,
      e8919, a8918, a8917, a8916, a8915, a8914, a8913, e8912, a8911, a8910, a8909, a8908,
      e8907, a8906, a8905, a8904, a8903, e8902, a8901, a8900, a8899, e8898]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8928, a8927, hB]

set_option maxRecDepth 10000 in
theorem vtB05_16F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9953) = σ (.n 9918) + σ (.n 3776) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 2)], [([77], 2)], [([40], 1), ([11, 40], 1), ([11, 39], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8929 [
    .atom (.load (.n 9919) (.n 14) 0),
    .atom (.const (.n 9920) (word 2 0 0)),
    .atom (.mul (.n 9921) (.n 9919) (.n 9920)),
    .atom (.const (.n 9922) (word 2 0 0)),
    .atom (.mul (.n 9923) (.n 8165) (.n 8279)),
    .atom (.mul (.n 9924) (.n 9922) (.n 9923)),
    .atom (.load (.n 9925) (.n 14) 1),
    .atom (.mul (.n 9926) (.n 9925) (.n 9924)),
    .atom (.add (.n 9927) (.n 9921) (.n 9926)),
    .atom (.const (.n 9928) (word 2 0 0)),
    .atom (.mul (.n 9929) (.n 9928) (.n 9248)),
    .atom (.load (.n 9930) (.n 14) 2),
    .atom (.mul (.n 9931) (.n 9930) (.n 9929)),
    .atom (.add (.n 9932) (.n 9927) (.n 9931)),
    .atom (.mul (.n 9933) (.n 8301) (.n 8711)),
    .atom (.add (.n 9934) (.n 8711) (.n 9933)),
    .atom (.mul (.n 9935) (.n 8301) (.n 8700)),
    .atom (.add (.n 9936) (.n 9934) (.n 9935)),
    .atom (.load (.n 9937) (.n 14) 3),
    .atom (.mul (.n 9938) (.n 9937) (.n 9936)),
    .atom (.add (.n 9939) (.n 9932) (.n 9938)),
    .atom (.mul (.n 9940) (.n 8301) (.n 8735)),
    .atom (.add (.n 9941) (.n 8735) (.n 9940)),
    .atom (.mul (.n 9942) (.n 8301) (.n 8711)),
    .atom (.add (.n 9943) (.n 9941) (.n 9942)),
    .atom (.load (.n 9944) (.n 14) 4),
    .atom (.mul (.n 9945) (.n 9944) (.n 9943)),
    .atom (.add (.n 9946) (.n 9939) (.n 9945)),
    .atom (.load (.n 9947) (.n 14) 5),
    .atom (.const (.n 9948) (word 0 0 0)),
    .atom (.mul (.n 9949) (.n 9947) (.n 9948)),
    .atom (.add (.n 9950) (.n 9946) (.n 9949)),
    .atom (.add (.n 9951) (.n 15) (.n 9950)),
    .atom (.mul (.n 9952) (.n 3776) (.n 9951)),
    .atom (.add (.n 9953) (.n 9918) (.n 9952))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8929, a8930, a8931, a8932, a8933, a8934, a8935, a8936, a8937, a8938, a8939, a8940, a8941, a8942,
    a8943, a8944, a8945, a8946, a8947, a8948, a8949, a8950, a8951, a8952, a8953, a8954, a8955,
    a8956, a8957, a8958, a8959, a8960, a8961, a8962, a8963, -⟩ := hs
  have e8929 := tb_loadHolds_unique a8929 (hw 0 (by norm_num))
  have e8935 := tb_loadHolds_unique a8935 (hw 1 (by norm_num))
  have e8940 := tb_loadHolds_unique a8940 (hw 2 (by norm_num))
  have e8947 := tb_loadHolds_unique a8947 (hw 3 (by norm_num))
  have e8954 := tb_loadHolds_unique a8954 (hw 4 (by norm_num))
  have e8957 := tb_loadHolds_unique a8957 (hw 5 (by norm_num))
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
  have hB : σ (.n 9951) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 2)], [([77], 2)], [([40], 1), ([11, 40], 1), ([11, 39], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)], [([], 0)]] := by
    simp only [v9248, v8735, v8711, v8700, v8301, v8279, v8165, a8961, a8960, a8959, a8958, e8957, a8956,
      a8955, e8954, a8953, a8952, a8951, a8950, a8949, a8948, e8947, a8946, a8945, a8944,
      a8943, a8942, a8941, e8940, a8939, a8938, a8937, a8936, e8935, a8934, a8933, a8932,
      a8931, a8930, e8929]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8963, a8962, hB]

set_option maxRecDepth 10000 in
theorem vtB05_17F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 9988) = σ (.n 9953) + σ (.n 3795) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 4)], [([78], 2)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8964 [
    .atom (.load (.n 9954) (.n 14) 0),
    .atom (.const (.n 9955) (word 2 0 0)),
    .atom (.mul (.n 9956) (.n 9954) (.n 9955)),
    .atom (.const (.n 9957) (word 4 0 0)),
    .atom (.mul (.n 9958) (.n 8165) (.n 8279)),
    .atom (.mul (.n 9959) (.n 9957) (.n 9958)),
    .atom (.load (.n 9960) (.n 14) 1),
    .atom (.mul (.n 9961) (.n 9960) (.n 9959)),
    .atom (.add (.n 9962) (.n 9956) (.n 9961)),
    .atom (.const (.n 9963) (word 2 0 0)),
    .atom (.mul (.n 9964) (.n 9963) (.n 9259)),
    .atom (.load (.n 9965) (.n 14) 2),
    .atom (.mul (.n 9966) (.n 9965) (.n 9964)),
    .atom (.add (.n 9967) (.n 9962) (.n 9966)),
    .atom (.mul (.n 9968) (.n 8301) (.n 8746)),
    .atom (.add (.n 9969) (.n 8746) (.n 9968)),
    .atom (.mul (.n 9970) (.n 8301) (.n 8735)),
    .atom (.add (.n 9971) (.n 9969) (.n 9970)),
    .atom (.load (.n 9972) (.n 14) 3),
    .atom (.mul (.n 9973) (.n 9972) (.n 9971)),
    .atom (.add (.n 9974) (.n 9967) (.n 9973)),
    .atom (.mul (.n 9975) (.n 8301) (.n 8757)),
    .atom (.add (.n 9976) (.n 8757) (.n 9975)),
    .atom (.mul (.n 9977) (.n 8301) (.n 8746)),
    .atom (.add (.n 9978) (.n 9976) (.n 9977)),
    .atom (.load (.n 9979) (.n 14) 4),
    .atom (.mul (.n 9980) (.n 9979) (.n 9978)),
    .atom (.add (.n 9981) (.n 9974) (.n 9980)),
    .atom (.load (.n 9982) (.n 14) 5),
    .atom (.const (.n 9983) (word 0 0 0)),
    .atom (.mul (.n 9984) (.n 9982) (.n 9983)),
    .atom (.add (.n 9985) (.n 9981) (.n 9984)),
    .atom (.add (.n 9986) (.n 15) (.n 9985)),
    .atom (.mul (.n 9987) (.n 3795) (.n 9986)),
    .atom (.add (.n 9988) (.n 9953) (.n 9987))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8964, a8965, a8966, a8967, a8968, a8969, a8970, a8971, a8972, a8973, a8974, a8975, a8976, a8977,
    a8978, a8979, a8980, a8981, a8982, a8983, a8984, a8985, a8986, a8987, a8988, a8989, a8990,
    a8991, a8992, a8993, a8994, a8995, a8996, a8997, a8998, -⟩ := hs
  have e8964 := tb_loadHolds_unique a8964 (hw 0 (by norm_num))
  have e8970 := tb_loadHolds_unique a8970 (hw 1 (by norm_num))
  have e8975 := tb_loadHolds_unique a8975 (hw 2 (by norm_num))
  have e8982 := tb_loadHolds_unique a8982 (hw 3 (by norm_num))
  have e8989 := tb_loadHolds_unique a8989 (hw 4 (by norm_num))
  have e8992 := tb_loadHolds_unique a8992 (hw 5 (by norm_num))
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
  have hB : σ (.n 9986) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 4)], [([78], 2)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)], [([], 0)]] := by
    simp only [v9259, v8757, v8746, v8735, v8301, v8279, v8165, a8996, a8995, a8994, a8993, e8992, a8991,
      a8990, e8989, a8988, a8987, a8986, a8985, a8984, a8983, e8982, a8981, a8980, a8979,
      a8978, a8977, a8976, e8975, a8974, a8973, a8972, a8971, e8970, a8969, a8968, a8967,
      a8966, a8965, e8964]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a8998, a8997, hB]

set_option maxRecDepth 10000 in
theorem vtB05_18F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10023) = σ (.n 9988) + σ (.n 3814) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 8)], [([79], 2)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 8999 [
    .atom (.load (.n 9989) (.n 14) 0),
    .atom (.const (.n 9990) (word 2 0 0)),
    .atom (.mul (.n 9991) (.n 9989) (.n 9990)),
    .atom (.const (.n 9992) (word 8 0 0)),
    .atom (.mul (.n 9993) (.n 8165) (.n 8279)),
    .atom (.mul (.n 9994) (.n 9992) (.n 9993)),
    .atom (.load (.n 9995) (.n 14) 1),
    .atom (.mul (.n 9996) (.n 9995) (.n 9994)),
    .atom (.add (.n 9997) (.n 9991) (.n 9996)),
    .atom (.const (.n 9998) (word 2 0 0)),
    .atom (.mul (.n 9999) (.n 9998) (.n 9270)),
    .atom (.load (.n 10000) (.n 14) 2),
    .atom (.mul (.n 10001) (.n 10000) (.n 9999)),
    .atom (.add (.n 10002) (.n 9997) (.n 10001)),
    .atom (.mul (.n 10003) (.n 8301) (.n 8768)),
    .atom (.add (.n 10004) (.n 8768) (.n 10003)),
    .atom (.mul (.n 10005) (.n 8301) (.n 8757)),
    .atom (.add (.n 10006) (.n 10004) (.n 10005)),
    .atom (.load (.n 10007) (.n 14) 3),
    .atom (.mul (.n 10008) (.n 10007) (.n 10006)),
    .atom (.add (.n 10009) (.n 10002) (.n 10008)),
    .atom (.mul (.n 10010) (.n 8301) (.n 8792)),
    .atom (.add (.n 10011) (.n 8792) (.n 10010)),
    .atom (.mul (.n 10012) (.n 8301) (.n 8768)),
    .atom (.add (.n 10013) (.n 10011) (.n 10012)),
    .atom (.load (.n 10014) (.n 14) 4),
    .atom (.mul (.n 10015) (.n 10014) (.n 10013)),
    .atom (.add (.n 10016) (.n 10009) (.n 10015)),
    .atom (.load (.n 10017) (.n 14) 5),
    .atom (.const (.n 10018) (word 0 0 0)),
    .atom (.mul (.n 10019) (.n 10017) (.n 10018)),
    .atom (.add (.n 10020) (.n 10016) (.n 10019)),
    .atom (.add (.n 10021) (.n 15) (.n 10020)),
    .atom (.mul (.n 10022) (.n 3814) (.n 10021)),
    .atom (.add (.n 10023) (.n 9988) (.n 10022))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a8999, a9000, a9001, a9002, a9003, a9004, a9005, a9006, a9007, a9008, a9009, a9010, a9011, a9012,
    a9013, a9014, a9015, a9016, a9017, a9018, a9019, a9020, a9021, a9022, a9023, a9024, a9025,
    a9026, a9027, a9028, a9029, a9030, a9031, a9032, a9033, -⟩ := hs
  have e8999 := tb_loadHolds_unique a8999 (hw 0 (by norm_num))
  have e9005 := tb_loadHolds_unique a9005 (hw 1 (by norm_num))
  have e9010 := tb_loadHolds_unique a9010 (hw 2 (by norm_num))
  have e9017 := tb_loadHolds_unique a9017 (hw 3 (by norm_num))
  have e9024 := tb_loadHolds_unique a9024 (hw 4 (by norm_num))
  have e9027 := tb_loadHolds_unique a9027 (hw 5 (by norm_num))
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
  have hB : σ (.n 10021) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 8)], [([79], 2)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)], [([], 0)]] := by
    simp only [v9270, v8792, v8768, v8757, v8301, v8279, v8165, a9031, a9030, a9029, a9028, e9027, a9026,
      a9025, e9024, a9023, a9022, a9021, a9020, a9019, a9018, e9017, a9016, a9015, a9014,
      a9013, a9012, a9011, e9010, a9009, a9008, a9007, a9006, e9005, a9004, a9003, a9002,
      a9001, a9000, e8999]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9033, a9032, hB]

set_option maxRecDepth 10000 in
theorem vtB05_19F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10058) = σ (.n 10023) + σ (.n 3833) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 16)], [([80], 2)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9034 [
    .atom (.load (.n 10024) (.n 14) 0),
    .atom (.const (.n 10025) (word 2 0 0)),
    .atom (.mul (.n 10026) (.n 10024) (.n 10025)),
    .atom (.const (.n 10027) (word 16 0 0)),
    .atom (.mul (.n 10028) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10029) (.n 10027) (.n 10028)),
    .atom (.load (.n 10030) (.n 14) 1),
    .atom (.mul (.n 10031) (.n 10030) (.n 10029)),
    .atom (.add (.n 10032) (.n 10026) (.n 10031)),
    .atom (.const (.n 10033) (word 2 0 0)),
    .atom (.mul (.n 10034) (.n 10033) (.n 9281)),
    .atom (.load (.n 10035) (.n 14) 2),
    .atom (.mul (.n 10036) (.n 10035) (.n 10034)),
    .atom (.add (.n 10037) (.n 10032) (.n 10036)),
    .atom (.mul (.n 10038) (.n 8301) (.n 8803)),
    .atom (.add (.n 10039) (.n 8803) (.n 10038)),
    .atom (.mul (.n 10040) (.n 8301) (.n 8792)),
    .atom (.add (.n 10041) (.n 10039) (.n 10040)),
    .atom (.load (.n 10042) (.n 14) 3),
    .atom (.mul (.n 10043) (.n 10042) (.n 10041)),
    .atom (.add (.n 10044) (.n 10037) (.n 10043)),
    .atom (.mul (.n 10045) (.n 8301) (.n 8814)),
    .atom (.add (.n 10046) (.n 8814) (.n 10045)),
    .atom (.mul (.n 10047) (.n 8301) (.n 8803)),
    .atom (.add (.n 10048) (.n 10046) (.n 10047)),
    .atom (.load (.n 10049) (.n 14) 4),
    .atom (.mul (.n 10050) (.n 10049) (.n 10048)),
    .atom (.add (.n 10051) (.n 10044) (.n 10050)),
    .atom (.load (.n 10052) (.n 14) 5),
    .atom (.const (.n 10053) (word 0 0 0)),
    .atom (.mul (.n 10054) (.n 10052) (.n 10053)),
    .atom (.add (.n 10055) (.n 10051) (.n 10054)),
    .atom (.add (.n 10056) (.n 15) (.n 10055)),
    .atom (.mul (.n 10057) (.n 3833) (.n 10056)),
    .atom (.add (.n 10058) (.n 10023) (.n 10057))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9034, a9035, a9036, a9037, a9038, a9039, a9040, a9041, a9042, a9043, a9044, a9045, a9046, a9047,
    a9048, a9049, a9050, a9051, a9052, a9053, a9054, a9055, a9056, a9057, a9058, a9059, a9060,
    a9061, a9062, a9063, a9064, a9065, a9066, a9067, a9068, -⟩ := hs
  have e9034 := tb_loadHolds_unique a9034 (hw 0 (by norm_num))
  have e9040 := tb_loadHolds_unique a9040 (hw 1 (by norm_num))
  have e9045 := tb_loadHolds_unique a9045 (hw 2 (by norm_num))
  have e9052 := tb_loadHolds_unique a9052 (hw 3 (by norm_num))
  have e9059 := tb_loadHolds_unique a9059 (hw 4 (by norm_num))
  have e9062 := tb_loadHolds_unique a9062 (hw 5 (by norm_num))
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
  have hB : σ (.n 10056) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 16)], [([80], 2)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)], [([], 0)]] := by
    simp only [v9281, v8814, v8803, v8792, v8301, v8279, v8165, a9066, a9065, a9064, a9063, e9062, a9061,
      a9060, e9059, a9058, a9057, a9056, a9055, a9054, a9053, e9052, a9051, a9050, a9049,
      a9048, a9047, a9046, e9045, a9044, a9043, a9042, a9041, e9040, a9039, a9038, a9037,
      a9036, a9035, e9034]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9068, a9067, hB]

set_option maxRecDepth 10000 in
theorem vtB05_20F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10093) = σ (.n 10058) + σ (.n 3852) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 32)], [([81], 2)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9069 [
    .atom (.load (.n 10059) (.n 14) 0),
    .atom (.const (.n 10060) (word 2 0 0)),
    .atom (.mul (.n 10061) (.n 10059) (.n 10060)),
    .atom (.const (.n 10062) (word 32 0 0)),
    .atom (.mul (.n 10063) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10064) (.n 10062) (.n 10063)),
    .atom (.load (.n 10065) (.n 14) 1),
    .atom (.mul (.n 10066) (.n 10065) (.n 10064)),
    .atom (.add (.n 10067) (.n 10061) (.n 10066)),
    .atom (.const (.n 10068) (word 2 0 0)),
    .atom (.mul (.n 10069) (.n 10068) (.n 9305)),
    .atom (.load (.n 10070) (.n 14) 2),
    .atom (.mul (.n 10071) (.n 10070) (.n 10069)),
    .atom (.add (.n 10072) (.n 10067) (.n 10071)),
    .atom (.mul (.n 10073) (.n 8301) (.n 8825)),
    .atom (.add (.n 10074) (.n 8825) (.n 10073)),
    .atom (.mul (.n 10075) (.n 8301) (.n 8814)),
    .atom (.add (.n 10076) (.n 10074) (.n 10075)),
    .atom (.load (.n 10077) (.n 14) 3),
    .atom (.mul (.n 10078) (.n 10077) (.n 10076)),
    .atom (.add (.n 10079) (.n 10072) (.n 10078)),
    .atom (.mul (.n 10080) (.n 8301) (.n 8849)),
    .atom (.add (.n 10081) (.n 8849) (.n 10080)),
    .atom (.mul (.n 10082) (.n 8301) (.n 8825)),
    .atom (.add (.n 10083) (.n 10081) (.n 10082)),
    .atom (.load (.n 10084) (.n 14) 4),
    .atom (.mul (.n 10085) (.n 10084) (.n 10083)),
    .atom (.add (.n 10086) (.n 10079) (.n 10085)),
    .atom (.load (.n 10087) (.n 14) 5),
    .atom (.const (.n 10088) (word 0 0 0)),
    .atom (.mul (.n 10089) (.n 10087) (.n 10088)),
    .atom (.add (.n 10090) (.n 10086) (.n 10089)),
    .atom (.add (.n 10091) (.n 15) (.n 10090)),
    .atom (.mul (.n 10092) (.n 3852) (.n 10091)),
    .atom (.add (.n 10093) (.n 10058) (.n 10092))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9069, a9070, a9071, a9072, a9073, a9074, a9075, a9076, a9077, a9078, a9079, a9080, a9081, a9082,
    a9083, a9084, a9085, a9086, a9087, a9088, a9089, a9090, a9091, a9092, a9093, a9094, a9095,
    a9096, a9097, a9098, a9099, a9100, a9101, a9102, a9103, -⟩ := hs
  have e9069 := tb_loadHolds_unique a9069 (hw 0 (by norm_num))
  have e9075 := tb_loadHolds_unique a9075 (hw 1 (by norm_num))
  have e9080 := tb_loadHolds_unique a9080 (hw 2 (by norm_num))
  have e9087 := tb_loadHolds_unique a9087 (hw 3 (by norm_num))
  have e9094 := tb_loadHolds_unique a9094 (hw 4 (by norm_num))
  have e9097 := tb_loadHolds_unique a9097 (hw 5 (by norm_num))
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
  have hB : σ (.n 10091) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 32)], [([81], 2)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)], [([], 0)]] := by
    simp only [v9305, v8849, v8825, v8814, v8301, v8279, v8165, a9101, a9100, a9099, a9098, e9097, a9096,
      a9095, e9094, a9093, a9092, a9091, a9090, a9089, a9088, e9087, a9086, a9085, a9084,
      a9083, a9082, a9081, e9080, a9079, a9078, a9077, a9076, e9075, a9074, a9073, a9072,
      a9071, a9070, e9069]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9103, a9102, hB]

set_option maxRecDepth 10000 in
theorem vtB05_21F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10128) = σ (.n 10093) + σ (.n 3871) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 64)], [([82], 2)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9104 [
    .atom (.load (.n 10094) (.n 14) 0),
    .atom (.const (.n 10095) (word 2 0 0)),
    .atom (.mul (.n 10096) (.n 10094) (.n 10095)),
    .atom (.const (.n 10097) (word 64 0 0)),
    .atom (.mul (.n 10098) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10099) (.n 10097) (.n 10098)),
    .atom (.load (.n 10100) (.n 14) 1),
    .atom (.mul (.n 10101) (.n 10100) (.n 10099)),
    .atom (.add (.n 10102) (.n 10096) (.n 10101)),
    .atom (.const (.n 10103) (word 2 0 0)),
    .atom (.mul (.n 10104) (.n 10103) (.n 9316)),
    .atom (.load (.n 10105) (.n 14) 2),
    .atom (.mul (.n 10106) (.n 10105) (.n 10104)),
    .atom (.add (.n 10107) (.n 10102) (.n 10106)),
    .atom (.mul (.n 10108) (.n 8301) (.n 8860)),
    .atom (.add (.n 10109) (.n 8860) (.n 10108)),
    .atom (.mul (.n 10110) (.n 8301) (.n 8849)),
    .atom (.add (.n 10111) (.n 10109) (.n 10110)),
    .atom (.load (.n 10112) (.n 14) 3),
    .atom (.mul (.n 10113) (.n 10112) (.n 10111)),
    .atom (.add (.n 10114) (.n 10107) (.n 10113)),
    .atom (.mul (.n 10115) (.n 8301) (.n 8871)),
    .atom (.add (.n 10116) (.n 8871) (.n 10115)),
    .atom (.mul (.n 10117) (.n 8301) (.n 8860)),
    .atom (.add (.n 10118) (.n 10116) (.n 10117)),
    .atom (.load (.n 10119) (.n 14) 4),
    .atom (.mul (.n 10120) (.n 10119) (.n 10118)),
    .atom (.add (.n 10121) (.n 10114) (.n 10120)),
    .atom (.load (.n 10122) (.n 14) 5),
    .atom (.const (.n 10123) (word 0 0 0)),
    .atom (.mul (.n 10124) (.n 10122) (.n 10123)),
    .atom (.add (.n 10125) (.n 10121) (.n 10124)),
    .atom (.add (.n 10126) (.n 15) (.n 10125)),
    .atom (.mul (.n 10127) (.n 3871) (.n 10126)),
    .atom (.add (.n 10128) (.n 10093) (.n 10127))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9104, a9105, a9106, a9107, a9108, a9109, a9110, a9111, a9112, a9113, a9114, a9115, a9116, a9117,
    a9118, a9119, a9120, a9121, a9122, a9123, a9124, a9125, a9126, a9127, a9128, a9129, a9130,
    a9131, a9132, a9133, a9134, a9135, a9136, a9137, a9138, -⟩ := hs
  have e9104 := tb_loadHolds_unique a9104 (hw 0 (by norm_num))
  have e9110 := tb_loadHolds_unique a9110 (hw 1 (by norm_num))
  have e9115 := tb_loadHolds_unique a9115 (hw 2 (by norm_num))
  have e9122 := tb_loadHolds_unique a9122 (hw 3 (by norm_num))
  have e9129 := tb_loadHolds_unique a9129 (hw 4 (by norm_num))
  have e9132 := tb_loadHolds_unique a9132 (hw 5 (by norm_num))
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
  have hB : σ (.n 10126) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 64)], [([82], 2)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)], [([], 0)]] := by
    simp only [v9316, v8871, v8860, v8849, v8301, v8279, v8165, a9136, a9135, a9134, a9133, e9132, a9131,
      a9130, e9129, a9128, a9127, a9126, a9125, a9124, a9123, e9122, a9121, a9120, a9119,
      a9118, a9117, a9116, e9115, a9114, a9113, a9112, a9111, e9110, a9109, a9108, a9107,
      a9106, a9105, e9104]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9138, a9137, hB]

set_option maxRecDepth 10000 in
theorem vtB05_22F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10163) = σ (.n 10128) + σ (.n 3890) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 128)], [([83], 2)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9139 [
    .atom (.load (.n 10129) (.n 14) 0),
    .atom (.const (.n 10130) (word 2 0 0)),
    .atom (.mul (.n 10131) (.n 10129) (.n 10130)),
    .atom (.const (.n 10132) (word 128 0 0)),
    .atom (.mul (.n 10133) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10134) (.n 10132) (.n 10133)),
    .atom (.load (.n 10135) (.n 14) 1),
    .atom (.mul (.n 10136) (.n 10135) (.n 10134)),
    .atom (.add (.n 10137) (.n 10131) (.n 10136)),
    .atom (.const (.n 10138) (word 2 0 0)),
    .atom (.mul (.n 10139) (.n 10138) (.n 9327)),
    .atom (.load (.n 10140) (.n 14) 2),
    .atom (.mul (.n 10141) (.n 10140) (.n 10139)),
    .atom (.add (.n 10142) (.n 10137) (.n 10141)),
    .atom (.mul (.n 10143) (.n 8301) (.n 8882)),
    .atom (.add (.n 10144) (.n 8882) (.n 10143)),
    .atom (.mul (.n 10145) (.n 8301) (.n 8871)),
    .atom (.add (.n 10146) (.n 10144) (.n 10145)),
    .atom (.load (.n 10147) (.n 14) 3),
    .atom (.mul (.n 10148) (.n 10147) (.n 10146)),
    .atom (.add (.n 10149) (.n 10142) (.n 10148)),
    .atom (.mul (.n 10150) (.n 8301) (.n 8906)),
    .atom (.add (.n 10151) (.n 8906) (.n 10150)),
    .atom (.mul (.n 10152) (.n 8301) (.n 8882)),
    .atom (.add (.n 10153) (.n 10151) (.n 10152)),
    .atom (.load (.n 10154) (.n 14) 4),
    .atom (.mul (.n 10155) (.n 10154) (.n 10153)),
    .atom (.add (.n 10156) (.n 10149) (.n 10155)),
    .atom (.load (.n 10157) (.n 14) 5),
    .atom (.const (.n 10158) (word 0 0 0)),
    .atom (.mul (.n 10159) (.n 10157) (.n 10158)),
    .atom (.add (.n 10160) (.n 10156) (.n 10159)),
    .atom (.add (.n 10161) (.n 15) (.n 10160)),
    .atom (.mul (.n 10162) (.n 3890) (.n 10161)),
    .atom (.add (.n 10163) (.n 10128) (.n 10162))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9139, a9140, a9141, a9142, a9143, a9144, a9145, a9146, a9147, a9148, a9149, a9150, a9151, a9152,
    a9153, a9154, a9155, a9156, a9157, a9158, a9159, a9160, a9161, a9162, a9163, a9164, a9165,
    a9166, a9167, a9168, a9169, a9170, a9171, a9172, a9173, -⟩ := hs
  have e9139 := tb_loadHolds_unique a9139 (hw 0 (by norm_num))
  have e9145 := tb_loadHolds_unique a9145 (hw 1 (by norm_num))
  have e9150 := tb_loadHolds_unique a9150 (hw 2 (by norm_num))
  have e9157 := tb_loadHolds_unique a9157 (hw 3 (by norm_num))
  have e9164 := tb_loadHolds_unique a9164 (hw 4 (by norm_num))
  have e9167 := tb_loadHolds_unique a9167 (hw 5 (by norm_num))
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
  have hB : σ (.n 10161) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 128)], [([83], 2)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)], [([], 0)]] := by
    simp only [v9327, v8906, v8882, v8871, v8301, v8279, v8165, a9171, a9170, a9169, a9168, e9167, a9166,
      a9165, e9164, a9163, a9162, a9161, a9160, a9159, a9158, e9157, a9156, a9155, a9154,
      a9153, a9152, a9151, e9150, a9149, a9148, a9147, a9146, e9145, a9144, a9143, a9142,
      a9141, a9140, e9139]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9173, a9172, hB]

set_option maxRecDepth 10000 in
theorem vtB05_23F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10195) = σ (.n 10163) + σ (.n 3909) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 256)], [([84], 2)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([11, 54], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9174 [
    .atom (.load (.n 10164) (.n 14) 0),
    .atom (.const (.n 10165) (word 2 0 0)),
    .atom (.mul (.n 10166) (.n 10164) (.n 10165)),
    .atom (.const (.n 10167) (word 256 0 0)),
    .atom (.mul (.n 10168) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10169) (.n 10167) (.n 10168)),
    .atom (.load (.n 10170) (.n 14) 1),
    .atom (.mul (.n 10171) (.n 10170) (.n 10169)),
    .atom (.add (.n 10172) (.n 10166) (.n 10171)),
    .atom (.const (.n 10173) (word 2 0 0)),
    .atom (.mul (.n 10174) (.n 10173) (.n 9338)),
    .atom (.load (.n 10175) (.n 14) 2),
    .atom (.mul (.n 10176) (.n 10175) (.n 10174)),
    .atom (.add (.n 10177) (.n 10172) (.n 10176)),
    .atom (.mul (.n 10178) (.n 8301) (.n 8917)),
    .atom (.add (.n 10179) (.n 8917) (.n 10178)),
    .atom (.mul (.n 10180) (.n 8301) (.n 8906)),
    .atom (.add (.n 10181) (.n 10179) (.n 10180)),
    .atom (.load (.n 10182) (.n 14) 3),
    .atom (.mul (.n 10183) (.n 10182) (.n 10181)),
    .atom (.add (.n 10184) (.n 10177) (.n 10183)),
    .atom (.mul (.n 10185) (.n 8301) (.n 8917)),
    .atom (.load (.n 10186) (.n 14) 4),
    .atom (.mul (.n 10187) (.n 10186) (.n 10185)),
    .atom (.add (.n 10188) (.n 10184) (.n 10187)),
    .atom (.load (.n 10189) (.n 14) 5),
    .atom (.const (.n 10190) (word 0 0 0)),
    .atom (.mul (.n 10191) (.n 10189) (.n 10190)),
    .atom (.add (.n 10192) (.n 10188) (.n 10191)),
    .atom (.add (.n 10193) (.n 15) (.n 10192)),
    .atom (.mul (.n 10194) (.n 3909) (.n 10193)),
    .atom (.add (.n 10195) (.n 10163) (.n 10194))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9174, a9175, a9176, a9177, a9178, a9179, a9180, a9181, a9182, a9183, a9184, a9185, a9186, a9187,
    a9188, a9189, a9190, a9191, a9192, a9193, a9194, a9195, a9196, a9197, a9198, a9199, a9200,
    a9201, a9202, a9203, a9204, a9205, -⟩ := hs
  have e9174 := tb_loadHolds_unique a9174 (hw 0 (by norm_num))
  have e9180 := tb_loadHolds_unique a9180 (hw 1 (by norm_num))
  have e9185 := tb_loadHolds_unique a9185 (hw 2 (by norm_num))
  have e9192 := tb_loadHolds_unique a9192 (hw 3 (by norm_num))
  have e9196 := tb_loadHolds_unique a9196 (hw 4 (by norm_num))
  have e9199 := tb_loadHolds_unique a9199 (hw 5 (by norm_num))
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
  have hB : σ (.n 10193) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 256)], [([84], 2)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([11, 54], 1)], [([], 0)]] := by
    simp only [v9338, v8917, v8906, v8301, v8279, v8165, a9203, a9202, a9201, a9200, e9199, a9198, a9197,
      e9196, a9195, a9194, a9193, e9192, a9191, a9190, a9189, a9188, a9187, a9186, e9185,
      a9184, a9183, a9182, a9181, e9180, a9179, a9178, a9177, a9176, a9175, e9174]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9205, a9204, hB]

set_option maxRecDepth 10000 in
theorem vtB05_24F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10222) = σ (.n 10195) + σ (.n 3928) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 512)], [([85], 2)], [([55], 1)], [([56], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9206 [
    .atom (.load (.n 10196) (.n 14) 0),
    .atom (.const (.n 10197) (word 2 0 0)),
    .atom (.mul (.n 10198) (.n 10196) (.n 10197)),
    .atom (.const (.n 10199) (word 512 0 0)),
    .atom (.mul (.n 10200) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10201) (.n 10199) (.n 10200)),
    .atom (.load (.n 10202) (.n 14) 1),
    .atom (.mul (.n 10203) (.n 10202) (.n 10201)),
    .atom (.add (.n 10204) (.n 10198) (.n 10203)),
    .atom (.const (.n 10205) (word 2 0 0)),
    .atom (.mul (.n 10206) (.n 10205) (.n 9362)),
    .atom (.load (.n 10207) (.n 14) 2),
    .atom (.mul (.n 10208) (.n 10207) (.n 10206)),
    .atom (.add (.n 10209) (.n 10204) (.n 10208)),
    .atom (.load (.n 10210) (.n 14) 3),
    .atom (.mul (.n 10211) (.n 10210) (.n 8928)),
    .atom (.add (.n 10212) (.n 10209) (.n 10211)),
    .atom (.load (.n 10213) (.n 14) 4),
    .atom (.mul (.n 10214) (.n 10213) (.n 8939)),
    .atom (.add (.n 10215) (.n 10212) (.n 10214)),
    .atom (.load (.n 10216) (.n 14) 5),
    .atom (.const (.n 10217) (word 0 0 0)),
    .atom (.mul (.n 10218) (.n 10216) (.n 10217)),
    .atom (.add (.n 10219) (.n 10215) (.n 10218)),
    .atom (.add (.n 10220) (.n 15) (.n 10219)),
    .atom (.mul (.n 10221) (.n 3928) (.n 10220)),
    .atom (.add (.n 10222) (.n 10195) (.n 10221))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9206, a9207, a9208, a9209, a9210, a9211, a9212, a9213, a9214, a9215, a9216, a9217, a9218, a9219,
    a9220, a9221, a9222, a9223, a9224, a9225, a9226, a9227, a9228, a9229, a9230, a9231, a9232, -⟩ := hs
  have e9206 := tb_loadHolds_unique a9206 (hw 0 (by norm_num))
  have e9212 := tb_loadHolds_unique a9212 (hw 1 (by norm_num))
  have e9217 := tb_loadHolds_unique a9217 (hw 2 (by norm_num))
  have e9220 := tb_loadHolds_unique a9220 (hw 3 (by norm_num))
  have e9223 := tb_loadHolds_unique a9223 (hw 4 (by norm_num))
  have e9226 := tb_loadHolds_unique a9226 (hw 5 (by norm_num))
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
  have hB : σ (.n 10220) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 512)], [([85], 2)], [([55], 1)], [([56], 1)], [([], 0)]] := by
    simp only [v9362, v8939, v8928, v8279, v8165, a9230, a9229, a9228, a9227, e9226, a9225, a9224, e9223,
      a9222, a9221, e9220, a9219, a9218, e9217, a9216, a9215, a9214, a9213, e9212, a9211,
      a9210, a9209, a9208, a9207, e9206]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9232, a9231, hB]

set_option maxRecDepth 10000 in
theorem vtB05_25F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10249) = σ (.n 10222) + σ (.n 3947) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 1024)], [([86], 2)], [([57], 1)], [([58], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9233 [
    .atom (.load (.n 10223) (.n 14) 0),
    .atom (.const (.n 10224) (word 2 0 0)),
    .atom (.mul (.n 10225) (.n 10223) (.n 10224)),
    .atom (.const (.n 10226) (word 1024 0 0)),
    .atom (.mul (.n 10227) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10228) (.n 10226) (.n 10227)),
    .atom (.load (.n 10229) (.n 14) 1),
    .atom (.mul (.n 10230) (.n 10229) (.n 10228)),
    .atom (.add (.n 10231) (.n 10225) (.n 10230)),
    .atom (.const (.n 10232) (word 2 0 0)),
    .atom (.mul (.n 10233) (.n 10232) (.n 9373)),
    .atom (.load (.n 10234) (.n 14) 2),
    .atom (.mul (.n 10235) (.n 10234) (.n 10233)),
    .atom (.add (.n 10236) (.n 10231) (.n 10235)),
    .atom (.load (.n 10237) (.n 14) 3),
    .atom (.mul (.n 10238) (.n 10237) (.n 8963)),
    .atom (.add (.n 10239) (.n 10236) (.n 10238)),
    .atom (.load (.n 10240) (.n 14) 4),
    .atom (.mul (.n 10241) (.n 10240) (.n 8974)),
    .atom (.add (.n 10242) (.n 10239) (.n 10241)),
    .atom (.load (.n 10243) (.n 14) 5),
    .atom (.const (.n 10244) (word 0 0 0)),
    .atom (.mul (.n 10245) (.n 10243) (.n 10244)),
    .atom (.add (.n 10246) (.n 10242) (.n 10245)),
    .atom (.add (.n 10247) (.n 15) (.n 10246)),
    .atom (.mul (.n 10248) (.n 3947) (.n 10247)),
    .atom (.add (.n 10249) (.n 10222) (.n 10248))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9233, a9234, a9235, a9236, a9237, a9238, a9239, a9240, a9241, a9242, a9243, a9244, a9245, a9246,
    a9247, a9248, a9249, a9250, a9251, a9252, a9253, a9254, a9255, a9256, a9257, a9258, a9259, -⟩ := hs
  have e9233 := tb_loadHolds_unique a9233 (hw 0 (by norm_num))
  have e9239 := tb_loadHolds_unique a9239 (hw 1 (by norm_num))
  have e9244 := tb_loadHolds_unique a9244 (hw 2 (by norm_num))
  have e9247 := tb_loadHolds_unique a9247 (hw 3 (by norm_num))
  have e9250 := tb_loadHolds_unique a9250 (hw 4 (by norm_num))
  have e9253 := tb_loadHolds_unique a9253 (hw 5 (by norm_num))
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
  have hB : σ (.n 10247) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 1024)], [([86], 2)], [([57], 1)], [([58], 1)], [([], 0)]] := by
    simp only [v9373, v8974, v8963, v8279, v8165, a9257, a9256, a9255, a9254, e9253, a9252, a9251, e9250,
      a9249, a9248, e9247, a9246, a9245, e9244, a9243, a9242, a9241, a9240, e9239, a9238,
      a9237, a9236, a9235, a9234, e9233]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9259, a9258, hB]

set_option maxRecDepth 10000 in
theorem vtB05_26F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10276) = σ (.n 10249) + σ (.n 3966) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 2048)], [([87], 2)], [([59], 1)], [([60], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9260 [
    .atom (.load (.n 10250) (.n 14) 0),
    .atom (.const (.n 10251) (word 2 0 0)),
    .atom (.mul (.n 10252) (.n 10250) (.n 10251)),
    .atom (.const (.n 10253) (word 2048 0 0)),
    .atom (.mul (.n 10254) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10255) (.n 10253) (.n 10254)),
    .atom (.load (.n 10256) (.n 14) 1),
    .atom (.mul (.n 10257) (.n 10256) (.n 10255)),
    .atom (.add (.n 10258) (.n 10252) (.n 10257)),
    .atom (.const (.n 10259) (word 2 0 0)),
    .atom (.mul (.n 10260) (.n 10259) (.n 9384)),
    .atom (.load (.n 10261) (.n 14) 2),
    .atom (.mul (.n 10262) (.n 10261) (.n 10260)),
    .atom (.add (.n 10263) (.n 10258) (.n 10262)),
    .atom (.load (.n 10264) (.n 14) 3),
    .atom (.mul (.n 10265) (.n 10264) (.n 8985)),
    .atom (.add (.n 10266) (.n 10263) (.n 10265)),
    .atom (.load (.n 10267) (.n 14) 4),
    .atom (.mul (.n 10268) (.n 10267) (.n 8996)),
    .atom (.add (.n 10269) (.n 10266) (.n 10268)),
    .atom (.load (.n 10270) (.n 14) 5),
    .atom (.const (.n 10271) (word 0 0 0)),
    .atom (.mul (.n 10272) (.n 10270) (.n 10271)),
    .atom (.add (.n 10273) (.n 10269) (.n 10272)),
    .atom (.add (.n 10274) (.n 15) (.n 10273)),
    .atom (.mul (.n 10275) (.n 3966) (.n 10274)),
    .atom (.add (.n 10276) (.n 10249) (.n 10275))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9260, a9261, a9262, a9263, a9264, a9265, a9266, a9267, a9268, a9269, a9270, a9271, a9272, a9273,
    a9274, a9275, a9276, a9277, a9278, a9279, a9280, a9281, a9282, a9283, a9284, a9285, a9286, -⟩ := hs
  have e9260 := tb_loadHolds_unique a9260 (hw 0 (by norm_num))
  have e9266 := tb_loadHolds_unique a9266 (hw 1 (by norm_num))
  have e9271 := tb_loadHolds_unique a9271 (hw 2 (by norm_num))
  have e9274 := tb_loadHolds_unique a9274 (hw 3 (by norm_num))
  have e9277 := tb_loadHolds_unique a9277 (hw 4 (by norm_num))
  have e9280 := tb_loadHolds_unique a9280 (hw 5 (by norm_num))
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
  have hB : σ (.n 10274) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 2048)], [([87], 2)], [([59], 1)], [([60], 1)], [([], 0)]] := by
    simp only [v9384, v8996, v8985, v8279, v8165, a9284, a9283, a9282, a9281, e9280, a9279, a9278, e9277,
      a9276, a9275, e9274, a9273, a9272, e9271, a9270, a9269, a9268, a9267, e9266, a9265,
      a9264, a9263, a9262, a9261, e9260]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9286, a9285, hB]

set_option maxRecDepth 10000 in
theorem vtB05_27F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10303) = σ (.n 10276) + σ (.n 3985) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 9], 4096)], [([88], 2)], [([61], 1)], [([62], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 9287 [
    .atom (.load (.n 10277) (.n 14) 0),
    .atom (.const (.n 10278) (word 2 0 0)),
    .atom (.mul (.n 10279) (.n 10277) (.n 10278)),
    .atom (.const (.n 10280) (word 4096 0 0)),
    .atom (.mul (.n 10281) (.n 8165) (.n 8279)),
    .atom (.mul (.n 10282) (.n 10280) (.n 10281)),
    .atom (.load (.n 10283) (.n 14) 1),
    .atom (.mul (.n 10284) (.n 10283) (.n 10282)),
    .atom (.add (.n 10285) (.n 10279) (.n 10284)),
    .atom (.const (.n 10286) (word 2 0 0)),
    .atom (.mul (.n 10287) (.n 10286) (.n 9395)),
    .atom (.load (.n 10288) (.n 14) 2),
    .atom (.mul (.n 10289) (.n 10288) (.n 10287)),
    .atom (.add (.n 10290) (.n 10285) (.n 10289)),
    .atom (.load (.n 10291) (.n 14) 3),
    .atom (.mul (.n 10292) (.n 10291) (.n 9020)),
    .atom (.add (.n 10293) (.n 10290) (.n 10292)),
    .atom (.load (.n 10294) (.n 14) 4),
    .atom (.mul (.n 10295) (.n 10294) (.n 9031)),
    .atom (.add (.n 10296) (.n 10293) (.n 10295)),
    .atom (.load (.n 10297) (.n 14) 5),
    .atom (.const (.n 10298) (word 0 0 0)),
    .atom (.mul (.n 10299) (.n 10297) (.n 10298)),
    .atom (.add (.n 10300) (.n 10296) (.n 10299)),
    .atom (.add (.n 10301) (.n 15) (.n 10300)),
    .atom (.mul (.n 10302) (.n 3985) (.n 10301)),
    .atom (.add (.n 10303) (.n 10276) (.n 10302))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a9287, a9288, a9289, a9290, a9291, a9292, a9293, a9294, a9295, a9296, a9297, a9298, a9299, a9300,
    a9301, a9302, a9303, a9304, a9305, a9306, a9307, a9308, a9309, a9310, a9311, a9312, a9313, -⟩ := hs
  have e9287 := tb_loadHolds_unique a9287 (hw 0 (by norm_num))
  have e9293 := tb_loadHolds_unique a9293 (hw 1 (by norm_num))
  have e9298 := tb_loadHolds_unique a9298 (hw 2 (by norm_num))
  have e9301 := tb_loadHolds_unique a9301 (hw 3 (by norm_num))
  have e9304 := tb_loadHolds_unique a9304 (hw 4 (by norm_num))
  have e9307 := tb_loadHolds_unique a9307 (hw 5 (by norm_num))
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
  have hB : σ (.n 10301) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 9], 4096)], [([88], 2)], [([61], 1)], [([62], 1)], [([], 0)]] := by
    simp only [v9395, v9031, v9020, v8279, v8165, a9311, a9310, a9309, a9308, e9307, a9306, a9305, e9304,
      a9303, a9302, e9301, a9300, a9299, e9298, a9297, a9296, a9295, a9294, e9293, a9292,
      a9291, a9290, a9289, a9288, e9287]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a9313, a9312, hB]

end
end LeanVM.Guest.B1.Tables
