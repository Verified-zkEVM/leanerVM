/-
  LeanVM.Guest.B1.Tables.VtC.FForms3

  `Vt/FormsT3.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT3

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB03_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7387) = σ (.n 3282) * vtBlockVal (σ (.n 15)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6595 [
    .atom (.load (.n 7377) (.n 14) 0),
    .atom (.const (.n 7378) (word 2 0 0)),
    .atom (.mul (.n 7379) (.n 7378) (.n 7170)),
    .atom (.load (.n 7380) (.n 14) 1),
    .atom (.mul (.n 7381) (.n 7380) (.n 7379)),
    .atom (.add (.n 7382) (.n 7377) (.n 7381)),
    .atom (.load (.n 7383) (.n 14) 2),
    .atom (.mul (.n 7384) (.n 7383) (.n 7181)),
    .atom (.add (.n 7385) (.n 7382) (.n 7384)),
    .atom (.add (.n 7386) (.n 15) (.n 7385)),
    .atom (.mul (.n 7387) (.n 3282) (.n 7386))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6595, a6596, a6597, a6598, a6599, a6600, a6601, a6602, a6603, a6604, a6605, -⟩ := hs
  have e6595 := tb_loadHolds_unique a6595 (hw 0 (by norm_num))
  have e6598 := tb_loadHolds_unique a6598 (hw 1 (by norm_num))
  have e6601 := tb_loadHolds_unique a6601 (hw 2 (by norm_num))
  have v7170 : σ (.n 7170) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 38) (by norm_num)).2.2.1
  have v7181 : σ (.n 7181) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 39) (by norm_num)).2.2.1
  have hB : σ (.n 7386) = vtBlockVal (σ (.n 15)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v7181, v7170, a6604, a6603, a6602, e6601, a6600, a6599, e6598, a6597, a6596, e6595]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6605, hB]

set_option maxRecDepth 10000 in
theorem vtB03_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7420) = σ (.n 7387) + σ (.n 3301) * vtBlockVal (σ (.n 15)) W ev
      [[([], 4)], [([0], 1)], [([14], 2)], [([], 8)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6606 [
    .atom (.load (.n 7388) (.n 14) 0),
    .atom (.const (.n 7389) (word 4 0 0)),
    .atom (.mul (.n 7390) (.n 7388) (.n 7389)),
    .atom (.load (.n 7391) (.n 14) 1),
    .atom (.mul (.n 7392) (.n 7391) (.n 7170)),
    .atom (.add (.n 7393) (.n 7390) (.n 7392)),
    .atom (.const (.n 7394) (word 2 0 0)),
    .atom (.mul (.n 7395) (.n 7394) (.n 7376)),
    .atom (.load (.n 7396) (.n 14) 2),
    .atom (.mul (.n 7397) (.n 7396) (.n 7395)),
    .atom (.add (.n 7398) (.n 7393) (.n 7397)),
    .atom (.load (.n 7399) (.n 14) 3),
    .atom (.const (.n 7400) (word 8 0 0)),
    .atom (.mul (.n 7401) (.n 7399) (.n 7400)),
    .atom (.add (.n 7402) (.n 7398) (.n 7401)),
    .atom (.load (.n 7403) (.n 14) 4),
    .atom (.mul (.n 7404) (.n 7403) (.n 7205)),
    .atom (.add (.n 7405) (.n 7402) (.n 7404)),
    .atom (.load (.n 7406) (.n 14) 5),
    .atom (.mul (.n 7407) (.n 7406) (.n 7216)),
    .atom (.add (.n 7408) (.n 7405) (.n 7407)),
    .atom (.load (.n 7409) (.n 14) 6),
    .atom (.mul (.n 7410) (.n 7409) (.n 7227)),
    .atom (.add (.n 7411) (.n 7408) (.n 7410)),
    .atom (.load (.n 7412) (.n 14) 7),
    .atom (.mul (.n 7413) (.n 7412) (.n 7238)),
    .atom (.add (.n 7414) (.n 7411) (.n 7413)),
    .atom (.load (.n 7415) (.n 14) 8),
    .atom (.mul (.n 7416) (.n 7415) (.n 7262)),
    .atom (.add (.n 7417) (.n 7414) (.n 7416)),
    .atom (.add (.n 7418) (.n 15) (.n 7417)),
    .atom (.mul (.n 7419) (.n 3301) (.n 7418)),
    .atom (.add (.n 7420) (.n 7387) (.n 7419))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6606, a6607, a6608, a6609, a6610, a6611, a6612, a6613, a6614, a6615, a6616, a6617, a6618, a6619,
    a6620, a6621, a6622, a6623, a6624, a6625, a6626, a6627, a6628, a6629, a6630, a6631, a6632,
    a6633, a6634, a6635, a6636, a6637, a6638, -⟩ := hs
  have e6606 := tb_loadHolds_unique a6606 (hw 0 (by norm_num))
  have e6609 := tb_loadHolds_unique a6609 (hw 1 (by norm_num))
  have e6614 := tb_loadHolds_unique a6614 (hw 2 (by norm_num))
  have e6617 := tb_loadHolds_unique a6617 (hw 3 (by norm_num))
  have e6621 := tb_loadHolds_unique a6621 (hw 4 (by norm_num))
  have e6624 := tb_loadHolds_unique a6624 (hw 5 (by norm_num))
  have e6627 := tb_loadHolds_unique a6627 (hw 6 (by norm_num))
  have e6630 := tb_loadHolds_unique a6630 (hw 7 (by norm_num))
  have e6633 := tb_loadHolds_unique a6633 (hw 8 (by norm_num))
  have v7170 : σ (.n 7170) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 38) (by norm_num)).2.2.1
  have v7205 : σ (.n 7205) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 40) (by norm_num)).2.2.1
  have v7216 : σ (.n 7216) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 41) (by norm_num)).2.2.1
  have v7227 : σ (.n 7227) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 42) (by norm_num)).2.2.1
  have v7238 : σ (.n 7238) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 43) (by norm_num)).2.2.1
  have v7262 : σ (.n 7262) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 44) (by norm_num)).2.2.1
  have v7376 : σ (.n 7376) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_evalF h (k := 52) (by norm_num)).2.2.1
  have hB : σ (.n 7418) = vtBlockVal (σ (.n 15)) W ev [[([], 4)], [([0], 1)], [([14], 2)], [([], 8)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)]] := by
    simp only [v7376, v7262, v7238, v7227, v7216, v7205, v7170, a6636, a6635, a6634, e6633, a6632, a6631,
      e6630, a6629, a6628, e6627, a6626, a6625, e6624, a6623, a6622, e6621, a6620, a6619,
      a6618, e6617, a6616, a6615, e6614, a6613, a6612, a6611, a6610, e6609, a6608, a6607,
      e6606]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6638, a6637, hB]

set_option maxRecDepth 10000 in
theorem vtB03_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7446) = σ (.n 7420) + σ (.n 3320) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 2], 1)], [([11], 2)], [([7], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 6639 [
    .atom (.load (.n 7421) (.n 14) 0),
    .atom (.const (.n 7422) (word 2 0 0)),
    .atom (.mul (.n 7423) (.n 7421) (.n 7422)),
    .atom (.mul (.n 7424) (.n 7181) (.n 7205)),
    .atom (.load (.n 7425) (.n 14) 1),
    .atom (.mul (.n 7426) (.n 7425) (.n 7424)),
    .atom (.add (.n 7427) (.n 7423) (.n 7426)),
    .atom (.const (.n 7428) (word 2 0 0)),
    .atom (.mul (.n 7429) (.n 7428) (.n 7330)),
    .atom (.load (.n 7430) (.n 14) 2),
    .atom (.mul (.n 7431) (.n 7430) (.n 7429)),
    .atom (.add (.n 7432) (.n 7427) (.n 7431)),
    .atom (.load (.n 7433) (.n 14) 3),
    .atom (.mul (.n 7434) (.n 7433) (.n 7273)),
    .atom (.add (.n 7435) (.n 7432) (.n 7434)),
    .atom (.load (.n 7436) (.n 14) 4),
    .atom (.const (.n 7437) (word 0 0 0)),
    .atom (.mul (.n 7438) (.n 7436) (.n 7437)),
    .atom (.add (.n 7439) (.n 7435) (.n 7438)),
    .atom (.load (.n 7440) (.n 14) 5),
    .atom (.const (.n 7441) (word 0 0 0)),
    .atom (.mul (.n 7442) (.n 7440) (.n 7441)),
    .atom (.add (.n 7443) (.n 7439) (.n 7442)),
    .atom (.add (.n 7444) (.n 15) (.n 7443)),
    .atom (.mul (.n 7445) (.n 3320) (.n 7444)),
    .atom (.add (.n 7446) (.n 7420) (.n 7445))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6639, a6640, a6641, a6642, a6643, a6644, a6645, a6646, a6647, a6648, a6649, a6650, a6651, a6652,
    a6653, a6654, a6655, a6656, a6657, a6658, a6659, a6660, a6661, a6662, a6663, a6664, -⟩ := hs
  have e6639 := tb_loadHolds_unique a6639 (hw 0 (by norm_num))
  have e6643 := tb_loadHolds_unique a6643 (hw 1 (by norm_num))
  have e6648 := tb_loadHolds_unique a6648 (hw 2 (by norm_num))
  have e6651 := tb_loadHolds_unique a6651 (hw 3 (by norm_num))
  have e6654 := tb_loadHolds_unique a6654 (hw 4 (by norm_num))
  have e6658 := tb_loadHolds_unique a6658 (hw 5 (by norm_num))
  have v7181 : σ (.n 7181) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 39) (by norm_num)).2.2.1
  have v7205 : σ (.n 7205) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 40) (by norm_num)).2.2.1
  have v7273 : σ (.n 7273) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 45) (by norm_num)).2.2.1
  have v7330 : σ (.n 7330) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 49) (by norm_num)).2.2.1
  have hB : σ (.n 7444) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 2], 1)], [([11], 2)], [([7], 1)], [([], 0)], [([], 0)]] := by
    simp only [v7330, v7273, v7205, v7181, a6662, a6661, a6660, a6659, e6658, a6657, a6656, a6655, e6654,
      a6653, a6652, e6651, a6650, a6649, e6648, a6647, a6646, a6645, a6644, e6643, a6642,
      a6641, a6640, e6639]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a6664, a6663, hB]

set_option maxRecDepth 10000 in
theorem vtB03_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7488) = σ (.n 7446) + σ (.n 3339) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([7, 3], 1)], [([12], 2)], [([8], 1), ([5, 8], 1), ([6, 8], 1), ([5, 0], 4), ([6, 1], 1)], [([9], 1), ([5, 9], 1), ([6, 9], 1)], [([10], 1), ([5, 10], 1), ([6, 10], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6665 [
    .atom (.load (.n 7447) (.n 14) 0),
    .atom (.const (.n 7448) (word 2 0 0)),
    .atom (.mul (.n 7449) (.n 7447) (.n 7448)),
    .atom (.mul (.n 7450) (.n 7273) (.n 7216)),
    .atom (.load (.n 7451) (.n 14) 1),
    .atom (.mul (.n 7452) (.n 7451) (.n 7450)),
    .atom (.add (.n 7453) (.n 7449) (.n 7452)),
    .atom (.const (.n 7454) (word 2 0 0)),
    .atom (.mul (.n 7455) (.n 7454) (.n 7341)),
    .atom (.load (.n 7456) (.n 14) 2),
    .atom (.mul (.n 7457) (.n 7456) (.n 7455)),
    .atom (.add (.n 7458) (.n 7453) (.n 7457)),
    .atom (.mul (.n 7459) (.n 7238) (.n 7284)),
    .atom (.add (.n 7460) (.n 7284) (.n 7459)),
    .atom (.mul (.n 7461) (.n 7262) (.n 7284)),
    .atom (.add (.n 7462) (.n 7460) (.n 7461)),
    .atom (.const (.n 7463) (word 4 0 0)),
    .atom (.mul (.n 7464) (.n 7238) (.n 7170)),
    .atom (.mul (.n 7465) (.n 7463) (.n 7464)),
    .atom (.add (.n 7466) (.n 7462) (.n 7465)),
    .atom (.mul (.n 7467) (.n 7262) (.n 7181)),
    .atom (.add (.n 7468) (.n 7466) (.n 7467)),
    .atom (.load (.n 7469) (.n 14) 3),
    .atom (.mul (.n 7470) (.n 7469) (.n 7468)),
    .atom (.add (.n 7471) (.n 7458) (.n 7470)),
    .atom (.mul (.n 7472) (.n 7238) (.n 7295)),
    .atom (.add (.n 7473) (.n 7295) (.n 7472)),
    .atom (.mul (.n 7474) (.n 7262) (.n 7295)),
    .atom (.add (.n 7475) (.n 7473) (.n 7474)),
    .atom (.load (.n 7476) (.n 14) 4),
    .atom (.mul (.n 7477) (.n 7476) (.n 7475)),
    .atom (.add (.n 7478) (.n 7471) (.n 7477)),
    .atom (.mul (.n 7479) (.n 7238) (.n 7319)),
    .atom (.add (.n 7480) (.n 7319) (.n 7479)),
    .atom (.mul (.n 7481) (.n 7262) (.n 7319)),
    .atom (.add (.n 7482) (.n 7480) (.n 7481)),
    .atom (.load (.n 7483) (.n 14) 5),
    .atom (.mul (.n 7484) (.n 7483) (.n 7482)),
    .atom (.add (.n 7485) (.n 7478) (.n 7484)),
    .atom (.add (.n 7486) (.n 15) (.n 7485)),
    .atom (.mul (.n 7487) (.n 3339) (.n 7486)),
    .atom (.add (.n 7488) (.n 7446) (.n 7487))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6665, a6666, a6667, a6668, a6669, a6670, a6671, a6672, a6673, a6674, a6675, a6676, a6677, a6678,
    a6679, a6680, a6681, a6682, a6683, a6684, a6685, a6686, a6687, a6688, a6689, a6690, a6691,
    a6692, a6693, a6694, a6695, a6696, a6697, a6698, a6699, a6700, a6701, a6702, a6703, a6704,
    a6705, a6706, -⟩ := hs
  have e6665 := tb_loadHolds_unique a6665 (hw 0 (by norm_num))
  have e6669 := tb_loadHolds_unique a6669 (hw 1 (by norm_num))
  have e6674 := tb_loadHolds_unique a6674 (hw 2 (by norm_num))
  have e6687 := tb_loadHolds_unique a6687 (hw 3 (by norm_num))
  have e6694 := tb_loadHolds_unique a6694 (hw 4 (by norm_num))
  have e6701 := tb_loadHolds_unique a6701 (hw 5 (by norm_num))
  have v7170 : σ (.n 7170) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 38) (by norm_num)).2.2.1
  have v7181 : σ (.n 7181) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 39) (by norm_num)).2.2.1
  have v7216 : σ (.n 7216) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 41) (by norm_num)).2.2.1
  have v7238 : σ (.n 7238) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 43) (by norm_num)).2.2.1
  have v7262 : σ (.n 7262) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 44) (by norm_num)).2.2.1
  have v7273 : σ (.n 7273) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 45) (by norm_num)).2.2.1
  have v7284 : σ (.n 7284) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 46) (by norm_num)).2.2.1
  have v7295 : σ (.n 7295) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 47) (by norm_num)).2.2.1
  have v7319 : σ (.n 7319) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 48) (by norm_num)).2.2.1
  have v7341 : σ (.n 7341) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 50) (by norm_num)).2.2.1
  have hB : σ (.n 7486) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([7, 3], 1)], [([12], 2)], [([8], 1), ([5, 8], 1), ([6, 8], 1), ([5, 0], 4), ([6, 1], 1)], [([9], 1), ([5, 9], 1), ([6, 9], 1)], [([10], 1), ([5, 10], 1), ([6, 10], 1)]] := by
    simp only [v7341, v7319, v7295, v7284, v7273, v7262, v7238, v7216, v7181, v7170, a6704, a6703, a6702,
      e6701, a6700, a6699, a6698, a6697, a6696, a6695, e6694, a6693, a6692, a6691, a6690,
      a6689, a6688, e6687, a6686, a6685, a6684, a6683, a6682, a6681, a6680, a6679, a6678,
      a6677, a6676, a6675, e6674, a6673, a6672, a6671, a6670, e6669, a6668, a6667, a6666,
      e6665]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6706, a6705, hB]

set_option maxRecDepth 10000 in
theorem vtB03_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7512) = σ (.n 7488) + σ (.n 3358) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 4], 1)], [([13], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6707 [
    .atom (.load (.n 7489) (.n 14) 0),
    .atom (.const (.n 7490) (word 2 0 0)),
    .atom (.mul (.n 7491) (.n 7489) (.n 7490)),
    .atom (.mul (.n 7492) (.n 7181) (.n 7227)),
    .atom (.load (.n 7493) (.n 14) 1),
    .atom (.mul (.n 7494) (.n 7493) (.n 7492)),
    .atom (.add (.n 7495) (.n 7491) (.n 7494)),
    .atom (.const (.n 7496) (word 2 0 0)),
    .atom (.mul (.n 7497) (.n 7496) (.n 7352)),
    .atom (.load (.n 7498) (.n 14) 2),
    .atom (.mul (.n 7499) (.n 7498) (.n 7497)),
    .atom (.add (.n 7500) (.n 7495) (.n 7499)),
    .atom (.load (.n 7501) (.n 14) 3),
    .atom (.mul (.n 7502) (.n 7501) (.n 7284)),
    .atom (.add (.n 7503) (.n 7500) (.n 7502)),
    .atom (.load (.n 7504) (.n 14) 4),
    .atom (.mul (.n 7505) (.n 7504) (.n 7295)),
    .atom (.add (.n 7506) (.n 7503) (.n 7505)),
    .atom (.load (.n 7507) (.n 14) 5),
    .atom (.mul (.n 7508) (.n 7507) (.n 7319)),
    .atom (.add (.n 7509) (.n 7506) (.n 7508)),
    .atom (.add (.n 7510) (.n 15) (.n 7509)),
    .atom (.mul (.n 7511) (.n 3358) (.n 7510)),
    .atom (.add (.n 7512) (.n 7488) (.n 7511))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6707, a6708, a6709, a6710, a6711, a6712, a6713, a6714, a6715, a6716, a6717, a6718, a6719, a6720,
    a6721, a6722, a6723, a6724, a6725, a6726, a6727, a6728, a6729, a6730, -⟩ := hs
  have e6707 := tb_loadHolds_unique a6707 (hw 0 (by norm_num))
  have e6711 := tb_loadHolds_unique a6711 (hw 1 (by norm_num))
  have e6716 := tb_loadHolds_unique a6716 (hw 2 (by norm_num))
  have e6719 := tb_loadHolds_unique a6719 (hw 3 (by norm_num))
  have e6722 := tb_loadHolds_unique a6722 (hw 4 (by norm_num))
  have e6725 := tb_loadHolds_unique a6725 (hw 5 (by norm_num))
  have v7181 : σ (.n 7181) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 39) (by norm_num)).2.2.1
  have v7227 : σ (.n 7227) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 42) (by norm_num)).2.2.1
  have v7284 : σ (.n 7284) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 46) (by norm_num)).2.2.1
  have v7295 : σ (.n 7295) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 47) (by norm_num)).2.2.1
  have v7319 : σ (.n 7319) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 48) (by norm_num)).2.2.1
  have v7352 : σ (.n 7352) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 51) (by norm_num)).2.2.1
  have hB : σ (.n 7510) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 4], 1)], [([13], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
    simp only [v7352, v7319, v7295, v7284, v7227, v7181, a6728, a6727, a6726, e6725, a6724, a6723, e6722,
      a6721, a6720, e6719, a6718, a6717, e6716, a6715, a6714, a6713, a6712, e6711, a6710,
      a6709, a6708, e6707]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6730, a6729, hB]

set_option maxRecDepth 10000 in
theorem vtSide03F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7512) =
      vtSideVal [σ (.n 3282), σ (.n 3301), σ (.n 3320), σ (.n 3339), σ (.n 3358)]
        (σ (.n 15)) W ev vtBTerms03 := by
  rw [vtB03_4F h hw hev, vtB03_3F h hw hev, vtB03_2F h hw hev, vtB03_1F h hw hev, vtB03_0F h hw hev]
  simp only [vtSideVal, vtBTerms03, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtB13_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7522) = σ (.n 4660) * vtBlockVal (σ (.n 15)) W ev
      [[([], 1)], [([0], 1)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6732 [
    .atom (.load (.n 7514) (.n 14) 0),
    .atom (.load (.n 7515) (.n 14) 1),
    .atom (.mul (.n 7516) (.n 7515) (.n 7170)),
    .atom (.add (.n 7517) (.n 7514) (.n 7516)),
    .atom (.load (.n 7518) (.n 14) 2),
    .atom (.mul (.n 7519) (.n 7518) (.n 7181)),
    .atom (.add (.n 7520) (.n 7517) (.n 7519)),
    .atom (.add (.n 7521) (.n 15) (.n 7520)),
    .atom (.mul (.n 7522) (.n 4660) (.n 7521))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6732, a6733, a6734, a6735, a6736, a6737, a6738, a6739, a6740, -⟩ := hs
  have e6732 := tb_loadHolds_unique a6732 (hw 0 (by norm_num))
  have e6733 := tb_loadHolds_unique a6733 (hw 1 (by norm_num))
  have e6736 := tb_loadHolds_unique a6736 (hw 2 (by norm_num))
  have v7170 : σ (.n 7170) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 38) (by norm_num)).2.2.1
  have v7181 : σ (.n 7181) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 39) (by norm_num)).2.2.1
  have hB : σ (.n 7521) = vtBlockVal (σ (.n 15)) W ev [[([], 1)], [([0], 1)], [([1], 1)]] := by
    simp only [v7181, v7170, a6739, a6738, a6737, e6736, a6735, a6734, e6733, e6732]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
    ring
  rw [a6740, hB]

set_option maxRecDepth 10000 in
theorem vtB13_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7553) = σ (.n 7522) + σ (.n 4667) * vtBlockVal (σ (.n 15)) W ev
      [[([], 4)], [([0], 1)], [([14], 1)], [([], 8)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6741 [
    .atom (.load (.n 7523) (.n 14) 0),
    .atom (.const (.n 7524) (word 4 0 0)),
    .atom (.mul (.n 7525) (.n 7523) (.n 7524)),
    .atom (.load (.n 7526) (.n 14) 1),
    .atom (.mul (.n 7527) (.n 7526) (.n 7170)),
    .atom (.add (.n 7528) (.n 7525) (.n 7527)),
    .atom (.load (.n 7529) (.n 14) 2),
    .atom (.mul (.n 7530) (.n 7529) (.n 7376)),
    .atom (.add (.n 7531) (.n 7528) (.n 7530)),
    .atom (.load (.n 7532) (.n 14) 3),
    .atom (.const (.n 7533) (word 8 0 0)),
    .atom (.mul (.n 7534) (.n 7532) (.n 7533)),
    .atom (.add (.n 7535) (.n 7531) (.n 7534)),
    .atom (.load (.n 7536) (.n 14) 4),
    .atom (.mul (.n 7537) (.n 7536) (.n 7205)),
    .atom (.add (.n 7538) (.n 7535) (.n 7537)),
    .atom (.load (.n 7539) (.n 14) 5),
    .atom (.mul (.n 7540) (.n 7539) (.n 7216)),
    .atom (.add (.n 7541) (.n 7538) (.n 7540)),
    .atom (.load (.n 7542) (.n 14) 6),
    .atom (.mul (.n 7543) (.n 7542) (.n 7227)),
    .atom (.add (.n 7544) (.n 7541) (.n 7543)),
    .atom (.load (.n 7545) (.n 14) 7),
    .atom (.mul (.n 7546) (.n 7545) (.n 7238)),
    .atom (.add (.n 7547) (.n 7544) (.n 7546)),
    .atom (.load (.n 7548) (.n 14) 8),
    .atom (.mul (.n 7549) (.n 7548) (.n 7262)),
    .atom (.add (.n 7550) (.n 7547) (.n 7549)),
    .atom (.add (.n 7551) (.n 15) (.n 7550)),
    .atom (.mul (.n 7552) (.n 4667) (.n 7551)),
    .atom (.add (.n 7553) (.n 7522) (.n 7552))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6741, a6742, a6743, a6744, a6745, a6746, a6747, a6748, a6749, a6750, a6751, a6752, a6753, a6754,
    a6755, a6756, a6757, a6758, a6759, a6760, a6761, a6762, a6763, a6764, a6765, a6766, a6767,
    a6768, a6769, a6770, a6771, -⟩ := hs
  have e6741 := tb_loadHolds_unique a6741 (hw 0 (by norm_num))
  have e6744 := tb_loadHolds_unique a6744 (hw 1 (by norm_num))
  have e6747 := tb_loadHolds_unique a6747 (hw 2 (by norm_num))
  have e6750 := tb_loadHolds_unique a6750 (hw 3 (by norm_num))
  have e6754 := tb_loadHolds_unique a6754 (hw 4 (by norm_num))
  have e6757 := tb_loadHolds_unique a6757 (hw 5 (by norm_num))
  have e6760 := tb_loadHolds_unique a6760 (hw 6 (by norm_num))
  have e6763 := tb_loadHolds_unique a6763 (hw 7 (by norm_num))
  have e6766 := tb_loadHolds_unique a6766 (hw 8 (by norm_num))
  have v7170 : σ (.n 7170) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 38) (by norm_num)).2.2.1
  have v7205 : σ (.n 7205) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 40) (by norm_num)).2.2.1
  have v7216 : σ (.n 7216) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 41) (by norm_num)).2.2.1
  have v7227 : σ (.n 7227) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 42) (by norm_num)).2.2.1
  have v7238 : σ (.n 7238) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 43) (by norm_num)).2.2.1
  have v7262 : σ (.n 7262) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 44) (by norm_num)).2.2.1
  have v7376 : σ (.n 7376) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_evalF h (k := 52) (by norm_num)).2.2.1
  have hB : σ (.n 7551) = vtBlockVal (σ (.n 15)) W ev [[([], 4)], [([0], 1)], [([14], 1)], [([], 8)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)]] := by
    simp only [v7376, v7262, v7238, v7227, v7216, v7205, v7170, a6769, a6768, a6767, e6766, a6765, a6764,
      e6763, a6762, a6761, e6760, a6759, a6758, e6757, a6756, a6755, e6754, a6753, a6752,
      a6751, e6750, a6749, a6748, e6747, a6746, a6745, e6744, a6743, a6742, e6741]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6771, a6770, hB]

set_option maxRecDepth 10000 in
theorem vtB13_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7577) = σ (.n 7553) + σ (.n 4674) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 2], 1)], [([11], 1)], [([7], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 6772 [
    .atom (.load (.n 7554) (.n 14) 0),
    .atom (.const (.n 7555) (word 2 0 0)),
    .atom (.mul (.n 7556) (.n 7554) (.n 7555)),
    .atom (.mul (.n 7557) (.n 7181) (.n 7205)),
    .atom (.load (.n 7558) (.n 14) 1),
    .atom (.mul (.n 7559) (.n 7558) (.n 7557)),
    .atom (.add (.n 7560) (.n 7556) (.n 7559)),
    .atom (.load (.n 7561) (.n 14) 2),
    .atom (.mul (.n 7562) (.n 7561) (.n 7330)),
    .atom (.add (.n 7563) (.n 7560) (.n 7562)),
    .atom (.load (.n 7564) (.n 14) 3),
    .atom (.mul (.n 7565) (.n 7564) (.n 7273)),
    .atom (.add (.n 7566) (.n 7563) (.n 7565)),
    .atom (.load (.n 7567) (.n 14) 4),
    .atom (.const (.n 7568) (word 0 0 0)),
    .atom (.mul (.n 7569) (.n 7567) (.n 7568)),
    .atom (.add (.n 7570) (.n 7566) (.n 7569)),
    .atom (.load (.n 7571) (.n 14) 5),
    .atom (.const (.n 7572) (word 0 0 0)),
    .atom (.mul (.n 7573) (.n 7571) (.n 7572)),
    .atom (.add (.n 7574) (.n 7570) (.n 7573)),
    .atom (.add (.n 7575) (.n 15) (.n 7574)),
    .atom (.mul (.n 7576) (.n 4674) (.n 7575)),
    .atom (.add (.n 7577) (.n 7553) (.n 7576))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6772, a6773, a6774, a6775, a6776, a6777, a6778, a6779, a6780, a6781, a6782, a6783, a6784, a6785,
    a6786, a6787, a6788, a6789, a6790, a6791, a6792, a6793, a6794, a6795, -⟩ := hs
  have e6772 := tb_loadHolds_unique a6772 (hw 0 (by norm_num))
  have e6776 := tb_loadHolds_unique a6776 (hw 1 (by norm_num))
  have e6779 := tb_loadHolds_unique a6779 (hw 2 (by norm_num))
  have e6782 := tb_loadHolds_unique a6782 (hw 3 (by norm_num))
  have e6785 := tb_loadHolds_unique a6785 (hw 4 (by norm_num))
  have e6789 := tb_loadHolds_unique a6789 (hw 5 (by norm_num))
  have v7181 : σ (.n 7181) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 39) (by norm_num)).2.2.1
  have v7205 : σ (.n 7205) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 40) (by norm_num)).2.2.1
  have v7273 : σ (.n 7273) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 45) (by norm_num)).2.2.1
  have v7330 : σ (.n 7330) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 49) (by norm_num)).2.2.1
  have hB : σ (.n 7575) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 2], 1)], [([11], 1)], [([7], 1)], [([], 0)], [([], 0)]] := by
    simp only [v7330, v7273, v7205, v7181, a6793, a6792, a6791, a6790, e6789, a6788, a6787, a6786, e6785,
      a6784, a6783, e6782, a6781, a6780, e6779, a6778, a6777, e6776, a6775, a6774, a6773,
      e6772]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a6795, a6794, hB]

set_option maxRecDepth 10000 in
theorem vtB13_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7617) = σ (.n 7577) + σ (.n 4681) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([7, 3], 1)], [([12], 1)], [([8], 1), ([5, 8], 1), ([6, 8], 1), ([5, 0], 4), ([6, 1], 1)], [([9], 1), ([5, 9], 1), ([6, 9], 1)], [([10], 1), ([5, 10], 1), ([6, 10], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6796 [
    .atom (.load (.n 7578) (.n 14) 0),
    .atom (.const (.n 7579) (word 2 0 0)),
    .atom (.mul (.n 7580) (.n 7578) (.n 7579)),
    .atom (.mul (.n 7581) (.n 7273) (.n 7216)),
    .atom (.load (.n 7582) (.n 14) 1),
    .atom (.mul (.n 7583) (.n 7582) (.n 7581)),
    .atom (.add (.n 7584) (.n 7580) (.n 7583)),
    .atom (.load (.n 7585) (.n 14) 2),
    .atom (.mul (.n 7586) (.n 7585) (.n 7341)),
    .atom (.add (.n 7587) (.n 7584) (.n 7586)),
    .atom (.mul (.n 7588) (.n 7238) (.n 7284)),
    .atom (.add (.n 7589) (.n 7284) (.n 7588)),
    .atom (.mul (.n 7590) (.n 7262) (.n 7284)),
    .atom (.add (.n 7591) (.n 7589) (.n 7590)),
    .atom (.const (.n 7592) (word 4 0 0)),
    .atom (.mul (.n 7593) (.n 7238) (.n 7170)),
    .atom (.mul (.n 7594) (.n 7592) (.n 7593)),
    .atom (.add (.n 7595) (.n 7591) (.n 7594)),
    .atom (.mul (.n 7596) (.n 7262) (.n 7181)),
    .atom (.add (.n 7597) (.n 7595) (.n 7596)),
    .atom (.load (.n 7598) (.n 14) 3),
    .atom (.mul (.n 7599) (.n 7598) (.n 7597)),
    .atom (.add (.n 7600) (.n 7587) (.n 7599)),
    .atom (.mul (.n 7601) (.n 7238) (.n 7295)),
    .atom (.add (.n 7602) (.n 7295) (.n 7601)),
    .atom (.mul (.n 7603) (.n 7262) (.n 7295)),
    .atom (.add (.n 7604) (.n 7602) (.n 7603)),
    .atom (.load (.n 7605) (.n 14) 4),
    .atom (.mul (.n 7606) (.n 7605) (.n 7604)),
    .atom (.add (.n 7607) (.n 7600) (.n 7606)),
    .atom (.mul (.n 7608) (.n 7238) (.n 7319)),
    .atom (.add (.n 7609) (.n 7319) (.n 7608)),
    .atom (.mul (.n 7610) (.n 7262) (.n 7319)),
    .atom (.add (.n 7611) (.n 7609) (.n 7610)),
    .atom (.load (.n 7612) (.n 14) 5),
    .atom (.mul (.n 7613) (.n 7612) (.n 7611)),
    .atom (.add (.n 7614) (.n 7607) (.n 7613)),
    .atom (.add (.n 7615) (.n 15) (.n 7614)),
    .atom (.mul (.n 7616) (.n 4681) (.n 7615)),
    .atom (.add (.n 7617) (.n 7577) (.n 7616))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6796, a6797, a6798, a6799, a6800, a6801, a6802, a6803, a6804, a6805, a6806, a6807, a6808, a6809,
    a6810, a6811, a6812, a6813, a6814, a6815, a6816, a6817, a6818, a6819, a6820, a6821, a6822,
    a6823, a6824, a6825, a6826, a6827, a6828, a6829, a6830, a6831, a6832, a6833, a6834, a6835, -⟩ := hs
  have e6796 := tb_loadHolds_unique a6796 (hw 0 (by norm_num))
  have e6800 := tb_loadHolds_unique a6800 (hw 1 (by norm_num))
  have e6803 := tb_loadHolds_unique a6803 (hw 2 (by norm_num))
  have e6816 := tb_loadHolds_unique a6816 (hw 3 (by norm_num))
  have e6823 := tb_loadHolds_unique a6823 (hw 4 (by norm_num))
  have e6830 := tb_loadHolds_unique a6830 (hw 5 (by norm_num))
  have v7170 : σ (.n 7170) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 38) (by norm_num)).2.2.1
  have v7181 : σ (.n 7181) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 39) (by norm_num)).2.2.1
  have v7216 : σ (.n 7216) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 41) (by norm_num)).2.2.1
  have v7238 : σ (.n 7238) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 43) (by norm_num)).2.2.1
  have v7262 : σ (.n 7262) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 44) (by norm_num)).2.2.1
  have v7273 : σ (.n 7273) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 45) (by norm_num)).2.2.1
  have v7284 : σ (.n 7284) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 46) (by norm_num)).2.2.1
  have v7295 : σ (.n 7295) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 47) (by norm_num)).2.2.1
  have v7319 : σ (.n 7319) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 48) (by norm_num)).2.2.1
  have v7341 : σ (.n 7341) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 50) (by norm_num)).2.2.1
  have hB : σ (.n 7615) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([7, 3], 1)], [([12], 1)], [([8], 1), ([5, 8], 1), ([6, 8], 1), ([5, 0], 4), ([6, 1], 1)], [([9], 1), ([5, 9], 1), ([6, 9], 1)], [([10], 1), ([5, 10], 1), ([6, 10], 1)]] := by
    simp only [v7341, v7319, v7295, v7284, v7273, v7262, v7238, v7216, v7181, v7170, a6833, a6832, a6831,
      e6830, a6829, a6828, a6827, a6826, a6825, a6824, e6823, a6822, a6821, a6820, a6819,
      a6818, a6817, e6816, a6815, a6814, a6813, a6812, a6811, a6810, a6809, a6808, a6807,
      a6806, a6805, a6804, e6803, a6802, a6801, e6800, a6799, a6798, a6797, e6796]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6835, a6834, hB]

set_option maxRecDepth 10000 in
theorem vtB13_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7639) = σ (.n 7617) + σ (.n 4688) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 4], 1)], [([13], 1)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 6836 [
    .atom (.load (.n 7618) (.n 14) 0),
    .atom (.const (.n 7619) (word 2 0 0)),
    .atom (.mul (.n 7620) (.n 7618) (.n 7619)),
    .atom (.mul (.n 7621) (.n 7181) (.n 7227)),
    .atom (.load (.n 7622) (.n 14) 1),
    .atom (.mul (.n 7623) (.n 7622) (.n 7621)),
    .atom (.add (.n 7624) (.n 7620) (.n 7623)),
    .atom (.load (.n 7625) (.n 14) 2),
    .atom (.mul (.n 7626) (.n 7625) (.n 7352)),
    .atom (.add (.n 7627) (.n 7624) (.n 7626)),
    .atom (.load (.n 7628) (.n 14) 3),
    .atom (.mul (.n 7629) (.n 7628) (.n 7284)),
    .atom (.add (.n 7630) (.n 7627) (.n 7629)),
    .atom (.load (.n 7631) (.n 14) 4),
    .atom (.mul (.n 7632) (.n 7631) (.n 7295)),
    .atom (.add (.n 7633) (.n 7630) (.n 7632)),
    .atom (.load (.n 7634) (.n 14) 5),
    .atom (.mul (.n 7635) (.n 7634) (.n 7319)),
    .atom (.add (.n 7636) (.n 7633) (.n 7635)),
    .atom (.add (.n 7637) (.n 15) (.n 7636)),
    .atom (.mul (.n 7638) (.n 4688) (.n 7637)),
    .atom (.add (.n 7639) (.n 7617) (.n 7638))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6836, a6837, a6838, a6839, a6840, a6841, a6842, a6843, a6844, a6845, a6846, a6847, a6848, a6849,
    a6850, a6851, a6852, a6853, a6854, a6855, a6856, a6857, -⟩ := hs
  have e6836 := tb_loadHolds_unique a6836 (hw 0 (by norm_num))
  have e6840 := tb_loadHolds_unique a6840 (hw 1 (by norm_num))
  have e6843 := tb_loadHolds_unique a6843 (hw 2 (by norm_num))
  have e6846 := tb_loadHolds_unique a6846 (hw 3 (by norm_num))
  have e6849 := tb_loadHolds_unique a6849 (hw 4 (by norm_num))
  have e6852 := tb_loadHolds_unique a6852 (hw 5 (by norm_num))
  have v7181 : σ (.n 7181) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 39) (by norm_num)).2.2.1
  have v7227 : σ (.n 7227) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 42) (by norm_num)).2.2.1
  have v7284 : σ (.n 7284) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 46) (by norm_num)).2.2.1
  have v7295 : σ (.n 7295) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 47) (by norm_num)).2.2.1
  have v7319 : σ (.n 7319) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 48) (by norm_num)).2.2.1
  have v7352 : σ (.n 7352) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 51) (by norm_num)).2.2.1
  have hB : σ (.n 7637) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 4], 1)], [([13], 1)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
    simp only [v7352, v7319, v7295, v7284, v7227, v7181, a6855, a6854, a6853, e6852, a6851, a6850, e6849,
      a6848, a6847, e6846, a6845, a6844, e6843, a6842, a6841, e6840, a6839, a6838, a6837,
      e6836]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a6857, a6856, hB]

set_option maxRecDepth 10000 in
theorem vtSide13F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7639) =
      vtSideVal [σ (.n 4660), σ (.n 4667), σ (.n 4674), σ (.n 4681), σ (.n 4688)]
        (σ (.n 15)) W ev vtBTerms13 := by
  rw [vtB13_4F h hw hev, vtB13_3F h hw hev, vtB13_2F h hw hev, vtB13_1F h hw hev, vtB13_0F h hw hev]
  simp only [vtSideVal, vtBTerms13, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide23F {rd : Reader} {σ : Val} (h : VtF rd σ) {ev : ℕ → E}
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 7648) =
      vtSideVal [σ (.n 5116), σ (.n 5135), σ (.n 5154), σ (.n 5173)]
        (0) (fun _ ↦ 1) ev vtBTerms23 := by
  obtain ⟨_, hs⟩ := h.slice 6860 [
    .atom (.mul (.n 7642) (.n 5116) (.n 7330)),
    .atom (.mul (.n 7643) (.n 5135) (.n 7341)),
    .atom (.add (.n 7644) (.n 7642) (.n 7643)),
    .atom (.mul (.n 7645) (.n 5154) (.n 7352)),
    .atom (.add (.n 7646) (.n 7644) (.n 7645)),
    .atom (.mul (.n 7647) (.n 5173) (.n 7376)),
    .atom (.add (.n 7648) (.n 7646) (.n 7647))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6860, a6861, a6862, a6863, a6864, a6865, a6866, -⟩ := hs
  have v7330 : σ (.n 7330) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 49) (by norm_num)).2.2.1
  have v7341 : σ (.n 7341) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 50) (by norm_num)).2.2.1
  have v7352 : σ (.n 7352) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 51) (by norm_num)).2.2.1
  have v7376 : σ (.n 7376) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_evalF h (k := 52) (by norm_num)).2.2.1
  rw [a6866, a6864, a6862, a6860, a6861, a6863, a6865, v7330, v7341, v7352, v7376]
  simp only [vtSideVal, vtBTerms23, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
