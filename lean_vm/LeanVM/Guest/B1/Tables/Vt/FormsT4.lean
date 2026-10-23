/-
  LeanVM.Guest.B1.Tables.Vt.FormsT4

  Table 4's forms on the three sides, from the guest's statements: each block's value from its
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
theorem vtB04_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 7881) = σ (.n 3377) * vtBlockVal (σ (.n 15)) W ev
      [[([], 1)], [([13, 6], 1), ([13, 0], 2), ([0], 2)], [([13, 7], 1), ([13, 1], 1), ([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 7057 [
    .atom (.load (.n 7861) (.n 14) 0),
    .atom (.mul (.n 7862) (.n 7852) (.n 7749)),
    .atom (.const (.n 7863) (word 2 0 0)),
    .atom (.mul (.n 7864) (.n 7852) (.n 7670)),
    .atom (.mul (.n 7865) (.n 7863) (.n 7864)),
    .atom (.add (.n 7866) (.n 7862) (.n 7865)),
    .atom (.const (.n 7867) (word 2 0 0)),
    .atom (.mul (.n 7868) (.n 7867) (.n 7670)),
    .atom (.add (.n 7869) (.n 7866) (.n 7868)),
    .atom (.load (.n 7870) (.n 14) 1),
    .atom (.mul (.n 7871) (.n 7870) (.n 7869)),
    .atom (.add (.n 7872) (.n 7861) (.n 7871)),
    .atom (.mul (.n 7873) (.n 7852) (.n 7773)),
    .atom (.mul (.n 7874) (.n 7852) (.n 7681)),
    .atom (.add (.n 7875) (.n 7873) (.n 7874)),
    .atom (.add (.n 7876) (.n 7875) (.n 7681)),
    .atom (.load (.n 7877) (.n 14) 2),
    .atom (.mul (.n 7878) (.n 7877) (.n 7876)),
    .atom (.add (.n 7879) (.n 7872) (.n 7878)),
    .atom (.add (.n 7880) (.n 15) (.n 7879)),
    .atom (.mul (.n 7881) (.n 3377) (.n 7880))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a7057, a7058, a7059, a7060, a7061, a7062, a7063, a7064, a7065, a7066, a7067, a7068, a7069, a7070,
    a7071, a7072, a7073, a7074, a7075, a7076, a7077, -⟩ := hs
  have e7057 := tb_loadHolds_unique a7057 (hw 0 (by norm_num))
  have e7066 := tb_loadHolds_unique a7066 (hw 1 (by norm_num))
  have e7073 := tb_loadHolds_unique a7073 (hw 2 (by norm_num))
  have v7670 : σ (.n 7670) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2.1
  have v7681 : σ (.n 7681) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2.1
  have v7749 : σ (.n 7749) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 59) (by norm_num)).2.2.1
  have v7773 : σ (.n 7773) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 60) (by norm_num)).2.2.1
  have v7852 : σ (.n 7852) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 66) (by norm_num)).2.2.1
  have hB : σ (.n 7880) = vtBlockVal (σ (.n 15)) W ev [[([], 1)], [([13, 6], 1), ([13, 0], 2), ([0], 2)], [([13, 7], 1), ([13, 1], 1), ([1], 1)]] := by
    simp only [v7852, v7773, v7749, v7681, v7670, a7076, a7075, a7074, e7073, a7072, a7071, a7070, a7069,
      a7068, a7067, e7066, a7065, a7064, a7063, a7062, a7061, a7060, a7059, a7058, e7057]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a7077, hB]

set_option maxRecDepth 10000 in
theorem vtB04_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 7916) = σ (.n 7881) + σ (.n 3396) * vtBlockVal (σ (.n 15)) W ev
      [[([], 4)], [([0], 1)], [([11], 2)], [([], 16)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 7078 [
    .atom (.load (.n 7882) (.n 14) 0),
    .atom (.const (.n 7883) (word 4 0 0)),
    .atom (.mul (.n 7884) (.n 7882) (.n 7883)),
    .atom (.load (.n 7885) (.n 14) 1),
    .atom (.mul (.n 7886) (.n 7885) (.n 7670)),
    .atom (.add (.n 7887) (.n 7884) (.n 7886)),
    .atom (.const (.n 7888) (word 2 0 0)),
    .atom (.mul (.n 7889) (.n 7888) (.n 7830)),
    .atom (.load (.n 7890) (.n 14) 2),
    .atom (.mul (.n 7891) (.n 7890) (.n 7889)),
    .atom (.add (.n 7892) (.n 7887) (.n 7891)),
    .atom (.load (.n 7893) (.n 14) 3),
    .atom (.const (.n 7894) (word 16 0 0)),
    .atom (.mul (.n 7895) (.n 7893) (.n 7894)),
    .atom (.add (.n 7896) (.n 7892) (.n 7895)),
    .atom (.load (.n 7897) (.n 14) 4),
    .atom (.mul (.n 7898) (.n 7897) (.n 7692)),
    .atom (.add (.n 7899) (.n 7896) (.n 7898)),
    .atom (.load (.n 7900) (.n 14) 5),
    .atom (.mul (.n 7901) (.n 7900) (.n 7716)),
    .atom (.add (.n 7902) (.n 7899) (.n 7901)),
    .atom (.load (.n 7903) (.n 14) 6),
    .atom (.mul (.n 7904) (.n 7903) (.n 7727)),
    .atom (.add (.n 7905) (.n 7902) (.n 7904)),
    .atom (.load (.n 7906) (.n 14) 7),
    .atom (.const (.n 7907) (word 0 0 0)),
    .atom (.mul (.n 7908) (.n 7906) (.n 7907)),
    .atom (.add (.n 7909) (.n 7905) (.n 7908)),
    .atom (.load (.n 7910) (.n 14) 8),
    .atom (.const (.n 7911) (word 0 0 0)),
    .atom (.mul (.n 7912) (.n 7910) (.n 7911)),
    .atom (.add (.n 7913) (.n 7909) (.n 7912)),
    .atom (.add (.n 7914) (.n 15) (.n 7913)),
    .atom (.mul (.n 7915) (.n 3396) (.n 7914)),
    .atom (.add (.n 7916) (.n 7881) (.n 7915))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a7078, a7079, a7080, a7081, a7082, a7083, a7084, a7085, a7086, a7087, a7088, a7089, a7090, a7091,
    a7092, a7093, a7094, a7095, a7096, a7097, a7098, a7099, a7100, a7101, a7102, a7103, a7104,
    a7105, a7106, a7107, a7108, a7109, a7110, a7111, a7112, -⟩ := hs
  have e7078 := tb_loadHolds_unique a7078 (hw 0 (by norm_num))
  have e7081 := tb_loadHolds_unique a7081 (hw 1 (by norm_num))
  have e7086 := tb_loadHolds_unique a7086 (hw 2 (by norm_num))
  have e7089 := tb_loadHolds_unique a7089 (hw 3 (by norm_num))
  have e7093 := tb_loadHolds_unique a7093 (hw 4 (by norm_num))
  have e7096 := tb_loadHolds_unique a7096 (hw 5 (by norm_num))
  have e7099 := tb_loadHolds_unique a7099 (hw 6 (by norm_num))
  have e7102 := tb_loadHolds_unique a7102 (hw 7 (by norm_num))
  have e7106 := tb_loadHolds_unique a7106 (hw 8 (by norm_num))
  have v7670 : σ (.n 7670) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2.1
  have v7692 : σ (.n 7692) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 55) (by norm_num)).2.2.1
  have v7716 : σ (.n 7716) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 56) (by norm_num)).2.2.1
  have v7727 : σ (.n 7727) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 57) (by norm_num)).2.2.1
  have v7830 : σ (.n 7830) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 64) (by norm_num)).2.2.1
  have hB : σ (.n 7914) = vtBlockVal (σ (.n 15)) W ev [[([], 4)], [([0], 1)], [([11], 2)], [([], 16)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v7830, v7727, v7716, v7692, v7670, a7110, a7109, a7108, a7107, e7106, a7105, a7104, a7103,
      e7102, a7101, a7100, e7099, a7098, a7097, e7096, a7095, a7094, e7093, a7092, a7091,
      a7090, e7089, a7088, a7087, e7086, a7085, a7084, a7083, a7082, e7081, a7080, a7079,
      e7078]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a7112, a7111, hB]

set_option maxRecDepth 10000 in
theorem vtB04_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 7942) = σ (.n 7916) + σ (.n 3415) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 2], 1)], [([8], 2)], [([5], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 7113 [
    .atom (.load (.n 7917) (.n 14) 0),
    .atom (.const (.n 7918) (word 2 0 0)),
    .atom (.mul (.n 7919) (.n 7917) (.n 7918)),
    .atom (.mul (.n 7920) (.n 7681) (.n 7692)),
    .atom (.load (.n 7921) (.n 14) 1),
    .atom (.mul (.n 7922) (.n 7921) (.n 7920)),
    .atom (.add (.n 7923) (.n 7919) (.n 7922)),
    .atom (.const (.n 7924) (word 2 0 0)),
    .atom (.mul (.n 7925) (.n 7924) (.n 7784)),
    .atom (.load (.n 7926) (.n 14) 2),
    .atom (.mul (.n 7927) (.n 7926) (.n 7925)),
    .atom (.add (.n 7928) (.n 7923) (.n 7927)),
    .atom (.load (.n 7929) (.n 14) 3),
    .atom (.mul (.n 7930) (.n 7929) (.n 7738)),
    .atom (.add (.n 7931) (.n 7928) (.n 7930)),
    .atom (.load (.n 7932) (.n 14) 4),
    .atom (.const (.n 7933) (word 0 0 0)),
    .atom (.mul (.n 7934) (.n 7932) (.n 7933)),
    .atom (.add (.n 7935) (.n 7931) (.n 7934)),
    .atom (.load (.n 7936) (.n 14) 5),
    .atom (.const (.n 7937) (word 0 0 0)),
    .atom (.mul (.n 7938) (.n 7936) (.n 7937)),
    .atom (.add (.n 7939) (.n 7935) (.n 7938)),
    .atom (.add (.n 7940) (.n 15) (.n 7939)),
    .atom (.mul (.n 7941) (.n 3415) (.n 7940)),
    .atom (.add (.n 7942) (.n 7916) (.n 7941))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a7113, a7114, a7115, a7116, a7117, a7118, a7119, a7120, a7121, a7122, a7123, a7124, a7125, a7126,
    a7127, a7128, a7129, a7130, a7131, a7132, a7133, a7134, a7135, a7136, a7137, a7138, -⟩ := hs
  have e7113 := tb_loadHolds_unique a7113 (hw 0 (by norm_num))
  have e7117 := tb_loadHolds_unique a7117 (hw 1 (by norm_num))
  have e7122 := tb_loadHolds_unique a7122 (hw 2 (by norm_num))
  have e7125 := tb_loadHolds_unique a7125 (hw 3 (by norm_num))
  have e7128 := tb_loadHolds_unique a7128 (hw 4 (by norm_num))
  have e7132 := tb_loadHolds_unique a7132 (hw 5 (by norm_num))
  have v7681 : σ (.n 7681) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2.1
  have v7692 : σ (.n 7692) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 55) (by norm_num)).2.2.1
  have v7738 : σ (.n 7738) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 58) (by norm_num)).2.2.1
  have v7784 : σ (.n 7784) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 61) (by norm_num)).2.2.1
  have hB : σ (.n 7940) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 2], 1)], [([8], 2)], [([5], 1)], [([], 0)], [([], 0)]] := by
    simp only [v7784, v7738, v7692, v7681, a7136, a7135, a7134, a7133, e7132, a7131, a7130, a7129, e7128,
      a7127, a7126, e7125, a7124, a7123, e7122, a7121, a7120, a7119, a7118, e7117, a7116,
      a7115, a7114, e7113]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a7138, a7137, hB]

set_option maxRecDepth 10000 in
theorem vtB04_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 7968) = σ (.n 7942) + σ (.n 3434) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 3], 1)], [([9], 2)], [([6], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 7139 [
    .atom (.load (.n 7943) (.n 14) 0),
    .atom (.const (.n 7944) (word 2 0 0)),
    .atom (.mul (.n 7945) (.n 7943) (.n 7944)),
    .atom (.mul (.n 7946) (.n 7681) (.n 7716)),
    .atom (.load (.n 7947) (.n 14) 1),
    .atom (.mul (.n 7948) (.n 7947) (.n 7946)),
    .atom (.add (.n 7949) (.n 7945) (.n 7948)),
    .atom (.const (.n 7950) (word 2 0 0)),
    .atom (.mul (.n 7951) (.n 7950) (.n 7795)),
    .atom (.load (.n 7952) (.n 14) 2),
    .atom (.mul (.n 7953) (.n 7952) (.n 7951)),
    .atom (.add (.n 7954) (.n 7949) (.n 7953)),
    .atom (.load (.n 7955) (.n 14) 3),
    .atom (.mul (.n 7956) (.n 7955) (.n 7749)),
    .atom (.add (.n 7957) (.n 7954) (.n 7956)),
    .atom (.load (.n 7958) (.n 14) 4),
    .atom (.const (.n 7959) (word 0 0 0)),
    .atom (.mul (.n 7960) (.n 7958) (.n 7959)),
    .atom (.add (.n 7961) (.n 7957) (.n 7960)),
    .atom (.load (.n 7962) (.n 14) 5),
    .atom (.const (.n 7963) (word 0 0 0)),
    .atom (.mul (.n 7964) (.n 7962) (.n 7963)),
    .atom (.add (.n 7965) (.n 7961) (.n 7964)),
    .atom (.add (.n 7966) (.n 15) (.n 7965)),
    .atom (.mul (.n 7967) (.n 3434) (.n 7966)),
    .atom (.add (.n 7968) (.n 7942) (.n 7967))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a7139, a7140, a7141, a7142, a7143, a7144, a7145, a7146, a7147, a7148, a7149, a7150, a7151, a7152,
    a7153, a7154, a7155, a7156, a7157, a7158, a7159, a7160, a7161, a7162, a7163, a7164, -⟩ := hs
  have e7139 := tb_loadHolds_unique a7139 (hw 0 (by norm_num))
  have e7143 := tb_loadHolds_unique a7143 (hw 1 (by norm_num))
  have e7148 := tb_loadHolds_unique a7148 (hw 2 (by norm_num))
  have e7151 := tb_loadHolds_unique a7151 (hw 3 (by norm_num))
  have e7154 := tb_loadHolds_unique a7154 (hw 4 (by norm_num))
  have e7158 := tb_loadHolds_unique a7158 (hw 5 (by norm_num))
  have v7681 : σ (.n 7681) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2.1
  have v7716 : σ (.n 7716) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 56) (by norm_num)).2.2.1
  have v7749 : σ (.n 7749) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 59) (by norm_num)).2.2.1
  have v7795 : σ (.n 7795) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2.1
  have hB : σ (.n 7966) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 3], 1)], [([9], 2)], [([6], 1)], [([], 0)], [([], 0)]] := by
    simp only [v7795, v7749, v7716, v7681, a7162, a7161, a7160, a7159, e7158, a7157, a7156, a7155, e7154,
      a7153, a7152, e7151, a7150, a7149, e7148, a7147, a7146, a7145, a7144, e7143, a7142,
      a7141, a7140, e7139]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a7164, a7163, hB]

set_option maxRecDepth 10000 in
theorem vtB04_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 7994) = σ (.n 7968) + σ (.n 3453) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 4], 1)], [([10], 2)], [([7], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 7165 [
    .atom (.load (.n 7969) (.n 14) 0),
    .atom (.const (.n 7970) (word 2 0 0)),
    .atom (.mul (.n 7971) (.n 7969) (.n 7970)),
    .atom (.mul (.n 7972) (.n 7681) (.n 7727)),
    .atom (.load (.n 7973) (.n 14) 1),
    .atom (.mul (.n 7974) (.n 7973) (.n 7972)),
    .atom (.add (.n 7975) (.n 7971) (.n 7974)),
    .atom (.const (.n 7976) (word 2 0 0)),
    .atom (.mul (.n 7977) (.n 7976) (.n 7806)),
    .atom (.load (.n 7978) (.n 14) 2),
    .atom (.mul (.n 7979) (.n 7978) (.n 7977)),
    .atom (.add (.n 7980) (.n 7975) (.n 7979)),
    .atom (.load (.n 7981) (.n 14) 3),
    .atom (.mul (.n 7982) (.n 7981) (.n 7773)),
    .atom (.add (.n 7983) (.n 7980) (.n 7982)),
    .atom (.load (.n 7984) (.n 14) 4),
    .atom (.const (.n 7985) (word 0 0 0)),
    .atom (.mul (.n 7986) (.n 7984) (.n 7985)),
    .atom (.add (.n 7987) (.n 7983) (.n 7986)),
    .atom (.load (.n 7988) (.n 14) 5),
    .atom (.const (.n 7989) (word 0 0 0)),
    .atom (.mul (.n 7990) (.n 7988) (.n 7989)),
    .atom (.add (.n 7991) (.n 7987) (.n 7990)),
    .atom (.add (.n 7992) (.n 15) (.n 7991)),
    .atom (.mul (.n 7993) (.n 3453) (.n 7992)),
    .atom (.add (.n 7994) (.n 7968) (.n 7993))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a7165, a7166, a7167, a7168, a7169, a7170, a7171, a7172, a7173, a7174, a7175, a7176, a7177, a7178,
    a7179, a7180, a7181, a7182, a7183, a7184, a7185, a7186, a7187, a7188, a7189, a7190, -⟩ := hs
  have e7165 := tb_loadHolds_unique a7165 (hw 0 (by norm_num))
  have e7169 := tb_loadHolds_unique a7169 (hw 1 (by norm_num))
  have e7174 := tb_loadHolds_unique a7174 (hw 2 (by norm_num))
  have e7177 := tb_loadHolds_unique a7177 (hw 3 (by norm_num))
  have e7180 := tb_loadHolds_unique a7180 (hw 4 (by norm_num))
  have e7184 := tb_loadHolds_unique a7184 (hw 5 (by norm_num))
  have v7681 : σ (.n 7681) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2.1
  have v7727 : σ (.n 7727) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 57) (by norm_num)).2.2.1
  have v7773 : σ (.n 7773) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 60) (by norm_num)).2.2.1
  have v7806 : σ (.n 7806) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 63) (by norm_num)).2.2.1
  have hB : σ (.n 7992) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 4], 1)], [([10], 2)], [([7], 1)], [([], 0)], [([], 0)]] := by
    simp only [v7806, v7773, v7727, v7681, a7188, a7187, a7186, a7185, e7184, a7183, a7182, a7181, e7180,
      a7179, a7178, e7177, a7176, a7175, e7174, a7173, a7172, a7171, a7170, e7169, a7168,
      a7167, a7166, e7165]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a7190, a7189, hB]

set_option maxRecDepth 10000 in
theorem vtSide04 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 7994) =
      vtSideVal [σ (.n 3377), σ (.n 3396), σ (.n 3415), σ (.n 3434), σ (.n 3453)]
        (σ (.n 15)) W ev vtBTerms04 := by
  rw [vtB04_4 h hw hev, vtB04_3 h hw hev, vtB04_2 h hw hev, vtB04_1 h hw hev, vtB04_0 h hw hev]
  simp only [vtSideVal, vtBTerms04, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtB14_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 8005) = σ (.n 4695) * vtBlockVal (σ (.n 15)) W ev
      [[([], 1)], [([0], 1)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.slice 7193 [
    .atom (.load (.n 7997) (.n 14) 0),
    .atom (.load (.n 7998) (.n 14) 1),
    .atom (.mul (.n 7999) (.n 7998) (.n 7670)),
    .atom (.add (.n 8000) (.n 7997) (.n 7999)),
    .atom (.load (.n 8001) (.n 14) 2),
    .atom (.mul (.n 8002) (.n 8001) (.n 7681)),
    .atom (.add (.n 8003) (.n 8000) (.n 8002)),
    .atom (.add (.n 8004) (.n 15) (.n 8003)),
    .atom (.mul (.n 8005) (.n 4695) (.n 8004))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a7193, a7194, a7195, a7196, a7197, a7198, a7199, a7200, a7201, -⟩ := hs
  have e7193 := tb_loadHolds_unique a7193 (hw 0 (by norm_num))
  have e7194 := tb_loadHolds_unique a7194 (hw 1 (by norm_num))
  have e7197 := tb_loadHolds_unique a7197 (hw 2 (by norm_num))
  have v7670 : σ (.n 7670) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2.1
  have v7681 : σ (.n 7681) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2.1
  have hB : σ (.n 8004) = vtBlockVal (σ (.n 15)) W ev [[([], 1)], [([0], 1)], [([1], 1)]] := by
    simp only [v7681, v7670, a7200, a7199, a7198, e7197, a7196, a7195, e7194, e7193]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
    ring
  rw [a7201, hB]

set_option maxRecDepth 10000 in
theorem vtB14_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 8038) = σ (.n 8005) + σ (.n 4702) * vtBlockVal (σ (.n 15)) W ev
      [[([], 4)], [([0], 1)], [([11], 1)], [([], 16)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 7202 [
    .atom (.load (.n 8006) (.n 14) 0),
    .atom (.const (.n 8007) (word 4 0 0)),
    .atom (.mul (.n 8008) (.n 8006) (.n 8007)),
    .atom (.load (.n 8009) (.n 14) 1),
    .atom (.mul (.n 8010) (.n 8009) (.n 7670)),
    .atom (.add (.n 8011) (.n 8008) (.n 8010)),
    .atom (.load (.n 8012) (.n 14) 2),
    .atom (.mul (.n 8013) (.n 8012) (.n 7830)),
    .atom (.add (.n 8014) (.n 8011) (.n 8013)),
    .atom (.load (.n 8015) (.n 14) 3),
    .atom (.const (.n 8016) (word 16 0 0)),
    .atom (.mul (.n 8017) (.n 8015) (.n 8016)),
    .atom (.add (.n 8018) (.n 8014) (.n 8017)),
    .atom (.load (.n 8019) (.n 14) 4),
    .atom (.mul (.n 8020) (.n 8019) (.n 7692)),
    .atom (.add (.n 8021) (.n 8018) (.n 8020)),
    .atom (.load (.n 8022) (.n 14) 5),
    .atom (.mul (.n 8023) (.n 8022) (.n 7716)),
    .atom (.add (.n 8024) (.n 8021) (.n 8023)),
    .atom (.load (.n 8025) (.n 14) 6),
    .atom (.mul (.n 8026) (.n 8025) (.n 7727)),
    .atom (.add (.n 8027) (.n 8024) (.n 8026)),
    .atom (.load (.n 8028) (.n 14) 7),
    .atom (.const (.n 8029) (word 0 0 0)),
    .atom (.mul (.n 8030) (.n 8028) (.n 8029)),
    .atom (.add (.n 8031) (.n 8027) (.n 8030)),
    .atom (.load (.n 8032) (.n 14) 8),
    .atom (.const (.n 8033) (word 0 0 0)),
    .atom (.mul (.n 8034) (.n 8032) (.n 8033)),
    .atom (.add (.n 8035) (.n 8031) (.n 8034)),
    .atom (.add (.n 8036) (.n 15) (.n 8035)),
    .atom (.mul (.n 8037) (.n 4702) (.n 8036)),
    .atom (.add (.n 8038) (.n 8005) (.n 8037))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a7202, a7203, a7204, a7205, a7206, a7207, a7208, a7209, a7210, a7211, a7212, a7213, a7214, a7215,
    a7216, a7217, a7218, a7219, a7220, a7221, a7222, a7223, a7224, a7225, a7226, a7227, a7228,
    a7229, a7230, a7231, a7232, a7233, a7234, -⟩ := hs
  have e7202 := tb_loadHolds_unique a7202 (hw 0 (by norm_num))
  have e7205 := tb_loadHolds_unique a7205 (hw 1 (by norm_num))
  have e7208 := tb_loadHolds_unique a7208 (hw 2 (by norm_num))
  have e7211 := tb_loadHolds_unique a7211 (hw 3 (by norm_num))
  have e7215 := tb_loadHolds_unique a7215 (hw 4 (by norm_num))
  have e7218 := tb_loadHolds_unique a7218 (hw 5 (by norm_num))
  have e7221 := tb_loadHolds_unique a7221 (hw 6 (by norm_num))
  have e7224 := tb_loadHolds_unique a7224 (hw 7 (by norm_num))
  have e7228 := tb_loadHolds_unique a7228 (hw 8 (by norm_num))
  have v7670 : σ (.n 7670) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2.1
  have v7692 : σ (.n 7692) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 55) (by norm_num)).2.2.1
  have v7716 : σ (.n 7716) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 56) (by norm_num)).2.2.1
  have v7727 : σ (.n 7727) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 57) (by norm_num)).2.2.1
  have v7830 : σ (.n 7830) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 64) (by norm_num)).2.2.1
  have hB : σ (.n 8036) = vtBlockVal (σ (.n 15)) W ev [[([], 4)], [([0], 1)], [([11], 1)], [([], 16)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v7830, v7727, v7716, v7692, v7670, a7232, a7231, a7230, a7229, e7228, a7227, a7226, a7225,
      e7224, a7223, a7222, e7221, a7220, a7219, e7218, a7217, a7216, e7215, a7214, a7213,
      a7212, e7211, a7210, a7209, e7208, a7207, a7206, e7205, a7204, a7203, e7202]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a7234, a7233, hB]

set_option maxRecDepth 10000 in
theorem vtB14_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 8062) = σ (.n 8038) + σ (.n 4709) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 2], 1)], [([8], 1)], [([5], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 7235 [
    .atom (.load (.n 8039) (.n 14) 0),
    .atom (.const (.n 8040) (word 2 0 0)),
    .atom (.mul (.n 8041) (.n 8039) (.n 8040)),
    .atom (.mul (.n 8042) (.n 7681) (.n 7692)),
    .atom (.load (.n 8043) (.n 14) 1),
    .atom (.mul (.n 8044) (.n 8043) (.n 8042)),
    .atom (.add (.n 8045) (.n 8041) (.n 8044)),
    .atom (.load (.n 8046) (.n 14) 2),
    .atom (.mul (.n 8047) (.n 8046) (.n 7784)),
    .atom (.add (.n 8048) (.n 8045) (.n 8047)),
    .atom (.load (.n 8049) (.n 14) 3),
    .atom (.mul (.n 8050) (.n 8049) (.n 7738)),
    .atom (.add (.n 8051) (.n 8048) (.n 8050)),
    .atom (.load (.n 8052) (.n 14) 4),
    .atom (.const (.n 8053) (word 0 0 0)),
    .atom (.mul (.n 8054) (.n 8052) (.n 8053)),
    .atom (.add (.n 8055) (.n 8051) (.n 8054)),
    .atom (.load (.n 8056) (.n 14) 5),
    .atom (.const (.n 8057) (word 0 0 0)),
    .atom (.mul (.n 8058) (.n 8056) (.n 8057)),
    .atom (.add (.n 8059) (.n 8055) (.n 8058)),
    .atom (.add (.n 8060) (.n 15) (.n 8059)),
    .atom (.mul (.n 8061) (.n 4709) (.n 8060)),
    .atom (.add (.n 8062) (.n 8038) (.n 8061))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a7235, a7236, a7237, a7238, a7239, a7240, a7241, a7242, a7243, a7244, a7245, a7246, a7247, a7248,
    a7249, a7250, a7251, a7252, a7253, a7254, a7255, a7256, a7257, a7258, -⟩ := hs
  have e7235 := tb_loadHolds_unique a7235 (hw 0 (by norm_num))
  have e7239 := tb_loadHolds_unique a7239 (hw 1 (by norm_num))
  have e7242 := tb_loadHolds_unique a7242 (hw 2 (by norm_num))
  have e7245 := tb_loadHolds_unique a7245 (hw 3 (by norm_num))
  have e7248 := tb_loadHolds_unique a7248 (hw 4 (by norm_num))
  have e7252 := tb_loadHolds_unique a7252 (hw 5 (by norm_num))
  have v7681 : σ (.n 7681) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2.1
  have v7692 : σ (.n 7692) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 55) (by norm_num)).2.2.1
  have v7738 : σ (.n 7738) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 58) (by norm_num)).2.2.1
  have v7784 : σ (.n 7784) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 61) (by norm_num)).2.2.1
  have hB : σ (.n 8060) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 2], 1)], [([8], 1)], [([5], 1)], [([], 0)], [([], 0)]] := by
    simp only [v7784, v7738, v7692, v7681, a7256, a7255, a7254, a7253, e7252, a7251, a7250, a7249, e7248,
      a7247, a7246, e7245, a7244, a7243, e7242, a7241, a7240, e7239, a7238, a7237, a7236,
      e7235]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a7258, a7257, hB]

set_option maxRecDepth 10000 in
theorem vtB14_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 8086) = σ (.n 8062) + σ (.n 4716) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 3], 1)], [([9], 1)], [([6], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 7259 [
    .atom (.load (.n 8063) (.n 14) 0),
    .atom (.const (.n 8064) (word 2 0 0)),
    .atom (.mul (.n 8065) (.n 8063) (.n 8064)),
    .atom (.mul (.n 8066) (.n 7681) (.n 7716)),
    .atom (.load (.n 8067) (.n 14) 1),
    .atom (.mul (.n 8068) (.n 8067) (.n 8066)),
    .atom (.add (.n 8069) (.n 8065) (.n 8068)),
    .atom (.load (.n 8070) (.n 14) 2),
    .atom (.mul (.n 8071) (.n 8070) (.n 7795)),
    .atom (.add (.n 8072) (.n 8069) (.n 8071)),
    .atom (.load (.n 8073) (.n 14) 3),
    .atom (.mul (.n 8074) (.n 8073) (.n 7749)),
    .atom (.add (.n 8075) (.n 8072) (.n 8074)),
    .atom (.load (.n 8076) (.n 14) 4),
    .atom (.const (.n 8077) (word 0 0 0)),
    .atom (.mul (.n 8078) (.n 8076) (.n 8077)),
    .atom (.add (.n 8079) (.n 8075) (.n 8078)),
    .atom (.load (.n 8080) (.n 14) 5),
    .atom (.const (.n 8081) (word 0 0 0)),
    .atom (.mul (.n 8082) (.n 8080) (.n 8081)),
    .atom (.add (.n 8083) (.n 8079) (.n 8082)),
    .atom (.add (.n 8084) (.n 15) (.n 8083)),
    .atom (.mul (.n 8085) (.n 4716) (.n 8084)),
    .atom (.add (.n 8086) (.n 8062) (.n 8085))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a7259, a7260, a7261, a7262, a7263, a7264, a7265, a7266, a7267, a7268, a7269, a7270, a7271, a7272,
    a7273, a7274, a7275, a7276, a7277, a7278, a7279, a7280, a7281, a7282, -⟩ := hs
  have e7259 := tb_loadHolds_unique a7259 (hw 0 (by norm_num))
  have e7263 := tb_loadHolds_unique a7263 (hw 1 (by norm_num))
  have e7266 := tb_loadHolds_unique a7266 (hw 2 (by norm_num))
  have e7269 := tb_loadHolds_unique a7269 (hw 3 (by norm_num))
  have e7272 := tb_loadHolds_unique a7272 (hw 4 (by norm_num))
  have e7276 := tb_loadHolds_unique a7276 (hw 5 (by norm_num))
  have v7681 : σ (.n 7681) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2.1
  have v7716 : σ (.n 7716) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 56) (by norm_num)).2.2.1
  have v7749 : σ (.n 7749) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 59) (by norm_num)).2.2.1
  have v7795 : σ (.n 7795) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2.1
  have hB : σ (.n 8084) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 3], 1)], [([9], 1)], [([6], 1)], [([], 0)], [([], 0)]] := by
    simp only [v7795, v7749, v7716, v7681, a7280, a7279, a7278, a7277, e7276, a7275, a7274, a7273, e7272,
      a7271, a7270, e7269, a7268, a7267, e7266, a7265, a7264, e7263, a7262, a7261, a7260,
      e7259]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a7282, a7281, hB]

set_option maxRecDepth 10000 in
theorem vtB14_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 8110) = σ (.n 8086) + σ (.n 4723) * vtBlockVal (σ (.n 15)) W ev
      [[([], 2)], [([1, 4], 1)], [([10], 1)], [([7], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.slice 7283 [
    .atom (.load (.n 8087) (.n 14) 0),
    .atom (.const (.n 8088) (word 2 0 0)),
    .atom (.mul (.n 8089) (.n 8087) (.n 8088)),
    .atom (.mul (.n 8090) (.n 7681) (.n 7727)),
    .atom (.load (.n 8091) (.n 14) 1),
    .atom (.mul (.n 8092) (.n 8091) (.n 8090)),
    .atom (.add (.n 8093) (.n 8089) (.n 8092)),
    .atom (.load (.n 8094) (.n 14) 2),
    .atom (.mul (.n 8095) (.n 8094) (.n 7806)),
    .atom (.add (.n 8096) (.n 8093) (.n 8095)),
    .atom (.load (.n 8097) (.n 14) 3),
    .atom (.mul (.n 8098) (.n 8097) (.n 7773)),
    .atom (.add (.n 8099) (.n 8096) (.n 8098)),
    .atom (.load (.n 8100) (.n 14) 4),
    .atom (.const (.n 8101) (word 0 0 0)),
    .atom (.mul (.n 8102) (.n 8100) (.n 8101)),
    .atom (.add (.n 8103) (.n 8099) (.n 8102)),
    .atom (.load (.n 8104) (.n 14) 5),
    .atom (.const (.n 8105) (word 0 0 0)),
    .atom (.mul (.n 8106) (.n 8104) (.n 8105)),
    .atom (.add (.n 8107) (.n 8103) (.n 8106)),
    .atom (.add (.n 8108) (.n 15) (.n 8107)),
    .atom (.mul (.n 8109) (.n 4723) (.n 8108)),
    .atom (.add (.n 8110) (.n 8086) (.n 8109))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a7283, a7284, a7285, a7286, a7287, a7288, a7289, a7290, a7291, a7292, a7293, a7294, a7295, a7296,
    a7297, a7298, a7299, a7300, a7301, a7302, a7303, a7304, a7305, a7306, -⟩ := hs
  have e7283 := tb_loadHolds_unique a7283 (hw 0 (by norm_num))
  have e7287 := tb_loadHolds_unique a7287 (hw 1 (by norm_num))
  have e7290 := tb_loadHolds_unique a7290 (hw 2 (by norm_num))
  have e7293 := tb_loadHolds_unique a7293 (hw 3 (by norm_num))
  have e7296 := tb_loadHolds_unique a7296 (hw 4 (by norm_num))
  have e7300 := tb_loadHolds_unique a7300 (hw 5 (by norm_num))
  have v7681 : σ (.n 7681) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2.1
  have v7727 : σ (.n 7727) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 57) (by norm_num)).2.2.1
  have v7773 : σ (.n 7773) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 60) (by norm_num)).2.2.1
  have v7806 : σ (.n 7806) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 63) (by norm_num)).2.2.1
  have hB : σ (.n 8108) = vtBlockVal (σ (.n 15)) W ev [[([], 2)], [([1, 4], 1)], [([10], 1)], [([7], 1)], [([], 0)], [([], 0)]] := by
    simp only [v7806, v7773, v7727, v7681, a7304, a7303, a7302, a7301, e7300, a7299, a7298, a7297, e7296,
      a7295, a7294, e7293, a7292, a7291, e7290, a7289, a7288, e7287, a7286, a7285, a7284,
      e7283]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a7306, a7305, hB]

set_option maxRecDepth 10000 in
theorem vtSide14 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 8110) =
      vtSideVal [σ (.n 4695), σ (.n 4702), σ (.n 4709), σ (.n 4716), σ (.n 4723)]
        (σ (.n 15)) W ev vtBTerms14 := by
  rw [vtB14_4 h hw hev, vtB14_3 h hw hev, vtB14_2 h hw hev, vtB14_1 h hw hev, vtB14_0 h hw hev]
  simp only [vtSideVal, vtBTerms14, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide24 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 8119) =
      vtSideVal [σ (.n 5192), σ (.n 5211), σ (.n 5230), σ (.n 5249)]
        (0) (fun _ ↦ 1) ev vtBTerms24 := by
  obtain ⟨_, hs⟩ := h.slice 7309 [
    .atom (.mul (.n 8113) (.n 5192) (.n 7784)),
    .atom (.mul (.n 8114) (.n 5211) (.n 7795)),
    .atom (.add (.n 8115) (.n 8113) (.n 8114)),
    .atom (.mul (.n 8116) (.n 5230) (.n 7806)),
    .atom (.add (.n 8117) (.n 8115) (.n 8116)),
    .atom (.mul (.n 8118) (.n 5249) (.n 7830)),
    .atom (.add (.n 8119) (.n 8117) (.n 8118))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a7309, a7310, a7311, a7312, a7313, a7314, a7315, -⟩ := hs
  have v7784 : σ (.n 7784) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 61) (by norm_num)).2.2.1
  have v7795 : σ (.n 7795) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2.1
  have v7806 : σ (.n 7806) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 63) (by norm_num)).2.2.1
  have v7830 : σ (.n 7830) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 64) (by norm_num)).2.2.1
  rw [a7315, a7313, a7311, a7309, a7310, a7312, a7314, v7784, v7795, v7806, v7830]
  simp only [vtSideVal, vtBTerms24, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
