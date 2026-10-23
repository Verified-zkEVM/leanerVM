/-
  LeanVM.Guest.B1.Tables.VtC.FForms5

  `Vt/FormsT5.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT5
public import LeanVM.Guest.B1.Tables.VtC.FForms5a
public import LeanVM.Guest.B1.Tables.VtC.FForms5b

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtSide05F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 10303) =
      vtSideVal [σ (.n 3472), σ (.n 3491), σ (.n 3510), σ (.n 3529), σ (.n 3548), σ (.n 3567), σ (.n 3586),
        σ (.n 3605), σ (.n 3624), σ (.n 3643), σ (.n 3662), σ (.n 3681), σ (.n 3700),
        σ (.n 3719), σ (.n 3738), σ (.n 3757), σ (.n 3776), σ (.n 3795), σ (.n 3814),
        σ (.n 3833), σ (.n 3852), σ (.n 3871), σ (.n 3890), σ (.n 3909), σ (.n 3928),
        σ (.n 3947), σ (.n 3966), σ (.n 3985)]
        (σ (.n 15)) W ev vtBTerms05 := by
  rw [vtB05_27F h hw hev, vtB05_26F h hw hev, vtB05_25F h hw hev, vtB05_24F h hw hev, vtB05_23F h hw hev,
    vtB05_22F h hw hev, vtB05_21F h hw hev, vtB05_20F h hw hev, vtB05_19F h hw hev,
    vtB05_18F h hw hev, vtB05_17F h hw hev, vtB05_16F h hw hev, vtB05_15F h hw hev,
    vtB05_14F h hw hev, vtB05_13F h hw hev, vtB05_12F h hw hev, vtB05_11F h hw hev,
    vtB05_10F h hw hev, vtB05_9F h hw hev, vtB05_8F h hw hev, vtB05_7F h hw hev, vtB05_6F h hw hev,
    vtB05_5F h hw hev, vtB05_4F h hw hev, vtB05_3F h hw hev, vtB05_2F h hw hev, vtB05_1F h hw hev,
    vtB05_0F h hw hev]
  simp only [vtSideVal, vtBTerms05, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide15F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i))
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 11132) =
      vtSideVal [σ (.n 4730), σ (.n 4737), σ (.n 4744), σ (.n 4751), σ (.n 4758), σ (.n 4765), σ (.n 4772),
        σ (.n 4779), σ (.n 4786), σ (.n 4793), σ (.n 4800), σ (.n 4807), σ (.n 4814),
        σ (.n 4821), σ (.n 4828), σ (.n 4835), σ (.n 4842), σ (.n 4849), σ (.n 4856),
        σ (.n 4863), σ (.n 4870), σ (.n 4877), σ (.n 4884), σ (.n 4891), σ (.n 4898),
        σ (.n 4905), σ (.n 4912), σ (.n 4919)]
        (σ (.n 15)) W ev vtBTerms15 := by
  rw [vtB15_27F h hw hev, vtB15_26F h hw hev, vtB15_25F h hw hev, vtB15_24F h hw hev, vtB15_23F h hw hev,
    vtB15_22F h hw hev, vtB15_21F h hw hev, vtB15_20F h hw hev, vtB15_19F h hw hev,
    vtB15_18F h hw hev, vtB15_17F h hw hev, vtB15_16F h hw hev, vtB15_15F h hw hev,
    vtB15_14F h hw hev, vtB15_13F h hw hev, vtB15_12F h hw hev, vtB15_11F h hw hev,
    vtB15_10F h hw hev, vtB15_9F h hw hev, vtB15_8F h hw hev, vtB15_7F h hw hev, vtB15_6F h hw hev,
    vtB15_5F h hw hev, vtB15_4F h hw hev, vtB15_3F h hw hev, vtB15_2F h hw hev, vtB15_1F h hw hev,
    vtB15_0F h hw hev]
  simp only [vtSideVal, vtBTerms15, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide25F {rd : Reader} {σ : Val} (h : VtF rd σ) {ev : ℕ → E}
    (hev : ∀ c < 90, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 11187) =
      vtSideVal [σ (.n 5268), σ (.n 5287), σ (.n 5306), σ (.n 5325), σ (.n 5344), σ (.n 5363), σ (.n 5382),
        σ (.n 5401), σ (.n 5420), σ (.n 5439), σ (.n 5458), σ (.n 5477), σ (.n 5496),
        σ (.n 5515), σ (.n 5534), σ (.n 5553), σ (.n 5572), σ (.n 5591), σ (.n 5610),
        σ (.n 5629), σ (.n 5648), σ (.n 5667), σ (.n 5686), σ (.n 5705), σ (.n 5724),
        σ (.n 5743), σ (.n 5762)]
        (0) (fun _ ↦ 1) ev vtBTerms25 := by
  obtain ⟨_, hs⟩ := h.slice 10145 [
    .atom (.mul (.n 11135) (.n 5268) (.n 9042)),
    .atom (.mul (.n 11136) (.n 5287) (.n 9053)),
    .atom (.add (.n 11137) (.n 11135) (.n 11136)),
    .atom (.mul (.n 11138) (.n 5306) (.n 9077)),
    .atom (.add (.n 11139) (.n 11137) (.n 11138)),
    .atom (.mul (.n 11140) (.n 5325) (.n 9088)),
    .atom (.add (.n 11141) (.n 11139) (.n 11140)),
    .atom (.mul (.n 11142) (.n 5344) (.n 9099)),
    .atom (.add (.n 11143) (.n 11141) (.n 11142)),
    .atom (.mul (.n 11144) (.n 5363) (.n 9110)),
    .atom (.add (.n 11145) (.n 11143) (.n 11144)),
    .atom (.mul (.n 11146) (.n 5382) (.n 9134)),
    .atom (.add (.n 11147) (.n 11145) (.n 11146)),
    .atom (.mul (.n 11148) (.n 5401) (.n 9145)),
    .atom (.add (.n 11149) (.n 11147) (.n 11148)),
    .atom (.mul (.n 11150) (.n 5420) (.n 9156)),
    .atom (.add (.n 11151) (.n 11149) (.n 11150)),
    .atom (.mul (.n 11152) (.n 5439) (.n 9167)),
    .atom (.add (.n 11153) (.n 11151) (.n 11152)),
    .atom (.mul (.n 11154) (.n 5458) (.n 9191)),
    .atom (.add (.n 11155) (.n 11153) (.n 11154)),
    .atom (.mul (.n 11156) (.n 5477) (.n 9202)),
    .atom (.add (.n 11157) (.n 11155) (.n 11156)),
    .atom (.mul (.n 11158) (.n 5496) (.n 9213)),
    .atom (.add (.n 11159) (.n 11157) (.n 11158)),
    .atom (.mul (.n 11160) (.n 5515) (.n 9224)),
    .atom (.add (.n 11161) (.n 11159) (.n 11160)),
    .atom (.mul (.n 11162) (.n 5534) (.n 9248)),
    .atom (.add (.n 11163) (.n 11161) (.n 11162)),
    .atom (.mul (.n 11164) (.n 5553) (.n 9259)),
    .atom (.add (.n 11165) (.n 11163) (.n 11164)),
    .atom (.mul (.n 11166) (.n 5572) (.n 9270)),
    .atom (.add (.n 11167) (.n 11165) (.n 11166)),
    .atom (.mul (.n 11168) (.n 5591) (.n 9281)),
    .atom (.add (.n 11169) (.n 11167) (.n 11168)),
    .atom (.mul (.n 11170) (.n 5610) (.n 9305)),
    .atom (.add (.n 11171) (.n 11169) (.n 11170)),
    .atom (.mul (.n 11172) (.n 5629) (.n 9316)),
    .atom (.add (.n 11173) (.n 11171) (.n 11172)),
    .atom (.mul (.n 11174) (.n 5648) (.n 9327)),
    .atom (.add (.n 11175) (.n 11173) (.n 11174)),
    .atom (.mul (.n 11176) (.n 5667) (.n 9338)),
    .atom (.add (.n 11177) (.n 11175) (.n 11176)),
    .atom (.mul (.n 11178) (.n 5686) (.n 9362)),
    .atom (.add (.n 11179) (.n 11177) (.n 11178)),
    .atom (.mul (.n 11180) (.n 5705) (.n 9373)),
    .atom (.add (.n 11181) (.n 11179) (.n 11180)),
    .atom (.mul (.n 11182) (.n 5724) (.n 9384)),
    .atom (.add (.n 11183) (.n 11181) (.n 11182)),
    .atom (.mul (.n 11184) (.n 5743) (.n 9395)),
    .atom (.add (.n 11185) (.n 11183) (.n 11184)),
    .atom (.mul (.n 11186) (.n 5762) (.n 9419)),
    .atom (.add (.n 11187) (.n 11185) (.n 11186))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a10145, a10146, a10147, a10148, a10149, a10150, a10151, a10152, a10153, a10154, a10155, a10156,
    a10157, a10158, a10159, a10160, a10161, a10162, a10163, a10164, a10165, a10166, a10167,
    a10168, a10169, a10170, a10171, a10172, a10173, a10174, a10175, a10176, a10177, a10178,
    a10179, a10180, a10181, a10182, a10183, a10184, a10185, a10186, a10187, a10188, a10189,
    a10190, a10191, a10192, a10193, a10194, a10195, a10196, a10197, -⟩ := hs
  have v9042 : σ (.n 9042) = ev 63 := by
    rw [← hev 63 (by norm_num)]; exact (vt_evalF h (k := 130) (by norm_num)).2.2.1
  have v9053 : σ (.n 9053) = ev 64 := by
    rw [← hev 64 (by norm_num)]; exact (vt_evalF h (k := 131) (by norm_num)).2.2.1
  have v9077 : σ (.n 9077) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_evalF h (k := 132) (by norm_num)).2.2.1
  have v9088 : σ (.n 9088) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_evalF h (k := 133) (by norm_num)).2.2.1
  have v9099 : σ (.n 9099) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_evalF h (k := 134) (by norm_num)).2.2.1
  have v9110 : σ (.n 9110) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_evalF h (k := 135) (by norm_num)).2.2.1
  have v9134 : σ (.n 9134) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_evalF h (k := 136) (by norm_num)).2.2.1
  have v9145 : σ (.n 9145) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_evalF h (k := 137) (by norm_num)).2.2.1
  have v9156 : σ (.n 9156) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_evalF h (k := 138) (by norm_num)).2.2.1
  have v9167 : σ (.n 9167) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_evalF h (k := 139) (by norm_num)).2.2.1
  have v9191 : σ (.n 9191) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_evalF h (k := 140) (by norm_num)).2.2.1
  have v9202 : σ (.n 9202) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_evalF h (k := 141) (by norm_num)).2.2.1
  have v9213 : σ (.n 9213) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_evalF h (k := 142) (by norm_num)).2.2.1
  have v9224 : σ (.n 9224) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_evalF h (k := 143) (by norm_num)).2.2.1
  have v9248 : σ (.n 9248) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_evalF h (k := 144) (by norm_num)).2.2.1
  have v9259 : σ (.n 9259) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_evalF h (k := 145) (by norm_num)).2.2.1
  have v9270 : σ (.n 9270) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_evalF h (k := 146) (by norm_num)).2.2.1
  have v9281 : σ (.n 9281) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_evalF h (k := 147) (by norm_num)).2.2.1
  have v9305 : σ (.n 9305) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_evalF h (k := 148) (by norm_num)).2.2.1
  have v9316 : σ (.n 9316) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_evalF h (k := 149) (by norm_num)).2.2.1
  have v9327 : σ (.n 9327) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_evalF h (k := 150) (by norm_num)).2.2.1
  have v9338 : σ (.n 9338) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_evalF h (k := 151) (by norm_num)).2.2.1
  have v9362 : σ (.n 9362) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_evalF h (k := 152) (by norm_num)).2.2.1
  have v9373 : σ (.n 9373) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_evalF h (k := 153) (by norm_num)).2.2.1
  have v9384 : σ (.n 9384) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_evalF h (k := 154) (by norm_num)).2.2.1
  have v9395 : σ (.n 9395) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_evalF h (k := 155) (by norm_num)).2.2.1
  have v9419 : σ (.n 9419) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_evalF h (k := 156) (by norm_num)).2.2.1
  rw [a10197, a10195, a10193, a10191, a10189, a10187, a10185, a10183, a10181, a10179, a10177, a10175,
    a10173, a10171, a10169, a10167, a10165, a10163, a10161, a10159, a10157, a10155, a10153,
    a10151, a10149, a10147, a10145, a10146, a10148, a10150, a10152, a10154, a10156, a10158,
    a10160, a10162, a10164, a10166, a10168, a10170, a10172, a10174, a10176, a10178, a10180,
    a10182, a10184, a10186, a10188, a10190, a10192, a10194, a10196, v9042, v9053, v9077, v9088,
    v9099, v9110, v9134, v9145, v9156, v9167, v9191, v9202, v9213, v9224, v9248, v9259, v9270,
    v9281, v9305, v9316, v9327, v9338, v9362, v9373, v9384, v9395, v9419]
  simp only [vtSideVal, vtBTerms25, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
