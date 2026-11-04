/-
  LeanVM.Guest.B1.Tables.VtC.FForms4

  `Vt/FormsT4.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT4

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB04_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4234) = σ (.n 1098) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([13, 6], 1), ([13, 0], 2), ([0], 2)], [([13, 7], 1), ([13, 1], 1), ([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4012 [
    .atom (.load (.n 4214) (.n 13) 0),
    .atom (.mul (.n 4215) (.n 4205) (.n 4102)),
    .atom (.const (.n 4216) (word 2 0 0)),
    .atom (.mul (.n 4217) (.n 4205) (.n 4023)),
    .atom (.mul (.n 4218) (.n 4216) (.n 4217)),
    .atom (.add (.n 4219) (.n 4215) (.n 4218)),
    .atom (.const (.n 4220) (word 2 0 0)),
    .atom (.mul (.n 4221) (.n 4220) (.n 4023)),
    .atom (.add (.n 4222) (.n 4219) (.n 4221)),
    .atom (.load (.n 4223) (.n 13) 1),
    .atom (.mul (.n 4224) (.n 4223) (.n 4222)),
    .atom (.add (.n 4225) (.n 4214) (.n 4224)),
    .atom (.mul (.n 4226) (.n 4205) (.n 4126)),
    .atom (.mul (.n 4227) (.n 4205) (.n 4034)),
    .atom (.add (.n 4228) (.n 4226) (.n 4227)),
    .atom (.add (.n 4229) (.n 4228) (.n 4034)),
    .atom (.load (.n 4230) (.n 13) 2),
    .atom (.mul (.n 4231) (.n 4230) (.n 4229)),
    .atom (.add (.n 4232) (.n 4225) (.n 4231)),
    .atom (.add (.n 4233) (.n 14) (.n 4232)),
    .atom (.mul (.n 4234) (.n 1098) (.n 4233))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4012, a4013, a4014, a4015, a4016, a4017, a4018, a4019, a4020, a4021, a4022, a4023, a4024, a4025,
    a4026, a4027, a4028, a4029, a4030, a4031, a4032, -⟩ := hs
  have e4012 := tb_loadHolds_unique a4012 (hw 0 (by norm_num))
  have e4021 := tb_loadHolds_unique a4021 (hw 1 (by norm_num))
  have e4028 := tb_loadHolds_unique a4028 (hw 2 (by norm_num))
  have v4023 : σ (.n 4023) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 53) (by norm_num)).2.2
  have v4034 : σ (.n 4034) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 54) (by norm_num)).2.2
  have v4102 : σ (.n 4102) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 59) (by norm_num)).2.2
  have v4126 : σ (.n 4126) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 60) (by norm_num)).2.2
  have v4205 : σ (.n 4205) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 66) (by norm_num)).2.2
  have hB : σ (.n 4233) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([13, 6], 1), ([13, 0], 2), ([0], 2)], [([13, 7], 1), ([13, 1], 1), ([1], 1)]] := by
    simp only [v4205, v4126, v4102, v4034, v4023, a4031, a4030, a4029, e4028, a4027, a4026, a4025, a4024,
      a4023, a4022, e4021, a4020, a4019, a4018, a4017, a4016, a4015, a4014, a4013, e4012]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4032, hB]

set_option maxRecDepth 10000 in
theorem vtB04_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4269) = σ (.n 4234) + σ (.n 1107) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([11], 2)], [([], 16)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4033 [
    .atom (.load (.n 4235) (.n 13) 0),
    .atom (.const (.n 4236) (word 4 0 0)),
    .atom (.mul (.n 4237) (.n 4235) (.n 4236)),
    .atom (.load (.n 4238) (.n 13) 1),
    .atom (.mul (.n 4239) (.n 4238) (.n 4023)),
    .atom (.add (.n 4240) (.n 4237) (.n 4239)),
    .atom (.const (.n 4241) (word 2 0 0)),
    .atom (.mul (.n 4242) (.n 4241) (.n 4183)),
    .atom (.load (.n 4243) (.n 13) 2),
    .atom (.mul (.n 4244) (.n 4243) (.n 4242)),
    .atom (.add (.n 4245) (.n 4240) (.n 4244)),
    .atom (.load (.n 4246) (.n 13) 3),
    .atom (.const (.n 4247) (word 16 0 0)),
    .atom (.mul (.n 4248) (.n 4246) (.n 4247)),
    .atom (.add (.n 4249) (.n 4245) (.n 4248)),
    .atom (.load (.n 4250) (.n 13) 4),
    .atom (.mul (.n 4251) (.n 4250) (.n 4045)),
    .atom (.add (.n 4252) (.n 4249) (.n 4251)),
    .atom (.load (.n 4253) (.n 13) 5),
    .atom (.mul (.n 4254) (.n 4253) (.n 4069)),
    .atom (.add (.n 4255) (.n 4252) (.n 4254)),
    .atom (.load (.n 4256) (.n 13) 6),
    .atom (.mul (.n 4257) (.n 4256) (.n 4080)),
    .atom (.add (.n 4258) (.n 4255) (.n 4257)),
    .atom (.load (.n 4259) (.n 13) 7),
    .atom (.const (.n 4260) (word 0 0 0)),
    .atom (.mul (.n 4261) (.n 4259) (.n 4260)),
    .atom (.add (.n 4262) (.n 4258) (.n 4261)),
    .atom (.load (.n 4263) (.n 13) 8),
    .atom (.const (.n 4264) (word 0 0 0)),
    .atom (.mul (.n 4265) (.n 4263) (.n 4264)),
    .atom (.add (.n 4266) (.n 4262) (.n 4265)),
    .atom (.add (.n 4267) (.n 14) (.n 4266)),
    .atom (.mul (.n 4268) (.n 1107) (.n 4267)),
    .atom (.add (.n 4269) (.n 4234) (.n 4268))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4033, a4034, a4035, a4036, a4037, a4038, a4039, a4040, a4041, a4042, a4043, a4044, a4045, a4046,
    a4047, a4048, a4049, a4050, a4051, a4052, a4053, a4054, a4055, a4056, a4057, a4058, a4059,
    a4060, a4061, a4062, a4063, a4064, a4065, a4066, a4067, -⟩ := hs
  have e4033 := tb_loadHolds_unique a4033 (hw 0 (by norm_num))
  have e4036 := tb_loadHolds_unique a4036 (hw 1 (by norm_num))
  have e4041 := tb_loadHolds_unique a4041 (hw 2 (by norm_num))
  have e4044 := tb_loadHolds_unique a4044 (hw 3 (by norm_num))
  have e4048 := tb_loadHolds_unique a4048 (hw 4 (by norm_num))
  have e4051 := tb_loadHolds_unique a4051 (hw 5 (by norm_num))
  have e4054 := tb_loadHolds_unique a4054 (hw 6 (by norm_num))
  have e4057 := tb_loadHolds_unique a4057 (hw 7 (by norm_num))
  have e4061 := tb_loadHolds_unique a4061 (hw 8 (by norm_num))
  have v4023 : σ (.n 4023) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 53) (by norm_num)).2.2
  have v4045 : σ (.n 4045) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 55) (by norm_num)).2.2
  have v4069 : σ (.n 4069) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 56) (by norm_num)).2.2
  have v4080 : σ (.n 4080) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 57) (by norm_num)).2.2
  have v4183 : σ (.n 4183) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 64) (by norm_num)).2.2
  have hB : σ (.n 4267) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([11], 2)], [([], 16)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v4183, v4080, v4069, v4045, v4023, a4065, a4064, a4063, a4062, e4061, a4060, a4059, a4058,
      e4057, a4056, a4055, e4054, a4053, a4052, e4051, a4050, a4049, e4048, a4047, a4046,
      a4045, e4044, a4043, a4042, e4041, a4040, a4039, a4038, a4037, e4036, a4035, a4034,
      e4033]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a4067, a4066, hB]

set_option maxRecDepth 10000 in
theorem vtB04_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4295) = σ (.n 4269) + σ (.n 1116) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([8], 2)], [([5], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4068 [
    .atom (.load (.n 4270) (.n 13) 0),
    .atom (.const (.n 4271) (word 2 0 0)),
    .atom (.mul (.n 4272) (.n 4270) (.n 4271)),
    .atom (.mul (.n 4273) (.n 4034) (.n 4045)),
    .atom (.load (.n 4274) (.n 13) 1),
    .atom (.mul (.n 4275) (.n 4274) (.n 4273)),
    .atom (.add (.n 4276) (.n 4272) (.n 4275)),
    .atom (.const (.n 4277) (word 2 0 0)),
    .atom (.mul (.n 4278) (.n 4277) (.n 4137)),
    .atom (.load (.n 4279) (.n 13) 2),
    .atom (.mul (.n 4280) (.n 4279) (.n 4278)),
    .atom (.add (.n 4281) (.n 4276) (.n 4280)),
    .atom (.load (.n 4282) (.n 13) 3),
    .atom (.mul (.n 4283) (.n 4282) (.n 4091)),
    .atom (.add (.n 4284) (.n 4281) (.n 4283)),
    .atom (.load (.n 4285) (.n 13) 4),
    .atom (.const (.n 4286) (word 0 0 0)),
    .atom (.mul (.n 4287) (.n 4285) (.n 4286)),
    .atom (.add (.n 4288) (.n 4284) (.n 4287)),
    .atom (.load (.n 4289) (.n 13) 5),
    .atom (.const (.n 4290) (word 0 0 0)),
    .atom (.mul (.n 4291) (.n 4289) (.n 4290)),
    .atom (.add (.n 4292) (.n 4288) (.n 4291)),
    .atom (.add (.n 4293) (.n 14) (.n 4292)),
    .atom (.mul (.n 4294) (.n 1116) (.n 4293)),
    .atom (.add (.n 4295) (.n 4269) (.n 4294))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4068, a4069, a4070, a4071, a4072, a4073, a4074, a4075, a4076, a4077, a4078, a4079, a4080, a4081,
    a4082, a4083, a4084, a4085, a4086, a4087, a4088, a4089, a4090, a4091, a4092, a4093, -⟩ := hs
  have e4068 := tb_loadHolds_unique a4068 (hw 0 (by norm_num))
  have e4072 := tb_loadHolds_unique a4072 (hw 1 (by norm_num))
  have e4077 := tb_loadHolds_unique a4077 (hw 2 (by norm_num))
  have e4080 := tb_loadHolds_unique a4080 (hw 3 (by norm_num))
  have e4083 := tb_loadHolds_unique a4083 (hw 4 (by norm_num))
  have e4087 := tb_loadHolds_unique a4087 (hw 5 (by norm_num))
  have v4034 : σ (.n 4034) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 54) (by norm_num)).2.2
  have v4045 : σ (.n 4045) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 55) (by norm_num)).2.2
  have v4091 : σ (.n 4091) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 58) (by norm_num)).2.2
  have v4137 : σ (.n 4137) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 61) (by norm_num)).2.2
  have hB : σ (.n 4293) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([8], 2)], [([5], 1)], [([], 0)], [([], 0)]] := by
    simp only [v4137, v4091, v4045, v4034, a4091, a4090, a4089, a4088, e4087, a4086, a4085, a4084, e4083,
      a4082, a4081, e4080, a4079, a4078, e4077, a4076, a4075, a4074, a4073, e4072, a4071,
      a4070, a4069, e4068]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a4093, a4092, hB]

set_option maxRecDepth 10000 in
theorem vtB04_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4321) = σ (.n 4295) + σ (.n 1125) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([9], 2)], [([6], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4094 [
    .atom (.load (.n 4296) (.n 13) 0),
    .atom (.const (.n 4297) (word 2 0 0)),
    .atom (.mul (.n 4298) (.n 4296) (.n 4297)),
    .atom (.mul (.n 4299) (.n 4034) (.n 4069)),
    .atom (.load (.n 4300) (.n 13) 1),
    .atom (.mul (.n 4301) (.n 4300) (.n 4299)),
    .atom (.add (.n 4302) (.n 4298) (.n 4301)),
    .atom (.const (.n 4303) (word 2 0 0)),
    .atom (.mul (.n 4304) (.n 4303) (.n 4148)),
    .atom (.load (.n 4305) (.n 13) 2),
    .atom (.mul (.n 4306) (.n 4305) (.n 4304)),
    .atom (.add (.n 4307) (.n 4302) (.n 4306)),
    .atom (.load (.n 4308) (.n 13) 3),
    .atom (.mul (.n 4309) (.n 4308) (.n 4102)),
    .atom (.add (.n 4310) (.n 4307) (.n 4309)),
    .atom (.load (.n 4311) (.n 13) 4),
    .atom (.const (.n 4312) (word 0 0 0)),
    .atom (.mul (.n 4313) (.n 4311) (.n 4312)),
    .atom (.add (.n 4314) (.n 4310) (.n 4313)),
    .atom (.load (.n 4315) (.n 13) 5),
    .atom (.const (.n 4316) (word 0 0 0)),
    .atom (.mul (.n 4317) (.n 4315) (.n 4316)),
    .atom (.add (.n 4318) (.n 4314) (.n 4317)),
    .atom (.add (.n 4319) (.n 14) (.n 4318)),
    .atom (.mul (.n 4320) (.n 1125) (.n 4319)),
    .atom (.add (.n 4321) (.n 4295) (.n 4320))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4094, a4095, a4096, a4097, a4098, a4099, a4100, a4101, a4102, a4103, a4104, a4105, a4106, a4107,
    a4108, a4109, a4110, a4111, a4112, a4113, a4114, a4115, a4116, a4117, a4118, a4119, -⟩ := hs
  have e4094 := tb_loadHolds_unique a4094 (hw 0 (by norm_num))
  have e4098 := tb_loadHolds_unique a4098 (hw 1 (by norm_num))
  have e4103 := tb_loadHolds_unique a4103 (hw 2 (by norm_num))
  have e4106 := tb_loadHolds_unique a4106 (hw 3 (by norm_num))
  have e4109 := tb_loadHolds_unique a4109 (hw 4 (by norm_num))
  have e4113 := tb_loadHolds_unique a4113 (hw 5 (by norm_num))
  have v4034 : σ (.n 4034) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 54) (by norm_num)).2.2
  have v4069 : σ (.n 4069) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 56) (by norm_num)).2.2
  have v4102 : σ (.n 4102) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 59) (by norm_num)).2.2
  have v4148 : σ (.n 4148) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have hB : σ (.n 4319) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([9], 2)], [([6], 1)], [([], 0)], [([], 0)]] := by
    simp only [v4148, v4102, v4069, v4034, a4117, a4116, a4115, a4114, e4113, a4112, a4111, a4110, e4109,
      a4108, a4107, e4106, a4105, a4104, e4103, a4102, a4101, a4100, a4099, e4098, a4097,
      a4096, a4095, e4094]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a4119, a4118, hB]

set_option maxRecDepth 10000 in
theorem vtB04_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4347) = σ (.n 4321) + σ (.n 1134) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([10], 2)], [([7], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4120 [
    .atom (.load (.n 4322) (.n 13) 0),
    .atom (.const (.n 4323) (word 2 0 0)),
    .atom (.mul (.n 4324) (.n 4322) (.n 4323)),
    .atom (.mul (.n 4325) (.n 4034) (.n 4080)),
    .atom (.load (.n 4326) (.n 13) 1),
    .atom (.mul (.n 4327) (.n 4326) (.n 4325)),
    .atom (.add (.n 4328) (.n 4324) (.n 4327)),
    .atom (.const (.n 4329) (word 2 0 0)),
    .atom (.mul (.n 4330) (.n 4329) (.n 4159)),
    .atom (.load (.n 4331) (.n 13) 2),
    .atom (.mul (.n 4332) (.n 4331) (.n 4330)),
    .atom (.add (.n 4333) (.n 4328) (.n 4332)),
    .atom (.load (.n 4334) (.n 13) 3),
    .atom (.mul (.n 4335) (.n 4334) (.n 4126)),
    .atom (.add (.n 4336) (.n 4333) (.n 4335)),
    .atom (.load (.n 4337) (.n 13) 4),
    .atom (.const (.n 4338) (word 0 0 0)),
    .atom (.mul (.n 4339) (.n 4337) (.n 4338)),
    .atom (.add (.n 4340) (.n 4336) (.n 4339)),
    .atom (.load (.n 4341) (.n 13) 5),
    .atom (.const (.n 4342) (word 0 0 0)),
    .atom (.mul (.n 4343) (.n 4341) (.n 4342)),
    .atom (.add (.n 4344) (.n 4340) (.n 4343)),
    .atom (.add (.n 4345) (.n 14) (.n 4344)),
    .atom (.mul (.n 4346) (.n 1134) (.n 4345)),
    .atom (.add (.n 4347) (.n 4321) (.n 4346))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4120, a4121, a4122, a4123, a4124, a4125, a4126, a4127, a4128, a4129, a4130, a4131, a4132, a4133,
    a4134, a4135, a4136, a4137, a4138, a4139, a4140, a4141, a4142, a4143, a4144, a4145, -⟩ := hs
  have e4120 := tb_loadHolds_unique a4120 (hw 0 (by norm_num))
  have e4124 := tb_loadHolds_unique a4124 (hw 1 (by norm_num))
  have e4129 := tb_loadHolds_unique a4129 (hw 2 (by norm_num))
  have e4132 := tb_loadHolds_unique a4132 (hw 3 (by norm_num))
  have e4135 := tb_loadHolds_unique a4135 (hw 4 (by norm_num))
  have e4139 := tb_loadHolds_unique a4139 (hw 5 (by norm_num))
  have v4034 : σ (.n 4034) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 54) (by norm_num)).2.2
  have v4080 : σ (.n 4080) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 57) (by norm_num)).2.2
  have v4126 : σ (.n 4126) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 60) (by norm_num)).2.2
  have v4159 : σ (.n 4159) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 63) (by norm_num)).2.2
  have hB : σ (.n 4345) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([10], 2)], [([7], 1)], [([], 0)], [([], 0)]] := by
    simp only [v4159, v4126, v4080, v4034, a4143, a4142, a4141, a4140, e4139, a4138, a4137, a4136, e4135,
      a4134, a4133, e4132, a4131, a4130, e4129, a4128, a4127, a4126, a4125, e4124, a4123,
      a4122, a4121, e4120]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a4145, a4144, hB]

set_option maxRecDepth 10000 in
theorem vtSide04F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4347) =
      vtSideVal [σ (.n 1098), σ (.n 1107), σ (.n 1116), σ (.n 1125), σ (.n 1134)]
        (σ (.n 14)) W ev vtBTerms04 := by
  rw [vtB04_4F h hw hev, vtB04_3F h hw hev, vtB04_2F h hw hev, vtB04_1F h hw hev, vtB04_0F h hw hev]
  simp only [vtSideVal, vtBTerms04, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD4_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4366) = σ (.n 1988) * vtSlots W ev 0
      [[], [([0], 3), ([0, 13], 2), ([6, 13], 1)], [([1, 13], 1), ([7, 13], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4148 [
    .atom (.const (.n 4350) (word 3 0 0)),
    .atom (.mul (.n 4351) (.n 4350) (.n 4023)),
    .atom (.const (.n 4352) (word 2 0 0)),
    .atom (.mul (.n 4353) (.n 4023) (.n 4205)),
    .atom (.mul (.n 4354) (.n 4352) (.n 4353)),
    .atom (.add (.n 4355) (.n 4351) (.n 4354)),
    .atom (.mul (.n 4356) (.n 4102) (.n 4205)),
    .atom (.add (.n 4357) (.n 4355) (.n 4356)),
    .atom (.load (.n 4358) (.n 13) 1),
    .atom (.mul (.n 4359) (.n 4358) (.n 4357)),
    .atom (.mul (.n 4360) (.n 4034) (.n 4205)),
    .atom (.mul (.n 4361) (.n 4126) (.n 4205)),
    .atom (.add (.n 4362) (.n 4360) (.n 4361)),
    .atom (.load (.n 4363) (.n 13) 2),
    .atom (.mul (.n 4364) (.n 4363) (.n 4362)),
    .atom (.add (.n 4365) (.n 4359) (.n 4364)),
    .atom (.mul (.n 4366) (.n 1988) (.n 4365))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4148, a4149, a4150, a4151, a4152, a4153, a4154, a4155, a4156, a4157, a4158, a4159, a4160, a4161,
    a4162, a4163, a4164, -⟩ := hs
  have e4156 := tb_loadHolds_unique a4156 (hw 1 (by norm_num))
  have e4161 := tb_loadHolds_unique a4161 (hw 2 (by norm_num))
  have v4023 : σ (.n 4023) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 53) (by norm_num)).2.2
  have v4034 : σ (.n 4034) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 54) (by norm_num)).2.2
  have v4102 : σ (.n 4102) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 59) (by norm_num)).2.2
  have v4126 : σ (.n 4126) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 60) (by norm_num)).2.2
  have v4205 : σ (.n 4205) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 66) (by norm_num)).2.2
  have hB : σ (.n 4365) = vtSlots W ev 0 [[], [([0], 3), ([0, 13], 2), ([6, 13], 1)], [([1, 13], 1), ([7, 13], 1)]] := by
    simp only [v4205, v4126, v4102, v4034, v4023, a4163, a4162, e4161, a4160, a4159, a4158, a4157, e4156,
      a4155, a4154, a4153, a4152, a4151, a4150, a4149, a4148]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4164, hB]

set_option maxRecDepth 10000 in
theorem vtD4_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4372) = σ (.n 4366) + σ (.n 1990) * vtSlots W ev 0
      [[], [], [([11], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4165 [
    .atom (.const (.n 4367) (word 3 0 0)),
    .atom (.mul (.n 4368) (.n 4367) (.n 4183)),
    .atom (.load (.n 4369) (.n 13) 2),
    .atom (.mul (.n 4370) (.n 4369) (.n 4368)),
    .atom (.mul (.n 4371) (.n 1990) (.n 4370)),
    .atom (.add (.n 4372) (.n 4366) (.n 4371))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4165, a4166, a4167, a4168, a4169, a4170, -⟩ := hs
  have e4167 := tb_loadHolds_unique a4167 (hw 2 (by norm_num))
  have v4183 : σ (.n 4183) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 64) (by norm_num)).2.2
  have hB : σ (.n 4370) = vtSlots W ev 0 [[], [], [([11], 3)], [], [], [], [], [], []] := by
    simp only [v4183, a4168, e4167, a4166, a4165]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a4170, a4169, hB]

set_option maxRecDepth 10000 in
theorem vtD4_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4378) = σ (.n 4372) + σ (.n 1992) * vtSlots W ev 0
      [[], [], [([8], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4171 [
    .atom (.const (.n 4373) (word 3 0 0)),
    .atom (.mul (.n 4374) (.n 4373) (.n 4137)),
    .atom (.load (.n 4375) (.n 13) 2),
    .atom (.mul (.n 4376) (.n 4375) (.n 4374)),
    .atom (.mul (.n 4377) (.n 1992) (.n 4376)),
    .atom (.add (.n 4378) (.n 4372) (.n 4377))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4171, a4172, a4173, a4174, a4175, a4176, -⟩ := hs
  have e4173 := tb_loadHolds_unique a4173 (hw 2 (by norm_num))
  have v4137 : σ (.n 4137) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 61) (by norm_num)).2.2
  have hB : σ (.n 4376) = vtSlots W ev 0 [[], [], [([8], 3)], [], [], []] := by
    simp only [v4137, a4174, e4173, a4172, a4171]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a4176, a4175, hB]

set_option maxRecDepth 10000 in
theorem vtD4_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4384) = σ (.n 4378) + σ (.n 1994) * vtSlots W ev 0
      [[], [], [([9], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4177 [
    .atom (.const (.n 4379) (word 3 0 0)),
    .atom (.mul (.n 4380) (.n 4379) (.n 4148)),
    .atom (.load (.n 4381) (.n 13) 2),
    .atom (.mul (.n 4382) (.n 4381) (.n 4380)),
    .atom (.mul (.n 4383) (.n 1994) (.n 4382)),
    .atom (.add (.n 4384) (.n 4378) (.n 4383))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4177, a4178, a4179, a4180, a4181, a4182, -⟩ := hs
  have e4179 := tb_loadHolds_unique a4179 (hw 2 (by norm_num))
  have v4148 : σ (.n 4148) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have hB : σ (.n 4382) = vtSlots W ev 0 [[], [], [([9], 3)], [], [], []] := by
    simp only [v4148, a4180, e4179, a4178, a4177]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a4182, a4181, hB]

set_option maxRecDepth 10000 in
theorem vtD4_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4390) = σ (.n 4384) + σ (.n 1996) * vtSlots W ev 0
      [[], [], [([10], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4183 [
    .atom (.const (.n 4385) (word 3 0 0)),
    .atom (.mul (.n 4386) (.n 4385) (.n 4159)),
    .atom (.load (.n 4387) (.n 13) 2),
    .atom (.mul (.n 4388) (.n 4387) (.n 4386)),
    .atom (.mul (.n 4389) (.n 1996) (.n 4388)),
    .atom (.add (.n 4390) (.n 4384) (.n 4389))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4183, a4184, a4185, a4186, a4187, a4188, -⟩ := hs
  have e4185 := tb_loadHolds_unique a4185 (hw 2 (by norm_num))
  have v4159 : σ (.n 4159) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 63) (by norm_num)).2.2
  have hB : σ (.n 4388) = vtSlots W ev 0 [[], [], [([10], 3)], [], [], []] := by
    simp only [v4159, a4186, e4185, a4184, a4183]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a4188, a4187, hB]

set_option maxRecDepth 10000 in
theorem vtSide14F {rd : Reader} {σ : Val} (h : VtF rd σ)
    (hq : [σ (.n 1988), σ (.n 1990), σ (.n 1992), σ (.n 1994), σ (.n 1996)] = [σ (.n 1098), σ (.n 1107), σ (.n 1116), σ (.n 1125), σ (.n 1134)]) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4391) =
      vtSideVal [σ (.n 1988), σ (.n 1990), σ (.n 1992), σ (.n 1994), σ (.n 1996)]
        (σ (.n 14)) W ev vtBTerms14 := by
  have hF0 : σ (.n 4347) =
      vtSideVal [σ (.n 1988), σ (.n 1990), σ (.n 1992), σ (.n 1994), σ (.n 1996)]
        (σ (.n 14)) W ev vtBTerms04 := by
    rw [hq]; exact vtSide04F h hw hev
  have a4189 := h.atomAt 4189 (.add (.n 4391) (.n 4347) (.n 4390)) (by decide +kernel)
  simp only [Atom.Holds] at a4189
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull4, ← hF0, a4189, vtD4_4F h hw hev, vtD4_3F h hw hev, vtD4_2F h hw hev, vtD4_1F h hw hev, vtD4_0F h hw hev]
  simp only [vtDiffSum, vtDTerms4, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide24F {rd : Reader} {σ : Val} (h : VtF rd σ) {ev : ℕ → E}
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4400) =
      vtSideVal [σ (.n 2175), σ (.n 2184), σ (.n 2193), σ (.n 2202)]
        (0) (fun _ ↦ 1) ev vtBTerms24 := by
  obtain ⟨_, hs⟩ := h.sliceAt 4192 [
    .atom (.mul (.n 4394) (.n 2175) (.n 4137)),
    .atom (.mul (.n 4395) (.n 2184) (.n 4148)),
    .atom (.add (.n 4396) (.n 4394) (.n 4395)),
    .atom (.mul (.n 4397) (.n 2193) (.n 4159)),
    .atom (.add (.n 4398) (.n 4396) (.n 4397)),
    .atom (.mul (.n 4399) (.n 2202) (.n 4183)),
    .atom (.add (.n 4400) (.n 4398) (.n 4399))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4192, a4193, a4194, a4195, a4196, a4197, a4198, -⟩ := hs
  have v4137 : σ (.n 4137) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 61) (by norm_num)).2.2
  have v4148 : σ (.n 4148) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4159 : σ (.n 4159) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 63) (by norm_num)).2.2
  have v4183 : σ (.n 4183) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 64) (by norm_num)).2.2
  rw [a4198, a4196, a4194, a4192, a4193, a4195, a4197, v4137, v4148, v4159, v4183]
  simp only [vtSideVal, vtBTerms24, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
