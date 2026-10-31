/-
  LeanVM.Guest.B1.Tables.Vt.PullTotal

  `verify_tables`' pull side total: its framework blocks' fingerprints (with the final memory and
  bytecode counts), the push side's padding sum, the selector sum and the GKR pull value.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.PushFw

/-!
# The pull side's total (G:2041-2043, 2128-2132)

The pull side's blocks mirror the push side's: their eq weights are the push blocks' copies, and
their padding sum is the push side's. `vt_pull_total`: `bus_table_total[PULL]`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `g^(2^19 - 1)`, the final `pc`, as the data writes it. -/
abbrev vtWFinalPc : E := word 12261764870545049476 0 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The pull side's total.** -/
theorem vt_pull_total {rd : Reader} {σ : Val} (h : VtH rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 14)) i (W i)) :
    σ (.n 4924) = σ (.n 2873) * (σ (.n 15) + (W 0 + W 1 * vtWFinalPc + W 2)) +
      σ (.n 2904) * (σ (.n 15) + (W 0 * gen + W 1 * σ (.n 4440) + W 2 * σ (.n 4444) +
        W 3 * σ (.n 4457) + W 4 * σ (.n 4461) + W 5 * σ (.n 4465))) +
      σ (.n 2979) * (σ (.n 15) + (W 0 * gen ^ 2 + W 1 * σ (.n 4485) + W 2 * σ (.n 4502) +
        σ (.n 2639))) + σ (.n 4406) +
      (1 + (σ (.n 2873) + σ (.n 2904) + σ (.n 2979) +
        (vtPushPadData.map fun x ↦ σ (.n x.2.2.1)).sum)) + σ (.n 28) := by
  have a3914 := h.atomAt 3914 (.load (.n 4418) (.n 14) 0) (by decide +kernel)
  have a3915 := h.atomAt 3915 (.load (.n 4419) (.n 14) 1) (by decide +kernel)
  have a3916 := h.atomAt 3916 (.const (.n 4420) (word 12261764870545049476 0 0)) (by decide +kernel)
  have a3917 := h.atomAt 3917 (.mul (.n 4421) (.n 4419) (.n 4420)) (by decide +kernel)
  have a3918 := h.atomAt 3918 (.add (.n 4422) (.n 4418) (.n 4421)) (by decide +kernel)
  have a3919 := h.atomAt 3919 (.load (.n 4423) (.n 14) 2) (by decide +kernel)
  have a3920 := h.atomAt 3920 (.add (.n 4424) (.n 4422) (.n 4423)) (by decide +kernel)
  have a3921 := h.atomAt 3921 (.const (.n 4425) (word 0 0 0)) (by decide +kernel)
  have a3922 := h.atomAt 3922 (.mul (.n 4426) (.n 4425) (.n 2639)) (by decide +kernel)
  have a3923 := h.atomAt 3923 (.add (.n 4427) (.n 4424) (.n 4426)) (by decide +kernel)
  have a3924 := h.atomAt 3924 (.add (.n 4428) (.n 15) (.n 4427)) (by decide +kernel)
  have a3925 := h.atomAt 3925 (.mul (.n 4429) (.n 2873) (.n 4428)) (by decide +kernel)
  have a3929 := h.atomAt 3929 (.add (.n 4435) (.n 2873) (.n 2904)) (by decide +kernel)
  have a3931 := h.atomAt 3931 (.load (.n 4437) (.n 14) 0) (by decide +kernel)
  have a3932 := h.atomAt 3932 (.const (.n 4438) (word 2 0 0)) (by decide +kernel)
  have a3933 := h.atomAt 3933 (.mul (.n 4439) (.n 4437) (.n 4438)) (by decide +kernel)
  have a3935 := h.atomAt 3935 (.load (.n 4441) (.n 14) 1) (by decide +kernel)
  have a3936 := h.atomAt 3936 (.mul (.n 4442) (.n 4441) (.n 4440)) (by decide +kernel)
  have a3937 := h.atomAt 3937 (.add (.n 4443) (.n 4439) (.n 4442)) (by decide +kernel)
  have a3949 := h.atomAt 3949 (.load (.n 4454) (.n 14) 2) (by decide +kernel)
  have a3950 := h.atomAt 3950 (.mul (.n 4455) (.n 4454) (.n 4444)) (by decide +kernel)
  have a3951 := h.atomAt 3951 (.add (.n 4456) (.n 4443) (.n 4455)) (by decide +kernel)
  have a3953 := h.atomAt 3953 (.load (.n 4458) (.n 14) 3) (by decide +kernel)
  have a3954 := h.atomAt 3954 (.mul (.n 4459) (.n 4458) (.n 4457)) (by decide +kernel)
  have a3955 := h.atomAt 3955 (.add (.n 4460) (.n 4456) (.n 4459)) (by decide +kernel)
  have a3957 := h.atomAt 3957 (.load (.n 4462) (.n 14) 4) (by decide +kernel)
  have a3958 := h.atomAt 3958 (.mul (.n 4463) (.n 4462) (.n 4461)) (by decide +kernel)
  have a3959 := h.atomAt 3959 (.add (.n 4464) (.n 4460) (.n 4463)) (by decide +kernel)
  have a3961 := h.atomAt 3961 (.load (.n 4466) (.n 14) 5) (by decide +kernel)
  have a3962 := h.atomAt 3962 (.mul (.n 4467) (.n 4466) (.n 4465)) (by decide +kernel)
  have a3963 := h.atomAt 3963 (.add (.n 4468) (.n 4464) (.n 4467)) (by decide +kernel)
  have a3964 := h.atomAt 3964 (.const (.n 4469) (word 0 0 0)) (by decide +kernel)
  have a3965 := h.atomAt 3965 (.mul (.n 4470) (.n 4469) (.n 2639)) (by decide +kernel)
  have a3966 := h.atomAt 3966 (.add (.n 4471) (.n 4468) (.n 4470)) (by decide +kernel)
  have a3967 := h.atomAt 3967 (.add (.n 4472) (.n 15) (.n 4471)) (by decide +kernel)
  have a3968 := h.atomAt 3968 (.mul (.n 4473) (.n 2904) (.n 4472)) (by decide +kernel)
  have a3969 := h.atomAt 3969 (.add (.n 4474) (.n 4429) (.n 4473)) (by decide +kernel)
  have a3973 := h.atomAt 3973 (.add (.n 4480) (.n 4435) (.n 2979)) (by decide +kernel)
  have a3975 := h.atomAt 3975 (.load (.n 4482) (.n 14) 0) (by decide +kernel)
  have a3976 := h.atomAt 3976 (.const (.n 4483) (word 4 0 0)) (by decide +kernel)
  have a3977 := h.atomAt 3977 (.mul (.n 4484) (.n 4482) (.n 4483)) (by decide +kernel)
  have a3979 := h.atomAt 3979 (.load (.n 4486) (.n 14) 1) (by decide +kernel)
  have a3980 := h.atomAt 3980 (.mul (.n 4487) (.n 4486) (.n 4485)) (by decide +kernel)
  have a3981 := h.atomAt 3981 (.add (.n 4488) (.n 4484) (.n 4487)) (by decide +kernel)
  have a3994 := h.atomAt 3994 (.load (.n 4512) (.n 14) 2) (by decide +kernel)
  have a3995 := h.atomAt 3995 (.mul (.n 4513) (.n 4512) (.n 4502)) (by decide +kernel)
  have a3996 := h.atomAt 3996 (.add (.n 4514) (.n 4488) (.n 4513)) (by decide +kernel)
  have a3997 := h.atomAt 3997 (.load (.n 4515) (.n 14) 3) (by decide +kernel)
  have a3998 := h.atomAt 3998 (.const (.n 4516) (word 0 0 0)) (by decide +kernel)
  have a3999 := h.atomAt 3999 (.mul (.n 4517) (.n 4515) (.n 4516)) (by decide +kernel)
  have a4000 := h.atomAt 4000 (.add (.n 4518) (.n 4514) (.n 4517)) (by decide +kernel)
  have a4001 := h.atomAt 4001 (.load (.n 4519) (.n 14) 4) (by decide +kernel)
  have a4002 := h.atomAt 4002 (.const (.n 4520) (word 0 0 0)) (by decide +kernel)
  have a4003 := h.atomAt 4003 (.mul (.n 4521) (.n 4519) (.n 4520)) (by decide +kernel)
  have a4004 := h.atomAt 4004 (.add (.n 4522) (.n 4518) (.n 4521)) (by decide +kernel)
  have a4005 := h.atomAt 4005 (.load (.n 4523) (.n 14) 5) (by decide +kernel)
  have a4006 := h.atomAt 4006 (.const (.n 4524) (word 0 0 0)) (by decide +kernel)
  have a4007 := h.atomAt 4007 (.mul (.n 4525) (.n 4523) (.n 4524)) (by decide +kernel)
  have a4008 := h.atomAt 4008 (.add (.n 4526) (.n 4522) (.n 4525)) (by decide +kernel)
  have a4009 := h.atomAt 4009 (.load (.n 4527) (.n 14) 6) (by decide +kernel)
  have a4010 := h.atomAt 4010 (.const (.n 4528) (word 0 0 0)) (by decide +kernel)
  have a4011 := h.atomAt 4011 (.mul (.n 4529) (.n 4527) (.n 4528)) (by decide +kernel)
  have a4012 := h.atomAt 4012 (.add (.n 4530) (.n 4526) (.n 4529)) (by decide +kernel)
  have a4013 := h.atomAt 4013 (.load (.n 4531) (.n 14) 7) (by decide +kernel)
  have a4014 := h.atomAt 4014 (.const (.n 4532) (word 0 0 0)) (by decide +kernel)
  have a4015 := h.atomAt 4015 (.mul (.n 4533) (.n 4531) (.n 4532)) (by decide +kernel)
  have a4016 := h.atomAt 4016 (.add (.n 4534) (.n 4530) (.n 4533)) (by decide +kernel)
  have a4017 := h.atomAt 4017 (.load (.n 4535) (.n 14) 8) (by decide +kernel)
  have a4018 := h.atomAt 4018 (.const (.n 4536) (word 0 0 0)) (by decide +kernel)
  have a4019 := h.atomAt 4019 (.mul (.n 4537) (.n 4535) (.n 4536)) (by decide +kernel)
  have a4020 := h.atomAt 4020 (.add (.n 4538) (.n 4534) (.n 4537)) (by decide +kernel)
  have a4021 := h.atomAt 4021 (.load (.n 4539) (.n 14) 9) (by decide +kernel)
  have a4022 := h.atomAt 4022 (.const (.n 4540) (word 0 0 0)) (by decide +kernel)
  have a4023 := h.atomAt 4023 (.mul (.n 4541) (.n 4539) (.n 4540)) (by decide +kernel)
  have a4024 := h.atomAt 4024 (.add (.n 4542) (.n 4538) (.n 4541)) (by decide +kernel)
  have a4025 := h.atomAt 4025 (.load (.n 4543) (.n 14) 10) (by decide +kernel)
  have a4026 := h.atomAt 4026 (.const (.n 4544) (word 0 0 0)) (by decide +kernel)
  have a4027 := h.atomAt 4027 (.mul (.n 4545) (.n 4543) (.n 4544)) (by decide +kernel)
  have a4028 := h.atomAt 4028 (.add (.n 4546) (.n 4542) (.n 4545)) (by decide +kernel)
  have a4029 := h.atomAt 4029 (.load (.n 4547) (.n 14) 11) (by decide +kernel)
  have a4030 := h.atomAt 4030 (.const (.n 4548) (word 0 0 0)) (by decide +kernel)
  have a4031 := h.atomAt 4031 (.mul (.n 4549) (.n 4547) (.n 4548)) (by decide +kernel)
  have a4032 := h.atomAt 4032 (.add (.n 4550) (.n 4546) (.n 4549)) (by decide +kernel)
  have a4033 := h.atomAt 4033 (.load (.n 4551) (.n 14) 12) (by decide +kernel)
  have a4034 := h.atomAt 4034 (.const (.n 4552) (word 0 0 0)) (by decide +kernel)
  have a4035 := h.atomAt 4035 (.mul (.n 4553) (.n 4551) (.n 4552)) (by decide +kernel)
  have a4036 := h.atomAt 4036 (.add (.n 4554) (.n 4550) (.n 4553)) (by decide +kernel)
  have a4037 := h.atomAt 4037 (.load (.n 4555) (.n 14) 13) (by decide +kernel)
  have a4038 := h.atomAt 4038 (.const (.n 4556) (word 0 0 0)) (by decide +kernel)
  have a4039 := h.atomAt 4039 (.mul (.n 4557) (.n 4555) (.n 4556)) (by decide +kernel)
  have a4040 := h.atomAt 4040 (.add (.n 4558) (.n 4554) (.n 4557)) (by decide +kernel)
  have a4041 := h.atomAt 4041 (.add (.n 4559) (.n 4558) (.n 2639)) (by decide +kernel)
  have a4042 := h.atomAt 4042 (.add (.n 4560) (.n 15) (.n 4559)) (by decide +kernel)
  have a4043 := h.atomAt 4043 (.mul (.n 4561) (.n 2979) (.n 4560)) (by decide +kernel)
  have a4044 := h.atomAt 4044 (.add (.n 4562) (.n 4474) (.n 4561)) (by decide +kernel)
  have a4048 := h.atomAt 4048 (.add (.n 4568) (.n 4480) (.n 3051)) (by decide +kernel)
  have a4053 := h.atomAt 4053 (.add (.n 4575) (.n 4568) (.n 3066)) (by decide +kernel)
  have a4058 := h.atomAt 4058 (.add (.n 4582) (.n 4575) (.n 3081)) (by decide +kernel)
  have a4063 := h.atomAt 4063 (.add (.n 4589) (.n 4582) (.n 3096)) (by decide +kernel)
  have a4068 := h.atomAt 4068 (.add (.n 4596) (.n 4589) (.n 3111)) (by decide +kernel)
  have a4073 := h.atomAt 4073 (.add (.n 4603) (.n 4596) (.n 3130)) (by decide +kernel)
  have a4078 := h.atomAt 4078 (.add (.n 4610) (.n 4603) (.n 3149)) (by decide +kernel)
  have a4083 := h.atomAt 4083 (.add (.n 4617) (.n 4610) (.n 3168)) (by decide +kernel)
  have a4088 := h.atomAt 4088 (.add (.n 4624) (.n 4617) (.n 3187)) (by decide +kernel)
  have a4093 := h.atomAt 4093 (.add (.n 4631) (.n 4624) (.n 3206)) (by decide +kernel)
  have a4098 := h.atomAt 4098 (.add (.n 4638) (.n 4631) (.n 3225)) (by decide +kernel)
  have a4103 := h.atomAt 4103 (.add (.n 4645) (.n 4638) (.n 3244)) (by decide +kernel)
  have a4108 := h.atomAt 4108 (.add (.n 4652) (.n 4645) (.n 3263)) (by decide +kernel)
  have a4113 := h.atomAt 4113 (.add (.n 4659) (.n 4652) (.n 3282)) (by decide +kernel)
  have a4118 := h.atomAt 4118 (.add (.n 4666) (.n 4659) (.n 3301)) (by decide +kernel)
  have a4123 := h.atomAt 4123 (.add (.n 4673) (.n 4666) (.n 3320)) (by decide +kernel)
  have a4128 := h.atomAt 4128 (.add (.n 4680) (.n 4673) (.n 3339)) (by decide +kernel)
  have a4133 := h.atomAt 4133 (.add (.n 4687) (.n 4680) (.n 3358)) (by decide +kernel)
  have a4138 := h.atomAt 4138 (.add (.n 4694) (.n 4687) (.n 3377)) (by decide +kernel)
  have a4143 := h.atomAt 4143 (.add (.n 4701) (.n 4694) (.n 3396)) (by decide +kernel)
  have a4148 := h.atomAt 4148 (.add (.n 4708) (.n 4701) (.n 3415)) (by decide +kernel)
  have a4153 := h.atomAt 4153 (.add (.n 4715) (.n 4708) (.n 3434)) (by decide +kernel)
  have a4158 := h.atomAt 4158 (.add (.n 4722) (.n 4715) (.n 3453)) (by decide +kernel)
  have a4163 := h.atomAt 4163 (.add (.n 4729) (.n 4722) (.n 3472)) (by decide +kernel)
  have a4168 := h.atomAt 4168 (.add (.n 4736) (.n 4729) (.n 3491)) (by decide +kernel)
  have a4173 := h.atomAt 4173 (.add (.n 4743) (.n 4736) (.n 3510)) (by decide +kernel)
  have a4178 := h.atomAt 4178 (.add (.n 4750) (.n 4743) (.n 3529)) (by decide +kernel)
  have a4183 := h.atomAt 4183 (.add (.n 4757) (.n 4750) (.n 3548)) (by decide +kernel)
  have a4188 := h.atomAt 4188 (.add (.n 4764) (.n 4757) (.n 3567)) (by decide +kernel)
  have a4193 := h.atomAt 4193 (.add (.n 4771) (.n 4764) (.n 3586)) (by decide +kernel)
  have a4198 := h.atomAt 4198 (.add (.n 4778) (.n 4771) (.n 3605)) (by decide +kernel)
  have a4203 := h.atomAt 4203 (.add (.n 4785) (.n 4778) (.n 3624)) (by decide +kernel)
  have a4208 := h.atomAt 4208 (.add (.n 4792) (.n 4785) (.n 3643)) (by decide +kernel)
  have a4213 := h.atomAt 4213 (.add (.n 4799) (.n 4792) (.n 3662)) (by decide +kernel)
  have a4218 := h.atomAt 4218 (.add (.n 4806) (.n 4799) (.n 3681)) (by decide +kernel)
  have a4223 := h.atomAt 4223 (.add (.n 4813) (.n 4806) (.n 3700)) (by decide +kernel)
  have a4228 := h.atomAt 4228 (.add (.n 4820) (.n 4813) (.n 3719)) (by decide +kernel)
  have a4233 := h.atomAt 4233 (.add (.n 4827) (.n 4820) (.n 3738)) (by decide +kernel)
  have a4238 := h.atomAt 4238 (.add (.n 4834) (.n 4827) (.n 3757)) (by decide +kernel)
  have a4243 := h.atomAt 4243 (.add (.n 4841) (.n 4834) (.n 3776)) (by decide +kernel)
  have a4248 := h.atomAt 4248 (.add (.n 4848) (.n 4841) (.n 3795)) (by decide +kernel)
  have a4253 := h.atomAt 4253 (.add (.n 4855) (.n 4848) (.n 3814)) (by decide +kernel)
  have a4258 := h.atomAt 4258 (.add (.n 4862) (.n 4855) (.n 3833)) (by decide +kernel)
  have a4263 := h.atomAt 4263 (.add (.n 4869) (.n 4862) (.n 3852)) (by decide +kernel)
  have a4268 := h.atomAt 4268 (.add (.n 4876) (.n 4869) (.n 3871)) (by decide +kernel)
  have a4273 := h.atomAt 4273 (.add (.n 4883) (.n 4876) (.n 3890)) (by decide +kernel)
  have a4278 := h.atomAt 4278 (.add (.n 4890) (.n 4883) (.n 3909)) (by decide +kernel)
  have a4283 := h.atomAt 4283 (.add (.n 4897) (.n 4890) (.n 3928)) (by decide +kernel)
  have a4288 := h.atomAt 4288 (.add (.n 4904) (.n 4897) (.n 3947)) (by decide +kernel)
  have a4293 := h.atomAt 4293 (.add (.n 4911) (.n 4904) (.n 3966)) (by decide +kernel)
  have a4298 := h.atomAt 4298 (.add (.n 4918) (.n 4911) (.n 3985)) (by decide +kernel)
  have a4300 := h.atomAt 4300 (.add (.n 4920) (.n 4562) (.n 4406)) (by decide +kernel)
  have a4301 := h.atomAt 4301 (.const (.n 4921) (word 1 0 0)) (by decide +kernel)
  have a4302 := h.atomAt 4302 (.add (.n 4922) (.n 4921) (.n 4918)) (by decide +kernel)
  have a4303 := h.atomAt 4303 (.add (.n 4923) (.n 4920) (.n 4922)) (by decide +kernel)
  have a4304 := h.atomAt 4304 (.add (.n 4924) (.n 4923) (.n 28)) (by decide +kernel)
  have e3914 := tb_loadHolds_unique a3914 (hw 0 (by norm_num))
  have e3915 := tb_loadHolds_unique a3915 (hw 1 (by norm_num))
  have e3919 := tb_loadHolds_unique a3919 (hw 2 (by norm_num))
  have e3931 := tb_loadHolds_unique a3931 (hw 0 (by norm_num))
  have e3935 := tb_loadHolds_unique a3935 (hw 1 (by norm_num))
  have e3949 := tb_loadHolds_unique a3949 (hw 2 (by norm_num))
  have e3953 := tb_loadHolds_unique a3953 (hw 3 (by norm_num))
  have e3957 := tb_loadHolds_unique a3957 (hw 4 (by norm_num))
  have e3961 := tb_loadHolds_unique a3961 (hw 5 (by norm_num))
  have e3975 := tb_loadHolds_unique a3975 (hw 0 (by norm_num))
  have e3979 := tb_loadHolds_unique a3979 (hw 1 (by norm_num))
  have e3994 := tb_loadHolds_unique a3994 (hw 2 (by norm_num))
  have e3997 := tb_loadHolds_unique a3997 (hw 3 (by norm_num))
  have e4001 := tb_loadHolds_unique a4001 (hw 4 (by norm_num))
  have e4005 := tb_loadHolds_unique a4005 (hw 5 (by norm_num))
  have e4009 := tb_loadHolds_unique a4009 (hw 6 (by norm_num))
  have e4013 := tb_loadHolds_unique a4013 (hw 7 (by norm_num))
  have e4017 := tb_loadHolds_unique a4017 (hw 8 (by norm_num))
  have e4021 := tb_loadHolds_unique a4021 (hw 9 (by norm_num))
  have e4025 := tb_loadHolds_unique a4025 (hw 10 (by norm_num))
  have e4029 := tb_loadHolds_unique a4029 (hw 11 (by norm_num))
  have e4033 := tb_loadHolds_unique a4033 (hw 12 (by norm_num))
  have e4037 := tb_loadHolds_unique a4037 (hw 13 (by norm_num))
  simp only [Atom.Holds] at a3916 a3917 a3918 a3920 a3921 a3922 a3923 a3924 a3925 a3929
  simp only [Atom.Holds] at a3932 a3933 a3936 a3937 a3950 a3951 a3954 a3955 a3958 a3959
  simp only [Atom.Holds] at a3962 a3963 a3964 a3965 a3966 a3967 a3968 a3969 a3973 a3976
  simp only [Atom.Holds] at a3977 a3980 a3981 a3995 a3996 a3998 a3999 a4000 a4002 a4003
  simp only [Atom.Holds] at a4004 a4006 a4007 a4008 a4010 a4011 a4012 a4014 a4015 a4016
  simp only [Atom.Holds] at a4018 a4019 a4020 a4022 a4023 a4024 a4026 a4027 a4028 a4030
  simp only [Atom.Holds] at a4031 a4032 a4034 a4035 a4036 a4038 a4039 a4040 a4041 a4042
  simp only [Atom.Holds] at a4043 a4044 a4048 a4053 a4058 a4063 a4068 a4073 a4078 a4083
  simp only [Atom.Holds] at a4088 a4093 a4098 a4103 a4108 a4113 a4118 a4123 a4128 a4133
  simp only [Atom.Holds] at a4138 a4143 a4148 a4153 a4158 a4163 a4168 a4173 a4178 a4183
  simp only [Atom.Holds] at a4188 a4193 a4198 a4203 a4208 a4213 a4218 a4223 a4228 a4233
  simp only [Atom.Holds] at a4238 a4243 a4248 a4253 a4258 a4263 a4268 a4273 a4278 a4283
  simp only [Atom.Holds] at a4288 a4293 a4298 a4300 a4301 a4302 a4303 a4304
  simp only [e3914, e3915, a3916, a3917, a3918, e3919, a3920, a3921, a3922, a3923, a3924, a3925, a3929,
    e3931, a3932, a3933, e3935, a3936, a3937, e3949, a3950, a3951, e3953, a3954, a3955, e3957,
    a3958, a3959, e3961, a3962, a3963, a3964, a3965, a3966, a3967, a3968, a3969, a3973, e3975,
    a3976, a3977, e3979, a3980, a3981, e3994, a3995, a3996, e3997, a3998, a3999, a4000, e4001,
    a4002, a4003, a4004, e4005, a4006, a4007, a4008, e4009, a4010, a4011, a4012, e4013, a4014,
    a4015, a4016, e4017, a4018, a4019, a4020, e4021, a4022, a4023, a4024, e4025, a4026, a4027,
    a4028, e4029, a4030, a4031, a4032, e4033, a4034, a4035, a4036, e4037, a4038, a4039, a4040,
    a4041, a4042, a4043, a4044, a4048, a4053, a4058, a4063, a4068, a4073, a4078, a4083, a4088,
    a4093, a4098, a4103, a4108, a4113, a4118, a4123, a4128, a4133, a4138, a4143, a4148, a4153,
    a4158, a4163, a4168, a4173, a4178, a4183, a4188, a4193, a4198, a4203, a4208, a4213, a4218,
    a4223, a4228, a4233, a4238, a4243, a4248, a4253, a4258, a4263, a4268, a4273, a4278, a4283,
    a4288, a4293, a4298, a4300, a4301, a4302, a4303, a4304]
  simp only [vtPushPadData, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [tb_word_zero, tb_word_one, tb_word_gen, show (4 : ℕ) = 2 ^ 2 by norm_num,
    tb_word_two_pow (by norm_num)]
  ring

end
end LeanVM.Guest.B1.Tables
