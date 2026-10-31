/-
  LeanVM.Guest.B1.Tables.Vt.PullSels

  The pull side's table block selectors are the push side's, copied.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Base

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vtPullSels0 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 4569), σ (.n 4576), σ (.n 4583), σ (.n 4590), σ (.n 4597)] =
      [σ (.n 3051), σ (.n 3066), σ (.n 3081), σ (.n 3096), σ (.n 3111)] := by
  have a4049 := h.atomAt 4049 (.copy (.n 4569) (.n 3051)) (by decide +kernel)
  have a4054 := h.atomAt 4054 (.copy (.n 4576) (.n 3066)) (by decide +kernel)
  have a4059 := h.atomAt 4059 (.copy (.n 4583) (.n 3081)) (by decide +kernel)
  have a4064 := h.atomAt 4064 (.copy (.n 4590) (.n 3096)) (by decide +kernel)
  have a4069 := h.atomAt 4069 (.copy (.n 4597) (.n 3111)) (by decide +kernel)
  simp only [Atom.Holds] at a4049 a4054 a4059 a4064 a4069
  rw [a4049, a4054, a4059, a4064, a4069]

theorem vtPullSels1 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 4604), σ (.n 4611), σ (.n 4618), σ (.n 4625), σ (.n 4632)] =
      [σ (.n 3130), σ (.n 3149), σ (.n 3168), σ (.n 3187), σ (.n 3206)] := by
  have a4074 := h.atomAt 4074 (.copy (.n 4604) (.n 3130)) (by decide +kernel)
  have a4079 := h.atomAt 4079 (.copy (.n 4611) (.n 3149)) (by decide +kernel)
  have a4084 := h.atomAt 4084 (.copy (.n 4618) (.n 3168)) (by decide +kernel)
  have a4089 := h.atomAt 4089 (.copy (.n 4625) (.n 3187)) (by decide +kernel)
  have a4094 := h.atomAt 4094 (.copy (.n 4632) (.n 3206)) (by decide +kernel)
  simp only [Atom.Holds] at a4074 a4079 a4084 a4089 a4094
  rw [a4074, a4079, a4084, a4089, a4094]

theorem vtPullSels2 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 4639), σ (.n 4646), σ (.n 4653)] =
      [σ (.n 3225), σ (.n 3244), σ (.n 3263)] := by
  have a4099 := h.atomAt 4099 (.copy (.n 4639) (.n 3225)) (by decide +kernel)
  have a4104 := h.atomAt 4104 (.copy (.n 4646) (.n 3244)) (by decide +kernel)
  have a4109 := h.atomAt 4109 (.copy (.n 4653) (.n 3263)) (by decide +kernel)
  simp only [Atom.Holds] at a4099 a4104 a4109
  rw [a4099, a4104, a4109]

theorem vtPullSels3 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 4660), σ (.n 4667), σ (.n 4674), σ (.n 4681), σ (.n 4688)] =
      [σ (.n 3282), σ (.n 3301), σ (.n 3320), σ (.n 3339), σ (.n 3358)] := by
  have a4114 := h.atomAt 4114 (.copy (.n 4660) (.n 3282)) (by decide +kernel)
  have a4119 := h.atomAt 4119 (.copy (.n 4667) (.n 3301)) (by decide +kernel)
  have a4124 := h.atomAt 4124 (.copy (.n 4674) (.n 3320)) (by decide +kernel)
  have a4129 := h.atomAt 4129 (.copy (.n 4681) (.n 3339)) (by decide +kernel)
  have a4134 := h.atomAt 4134 (.copy (.n 4688) (.n 3358)) (by decide +kernel)
  simp only [Atom.Holds] at a4114 a4119 a4124 a4129 a4134
  rw [a4114, a4119, a4124, a4129, a4134]

theorem vtPullSels4 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 4695), σ (.n 4702), σ (.n 4709), σ (.n 4716), σ (.n 4723)] =
      [σ (.n 3377), σ (.n 3396), σ (.n 3415), σ (.n 3434), σ (.n 3453)] := by
  have a4139 := h.atomAt 4139 (.copy (.n 4695) (.n 3377)) (by decide +kernel)
  have a4144 := h.atomAt 4144 (.copy (.n 4702) (.n 3396)) (by decide +kernel)
  have a4149 := h.atomAt 4149 (.copy (.n 4709) (.n 3415)) (by decide +kernel)
  have a4154 := h.atomAt 4154 (.copy (.n 4716) (.n 3434)) (by decide +kernel)
  have a4159 := h.atomAt 4159 (.copy (.n 4723) (.n 3453)) (by decide +kernel)
  simp only [Atom.Holds] at a4139 a4144 a4149 a4154 a4159
  rw [a4139, a4144, a4149, a4154, a4159]

theorem vtPullSels5 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 4730), σ (.n 4737), σ (.n 4744), σ (.n 4751), σ (.n 4758), σ (.n 4765), σ (.n 4772), σ (.n 4779), σ (.n 4786), σ (.n 4793), σ (.n 4800), σ (.n 4807), σ (.n 4814), σ (.n 4821), σ (.n 4828), σ (.n 4835), σ (.n 4842), σ (.n 4849), σ (.n 4856), σ (.n 4863), σ (.n 4870), σ (.n 4877), σ (.n 4884), σ (.n 4891), σ (.n 4898), σ (.n 4905), σ (.n 4912), σ (.n 4919)] =
      [σ (.n 3472), σ (.n 3491), σ (.n 3510), σ (.n 3529), σ (.n 3548), σ (.n 3567), σ (.n 3586), σ (.n 3605), σ (.n 3624), σ (.n 3643), σ (.n 3662), σ (.n 3681), σ (.n 3700), σ (.n 3719), σ (.n 3738), σ (.n 3757), σ (.n 3776), σ (.n 3795), σ (.n 3814), σ (.n 3833), σ (.n 3852), σ (.n 3871), σ (.n 3890), σ (.n 3909), σ (.n 3928), σ (.n 3947), σ (.n 3966), σ (.n 3985)] := by
  have a4164 := h.atomAt 4164 (.copy (.n 4730) (.n 3472)) (by decide +kernel)
  have a4169 := h.atomAt 4169 (.copy (.n 4737) (.n 3491)) (by decide +kernel)
  have a4174 := h.atomAt 4174 (.copy (.n 4744) (.n 3510)) (by decide +kernel)
  have a4179 := h.atomAt 4179 (.copy (.n 4751) (.n 3529)) (by decide +kernel)
  have a4184 := h.atomAt 4184 (.copy (.n 4758) (.n 3548)) (by decide +kernel)
  have a4189 := h.atomAt 4189 (.copy (.n 4765) (.n 3567)) (by decide +kernel)
  have a4194 := h.atomAt 4194 (.copy (.n 4772) (.n 3586)) (by decide +kernel)
  have a4199 := h.atomAt 4199 (.copy (.n 4779) (.n 3605)) (by decide +kernel)
  have a4204 := h.atomAt 4204 (.copy (.n 4786) (.n 3624)) (by decide +kernel)
  have a4209 := h.atomAt 4209 (.copy (.n 4793) (.n 3643)) (by decide +kernel)
  have a4214 := h.atomAt 4214 (.copy (.n 4800) (.n 3662)) (by decide +kernel)
  have a4219 := h.atomAt 4219 (.copy (.n 4807) (.n 3681)) (by decide +kernel)
  have a4224 := h.atomAt 4224 (.copy (.n 4814) (.n 3700)) (by decide +kernel)
  have a4229 := h.atomAt 4229 (.copy (.n 4821) (.n 3719)) (by decide +kernel)
  have a4234 := h.atomAt 4234 (.copy (.n 4828) (.n 3738)) (by decide +kernel)
  have a4239 := h.atomAt 4239 (.copy (.n 4835) (.n 3757)) (by decide +kernel)
  have a4244 := h.atomAt 4244 (.copy (.n 4842) (.n 3776)) (by decide +kernel)
  have a4249 := h.atomAt 4249 (.copy (.n 4849) (.n 3795)) (by decide +kernel)
  have a4254 := h.atomAt 4254 (.copy (.n 4856) (.n 3814)) (by decide +kernel)
  have a4259 := h.atomAt 4259 (.copy (.n 4863) (.n 3833)) (by decide +kernel)
  have a4264 := h.atomAt 4264 (.copy (.n 4870) (.n 3852)) (by decide +kernel)
  have a4269 := h.atomAt 4269 (.copy (.n 4877) (.n 3871)) (by decide +kernel)
  have a4274 := h.atomAt 4274 (.copy (.n 4884) (.n 3890)) (by decide +kernel)
  have a4279 := h.atomAt 4279 (.copy (.n 4891) (.n 3909)) (by decide +kernel)
  have a4284 := h.atomAt 4284 (.copy (.n 4898) (.n 3928)) (by decide +kernel)
  have a4289 := h.atomAt 4289 (.copy (.n 4905) (.n 3947)) (by decide +kernel)
  have a4294 := h.atomAt 4294 (.copy (.n 4912) (.n 3966)) (by decide +kernel)
  have a4299 := h.atomAt 4299 (.copy (.n 4919) (.n 3985)) (by decide +kernel)
  simp only [Atom.Holds] at a4164 a4169 a4174 a4179 a4184 a4189 a4194 a4199 a4204 a4209 a4214 a4219 a4224 a4229 a4234 a4239 a4244 a4249 a4254 a4259 a4264 a4269 a4274 a4279 a4284 a4289 a4294 a4299
  rw [a4164, a4169, a4174, a4179, a4184, a4189, a4194, a4199, a4204, a4209, a4214, a4219, a4224, a4229, a4234, a4239, a4244, a4249, a4254, a4259, a4264, a4269, a4274, a4279, a4284, a4289, a4294, a4299]

end
end LeanVM.Guest.B1.Tables
