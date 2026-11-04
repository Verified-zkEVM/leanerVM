/-
  LeanVM.Guest.B1.Tables.Vt.Air

  `verify_tables`' air check: each table's weight and form value, and their sum the table
  sumcheck's final claim.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsVal
public import LeanVM.Guest.B1.Tables.Vt.Pi

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
/-- Table 0's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[2]`), times
its form value. -/
theorem vtAir0 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2500) = σ (.n 2980) * σ (.n 30) ∧
      LoadHolds rd (σ (.n 2592) * σ (.n 2980)) 0 (σ (.n 2982)) ∧
      LoadHolds rd (σ (.n 2613) * σ (.n 30)) 0 (σ (.n 2984)) ∧
      σ (.n 2986) = σ (.n 2982) * σ (.n 2984) *
        (((σ (.n 2575) * σ (.n 2937)) + (σ (.n 2576) * σ (.n 2968))) + (σ (.n 2577) * σ (.n 2977))) := by
  have a2986 := h.atomAt 2986 (.mul (.n 2500) (.n 2980) (.n 30)) (by decide +kernel)
  have a2987 := h.atomAt 2987 (.mul (.n 2981) (.n 2592) (.n 2980)) (by decide +kernel)
  have a2988 := h.atomAt 2988 (.load (.n 2982) (.n 2981) 0) (by decide +kernel)
  have a2989 := h.atomAt 2989 (.mul (.n 2983) (.n 2613) (.n 30)) (by decide +kernel)
  have a2990 := h.atomAt 2990 (.load (.n 2984) (.n 2983) 0) (by decide +kernel)
  have a2991 := h.atomAt 2991 (.mul (.n 2985) (.n 2982) (.n 2984)) (by decide +kernel)
  have a2992 := h.atomAt 2992 (.mul (.n 2986) (.n 2985) (.n 2979)) (by decide +kernel)
  have a2944 := h.atomAt 2944 (.mul (.n 2938) (.n 2575) (.n 2937)) (by decide +kernel)
  have a2975 := h.atomAt 2975 (.mul (.n 2969) (.n 2576) (.n 2968)) (by decide +kernel)
  have a2976 := h.atomAt 2976 (.add (.n 2970) (.n 2938) (.n 2969)) (by decide +kernel)
  have a2984 := h.atomAt 2984 (.mul (.n 2978) (.n 2577) (.n 2977)) (by decide +kernel)
  have a2985 := h.atomAt 2985 (.add (.n 2979) (.n 2970) (.n 2978)) (by decide +kernel)
  simp only [Atom.Holds] at a2986 a2987 a2988 a2989 a2990 a2991 a2992 a2944 a2975 a2976 a2984 a2985
  refine ⟨a2986, by rw [← a2987]; exact a2988, by rw [← a2989]; exact a2990, ?_⟩
  rw [a2992, a2991, a2985, a2984, a2976, a2975, a2944]

set_option maxRecDepth 10000 in
/-- Table 1's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[3]`), times
its form value. -/
theorem vtAir1 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2500) = σ (.n 3385) * σ (.n 31) ∧
      LoadHolds rd (σ (.n 2592) * σ (.n 3385)) 0 (σ (.n 3387)) ∧
      LoadHolds rd (σ (.n 2613) * σ (.n 31)) 0 (σ (.n 3389)) ∧
      σ (.n 3391) = σ (.n 3387) * σ (.n 3389) *
        (((σ (.n 2575) * σ (.n 3342)) + (σ (.n 2576) * σ (.n 3373))) + (σ (.n 2577) * σ (.n 3382))) := by
  have a3328 := h.atomAt 3328 (.mul (.n 2500) (.n 3385) (.n 31)) (by decide +kernel)
  have a3329 := h.atomAt 3329 (.mul (.n 3386) (.n 2592) (.n 3385)) (by decide +kernel)
  have a3330 := h.atomAt 3330 (.load (.n 3387) (.n 3386) 0) (by decide +kernel)
  have a3331 := h.atomAt 3331 (.mul (.n 3388) (.n 2613) (.n 31)) (by decide +kernel)
  have a3332 := h.atomAt 3332 (.load (.n 3389) (.n 3388) 0) (by decide +kernel)
  have a3333 := h.atomAt 3333 (.mul (.n 3390) (.n 3387) (.n 3389)) (by decide +kernel)
  have a3334 := h.atomAt 3334 (.mul (.n 3391) (.n 3390) (.n 3384)) (by decide +kernel)
  have a3286 := h.atomAt 3286 (.mul (.n 3343) (.n 2575) (.n 3342)) (by decide +kernel)
  have a3317 := h.atomAt 3317 (.mul (.n 3374) (.n 2576) (.n 3373)) (by decide +kernel)
  have a3318 := h.atomAt 3318 (.add (.n 3375) (.n 3343) (.n 3374)) (by decide +kernel)
  have a3326 := h.atomAt 3326 (.mul (.n 3383) (.n 2577) (.n 3382)) (by decide +kernel)
  have a3327 := h.atomAt 3327 (.add (.n 3384) (.n 3375) (.n 3383)) (by decide +kernel)
  simp only [Atom.Holds] at a3328 a3329 a3330 a3331 a3332 a3333 a3334 a3286 a3317 a3318 a3326 a3327
  refine ⟨a3328, by rw [← a3329]; exact a3330, by rw [← a3331]; exact a3332, ?_⟩
  rw [a3334, a3333, a3327, a3326, a3318, a3317, a3286]

set_option maxRecDepth 10000 in
/-- Table 2's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[4]`), times
its form value. -/
theorem vtAir2 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2500) = σ (.n 3602) * σ (.n 32) ∧
      LoadHolds rd (σ (.n 2592) * σ (.n 3602)) 0 (σ (.n 3604)) ∧
      LoadHolds rd (σ (.n 2613) * σ (.n 32)) 0 (σ (.n 3606)) ∧
      σ (.n 3608) = σ (.n 3604) * σ (.n 3606) *
        (((σ (.n 2575) * σ (.n 3575)) + (σ (.n 2576) * σ (.n 3594))) + (σ (.n 2577) * σ (.n 3599))) := by
  have a3513 := h.atomAt 3513 (.mul (.n 2500) (.n 3602) (.n 32)) (by decide +kernel)
  have a3514 := h.atomAt 3514 (.mul (.n 3603) (.n 2592) (.n 3602)) (by decide +kernel)
  have a3515 := h.atomAt 3515 (.load (.n 3604) (.n 3603) 0) (by decide +kernel)
  have a3516 := h.atomAt 3516 (.mul (.n 3605) (.n 2613) (.n 32)) (by decide +kernel)
  have a3517 := h.atomAt 3517 (.load (.n 3606) (.n 3605) 0) (by decide +kernel)
  have a3518 := h.atomAt 3518 (.mul (.n 3607) (.n 3604) (.n 3606)) (by decide +kernel)
  have a3519 := h.atomAt 3519 (.mul (.n 3608) (.n 3607) (.n 3601)) (by decide +kernel)
  have a3487 := h.atomAt 3487 (.mul (.n 3576) (.n 2575) (.n 3575)) (by decide +kernel)
  have a3506 := h.atomAt 3506 (.mul (.n 3595) (.n 2576) (.n 3594)) (by decide +kernel)
  have a3507 := h.atomAt 3507 (.add (.n 3596) (.n 3576) (.n 3595)) (by decide +kernel)
  have a3511 := h.atomAt 3511 (.mul (.n 3600) (.n 2577) (.n 3599)) (by decide +kernel)
  have a3512 := h.atomAt 3512 (.add (.n 3601) (.n 3596) (.n 3600)) (by decide +kernel)
  simp only [Atom.Holds] at a3513 a3514 a3515 a3516 a3517 a3518 a3519 a3487 a3506 a3507 a3511 a3512
  refine ⟨a3513, by rw [← a3514]; exact a3515, by rw [← a3516]; exact a3517, ?_⟩
  rw [a3519, a3518, a3512, a3511, a3507, a3506, a3487]

set_option maxRecDepth 10000 in
/-- Table 3's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[5]`), times
its form value. -/
theorem vtAir3 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2500) = σ (.n 4005) * σ (.n 33) ∧
      LoadHolds rd (σ (.n 2592) * σ (.n 4005)) 0 (σ (.n 4007)) ∧
      LoadHolds rd (σ (.n 2613) * σ (.n 33)) 0 (σ (.n 4009)) ∧
      σ (.n 4011) = σ (.n 4007) * σ (.n 4009) *
        (((σ (.n 2575) * σ (.n 3962)) + (σ (.n 2576) * σ (.n 3993))) + (σ (.n 2577) * σ (.n 4002))) := by
  have a3853 := h.atomAt 3853 (.mul (.n 2500) (.n 4005) (.n 33)) (by decide +kernel)
  have a3854 := h.atomAt 3854 (.mul (.n 4006) (.n 2592) (.n 4005)) (by decide +kernel)
  have a3855 := h.atomAt 3855 (.load (.n 4007) (.n 4006) 0) (by decide +kernel)
  have a3856 := h.atomAt 3856 (.mul (.n 4008) (.n 2613) (.n 33)) (by decide +kernel)
  have a3857 := h.atomAt 3857 (.load (.n 4009) (.n 4008) 0) (by decide +kernel)
  have a3858 := h.atomAt 3858 (.mul (.n 4010) (.n 4007) (.n 4009)) (by decide +kernel)
  have a3859 := h.atomAt 3859 (.mul (.n 4011) (.n 4010) (.n 4004)) (by decide +kernel)
  have a3811 := h.atomAt 3811 (.mul (.n 3963) (.n 2575) (.n 3962)) (by decide +kernel)
  have a3842 := h.atomAt 3842 (.mul (.n 3994) (.n 2576) (.n 3993)) (by decide +kernel)
  have a3843 := h.atomAt 3843 (.add (.n 3995) (.n 3963) (.n 3994)) (by decide +kernel)
  have a3851 := h.atomAt 3851 (.mul (.n 4003) (.n 2577) (.n 4002)) (by decide +kernel)
  have a3852 := h.atomAt 3852 (.add (.n 4004) (.n 3995) (.n 4003)) (by decide +kernel)
  simp only [Atom.Holds] at a3853 a3854 a3855 a3856 a3857 a3858 a3859 a3811 a3842 a3843 a3851 a3852
  refine ⟨a3853, by rw [← a3854]; exact a3855, by rw [← a3856]; exact a3857, ?_⟩
  rw [a3859, a3858, a3852, a3851, a3843, a3842, a3811]

set_option maxRecDepth 10000 in
/-- Table 4's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[6]`), times
its form value. -/
theorem vtAir4 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c)
    : σ (.n 2500) = σ (.n 4403) * σ (.n 34) ∧
      LoadHolds rd (σ (.n 2592) * σ (.n 4403)) 0 (σ (.n 4405)) ∧
      LoadHolds rd (σ (.n 2613) * σ (.n 34)) 0 (σ (.n 4407)) ∧
      σ (.n 4409) = σ (.n 4405) * σ (.n 4407) *
        (((((σ (.n 2573) * (ev 13 + (ev 5 * ev 12))) + (σ (.n 2574) * (ev 5 * (ev 13 + word 1 0 0)))) + (σ (.n 2575) * σ (.n 4347))) + (σ (.n 2576) * σ (.n 4391))) + (σ (.n 2577) * σ (.n 4400))) := by
  have a4201 := h.atomAt 4201 (.mul (.n 2500) (.n 4403) (.n 34)) (by decide +kernel)
  have a4202 := h.atomAt 4202 (.mul (.n 4404) (.n 2592) (.n 4403)) (by decide +kernel)
  have a4203 := h.atomAt 4203 (.load (.n 4405) (.n 4404) 0) (by decide +kernel)
  have a4204 := h.atomAt 4204 (.mul (.n 4406) (.n 2613) (.n 34)) (by decide +kernel)
  have a4205 := h.atomAt 4205 (.load (.n 4407) (.n 4406) 0) (by decide +kernel)
  have a4206 := h.atomAt 4206 (.mul (.n 4408) (.n 4405) (.n 4407)) (by decide +kernel)
  have a4207 := h.atomAt 4207 (.mul (.n 4409) (.n 4408) (.n 4402)) (by decide +kernel)
  have a4004 := h.atomAt 4004 (.mul (.n 4206) (.n 4091) (.n 4194)) (by decide +kernel)
  have a4005 := h.atomAt 4005 (.add (.n 4207) (.n 4205) (.n 4206)) (by decide +kernel)
  have a4006 := h.atomAt 4006 (.mul (.n 4208) (.n 2573) (.n 4207)) (by decide +kernel)
  have a4007 := h.atomAt 4007 (.const (.n 4209) (word 1 0 0)) (by decide +kernel)
  have a4008 := h.atomAt 4008 (.add (.n 4210) (.n 4205) (.n 4209)) (by decide +kernel)
  have a4009 := h.atomAt 4009 (.mul (.n 4211) (.n 4091) (.n 4210)) (by decide +kernel)
  have a4010 := h.atomAt 4010 (.mul (.n 4212) (.n 2574) (.n 4211)) (by decide +kernel)
  have a4011 := h.atomAt 4011 (.add (.n 4213) (.n 4208) (.n 4212)) (by decide +kernel)
  have a4146 := h.atomAt 4146 (.mul (.n 4348) (.n 2575) (.n 4347)) (by decide +kernel)
  have a4147 := h.atomAt 4147 (.add (.n 4349) (.n 4213) (.n 4348)) (by decide +kernel)
  have a4190 := h.atomAt 4190 (.mul (.n 4392) (.n 2576) (.n 4391)) (by decide +kernel)
  have a4191 := h.atomAt 4191 (.add (.n 4393) (.n 4349) (.n 4392)) (by decide +kernel)
  have a4199 := h.atomAt 4199 (.mul (.n 4401) (.n 2577) (.n 4400)) (by decide +kernel)
  have a4200 := h.atomAt 4200 (.add (.n 4402) (.n 4393) (.n 4401)) (by decide +kernel)
  simp only [Atom.Holds] at a4201 a4202 a4203 a4204 a4205 a4206 a4207 a4004 a4005 a4006 a4007 a4008 a4009 a4010 a4011 a4146 a4147 a4190 a4191 a4199 a4200
  have v4091 : σ (.n 4091) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 58) (by norm_num)).2.2
  have v4194 : σ (.n 4194) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 65) (by norm_num)).2.2
  have v4205 : σ (.n 4205) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 66) (by norm_num)).2.2
  refine ⟨a4201, by rw [← a4202]; exact a4203, by rw [← a4204]; exact a4205, ?_⟩
  rw [a4207, a4206, a4200, a4199, a4191, a4190, a4147, a4146, a4011, a4010, a4009, a4008, a4007, a4006, a4005,
    a4004, v4091, v4194, v4205]

set_option maxRecDepth 10000 in
/-- Table 5's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[7]`), times
its form value. -/
theorem vtAir5 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2500) = σ (.n 6810) * σ (.n 35) ∧
      LoadHolds rd (σ (.n 2592) * σ (.n 6810)) 0 (σ (.n 6812)) ∧
      LoadHolds rd (σ (.n 2613) * σ (.n 35)) 0 (σ (.n 6814)) ∧
      σ (.n 6816) = σ (.n 6812) * σ (.n 6814) *
        (((σ (.n 2575) * σ (.n 6583)) + (σ (.n 2576) * σ (.n 6752))) + (σ (.n 2577) * σ (.n 6807))) := by
  have a6242 := h.atomAt 6242 (.mul (.n 2500) (.n 6810) (.n 35)) (by decide +kernel)
  have a6243 := h.atomAt 6243 (.mul (.n 6811) (.n 2592) (.n 6810)) (by decide +kernel)
  have a6244 := h.atomAt 6244 (.load (.n 6812) (.n 6811) 0) (by decide +kernel)
  have a6245 := h.atomAt 6245 (.mul (.n 6813) (.n 2613) (.n 35)) (by decide +kernel)
  have a6246 := h.atomAt 6246 (.load (.n 6814) (.n 6813) 0) (by decide +kernel)
  have a6247 := h.atomAt 6247 (.mul (.n 6815) (.n 6812) (.n 6814)) (by decide +kernel)
  have a6248 := h.atomAt 6248 (.mul (.n 6816) (.n 6815) (.n 6809)) (by decide +kernel)
  have a6016 := h.atomAt 6016 (.mul (.n 6584) (.n 2575) (.n 6583)) (by decide +kernel)
  have a6185 := h.atomAt 6185 (.mul (.n 6753) (.n 2576) (.n 6752)) (by decide +kernel)
  have a6186 := h.atomAt 6186 (.add (.n 6754) (.n 6584) (.n 6753)) (by decide +kernel)
  have a6240 := h.atomAt 6240 (.mul (.n 6808) (.n 2577) (.n 6807)) (by decide +kernel)
  have a6241 := h.atomAt 6241 (.add (.n 6809) (.n 6754) (.n 6808)) (by decide +kernel)
  simp only [Atom.Holds] at a6242 a6243 a6244 a6245 a6246 a6247 a6248 a6016 a6185 a6186 a6240 a6241
  refine ⟨a6242, by rw [← a6243]; exact a6244, by rw [← a6245]; exact a6246, ?_⟩
  rw [a6248, a6247, a6241, a6240, a6186, a6185, a6016]

set_option maxRecDepth 10000 in
/-- **The air check**: the sumcheck's final claim is the six tables' air terms' sum. -/
theorem vt_air_total {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 2610) = σ (.n 2986) + σ (.n 3391) + σ (.n 3608) + σ (.n 4011) + σ (.n 4409) + σ (.n 6816) := by
  have a6249 := h.atomAt 6249 (.add (.n 6817) (.n 4410) (.n 6816)) (by decide +kernel)
  have a4208 := h.atomAt 4208 (.add (.n 4410) (.n 4012) (.n 4409)) (by decide +kernel)
  have a3860 := h.atomAt 3860 (.add (.n 4012) (.n 3609) (.n 4011)) (by decide +kernel)
  have a3520 := h.atomAt 3520 (.add (.n 3609) (.n 3392) (.n 3608)) (by decide +kernel)
  have a3335 := h.atomAt 3335 (.add (.n 3392) (.n 2986) (.n 3391)) (by decide +kernel)
  have a6250 := h.atomAt 6250 (.assertEq (.n 6817) (.n 2610)) (by decide +kernel)
  simp only [Atom.Holds] at a6249 a4208 a3860 a3520 a3335 a6250
  rw [eq_neg_of_add_eq_zero_right a6250, CharTwo.neg_eq, a6249, a4208, a3860, a3520, a3335]

end
end LeanVM.Guest.B1.Tables
