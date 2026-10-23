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
/-- Table 0's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ`, times its form value. -/
theorem vtAir0 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 5817) = σ (.n 6383) * σ (.n 5938) ∧ LoadHolds rd (σ (.n 10)) 1 (σ (.n 5938)) ∧
      LoadHolds rd (σ (.n 5915) * σ (.n 6383)) 0 (σ (.n 6385)) ∧
      LoadHolds rd (σ (.n 5936) * σ (.n 5938)) 0 (σ (.n 6387)) ∧
      σ (.n 6389) = σ (.n 6385) * σ (.n 6387) *
        (((σ (.n 5898) * σ (.n 6261)) + (σ (.n 5899) * σ (.n 6371))) + (σ (.n 5900) * σ (.n 6380))) := by
  have a5683 := h.atom 5683 (.mul (.n 5817) (.n 6383) (.n 5938)) (by decide +kernel)
  have a5259 := h.atom 5259 (.load (.n 5938) (.n 10) 1) (by decide +kernel)
  have a5684 := h.atom 5684 (.mul (.n 6384) (.n 5915) (.n 6383)) (by decide +kernel)
  have a5685 := h.atom 5685 (.load (.n 6385) (.n 6384) 0) (by decide +kernel)
  have a5686 := h.atom 5686 (.mul (.n 6386) (.n 5936) (.n 5938)) (by decide +kernel)
  have a5687 := h.atom 5687 (.load (.n 6387) (.n 6386) 0) (by decide +kernel)
  have a5688 := h.atom 5688 (.mul (.n 6388) (.n 6385) (.n 6387)) (by decide +kernel)
  have a5689 := h.atom 5689 (.mul (.n 6389) (.n 6388) (.n 6382)) (by decide +kernel)
  have a5562 := h.atom 5562 (.mul (.n 6262) (.n 5898) (.n 6261)) (by decide +kernel)
  have a5672 := h.atom 5672 (.mul (.n 6372) (.n 5899) (.n 6371)) (by decide +kernel)
  have a5673 := h.atom 5673 (.add (.n 6373) (.n 6262) (.n 6372)) (by decide +kernel)
  have a5681 := h.atom 5681 (.mul (.n 6381) (.n 5900) (.n 6380)) (by decide +kernel)
  have a5682 := h.atom 5682 (.add (.n 6382) (.n 6373) (.n 6381)) (by decide +kernel)
  simp only [Atom.Holds] at a5683 a5259 a5684 a5685 a5686 a5687 a5688 a5689 a5562 a5672 a5673 a5681 a5682
  refine ⟨a5683, a5259, by rw [← a5684]; exact a5685, by rw [← a5686]; exact a5687, ?_⟩
  rw [a5689, a5688, a5682, a5681, a5673, a5672, a5562]

set_option maxRecDepth 10000 in
/-- Table 1's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ`, times its form value. -/
theorem vtAir1 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 5817) = σ (.n 6888) * σ (.n 6390) ∧ LoadHolds rd (σ (.n 10)) 2 (σ (.n 6390)) ∧
      LoadHolds rd (σ (.n 5915) * σ (.n 6888)) 0 (σ (.n 6890)) ∧
      LoadHolds rd (σ (.n 5936) * σ (.n 6390)) 0 (σ (.n 6892)) ∧
      σ (.n 6894) = σ (.n 6890) * σ (.n 6892) *
        (((σ (.n 5898) * σ (.n 6746)) + (σ (.n 5899) * σ (.n 6876))) + (σ (.n 5900) * σ (.n 6885))) := by
  have a6155 := h.atom 6155 (.mul (.n 5817) (.n 6888) (.n 6390)) (by decide +kernel)
  have a5690 := h.atom 5690 (.load (.n 6390) (.n 10) 2) (by decide +kernel)
  have a6156 := h.atom 6156 (.mul (.n 6889) (.n 5915) (.n 6888)) (by decide +kernel)
  have a6157 := h.atom 6157 (.load (.n 6890) (.n 6889) 0) (by decide +kernel)
  have a6158 := h.atom 6158 (.mul (.n 6891) (.n 5936) (.n 6390)) (by decide +kernel)
  have a6159 := h.atom 6159 (.load (.n 6892) (.n 6891) 0) (by decide +kernel)
  have a6160 := h.atom 6160 (.mul (.n 6893) (.n 6890) (.n 6892)) (by decide +kernel)
  have a6161 := h.atom 6161 (.mul (.n 6894) (.n 6893) (.n 6887)) (by decide +kernel)
  have a6014 := h.atom 6014 (.mul (.n 6747) (.n 5898) (.n 6746)) (by decide +kernel)
  have a6144 := h.atom 6144 (.mul (.n 6877) (.n 5899) (.n 6876)) (by decide +kernel)
  have a6145 := h.atom 6145 (.add (.n 6878) (.n 6747) (.n 6877)) (by decide +kernel)
  have a6153 := h.atom 6153 (.mul (.n 6886) (.n 5900) (.n 6885)) (by decide +kernel)
  have a6154 := h.atom 6154 (.add (.n 6887) (.n 6878) (.n 6886)) (by decide +kernel)
  simp only [Atom.Holds] at a6155 a5690 a6156 a6157 a6158 a6159 a6160 a6161 a6014 a6144 a6145 a6153 a6154
  refine ⟨a6155, a5690, by rw [← a6156]; exact a6157, by rw [← a6158]; exact a6159, ?_⟩
  rw [a6161, a6160, a6154, a6153, a6145, a6144, a6014]

set_option maxRecDepth 10000 in
/-- Table 2's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ`, times its form value. -/
theorem vtAir2 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 5817) = σ (.n 7151) * σ (.n 6896) ∧ LoadHolds rd (σ (.n 10)) 3 (σ (.n 6896)) ∧
      LoadHolds rd (σ (.n 5915) * σ (.n 7151)) 0 (σ (.n 7153)) ∧
      LoadHolds rd (σ (.n 5936) * σ (.n 6896)) 0 (σ (.n 7155)) ∧
      σ (.n 7157) = σ (.n 7153) * σ (.n 7155) *
        (((σ (.n 5898) * σ (.n 7079)) + (σ (.n 5899) * σ (.n 7143))) + (σ (.n 5900) * σ (.n 7148))) := by
  have a6402 := h.atom 6402 (.mul (.n 5817) (.n 7151) (.n 6896)) (by decide +kernel)
  have a6163 := h.atom 6163 (.load (.n 6896) (.n 10) 3) (by decide +kernel)
  have a6403 := h.atom 6403 (.mul (.n 7152) (.n 5915) (.n 7151)) (by decide +kernel)
  have a6404 := h.atom 6404 (.load (.n 7153) (.n 7152) 0) (by decide +kernel)
  have a6405 := h.atom 6405 (.mul (.n 7154) (.n 5936) (.n 6896)) (by decide +kernel)
  have a6406 := h.atom 6406 (.load (.n 7155) (.n 7154) 0) (by decide +kernel)
  have a6407 := h.atom 6407 (.mul (.n 7156) (.n 7153) (.n 7155)) (by decide +kernel)
  have a6408 := h.atom 6408 (.mul (.n 7157) (.n 7156) (.n 7150)) (by decide +kernel)
  have a6331 := h.atom 6331 (.mul (.n 7080) (.n 5898) (.n 7079)) (by decide +kernel)
  have a6395 := h.atom 6395 (.mul (.n 7144) (.n 5899) (.n 7143)) (by decide +kernel)
  have a6396 := h.atom 6396 (.add (.n 7145) (.n 7080) (.n 7144)) (by decide +kernel)
  have a6400 := h.atom 6400 (.mul (.n 7149) (.n 5900) (.n 7148)) (by decide +kernel)
  have a6401 := h.atom 6401 (.add (.n 7150) (.n 7145) (.n 7149)) (by decide +kernel)
  simp only [Atom.Holds] at a6402 a6163 a6403 a6404 a6405 a6406 a6407 a6408 a6331 a6395 a6396 a6400 a6401
  refine ⟨a6402, a6163, by rw [← a6403]; exact a6404, by rw [← a6405]; exact a6406, ?_⟩
  rw [a6408, a6407, a6401, a6400, a6396, a6395, a6331]

set_option maxRecDepth 10000 in
/-- Table 3's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ`, times its form value. -/
theorem vtAir3 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 5817) = σ (.n 7651) * σ (.n 7159) ∧ LoadHolds rd (σ (.n 10)) 4 (σ (.n 7159)) ∧
      LoadHolds rd (σ (.n 5915) * σ (.n 7651)) 0 (σ (.n 7653)) ∧
      LoadHolds rd (σ (.n 5936) * σ (.n 7159)) 0 (σ (.n 7655)) ∧
      σ (.n 7657) = σ (.n 7653) * σ (.n 7655) *
        (((σ (.n 5898) * σ (.n 7512)) + (σ (.n 5899) * σ (.n 7639))) + (σ (.n 5900) * σ (.n 7648))) := by
  have a6869 := h.atom 6869 (.mul (.n 5817) (.n 7651) (.n 7159)) (by decide +kernel)
  have a6410 := h.atom 6410 (.load (.n 7159) (.n 10) 4) (by decide +kernel)
  have a6870 := h.atom 6870 (.mul (.n 7652) (.n 5915) (.n 7651)) (by decide +kernel)
  have a6871 := h.atom 6871 (.load (.n 7653) (.n 7652) 0) (by decide +kernel)
  have a6872 := h.atom 6872 (.mul (.n 7654) (.n 5936) (.n 7159)) (by decide +kernel)
  have a6873 := h.atom 6873 (.load (.n 7655) (.n 7654) 0) (by decide +kernel)
  have a6874 := h.atom 6874 (.mul (.n 7656) (.n 7653) (.n 7655)) (by decide +kernel)
  have a6875 := h.atom 6875 (.mul (.n 7657) (.n 7656) (.n 7650)) (by decide +kernel)
  have a6731 := h.atom 6731 (.mul (.n 7513) (.n 5898) (.n 7512)) (by decide +kernel)
  have a6858 := h.atom 6858 (.mul (.n 7640) (.n 5899) (.n 7639)) (by decide +kernel)
  have a6859 := h.atom 6859 (.add (.n 7641) (.n 7513) (.n 7640)) (by decide +kernel)
  have a6867 := h.atom 6867 (.mul (.n 7649) (.n 5900) (.n 7648)) (by decide +kernel)
  have a6868 := h.atom 6868 (.add (.n 7650) (.n 7641) (.n 7649)) (by decide +kernel)
  simp only [Atom.Holds] at a6869 a6410 a6870 a6871 a6872 a6873 a6874 a6875 a6731 a6858 a6859 a6867 a6868
  refine ⟨a6869, a6410, by rw [← a6870]; exact a6871, by rw [← a6872]; exact a6873, ?_⟩
  rw [a6875, a6874, a6868, a6867, a6859, a6858, a6731]

set_option maxRecDepth 10000 in
/-- Table 4's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ`, times its form value. -/
theorem vtAir4 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c)
    : σ (.n 5817) = σ (.n 8122) * σ (.n 7659) ∧ LoadHolds rd (σ (.n 10)) 5 (σ (.n 7659)) ∧
      LoadHolds rd (σ (.n 5915) * σ (.n 8122)) 0 (σ (.n 8124)) ∧
      LoadHolds rd (σ (.n 5936) * σ (.n 7659)) 0 (σ (.n 8126)) ∧
      σ (.n 8128) = σ (.n 8124) * σ (.n 8126) *
        (((((σ (.n 5896) * (ev 13 + (ev 5 * ev 12))) + (σ (.n 5897) * (ev 5 * (ev 13 + word 1 0 0)))) + (σ (.n 5898) * σ (.n 7994))) + (σ (.n 5899) * σ (.n 8110))) + (σ (.n 5900) * σ (.n 8119))) := by
  have a7318 := h.atom 7318 (.mul (.n 5817) (.n 8122) (.n 7659)) (by decide +kernel)
  have a6877 := h.atom 6877 (.load (.n 7659) (.n 10) 5) (by decide +kernel)
  have a7319 := h.atom 7319 (.mul (.n 8123) (.n 5915) (.n 8122)) (by decide +kernel)
  have a7320 := h.atom 7320 (.load (.n 8124) (.n 8123) 0) (by decide +kernel)
  have a7321 := h.atom 7321 (.mul (.n 8125) (.n 5936) (.n 7659)) (by decide +kernel)
  have a7322 := h.atom 7322 (.load (.n 8126) (.n 8125) 0) (by decide +kernel)
  have a7323 := h.atom 7323 (.mul (.n 8127) (.n 8124) (.n 8126)) (by decide +kernel)
  have a7324 := h.atom 7324 (.mul (.n 8128) (.n 8127) (.n 8121)) (by decide +kernel)
  have a7049 := h.atom 7049 (.mul (.n 7853) (.n 7738) (.n 7841)) (by decide +kernel)
  have a7050 := h.atom 7050 (.add (.n 7854) (.n 7852) (.n 7853)) (by decide +kernel)
  have a7051 := h.atom 7051 (.mul (.n 7855) (.n 5896) (.n 7854)) (by decide +kernel)
  have a7052 := h.atom 7052 (.const (.n 7856) (word 1 0 0)) (by decide +kernel)
  have a7053 := h.atom 7053 (.add (.n 7857) (.n 7852) (.n 7856)) (by decide +kernel)
  have a7054 := h.atom 7054 (.mul (.n 7858) (.n 7738) (.n 7857)) (by decide +kernel)
  have a7055 := h.atom 7055 (.mul (.n 7859) (.n 5897) (.n 7858)) (by decide +kernel)
  have a7056 := h.atom 7056 (.add (.n 7860) (.n 7855) (.n 7859)) (by decide +kernel)
  have a7191 := h.atom 7191 (.mul (.n 7995) (.n 5898) (.n 7994)) (by decide +kernel)
  have a7192 := h.atom 7192 (.add (.n 7996) (.n 7860) (.n 7995)) (by decide +kernel)
  have a7307 := h.atom 7307 (.mul (.n 8111) (.n 5899) (.n 8110)) (by decide +kernel)
  have a7308 := h.atom 7308 (.add (.n 8112) (.n 7996) (.n 8111)) (by decide +kernel)
  have a7316 := h.atom 7316 (.mul (.n 8120) (.n 5900) (.n 8119)) (by decide +kernel)
  have a7317 := h.atom 7317 (.add (.n 8121) (.n 8112) (.n 8120)) (by decide +kernel)
  simp only [Atom.Holds] at a7318 a6877 a7319 a7320 a7321 a7322 a7323 a7324 a7049 a7050 a7051 a7052 a7053 a7054 a7055 a7056 a7191 a7192 a7307 a7308 a7316 a7317
  have v7738 : σ (.n 7738) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 58) (by norm_num)).2.2.1
  have v7841 : σ (.n 7841) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 65) (by norm_num)).2.2.1
  have v7852 : σ (.n 7852) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 66) (by norm_num)).2.2.1
  refine ⟨a7318, a6877, by rw [← a7319]; exact a7320, by rw [← a7321]; exact a7322, ?_⟩
  rw [a7324, a7323, a7317, a7316, a7308, a7307, a7192, a7191, a7056, a7055, a7054, a7053, a7052, a7051, a7050,
    a7049, v7738, v7841, v7852]

set_option maxRecDepth 10000 in
/-- Table 5's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ`, times its form value. -/
theorem vtAir5 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 5817) = σ (.n 11190) * σ (.n 8130) ∧ LoadHolds rd (σ (.n 10)) 6 (σ (.n 8130)) ∧
      LoadHolds rd (σ (.n 5915) * σ (.n 11190)) 0 (σ (.n 11192)) ∧
      LoadHolds rd (σ (.n 5936) * σ (.n 8130)) 0 (σ (.n 11194)) ∧
      σ (.n 11196) = σ (.n 11192) * σ (.n 11194) *
        (((σ (.n 5898) * σ (.n 10303)) + (σ (.n 5899) * σ (.n 11132))) + (σ (.n 5900) * σ (.n 11187))) := by
  have a10200 := h.atom 10200 (.mul (.n 5817) (.n 11190) (.n 8130)) (by decide +kernel)
  have a7326 := h.atom 7326 (.load (.n 8130) (.n 10) 6) (by decide +kernel)
  have a10201 := h.atom 10201 (.mul (.n 11191) (.n 5915) (.n 11190)) (by decide +kernel)
  have a10202 := h.atom 10202 (.load (.n 11192) (.n 11191) 0) (by decide +kernel)
  have a10203 := h.atom 10203 (.mul (.n 11193) (.n 5936) (.n 8130)) (by decide +kernel)
  have a10204 := h.atom 10204 (.load (.n 11194) (.n 11193) 0) (by decide +kernel)
  have a10205 := h.atom 10205 (.mul (.n 11195) (.n 11192) (.n 11194)) (by decide +kernel)
  have a10206 := h.atom 10206 (.mul (.n 11196) (.n 11195) (.n 11189)) (by decide +kernel)
  have a9314 := h.atom 9314 (.mul (.n 10304) (.n 5898) (.n 10303)) (by decide +kernel)
  have a10143 := h.atom 10143 (.mul (.n 11133) (.n 5899) (.n 11132)) (by decide +kernel)
  have a10144 := h.atom 10144 (.add (.n 11134) (.n 10304) (.n 11133)) (by decide +kernel)
  have a10198 := h.atom 10198 (.mul (.n 11188) (.n 5900) (.n 11187)) (by decide +kernel)
  have a10199 := h.atom 10199 (.add (.n 11189) (.n 11134) (.n 11188)) (by decide +kernel)
  simp only [Atom.Holds] at a10200 a7326 a10201 a10202 a10203 a10204 a10205 a10206 a9314 a10143 a10144 a10198 a10199
  refine ⟨a10200, a7326, by rw [← a10201]; exact a10202, by rw [← a10203]; exact a10204, ?_⟩
  rw [a10206, a10205, a10199, a10198, a10144, a10143, a9314]

set_option maxRecDepth 10000 in
/-- **The air check**: the sumcheck's final claim is the six tables' air terms' sum. -/
theorem vt_air_total {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 5933) = σ (.n 6389) + σ (.n 6894) + σ (.n 7157) + σ (.n 7657) + σ (.n 8128) + σ (.n 11196) := by
  have a10207 := h.atom 10207 (.add (.n 11197) (.n 8129) (.n 11196)) (by decide +kernel)
  have a7325 := h.atom 7325 (.add (.n 8129) (.n 7658) (.n 8128)) (by decide +kernel)
  have a6876 := h.atom 6876 (.add (.n 7658) (.n 7158) (.n 7657)) (by decide +kernel)
  have a6409 := h.atom 6409 (.add (.n 7158) (.n 6895) (.n 7157)) (by decide +kernel)
  have a6162 := h.atom 6162 (.add (.n 6895) (.n 6389) (.n 6894)) (by decide +kernel)
  have a10208 := h.atom 10208 (.assertEq (.n 11197) (.n 5933)) (by decide +kernel)
  simp only [Atom.Holds] at a10207 a7325 a6876 a6409 a6162 a10208
  rw [eq_neg_of_add_eq_zero_right a10208, CharTwo.neg_eq, a10207, a7325, a6876, a6409, a6162]

end
end LeanVM.Guest.B1.Tables
