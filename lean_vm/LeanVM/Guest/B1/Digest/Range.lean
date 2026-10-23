/-
  LeanVM.Guest.B1.Digest.Range

  Range checks on a memory image, the compile-time powers of `g` the guest bounds them by, and B1
  for `list_split` (G:3812-3824; TRIAGE #87) and `cover_da_root` (G:4078-4083; TRIAGE #95).
-/

module

public import LeanVM.Guest.B1.Digest.Lists

/-!
# Range checks; `list_split`, `cover_da_root`

On a memory image of `2^κ` words, `16 ≤ κ ≤ 32` (`MemOk`), a word read through a pointer at
offset `0` is a power of `g` below `2^32` (`load_gpow`), so a range check
`rangeCheck x y t1 t2 k` makes `x = g^e`, `k = g^(e + e')` (`rc_sound`): against a compile-time
`g^c` it bounds `e ≤ c` (`rc_const`), against a runtime bound `b · g⁻¹` it gives `BelowLog b e`
(`rc_below`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Range checks on a memory image -/

/-- A word read at offset `0` through a pointer of the memory is a power of `g` below `2^32`. -/
theorem load_gpow {rd : Reader} (hm : MemOk rd) {x t : E} (h : LoadHolds rd x 0 t) :
    ∃ e < 2 ^ 32, x = gen ^ e := by
  obtain ⟨κ, -, hκ, L, rfl⟩ := hm
  obtain ⟨hx, hr⟩ := h
  rw [Parameters.gpow, pow_zero, mul_one] at hr
  obtain ⟨i, hi, -⟩ := (read_some_iff (by omega) L _ _).mp hr
  refine ⟨i, lt_of_lt_of_le i.2 (Nat.pow_le_pow_right (by decide) hκ), ?_⟩
  rw [eq_ofK_limb hx, hi, gen_pow_eq_ofK]

theorem gen_pow_inj' {a b : ℕ} (ha : a < 2 ^ 34) (hb : b < 2 ^ 34) (h : gen ^ a = gen ^ b) :
    a = b :=
  gen_pow_inj (by omega) (by omega) h

/-- A range check: its two reads make `x`, `y` powers of `g` below `2^32`, `k` their product. -/
theorem rc_sound {rd : Reader} (hm : MemOk rd) {x y t1 t2 k : E}
    (h : LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2) :
    ∃ e e', e < 2 ^ 32 ∧ e' < 2 ^ 32 ∧ x = gen ^ e ∧ k = gen ^ (e + e') := by
  obtain ⟨e, he, rfl⟩ := load_gpow hm h.1
  obtain ⟨e', he', rfl⟩ := load_gpow hm h.2.2
  exact ⟨e, e', he, he', rfl, by rw [h.2.1, pow_add]⟩

/-- **A range check against `g^c`**: `x = g^e` with `e ≤ c`. -/
theorem rc_const {rd : Reader} (hm : MemOk rd) {x y t1 t2 k : E} {c : ℕ} (hc : c < 2 ^ 33)
    (hk : k = gen ^ c) (h : LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2) :
    ∃ e ≤ c, x = gen ^ e := by
  obtain ⟨e, e', he, he', hx, hk'⟩ := rc_sound hm h
  have := gen_pow_inj' (by omega) (by omega) (hk.symm.trans hk')
  exact ⟨e, by omega, hx⟩

set_option maxRecDepth 100000 in
theorem ginvW_mul_gen : ginvW * gen = 1 := by
  unfold ginvW
  rw [word_eOfNat, gen, eOfNat, eOfNat, ← ofK_mul, ← ofK_one]
  congr 1

/-- **A range check against a runtime bound** `b` (`assert log x < log b`, its `k` the product
`b · g⁻¹`): `x = g^e` with `BelowLog b e`. -/
theorem rc_below {rd : Reader} (hm : MemOk rd) {x y t1 t2 k b : E} (hk : k = b * ginvW)
    (h : LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2) :
    ∃ e, x = gen ^ e ∧ BelowLog b e := by
  obtain ⟨e, e', he, he', hx, hk'⟩ := rc_sound hm h
  refine ⟨e, hx, he, e', he', ?_⟩
  rw [show b = b * (ginvW * gen) by rw [ginvW_mul_gen, mul_one], ← mul_assoc, ← hk, hk', pow_succ]

/-- `BelowLog` against a known power: the exponent is below. -/
theorem belowLog_lt {b : E} {e M : ℕ} (hM : M < 2 ^ 33) (hb : b = gen ^ M) (h : BelowLog b e) :
    e < M := by
  obtain ⟨he, e', he', hb'⟩ := h
  have := gen_pow_inj' (by omega) (by omega) (hb.symm.trans hb')
  omega

/-! ## Compile-time powers of `g` -/

set_option maxRecDepth 100000 in
theorem word_gmax : word 9272771591053052074 0 0 = gen ^ 65535 := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

theorem word_g16 : word 65536 0 0 = gen ^ 16 := word_two_pow (a := 16) (by decide)

/-! ## `list_split` (G:3812-3824, TRIAGE #87) -/

theorem core22_body : Fn.body Data.core22 =
    [.atom (.hint (.witness "signers_split" (.stack [.n 1, .n 2]))),
     .atom (.const (.n 3) (word 65536 0 0)),
     .atom (.rangeCheck (.n 2) (.n 4) (.n 5) (.n 6) (.n 3)),
     .atom (.const (.n 7) (word 9272771591053052074 0 0)),
     .atom (.rangeCheck (.n 1) (.n 8) (.n 9) (.n 10) (.n 7)),
     .atom (.mul (.n 11) (.n 1) (.n 1)), .atom (.mul (.n 12) (.n 11) (.n 11)),
     .atom (.mul (.n 13) (.n 12) (.n 12)), .atom (.mul (.n 14) (.n 13) (.n 13)),
     .atom (.mul (.n 15) (.n 14) (.n 1)), .atom (.mul (.n 16) (.n 15) (.n 2)),
     .atom (.assertEq (.n 16) (.n 0)), .atom (.copy (.n 17) (.n 1)), .atom (.copy (.n 18) (.n 2)),
     .ret [.n 17, .n 18]] :=
  stmtsEqb_sound (by decide +kernel)

/-- **`list_split` splits a count into whole claim groups and a rest.** -/
theorem list_split_sound : list_split_sound_Spec := by
  intro rd hm args rets h
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_list_split args rets).mp h
  rw [core22_body] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨-, c3, rc1, c7, rc2, m11, m12, m13, m14, m15, m16, aeq, e17, e18, hr⟩ := hb
  obtain ⟨b, hb, hx2⟩ := rc_const hm (c := 16) (by norm_num) (by rw [c3, word_g16]) rc1
  obtain ⟨a, ha, hx1⟩ := rc_const hm (c := 65535) (by norm_num) (by rw [c7, word_gmax]) rc2
  have hp' : args = [σ (.n 0)] := by rw [← hp]; rfl
  subst hp'
  refine ⟨a, by simp only [maxKeys]; omega, b, by simp only [claimGroup]; omega, ?_, ?_⟩
  · rw [← e_add_eq_zero_iff.mp aeq, m16, m15, m14, m13, m12, m11, hx1, hx2]
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    simp only [claimGroup]
    ring
  · rw [← hr, e17, e18, hx1, hx2]

/-! ## `cover_da_root` (G:4078-4083, TRIAGE #95) -/

theorem core30_body : Fn.body Data.core30 =
    [.atom (.hint (.witness "da_index" (.stack [.n 4]))),
     .atom (.const (.n 5) (word 9223372036854775821 0 0)),
     .atom (.mul (.n 6) (.n 2) (.n 5)),
     .atom (.rangeCheck (.n 4) (.n 7) (.n 8) (.n 9) (.n 6)),
     .atom (.mul (.n 10) (.n 1) (.n 4)), .atom (.load (.n 3) (.n 10) 0),
     .atom (.mul (.n 11) (.n 4) (.n 4)), .atom (.mul (.n 12) (.n 11) (.n 11)),
     .atom (.mul (.n 13) (.n 0) (.n 12)), .atom (.load (.n 14) (.n 13) 0),
     .atom (.load (.n 15) (.n 13) 1), .atom (.load (.n 16) (.n 13) 2),
     .atom (.load (.n 17) (.n 13) 3), .ret [.n 14, .n 15, .n 16, .n 17]] :=
  stmtsEqb_sound (by decide +kernel)

/-- **`cover_da_root` marks a DA slot below the bound and returns its four cells.** -/
theorem cover_da_root_sound : cover_da_root_sound_Spec := by
  intro rd hm args rets h
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_cover_da_root args rets).mp h
  rw [core30_body] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨-, c5, m6, rc, m10, l3, m11, m12, m13, l14, l15, l16, l17, hr⟩ := hb
  obtain ⟨i, hx, hbl⟩ := rc_below hm (b := σ (.n 2)) (by rw [m6, c5]) rc
  have hp' : args = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3)] := by rw [← hp]; rfl
  subst hp'
  have h4 : σ (.n 13) = σ (.n 0) * gen ^ (4 * i) := by
    rw [m13, m12, m11, hx, ← pow_add, ← pow_add]
    congr 2
    ring
  refine ⟨i, hbl, ?_, by rw [← hr]; rfl, fun c hc => ?_⟩
  · rw [m10, hx] at l3
    have := (loadHolds_mul_gen_pow rd _ i 0 _).mp l3
    simpa using this
  · rw [h4] at l14 l15 l16 l17
    rw [← hr]
    interval_cases c
    · exact (loadHolds_mul_gen_pow rd _ _ 0 _).mp l14
    · exact (loadHolds_mul_gen_pow rd _ _ 1 _).mp l15
    · exact (loadHolds_mul_gen_pow rd _ _ 2 _).mp l16
    · exact (loadHolds_mul_gen_pow rd _ _ 3 _).mp l17

end
end LeanVM.Guest.B1.Digest
