/-
  LeanVM.Guest.B1.Opening.QueriesCap

  One query's cap leaf: the parent's flag set and the node reached stored at the cap leaf.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPath

/-!
# A query's cap leaf (`opening_query`, G:1226-1241)

The cap bits `pd + 1 .. depth - 1` of the position build `q = g^(Q)`, `Q = pos / 2^(pd+1)` (the
parent's index among the cap's internal nodes at the level above the leaves), one factor
`1 + b·(1 + g^(2^j))` a bit (`capFac`); the parent's flag `flags[2^(cd-1) + Q]` is set to `1`, and
the node reached is stored at the cap leaf `cap·q⁴·g^(2b)`, `b` the bit `pd`, at the offset
`2^(cd+1)`: the cells `2(2^cd + pos / 2^pd)` and the next (`oqCap_sound`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

theorem g_pow_64 : Parameters.g ^ 64 = K.ofBits 27 := by decide +kernel

/-- The folded constants are `1 + g^(2^j)`. -/
theorem word_capFac {j : ℕ} (hj : j < 7) : word (capFac.getD j 0) 0 0 = 1 + gen ^ 2 ^ j := by
  rw [word_eOfNat]
  interval_cases j
  all_goals first
    | (rw [gen_pow_eq_eOfNat (by decide), ← eOfNat_one, ← eOfNat_xor]; rfl)
    | (rw [show (2 : ℕ) ^ 6 = 64 from rfl, gen_eq_ofK, ← ofK_pow, g_pow_64, ← eOfNat_one,
        show ofK (K.ofBits 27) = eOfNat 27 from rfl, ← eOfNat_xor]; rfl)

/-- A bit's factor: `1 + b·(1 + g^m) = g^(b·m)`. -/
theorem bit_factor (b : Bool) (m : ℕ) : 1 + bitE b * (1 + gen ^ m) = gen ^ (if b then m else 0) := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  cases b
  · simp [bitE]
  · simp only [bitE, ↓reduceIte, one_mul]
    linear_combination h2

theorem mem_oqCapT_bit {s : Oq} {bp cap flags : V} {kL ch j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ s.cd - 2)
    {a : Atom} (ha : Stmt.atom a ∈ oqCapBitT s bp ch j) :
    Stmt.atom a ∈ oqCapT s bp cap flags kL ch := by
  unfold oqCapT
  refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr
    ⟨_, List.mem_map.mpr ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩, ha⟩))
  rw [Nat.sub_add_cancel hj1]

/-- **The cap leaf** (G:1226-1240): with the bits `pd .. pd + cd - 1` those of `q < 2^(pd+cd)`, the
parent's flag is set and the node `oqNode … pd` is stored at the cap leaf's cells. -/
theorem oqCap_sound {s : Oq} (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {bp cap flags : V} {kL ch q : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqCapT s bp cap flags kL ch → a.Holds rd σ)
    (hq : q < 2 ^ (s.pd + s.cd))
    (hbits : ∀ l, s.pd ≤ l → l < s.pd + s.cd → LoadHolds rd (σ bp) l (bitE (q.testBit l))) :
    LoadHolds rd (σ flags) (2 ^ (s.cd - 1) + q / 2 ^ (s.pd + 1)) 1 ∧
      LoadHolds rd (σ cap) (2 * (2 ^ s.cd + q / 2 ^ s.pd)) (σ (.n (oqNode s kL ch s.pd 0))) ∧
      LoadHolds rd (σ cap) (2 * (2 ^ s.cd + q / 2 ^ s.pd) + 1) (σ (.n (oqNode s kL ch s.pd 1))) := by
  set Cq := oqCq s ch with hCq
  have bit : ∀ l, s.pd ≤ l → l < s.pd + s.cd → ∀ v, LoadHolds rd (σ bp) l v → v = bitE (q.testBit l) :=
    fun l h1 h2 v hv => loadHolds_unique hv (hbits l h1 h2)
  -- the first factor
  have c0 := hA _ (by simp [oqCapT, ← hCq] : Stmt.atom (.const (.n Cq) (word 1 0 0)) ∈ _)
  have c1 := hA _ (by simp [oqCapT, ← hCq] : Stmt.atom (.load (.n (Cq + 1)) bp (s.pd + 1)) ∈ _)
  have c2 := hA _ (by simp [oqCapT, ← hCq] :
    Stmt.atom (.const (.n (Cq + 2)) (word (capFac.getD 0 0) 0 0)) ∈ _)
  have c3 := hA _ (by simp [oqCapT, ← hCq] :
    Stmt.atom (.mul (.n (Cq + 3)) (.n (Cq + 1)) (.n (Cq + 2))) ∈ _)
  have c4 := hA _ (by simp [oqCapT, ← hCq] : Stmt.atom (.add (.n (Cq + 4)) (.n Cq) (.n (Cq + 3))) ∈ _)
  simp only [Atom.Holds] at c0 c2 c3 c4
  -- the product over the cap bits
  have qv : ∀ j, j ≤ s.cd - 2 → σ (.n (oqQ s ch j)) = gen ^ (q / 2 ^ (s.pd + 1) % 2 ^ (j + 1)) := by
    intro j hj
    induction j with
    | zero =>
      have hb := bit _ (by omega) (by omega) _ c1
      rw [show oqQ s ch 0 = Cq + 4 by simp [oqQ, hCq], c4, c3, c0, c2, hb,
        word_capFac (by decide), word_one, bit_factor, Nat.testBit_eq_decide_div_mod_eq]
      congr 1
      by_cases h : q / 2 ^ (s.pd + 1) % 2 = 1 <;> simp [h]
      omega
    | succ j ih =>
      set Y := Cq + 5 + 6 * j with hY
      have mem := fun a (ha : Stmt.atom a ∈ oqCapBitT s bp ch (j + 1)) =>
        hA a (mem_oqCapT_bit (by omega) hj ha)
      have d0 := mem _ (by simp [oqCapBitT, ← hCq, ← hY] : Stmt.atom (.const (.n Y) (word 1 0 0)) ∈ _)
      have d1 := mem _ (by simp [oqCapBitT, ← hCq, ← hY] :
        Stmt.atom (.load (.n (Y + 1)) bp (s.pd + 1 + (j + 1))) ∈ _)
      have d2 := mem _ (by simp [oqCapBitT, ← hCq, ← hY] :
        Stmt.atom (.const (.n (Y + 2)) (word (capFac.getD (j + 1) 0) 0 0)) ∈ _)
      have d3 := mem _ (by simp [oqCapBitT, ← hCq, ← hY] :
        Stmt.atom (.mul (.n (Y + 3)) (.n (Y + 1)) (.n (Y + 2))) ∈ _)
      have d4 := mem _ (by simp [oqCapBitT, ← hCq, ← hY] :
        Stmt.atom (.add (.n (Y + 4)) (.n Y) (.n (Y + 3))) ∈ _)
      have d5 := mem _ (by simp [oqCapBitT, ← hCq, ← hY] :
        Stmt.atom (.mul (.n (Y + 5)) (.n (oqQ s ch j)) (.n (Y + 4))) ∈ _)
      simp only [Atom.Holds] at d0 d2 d3 d4 d5
      have hb := bit _ (by omega) (by omega) _ d1
      rw [show oqQ s ch (j + 1) = Y + 5 by simp [oqQ, hY, hCq]; omega, d5, d4, d3, d0, d2, hb,
        word_capFac (by omega), word_one, ih (by omega), bit_factor, ← pow_add,
        show q / 2 ^ (s.pd + 1) % 2 ^ (j + 1 + 1) = q / 2 ^ (s.pd + 1) % 2 ^ (j + 1) +
          2 ^ (j + 1) * (q / 2 ^ (s.pd + 1) / 2 ^ (j + 1) % 2) from Nat.mod_pow_succ,
        Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul, ← pow_add]
      congr 1
      by_cases h : q / 2 ^ (s.pd + 1 + (j + 1)) % 2 = 1
      · simp [h]
      · simp [show q / 2 ^ (s.pd + 1 + (j + 1)) % 2 = 0 by omega]
  -- the cap index
  set Q := q / 2 ^ (s.pd + 1) with hQdef
  have hQlt : Q < 2 ^ (s.cd - 1) := by
    rw [hQdef, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    calc q < 2 ^ (s.pd + s.cd) := hq
      _ = 2 ^ (s.cd - 1 + (s.pd + 1)) := by congr 1; omega
  have hqf : σ (.n (oqQ s ch (s.cd - 2))) = gen ^ Q := by
    rw [qv _ le_rfl, show s.cd - 2 + 1 = s.cd - 1 by omega, Nat.mod_eq_of_lt hQlt]
  set z := Cq + 5 + 6 * (s.cd - 2) with hz
  have e0 := hA _ (by simp [oqCapT, ← hCq, ← hz] :
    Stmt.atom (.mul (.n z) flags (.n (oqQ s ch (s.cd - 2)))) ∈ _)
  have e1 := hA _ (by simp [oqCapT, ← hCq, ← hz] : Stmt.atom (.const (.n (z + 1)) (word 1 0 0)) ∈ _)
  have e2 := hA _ (by simp [oqCapT, ← hCq, ← hz] :
    Stmt.atom (.load (.n (z + 1)) (.n z) (2 ^ (s.cd - 1))) ∈ _)
  have e3 := hA _ (by simp [oqCapT, ← hCq, ← hz] :
    Stmt.atom (.mul (.n (z + 2)) (.n (oqQ s ch (s.cd - 2))) (.n (oqQ s ch (s.cd - 2)))) ∈ _)
  have e4 := hA _ (by simp [oqCapT, ← hCq, ← hz] : Stmt.atom (.mul (.n (z + 3)) cap (.n (z + 2))) ∈ _)
  have e5 := hA _ (by simp [oqCapT, ← hCq, ← hz] :
    Stmt.atom (.mul (.n (z + 4)) (.n (z + 3)) (.n (z + 2))) ∈ _)
  have e6 := hA _ (by simp [oqCapT, ← hCq, ← hz] : Stmt.atom (.const (.n (z + 5)) (word 1 0 0)) ∈ _)
  have e7 := hA _ (by simp [oqCapT, ← hCq, ← hz] : Stmt.atom (.load (.n (z + 6)) bp s.pd) ∈ _)
  have e8 := hA _ (by simp [oqCapT, ← hCq, ← hz] : Stmt.atom (.const (.n (z + 7)) (word 5 0 0)) ∈ _)
  have e9 := hA _ (by simp [oqCapT, ← hCq, ← hz] :
    Stmt.atom (.mul (.n (z + 8)) (.n (z + 6)) (.n (z + 7))) ∈ _)
  have e10 := hA _ (by simp [oqCapT, ← hCq, ← hz] :
    Stmt.atom (.add (.n (z + 9)) (.n (z + 5)) (.n (z + 8))) ∈ _)
  have e11 := hA _ (by simp [oqCapT, ← hCq, ← hz] :
    Stmt.atom (.mul (.n (z + 10)) (.n (z + 4)) (.n (z + 9))) ∈ _)
  have e12 := hA _ (by simp [oqCapT, ← hCq, ← hz] :
    Stmt.atom (.load (.n (oqNode s kL ch s.pd 0)) (.n (z + 10)) (2 ^ (s.cd + 1))) ∈ _)
  have e13 := hA _ (by simp [oqCapT, ← hCq, ← hz] :
    Stmt.atom (.load (.n (oqNode s kL ch s.pd 1)) (.n (z + 10)) (2 ^ (s.cd + 1) + 1)) ∈ _)
  simp only [Atom.Holds] at e0 e1 e3 e4 e5 e6 e8 e9 e10 e11
  have hb := bit _ le_rfl (by omega) _ e7
  have hz0 : σ (.n z) = σ flags * gen ^ Q := by rw [e0, hqf]
  have hz10 : σ (.n (z + 10)) = σ cap * gen ^ (4 * Q + (if q.testBit s.pd then 2 else 0)) := by
    rw [e11, e5, e4, e3, e10, e9, e6, e8, hb, hqf, word_one, word_five, bit_factor, ← pow_add,
      mul_assoc, ← pow_add, mul_assoc, ← pow_add]
    congr 2; ring
  have hsplit : q / 2 ^ s.pd = 2 * Q + (if q.testBit s.pd then 1 else 0) := by
    rw [hQdef, Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
    by_cases h : q / 2 ^ s.pd % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  refine ⟨?_, ?_, ?_⟩
  · have := e2
    simp only [Atom.Holds, hz0, e1, word_one] at this
    rw [loadHolds_mul_gen_pow, add_comm] at this
    exact this
  · have := e12
    simp only [Atom.Holds, hz10] at this
    rw [loadHolds_mul_gen_pow] at this
    rw [hsplit, show 2 * (2 ^ s.cd + (2 * Q + (if q.testBit s.pd then 1 else 0))) =
      4 * Q + (if q.testBit s.pd then 2 else 0) + 2 ^ (s.cd + 1) by
        rw [pow_succ]; split <;> ring]
    exact this
  · have := e13
    simp only [Atom.Holds, hz10] at this
    rw [loadHolds_mul_gen_pow] at this
    rw [hsplit, show 2 * (2 ^ s.cd + (2 * Q + (if q.testBit s.pd then 1 else 0))) + 1 =
      4 * Q + (if q.testBit s.pd then 2 else 0) + (2 ^ (s.cd + 1) + 1) by
        rw [pow_succ]; split <;> ring]
    exact this

end
end LeanVM.Guest.B1
