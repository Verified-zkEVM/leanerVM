/-
  LeanVM.Guest.B1.Sig.Codeword

  What a codeword's check computes (`codewordT`, any chain step): each chain's tip is its chain
  from the hinted start at its digit, the digits sum to the target, and they are the digest's
  first cell, base 4.
-/

module

public import LeanVM.Guest.B1.Sig.WotsSound

/-!
# The codeword, sound

`codewordT W G target d0 b` runs `G` groups of three digits and the last chain's group. The digit
values a group's dispatch takes are its selector's exponent, `cwK σ p` (`logG`, the unique exponent
below the arm count). Then (`codewordT_sound`), with the digits `cwDigit σ i` of the chains
`i < 3G + 1`:

* chain `i`'s tip `cwTip i` is `chainT f i (3 - x) x` of its start `cwStart σ i`, `x` its digit;
* `g^(Σ digits) = target` (the assertion, the powers being `g^s`);
* the digest's first cell `d0` is `Σ x_i · 4^i`, as a 192-bit word.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-! ## Exponents -/

open Classical in
/-- The exponent `k < bound` with `x = g^k` (`0` if none). -/
noncomputable def logG (x : E) (bound : Nat) : Nat :=
  ((List.range bound).find? fun k => decide (x = ofK (gpow k))).getD 0

theorem logG_eq {x : E} {k bound : Nat} (hk : k < bound) (hb : bound ≤ 2 ^ 64 - 1)
    (hx : x = ofK (gpow k)) : logG x bound = k := by
  classical
  unfold logG
  have hsome : ((List.range bound).find? fun k => decide (x = ofK (gpow k))).isSome := by
    rw [List.find?_isSome]
    exact ⟨k, List.mem_range.mpr hk, by simp [hx]⟩
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp hsome
  rw [hk', Option.getD_some]
  have hmem := List.mem_of_find?_eq_some hk'
  have hp := List.find?_some hk'
  simp only [decide_eq_true_eq] at hp
  rw [hx] at hp
  have hk' := List.mem_range.mp hmem
  exact (gpow_injOn (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) (ofK_injective hp)).symm

/-! ## The groups of a codeword -/

/-- Group `p` of a codeword from base `b`: its running product's and encoding's cells and its base. -/
def cwState (W : WotsT) (b : Nat) : Nat → V × V × Nat
  | 0 => (.n 0, .n 0, b)
  | p + 1 =>
      let st := cwState W b p
      (prodT W (p == 0) 3 st.2.2, encT W (p == 0) 3 st.2.2,
        (groupT W (3 * p) 3 (p == 0) st.1 st.2.1 st.2.2).2)

/-- What group `q` of `G + 1` establishes: its digits `k < 4^n`, its arm. -/
def GroupOK (rd : Reader) (σ : Val) (W : WotsT) (b q : Nat) (fold : Bool) (n : Nat) : Prop :=
  ∃ k < 4 ^ n, σ (.n (cwState W b q).2.2) = ofK (gpow k) ∧
    AtomsHold rd σ (armT W (slotsT W fold (cwState W b q).2.2) (3 * q) n fold (cwState W b q).1
      (cwState W b q).2.1 (prodT W fold n (cwState W b q).2.2) (encT W fold n (cwState W b q).2.2) k
      (armBase W (slotsT W fold (cwState W b q).2.2) (3 * q) n fold (cwState W b q).1
        (cwState W b q).2.1 (prodT W fold n (cwState W b q).2.2) (encT W fold n (cwState W b q).2.2)
        0 k ((cwState W b q).2.2 + 5))).1

theorem groupsT_eq (W : WotsT) (b : Nat) : ∀ (m p : Nat),
    (groupsT W m p (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2).2 =
      ((cwState W b (p + m)).2.2, (List.range m).flatMap (fun j => (List.range 3).map fun r =>
        V.n (slotsT W (p + j == 0) (cwState W b (p + j)).2.2 r 2)),
        (cwState W b (p + m)).1, (cwState W b (p + m)).2.1)
  | 0, p => by simp [groupsT]
  | m + 1, p => by
      have ih := groupsT_eq W b m (p + 1)
      have e : (groupsT W m (p + 1) (prodT W (p == 0) 3 (cwState W b p).2.2)
          (encT W (p == 0) 3 (cwState W b p).2.2)
          (groupT W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2).2).2 =
          ((cwState W b (p + 1 + m)).2.2, (List.range m).flatMap (fun j => (List.range 3).map fun r =>
            V.n (slotsT W (p + 1 + j == 0) (cwState W b (p + 1 + j)).2.2 r 2)),
            (cwState W b (p + 1 + m)).1, (cwState W b (p + 1 + m)).2.1) := ih
      simp only [groupsT]
      rw [e, show p + 1 + m = p + (m + 1) by omega]
      simp only [Prod.mk.injEq, true_and, and_true]
      rw [List.range_succ_eq_map (n := m), List.flatMap_cons, List.flatMap_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.flatMap_congr
      intro j _
      simp only [Nat.succ_eq_add_one, show p + 1 + j = p + (j + 1) by omega]

theorem groupsT_sound {W : WotsT} (hW : StepAtoms W) (b : Nat) {rest : List Stmt} {next : Prop} :
    ∀ (m p : Nat),
    Stmt.HoldsList C rd σ ((groupsT W m p (cwState W b p).1 (cwState W b p).2.1
      (cwState W b p).2.2).1 ++ rest) next kret →
      Stmt.HoldsList C rd σ rest next kret ∧ ∀ j < m, GroupOK rd σ W b (p + j) (p + j == 0) 3
  | 0, p, h => ⟨by simpa [groupsT] using h, fun j hj => absurd hj (by omega)⟩
  | m + 1, p, h => by
      simp only [groupsT, List.append_assoc] at h
      obtain ⟨h1, k, hk, hx, ha⟩ := groupT_sound hW h
      have ih := groupsT_sound hW b m (p + 1) (by simpa only [cwState] using h1)
      refine ⟨ih.1, fun j hj => ?_⟩
      rcases j with _ | j
      · exact ⟨k, hk, hx, ha⟩
      · have := ih.2 j (by omega)
        rwa [show p + 1 + j = p + (j + 1) by omega] at this

/-! ## The codeword -/

/-- The digits of group `p` of a codeword of `G` groups of three and the last chain's. -/
def cwN (G p : Nat) : Nat := if p < G then 3 else 1

/-- Group `p`'s arm `k`, from its base. -/
def cwArm (W : WotsT) (G b p k : Nat) : List Stmt × Nat :=
  armT W (slotsT W (p == 0) (cwState W b p).2.2) (3 * p) (cwN G p) (p == 0) (cwState W b p).1
    (cwState W b p).2.1 (prodT W (p == 0) (cwN G p) (cwState W b p).2.2)
    (encT W (p == 0) (cwN G p) (cwState W b p).2.2) k
    (armBase W (slotsT W (p == 0) (cwState W b p).2.2) (3 * p) (cwN G p) (p == 0) (cwState W b p).1
      (cwState W b p).2.1 (prodT W (p == 0) (cwN G p) (cwState W b p).2.2)
      (encT W (p == 0) (cwN G p) (cwState W b p).2.2) 0 k ((cwState W b p).2.2 + 5))

/-- The digit values group `p`'s dispatch takes: its selector's exponent. -/
noncomputable def cwK (W : WotsT) (G b : Nat) (σ : Val) (p : Nat) : Nat :=
  logG (σ (.n (cwState W b p).2.2)) (4 ^ cwN G p)

/-- **The digit of chain `i`.** -/
noncomputable def cwDigit (W : WotsT) (G b : Nat) (σ : Val) (i : Nat) : Nat :=
  cwK W G b σ (i / 3) / 4 ^ (i % 3) % 4

/-- **Chain `i`'s tip**: the slot of its last step. -/
def cwTip (W : WotsT) (b i : Nat) : V := .n (slotsT W (i / 3 == 0) (cwState W b (i / 3)).2.2 (i % 3) 2)

/-- **Chain `i`'s start**: the value its walk hints, in the arm its group's dispatch takes. -/
noncomputable def cwStart (W : WotsT) (G b : Nat) (σ : Val) (i : Nat) : V :=
  armStart W (slotsT W (i / 3 == 0) (cwState W b (i / 3)).2.2) (i / 3 == 0) (cwK W G b σ (i / 3))
    (armBase W (slotsT W (i / 3 == 0) (cwState W b (i / 3)).2.2) (3 * (i / 3)) (cwN G (i / 3))
      (i / 3 == 0) (cwState W b (i / 3)).1 (cwState W b (i / 3)).2.1
      (prodT W (i / 3 == 0) (cwN G (i / 3)) (cwState W b (i / 3)).2.2)
      (encT W (i / 3 == 0) (cwN G (i / 3)) (cwState W b (i / 3)).2.2) 0 (cwK W G b σ (i / 3))
      ((cwState W b (i / 3)).2.2 + 5)) (i % 3)

theorem codewordT_groups {W : WotsT} (hW : StepAtoms W) {G : Nat} (hG : 0 < G) {target : E} {d0 : V}
    {b : Nat} {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ ((codewordT W G target d0 b).1 ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧
      (∀ p ≤ G, ∃ k < 4 ^ cwN G p, σ (.n (cwState W b p).2.2) = ofK (gpow k) ∧
        AtomsHold rd σ (cwArm W G b p k).1) ∧
      σ d0 = σ (encT W false 1 (cwState W b G).2.2) ∧
      σ (prodT W false 1 (cwState W b G).2.2) = target := by
  have hgs := groupsT_eq W b G 0
  simp only [Nat.zero_add] at hgs
  simp only [codewordT, List.append_assoc] at h
  have hgs' : (groupsT W G 0 (.n 0) (.n 0) b).2 = _ := hgs
  rw [hgs'] at h
  obtain ⟨h1, hg⟩ := groupsT_sound (rd := rd) (σ := σ) (C := C) (kret := kret) hW b G 0 h
  obtain ⟨h2, kL, hkL, hxL, haL⟩ := groupT_sound hW h1
  have hc := h2
  simp only [List.cons_append, List.nil_append] at hc
  have e1 : σ d0 = σ (encT W false 1 (cwState W b G).2.2) := hc.1
  have e2 := hc.2.1
  have e3 := hc.2.2.1
  simp only [Atom.Holds] at e2 e3
  refine ⟨hc.2.2.2, fun p hp => ?_, e1, ?_⟩
  · by_cases hpG : p < G
    · obtain ⟨k, hk, hx, ha⟩ := hg p hpG
      simp only [Nat.zero_add] at hk hx ha
      exact ⟨k, by simp only [cwN, hpG, ↓reduceIte]; exact hk, hx, by simpa [cwArm, cwN, hpG] using ha⟩
    · have hpe : p = G := by omega
      subst hpe
      have hf : (p == 0) = false := by simp; omega
      exact ⟨kL, by simpa [cwN] using hkL, hxL, by simpa [cwArm, cwN, hf] using haL⟩
  · rw [← e2]
    exact (Value.e_add_eq_zero_iff).mp e3

/-! ## Sums of digits -/

theorem sum_range_three_mul {M : Type} [AddCommMonoid M] (g : Nat → M) :
    ∀ m, ∑ i ∈ Finset.range (3 * m), g i = ∑ p ∈ Finset.range m, (g (3 * p) + g (3 * p + 1) + g (3 * p + 2))
  | 0 => by simp
  | m + 1 => by
      rw [Finset.sum_range_succ (n := m), ← sum_range_three_mul g m,
        show 3 * (m + 1) = 3 * m + 2 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      simp only [add_assoc]

theorem digits_three (k : Nat) (hk : k < 64) : k % 4 + k / 4 % 4 * 4 + k / 16 % 4 * 16 = k := by
  omega

theorem digitSum_three (k : Nat) : digitSum k 3 = k % 4 + k / 4 % 4 + k / 16 % 4 := by
  simp [digitSum]; omega

theorem digitSum_one (k : Nat) (hk : k < 4) : digitSum k 1 = k := by
  simp [digitSum]; omega

theorem eOfNat192_add_shift {S k s : Nat} (hS : S < 2 ^ s) :
    eOfNat192 S + eOfNat192 (2 ^ s * k) = eOfNat192 (S + 2 ^ s * k) := by
  rw [← eOfNat192_xor, Nat.xor_comm, two_pow_mul_xor hS, add_comm]

end
end LeanVM.Guest.B1.Sig
