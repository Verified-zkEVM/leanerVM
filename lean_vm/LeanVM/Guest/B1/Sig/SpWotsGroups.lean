/-
  LeanVM.Guest.B1.Sig.SpWotsGroups

  `sp_wots`'s codeword, sound: each digit group's dispatch takes the arm of its hinted digit word,
  and with the digits those choose each chain's tip is its chain from its start, the product is
  `g` to the digits' sum and the encoding their base-4 number.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsCheck
public import LeanVM.Guest.B1.Sig.Codeword

/-!
# `sp_wots`'s codeword, sound

* `spGroupT_sound`, `spGroupsT_sound`: a group's dispatch runs one arm `k < 4^n`, its selector
  `g^k`; the 21 groups of three digits each do (`SpGroupOK`);
* `spDigitWord σ p` (`logG`, the unique exponent below the arm count), `spDigit σ i`, `spStart σ i`:
  the digits the dispatches take, chain `i`'s digit and the cell its start is hinted in
  (`spStartAt`, `SpWotsLayout`);
* `spCodeword_sound`: the tips, the product and the encoding (`spCodeword_vals`, the arithmetic).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-! ## Atoms -/

theorem atomsOnly_iff : ∀ {L : List Stmt}, atomsOnly L = true ↔ ∀ x ∈ L, ∃ a, x = .atom a
  | [] => by simp [atomsOnly]
  | .atom a :: L => by
      simp only [atomsOnly, List.mem_cons, forall_eq_or_imp, atomsOnly_iff]
      exact ⟨fun h => ⟨⟨a, rfl⟩, h⟩, fun h => h.2⟩
  | .ite .. :: _ | .match_ .. :: _ | .call .. :: _ | .callIf .. :: _ | .dispatch .. :: _
  | .ret _ :: _ => by simp [atomsOnly]

theorem spW_atoms : StepAtoms spW := fun _ _ _ _ _ => rfl

theorem spArmK_atoms (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k b : Nat) :
    atomsOnly (spArmK first n fold B prodIn encIn k b).1 = true :=
  armT_atoms spW_atoms _ _ _ _ _ _ _ _ _ _

theorem spPre_atoms (fold : Bool) (B : Nat) : atomsOnly (spPre fold B) = true := by
  cases fold <;> rfl

/-! ## The groups -/

/-- **A group's dispatch takes one arm**: what it sets before holds, and some `k < 4^n` is the
selector's exponent, and arm `k`'s atoms hold, from its base. -/
theorem spGroupT_sound {first n : Nat} {fold : Bool} {prodIn encIn : V} {B : Nat} {rest : List Stmt}
    {next : Prop} (h : Stmt.HoldsList C rd σ ((spGroupT first n fold prodIn encIn B).1 ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧ AtomsHold rd σ (spPre fold B) ∧ ∃ k < 4 ^ n,
      σ (.n B) = ofK (addressOfIndex k) ∧
      AtomsHold rd σ (spArmK first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k)).1 :=
  groupD_sound spW_atoms (spPre_atoms fold B) h

/-- **What group `p` establishes**: its digit word `k < 4^n` and its arm's atoms. -/
def SpGroupOK (rd : Reader) (σ : Val) (p : Nat) : Prop :=
  ∃ k < 4 ^ spN p, σ (.n (spState p).2.2) = ofK (addressOfIndex k) ∧
    AtomsHold rd σ (spArmK (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k
      (spArmB (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k)).1

theorem spN_of_lt {p : Nat} (hp : p < 21) : spN p = 3 := by simp [spN, hp]

/-- **The groups of three digits, sound.** -/
theorem spGroupsT_sound {rest : List Stmt} {next : Prop} : ∀ (m p : Nat), p + m ≤ 21 →
    Stmt.HoldsList C rd σ ((spGroupsT m p (spState p).1 (spState p).2.1 (spState p).2.2).1 ++ rest)
      next kret →
      Stmt.HoldsList C rd σ rest next kret ∧ (p = 0 → 0 < m → PadOK σ spPad) ∧
        ∀ j < m, SpGroupOK rd σ (p + j)
  | 0, p, _, h => ⟨by simpa [spGroupsT] using h, fun _ h => absurd h (by omega),
      fun j hj => absurd hj (by omega)⟩
  | m + 1, p, hm, h => by
      rw [spGroupsT_succ, List.append_assoc] at h
      obtain ⟨h1, hpre, k, hk, hx, ha⟩ := spGroupT_sound h
      have ih := spGroupsT_sound m (p + 1) (by omega) (by rw [spState_succ]; exact h1)
      refine ⟨ih.1, fun hp _ => ?_, fun j hj => ?_⟩
      · subst hp
        exact padRun_ok (P := 13 + 5) (by simpa [spPre, spState_zero] using hpre)
      rcases j with _ | j
      · refine ⟨k, by rw [Nat.add_zero, spN_of_lt (by omega)]; exact hk, by simpa using hx, ?_⟩
        rw [Nat.add_zero, spN_of_lt (by omega)]
        exact ha
      · have := ih.2.2 j (by omega)
        rwa [show p + 1 + j = p + (j + 1) by omega] at this

/-! ## The digits and the starts -/

/-- **The digit word group `p`'s dispatch takes**: its selector's exponent. -/
noncomputable def spDigitWord (σ : Val) (p : Nat) : Nat :=
  logG (σ (.n (spState p).2.2)) (4 ^ spN p)

/-- **The digit of chain `i`.** -/
noncomputable def spDigit (σ : Val) (i : Nat) : Nat := spDigitWord σ (i / 3) / 4 ^ (i % 3) % 4

/-- **Chain `i`'s start**: the value its walk hints, in the arm its group's dispatch takes. -/
noncomputable def spStart (σ : Val) (i : Nat) : V := spStartAt (spDigitWord σ) i

theorem spDigitWord_eq {p k : Nat} (hk : k < 4 ^ spN p)
    (hx : σ (.n (spState p).2.2) = ofK (addressOfIndex k)) : spDigitWord σ p = k :=
  logG_eq hk (by unfold spN; split <;> norm_num) hx

/-! ## The values -/

/-- **The codeword's arithmetic**: running products and encodings folded group by group (`G`
groups of three digits, then the last chain's) give `g` to the digits' sum and their base-4
number. -/
theorem spCodeword_vals {G : Nat} (hG : 0 < G) (hG21 : G ≤ 21) (K : Nat → Nat)
    (hK : ∀ p ≤ G, K p < 4 ^ cwN G p) (hpow : ∀ s < 10, σ (.n (3 + s)) = gen ^ s) (prodV encV : Nat → E)
    (hprod0 : prodV 0 = σ (.n (3 + digitSum (K 0) (cwN G 0))))
    (hprod : ∀ p < G, prodV (p + 1) = prodV p * σ (.n (3 + digitSum (K (p + 1)) (cwN G (p + 1)))))
    (henc0 : encV 0 = lit (K 0 * 4 ^ (3 * 0)))
    (henc : ∀ p < G, encV (p + 1) = encV p + lit (K (p + 1) * 4 ^ (3 * (p + 1)))) :
    prodV G = gen ^ (∑ i ∈ Finset.range (3 * G + 1), K (i / 3) / 4 ^ (i % 3) % 4) ∧
      encV G = lit (∑ i ∈ Finset.range (3 * G + 1), K (i / 3) / 4 ^ (i % 3) % 4 * 4 ^ i) := by
  have hK64 : ∀ q, q < G → K q < 64 := fun q hq => by
    have := hK q (by omega)
    simpa [cwN, hq] using this
  have hKG : K G < 4 := by simpa [cwN] using hK G le_rfl
  refine ⟨?_, ?_⟩
  · have hpr : ∀ p < G, prodV p = gen ^ (∑ q ∈ Finset.range (p + 1), digitSum (K q) 3) := by
      intro p hp
      induction p with
      | zero =>
          rw [hprod0]
          simp only [cwN, hp, ↓reduceIte]
          rw [hpow _ (by rw [digitSum_three]; omega)]
          simp
      | succ p ih =>
          rw [hprod p (by omega), ih (by omega)]
          simp only [cwN, hp, ↓reduceIte]
          rw [hpow _ (by rw [digitSum_three]; omega), Finset.sum_range_succ (n := p + 1), pow_add]
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    rw [hprod G' (by omega), hpr G' (by omega)]
    simp only [cwN, lt_irrefl, ↓reduceIte]
    rw [hpow _ (by rw [digitSum_one _ hKG]; omega), digitSum_one _ hKG, ← pow_add,
      Finset.sum_range_succ (n := 3 * (G' + 1)), sum_range_three_mul]
    congr 1
    simp only [show ∀ q, (3 * q) / 3 = q from fun q => by omega,
      show ∀ q, (3 * q + 1) / 3 = q from fun q => by omega, show ∀ q, (3 * q + 2) / 3 = q from fun q => by omega,
      show ∀ q, (3 * q) % 3 = 0 from fun q => by omega, show ∀ q, (3 * q + 1) % 3 = 1 from fun q => by omega,
      show ∀ q, (3 * q + 2) % 3 = 2 from fun q => by omega, digitSum_three]
    congr 1
    · apply Finset.sum_congr rfl
      intro q _
      simp
    · rw [pow_zero, Nat.div_one]; exact (Nat.mod_eq_of_lt hKG).symm
  · have h4 : ∀ q, (4 : Nat) ^ (3 * q) = 2 ^ (6 * q) := fun q => by rw [pow_mul, pow_mul]; norm_num
    let K' : Nat → Nat := fun q => if q < G then K q else 0
    have hK' : ∀ q, K' q < 64 := fun q => by
      simp only [K']; split
      · exact hK64 q (by assumption)
      · omega
    have hsum : ∀ p, p ≤ G → ∑ q ∈ Finset.range p, K' q * 4 ^ (3 * q) =
        ∑ q ∈ Finset.range p, K q * 4 ^ (3 * q) := fun p hp =>
      Finset.sum_congr rfl fun q hq => by simp [K', show q < G by simp at hq; omega]
    have hen : ∀ p < G, encV p = eOfNat192 (∑ q ∈ Finset.range (p + 1), K q * 4 ^ (3 * q)) := by
      intro p hp
      induction p with
      | zero =>
          rw [henc0, lit_eq _ (group_lit_bound (hK64 0 hp) (by omega))]
          simp
      | succ p ih =>
          have hlt := sum_lt_pow64 K' hK' (p + 1)
          rw [hsum (p + 1) (by omega)] at hlt
          rw [henc p (by omega), ih (by omega), Finset.sum_range_succ (n := p + 1),
            lit_eq _ (group_lit_bound (hK64 (p + 1) hp) (by omega)),
            show K (p + 1) * 4 ^ (3 * (p + 1)) = 2 ^ (6 * (p + 1)) * K (p + 1) by rw [h4, mul_comm],
            eOfNat192_add_shift hlt]
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hlt := sum_lt_pow64 K' hK' (G' + 1)
    rw [hsum (G' + 1) (by omega)] at hlt
    have hbound : K (G' + 1) * 4 ^ (3 * (G' + 1)) < 2 ^ 128 := last_lit_bound hKG (by omega)
    rw [henc G' (by omega), hen G' (by omega), lit_eq _ hbound,
      show K (G' + 1) * 4 ^ (3 * (G' + 1)) = 2 ^ (6 * (G' + 1)) * K (G' + 1) by rw [h4, mul_comm],
      eOfNat192_add_shift hlt]
    have hN : ∑ q ∈ Finset.range (G' + 1), K q * 4 ^ (3 * q) + 2 ^ (6 * (G' + 1)) * K (G' + 1) =
        ∑ i ∈ Finset.range (3 * (G' + 1) + 1), K (i / 3) / 4 ^ (i % 3) % 4 * 4 ^ i := by
      rw [Finset.sum_range_succ (n := 3 * (G' + 1)), sum_range_three_mul]
      simp only [show ∀ q, (3 * q) / 3 = q from fun q => by omega,
        show ∀ q, (3 * q + 1) / 3 = q from fun q => by omega,
        show ∀ q, (3 * q + 2) / 3 = q from fun q => by omega,
        show ∀ q, (3 * q) % 3 = 0 from fun q => by omega, show ∀ q, (3 * q + 1) % 3 = 1 from fun q => by omega,
        show ∀ q, (3 * q + 2) % 3 = 2 from fun q => by omega]
      congr 1
      · apply Finset.sum_congr rfl
        intro q hq
        have hq' := hK64 q (by simp at hq; omega)
        have e := digits_three (K q) hq'
        simp only [pow_zero, pow_one, Nat.div_one, pow_add, show (4 : Nat) ^ 2 = 16 by norm_num]
        nth_rewrite 1 [← e]
        ring
      · rw [← h4]
        simp [Nat.mod_eq_of_lt hKG, mul_comm]
    rw [hN, lit_eq _ (by
      rw [← hN]
      have := Nat.mul_le_mul_left (2 ^ (6 * (G' + 1))) (show K (G' + 1) ≤ 3 by omega)
      calc _ < 2 ^ (6 * (G' + 1)) + 2 ^ (6 * (G' + 1)) * 3 := by omega
        _ = 2 ^ 2 * 2 ^ (6 * (G' + 1)) := by ring
        _ ≤ 2 ^ 2 * 2 ^ 126 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = 2 ^ 128 := by norm_num)]

end
end LeanVM.Guest.B1.Sig
