/-
  LeanVM.Guest.B1.Sig.WotsGroupComplete

  An arm of a WOTS+C group completes on the group's arms region.
-/

module

public import LeanVM.Guest.B1.Sig.WotsGroup

/-!
# A group's arm, complete

`groupArm_complete`: arm `k < 4^n` of a group from base `b` completes on `b + 5 ..< armB (4^n)`,
its valuation the arm evaluated and its tips canonical, from canonical starts.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem prodT_eq (W : WotsT) (fold : Bool) (n b : Nat) :
    prodT W fold n b = .n (groupStart fold b + chainStride W * n) := rfl

theorem encT_eq (W : WotsT) (fold : Bool) (n b : Nat) :
    encT W fold n b = .n (groupStart fold b + chainStride W * n + 1) := rfl

/-- **An arm of a group completes.** -/
theorem groupArm_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) {first n : Nat} {fold : Bool} {prodIn encIn : V} {b k : Nat}
    (hk : k < 4 ^ n) (hB : B ≤ b) (hpi : NBv B prodIn) (hei : NBv B encIn)
    (hpw : NBv B (W.power (digitSum k n))) (σ : Val) (hg : good σ)
    (hs : ∀ t < n, StartCanon σ (slotsT W fold b t) (dig k t)
      (walkBase (if k = 0 then W.size + 13 else W.size) k 0 t
        (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k))) :
    Completes C rd (b + 5) (armB W first n fold prodIn encIn b (4 ^ n))
      (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) k
        (armB W first n fold prodIn encIn b k)).1 σ
      (fun σ' => σ' = fwd (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b)
          (encT W fold n b) k (armB W first n fold prodIn encIn b k)).1 σ ∧
        ∀ t < n, IsCanonical128 (σ' (.n (slotsT W fold b t 2)))) := by
  have hend : armB W first n fold prodIn encIn b (k + 1) ≤ armB W first n fold prodIn encIn b (4 ^ n) :=
    armB_mono W first n fold prodIn encIn b (by omega)
  have hgs : b + 5 ≤ groupStart fold b := by rw [groupStart_eq]; split <;> omega
  have hgsf : fold = true → b + 6 ≤ groupStart fold b := by intro hf; rw [groupStart_eq, hf]; simp
  have hpoB : B ≤ groupStart fold b + chainStride W * n := by omega
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.zero_add] at hend
    have h1 := armB_one W first n fold prodIn encIn b
    rw [armB_zero] at hs ⊢
    simp only [↓reduceIte] at hs ⊢
    obtain ⟨l1, l2, l3⟩ := arm0_lay W fold (n := n) hB
    have hR : ∀ x, WalksR (slotsT W fold b) (W.size + 13) 0 n (if fold then b + 5 + 1 else b + 5) x →
        x ≠ .n (groupStart fold b + chainStride W * n) ∧
        x ≠ .n (groupStart fold b + chainStride W * n + 1) ∧ (fold = true → x ≠ .n (b + 5)) ∧
        (0 ≠ 0 → x ≠ .n (walksT W (slotsT W fold b) first 0 W.size n 0 (if fold then b + 5 + 1 else b + 5)).2) := by
      intro x hx
      obtain ⟨j, rfl, h1, h2⟩ := l3 x hx
      refine ⟨fun e => ?_, fun e => ?_, fun hf e => ?_, fun h => absurd rfl h⟩ <;>
        simp only [V.mk.injEq, true_and] at e
      · omega
      · omega
      · have := hgsf hf; omega
    have hssa := armT_ssa (first := first) (prodIn := prodIn) (encIn := encIn) hW l1 l2 hpi hei hpw
      (show groupStart fold b + chainStride W * n ≠ groupStart fold b + chainStride W * n + 1 by omega)
      hpoB (by omega)
      (fun hf => ⟨by have := hgsf hf; omega, by have := hgsf hf; omega⟩)
      hR (fun h => absurd rfl h)
    obtain ⟨kc, ktip⟩ := armT_canon (first := first) (prodIn := prodIn) (encIn := encIn) hW hc l1 l2
      (by omega) hR hssa.1 σ hg (by simpa using hs)
    obtain ⟨σ', he, hp, hh⟩ := fwd_completes (C := C) (rd := rd) (lo := b + 5)
      (hi := armB W first n fold prodIn encIn b (4 ^ n)) hssa.1 (fun x hx => by
        rcases hssa.2 x hx with h | rfl | rfl | ⟨-, rfl⟩ | ⟨h, -⟩
        · obtain ⟨j, rfl, h1', h2'⟩ := l3 x h
          exact ⟨j, by omega, by omega, rfl⟩
        · exact ⟨_, by omega, by omega, rfl⟩
        · exact ⟨_, by omega, by omega, rfl⟩
        · exact ⟨b + 5, le_rfl, by omega, rfl⟩
        · exact absurd rfl h) σ kc
    refine ⟨σ', he, ⟨hp, fun t ht => ?_⟩, hh⟩
    rw [hp]
    exact ktip t ht
  · have ha := armB_pos W first n fold prodIn encIn b hk0
    have hnext := armB_next_pos W first n fold prodIn encIn b k hk0
    have h1 : armB W first n fold prodIn encIn b 1 ≤ armB W first n fold prodIn encIn b (4 ^ n) :=
      armB_mono W first n fold prodIn encIn b (Nat.one_le_two_pow.trans (Nat.pow_le_pow_left (by norm_num) n))
    have h1' := armB_one W first n fold prodIn encIn b
    simp only [hk0, ↓reduceIte] at hs ⊢
    obtain ⟨l1, l2, l3⟩ := armPos_lay W fold (n := n) (k := k) (a := armB W first n fold prodIn encIn b k) hB ha
    have hws2 := walksT_snd W (slotsT W fold b) first k W.size n 0
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)
    have hb0 : armB W first n fold prodIn encIn b k ≤
        (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k) := by
      split <;> omega
    have hb0f : fold = true → armB W first n fold prodIn encIn b k + 1 ≤
        (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k) := by
      intro hf; simp [hf]
    have hwb := walkBase_le W.size k
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)
      (Nat.zero_le n)
    simp only [walkBase] at hwb
    have hR : ∀ x, WalksR (slotsT W fold b) W.size k n
        (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k) x →
        x ≠ .n (groupStart fold b + chainStride W * n) ∧
        x ≠ .n (groupStart fold b + chainStride W * n + 1) ∧
        (fold = true → x ≠ .n (armB W first n fold prodIn encIn b k)) ∧
        (k ≠ 0 → x ≠ .n (walksT W (slotsT W fold b) first k W.size n 0
          (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)).2) := by
      intro x hx
      obtain ⟨j, rfl, h⟩ := l3 x hx
      refine ⟨fun e => ?_, fun e => ?_, fun hf e => ?_, fun _ e => ?_⟩ <;>
        simp only [V.mk.injEq, true_and] at e <;> rcases h with h | h
      all_goals first | omega | (have := hb0f hf; omega)
    have hssa := armT_ssa (first := first) (prodIn := prodIn) (encIn := encIn)
      (po := groupStart fold b + chainStride W * n) (eo := groupStart fold b + chainStride W * n + 1)
      (k := k) (b := armB W first n fold prodIn encIn b k) hW (by simpa [hk0] using l1)
      (by simpa [hk0] using l2) hpi hei hpw (by omega) hpoB (by omega) (fun hf => ⟨by omega, by omega⟩)
      (by simpa [hk0] using hR)
      (fun _ => ⟨by rw [hws2]; rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega,
        by rw [hws2]; omega, by rw [hws2]; omega, fun hf => by rw [hws2]; have := hb0f hf; omega⟩)
    obtain ⟨kc, ktip⟩ := armT_canon (first := first) (prodIn := prodIn) (encIn := encIn) hW hc
      (by simpa [hk0] using l1) (by simpa [hk0] using l2) (by omega) (by simpa [hk0] using hR) hssa.1 σ hg
      (by simpa [hk0] using hs)
    obtain ⟨σ', he, hp, hh⟩ := fwd_completes (C := C) (rd := rd) (lo := b + 5)
      (hi := armB W first n fold prodIn encIn b (4 ^ n)) hssa.1 (fun x hx => by
        rcases hssa.2 x hx with h | rfl | rfl | ⟨-, rfl⟩ | ⟨-, rfl⟩
        · obtain ⟨j, rfl, h⟩ := l3 x (by simpa [hk0] using h)
          rcases h with h | h
          · exact ⟨j, by omega, by omega, rfl⟩
          · exact ⟨j, by omega, by omega, rfl⟩
        · exact ⟨_, by omega, by omega, rfl⟩
        · exact ⟨_, by omega, by omega, rfl⟩
        · exact ⟨_, by omega, by omega, rfl⟩
        · exact ⟨_, by rw [hws2]; omega, by rw [hws2]; omega, rfl⟩) σ kc
    refine ⟨σ', he, ⟨hp, fun t ht => ?_⟩, hh⟩
    rw [hp]
    exact ktip t ht

end
end LeanVM.Guest.B1.Sig
