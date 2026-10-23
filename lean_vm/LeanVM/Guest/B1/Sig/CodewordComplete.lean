/-
  LeanVM.Guest.B1.Sig.CodewordComplete

  The WOTS+C codeword completes: its groups dispatch on the digits hinted, the encoding is the
  digest's first cell and the product the target.
-/

module

public import LeanVM.Guest.B1.Sig.CwComplete
public import LeanVM.Guest.B1.Sig.Codeword

/-!
# The codeword, complete

* `StepShape.mono`, `StepCanon.mono`: a step's shape above a larger bound;
* `Completes.withHolds`: a completed block holds of its valuation;
* `GroupHyp`: group `q`'s digits `K q` hinted and its arm's starts canonical;
* `groupT_end`, `groupsT_complete`: the groups complete in sequence.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem Completes.withHolds {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : Completes C rd lo hi ss σ P) :
    Completes C rd lo hi ss σ (fun σ' => P σ' ∧ Stmt.HoldsList C rd σ' ss True (fun _ => True)) :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', he, ⟨hp, hh True (fun _ => True) trivial⟩, hh⟩

/-- Group `q`'s digits `K q` hinted at its base and its arm's starts canonical. -/
def GroupHyp (W : WotsT) (G b : Nat) (K : Nat → Nat) (σ : Val) (q : Nat) : Prop :=
  K q < 4 ^ cwN G q ∧ σ (.n (cwState W b q).2.2) = ofK (gpow (K q)) ∧
    ∀ t < cwN G q, StartCanon σ (slotsT W (q == 0) (cwState W b q).2.2 t) (dig (K q) t)
      (walkBase (if K q = 0 then W.size + 13 else W.size) (K q) 0 t
        (if (q == 0) then armB W (3 * q) (cwN G q) (q == 0) (cwState W b q).1 (cwState W b q).2.1
            (cwState W b q).2.2 (K q) + 1
          else armB W (3 * q) (cwN G q) (q == 0) (cwState W b q).1 (cwState W b q).2.1
            (cwState W b q).2.2 (K q)))

theorem groupT_end (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b : Nat) :
    groupStart fold b + chainStride W * n + 2 ≤ (groupT W first n fold prodIn encIn b).2 := by
  have : (groupT W first n fold prodIn encIn b).2 = armB W first n fold prodIn encIn b (4 ^ n) := by
    simp only [groupT]; rw [armsT_snd]; rfl
  rw [this, ← armB_one W first n fold prodIn encIn b]
  exact armB_mono W first n fold prodIn encIn b (Nat.one_le_two_pow.trans
    (Nat.pow_le_pow_left (by norm_num) n))

theorem cwState_succ (W : WotsT) (b p : Nat) :
    (cwState W b (p + 1)).2.2 = (groupT W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1
      (cwState W b p).2.2).2 := rfl

theorem cwState_mono (W : WotsT) (b : Nat) : ∀ p, b ≤ (cwState W b p).2.2
  | 0 => le_rfl
  | p + 1 => by
      rw [cwState_succ]
      have := groupT_end W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2
      have := cwState_mono W b p
      rw [groupStart_eq] at *
      omega

theorem Completes.keep {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop} {Q Q' : Val → Prop}
    (h : Completes C rd lo hi ss σ P) (hq : Q σ) (ht : ∀ σ', Ext lo hi σ σ' → Q σ → Q' σ') :
    Completes C rd lo hi ss σ (fun σ' => P σ' ∧ Q' σ') :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', he, ⟨hp, ht σ' he hq⟩, hh⟩

theorem armB_ge (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b k : Nat) :
    b + 5 ≤ armB W first n fold prodIn encIn b k := by
  rw [← armB_zero W first n fold prodIn encIn b]
  exact armB_mono W first n fold prodIn encIn b (Nat.zero_le _)

/-- A group's facts above its base survive changes below. -/
theorem GroupHyp.transfer {W : WotsT} {G b : Nat} {K : Nat → Nat} {σ σ' : Val} {q lo hi : Nat}
    (h : GroupHyp W G b K σ q) (he : Ext lo hi σ σ') (hhi : hi ≤ (cwState W b q).2.2) :
    GroupHyp W G b K σ' q := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, by rw [he.apply (Or.inr hhi)]; exact h2, fun t ht => ?_⟩
  have := h3 t ht
  unfold StartCanon at this ⊢
  have hab := armB_ge W (3 * q) (cwN G q) (q == 0) (cwState W b q).1 (cwState W b q).2.1
    (cwState W b q).2.2 (K q)
  have hwb := walkBase_le (if K q = 0 then W.size + 13 else W.size) (K q)
    (if (q == 0) then armB W (3 * q) (cwN G q) (q == 0) (cwState W b q).1 (cwState W b q).2.1
        (cwState W b q).2.2 (K q) + 1
      else armB W (3 * q) (cwN G q) (q == 0) (cwState W b q).1 (cwState W b q).2.1
        (cwState W b q).2.2 (K q)) (Nat.zero_le t)
  simp only [walkBase] at hwb
  have hb0 : armB W (3 * q) (cwN G q) (q == 0) (cwState W b q).1 (cwState W b q).2.1
        (cwState W b q).2.2 (K q) ≤ (if (q == 0) then armB W (3 * q) (cwN G q) (q == 0) (cwState W b q).1
          (cwState W b q).2.1 (cwState W b q).2.2 (K q) + 1
        else armB W (3 * q) (cwN G q) (q == 0) (cwState W b q).1 (cwState W b q).2.1
          (cwState W b q).2.2 (K q)) := by split <;> omega
  have hsl := (slot_bounds W (q == 0) (cwState W b q).2.2 t 2 (by norm_num)).1
  have hgs : (cwState W b q).2.2 + 5 ≤ groupStart (q == 0) (cwState W b q).2.2 := by
    rw [groupStart_eq]; split <;> omega
  obtain ⟨j, e, hj⟩ := start_ge (W := W) (fold := q == 0) (b := (cwState W b q).2.2) (k := K q) (t := t)
    (lo := (cwState W b q).2.2)
    (le_trans (show (cwState W b q).2.2 ≤ armB W (3 * q) (cwN G q) (q == 0) (cwState W b q).1
      (cwState W b q).2.1 (cwState W b q).2.2 (K q) by omega) (le_trans hb0 hwb)) (by omega)
  rw [e] at this ⊢
  rw [he.apply (Or.inr (by omega))]
  exact this

theorem cwState_in (W : WotsT) {b : Nat} (hb : 0 < b) :
    ∀ p, NBv (cwState W b p).2.2 (cwState W b p).1 ∧ NBv (cwState W b p).2.2 (cwState W b p).2.1
  | 0 => ⟨⟨0, hb, rfl⟩, ⟨0, hb, rfl⟩⟩
  | p + 1 => by
      have := groupT_end W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2
      rw [cwState_succ]
      exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩

theorem cwState_le (W : WotsT) (b p : Nat) : ∀ m, (cwState W b p).2.2 ≤ (cwState W b (p + m)).2.2
  | 0 => le_rfl
  | m + 1 => by
      have := cwState_le W b p m
      have h2 := groupT_end W (3 * (p + m)) 3 (p + m == 0) (cwState W b (p + m)).1
        (cwState W b (p + m)).2.1 (cwState W b (p + m)).2.2
      rw [show p + (m + 1) = p + m + 1 by omega, cwState_succ]
      rw [groupStart_eq] at h2
      omega

/-- **The groups of a codeword complete.** -/
theorem groupsT_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) {G b : Nat} (hb0 : 0 < b) (hB : B ≤ b) (hm : MemOK rd 64)
    (hpw : ∀ j, NBv B (W.power j)) (K : Nat → Nat) :
    ∀ m p, p + m ≤ G → ∀ σ, good σ → (∀ q, p ≤ q → q < p + m → GroupHyp W G b K σ q) →
      Completes C rd (cwState W b p).2.2 (cwState W b (p + m)).2.2
        (groupsT W m p (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2).1 σ
        (fun σ' => good σ' ∧ ∀ q, p ≤ q → q < p + m → ∀ t < 3,
          IsCanonical128 (σ' (.n (slotsT W (q == 0) (cwState W b q).2.2 t 2))))
  | 0, p, _, σ, hg, _ => ⟨σ, Ext.refl _ _ _, ⟨hg, fun q h1 h2 => by omega⟩, fun _ _ hn => hn⟩
  | m + 1, p, hpm, σ, hg, hh => by
      have hbp := cwState_mono W b p
      have hBp : B ≤ (cwState W b p).2.2 := by omega
      obtain ⟨hpi, hei⟩ := cwState_in W hb0 p
      have hpwp : ∀ j, NBv (cwState W b p).2.2 (W.power j) := fun j => (hpw j).mono' hBp
      obtain ⟨g1, g2, g3⟩ := hh p le_rfl (by omega)
      have hn : cwN G p = 3 := by simp [cwN]; omega
      rw [hn] at g1 g3
      have hgroup := groupT_complete (C := C) (rd := rd) (first := 3 * p) (hW.mono hBp) (hc.mono hBp)
        (le_refl 3) g1 hm le_rfl hpi hei hpwp σ hg g2 g3
      have hnb := groupT_numBelow (first := 3 * p) (n := 3) (fold := p == 0) hW hBp hpi hei hpwp
      have hle := cwState_le W b (p + 1) m
      simp only [groupsT]
      refine Completes.append (m := (cwState W b (p + 1)).2.2) (cwState_le W b p 1)
        (by rw [show p + (m + 1) = p + 1 + m by omega]; exact hle) hnb hgroup (fun σ1 he1 hp1 => ?_)
      have hag : AgreeBelow B σ σ1 := fun k hk => he1.agree k (by omega)
      have hg1 := hc.1 _ _ hag hg
      have ih := groupsT_complete hW hc hb0 hB hm hpw K m (p + 1) (by omega) σ1 hg1 (fun q h1 h2 =>
        (hh q (by omega) (by omega)).transfer he1 (by
          have := cwState_le W b (p + 1) (q - (p + 1))
          rw [show p + 1 + (q - (p + 1)) = q by omega] at this
          exact this))
      rw [show p + (m + 1) = p + 1 + m by omega]
      refine (ih.keep (Q := fun σ => ∀ t < 3,
          IsCanonical128 (σ (.n (slotsT W (p == 0) (cwState W b p).2.2 t 2))))
        (Q' := fun σ => ∀ t < 3, IsCanonical128 (σ (.n (slotsT W (p == 0) (cwState W b p).2.2 t 2))))
        hp1 (fun σ' he' hq t ht => ?_)).mono le_rfl le_rfl (fun σ' ⟨⟨hg', hr⟩, hq'⟩ =>
        ⟨hg', fun q h1 h2 => ?_⟩)
      · have hs := (slot_bounds W (p == 0) (cwState W b p).2.2 t 2 (by norm_num)).2
        have := groupT_end W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2
        have : chainStride W * (t + 1) ≤ chainStride W * 3 := Nat.mul_le_mul_left _ (by omega)
        rw [he'.apply (Or.inl (by rw [cwState_succ]; omega))]
        exact hq t ht
      · rcases Nat.lt_or_ge q (p + 1) with hq | hq
        · have : q = p := by omega
          subst this
          exact hq'
        · exact hr q hq (by omega)

end
end LeanVM.Guest.B1.Sig
