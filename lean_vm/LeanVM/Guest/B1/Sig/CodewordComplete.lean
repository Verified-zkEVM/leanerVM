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
open LeanVM.Protocol.Verifier (gen)

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
        (fun σ' => good σ' ∧ ∀ q, p ≤ q → q < p + m → σ' (.n (cwState W b q).2.2) = ofK (gpow (K q)) ∧
          ∀ t < 3, IsCanonical128 (σ' (.n (slotsT W (q == 0) (cwState W b q).2.2 t 2))))
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
      refine (ih.keep (Q := fun σ => σ (.n (cwState W b p).2.2) = ofK (gpow (K p)) ∧ ∀ t < 3,
          IsCanonical128 (σ (.n (slotsT W (p == 0) (cwState W b p).2.2 t 2))))
        (Q' := fun σ => σ (.n (cwState W b p).2.2) = ofK (gpow (K p)) ∧
          ∀ t < 3, IsCanonical128 (σ (.n (slotsT W (p == 0) (cwState W b p).2.2 t 2))))
        hp1 (fun σ' he' hq => ⟨?_, fun t ht => ?_⟩)).mono le_rfl le_rfl (fun σ' ⟨⟨hg', hr⟩, hq'⟩ =>
        ⟨hg', fun q h1 h2 => ?_⟩)
      · have := cwState_le W b p 1
        have := groupT_end W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2
        rw [he'.apply (Or.inl (by rw [cwState_succ]; rw [groupStart_eq] at this; omega))]
        exact hq.1
      · have hs := (slot_bounds W (p == 0) (cwState W b p).2.2 t 2 (by norm_num)).2
        have := groupT_end W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2
        have : chainStride W * (t + 1) ≤ chainStride W * 3 := Nat.mul_le_mul_left _ (by omega)
        rw [he'.apply (Or.inl (by rw [cwState_succ]; omega))]
        exact hq.2 t ht
      · rcases Nat.lt_or_ge q (p + 1) with hq | hq
        · have : q = p := by omega
          subst this
          exact hq'
        · exact hr q hq (by omega)

/-- The digit `i` of the digits `K` of the groups. -/
def digK (K : Nat → Nat) (i : Nat) : Nat := K (i / 3) / 4 ^ (i % 3) % 4

theorem codewordT_eq (W : WotsT) (G : Nat) (target : E) (d0 : V) (b : Nat) :
    (codewordT W G target d0 b).1 =
      (groupsT W G 0 (cwState W b 0).1 (cwState W b 0).2.1 (cwState W b 0).2.2).1 ++
        (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).1 ++
        [copyS d0 (encT W false 1 (cwState W b G).2.2),
          cst (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).2 target,
          .atom (.assertEq (prodT W false 1 (cwState W b G).2.2)
            (.n (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).2))] := by
  have hgs := groupsT_eq W b G 0
  simp only [Nat.zero_add] at hgs
  have hgs' : (groupsT W G 0 (.n 0) (.n 0) b).2 = _ := hgs
  simp only [codewordT]
  rw [hgs']
  rfl

theorem codewordT_snd (W : WotsT) (G : Nat) (target : E) (d0 : V) (b : Nat) :
    (codewordT W G target d0 b).2.1 =
      (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).2 + 1 := by
  have hgs := groupsT_eq W b G 0
  simp only [Nat.zero_add] at hgs
  have hgs' : (groupsT W G 0 (.n 0) (.n 0) b).2 = _ := hgs
  simp only [codewordT]
  rw [hgs']

theorem groupsT_numBelow {W : WotsT} {B : Nat} (hW : StepShape W B) {b : Nat} (hb0 : 0 < b) (hB : B ≤ b)
    (hpw : ∀ j, NBv B (W.power j)) : ∀ m p,
    NumBelow (cwState W b (p + m)).2.2
      (Stmt.valsList (groupsT W m p (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2).1)
  | 0, _ => NumBelow.nil _
  | m + 1, p => by
      have hbp := cwState_mono W b p
      obtain ⟨hpi, hei⟩ := cwState_in W hb0 p
      have h1 := groupT_numBelow (first := 3 * p) (n := 3) (fold := p == 0) hW (show B ≤ (cwState W b p).2.2 by omega)
        hpi hei (fun j => (hpw j).mono' (by omega))
      have h2 := groupsT_numBelow hW hb0 hB hpw m (p + 1)
      have hle := cwState_le W b (p + 1) m
      simp only [groupsT, valsList_append]
      rw [show p + (m + 1) = p + 1 + m by omega]
      exact (h1.mono (by rw [← cwState_succ]; exact hle)).append h2

/-- **The codeword completes**: its groups dispatching on the digits `K`, the digest's first cell
their base-4 number and the target `g` to their sum. -/
theorem codewordT_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) (hWa : StepAtoms W) {F : Val → Nat → Nat → E → E}
    (hss : ∀ σ, good σ → StepSound rd σ W (F σ)) (hpow : ∀ σ, good σ → ∀ s < 10, σ (W.power s) = gen ^ s)
    {G : Nat} {target : E} {d0 : V} {b : Nat} (hG : 0 < G) (hG21 : G ≤ 21) (hb0 : 0 < b) (hB : B ≤ b)
    (hm : MemOK rd 64) (hpw : ∀ j, NBv B (W.power j)) (hd0 : NBv b d0) (K : Nat → Nat) (σ : Val)
    (hg : good σ) (hh : ∀ q ≤ G, GroupHyp W G b K σ q)
    (hsum : gen ^ (∑ i ∈ Finset.range (3 * G + 1), digK K i) = target)
    (hd0v : σ d0 = lit (∑ i ∈ Finset.range (3 * G + 1), digK K i * 4 ^ i)) :
    Completes C rd b (codewordT W G target d0 b).2.1 (codewordT W G target d0 b).1 σ
      (fun σ' => good σ' ∧ ∀ i < 3 * G + 1, IsCanonical128 (σ' (cwTip W b i))) := by
  have hbG := cwState_mono W b G
  obtain ⟨hpiG, heiG⟩ := cwState_in W hb0 G
  have hpwG : ∀ j, NBv (cwState W b G).2.2 (W.power j) := fun j => (hpw j).mono' (by omega)
  have hendL := groupT_end W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2
  rw [groupStart_eq] at hendL
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hendL
  rw [codewordT_eq, codewordT_snd]
  have hnbG := groupsT_numBelow hW hb0 hB hpw G 0
  simp only [Nat.zero_add] at hnbG
  have hnbL := groupT_numBelow (first := 3 * G) (n := 1) (fold := false) hW
    (show B ≤ (cwState W b G).2.2 by omega) hpiG heiG hpwG
  have hfG : (G == 0) = false := by simp; omega
  -- the groups, then the last chain's
  have hgl : Completes C rd b (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1
      (cwState W b G).2.2).2
      ((groupsT W G 0 (cwState W b 0).1 (cwState W b 0).2.1 (cwState W b 0).2.2).1 ++
        (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).1) σ
      (fun σ' => good σ' ∧ (∀ q ≤ G, σ' (.n (cwState W b q).2.2) = ofK (gpow (K q))) ∧
        ∀ i < 3 * G + 1, IsCanonical128 (σ' (cwTip W b i))) := by
    have hgc := groupsT_complete (C := C) (rd := rd) hW hc hb0 hB hm hpw K G 0 (by omega) σ hg
      (fun q _ h2 => hh q (by omega))
    rw [Nat.zero_add] at hgc
    refine Completes.append (m := (cwState W b G).2.2) hbG (by omega) hnbG hgc (fun σ1 he1 hp1 => ?_)
    obtain ⟨hg1, hq1⟩ := hp1
    obtain ⟨g1, g2, g3⟩ := (hh G le_rfl).transfer he1 le_rfl
    have hnG : cwN G G = 1 := by simp [cwN]
    rw [hnG] at g1 g3
    simp only [hfG, Bool.false_eq_true, ↓reduceIte] at g3
    have hlast := groupT_complete (C := C) (rd := rd) (first := 3 * G) (prodIn := (cwState W b G).1)
      (encIn := (cwState W b G).2.1) (fold := false)
      (hW.mono (show B ≤ (cwState W b G).2.2 by omega)) (hc.mono (show B ≤ (cwState W b G).2.2 by omega))
      (by norm_num) g1 hm le_rfl hpiG heiG hpwG σ1 hg1 g2 (by simpa [hnG] using g3)
    refine (hlast.keep (Q := fun σ => good σ ∧ ∀ q < G, σ (.n (cwState W b q).2.2) = ofK (gpow (K q)) ∧
        ∀ t < 3, IsCanonical128 (σ (.n (slotsT W (q == 0) (cwState W b q).2.2 t 2))))
      (Q' := fun σ => good σ ∧ ∀ q < G, σ (.n (cwState W b q).2.2) = ofK (gpow (K q)) ∧
        ∀ t < 3, IsCanonical128 (σ (.n (slotsT W (q == 0) (cwState W b q).2.2 t 2))))
      ⟨hg1, fun q hq => hq1 q (by omega) (by omega)⟩ (fun σ' he' hq => ⟨?_, fun q hqG => ?_⟩)).mono
      le_rfl le_rfl (fun σ' ⟨⟨hhint, htip⟩, hgood, hgr⟩ => ⟨hgood, fun q hq => ?_, fun i hi => ?_⟩)
    · exact hc.1 _ _ (fun j hj => he'.agree j (by omega)) hq.1
    · have hle := cwState_le W b (q + 1) (G - (q + 1))
      rw [show q + 1 + (G - (q + 1)) = G by omega] at hle
      have hend := groupT_end W (3 * q) 3 (q == 0) (cwState W b q).1 (cwState W b q).2.1 (cwState W b q).2.2
      rw [← cwState_succ, groupStart_eq] at hend
      refine ⟨by rw [he'.apply (Or.inl (by split at hend <;> omega))]; exact (hq.2 q hqG).1,
        fun t ht => ?_⟩
      have hs := (slot_bounds W (q == 0) (cwState W b q).2.2 t 2 (by norm_num)).2
      have : chainStride W * (t + 1) ≤ chainStride W * 3 := Nat.mul_le_mul_left _ (by omega)
      rw [groupStart_eq] at hs
      rw [he'.apply (Or.inl (by split at hs <;> split at hend <;> omega))]
      exact (hq.2 q hqG).2 t ht
    · rcases Nat.lt_or_ge q G with hq' | hq'
      · exact (hgr q hq').1
      · have : q = G := by omega
        subst this
        exact hhint
    · unfold cwTip
      rcases Nat.lt_or_ge (i / 3) G with hq' | hq'
      · exact (hgr (i / 3) hq').2 (i % 3) (Nat.mod_lt _ (by norm_num))
      · have h1 : i / 3 = G := by omega
        have h2 : i % 3 = 0 := by omega
        rw [h1, h2, hfG]
        exact htip 0 (by norm_num)
  have hnb1 : NumBelow (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).2
      (Stmt.valsList ((groupsT W G 0 (cwState W b 0).1 (cwState W b 0).2.1 (cwState W b 0).2.2).1 ++
        (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).1)) := by
    rw [valsList_append]
    exact (hnbG.mono (by omega)).append hnbL
  refine Completes.append (m := (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1
    (cwState W b G).2.2).2) (by omega) (Nat.le_succ _) hnb1 hgl.withHolds (fun σ1 he1 hp1 => ?_)
  obtain ⟨⟨hg1, hk1, ht1⟩, hhold⟩ := hp1
  -- the groups' facts
  have hgrp : ∀ p ≤ G, ∃ k < 4 ^ cwN G p, σ1 (.n (cwState W b p).2.2) = ofK (gpow k) ∧
      AtomsHold rd σ1 (cwArm W G b p k).1 := by
    obtain ⟨h1, hg⟩ := groupsT_sound (rd := rd) (σ := σ1) (C := C) hWa b G 0 hhold
    obtain ⟨-, kL, hkL, hxL, haL⟩ := groupT_sound (rest := []) hWa (by simpa using h1)
    intro p hp
    by_cases hpG : p < G
    · obtain ⟨k, hk, hx, ha⟩ := hg p hpG
      simp only [Nat.zero_add] at hk hx ha
      exact ⟨k, by simp only [cwN, hpG, ↓reduceIte]; exact hk, hx, by simpa [cwArm, cwN, hpG] using ha⟩
    · have hpe : p = G := by omega
      subst hpe
      exact ⟨kL, by simpa [cwN] using hkL, hxL, by simpa [cwArm, cwN, hfG] using haL⟩
  obtain ⟨-, hprod, henc⟩ := codeword_vals (hss σ1 hg1) (hpow σ1 hg1) hG hG21 hgrp
  have hdig : ∀ i < 3 * G + 1, cwDigit W G b σ1 i = digK K i := by
    intro i hi
    have hb : 4 ^ cwN G (i / 3) ≤ 2 ^ 64 - 1 := by unfold cwN; split <;> norm_num
    unfold cwDigit cwK digK
    rw [logG_eq (hh (i / 3) (by omega)).1 hb (hk1 (i / 3) (by omega))]
  have hs1 : ∑ i ∈ Finset.range (3 * G + 1), cwDigit W G b σ1 i = ∑ i ∈ Finset.range (3 * G + 1), digK K i :=
    Finset.sum_congr rfl fun i hi => hdig i (Finset.mem_range.mp hi)
  have hs2 : ∑ i ∈ Finset.range (3 * G + 1), cwDigit W G b σ1 i * 4 ^ i =
      ∑ i ∈ Finset.range (3 * G + 1), digK K i * 4 ^ i :=
    Finset.sum_congr rfl fun i hi => by rw [hdig i (Finset.mem_range.mp hi)]
  rw [hs1, hsum] at hprod
  rw [hs2, ← hd0v] at henc
  have hd01 : σ1 d0 = σ d0 := by
    obtain ⟨j, hj, rfl⟩ := hd0
    exact he1.apply (Or.inl hj)
  -- the checks
  set c := (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).2 with hcdef
  have hext : Ext c (c + 1) σ1 (upds σ1 [(c, target)]) := upds_ext σ1 _ (by simp)
  have hpo : (prodT W false 1 (cwState W b G).2.2) = .n (groupStart false (cwState W b G).2.2 + chainStride W * 1) :=
    rfl
  have heo : (encT W false 1 (cwState W b G).2.2) = .n (groupStart false (cwState W b G).2.2 + chainStride W * 1 + 1) :=
    rfl
  have hgs : groupStart false (cwState W b G).2.2 = (cwState W b G).2.2 + 5 := by simp [groupStart]
  have hpv : upds σ1 [(c, target)] (prodT W false 1 (cwState W b G).2.2) = target := by
    rw [hpo, hext.apply (Or.inl (by rw [hgs]; omega)), ← hpo, hprod]
  have hev : upds σ1 [(c, target)] (encT W false 1 (cwState W b G).2.2) = σ d0 := by
    rw [heo, hext.apply (Or.inl (by rw [hgs]; omega)), ← heo, henc]
  have hdv : upds σ1 [(c, target)] d0 = σ d0 := by
    obtain ⟨j, hj, rfl⟩ := hd0
    rw [hext.apply (Or.inl (by omega))]
    exact hd01
  refine completes_atoms rfl hext ⟨hc.1 _ _ (fun j hj => hext.agree j (by omega)) hg1, fun i hi => ?_⟩
    (fun a ha => ?_)
  · have := ht1 i hi
    unfold cwTip at this ⊢
    have hlt : slotsT W (i / 3 == 0) (cwState W b (i / 3)).2.2 (i % 3) 2 < c := by
      have hs := (slot_bounds W (i / 3 == 0) (cwState W b (i / 3)).2.2 (i % 3) 2 (by norm_num)).2
      rcases Nat.lt_or_ge (i / 3) G with hq | hq
      · have hle := cwState_le W b (i / 3 + 1) (G - (i / 3 + 1))
        rw [show i / 3 + 1 + (G - (i / 3 + 1)) = G by omega] at hle
        have hend := groupT_end W (3 * (i / 3)) 3 (i / 3 == 0) (cwState W b (i / 3)).1
          (cwState W b (i / 3)).2.1 (cwState W b (i / 3)).2.2
        rw [← cwState_succ] at hend
        have : chainStride W * (i % 3 + 1) ≤ chainStride W * 3 := Nat.mul_le_mul_left _ (by omega)
        omega
      · have h1 : i / 3 = G := by omega
        have h2 : i % 3 = 0 := by omega
        rw [h1, h2, hfG] at hs ⊢
        rw [hgs] at hs
        omega
    rw [hext.apply (Or.inl hlt)]
    exact this
  · simp only [copyS, cst, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · show upds σ1 [(c, target)] d0 = upds σ1 [(c, target)] (encT W false 1 (cwState W b G).2.2)
      rw [hdv, hev]
    · exact upds_cons_self σ1 c target []
    · show upds σ1 [(c, target)] _ + upds σ1 [(c, target)] (.n c) = 0
      rw [hpv, upds_cons_self]
      exact e_add_self _

end
end LeanVM.Guest.B1.Sig
