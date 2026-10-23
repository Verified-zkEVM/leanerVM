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

theorem NBv.mono' {b b' : Nat} {v : V} (h : NBv b v) (hle : b ≤ b') : NBv b' v := by
  obtain ⟨j, hj, rfl⟩ := h; exact ⟨j, by omega, rfl⟩

theorem StepShape.mono {W : WotsT} {B B' : Nat} (h : StepShape W B) (hle : B ≤ B') : StepShape W B' := by
  intro i s v c o hc ho hco h1 h2
  obtain ⟨a1, a2, a3⟩ := h i s v c o (by omega) (by omega) hco h1 h2
  refine ⟨a1, a2, fun x hx => ?_⟩
  rcases a3 x hx with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (h.mono' hle))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem StepCanon.mono {W : WotsT} {B B' : Nat} {good : Val → Prop} (h : StepCanon W B good)
    (hle : B ≤ B') : StepCanon W B' good :=
  ⟨fun σ σ' hσ hg => h.1 σ σ' (fun k hk => hσ k (by omega)) hg,
    fun i s v c o σ hc ho hco h1 h2 hg hv => h.2 i s v c o σ (by omega) (by omega) hco h1 h2 hg hv⟩

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

end
end LeanVM.Guest.B1.Sig
