/-
  LeanVM.Guest.B1.Sig.SpWotsGroupComplete

  A digit group of `sp_wots` completes: its digit word `g^k` hinted, its range check on a memory of
  at least `64` words, its dispatch taking arm `k`, whose chains' starts are loaded.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsArmComplete
public import LeanVM.Guest.B1.Sig.SpWotsCheck
public import LeanVM.Guest.B1.Sig.CwComplete

/-!
# A group, complete

* `spGroupT_complete`: a group from base `B` completes on `B ..< end`, from any valuation whose
  `pp` and address are canonical: its digit word `g^k` at `B`, its arm `k`'s tips canonical and
  starts holding `vals`;
* `spGroupP_complete`: group `p` of the body, its numbers checked (`spLayout_all`, `spPad_all`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem spGroupT_fst_eq (first n : Nat) (fold : Bool) (prodIn encIn : V) (B : Nat) :
    (spGroupT first n fold prodIn encIn B).1 = [hintW "digits" [.n B]] ++
      (rangeS (.n B) (word (2 ^ (4 ^ n - 1)) 0 0) (B + 1) ++
        [.match_ (.n B) (spArmsT first n fold B prodIn encIn (4 ^ n) 0 (B + 5)).1]) := rfl

theorem spArmB_ge (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) :
    ∀ k, B + 5 ≤ spArmB first n fold B prodIn encIn k
  | 0 => le_rfl
  | k + 1 => by
      have ih := spArmB_ge first n fold B prodIn encIn k
      rw [spArmB_succ, spArmEnd, spArmV, armT_snd]
      have := walkBase_le (if k = 0 then spW.size + 13 else spW.size) k
        (if fold then spArmB first n fold B prodIn encIn k + 1 else spArmB first n fold B prodIn encIn k)
        (Nat.zero_le n)
      simp only [walkBase] at this
      split <;> split at this <;> cases fold <;> simp_all <;> omega

/-- **A group completes**, its digit word `g^k` loaded at its base. -/
theorem spGroupT_complete {first n : Nat} {fold : Bool} {B : Nat} {prodIn encIn : V} {k : Nat}
    (hn0 : 0 < n) (hn : n ≤ 3) (hk : k < 4 ^ n) (hm : MemOK rd 64) (hB : 13 ≤ B) (hpi : NBv B prodIn)
    (hei : NBv B encIn) (hend : spArmB first n fold B prodIn encIn (4 ^ n) + 5 < spVPad)
    (hlay : spLayoutOK first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k) = true)
    (hpad : spPadOK first n fold B prodIn encIn k = true)
    (σ : Val) (hg0 : IsCanonical128 (σ (.n 0))) (hg1 : IsCanonical128 (σ (.n 1))) (vals : Nat → E)
    (hv : ∀ t < n, IsCanonical128 (vals t)) :
    Completes C rd B (spGroupT first n fold prodIn encIn B).2 (spGroupT first n fold prodIn encIn B).1 σ
      (fun σ' => σ' (.n B) = ofK (addressOfIndex k) ∧ SpArmPost first n fold B prodIn encIn k vals σ') := by
  have h4n : 4 ^ n ≤ 64 := by
    calc 4 ^ n ≤ 4 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 64 := by norm_num
  have hge := spArmB_ge first n fold B prodIn encIn (4 ^ n)
  rw [spGroupT_end, spGroupT_fst_eq]
  set σL := Function.update σ (.n B) (ofK (addressOfIndex k)) with hσL
  have hextL : Ext B (spArmB first n fold B prodIn encIn (4 ^ n)) σ σL := fun v hv =>
    Function.update_of_ne (fun e => hv B le_rfl (by omega) e) _ _
  have hb : σL (.n B) = ofK (addressOfIndex k) := Function.update_self ..
  refine Completes.reload hextL ?_
  refine Completes.append (m := B + 1) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨B, by omega, rfl⟩ (.nil _)) (hintKeep_complete σL _ _ _ _)
    (fun σ1 he1 hp1 => ?_)
  rw [hp1, word_two_pow_eq (by omega)]
  refine Completes.append (m := B + 5) (by omega) hge ?_
    (rangeS_complete (n := 64) (K := 4 ^ n) hm h4n hk σL (.n B) ⟨B, by omega, rfl⟩ hb)
    (fun σ2 he2 _ => ?_)
  · simp only [rangeS, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
      List.cons_append, List.nil_append]
    repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))
  have hag : AgreeBelow (B + 1) σL σ2 := he2.agree
  have hb2 : σ2 (.n B) = ofK (addressOfIndex k) := by rw [← hag B (by omega)]; exact hb
  have hk' : k < (spArmsT first n fold B prodIn encIn (4 ^ n) 0 (B + 5)).1.length := by
    rw [spArmsT_length]; exact hk
  refine match_complete hk' ⟨B, by omega, rfl⟩ hb2 ?_
  rw [spGroupArm _ _ _ _ _ _ _ hk']
  have h0 : σ2 (.n 0) = σ (.n 0) := by
    rw [← hag 0 (by omega), hσL, Function.update_of_ne (by simp; omega)]
  have h1 : σ2 (.n 1) = σ (.n 1) := by
    rw [← hag 1 (by omega), hσL, Function.update_of_ne (by simp; omega)]
  obtain ⟨σ', he', hp', hh'⟩ := (spArm_complete (C := C) (rd := rd) (k := k) hn0 hn hB hpi hei hend hlay
    hpad σ2 (by rw [h0]; exact hg0) (by rw [h1]; exact hg1) vals hv).1
  exact ⟨σ', he', ⟨by rw [he'.apply (Or.inl (by omega))]; exact hb2, hp'⟩, hh'⟩

theorem spN_pos (p : Nat) : 0 < spN p := by unfold spN; split <;> omega

theorem spN_le (p : Nat) : spN p ≤ 3 := by unfold spN; split <;> omega

/-- **Group `p` of the body completes**, its digit word `g^k` loaded. -/
theorem spGroupP_complete {p k : Nat} (hp : p < 22) (hk : k < 4 ^ spN p) (hm : MemOK rd 64)
    (σ : Val) (hg0 : IsCanonical128 (σ (.n 0))) (hg1 : IsCanonical128 (σ (.n 1))) (vals : Nat → E)
    (hv : ∀ t < spN p, IsCanonical128 (vals t)) :
    Completes C rd (spState p).2.2
      (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).2
      (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).1 σ
      (fun σ' => σ' (.n (spState p).2.2) = ofK (addressOfIndex k) ∧
        SpArmPost (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k vals σ') := by
  have hg := spGroupPad_all hp
  simp only [spGroupPadOK, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨-, hpi1⟩, hpi2⟩, hei1⟩, hei2⟩, hB⟩, hend⟩ := hg
  exact spGroupT_complete (spN_pos p) (spN_le p) hk hm hB ⟨_, hpi2, hpi1⟩ ⟨_, hei2, hei1⟩ hend
    (spLayout_all hp hk) (spPad_all hp hk) σ hg0 hg1 vals hv

/-- **A group's values are numbered below its end**, every arm's numbers checked. -/
theorem spGroupT_nb {first n : Nat} {fold : Bool} {B : Nat} {prodIn encIn : V}
    (hn0 : 0 < n) (hn : n ≤ 3) (hB : 13 ≤ B) (hpi : NBv B prodIn)
    (hei : NBv B encIn) (hend : spArmB first n fold B prodIn encIn (4 ^ n) + 5 < spVPad)
    (hlay : ∀ k < 4 ^ n, spLayoutOK first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k) = true)
    (hpad : ∀ k < 4 ^ n, spPadOK first n fold B prodIn encIn k = true) :
    NumBelow (spGroupT first n fold prodIn encIn B).2 (Stmt.valsList (spGroupT first n fold prodIn encIn B).1) := by
  have hge := spArmB_ge first n fold B prodIn encIn (4 ^ n)
  rw [spGroupT_end, spGroupT_fst_eq]
  simp only [List.cons_append, valsList_cons, valsList_append, hintW, rangeS, cst]
  intro x hx
  simp only [Stmt.vals, Atom.vals, Hint.vals, Dest.vals, valsList_nil,
    List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  have key : x = .n B ∨ x = .n (B + 1) ∨ x = .n (B + 1 + 1) ∨ x = .n (B + 1 + 2) ∨
      x = .n (B + 1 + 3) ∨ x ∈ Stmt.valsArms (spArmsT first n fold B prodIn encIn (4 ^ n) 0 (B + 5)).1 := by
    tauto
  clear hx
  rcases key with rfl | rfl | rfl | rfl | rfl | hx
  all_goals first | exact ⟨_, by omega, rfl⟩ | skip
  refine numBelow_valsArms _ (fun arm ha => ?_) x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  have hk' := hk
  rw [spArmsT_length] at hk'
  rw [spGroupArm _ _ _ _ _ _ _ hk]
  exact (spArm_complete (C := fun _ _ _ => True) (rd := fun _ => none) hn0 hn hB hpi hei hend
    (hlay k hk') (hpad k hk') (fun _ => 0) canon_zero canon_zero (fun _ => 0) (fun _ _ => canon_zero)).2

/-- **Group `p`'s values are numbered below its end.** -/
theorem spGroupP_nb {p : Nat} (hp : p < 22) :
    NumBelow (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).2
      (Stmt.valsList (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).1) := by
  have hg := spGroupPad_all hp
  simp only [spGroupPadOK, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨-, hpi1⟩, hpi2⟩, hei1⟩, hei2⟩, hB⟩, hend⟩ := hg
  exact spGroupT_nb (spN_pos p) (spN_le p) hB ⟨_, hpi2, hpi1⟩ ⟨_, hei2, hei1⟩ hend
    (fun k hk => spLayout_all hp hk) (fun k hk => spPad_all hp hk)

end
end LeanVM.Guest.B1.Sig
