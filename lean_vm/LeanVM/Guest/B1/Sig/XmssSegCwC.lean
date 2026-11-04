/-
  LeanVM.Guest.B1.Sig.XmssSegCwC

  The dispatches of leanXMSS's codeword inline in `__loop2` complete: an arm `k` below `4^n` is
  `armT`'s, and a group's dispatch completes by the arm of its honest digits.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegStepC
public import LeanVM.Guest.B1.Sig.WotsGroupComplete

/-!
# The codeword's dispatches, complete

* `armM_eq`, `armsM_eq`: arm `k < 4^n` of a group is `armT`'s; the `4^4` arms of a group of four
  are `armsT`'s;
* `armsM_append`: the arms of a table split at an arm;
* `matchArm_complete`: a dispatch on `d` whose arm `k` is `armT`'s from `armB … k`, its chains'
  starts `vals` loaded: the arm's atoms, its tips canonical and its starts kept, the step's reads
  (`good`) kept.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The arms -/

theorem armM_eq (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) {k : Nat} (b : Nat) (hk : k < 4 ^ n) :
    armM W slots first n fold prodIn encIn prodOut encOut k b =
      armT W slots first n fold prodIn encIn prodOut encOut k b := by
  simp only [armM, armT, Nat.mod_eq_of_lt hk]

theorem armsM_eq (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : ∀ (m k b : Nat), k + m ≤ 4 ^ n →
    armsM W slots first n fold prodIn encIn prodOut encOut m k b =
      armsT W slots first n fold prodIn encIn prodOut encOut m k b
  | 0, _, _, _ => rfl
  | m + 1, k, b, h => by
      simp only [armsM, armsT, armM_eq W slots first n fold prodIn encIn prodOut encOut b
        (show k < 4 ^ n by omega)]
      rw [armsM_eq W slots first n fold prodIn encIn prodOut encOut m (k + 1) _ (by omega)]

theorem armsM_append (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (m : Nat) : ∀ (j k b : Nat),
    armsM W slots first n fold prodIn encIn prodOut encOut (j + m) k b =
      ((armsM W slots first n fold prodIn encIn prodOut encOut j k b).1 ++
        (armsM W slots first n fold prodIn encIn prodOut encOut m (k + j)
          (armsM W slots first n fold prodIn encIn prodOut encOut j k b).2).1,
        (armsM W slots first n fold prodIn encIn prodOut encOut m (k + j)
          (armsM W slots first n fold prodIn encIn prodOut encOut j k b).2).2)
  | 0, k, b => by simp [armsM]
  | j + 1, k, b => by
      rw [show j + 1 + m = (j + m) + 1 by omega]
      simp only [armsM]
      rw [armsM_append W slots first n fold prodIn encIn prodOut encOut m j (k + 1),
        show k + 1 + j = k + (j + 1) by omega]
      rfl

theorem armsM_length (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) :
    ∀ m k b, (armsM W slots first n fold prodIn encIn prodOut encOut m k b).1.length = m
  | 0, _, _ => rfl
  | m + 1, k, b => by simp [armsM, armsM_length W slots first n fold prodIn encIn prodOut encOut m]

/-! ## A group's dispatch -/

/-- **A group's dispatch completes** by arm `k`, `armT`'s from `armB … k`, its starts `vals`
loaded, the dispatch's end `Ee` past the arms. -/
theorem matchArm_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) (hWa : StepAtoms W) {first n : Nat} {fold : Bool} {prodIn encIn : V}
    {b k d Ee : Nat} {arms : List (List Stmt)} (hk : k < 4 ^ n) (hB : B ≤ b + 6) (hpi : NBv B prodIn)
    (hei : NBv B encIn) (hpw : NBv B (W.power (digitSum k n))) (hkl : k < arms.length)
    (harm : arms[k] = (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b)
      (encT W fold n b) k (armB W first n fold prodIn encIn b k)).1)
    (hE : armB W first n fold prodIn encIn b (4 ^ n) ≤ Ee) (hd : d < b + 6) (vals : Nat → E)
    (hv : ∀ t < n, IsCanonical128 (vals t)) (σ : Val) (hg : good σ)
    (hx : σ (.n d) = ofK (addressOfIndex k)) :
    Completes C rd (b + 6) Ee [.match_ (.n d) arms] σ
      (fun σ' => good σ' ∧ (∀ t < n, IsCanonical128 (σ' (.n (slotsT W fold b t 2)))) ∧
        (∀ t < n, σ' (grpPos W first n fold prodIn encIn b k t) = vals t) ∧
        AtomsHold rd σ' (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b)
          (encT W fold n b) k (armB W first n fold prodIn encIn b k)).1) := by
  set σr := sLoad (grpPos W first n fold prodIn encIn b k) vals σ n with hσr
  have hpos : ∀ t < n, ∃ j, grpPos W first n fold prodIn encIn b k t = .n j ∧ b + 6 ≤ j ∧
      j < armB W first n fold prodIn encIn b (4 ^ n) := fun t ht => by
    obtain ⟨j, e, h1, h2, -⟩ := grpPos_spec W first n fold prodIn encIn b k t hk ht
    exact ⟨j, e, h1, h2⟩
  have hext : Ext (b + 6) (armB W first n fold prodIn encIn b (4 ^ n)) σ σr := fun v hv =>
    sLoad_other _ _ σ n fun t ht e => by
      obtain ⟨j, ej, h1, h2⟩ := hpos t ht
      rw [ej] at e
      exact hv j h1 h2 e
  have hat : ∀ t < n, σr (grpPos W first n fold prodIn encIn b k t) = vals t :=
    sLoad_at _ vals σ n (fun a c h1 h2 => grpPos_ne hk h1 h2)
  have hgr : good σr := hc.1 _ _ (fun j hj => (hext.apply (Or.inl (by omega))).symm) hg
  have hxr : σr (.n d) = ofK (addressOfIndex k) := by rw [hext.apply (Or.inl hd)]; exact hx
  refine Completes.reload (hext.mono le_rfl hE) (match_complete hkl ⟨d, hd, rfl⟩ hxr ?_)
  rw [harm]
  obtain ⟨σ', he', hp', hh'⟩ := groupArm_complete (C := C) (rd := rd) (first := first) (n := n)
    (fold := fold) (prodIn := prodIn) (encIn := encIn) (b := b) (k := k) hW hc hk hB hpi hei hpw σr hgr
    (fun t ht => by
      show IsCanonical128 (σr (grpPos W first n fold prodIn encIn b k t))
      rw [hat t ht]
      exact hv t ht)
  refine ⟨σ', he'.mono le_rfl hE, ⟨hc.1 _ _ (fun j hj => (he'.apply (Or.inl (by omega))).symm) hgr,
    hp'.2.1, fun t ht => ?_, atomsHold_of_holdsList (armT_atoms hWa ..)
      (hh' True (fun _ => True) trivial)⟩, hh'⟩
  obtain ⟨j, ej, -⟩ := hpos t ht
  rw [hp'.1, ej, fwd_hint_keep _ σr hp'.2.2
    (armStart_mem W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) k
      (armB W first n fold prodIn encIn b k) ht) (.n j) (by rw [← ej]; exact List.mem_singleton_self _),
    ← ej, hat t ht]

end
end LeanVM.Guest.B1.Sig
