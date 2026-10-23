/-
  LeanVM.Guest.B1.Sig.CwComplete

  A WOTS+C group completes: its digits hinted, their range check on a memory of at least `4^n`
  words, the dispatch taking the arm of the digits.
-/

module

public import LeanVM.Guest.B1.Sig.WotsGroupComplete
public import LeanVM.Guest.B1.Sig.Interface

/-!
# A group, complete

* `hintKeep_complete`: a hint completes keeping the valuation;
* `rangeS_complete`: a range check of `g^k`, `k < K ≤ n`, completes on a memory of `n` words;
* `holdsArms_of`, `match_complete`: a dispatch completes by its arm;
* `groupT_complete`: a group of digits `k`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem hintKeep_complete (σ : Val) (s : String) (vs : List V) (lo hi : Nat) :
    Completes C rd lo hi [hintW s vs] σ (fun σ' => σ' = σ) :=
  completes_atoms rfl (Ext.refl _ _ _) rfl (fun a ha => by
    simp only [hintW, List.mem_singleton, Stmt.atom.injEq] at ha
    subst ha
    trivial)

theorem load_gpow {n : Nat} (hm : MemOK rd n) {i : Nat} (hi : i < n) :
    ∃ w, LoadHolds rd (ofK (gpow i)) 0 w := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hm i hi)
  refine ⟨w, (isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  simp only [limb_ofK, Fin.isValue, gpow, pow_zero, mul_one]
  simpa [gpow] using hw

/-- **A range check of `g^k` completes**, `k < K`, on a memory of `n ≥ K` words. -/
theorem rangeS_complete {n K k : Nat} (hm : MemOK rd n) (hK : K ≤ n) (hk : k < K) (σ : Val) (x : V)
    {b : Nat} (hx : ∃ j < b, x = .n j) (hxv : σ x = ofK (gpow k)) :
    Completes C rd b (b + 4) (rangeS x (ofK (gpow (K - 1))) b) σ (fun _ => True) := by
  obtain ⟨t1, h1⟩ := load_gpow hm (show k < n by omega)
  obtain ⟨t2, h2⟩ := load_gpow hm (show K - 1 - k < n by omega)
  set σ' := upds σ [(b, ofK (gpow (K - 1))), (b + 1, ofK (gpow (K - 1 - k))), (b + 2, t1), (b + 3, t2)]
  have hext : Ext b (b + 4) σ σ' := upds_ext σ _ (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp)
  have hx' : σ' x = σ x := by
    obtain ⟨j, hj, rfl⟩ := hx
    exact hext.apply (Or.inl hj)
  have e0 : σ' (.n b) = ofK (gpow (K - 1)) := by simp [σ', upds]
  have e1 : σ' (.n (b + 1)) = ofK (gpow (K - 1 - k)) := by simp [σ', upds]
  have e2 : σ' (.n (b + 2)) = t1 := by simp [σ', upds]
  have e3 : σ' (.n (b + 3)) = t2 := by simp [σ', upds]
  refine completes_atoms rfl hext trivial (fun a ha => ?_)
  simp only [rangeS, cst, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact e0
  · refine ⟨by rw [hx', hxv, e2]; exact h1, ?_, by rw [e1, e3]; exact h2⟩
    rw [e0, hx', hxv, e1, ← ofK_mul, gpow, gpow, gpow, ← pow_add]
    congr 2
    omega

theorem holdsArms_of {x : V} {σ : Val} : ∀ (arms : List (List Stmt)) (j0 k : Nat) (hk : k < arms.length)
    {N : Prop} {kret : List E → Prop}, σ x = ofK (gpow (j0 + k)) →
    Stmt.HoldsList C rd σ arms[k] N kret → Stmt.HoldsArms C rd σ x j0 arms N kret
  | [], _, _, hk, _, _, _, _ => absurd hk (by simp)
  | a :: as, j0, 0, _, _, _, hx, h => Or.inl ⟨by simpa using hx, h⟩
  | a :: as, j0, k + 1, hk, _, _, hx, h =>
      Or.inr (holdsArms_of as (j0 + 1) k (by simpa using hk)
        (by rw [hx]; congr 2; omega) h)

/-- **A dispatch completes** by the arm its value selects. -/
theorem match_complete {x : V} {arms : List (List Stmt)} {k lo hi : Nat} (hk : k < arms.length)
    (hx : ∃ j < lo, x = .n j) {σ : Val} (hxv : σ x = ofK (gpow k)) {Post : Val → Prop}
    (h : Completes C rd lo hi arms[k] σ Post) :
    Completes C rd lo hi [.match_ x arms] σ Post := by
  obtain ⟨σ', he, hp, hh⟩ := h
  refine ⟨σ', he, hp, fun next kret hn => ?_⟩
  have hx' : σ' x = σ x := by
    obtain ⟨j, hj, rfl⟩ := hx
    exact he.apply (Or.inl hj)
  exact holdsArms_of arms 0 k hk (by rw [hx', hxv, Nat.zero_add]) (hh next kret hn)

end
end LeanVM.Guest.B1.Sig
