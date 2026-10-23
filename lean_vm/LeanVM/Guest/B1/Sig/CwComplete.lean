/-
  LeanVM.Guest.B1.Sig.CwComplete

  A WOTS+C group completes: its digits hinted, their range check on a memory of at least `4^n`
  words, the dispatch taking the arm of the digits.
-/

module

public import LeanVM.Guest.B1.Sig.WotsGroupComplete
public import LeanVM.Guest.B1.Sig.Interface
public import LeanVM.Guest.B1.Sig.Shifts

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

theorem word_two_pow_eq {j : Nat} (hj : j < 64) : word (2 ^ j) 0 0 = ofK (gpow j) := by
  rw [word_eq_eOfNat, ← Value.gen_pow_eq_eOfNat hj, Value.gen_pow_eq_ofK]

theorem start_ge {W : WotsT} {fold : Bool} {b k t lo : Nat} {base : Nat}
    (h1 : lo ≤ base) (h2 : lo ≤ slotsT W fold b t 2) :
    ∃ j, walkStartV (slotsT W fold b t) (dig k t) base = .n j ∧ lo ≤ j := by
  unfold walkStartV
  split
  · exact ⟨_, rfl, h2⟩
  · exact ⟨_, rfl, h1⟩

/-- **A group completes**, its digits `k` hinted. -/
theorem groupT_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) {first n : Nat} {fold : Bool} {prodIn encIn : V} {b k : Nat}
    (hn : n ≤ 3) (hk : k < 4 ^ n) (hm : MemOK rd 64) (hB : B ≤ b) (hpi : NBv B prodIn)
    (hei : NBv B encIn) (hpw : ∀ j, NBv B (W.power j)) (σ : Val) (hg : good σ)
    (hb : σ (.n b) = ofK (gpow k))
    (hs : ∀ t < n, StartCanon σ (slotsT W fold b t) (dig k t)
      (walkBase (if k = 0 then W.size + 13 else W.size) k 0 t
        (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k))) :
    Completes C rd b (groupT W first n fold prodIn encIn b).2 (groupT W first n fold prodIn encIn b).1 σ
      (fun σ' => σ' (.n b) = ofK (gpow k) ∧ ∀ t < n, IsCanonical128 (σ' (.n (slotsT W fold b t 2)))) := by
  have h4n : 4 ^ n ≤ 64 := by
    calc 4 ^ n ≤ 4 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 64 := by norm_num
  have hend : (groupT W first n fold prodIn encIn b).2 = armB W first n fold prodIn encIn b (4 ^ n) := by
    simp only [groupT]
    rw [armsT_snd]
    rfl
  have hge : b + 5 ≤ armB W first n fold prodIn encIn b (4 ^ n) := by
    rw [← armB_zero W first n fold prodIn encIn b]
    exact armB_mono W first n fold prodIn encIn b (Nat.zero_le _)
  rw [hend]
  simp only [groupT, List.cons_append]
  show Completes C rd b _ ([hintW "digits" [.n b]] ++
    (rangeS (.n b) (word (2 ^ (4 ^ n - 1)) 0 0) (b + 1) ++ [.match_ (.n b) _])) σ _
  refine Completes.append (m := b + 1) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨b, by omega, rfl⟩ (.nil _)) (hintKeep_complete σ _ _ _ _)
    (fun σ1 he1 hp1 => ?_)
  rw [hp1, word_two_pow_eq (by omega)]
  refine Completes.append (m := b + 5) (by omega) hge ?_
    (rangeS_complete (n := 64) (K := 4 ^ n) hm h4n hk σ (.n b) ⟨b, by omega, rfl⟩ hb)
    (fun σ2 he2 _ => ?_)
  · simp only [rangeS, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
      List.cons_append, List.nil_append]
    repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))
  have hag : AgreeBelow (b + 1) σ σ2 := he2.agree
  have hb2 : σ2 (.n b) = ofK (gpow k) := by rw [← hag b (by omega)]; exact hb
  have hk' : k < (armsT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b)
      (4 ^ n) 0 (b + 5)).1.length := by rw [armsT_length]; exact hk
  refine match_complete hk' ⟨b, by omega, rfl⟩ hb2 ?_
  rw [armsT_getElem]
  simp only [Nat.zero_add]
  obtain ⟨σ', he', hp', hh'⟩ := groupArm_complete (C := C) (rd := rd) (first := first) hW hc hk hB hpi hei
    (hpw _) σ2 (hc.1 _ _ (fun j hj => hag j (by omega)) hg)
    (fun t ht => by
      have := hs t ht
      unfold StartCanon at this ⊢
      have hbase : b + 5 ≤ armB W first n fold prodIn encIn b k := by
        rw [← armB_zero W first n fold prodIn encIn b]
        exact armB_mono W first n fold prodIn encIn b (Nat.zero_le _)
      have hwb := walkBase_le (if k = 0 then W.size + 13 else W.size) k
        (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)
        (Nat.zero_le t)
      simp only [walkBase] at hwb
      have hb0 : armB W first n fold prodIn encIn b k ≤
          (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k) := by
        split <;> omega
      have hsl := slot_bounds W fold b t 2 (by norm_num)
      have hgs : b + 5 ≤ groupStart fold b := by rw [groupStart_eq]; split <;> omega
      obtain ⟨j, e, hj⟩ := start_ge (W := W) (fold := fold) (b := b) (k := k) (t := t) (lo := b + 5)
        (base := walkBase (if k = 0 then W.size + 13 else W.size) k 0 t
          (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k))
        (by omega) (by omega)
      rw [e] at this ⊢
      rw [he2.apply (Or.inr hj)]
      exact this)
  exact ⟨σ', he', ⟨by rw [he'.apply (Or.inl (by omega))]; exact hb2, hp'.2⟩, hh'⟩

end
end LeanVM.Guest.B1.Sig
