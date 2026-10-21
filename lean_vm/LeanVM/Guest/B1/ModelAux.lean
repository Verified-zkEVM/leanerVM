/-
  LeanVM.Guest.B1.ModelAux

  Blocks without `BLAKE2S` under any semantics: their deployed facts carry over, the transfer of
  `Core.relB_iff_rel_of_freeOn` at the level of a block.
-/

module

public import LeanVM.Guest.B1.Basic

/-!
# Blocks free of `BLAKE2S`

`Core.holdsListB_freeIn` says that a block with no `BLAKE2S` atom holds under one semantics
exactly when it holds under another, at call relations agreeing on its callees. At one call
relation it agrees with itself, so such a block's `HoldsListB S C` is its deployed `HoldsList C`
(`holdsListB_iff_of_free`): every deployed lemma about a hash-free block, stated over any call
relation, is one about the block under any semantics. The freeness of a template is checked by
`freeInList_append`, `freeInList_flatten_range` and evaluation of its atoms.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val}

/-- A call relation agrees with itself on any names. -/
theorem CallRel.agreeOn_refl (F : List String) (C : CallRel) : CallRel.AgreeOn F C C :=
  fun _ _ _ _ ↦ Iff.rfl

/-- **A block free of `BLAKE2S`** holds under any semantics exactly when it holds deployed. -/
theorem holdsListB_iff_of_free {F : List String} {ss : List Stmt} (hF : Stmt.freeInList F ss = true)
    (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ ss next kret ↔ Stmt.HoldsList C rd σ ss next kret := by
  rw [holdsListB_freeIn (S' := blakeDeployed) (CallRel.agreeOn_refl F C) ss hF next kret,
    holdsListB_deployed]

/-- **A statement free of `BLAKE2S`** holds under any semantics exactly when it holds deployed. -/
theorem holdsB_iff_of_free {F : List String} {s : Stmt} (hF : Stmt.freeIn F s = true)
    (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsB S C rd σ s next kret ↔ Stmt.Holds C rd σ s next kret := by
  rw [holdsB_freeIn (S' := blakeDeployed) (CallRel.agreeOn_refl F C) s hF next kret,
    holdsB_deployed]

theorem freeInList_append (F : List String) (xs ys : List Stmt) :
    Stmt.freeInList F (xs ++ ys) = (Stmt.freeInList F xs && Stmt.freeInList F ys) := by
  induction xs with
  | nil => simp [Stmt.freeInList]
  | cons x xs ih => simp only [List.cons_append, Stmt.freeInList, ih, Bool.and_assoc]

theorem freeInList_flatten (F : List String) :
    ∀ (bs : List (List Stmt)), (∀ b ∈ bs, Stmt.freeInList F b = true) →
      Stmt.freeInList F bs.flatten = true
  | [], _ => rfl
  | b :: bs, h => by
    rw [List.flatten_cons, freeInList_append, h b List.mem_cons_self,
      freeInList_flatten F bs fun b' hb' ↦ h b' (List.mem_cons_of_mem _ hb')]
    rfl

/-- Blocks free of `BLAKE2S`, one per index below `n`: their concatenation is. -/
theorem freeInList_flatten_range (F : List String) (n : ℕ) (blk : ℕ → List Stmt)
    (h : ∀ i, Stmt.freeInList F (blk i) = true) :
    Stmt.freeInList F ((List.range n).map blk).flatten = true :=
  freeInList_flatten F _ fun b hb ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
    exact h i

/-! ## Loops under any semantics, soundness only -/

/-- `loop_sound` (`Whir/Queries.lean`) under any semantics: a `mul_range` loop from `g^k`, the
step's relation giving its body. -/
theorem loopB_sound {P : Core.Program} {f : String} {ps : List E} {N : E} {B : E → Prop}
    (hstep : ∀ d x, P.relNB S rd (d + 1) f (x :: ps) [] →
      B x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → P.relNB S rd d f (x * gen :: ps) [])) (k : ℕ)
    (h : P.RelB S rd f (gen ^ k :: ps) []) :
    ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧ ∀ j, k ≤ j → j < m → B (gen ^ j) := by
  obtain ⟨d, hd⟩ := h
  induction d generalizing k with
  | zero => exact hd.elim
  | succ d ih =>
    obtain ⟨hB, -, hnext⟩ := hstep d _ hd
    by_cases h0 : gen ^ k * gen + N = 0
    · refine ⟨k + 1, by omega, (gen_pow_add_eq_zero_iff k).mp h0, fun j h1 h2 => by omega,
        fun j h1 h2 => ?_⟩
      rwa [show j = k by omega]
    · have := hnext h0
      rw [gen_pow_mul_gen] at this
      obtain ⟨m, hm, hN, hfirst, hall⟩ := ih (k + 1) this
      refine ⟨m, by omega, hN, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
      · rcases Nat.lt_or_ge (k + 1) j with h | h
        · exact hfirst j h h2
        · rw [show j = k + 1 by omega]
          intro he
          exact h0 ((gen_pow_add_eq_zero_iff k).mpr he.symm)
      · rcases Nat.lt_or_ge k j with h | h
        · exact hall j (by omega) h2
        · rwa [show j = k by omega]

/-- `guarded_loop_sound` under any semantics: `N = g^m` below the order of `g`, the body at every
`g^j`, `j < m`. -/
theorem guarded_loopB_sound {P : Core.Program} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hstep : ∀ d x, P.relNB S rd (d + 1) f (x :: ps) [] →
      B x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → P.relNB S rd d f (x * gen :: ps) []))
    (hrun : 1 + N ≠ 0 → P.RelB S rd f (1 :: ps) []) :
    ∃ m < ordG, N = gen ^ m ∧ ∀ j < m, B (gen ^ j) := by
  by_cases h1 : 1 + N = 0
  · exact ⟨0, by decide, by rw [pow_zero]; exact (e_add_eq_zero_iff.mp h1).symm,
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  · have hr := hrun h1
    rw [← pow_zero gen] at hr
    obtain ⟨m, hm, hN, hfirst, hall⟩ := loopB_sound hstep 0 hr
    refine ⟨m, ?_, hN, fun j hj => hall j (Nat.zero_le j) hj⟩
    by_contra hge
    rcases Nat.lt_or_ge ordG m with hgt | hle
    · have : gen ^ (m - ordG) = N := by
        obtain ⟨t, rfl⟩ : ∃ t, m = ordG + t := ⟨m - ordG, by omega⟩
        rw [hN, pow_add, gen_pow_ordG, one_mul, Nat.add_sub_cancel_left]
      exact hfirst (m - ordG) (Nat.sub_pos_of_lt hgt) (Nat.sub_lt (by omega) ordG_pos) this
    · have hm' : m = ordG := by omega
      rw [hm', gen_pow_ordG] at hN
      exact h1 (by rw [hN]; exact e_add_self 1)

/-! ## Blocks without a `BLAKE2S` atom, at one call relation

At one call relation the callees do not matter: a block with no `BLAKE2S` atom anywhere
(`Stmt.noBlakeList`, its calls unrestricted) holds under any semantics exactly when it holds
deployed (`holdsListB_iff_of_noBlake`). -/

mutual
/-- A statement with no `BLAKE2S` atom, its calls unrestricted. -/
def Stmt.noBlake : Stmt → Bool
  | .atom (.blake2s ..) => false
  | .atom _ => true
  | .ite _ z n => Stmt.noBlakeList z && Stmt.noBlakeList n
  | .match_ _ arms => Stmt.noBlakeArms arms
  | .call .. => true
  | .callIf .. => true
  | .dispatch .. => true
  | .ret _ => true

/-- A block with no `BLAKE2S` atom. -/
def Stmt.noBlakeList : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.noBlake s && Stmt.noBlakeList ss

/-- Arms with no `BLAKE2S` atom. -/
def Stmt.noBlakeArms : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.noBlakeList a && Stmt.noBlakeArms as
end

mutual
theorem holdsB_noBlake {S' : BlakeSem} :
    ∀ (s : Stmt), Stmt.noBlake s = true → ∀ (next : Prop) (kret : List E → Prop),
      (Stmt.HoldsB S C rd σ s next kret ↔ Stmt.HoldsB S' C rd σ s next kret)
  | .atom a, h, _, _ => by
      cases a <;> first | exact Iff.rfl | simp [Stmt.noBlake] at h
  | .ite c z n, h, next, kret => by
      simp only [Stmt.noBlake, Bool.and_eq_true] at h
      simp only [Stmt.HoldsB, holdsListB_noBlake (S' := S') z h.1, holdsListB_noBlake (S' := S') n h.2]
  | .match_ x arms, h, next, kret => by
      simp only [Stmt.noBlake] at h
      exact holdsArmsB_noBlake x arms h 0 next kret
  | .call _ _ _, _, _, _ => Iff.rfl
  | .callIf _ _ _, _, _, _ => Iff.rfl
  | .dispatch _ _ _ _, _, _, _ => Iff.rfl
  | .ret _, _, _, _ => Iff.rfl

theorem holdsListB_noBlake {S' : BlakeSem} :
    ∀ (ss : List Stmt), Stmt.noBlakeList ss = true → ∀ (next : Prop) (kret : List E → Prop),
      (Stmt.HoldsListB S C rd σ ss next kret ↔ Stmt.HoldsListB S' C rd σ ss next kret)
  | [], _, _, _ => Iff.rfl
  | s :: ss, h, next, kret => by
      simp only [Stmt.noBlakeList, Bool.and_eq_true] at h
      simp only [Stmt.HoldsListB]
      rw [holdsB_noBlake s h.1, holdsListB_noBlake ss h.2]

theorem holdsArmsB_noBlake {S' : BlakeSem} (x : V) :
    ∀ (arms : List (List Stmt)), Stmt.noBlakeArms arms = true →
      ∀ (j : Nat) (next : Prop) (kret : List E → Prop),
      (Stmt.HoldsArmsB S C rd σ x j arms next kret ↔ Stmt.HoldsArmsB S' C rd σ x j arms next kret)
  | [], _, _, _, _ => Iff.rfl
  | a :: as, h, j, next, kret => by
      simp only [Stmt.noBlakeArms, Bool.and_eq_true] at h
      simp only [Stmt.HoldsArmsB]
      rw [holdsListB_noBlake a h.1, holdsArmsB_noBlake x as h.2 (j + 1)]
end

/-- **A block with no `BLAKE2S` atom** holds under any semantics exactly when it holds deployed,
at any one call relation. -/
theorem holdsListB_iff_of_noBlake {ss : List Stmt} (h : Stmt.noBlakeList ss = true)
    (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ ss next kret ↔ Stmt.HoldsList C rd σ ss next kret := by
  rw [holdsListB_noBlake (S' := blakeDeployed) ss h next kret, holdsListB_deployed]

theorem noBlakeList_append (xs ys : List Stmt) :
    Stmt.noBlakeList (xs ++ ys) = (Stmt.noBlakeList xs && Stmt.noBlakeList ys) := by
  induction xs with
  | nil => simp [Stmt.noBlakeList]
  | cons x xs ih => simp only [List.cons_append, Stmt.noBlakeList, ih, Bool.and_assoc]

theorem noBlakeList_flatten :
    ∀ (bs : List (List Stmt)), (∀ b ∈ bs, Stmt.noBlakeList b = true) →
      Stmt.noBlakeList bs.flatten = true
  | [], _ => rfl
  | b :: bs, h => by
    rw [List.flatten_cons, noBlakeList_append, h b List.mem_cons_self,
      noBlakeList_flatten bs fun b' hb' ↦ h b' (List.mem_cons_of_mem _ hb')]
    rfl

theorem noBlakeList_flatten_range (n : ℕ) (blk : ℕ → List Stmt)
    (h : ∀ i, Stmt.noBlakeList (blk i) = true) :
    Stmt.noBlakeList ((List.range n).map blk).flatten = true :=
  noBlakeList_flatten _ fun b hb ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
    exact h i

/-- A function whose body has no `BLAKE2S` atom and calls only itself is free of `BLAKE2S`. -/
theorem freeOn_self {P : Core.Program} {f : String} {fn : Fn} (hfind : P.find? f = some fn)
    (h : Stmt.freeInList [f] fn.body = true) : P.FreeOn [f] = true := by
  simp [Program.FreeOn, hfind, h]

/-- A block without a return under any semantics: its facts and its continuation. -/
theorem holdsListB_true_of {ss : List Stmt} {next : Prop} {kret : List E → Prop}
    (hs : Stmt.noRetList ss = true) (h : Stmt.HoldsListB S C rd σ ss next kret) :
    Stmt.HoldsListB S C rd σ ss True kret ∧ next :=
  (holdsListB_noRet ss hs next kret).mp h

/-- A block without a return and without `BLAKE2S` under any semantics: its deployed facts and
its continuation. -/
theorem holdsListB_split_free {ss : List Stmt} {next : Prop} {kret : List E → Prop}
    (hb : Stmt.noBlakeList ss = true) (hs : Stmt.noRetList ss = true)
    (h : Stmt.HoldsListB S C rd σ ss next kret) : Stmt.HoldsList C rd σ ss True kret ∧ next := by
  obtain ⟨h1, h2⟩ := holdsListB_true_of hs h
  exact ⟨(holdsListB_iff_of_noBlake hb _ _).mp h1, h2⟩

end
end LeanVM.Guest.B1
