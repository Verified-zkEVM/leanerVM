/-
  LeanVM.Guest.Budget.Kids

  A node's callees' weights and words, bounded call by call: an entered call by its callee's
  bound on its valid trees at the call's arguments, a call not entered by its phantom.
-/

module

public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.B1.Main.KidsT

/-!
# The callees' weights and words

`kids_weight_le`, `kids_total_le`: for the callees `ks` of the calls `cs` (`Tree.KidsValid`), the
weight is at most the sum over the entered calls of a bound `W c` on their callees' valid trees at
the call's arguments, and the words at most the sum of a bound `T c` over the entered calls and of
the callee's frame over the others (a phantom allocates its frame).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The bounds of the entered calls. -/
def callsW (W : Call → ℕ) (cs : List Call) : ℕ := (cs.map fun c => if c.taken then W c else 0).sum

/-- The words of the calls: a bound for an entered call, the callee's frame for the others. -/
def callsT (fs : String → ℕ) (T : Call → ℕ) (cs : List Call) : ℕ :=
  (cs.map fun c => if c.taken then T c else fs c.f).sum

variable {P : Core.Program} {rd : Reader} {σ : Val}

theorem kids_weight_le (ω : String → ℕ) (W : Call → ℕ) :
    ∀ (cs : List Call) (ks : List Tree), Tree.KidsValid P rd σ cs ks → Tree.BufsOkKids P ks →
      (∀ c ∈ cs, c.taken = true → ∀ (t : Tree) (rets : List E), t.name = c.f →
        t.Valid P rd (c.args.map σ) rets → t.BufsOk P → t.weight ω ≤ W c) →
      Tree.weightKids ω ks ≤ callsW W cs
  | [], [], _, _, _ => by simp [Tree.weightKids, callsW]
  | [], _ :: _, hk, _, _ => hk.elim
  | _ :: _, [], hk, _, _ => hk.elim
  | c :: cs, k :: ks, ⟨hn, hk, hks⟩, ⟨hb, hbs⟩, hB => by
    have ih := kids_weight_le ω W cs ks hks hbs fun c' hc' => hB c' (List.mem_cons_of_mem _ hc')
    rw [Tree.weightKids]
    unfold callsW at ih ⊢
    rw [List.map_cons, List.sum_cons]
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at hk ⊢
      exact Nat.add_le_add (hB c (List.mem_cons_self ..) ht k _ hn hk hb) ih
    · simp only [Bool.not_eq_true] at ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk ⊢
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
      rw [Tree.weight]
      omega

theorem kids_total_le (fs : String → ℕ) (T : Call → ℕ) :
    ∀ (cs : List Call) (ks : List Tree), Tree.KidsValid P rd σ cs ks → Tree.BufsOkKids P ks →
      (∀ c ∈ cs, c.taken = true → ∀ (t : Tree) (rets : List E), t.name = c.f →
        t.Valid P rd (c.args.map σ) rets → t.BufsOk P → t.total fs ≤ T c) →
      Tree.totalKids fs ks ≤ callsT fs T cs
  | [], [], _, _, _ => by simp [Tree.totalKids, callsT]
  | [], _ :: _, hk, _, _ => hk.elim
  | _ :: _, [], hk, _, _ => hk.elim
  | c :: cs, k :: ks, ⟨hn, hk, hks⟩, ⟨hb, hbs⟩, hB => by
    have ih := kids_total_le fs T cs ks hks hbs fun c' hc' => hB c' (List.mem_cons_of_mem _ hc')
    rw [Tree.totalKids]
    unfold callsT at ih ⊢
    rw [List.map_cons, List.sum_cons]
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at hk ⊢
      exact Nat.add_le_add (hB c (List.mem_cons_self ..) ht k _ hn hk hb) ih
    · simp only [Bool.not_eq_true] at ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk ⊢
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
      simp only [Tree.name] at hn
      subst hn
      rw [Tree.total]
      omega

/-! ## With the callees' predicates

The same, a call's bound holding of its callee's valid trees that satisfy the call's predicate
(`KidsT`: an entered call's callee satisfies its predicate). -/

theorem kids_weight_leT (ω : String → ℕ) (W : Call → ℕ) :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (ks : List Tree), Tree.KidsValid P rd σ cs ks →
      Tree.BufsOkKids P ks → cs.length ≤ Ts.length → KidsT cs Ts ks →
      (∀ c T, (c, T) ∈ cs.zip Ts → c.taken = true → ∀ (t : Tree) (rets : List E), t.name = c.f →
        t.Valid P rd (c.args.map σ) rets → t.BufsOk P → T t → t.weight ω ≤ W c) →
      Tree.weightKids ω ks ≤ callsW W cs
  | [], _, [], _, _, _, _, _ => by simp [Tree.weightKids, callsW]
  | [], _, _ :: _, hk, _, _, _, _ => hk.elim
  | _ :: _, _, [], hk, _, _, _, _ => hk.elim
  | _ :: _, [], _ :: _, _, _, hl, _, _ => by simp at hl
  | c :: cs, T :: Ts, k :: ks, ⟨hn, hk, hks⟩, ⟨hb, hbs⟩, hl, ⟨hT, hTs⟩, hB => by
    have ih := kids_weight_leT ω W cs Ts ks hks hbs (by simpa using hl) hTs
      fun c' T' hc' => hB c' T' (by simp [hc'])
    rw [Tree.weightKids]
    unfold callsW at ih ⊢
    rw [List.map_cons, List.sum_cons]
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at hk ⊢
      exact Nat.add_le_add (hB c T (by simp) ht k _ hn hk hb (hT ht)) ih
    · simp only [Bool.not_eq_true] at ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk ⊢
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
      rw [Tree.weight]
      omega

theorem kids_total_leT (fs : String → ℕ) (T : Call → ℕ) :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (ks : List Tree), Tree.KidsValid P rd σ cs ks →
      Tree.BufsOkKids P ks → cs.length ≤ Ts.length → KidsT cs Ts ks →
      (∀ c Q, (c, Q) ∈ cs.zip Ts → c.taken = true → ∀ (t : Tree) (rets : List E), t.name = c.f →
        t.Valid P rd (c.args.map σ) rets → t.BufsOk P → Q t → t.total fs ≤ T c) →
      Tree.totalKids fs ks ≤ callsT fs T cs
  | [], _, [], _, _, _, _, _ => by simp [Tree.totalKids, callsT]
  | [], _, _ :: _, hk, _, _, _, _ => hk.elim
  | _ :: _, _, [], hk, _, _, _, _ => hk.elim
  | _ :: _, [], _ :: _, _, _, hl, _, _ => by simp at hl
  | c :: cs, Q :: Ts, k :: ks, ⟨hn, hk, hks⟩, ⟨hb, hbs⟩, hl, ⟨hT, hTs⟩, hB => by
    have ih := kids_total_leT fs T cs Ts ks hks hbs (by simpa using hl) hTs
      fun c' T' hc' => hB c' T' (by simp [hc'])
    rw [Tree.totalKids]
    unfold callsT at ih ⊢
    rw [List.map_cons, List.sum_cons]
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at hk ⊢
      exact Nat.add_le_add (hB c Q (by simp) ht k _ hn hk hb (hT ht)) ih
    · simp only [Bool.not_eq_true] at ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk ⊢
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
      simp only [Tree.name] at hn
      subst hn
      rw [Tree.total]
      omega

end
end LeanVM.Guest.Budget
