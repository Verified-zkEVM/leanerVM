/-
  LeanVM.Guest.B1.Whir.Flat

  A flat body (atoms, calls, conditional calls, then one `ret`) holds exactly when each of its
  statements does: the facts of `open_stacked`'s template, block by block.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Flat bodies

`open_stacked`'s body (`osBody`) and its loops have no branch, `match` or dispatch: every
statement is an atom, a call or a conditional call, and the last is the `ret`. So the body holds
of a valuation exactly when every statement's relation does (`StmtOk`) and the `ret`'s words are
the returns (`holdsList_flat_ret`). `AllOk σ ss` is that conjunction over a block; it splits over
`++` (`allOk_append`), so each block of the template is read on its own.

* `gw_eq`: the template's g-power words are `gen ^ e`;
* `osMat_val`: a materialized pointer is the base times `gen ^ off`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Flat statements -/

/-- A flat statement: an atom, a call or a conditional call. -/
def Stmt.flat : Stmt → Bool
  | .atom _ | .call .. | .callIf .. => true
  | _ => false

/-- A flat statement's relation. -/
def StmtOk (C : CallRel) (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .call f args rets => C f (args.map σ) (rets.map σ)
  | .callIf c f args => IsInK (σ c) ∧ (σ c ≠ 0 → C f (args.map σ) [])
  | _ => True

/-- Every statement of a block holds. -/
def AllOk (C : CallRel) (rd : Reader) (σ : Val) (ss : List Stmt) : Prop := ∀ s ∈ ss, StmtOk C rd σ s

theorem allOk_append {ss ts : List Stmt} :
    AllOk C rd σ (ss ++ ts) ↔ AllOk C rd σ ss ∧ AllOk C rd σ ts := by
  simp only [AllOk, List.mem_append]
  exact ⟨fun h ↦ ⟨fun s hs ↦ h s (Or.inl hs), fun s hs ↦ h s (Or.inr hs)⟩,
    fun h s hs ↦ hs.elim (h.1 s) (h.2 s)⟩

theorem allOk_cons {s : Stmt} {ss : List Stmt} :
    AllOk C rd σ (s :: ss) ↔ StmtOk C rd σ s ∧ AllOk C rd σ ss := by
  simp [AllOk]

theorem allOk_nil : AllOk C rd σ [] := fun _ h ↦ absurd h (by simp)

theorem allOk_flatten {bs : List (List Stmt)} :
    AllOk C rd σ bs.flatten ↔ ∀ b ∈ bs, AllOk C rd σ b := by
  simp only [AllOk, List.mem_flatten]
  exact ⟨fun h b hb s hs ↦ h s ⟨b, hb, hs⟩, fun h s ⟨b, hb, hs⟩ ↦ h b hb s hs⟩

/-- A flat block holds, then `next`, exactly when every statement does and `next`. -/
theorem holdsList_flat : ∀ (ss : List Stmt), ss.all Stmt.flat = true → ∀ (next : Prop)
    (kret : List E → Prop), Stmt.HoldsList C rd σ ss next kret ↔ AllOk C rd σ ss ∧ next
  | [], _, next, kret => by simp [Stmt.HoldsList, allOk_nil]
  | s :: ss, h, next, kret => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := holdsList_flat ss h.2 next kret
    rw [allOk_cons]
    match s, h.1 with
    | .atom a, _ => simp only [Stmt.HoldsList, Stmt.Holds, StmtOk, ih, and_assoc]
    | .call f args rets, _ => simp only [Stmt.HoldsList, Stmt.Holds, StmtOk, ih, and_assoc]
    | .callIf c f args, _ => simp only [Stmt.HoldsList, Stmt.Holds, StmtOk, ih, and_assoc]

/-- **A flat body ending in a `ret`** holds exactly when every statement before it does and the
returns are its words. -/
theorem holdsList_flat_ret (ss : List Stmt) (h : ss.all Stmt.flat = true) (vs : List V)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (ss ++ [.ret vs]) False kret ↔ AllOk C rd σ ss ∧ kret (vs.map σ) := by
  rw [holdsList_append, holdsList_flat ss h]
  simp [Stmt.HoldsList, Stmt.Holds]

/-! ## Words -/

/-- The template's g-power words. -/
theorem gw_eq {e : ℕ} (h : e < u128Bound) : gw e = gen ^ e := by
  rw [gw, gpowK_eq h, gen_pow_eq_ofK, ofK_eq_ofLimbs]

/-- A materialized pointer is the base times `gen ^ off`. -/
theorem osMat_val {base off k : ℕ} (h : off < u128Bound)
    (hok : AllOk C rd σ (osMat base off k).1) :
    σ (.n (osMat base off k).2.1) = σ (.n base) * gen ^ off := by
  by_cases h0 : off = 0
  · subst h0; simp [osMat]
  · simp only [osMat, h0, ↓reduceIte, allOk_cons, StmtOk, Atom.Holds] at hok ⊢
    rw [hok.2.1, hok.1, gw_eq h]

theorem osMat_next (base off k : ℕ) : k ≤ (osMat base off k).2.2 := by
  unfold osMat; split_ifs <;> simp

end
end LeanVM.Guest.B1.Whir
