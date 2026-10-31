/-
  LeanVM.Guest.B1.Tables.VtC.Glue

  `verify_tables`' relation from its statements one by one: each atom, call and dispatch, and
  each `ite` by its taken branch.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Flat

/-!
# From statements to the relation

`VSH C rd σ s`: the statement holds, its continuation aside; an `ite` by its taken branch, every
statement of which is straight (`iteOk`, checked of `vtPre` by the kernel). `vt_rel_of`: when every
statement of `vtPre` does, the parameters are the arguments and `vtRets` the returns, the relation
holds.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- A straight statement: an atom, a call, a conditional call or a dispatch. -/
def straightB : Stmt → Bool
  | .atom _ | .call .. | .callIf .. | .dispatch .. => true
  | _ => false

/-- A straight statement, or an `ite` of straight branches. -/
def iteOk : Stmt → Bool
  | .ite _ z n => z.all straightB && n.all straightB
  | s => straightB s

/-- A statement holds, its continuation aside; an `ite` by its taken branch. -/
def VSH (C : CallRel) (rd : Reader) (σ : Val) : Stmt → Prop
  | .ite c z n => IsInK (σ c) ∧ (σ c = 0 → ∀ s ∈ z, SHolds C rd σ s) ∧
      (σ c ≠ 0 → ∀ s ∈ n, SHolds C rd σ s)
  | s => SHolds C rd σ s

theorem holdsList_straightN {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    ∀ (ss : List Stmt) {next : Prop}, ss.all straightB = true → (∀ s ∈ ss, SHolds C rd σ s) →
      next → Stmt.HoldsList C rd σ ss next kret
  | [], _, _, _, hn => hn
  | s :: ss, next, hst, hs, hn => by
    simp only [List.all_cons, Bool.and_eq_true] at hst
    have ih := holdsList_straightN (kret := kret) ss (next := next) hst.2
      (fun t ht => hs t (List.mem_cons_of_mem _ ht)) hn
    have h0 := hs s List.mem_cons_self
    simp only [Stmt.HoldsList]
    cases s with
    | atom a => exact ⟨h0, ih⟩
    | call f args rets => exact ⟨h0, ih⟩
    | callIf c f args => exact ⟨h0.1, h0.2, ih⟩
    | dispatch x fs args rets => exact ⟨h0, ih⟩
    | _ => simp [straightB] at hst

/-- **A block of straight statements and `ite`s of straight branches holds** when each does. -/
theorem holdsList_of_vsh {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    ∀ (ss : List Stmt) {next : Prop}, ss.all iteOk = true → (∀ s ∈ ss, VSH C rd σ s) →
      next → Stmt.HoldsList C rd σ ss next kret
  | [], _, _, _, hn => hn
  | s :: ss, next, hok, hs, hn => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have ih := holdsList_of_vsh (kret := kret) ss (next := next) hok.2
      (fun t ht => hs t (List.mem_cons_of_mem _ ht)) hn
    have h0 := hs s List.mem_cons_self
    simp only [Stmt.HoldsList]
    cases s with
    | atom a => exact ⟨h0, ih⟩
    | call f args rets => exact ⟨h0, ih⟩
    | callIf c f args => exact ⟨h0.1, h0.2, ih⟩
    | dispatch x fs args rets => exact ⟨h0, ih⟩
    | ite c z n =>
      simp only [iteOk, Bool.and_eq_true] at hok
      obtain ⟨hk, hz, hn'⟩ := h0
      exact ⟨hk, fun h => holdsList_straightN z hok.1.1 (hz h) ih,
        fun h => holdsList_straightN n hok.1.2 (hn' h) ih⟩
    | _ => simp [iteOk, straightB] at hok

theorem vt_iteOk : vtPre.all iteOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables
