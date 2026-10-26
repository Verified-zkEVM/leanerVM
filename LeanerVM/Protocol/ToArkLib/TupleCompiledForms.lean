/-
  LeanerVM.Protocol.ToArkLib.TupleCompiledForms

  Below this header, a verbatim copy of the section "Compiled forms of the snocs and appends" of
  ArkLib's `ArkLib/Data/Fin/Tuple/Lemmas.lean` at `f1a1e7deb` (branch
  `perf/fin-append-compiled-forms` of `scaraven/ArkLib`, proposed to ArkLib), which the pin does
  not contain. Deleted when the pin contains it, with `ToArkLib/AppendLazy.lean`; their importers
  then import `ArkLib.Data.Fin.Tuple.Lemmas`, and the aggregate drops both.

  ArkLib's licence notice:

  Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ArkLib.Data.Fin.Tuple.Lemmas

/-!
# Compiled forms of `Fin` tuple snocs and appends

ArkLib's `Fin.vconcat`, `Fin.fconcat`, `Fin.fconcat₂`, `Fin.hconcat`, `Fin.fappend`, `Fin.fappend₂`
and `Fin.happend`, read by one comparison and substituted for the recursive definitions in
compiled code by `@[csimp]`.
-/

@[expose] public section

universe u v w

namespace Fin

/-! ### Compiled forms of the snocs and appends

`vconcat` is `dconcat` at a constant motive, but its compiled code predates `dconcat_eq_snoc`
and runs `dconcat`'s recursion through `dcons`. `fconcat` and `fconcat₂` recurse on the length of
their tuple through `fcons` and `fcons₂`, and `fappend`, `fappend₂` and `happend` recurse on the
length of their second argument through `fconcat` and `fconcat₂`. The recursion gives them their
definitional equalities, but compiled code evaluates the arguments of each step eagerly, so
reading one entry can evaluate entries of the arguments many times: for a tuple built by `k`
nested snocs, or by appending a tuple of length `k`, the work grows exponentially with `k`. The
forms below read entry `i` by one comparison: with the last index, as `snoc` does, or with the
seam, as `addCases` does. They are equal to the recursive definitions, and the `@[csimp]`
theorems make compiled code run them in their place. -/

/-- `vconcat v a`, read by one comparison with the last index: `snoc v a`. -/
def vconcatSnoc {α : Sort u} {n : ℕ} (v : Fin n → α) (a : α) : Fin (n + 1) → α :=
  snoc v a

/-- `vconcat` is `vconcatSnoc`, which compiled code runs in its place. -/
@[csimp]
theorem vconcat_eq_vconcatSnoc : @vconcat = @vconcatSnoc := by
  funext α n v a
  exact vconcat_eq_snoc v a

/-- `fconcat u a`, read by one comparison with the last index: entry `castSucc i` is `u i` and
entry `last n` is `a`, transported along `vconcat_castSucc` and `vconcat_last`. -/
def fconcatSnoc {A : Sort u} {F : A → Sort v} {n : ℕ} {α : Fin n → A} {β : A}
    (u : (i : Fin n) → F (α i)) (a : F β) : (i : Fin (n + 1)) → F (vconcat α β i) :=
  snoc (α := fun i => F (vconcat α β i))
    (fun i => cast (congrArg F (vconcat_castSucc α β i)).symm (u i))
    (cast (congrArg F (vconcat_last α β)).symm a)

/-- `fconcat` is `fconcatSnoc`, which compiled code runs in its place. -/
@[csimp]
theorem fconcat_eq_fconcatSnoc : @fconcat = @fconcatSnoc := by
  funext A F n α β u a i
  induction i using lastCases <;> simp [fconcatSnoc]

/-- `fconcat₂ u a`, read by one comparison with the last index: entry `castSucc i` is `u i` and
entry `last n` is `a`, transported along `vconcat_castSucc` and `vconcat_last`. -/
def fconcat₂Snoc {A : Sort u} {B : Sort v} {F : A → B → Sort w} {n : ℕ}
    {α₁ : Fin n → A} {β₁ : A} {α₂ : Fin n → B} {β₂ : B}
    (u : (i : Fin n) → F (α₁ i) (α₂ i)) (a : F β₁ β₂) :
    (i : Fin (n + 1)) → F (vconcat α₁ β₁ i) (vconcat α₂ β₂ i) :=
  snoc (α := fun i => F (vconcat α₁ β₁ i) (vconcat α₂ β₂ i))
    (fun i => cast (congrArg₂ F (vconcat_castSucc α₁ β₁ i) (vconcat_castSucc α₂ β₂ i)).symm (u i))
    (cast (congrArg₂ F (vconcat_last α₁ β₁) (vconcat_last α₂ β₂)).symm a)

/-- `fconcat₂` is `fconcat₂Snoc`, which compiled code runs in its place. -/
@[csimp]
theorem fconcat₂_eq_fconcat₂Snoc : @fconcat₂ = @fconcat₂Snoc := by
  funext A B F n α₁ β₁ α₂ β₂ u a i
  induction i using lastCases <;> simp [fconcat₂Snoc]

/-- `hconcat u a`, read by one comparison with the last index: `fconcatSnoc` at the identity, as
`hconcat` is `fconcat`. -/
def hconcatSnoc {n : ℕ} {α : Fin n → Sort u} {β : Sort u} (u : (i : Fin n) → α i) (a : β) :
    (i : Fin (n + 1)) → vconcat α β i :=
  fconcatSnoc (F := id) u a

/-- `hconcat` is `hconcatSnoc`, which compiled code runs in its place. -/
@[csimp]
theorem hconcat_eq_hconcatSnoc : @hconcat = @hconcatSnoc := by
  unfold hconcat hconcatSnoc
  rw [fconcat_eq_fconcatSnoc]

/-- `fappend u v`, read by one comparison with the seam: entry `castAdd n i` is `u i` and entry
`natAdd m i` is `v i`, transported along `vappend_left` and `vappend_right`. -/
def fappendAddCases {A : Sort u} {F : A → Sort v} {m n : ℕ} {α : Fin m → A} {β : Fin n → A}
    (u : (i : Fin m) → F (α i)) (v : (i : Fin n) → F (β i)) :
    (i : Fin (m + n)) → F (vappend α β i) :=
  addCases (motive := fun i => F (vappend α β i))
    (fun i => cast (congrArg F (vappend_left α β i)).symm (u i))
    (fun i => cast (congrArg F (vappend_right α β i)).symm (v i))

/-- `fappend` is `fappendAddCases`, which compiled code runs in its place. -/
@[csimp]
theorem fappend_eq_fappendAddCases : @fappend = @fappendAddCases := by
  funext A F m n α β u v i
  induction i using addCases <;> simp [fappendAddCases]

/-- `fappend₂ u v`, read by one comparison with the seam: entry `castAdd n i` is `u i` and entry
`natAdd m i` is `v i`, transported along `vappend_left` and `vappend_right`. -/
def fappend₂AddCases {A : Sort u} {B : Sort v} {F : A → B → Sort w} {m n : ℕ}
    {α₁ : Fin m → A} {β₁ : Fin n → A} {α₂ : Fin m → B} {β₂ : Fin n → B}
    (u : (i : Fin m) → F (α₁ i) (α₂ i)) (v : (i : Fin n) → F (β₁ i) (β₂ i)) :
    (i : Fin (m + n)) → F (vappend α₁ β₁ i) (vappend α₂ β₂ i) :=
  addCases (motive := fun i => F (vappend α₁ β₁ i) (vappend α₂ β₂ i))
    (fun i => cast (congrArg₂ F (vappend_left α₁ β₁ i) (vappend_left α₂ β₂ i)).symm (u i))
    (fun i => cast (congrArg₂ F (vappend_right α₁ β₁ i) (vappend_right α₂ β₂ i)).symm (v i))

/-- `fappend₂` is `fappend₂AddCases`, which compiled code runs in its place. -/
@[csimp]
theorem fappend₂_eq_fappend₂AddCases : @fappend₂ = @fappend₂AddCases := by
  funext A B F m n α₁ β₁ α₂ β₂ u v i
  induction i using addCases <;> simp [fappend₂AddCases]

/-- `happend u v`, read by one comparison with the seam: `fappendAddCases` at the identity, as
`happend` is `fappend`. -/
def happendAddCases {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) : (i : Fin (m + n)) → vappend α β i :=
  fappendAddCases (F := id) u v

/-- `happend` is `happendAddCases`, which compiled code runs in its place. -/
@[csimp]
theorem happend_eq_happendAddCases : @happend = @happendAddCases := by
  unfold happend happendAddCases
  rw [fappend_eq_fappendAddCases]

end Fin
