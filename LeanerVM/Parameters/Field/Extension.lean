/-
  LeanerVM.Parameters.Field.Extension

  The leanVM extension field `E = K[y]/(y^3 + y + 1)`, the 192-bit machine word.
-/

module

public import LeanerVM.Parameters.Field.Carrier
public import CompPoly.Fields.Extension
public import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The leanVM extension field `E`

The leanVM specification fixes

```text
E = K[y]/(y^3 + y + 1),   |E| = 2^192
```

(`doc/leanvm/body/02-vm-specification.tex`, lines 5-12). An element is
`c0 + c1 * y + c2 * y^2` with each coefficient in `K`, which is the pinned Rust's
`F192 { c0, c1, c2 }` (`crates/primitives/src/field/gf2_64x3.rs`). Memory words are
`E`-valued; addresses, the program counter, the frame pointer, and counters stay in `K`.

The carrier comes from CompPoly's computable extension framework, so `Ext extensionParams`
is definitionally `Vector Base 3` — the three-limb layout, with no translation needed.

Source revision: leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`.

## Main definitions and statements

* `extensionPoly` — the modulus `y^3 + y + 1` over `K`, and `extensionPoly_irreducible`.
* `Extension` — the field `E`, with `card_extension : Fintype.card Extension = 2 ^ 192`.
-/

namespace LeanerVM.Parameters.Field

open Polynomial CompPoly.Extension

public section

set_option maxRecDepth 4000

/-! ## The defining cubic -/

/-- The leanVM extension modulus `y^3 + y + 1` over `K`. -/
@[expose] noncomputable def extensionPoly : Polynomial Base := X ^ 3 + X + 1

theorem extensionPoly_natDegree : extensionPoly.natDegree = 3 := by
  rw [extensionPoly]; compute_degree!

theorem extensionPoly_degree : extensionPoly.degree = (3 : ℕ) := by
  rw [extensionPoly]; compute_degree!

theorem extensionPoly_monic : extensionPoly.Monic := by
  rw [extensionPoly]; monicity!

/-! ## Irreducibility

A cubic is irreducible exactly when it has no root. A root `a` of `y^3 + y + 1` satisfies
`a^3 = a + 1`, from which `a^7 = 1`. The multiplicative group of `K` has order `2^64 - 1`,
which is coprime to `7`, so `a = 1` — and `1` is not a root.
-/

/-- A root of the cubic would have multiplicative order dividing `7`. -/
private theorem pow_seven_of_isRoot {a : Base} (h : extensionPoly.IsRoot a) : a ^ 7 = 1 := by
  have h3 : a ^ 3 = a + 1 := by
    have := h
    rw [extensionPoly, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at this
    rw [← sub_eq_zero, CharTwo.sub_eq_add,
      show a ^ 3 + (a + 1) = a ^ 3 + a + 1 from by ring]
    exact this
  calc a ^ 7 = (a ^ 3) ^ 2 * a := by ring
    _ = (a + 1) ^ 2 * a := by rw [h3]
    _ = (a ^ 2 + 1) * a := by rw [CharTwo.add_sq, one_pow]
    _ = a ^ 3 + a := by ring
    _ = (a + 1) + a := by rw [h3]
    _ = 1 := by rw [add_comm a 1, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The cubic has no root in `K`.

A root has `a ^ 7 = 1`, so its multiplicative order divides `7`. It also divides
`Fintype.card Base - 1 = 2 ^ 64 - 1`, which is coprime to `7`, so the order is `1` and
`a = 1`. But `1` is not a root.
-/
theorem extensionPoly_no_root (a : Base) : ¬extensionPoly.IsRoot a := by
  intro h
  have h7 := pow_seven_of_isRoot h
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at h7
    exact zero_ne_one h7
  -- the order divides 7 and divides the group order
  have hdvd7 : orderOf a ∣ 7 := orderOf_dvd_of_pow_eq_one h7
  have hdvdcard : orderOf a ∣ 2 ^ 64 - 1 := by
    have hc : a ^ (Fintype.card Base - 1) = 1 := FiniteField.pow_card_sub_one_eq_one a ha
    rw [Base.card_base] at hc
    exact orderOf_dvd_of_pow_eq_one hc
  have hcop : Nat.Coprime 7 (2 ^ 64 - 1) := by decide +kernel
  have h1 : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd7 hdvdcard
  have : a = 1 := orderOf_eq_one_iff.mp h1
  -- but 1 is not a root
  rw [this] at h
  rw [extensionPoly, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, one_pow] at h
  rw [show (1 : Base) + 1 + 1 = 1 from by
    rw [CharTwo.add_self_eq_zero, zero_add]] at h
  exact one_ne_zero h

/-- The cubic `y^3 + y + 1` is irreducible over `K`. -/
theorem extensionPoly_irreducible : Irreducible extensionPoly :=
  Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [extensionPoly_natDegree]; decide) extensionPoly_no_root

instance : Fact (Irreducible extensionPoly) := ⟨extensionPoly_irreducible⟩

end
end LeanerVM.Parameters.Field
