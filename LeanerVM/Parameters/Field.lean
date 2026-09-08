/-
  LeanerVM.Parameters.Field

  The leanVM fields `K = GF(2^64)` and `E = GF(2^192)` as CompPoly's computable carriers, and
  the limb view of `E`.
-/

module

public import CompPoly.Fields.Binary.BF64

/-!
# The fields `K` and `E`

leanISA roadmap Layer 0 (`docs/roadmap/leanisa-blueprint.md`). Category B: the moduli and the
limb order are transcribed from specification §2, `doc/leanvm/body/02-vm-specification.tex:6-8`
at leanVM pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`, and are exactly CompPoly's `BF64` and
`BF64.Ext3` at pin `3468b38c8fd270f93f55a259220a8abc544e7437`:

```text
K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)      BF64.basePoly_eq, BF64.basePoly_irreducible
E = K[y]/(y^3 + y + 1),  |E| = 2^192         BF64.ext3Params_poly, BF64.ext3Poly_irreducible
```

`K` is a `BitVec 64` whose bit `i` is the coefficient of `x^i`
(`crates/primitives/src/field/gf2_64.rs:19-22`, `F64`); `E` is a `Vector K 3` whose limb `i` is
the coefficient of `y^i`. Everything below is an abbreviation or a one-line definition over those
CompPoly declarations, so the trusted surface is the CompPoly rows of the roadmap's dependency
table plus this file.

## Wrong readings excluded

* `CompPoly.Fields.Binary.Tower` presents `GF(2^64)` with a different bit encoding; it is never
  used.
* The numeral `2 : K` is the `BitVec` literal `x` (bit 1), not `1 + 1`, which is `0` in
  characteristic two.
* `ofK a` occupies the `y^0` limb only. "`x ∈ K`" is the predicate `IsInK`; a canonical 128-bit
  word, the cell shape BLAKE2S consumes, is `IsCanonical128`.

## Computability and the module system

The section is `@[expose]`d so that definitions unfold downstream. From a `module` file, the
kernel reduces `K` arithmetic, `E.ofLimbs`, `E.limb`, and the two predicates on literal words
(`decide +kernel`), which is why `E.ofLimbs` is a literal vector. It does not reduce CompPoly's
`Ext.ofFn`, hence not `ofK`, `y`, `+`, `*`, or `DecidableEq E`: core's `Array.ofFn` is not
`@[expose]`d, and a `module` importer sees only exposed bodies. Executable checks of those go
through compiled evaluation (`#guard` under `meta import`), and any later-layer plan to decide an
execution by `decide` depends on CompPoly or core lifting this.

## Clean's field interface

Clean's `FiniteField K` is `instFiniteFieldK` in `LeanerVM.Parameters.CleanField`, a plain
file: Clean at `93c9d1ef` does not use Lean's module system, and Lean `v4.33.1` refuses to
import a non-`module` file from a `module` (`Lean.Environment.importModulesCore`). This module
stays a `module` so that the Semantics layer can import it as one.
-/

namespace LeanerVM.Parameters

@[expose] public section

open CompPoly.Extension

/-! ## The fields -/

/-- `K = GF(2^64)`, CompPoly's `BF64`: a `BitVec 64` with bit `i` the coefficient of `x^i`. -/
abbrev K : Type := BF64

/-- `E = K[y]/(y^3 + y + 1)`, CompPoly's `BF64.Ext3`: a `Vector K 3` in limb order
`c0 + c1·y + c2·y²`. -/
abbrev E : Type := BF64.Ext3

/-- The adjoined root `y` of `y^3 + y + 1`. -/
def y : E := BF64.ext3Gen

/-- The defining relation of `E`: `y^3 = y + 1`. -/
theorem y_pow_three : y ^ 3 = y + 1 := BF64.ext3Gen_pow_three

/-! ## Limbs -/

/-- The embedding `K ↪ E` as the `y^0` limb; it is `algebraMap K E` by `rfl`. -/
abbrev ofK (a : K) : E := Ext.ofBase a

/-- Limb `i` of a word: the coefficient of `y^i`. -/
abbrev E.limb (x : E) (i : Fin 3) : K := Ext.coeff x i

/-- The word `c0 + c1·y + c2·y²`, as the literal limb vector. -/
def E.ofLimbs (c0 c1 c2 : K) : E := Ext.ofVector #v[c0, c1, c2]

/-- A word lies in `K`: its `y` and `y²` limbs are zero. -/
def IsInK (x : E) : Prop := x.limb 1 = 0 ∧ x.limb 2 = 0

/-- A canonical 128-bit word: its `y²` limb is zero. -/
def IsCanonical128 (x : E) : Prop := x.limb 2 = 0

instance : DecidablePred IsInK :=
  fun x ↦ inferInstanceAs (Decidable (x.limb 1 = 0 ∧ x.limb 2 = 0))

instance : DecidablePred IsCanonical128 :=
  fun x ↦ inferInstanceAs (Decidable (x.limb 2 = 0))

/-- Hexadecimal rendering `E(0x<c2><c1><c0>)`, the Python verifier's `E.__repr__`
(`python-verifier/verifier.py:177`). -/
instance : ToString E :=
  ⟨fun x ↦ s!"E(0x{(x.limb 2).toHex}{(x.limb 1).toHex}{(x.limb 0).toHex})"⟩

/-! ## Load-bearing lemmas -/

/-- Words with the same limbs are equal. -/
theorem E.ext {x z : E} (h : ∀ i, x.limb i = z.limb i) : x = z := Ext.ext h

/-- The limbs of `E.ofLimbs c0 c1 c2` are `c0, c1, c2`. -/
@[simp] theorem limb_ofLimbs (c0 c1 c2 : K) (i : Fin 3) :
    (E.ofLimbs c0 c1 c2).limb i = ![c0, c1, c2] i := by
  fin_cases i <;> rfl

/-- `ofK a` has `a` in limb `0` and zero elsewhere. -/
@[simp] theorem limb_ofK (a : K) (i : Fin 3) :
    (ofK a).limb i = if (i : ℕ) = 0 then a else 0 :=
  Ext.coeff_ofBase (P := BF64.ext3Params) a i

/-- `ofK` is injective. -/
theorem ofK_injective : Function.Injective ofK := by
  intro a b h
  simpa using congrArg (fun z : E ↦ z.limb 0) h

/-- Every word is its limbs in the basis `1, y, y²`. -/
theorem E.eq_sum_limbs (x : E) :
    x = ofK (x.limb 0) + ofK (x.limb 1) * y + ofK (x.limb 2) * y ^ 2 := by
  apply Ext.toQuot_injective
  have hx : Ext.toQuot x = ∑ i : Fin 3,
      algebraMap K (AdjoinRoot BF64.ext3Params.poly) (x.limb i) *
        Ext.rt BF64.ext3Params ^ (i : ℕ) := rfl
  rw [hx, Fin.sum_univ_three]
  simp [y]

/-- `E.ofLimbs c0 c1 c2 = c0 + c1·y + c2·y²`. -/
theorem ofLimbs_eq (c0 c1 c2 : K) :
    E.ofLimbs c0 c1 c2 = ofK c0 + ofK c1 * y + ofK c2 * y ^ 2 := by
  conv_lhs => rw [E.eq_sum_limbs (E.ofLimbs c0 c1 c2)]
  simp

/-- Rebuilding a word from its limbs is the identity. -/
theorem ofLimbs_limb (x : E) : E.ofLimbs (x.limb 0) (x.limb 1) (x.limb 2) = x :=
  E.ext fun i ↦ by fin_cases i <;> simp

/-- `IsInK` is exactly the image of `ofK`. -/
theorem isInK_iff (x : E) : IsInK x ↔ ∃ a, x = ofK a := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x.limb 0, E.ext fun i ↦ by fin_cases i <;> simp [h1, h2]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨by simp, by simp⟩

end
end LeanerVM.Parameters
