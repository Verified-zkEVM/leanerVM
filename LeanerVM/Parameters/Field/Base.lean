/-
  LeanerVM.Parameters.Field.Base

  The leanVM base field `K = GF(2^64)` and its distinguished generator, bound to the
  pinned leanVM revision.
-/

module

public import LeanerVM.Parameters.Field.BaseCertificate
public import CompPoly.Data.Polynomial.Rabin
public import CompPoly.Data.RingTheory.CanonicalEuclideanDomain
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.ComputeDegree

/-!
# The leanVM base field `K = GF(2^64)`

The leanVM specification fixes

```text
K = F_2[x]/(x^64 + x^4 + x^3 + x + 1)
```

(`doc/leanvm/body/02-vm-specification.tex`, lines 5-12) and a generator `g` of `K^×`
of order `2^64 - 1`. The pinned Rust agrees: `crates/primitives/src/field/gf2_64.rs`
represents an element as a `u64` whose bit `i` is the coefficient of `x^i`, names the
reduction constant `R64 = 0x1B = x^4 + x^3 + x + 1`, and fixes `G = F64(2)`, the
element `x`.

Source revision: leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`.

## Main definitions and statements

* `basePoly` — the modulus, as a `Polynomial (ZMod 2)`. Specification only.
* `basePoly_irreducible` — irreducibility, by Rabin's test against the kernel-checked
  chains in `LeanerVM.Parameters.BaseCert`.
* `K` — the base field, as `AdjoinRoot basePoly`.
* `card_K` — `Fintype.card K = 2 ^ 64`.

## Implementation notes

`basePoly` is `noncomputable` because Mathlib's `Polynomial` is a `Finsupp`, which has
no executable representation. It exists to state irreducibility and is never evaluated.
CompPoly makes the same choice for `ExtensionParams.poly`.

`K` here is the *quotient* presentation, used for cardinality and as the target of the
bridge. The computable presentation that arithmetic actually runs on is
`LeanerVM.Parameters.Field.Base` in `Carrier.lean`, a `BitVec 64`; the two are related by
`Base.toQuot`, which `Base.toQuot_injective` and `Base.toQuot_surjective` show is a
bijection.
-/

namespace LeanerVM.Parameters.Field

open Polynomial CompPoly.RabinCert LeanerVM.Parameters.BaseCert

public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Little-endian coefficients of `x^64 + x^4 + x^3 + x + 1`: the terms of degree
`0, 1, 3, 4` and `64`. -/
@[expose] def baseCoeffs : List ℕ := [1, 1, 0, 1, 1] ++ List.replicate 59 0 ++ [1]

/-- The leanVM base-field modulus `x^64 + x^4 + x^3 + x + 1` over `GF(2)`. Part of the
specification only; it is never evaluated. -/
@[expose] noncomputable def basePoly : Polynomial (ZMod 2) := X ^ 64 + X ^ 4 + X ^ 3 + X + 1

/-- A run of zero coefficients shifts the rest of the list up by that many degrees. -/
theorem toPoly_replicate_zero {p : ℕ} (n : ℕ) (rest : List ℕ) :
    toPoly p (List.replicate n 0 ++ rest) = X ^ n * toPoly p rest := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, toPoly_cons, ih]
    simp [pow_succ]
    ring

/-- The certificate's coefficient encoding denotes `basePoly`. -/
theorem toPoly_baseCoeffs : toPoly 2 baseCoeffs = basePoly := by
  show toPoly 2 ([1, 1, 0, 1, 1] ++ (List.replicate 59 0 ++ [1])) = basePoly
  simp only [List.cons_append, List.nil_append, toPoly_cons, toPoly_replicate_zero, toPoly_nil,
    Nat.cast_zero, Nat.cast_one, map_zero, map_one, basePoly]
  ring

theorem basePoly_natDegree : basePoly.natDegree = 64 := by
  rw [basePoly]; compute_degree!

theorem basePoly_degree : basePoly.degree = (64 : ℕ) := by
  rw [basePoly]; compute_degree!

theorem basePoly_ne_zero : basePoly ≠ 0 := by
  intro h
  have hd := basePoly_natDegree
  rw [h, natDegree_zero] at hd
  exact absurd hd (by norm_num)

/-- The prime factors of `64`. `decide` cannot do this: `Nat.primeFactorsList` is
well-founded recursive and does not reduce in the kernel. -/
private theorem primeFactors_sixtyFour : (64 : ℕ).primeFactors = {2} := by
  rw [show (64 : ℕ) = 2 ^ 6 from by norm_num,
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]

/--
`x^64 + x^4 + x^3 + x + 1` is irreducible over `GF(2)`, by Rabin's test against the
kernel-checked chains in `LeanerVM.Parameters.BaseCert`.

Degree `64` has the single prime factor `2`, so the trace condition is joined by one
coprimality check, at exponent `2^32`.
-/
theorem basePoly_irreducible : Irreducible basePoly := by
  refine Polynomial.irreducible_of_rabin (d := 64) ?_ (by norm_num) ?_ ?_
  · exact basePoly_natDegree
  · rw [ZMod.card]
    exact dvd_X_pow_sub_X_of_runChain (steps := traceSteps) toPoly_baseCoeffs basePoly_ne_zero
      (by rfl) (by rfl)
  · intro ℓ hℓ
    rw [primeFactors_sixtyFour, Finset.mem_singleton] at hℓ
    subst hℓ
    rw [ZMod.card]
    exact isCoprime_X_pow_sub_X_of_runChain (steps := cop32Steps) (rp := cop32Rp)
      (w := cop32W) (u := cop32U) (v := cop32V) toPoly_baseCoeffs basePoly_ne_zero
      (by rfl) (by rfl) (by rfl) (by rfl)

instance : Fact (Irreducible basePoly) := ⟨basePoly_irreducible⟩

/-! ## The reduction identity -/

/-- The modulus below its leading term: `x^4 + x^3 + x + 1`, the polynomial the Rust
names `R64 = 0x1B`. -/
@[expose] noncomputable def baseTail : Polynomial (ZMod 2) := X ^ 4 + X ^ 3 + X + 1

theorem baseTail_eq : baseTail = X ^ 4 + X ^ 3 + X + 1 := rfl

theorem basePoly_eq : basePoly = X ^ 64 + X ^ 4 + X ^ 3 + X + 1 := rfl

theorem basePoly_eq_add_tail : basePoly = X ^ 64 + baseTail := by
  unfold basePoly baseTail; ring

/-- `x^64 ≡ x^4 + x^3 + x + 1` modulo the modulus: multiplying by `X ^ 64` may be
replaced by multiplying by `baseTail`. -/
theorem mul_pow_reduce (A : Polynomial (ZMod 2)) :
    (A * X ^ 64) % basePoly = (A * baseTail) % basePoly := by
  have hadd : (X : (ZMod 2)[X]) ^ 64 = basePoly + baseTail := by
    rw [basePoly_eq_add_tail, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, mul_add, show A * basePoly + A * baseTail = A * baseTail + basePoly * A from by ring,
    CanonicalEuclideanDomain.add_mul_mod_right _ _ _ basePoly_ne_zero]

/-! ## The base field -/

/-- `K = GF(2^64)`, the leanVM base field: addresses, the program counter, the frame
pointer, counters, and committed lanes are `K`-valued. -/
noncomputable abbrev K : Type := AdjoinRoot basePoly

noncomputable instance : Field K := AdjoinRoot.instField

noncomputable instance : Fintype K := by
  let pb := AdjoinRoot.powerBasis basePoly_ne_zero
  letI : Module.Finite (ZMod 2) K := PowerBasis.finite pb
  haveI : Finite K := by
    have : Module.finrank (ZMod 2) K = pb.dim := PowerBasis.finrank pb
    exact Finite.of_equiv (Fin pb.dim →₀ ZMod 2) (pb.basis.repr.toEquiv.symm)
  exact Fintype.ofFinite K

/-- `K` has `2^64` elements. -/
theorem card_K : Fintype.card K = 2 ^ 64 := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := K)]
  let pb := AdjoinRoot.powerBasis basePoly_ne_zero
  rw [PowerBasis.finrank pb]
  have hdim : pb.dim = basePoly.natDegree := rfl
  rw [hdim, basePoly_natDegree]
  norm_num

end
end LeanerVM.Parameters.Field
