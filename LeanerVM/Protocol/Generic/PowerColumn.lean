/-
  LeanerVM.Protocol.Generic.PowerColumn

  Multilinear evaluation of a geometric power table.
-/

module

public import LeanerVM.Protocol.Multilinear

/-!
# Power columns

The table indexed by little-endian Boolean integers has entry `a ^ i` at index `i`.
Its multilinear extension is the product of the one-bit interpolants. The proof follows
CompPoly's low-bit-first folding evaluator, so the ordering is part of the theorem.
This generic algebra supplies the public index column of protocol-blueprint Layer 1.

Category A: the index-column factorization in leanVM specification §6.5
(`doc/leanvm/body/06-bus-interactions.tex:95-100`) at
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, generalized from the characteristic-two
generator to any element of a commutative ring. The pinned
`crates/primitives/src/field/mod.rs:102-113` and `python-verifier/verifier.py:271-278`
use this factorization with successive squaring in low-coordinate order.

Upstream consumer: [ArkLib #900](https://github.com/Verified-zkEVM/ArkLib/issues/900),
for public-column readout in protocol Layer 1. The geometric-table algebra remains a
CompPoly migration candidate; this staging module changes no dependency pin.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Powers in little-endian cube order. -/
def powerColumnValues (a : R) (n : ℕ) : CMlPolynomialEval R n :=
  Vector.ofFn fun i ↦ a ^ i.val

/-- A coefficient homomorphism maps a power table to the power table of the mapped base. -/
theorem map_powerColumnValues (φ : R →+* S) (a : R) (n : ℕ) :
    CMlPolynomialEval.map φ (powerColumnValues a n) = powerColumnValues (φ a) n := by
  apply Vector.ext
  intro i hi
  simp [CMlPolynomialEval.map, powerColumnValues]

/-- Native evaluation of the geometric table, with the low bit at coordinate zero. -/
theorem evalMle_powerColumnValues (a : R) (n : ℕ) (x : Vector R n) :
    evalMle (powerColumnValues a n) x =
      ∏ j : Fin n, ((1 - x[j]) + x[j] * a ^ (2 ^ j.val)) := by
  induction n generalizing a with
  | zero => simp [powerColumnValues, evalMle, evalMleValues]
  | succ n ih =>
    rw [evalMle_succ]
    have hstep : evalMleLayer (powerColumnValues a (n + 1)) x.head =
        ((1 - x.head) + x.head * a) • powerColumnValues (a ^ 2) n := by
      apply Vector.ext
      intro j hj
      rw [← Vector.get_eq_getElem _ ⟨j, hj⟩, evalMleLayer_get]
      rw [Vector.getElem_smul]
      simp only [powerColumnValues, Vector.get_ofFn, Vector.getElem_ofFn, smul_eq_mul]
      simp only [pow_mul, pow_add, pow_one]
      ring
    rw [hstep, eval_mle_eq_eval, eval_smul, ← eval_mle_eq_eval, ih,
      Fin.prod_univ_succ]
    congr 1
    · simp [Vector.head]
    · apply Finset.prod_congr rfl
      intro j _
      simp [pow_mul, Nat.pow_succ, Nat.mul_comm, Nat.add_comm]

/-- The same native formula after explicit coefficient embedding into another ring. -/
theorem eval₂Mle_powerColumnValues (φ : R →+* S) (a : R) (n : ℕ) (x : Vector S n) :
    eval₂Mle (powerColumnValues a n) φ x =
      ∏ j : Fin n, ((1 - x[j]) + x[j] * φ (a ^ (2 ^ j.val))) := by
  rw [eval₂Mle, map_powerColumnValues, evalMle_powerColumnValues]
  simp only [map_pow]

end
end LeanerVM.Protocol
