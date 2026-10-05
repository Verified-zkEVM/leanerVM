import LeanerVM.Protocol.Fingerprint

/-!
# Fingerprint and side-product tests

Over `E`, on concrete tuples:

* **Bit order.** At a Boolean `α` the fingerprint reads one coordinate, `α_k` the bit `k` of its
  index, low bit first: `α = (1, 0, 1, 0)` reads coordinate 5, `α = (1, 0, 0, 0)` coordinate 1
  and not 8. At a point off the cube it is the tuple's extension (`fingerprint_eq_eval₂Mle`).
* **Domain separators** (acceptance test 5). Two tuples equal but at coordinate 0, the
  separator, have different fingerprints, so a memory tuple and a bytecode tuple with the same
  other coordinates are not confused.
* **Multiplicities.** The product counts a tuple pushed twice twice, in characteristic two too:
  `{t}` and `{t, t}` give different products at a challenge, and different polynomials
  (`sideProduct_poly_eq_iff`). A sum of fingerprints, the shape a balance summed in the field
  takes, gives `0` for `{t, t}` and for `∅` alike.
* **Order.** The product of a list of tuples does not depend on its order.
* **The collision bound** applies to `{t}` and `{t, t}` with `N = 2`: at most `8·|E|⁴`
  challenges collide.

A plain file, so `#guard` evaluates the compiled definitions. Values of `E` written with numerals
are named as definitions before a guard uses them.
-/

namespace LeanerVMTests.Protocol.SideProduct

open LeanerVM.Parameters LeanerVM.Protocol CompPoly CMlPolynomialEval OracleComp
open scoped ENNReal

/-- A tuple with distinct coordinates: coordinate `i` is the polynomial whose bits are `i + 1`. -/
def t : Vector K 16 := Vector.ofFn fun i ↦ K.ofBits (i.val + 1)

/-- The same tuple with another separator. -/
def t' : Vector K 16 := t.set 0 (K.ofBits 100)

/-- `0` and `1` in `E`. -/
def e0 : E := 0
def e1 : E := 1

/-- Two challenges off the cube. -/
def α : Fin 4 → E := ![y, y + 1, y * y, y * y + 1]
def β : E := y * y * y + y

-- At a Boolean point the fingerprint reads one coordinate, low bit first.
#guard fingerprint ![e1, e0, e1, e0] t = ofK t[5]
#guard fingerprint ![e1, e0, e0, e0] t = ofK t[1]
#guard fingerprint ![e1, e0, e0, e0] t ≠ ofK t[8]

-- Off the cube it is the tuple's extension at `α`.
#guard fingerprint α t = eval₂Mle (n := 4) t (algebraMap K E) (Vector.ofFn α)

-- The separator is read: tuples differing only at coordinate 0 have different fingerprints.
#guard t'[1] = t[1] ∧ t'[15] = t[15]
#guard fingerprint α t ≠ fingerprint α t'

-- A tuple pushed twice is not a tuple pushed once.
#guard sideProduct α β {t} ≠ sideProduct α β {t, t}
#guard sideProduct α β {t, t} = (β - fingerprint α t) * (β - fingerprint α t)

-- A sum of fingerprints in characteristic two forgets the pair.
#guard fingerprint α t + fingerprint α t = e0

-- The polynomials differ: the product polynomial determines the multiset.
example : grandProductPoly (n := 4) ({t} : Multiset (Vector K 16)) ≠
    grandProductPoly (n := 4) ({t, t} : Multiset (Vector K 16)) := fun h ↦ by
  have := congrArg Multiset.card ((sideProduct_poly_eq_iff _ _).mp h)
  simp at this

-- The product does not depend on the order of the tuples.
example (a : Fin 4 → E) (b : E) (u v : Vector K 16) :
    sideProduct a b ↑[u, v] = sideProduct a b ↑[v, u] := by
  rw [Multiset.coe_eq_coe.mpr (List.Perm.swap v u [])]

-- The collision bound on `{t}` and `{t, t}`: at most `4·2·|E|⁴` challenges collide.
example : Nat.card {ab : (Fin 4 → E) × E //
      sideProduct ab.1 ab.2 {t} = sideProduct ab.1 ab.2 {t, t}} ≤ 4 * 2 * Nat.card E ^ 4 :=
  card_sideProduct_collision_le (by simp) (by simp) (by simp)

-- Its probability form: a uniform challenge collides with probability at most `8 / |E|`.
example : Pr{let ab ← $ᵗ ((Fin 4 → E) × E)}[
      sideProduct ab.1 ab.2 {t} = sideProduct ab.1 ab.2 {t, t}] ≤
    (4 * 2 : ℕ) / (Fintype.card E : ℝ≥0∞) :=
  sideProduct_collision (by simp) (by simp) (by simp)

end LeanerVMTests.Protocol.SideProduct
