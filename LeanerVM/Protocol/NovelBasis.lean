/-
  LeanerVM.Protocol.NovelBasis

  The Reed-Solomon encoder of leanVM's polynomial commitment scheme over `K = GF(2^64)`: the
  subspace polynomials, the novel basis, the encoder, and the column weights (Annex B).
-/

module

public import LeanerVM.Parameters.Generator
public import LeanerVM.Protocol.ToArkLib.InnerProduct
public import LeanerVM.Protocol.ToCompPoly.BitProductTable
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Data.Nat.BitIndices

/-!
# The novel basis, the encoder and the column weights

Category B: Annex B, "Novel polynomial basis and additive NTT"
(`doc/leanvm/body/b-polynomial-commitment-scheme.tex`, `app:ntt`) at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, with `crates/pcs/src/ntt/additive_ntt_f64.rs`
(`AdditiveNttF64::standard`) and `python-verifier/verifier.py:956-989` (`_subspace_roots`,
`_induced_weight`) as the implementations it describes.

## What is defined

With the `F_2`-basis `e_c = g ^ c` of `K` (`basisElt`), the subspace polynomial `V_k` vanishes
on `U_k = <e_0, ..., e_{k-1}>`, and `Ŵ_k = V_k / V_k(e_k)` is its normalization (`normW`). The
novel basis is `X_j = ∏_k Ŵ_k ^ (bit k of j)`, and the encoder of a message `g : {0,1}^κ → S`
is read off the Annex's `Definition enc` directly,

```text
Enc_{κ,R}(g)[x_v] = Σ_u g(u) · ∏_k Ŵ_k(x_v) ^ u_k          x_v = Σ_c v_c e_c = K.ofBits v
```

(`encode`), the message read *directly* as novel-basis coefficients. The additive NTT is the
fast way to compute this table and is not defined here: the verifier never runs it
(Annex B, end of `app:ntt`), it touches the code through `columnWeight`, the weight `W_x` with
`Enc(g)[x] = <W_x, g>` (`encode_columnWeight`, `lem:colweight`) and its multilinear extension
`∏_k ((1 - r_k) + r_k Ŵ_k(x))` (`columnWeightMle`, the `mle` field of `columnWeight`), whose
agreement with the table is the structure's proof field. The extension is evaluated in `κ`
steps; building the table costs `2^κ`, so a verifier evaluates `columnWeightMle` directly.

`V_k(x)` is computed as the Rust and the Python compute it, not as the product over `U_k`:
`V_0(x) = x` and `V_{k+1}(x) = V_k(x) · (V_k(x) + V_k(e_k))` (`lem:subspace` (i) with (ii)),
the roots `V_k(e_k)` read off the layers `V_k(e_c)` (`subspaceLayer`) once, in one pass
(`subspaceRoots`). The Annex's definition,
the product over `U_k` (`subspaceVanish`), is what the recursion is proved to compute
(`vanish_eq`, `subspaceRoot_eq`), with `Ŵ_k(e_k) = 1` (`normW_basisElt`), `Ŵ_k = 0` on `U_k`
(`normW_domainPt_of_lt`) and `F_2`-linearity (`normW_add`); `basisElt_linearIndependent` is the
premise of CompPoly's additive NTT at this basis.

The encoder commutes with ring maps of the message ring (`encode_map`), so a `K`-valued message
has a `K`-valued word (`encode_ofK`, `isInK_encode_ofK`): level 0 of the protocol is the `K`
code, the later levels the `E` code. The encoder is linear (`encodeLinear`), evaluates the
polynomial with novel-basis coefficients `g` on the domain (`encode_eq_eval`), and two words that
agree on `2^κ` positions encode one message (`encode_eq_of_agree`, the distance
`2^(κ+R) - 2^κ + 1`; `encode_injective`), since the novel basis is triangular
(`natDegree_novelPoly`, `def:enc`).

CompPoly's `Fields/Binary/AdditiveNTT/NovelPolynomialBasis.lean` has the polynomial half generically
over a basis `β` of a binary field: `W` is `subspaceVanish` as a polynomial, `normalizedW` is
`normWPoly`, `Xⱼ` is `novelPoly` with `degree_Xⱼ`, `polynomialFromNovelCoeffs` is the polynomial
of `encode_eq_eval`, and `inductive_linear_map_W`, `inductive_rec_form_W_comp` are
`subspaceVanish_add`, `subspaceVanish_succ'`. They are restated here at `K` rather than
instantiated: CompPoly's definitions are noncomputable, take `[Fintype L]` (noncomputable at `K`)
and an index `Fin r` bounding the stage, while the verifier runs the recursion; the bridge is
`vanish_eq`.

## Wrong readings excluded

* `e_c` (`basisElt`) is the field element `x ^ c`, the word `2 ^ c`, not the `c`-th novel
  polynomial `X_c`.
* The message is not converted between bases before encoding (`def:enc`, last sentence).
* A query position `v` is an integer whose bits are the coordinates of `x_v` in the basis `e_c`:
  `domainPt v = K.ofBits v`, as in the Python's `E(query)`.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomial CMlPolynomialEval

@[expose] public section

/-! ## The subspace polynomials -/

/-- The `F_2`-basis `e_c = g ^ c` of `K`, `0 ≤ c < 64`; `e_0 = 1`. -/
abbrev basisElt (c : ℕ) : K := g ^ c

/-- The layers of the roots: layer `k` lists `V_k(e_c)` for `c < 64`, from
`V_{k+1}(e_c) = V_k(e_c) · (V_k(e_c) + V_k(e_k))` (`_subspace_roots`, `verifier.py:956`). -/
def subspaceLayer : ℕ → List K
  | 0 => (List.range 64).map basisElt
  | k + 1 =>
    let layer := subspaceLayer k
    let root := layer.getD k 0
    layer.map fun v ↦ v * (v + root)

/-- The diagonal of the layers from stage `k` on: the roots of `n` stages, each layer computed
once from the previous one. -/
def rootsFrom : ℕ → ℕ → List K → List K
  | 0, _, _ => []
  | n + 1, k, layer =>
    let root := layer.getD k 0
    root :: rootsFrom n (k + 1) (layer.map fun v ↦ v * (v + root))

/-- The roots `V_k(e_k)`, `k < 64`, in one pass over the layers (`_subspace_roots`). -/
def subspaceRoots : List K := rootsFrom 64 0 (subspaceLayer 0)

/-- The root `V_k(e_k)` of stage `k`. From stage `64` on it is `0`: `U_64` is all of `K`, the
normalization `Ŵ_k` is `0` there, and every theorem below bounds the stage. -/
def subspaceRoot (k : ℕ) : K := subspaceRoots.getD k 0

/-- `V_k(x)`, the subspace vanishing polynomial of `U_k` at `x`: `V_0(x) = x`,
`V_{k+1}(x) = V_k(x) · (V_k(x) + V_k(e_k))`. -/
def vanish (x : K) : ℕ → K
  | 0 => x
  | k + 1 => vanish x k * (vanish x k + subspaceRoot k)

/-- The normalized subspace polynomial `Ŵ_k(x) = V_k(x) / V_k(e_k)`, so `Ŵ_k(e_k) = 1`. -/
def normW (k : ℕ) (x : K) : K := vanish x k / subspaceRoot k

/-! ## The Annex's definition -/

/-- The point `x_v = Σ_c v_c e_c` of the domain `D`, for the position `v`. -/
def domainPt (v : ℕ) : K := K.ofBits v

/-- The Annex's definition: `V_k(x) = ∏_{u ∈ U_k} (x + u)`, the product over the `2 ^ k` points
`x_m = Σ_c m_c e_c`, `m < 2 ^ k`, of the span `U_k = <e_0, ..., e_{k-1}>`. -/
def subspaceVanish (k : ℕ) (x : K) : K := ∏ m ∈ Finset.range (2 ^ k), (x + domainPt m)

/-- The domain's origin is `0`. -/
private theorem domainPt_zero : domainPt 0 = 0 := by decide +kernel

/-- `x_v` is additive in the position: `x_{a ⊕ b} = x_a + x_b`. -/
private theorem domainPt_xor (a b : ℕ) : domainPt (a ^^^ b) = domainPt a + domainPt b := by
  unfold domainPt K.ofBits
  rw [BF64.add_def, BitVec.ofNat_xor]
  rfl

/-- Adding the bit `2 ^ k` to a position below it adds `e_k`. -/
private theorem domainPt_two_pow_add {k m : ℕ} (hm : m < 2 ^ k) :
    domainPt (2 ^ k + m) = domainPt (2 ^ k) + domainPt m := by
  rw [← domainPt_xor, Nat.sum_of_and_eq_zero_is_xor (by
    simp [Nat.two_pow_and, Nat.testBit_eq_false_of_lt hm])]

/-- Positions below `2 ^ 64` are distinct points of `K`. -/
theorem domainPt_injOn {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : domainPt a = domainPt b) : a = b := by
  have h' : BitVec.ofNat 64 a = BitVec.ofNat 64 b := congrArg BF64.toBitVec h
  have := congrArg BitVec.toNat h'
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- `lem:subspace` (i), before (ii): `V_{k+1}(x) = V_k(x) · V_k(x + e_k)`, by splitting
`U_{k+1} = U_k ⊔ (e_k + U_k)`. -/
private theorem subspaceVanish_succ {k : ℕ} (x : K) :
    subspaceVanish (k + 1) x = subspaceVanish k x * subspaceVanish k (x + domainPt (2 ^ k)) := by
  unfold subspaceVanish
  rw [pow_succ, mul_two, Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun m hm ↦ ?_
  rw [domainPt_two_pow_add (Finset.mem_range.mp hm), add_assoc]

theorem subspaceVanish_zero (x : K) : subspaceVanish 0 x = x := by
  simp [subspaceVanish, domainPt_zero]

/-- `lem:subspace` (ii): `V_k` is `F_2`-linear. -/
theorem subspaceVanish_add : ∀ {k : ℕ}, k ≤ 64 → ∀ x y : K,
    subspaceVanish k (x + y) = subspaceVanish k x + subspaceVanish k y
  | 0, _, x, y => by simp [subspaceVanish_zero]
  | k + 1, hk, x, y => by
    have ih := subspaceVanish_add (k := k) (by omega)
    have hrec : ∀ z, subspaceVanish (k + 1) z =
        subspaceVanish k z ^ 2 + subspaceVanish k (domainPt (2 ^ k)) * subspaceVanish k z := by
      intro z
      rw [subspaceVanish_succ, ih z, sq]; ring
    rw [hrec, hrec, hrec, ih, CharTwo.add_sq]
    ring

/-- `lem:subspace` (i): `V_{k+1}(x) = V_k(x) · (V_k(x) + V_k(e_k))`. -/
theorem subspaceVanish_succ' {k : ℕ} (hk : k < 64) (x : K) :
    subspaceVanish (k + 1) x =
      subspaceVanish k x * (subspaceVanish k x + subspaceVanish k (domainPt (2 ^ k))) := by
  rw [subspaceVanish_succ, subspaceVanish_add (by omega)]

private theorem length_subspaceLayer : ∀ k, (subspaceLayer k).length = 64
  | 0 => by simp [subspaceLayer]
  | k + 1 => by simp [subspaceLayer, length_subspaceLayer k]

/-- The basis element `e_k = g ^ k` is the point of position `2 ^ k`. -/
theorem basisElt_eq_domainPt : ∀ k < 64, basisElt k = domainPt (2 ^ k) := by decide +kernel

/-- Layer `k` lists `V_k(e_c)`. -/
private theorem subspaceLayer_getD : ∀ {k : ℕ}, k ≤ 64 → ∀ {c : ℕ}, c < 64 →
    (subspaceLayer k).getD c 0 = subspaceVanish k (basisElt c)
  | 0, _, c, hc => by
    simp [subspaceLayer, subspaceVanish_zero, hc]
  | k + 1, hk, c, hc => by
    have ih : ∀ {c : ℕ}, c < 64 →
        (subspaceLayer k).getD c 0 = subspaceVanish k (basisElt c) :=
      fun {c} hc ↦ subspaceLayer_getD (k := k) (by omega) hc
    have hlen := length_subspaceLayer k
    have hroot : (subspaceLayer k).getD k 0 = subspaceVanish k (basisElt k) := ih (by omega)
    simp only [subspaceLayer]
    rw [List.getD_eq_getElem _ _ (by simp [hlen, hc])]
    simp only [List.getElem_map]
    rw [← List.getD_eq_getElem _ 0 (by omega), ih hc, hroot, basisElt_eq_domainPt k (by omega),
      subspaceVanish_succ' (by omega), ← basisElt_eq_domainPt k (by omega)]

private theorem getD_rootsFrom : ∀ n k j : ℕ, j < n →
    (rootsFrom n k (subspaceLayer k)).getD j 0 = (subspaceLayer (k + j)).getD (k + j) 0
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, 0, _ => rfl
  | n + 1, k, j + 1, h => by
    rw [show k + (j + 1) = k + 1 + j by omega]
    exact getD_rootsFrom n (k + 1) j (by omega)

/-- The root `V_k(e_k)` of the implementation is the Annex's. -/
theorem subspaceRoot_eq {k : ℕ} (hk : k < 64) : subspaceRoot k = subspaceVanish k (basisElt k) :=
  ((getD_rootsFrom 64 0 k hk).trans (by rw [Nat.zero_add])).trans
    (subspaceLayer_getD (by omega) hk)

/-- The recursion computes the Annex's product: `vanish x k = V_k(x)`, for `k ≤ 64`. -/
theorem vanish_eq : ∀ {k : ℕ}, k ≤ 64 → ∀ x : K, vanish x k = subspaceVanish k x
  | 0, _, x => by simp [vanish, subspaceVanish_zero]
  | k + 1, hk, x => by
    rw [vanish, vanish_eq (by omega), subspaceRoot_eq (by omega),
      subspaceVanish_succ' (by omega), basisElt_eq_domainPt k (by omega)]

/-- `V_k(e_k) ≠ 0`: `e_k ∉ U_k`, so the normalization divides by a unit. -/
theorem subspaceRoot_ne_zero {k : ℕ} (hk : k < 64) : subspaceRoot k ≠ 0 := by
  rw [subspaceRoot_eq hk, basisElt_eq_domainPt k hk, subspaceVanish, Finset.prod_ne_zero_iff]
  intro m hm h
  have hm := Finset.mem_range.mp hm
  have hlt : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hk
  have := domainPt_injOn hlt (hm.trans hlt) (CharTwo.add_eq_zero.mp h)
  omega

/-- `Ŵ_k(e_k) = 1`. -/
theorem normW_basisElt {k : ℕ} (hk : k < 64) : normW k (basisElt k) = 1 := by
  rw [normW, vanish_eq (by omega), ← subspaceRoot_eq hk, div_self (subspaceRoot_ne_zero hk)]

/-- `Ŵ_k` vanishes on `U_k`. -/
theorem normW_domainPt_of_lt {k m : ℕ} (hk : k ≤ 64) (hm : m < 2 ^ k) :
    normW k (domainPt m) = 0 := by
  rw [normW, vanish_eq hk, subspaceVanish,
    Finset.prod_eq_zero (Finset.mem_range.mpr hm) (CharTwo.add_self_eq_zero (domainPt m)), zero_div]

/-- `Ŵ_k` is `F_2`-linear, so `Ŵ_k(x_v) = Σ_c v_c Ŵ_k(e_c)`. -/
theorem normW_add {k : ℕ} (hk : k ≤ 64) (x y : K) :
    normW k (x + y) = normW k x + normW k y := by
  simp only [normW, vanish_eq hk, subspaceVanish_add hk, add_div]

/-- `Ŵ_0 = X`, since `e_0 = 1`. -/
theorem normW_zero (x : K) : normW 0 x = x := by
  rw [normW, vanish, subspaceRoot_eq (by omega), subspaceVanish_zero, show basisElt 0 = 1 from
    pow_zero g, div_one]

/-! ## The basis `e_c` -/

/-- The coordinates of a point of `K` in the `F_2`-basis `e_c`: the bits of its word. -/
private def bitsOf (x : K) : Fin 64 → ZMod 2 := fun c ↦ if x.toBitVec[c.val] then 1 else 0

private theorem bitsOf_add (x y : K) : bitsOf (x + y) = bitsOf x + bitsOf y := by
  funext c
  have h : (x + y).toBitVec = x.toBitVec ^^^ y.toBitVec := rfl
  simp only [bitsOf, Pi.add_apply, h, BitVec.getElem_xor]
  cases x.toBitVec[c.val] <;> cases y.toBitVec[c.val] <;> decide

private theorem bitsOf_basisElt (c : Fin 64) : bitsOf (basisElt c) = Pi.single c 1 := by
  funext j
  have h : ∀ c j : Fin 64, (basisElt c).toBitVec[j.val] = decide (j = c) := by decide +kernel
  simp [bitsOf, h, Pi.single_apply]

/-- `e_0, ..., e_63` are linearly independent over `F_2` (so they are a basis of `K`, which has
`2 ^ 64` elements): the premise of CompPoly's additive NTT at `β = e`. Stated for any module
structure of `K` over `ZMod 2`, since the proof uses the module laws only. -/
theorem basisElt_linearIndependent [Module (ZMod 2) K] :
    LinearIndependent (ZMod 2) (fun c : Fin 64 ↦ basisElt c) := by
  let f : K →ₗ[ZMod 2] (Fin 64 → ZMod 2) :=
    { toFun := bitsOf
      map_add' := bitsOf_add
      map_smul' := fun c x ↦ by
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl <;> (funext j; simp [bitsOf]) }
  refine LinearIndependent.of_comp f ?_
  convert (Pi.basisFun (ZMod 2) (Fin 64)).linearIndependent using 1
  funext c
  simp [f, bitsOf_basisElt]

/-! ## The encoder and the column weights -/

/-- The extension `∏_k ((1 - r_k) + r_k Ŵ_k(x_v))` of the weight of the column at `x_v`
(`lem:colweight`): what a verifier evaluates, in `κ` steps and without the table. -/
def columnWeightMle {S : Type*} [CommRing S] (φ : K →+* S) (κ R : ℕ) (v : Fin (2 ^ (κ + R)))
    (r : Vector S κ) : S :=
  ∏ k : Fin κ, ((1 - r[k]) + r[k] * φ (normW k (domainPt v)))

/-- The weight `W_x(u) = ∏_k Ŵ_k(x) ^ u_k` of the column at `x`, as a table over the cube built
from its `κ` factors, with its extension `columnWeightMle`. -/
def columnWeight {S : Type*} [CommRing S] (φ : K →+* S) (κ R : ℕ) (v : Fin (2 ^ (κ + R))) :
    Weight S κ :=
  let w := Vector.ofFn fun k : Fin κ ↦ φ (normW k (domainPt v))
  { onCube := bitProductTable fun k b ↦ if b then w[k] else 1
    mle := columnWeightMle φ κ R v
    mle_eq := fun r ↦ by
      rw [evalMle_bitProductTable]
      exact Finset.prod_congr rfl fun k _ ↦ by simp [w] }

/-- The encoder `Enc_{κ,R}`: the message `m`, read as novel-basis coefficients, evaluated on
the domain. -/
def encode {S : Type*} [CommRing S] (φ : K →+* S) (κ R : ℕ) (m : CMlPolynomialEval S κ)
    (v : Fin (2 ^ (κ + R))) : S :=
  (columnWeight φ κ R v).pair (RingHom.id S) m

/-- `lem:colweight`, first identity: the encoder is the inner product with the column weight.
It holds by definition, `encode` being that pairing; the identity's content, that the pairing is
`def:enc`, is `encode_eq_sum` with `eval_novelPoly`, or `encode_eq_eval`. -/
theorem encode_columnWeight {S : Type*} [CommRing S] (φ : K →+* S) (κ R : ℕ)
    (m : CMlPolynomialEval S κ) (v : Fin (2 ^ (κ + R))) :
    encode φ κ R m v = (columnWeight φ κ R v).pair (RingHom.id S) m := rfl

/-- The encoder as `Σ_u g(u) · ∏_k Ŵ_k(x_v) ^ u_k`: `def:enc` with the message read directly as
novel-basis coefficients. -/
theorem encode_eq_sum {S : Type*} [CommRing S] (φ : K →+* S) (κ R : ℕ)
    (m : CMlPolynomialEval S κ) (v : Fin (2 ^ (κ + R))) :
    encode φ κ R m v = ∑ u : Fin (2 ^ κ),
      (∏ k : Fin κ, if u.val.testBit k then φ (normW k (domainPt v)) else 1) * m[u] := by
  simp [encode, columnWeight, Weight.pair, bitProductTable_getElem]

/-- Encoding commutes with ring homomorphisms of the message ring: with `ψ` the inclusion of `K`
in `E`, a `K`-valued message gives a `K`-valued word. -/
theorem encode_map {S T : Type*} [CommRing S] [CommRing T] (φ : K →+* S) (ψ : S →+* T)
    (κ R : ℕ) (m : CMlPolynomialEval S κ) (v : Fin (2 ^ (κ + R))) :
    encode (ψ.comp φ) κ R (CMlPolynomialEval.map ψ m) v = ψ (encode φ κ R m v) := by
  rw [encode_eq_sum, encode_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [map_mul, map_prod]
  congr 1
  · exact Finset.prod_congr rfl fun k _ ↦ by split_ifs <;> simp
  · simp [CMlPolynomialEval.map]

/-- A `K`-valued message encodes, over `E`, to the image of its `K`-valued word. -/
theorem encode_ofK (κ R : ℕ) (m : CMlPolynomialEval K κ) (v : Fin (2 ^ (κ + R))) :
    encode (algebraMap K E) κ R (CMlPolynomialEval.map (algebraMap K E) m) v =
      ofK (encode (RingHom.id K) κ R m v) := by
  have := encode_map (RingHom.id K) (algebraMap K E) κ R m v
  rwa [RingHom.comp_id] at this

/-- Level 0 of the code: a word of `E`-valued weights against `K`-valued data lies in `K`. -/
theorem isInK_encode_ofK (κ R : ℕ) (m : CMlPolynomialEval K κ) (v : Fin (2 ^ (κ + R))) :
    IsInK (encode (algebraMap K E) κ R (CMlPolynomialEval.map (algebraMap K E) m) v) :=
  (isInK_iff _).2 ⟨_, encode_ofK κ R m v⟩

/-! ## The encoder is linear -/

section Linear
variable {S : Type*} [CommRing S] (φ : K →+* S) (κ R : ℕ)

/-- The encoder as an `S`-linear map of the message table: `def:enc`'s encoder is linear. The
tables' addition and scaling are CompPoly's module structure on `CMlPolynomialEval`. -/
noncomputable def encodeLinear : CMlPolynomialEval S κ →ₗ[S] (Fin (2 ^ (κ + R)) → S) where
  toFun m v := encode φ κ R m v
  map_add' m m' := by
    funext v
    simp only [encode_eq_sum, Pi.add_apply, ← Finset.sum_add_distrib, ← mul_add]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    congr 1
    change (Vector.zipWith (· + ·) m m')[u] = m[u] + m'[u]
    simp
  map_smul' c m := by
    funext v
    simp only [encode_eq_sum, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    change _ * (Vector.map (fun a ↦ c * a) m)[u] = _
    have h2 : (Vector.map (fun a ↦ c * a) m)[u] = c * m[u] := by simp
    rw [h2]
    ring

end Linear

/-! ## The encoder is injective -/

section Injectivity

open Polynomial

/-- `Ŵ_k` as a polynomial over `K`: the product over `U_k` scaled by the root's inverse. -/
noncomputable def normWPoly (k : ℕ) : K[X] :=
  C (subspaceRoot k)⁻¹ * ∏ m ∈ Finset.range (2 ^ k), (X + C (domainPt m))

/-- The polynomial `Ŵ_k` evaluates to `normW k`. -/
private theorem eval_normWPoly {k : ℕ} (hk : k < 64) (x : K) :
    (normWPoly k).eval x = normW k x := by
  simp only [normWPoly, normW, eval_mul, eval_C, eval_prod, Polynomial.eval_add, eval_X,
    vanish_eq (Nat.le_of_lt hk), subspaceVanish, div_eq_inv_mul]

/-- `Ŵ_k` is not the zero polynomial. -/
private theorem normWPoly_ne_zero {k : ℕ} (hk : k < 64) : normWPoly k ≠ 0 := by
  unfold normWPoly
  refine mul_ne_zero (by simpa using subspaceRoot_ne_zero hk) ?_
  exact (Polynomial.monic_prod_of_monic _ _ fun m _ ↦ monic_X_add_C _).ne_zero

/-- `deg Ŵ_k = 2 ^ k`. -/
private theorem natDegree_normWPoly {k : ℕ} (hk : k < 64) : (normWPoly k).natDegree = 2 ^ k := by
  unfold normWPoly
  rw [natDegree_C_mul (by simpa using subspaceRoot_ne_zero hk),
    natDegree_prod_of_monic _ _ fun m _ ↦ monic_X_add_C _]
  simp

/-- The novel polynomial `X_j = ∏_{k < κ, bit k of j} Ŵ_k` (`def:enc`). -/
noncomputable def novelPoly (κ j : ℕ) : K[X] :=
  ∏ k ∈ (Finset.range κ).filter (j.testBit ·), normWPoly k

/-- The binary expansion of `j < 2 ^ κ`: the powers of its bits sum to `j`. -/
private theorem sum_testBit_two_pow (κ j : ℕ) (hj : j < 2 ^ κ) :
    ∑ k ∈ (Finset.range κ).filter (j.testBit ·), 2 ^ k = j := by
  have h : (Finset.range κ).filter (j.testBit ·) = j.bitIndices.toFinset := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, Nat.mem_bitIndices,
      and_iff_right_iff_imp]
    exact fun hk ↦
      (Nat.pow_lt_pow_iff_right (by decide)).1 ((Nat.ge_two_pow_of_testBit hk).trans_lt hj)
  rw [h, List.sum_toFinset _ Nat.bitIndices_nodup, Nat.sum_map_two_pow_bitIndices]

/-- `deg X_j = j` for `j < 2 ^ κ`: the novel basis is triangular (`def:enc`). -/
theorem natDegree_novelPoly {κ j : ℕ} (hκ : κ ≤ 64) (hj : j < 2 ^ κ) :
    (novelPoly κ j).natDegree = j := by
  unfold novelPoly
  rw [natDegree_prod _ _ fun k hk ↦ normWPoly_ne_zero (by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1; omega)]
  refine Eq.trans (Finset.sum_congr rfl fun k hk ↦ natDegree_normWPoly (by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1; omega)) (sum_testBit_two_pow κ j hj)

private theorem novelPoly_ne_zero {κ j : ℕ} (hκ : κ ≤ 64) : novelPoly κ j ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k hk ↦ normWPoly_ne_zero (by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1; omega)

/-- `X_j(x) = ∏_k Ŵ_k(x) ^ (bit k of j)`: the novel polynomial is the encoder's table entry. -/
theorem eval_novelPoly {κ j : ℕ} (hκ : κ ≤ 64) (x : K) :
    (novelPoly κ j).eval x = ∏ k : Fin κ, if j.testBit k then normW k x else 1 := by
  unfold novelPoly
  rw [eval_prod, Finset.prod_filter, ← Fin.prod_univ_eq_prod_range (fun k ↦
    if j.testBit k then (normWPoly k).eval x else 1)]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  split_ifs
  · exact eval_normWPoly (by omega) x
  · rfl

/-- `def:enc`: the word at the position `v` is the polynomial with novel-basis coefficients `m`
evaluated at `x_v`. -/
theorem encode_eq_eval {S : Type*} [CommRing S] (φ : K →+* S) {κ R : ℕ} (hκ : κ ≤ 64)
    (m : CMlPolynomialEval S κ) (v : Fin (2 ^ (κ + R))) :
    encode φ κ R m v =
      (∑ u : Fin (2 ^ κ), C m[u] * (novelPoly κ u).map φ).eval (φ (domainPt v)) := by
  rw [encode_eq_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    eval_novelPoly hκ, map_prod]
  simp only [apply_ite φ, map_one]
  ring

/-- The difference of two encodings at `v` is the evaluation at `x_v` of the polynomial whose
novel-basis coefficients are the difference of the messages. -/
private theorem encode_sub_eq_eval {S : Type*} [CommRing S] (φ : K →+* S) {κ R : ℕ} (hκ : κ ≤ 64)
    (m m' : CMlPolynomialEval S κ) (v : Fin (2 ^ (κ + R))) :
    encode φ κ R m v - encode φ κ R m' v =
      (∑ u : Fin (2 ^ κ), C (m[u] - m'[u]) * (novelPoly κ u).map φ).eval
        (φ (domainPt v)) := by
  rw [encode_eq_eval φ hκ, encode_eq_eval φ hκ, ← Polynomial.eval_sub, ← Finset.sum_sub_distrib]
  simp only [C_sub, sub_mul]

/-- Two messages whose words agree on `2 ^ κ` distinct points of `K` are equal: the difference
polynomial has degree below `2 ^ κ` and vanishes there, and the novel polynomials have distinct
degrees. -/
private theorem eq_of_agree {S : Type*} [CommRing S] [IsDomain S] (φ : K →+* S) {κ R : ℕ}
    (hκ : κ ≤ 64) (hφ : Function.Injective φ) {m m' : CMlPolynomialEval S κ}
    (T : Finset (Fin (2 ^ (κ + R)))) (hT64 : ∀ v ∈ T, v.val < 2 ^ 64) (hT : 2 ^ κ ≤ T.card)
    (h : ∀ v ∈ T, encode φ κ R m v = encode φ κ R m' v) : m = m' := by
  classical
  set P : S[X] := ∑ u : Fin (2 ^ κ), C (m[u] - m'[u]) * (novelPoly κ u).map φ with hPdef
  have hP : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
      (f := fun v : T ↦ φ (domainPt v)) (fun i j hij ↦ ?_) (fun i ↦ ?_) ?_
    · exact Subtype.ext (Fin.ext (domainPt_injOn (hT64 _ i.2) (hT64 _ j.2) (hφ hij)))
    · have := encode_sub_eq_eval φ hκ m m' i.1
      rw [h _ i.2, sub_self] at this
      exact this.symm
    · refine (natDegree_sum_le_of_forall_le _ _ (n := 2 ^ κ - 1) fun u _ ↦ ?_).trans_lt
        (by rw [Fintype.card_coe]; have := Nat.two_pow_pos κ; omega)
      refine (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans ?_)
      rw [natDegree_novelPoly hκ u.2]
      omega
  by_contra hne
  have hT : (Finset.univ.filter fun u : Fin (2 ^ κ) ↦ m[u] ≠ m'[u]).Nonempty := by
    by_contra hT
    exact hne (Vector.ext fun i hi ↦ by_contra fun hi' ↦ hT ⟨⟨i, hi⟩, by simpa using hi'⟩)
  set u₀ := (Finset.univ.filter fun u : Fin (2 ^ κ) ↦ m[u] ≠ m'[u]).max' hT
  have hcoeff : P.coeff u₀ = (m[u₀] - m'[u₀]) * φ (novelPoly κ u₀).leadingCoeff := by
    rw [hPdef, finsetSum_coeff, Finset.sum_eq_single u₀ (fun u _ hu ↦ ?_) (by simp)]
    · rw [coeff_C_mul, coeff_map, leadingCoeff, natDegree_novelPoly hκ u₀.2]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hu) with hlt | hgt
    · rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
      exact natDegree_map_le.trans_lt ((natDegree_novelPoly hκ u.2).trans_lt hlt)
    · have : m[u] = m'[u] := by_contra fun hmem ↦
        absurd (Finset.le_max' _ u (by simpa using hmem)) (not_le.mpr hgt)
      rw [coeff_C_mul, this, sub_self, zero_mul]
  rw [hP, coeff_zero] at hcoeff
  exact mul_ne_zero (sub_ne_zero.mpr (Finset.mem_filter.mp (Finset.max'_mem _ hT)).2)
    ((map_ne_zero_iff φ hφ).mpr (leadingCoeff_ne_zero.mpr (novelPoly_ne_zero hκ))) hcoeff.symm

/-- The code has distance `2 ^ (κ + R) - 2 ^ κ + 1`: two words that agree on `2 ^ κ` positions
encode one message. `κ + R ≤ 64` keeps the positions distinct points of `K`; `S` is a domain into
which `K` embeds, as `E` is. -/
theorem encode_eq_of_agree {S : Type*} [CommRing S] [IsDomain S] (φ : K →+* S) {κ R : ℕ}
    (hκR : κ + R ≤ 64) (hφ : Function.Injective φ) {m m' : CMlPolynomialEval S κ}
    (T : Finset (Fin (2 ^ (κ + R)))) (hT : 2 ^ κ ≤ T.card)
    (h : ∀ v ∈ T, encode φ κ R m v = encode φ κ R m' v) : m = m' :=
  eq_of_agree φ (by omega) hφ T
    (fun v _ ↦ v.2.trans_le (Nat.pow_le_pow_right (by norm_num) hκR)) hT h

/-- The encoder is injective (`def:enc`: a linear injection), already on the first `2 ^ κ`
positions. `κ ≤ 64`, where the domain has `2 ^ 64` points. -/
theorem encode_injective {S : Type*} [CommRing S] [IsDomain S] (φ : K →+* S) {κ R : ℕ}
    (hκ : κ ≤ 64) (hφ : Function.Injective φ) : Function.Injective (encode φ κ R) := by
  intro m m' h
  have hle : 2 ^ κ ≤ 2 ^ (κ + R) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right κ R)
  refine eq_of_agree φ hκ hφ (Finset.univ.map (Fin.castLEEmb hle)) (fun v hv ↦ ?_) (by simp)
    fun v _ ↦ congrFun h v
  obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hv
  exact u.2.trans_le (Nat.pow_le_pow_right (by norm_num) hκ)

end Injectivity

end

end LeanerVM.Protocol
