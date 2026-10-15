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

/-!
# The novel basis, the encoder and the column weights

Protocol roadmap Layer 11 (`docs/roadmap/protocol-blueprint.md`), first slice of the WHIR
opening (issue #101). Category B: Annex B, "Novel polynomial basis and additive NTT"
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
`∏_k ((1 - r_k) + r_k Ŵ_k(x))`, the `mle` field of `columnWeight`, whose agreement with the
table is the structure's proof field.

`V_k(x)` is computed as the Rust and the Python compute it, not as the product over `U_k`:
`V_0(x) = x` and `V_{k+1}(x) = V_k(x) · (V_k(x) + V_k(e_k))` (`lem:subspace` (i) with (ii)),
the roots `V_k(e_k)` coming from the layers `V_k(e_c)` (`subspaceLayer`). The Annex's definition,
the product over `U_k` (`subspaceVanish`), is what the recursion is proved to compute
(`vanish_eq`, `subspaceRoot_eq`), with `Ŵ_k(e_k) = 1` (`normW_basisElt`), `Ŵ_k = 0` on `U_k`
(`normW_domainPt_of_lt`) and `F_2`-linearity (`normW_add`); `basisElt_linearIndependent` is the
premise of CompPoly's additive NTT at this basis
(`tests/LeanerVMTests/Protocol/NovelBasisNtt.lean`).

The encoder commutes with ring maps of the message ring (`encode_map`), so a `K`-valued message
has a `K`-valued word (`encode_ofK`, `isInK_encode_ofK`): level 0 of the protocol is the `K`
code, the later levels the `E` code. Not proved here: that `encode` is injective (the novel basis
is triangular, `def:enc`), which the soundness of the opening will need.

## Wrong readings excluded

* `e_c` is the field element `x ^ c`, the word `2 ^ c`, not the `c`-th novel polynomial: the
  blueprint's sketch names this basis `novelBasis`, here `basisElt`.
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

/-- The root `V_k(e_k)` of stage `k`. -/
def subspaceRoot (k : ℕ) : K := (subspaceLayer k).getD k 0

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
theorem domainPt_zero : domainPt 0 = 0 := by decide +kernel

/-- `x_v` is additive in the position: `x_{a ⊕ b} = x_a + x_b`. -/
theorem domainPt_xor (a b : ℕ) : domainPt (a ^^^ b) = domainPt a + domainPt b := by
  unfold domainPt K.ofBits
  rw [BF64.add_def, BitVec.ofNat_xor]
  rfl

/-- A position below `2 ^ k` shares no bit with `2 ^ k`. -/
theorem and_two_pow_of_lt {k m : ℕ} (hm : m < 2 ^ k) : 2 ^ k &&& m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  simp only [Nat.zero_testBit, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  by_cases h : k = i
  · subst h
    right; exact Nat.testBit_eq_false_of_lt hm
  · left; exact h

/-- Adding the bit `2 ^ k` to a position below it adds `e_k`. -/
theorem domainPt_two_pow_add {k m : ℕ} (hm : m < 2 ^ k) :
    domainPt (2 ^ k + m) = domainPt (2 ^ k) + domainPt m := by
  rw [← domainPt_xor, Nat.sum_of_and_eq_zero_is_xor (and_two_pow_of_lt hm)]

/-- Positions below `2 ^ 64` are distinct points of `K`. -/
theorem domainPt_injOn {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : domainPt a = domainPt b) : a = b := by
  have h' : BitVec.ofNat 64 a = BitVec.ofNat 64 b := congrArg BF64.toBitVec h
  have := congrArg BitVec.toNat h'
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- `lem:subspace` (i), before (ii): `V_{k+1}(x) = V_k(x) · V_k(x + e_k)`, by splitting
`U_{k+1} = U_k ⊔ (e_k + U_k)`. -/
theorem subspaceVanish_succ {k : ℕ} (x : K) :
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

theorem length_subspaceLayer : ∀ k, (subspaceLayer k).length = 64
  | 0 => by simp [subspaceLayer]
  | k + 1 => by simp [subspaceLayer, length_subspaceLayer k]

/-- The basis element `e_k = g ^ k` is the point of position `2 ^ k`. -/
theorem basisElt_eq_domainPt : ∀ k < 64, basisElt k = domainPt (2 ^ k) := by decide +kernel

/-- Layer `k` lists `V_k(e_c)`. -/
theorem subspaceLayer_getD : ∀ {k : ℕ}, k ≤ 64 → ∀ {c : ℕ}, c < 64 →
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

/-- The root `V_k(e_k)` of the implementation is the Annex's. -/
theorem subspaceRoot_eq {k : ℕ} (hk : k < 64) : subspaceRoot k = subspaceVanish k (basisElt k) :=
  subspaceLayer_getD (by omega) hk

/-- The recursion computes the Annex's product: `vanish x k = V_k(x)`, for `k ≤ 64`. -/
theorem vanish_eq : ∀ {k : ℕ}, k ≤ 64 → ∀ x : K, vanish x k = subspaceVanish k x
  | 0, _, x => by simp [vanish, subspaceVanish_zero]
  | k + 1, hk, x => by
    rw [vanish, vanish_eq (by omega), subspaceRoot_eq (by omega),
      subspaceVanish_succ' (by omega), basisElt_eq_domainPt k (by omega)]

/-- `V_k(e_k) ≠ 0`: `e_k ∉ U_k`, so the normalization divides by a unit. -/
theorem subspaceRoot_ne_zero {k : ℕ} (hk : k < 64) : subspaceRoot k ≠ 0 := by
  rw [subspaceRoot_eq hk, basisElt_eq_domainPt k hk]
  unfold subspaceVanish
  rw [Finset.prod_ne_zero_iff]
  intro m hm h
  have hm' := Finset.mem_range.mp hm
  have h2 : domainPt (2 ^ k) = domainPt m := by
    have := CharTwo.add_eq_zero.mp h
    exact this
  have hlt : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hk
  have := domainPt_injOn hlt (hm'.trans hlt) h2
  omega

/-- `Ŵ_k(e_k) = 1`. -/
theorem normW_basisElt {k : ℕ} (hk : k < 64) : normW k (basisElt k) = 1 := by
  unfold normW
  rw [vanish_eq (by omega), ← subspaceRoot_eq hk]
  exact div_self (subspaceRoot_ne_zero hk)

/-- `Ŵ_k` vanishes on `U_k`. -/
theorem normW_domainPt_of_lt {k m : ℕ} (hk : k ≤ 64) (hm : m < 2 ^ k) :
    normW k (domainPt m) = 0 := by
  unfold normW
  rw [vanish_eq hk]
  unfold subspaceVanish
  rw [Finset.prod_eq_zero (Finset.mem_range.mpr hm) (CharTwo.add_self_eq_zero (domainPt m)),
    zero_div]

/-- `Ŵ_k` is `F_2`-linear, so `Ŵ_k(x_v) = Σ_c v_c Ŵ_k(e_c)`. -/
theorem normW_add {k : ℕ} (hk : k ≤ 64) (x y : K) :
    normW k (x + y) = normW k x + normW k y := by
  unfold normW
  rw [vanish_eq hk, vanish_eq hk, vanish_eq hk, subspaceVanish_add hk, add_div]

/-- `Ŵ_0 = X`, since `e_0 = 1`. -/
theorem normW_zero (x : K) : normW 0 x = x := by
  unfold normW
  rw [vanish_eq (by omega), subspaceVanish_zero]
  have : subspaceRoot 0 = 1 := by
    rw [subspaceRoot_eq (by omega), subspaceVanish_zero]; decide +kernel
  rw [this, div_one]

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
  apply LinearIndependent.of_comp f
  have h : (f ∘ fun c : Fin 64 ↦ basisElt c) =
      fun c : Fin 64 ↦ (Pi.single c 1 : Fin 64 → ZMod 2) := by
    funext c; exact bitsOf_basisElt c
  rw [h]
  have h' := (Pi.basisFun (ZMod 2) (Fin 64)).linearIndependent
  have e : (⇑(Pi.basisFun (ZMod 2) (Fin 64)) : Fin 64 → Fin 64 → ZMod 2) =
      fun c : Fin 64 ↦ (Pi.single c 1 : Fin 64 → ZMod 2) := by
    funext c; exact Pi.basisFun_apply (ZMod 2) (Fin 64) c
  rw [← e]; exact h'

/-! ## The encoder and the column weights -/

/-- The weight `W_x(u) = ∏_k Ŵ_k(x) ^ u_k` of the column at `x`, as a table over the cube, with
its extension `∏_k ((1 - r_k) + r_k Ŵ_k(x))` (`lem:colweight`). -/
def columnWeight {S : Type*} [CommRing S] (φ : K →+* S) (κ R : ℕ) (v : Fin (2 ^ (κ + R))) :
    Weight S κ where
  onCube := bitProductTable fun (k : Fin κ) b ↦ if b then φ (normW k (domainPt v)) else 1
  mle := fun r ↦ ∏ k : Fin κ, ((1 - r[k]) + r[k] * φ (normW k (domainPt v)))
  mle_eq := fun r ↦ by
    rw [evalMle_bitProductTable]
    exact Finset.prod_congr rfl fun k _ ↦ by simp

/-- The encoder `Enc_{κ,R}`: the message `m`, read as novel-basis coefficients, evaluated on
the domain. -/
def encode {S : Type*} [CommRing S] (φ : K →+* S) (κ R : ℕ) (m : CMlPolynomialEval S κ)
    (v : Fin (2 ^ (κ + R))) : S :=
  (columnWeight φ κ R v).pair (RingHom.id S) m

/-- `lem:colweight`, first identity: the encoder is the inner product with the column weight. -/
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

/-- Encoding commutes with ring homomorphisms of the message ring: a `K`-valued message gives
a `K`-valued word (`encode_K` of the blueprint, with `ψ` the inclusion of `K` in `E`). -/
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

end

end LeanerVM.Protocol
