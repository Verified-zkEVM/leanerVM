/-
  LeanerVM.Protocol.Whir.TransformWords

  The additive transform of an `E` table as three transforms of `K` tables, one per limb, run on
  the limbs' machine words: the twiddles lie in `K`, so the transform acts on each limb alone.
  Proved to compute the encoder.
-/

module

public import LeanerVM.Protocol.Whir.Transform
public import LeanerVM.Parameters.ToCompPoly.BF64Fast

/-!
# The additive transform on words

`fwd φ j m s` multiplies only by twiddles `φ (twiddle j s)` of `K`. Over `E`, with `φ` the
embedding of `K`, a product by an element of `K` acts on each limb alone, so the transform of an
`E` table is, limb by limb, the transform over `K` of its limbs (`limb_fwd`). `fwdW` is the
transform over `K` on the elements' 64-bit words, `xor` for the sum and `mulWord` for the product
(`fwdW_map`), each node's halves read once.

`encodeE κ R m` is the encoder by three such transforms per coset (`encodeE_getElem`: its entries
are `encode`'s, on `κ + R ≤ 64` positions' bits).

`fwd` itself reads each node's halves inside the closures that build the node's outputs; compiled
code runs it as `fwdFast`, with the halves read once (`fwd_eq_fwdFast`, `@[csimp]`, in
`LeanerVM.Protocol.Whir.Transform`): the transform in `j · 2 ^ (j - 1)` products and linear work
per level, over any ring.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly FastBF64

@[expose] public section

namespace Whir

/-! ## Halves of mapped vectors -/

section Halves

variable {α β : Type} {j : ℕ} (f : α → β)

private theorem joinHalves_map (a b : Vector α (2 ^ j)) :
    joinHalves (a.map f) (b.map f) = (joinHalves a b).map f := by
  ext w hw
  rw [joinHalves_getElem, Vector.getElem_map, joinHalves_getElem]
  split <;> simp

end Halves

/-! ## The transform on words -/

/-- The transform over `K` on the elements' words: `fwd` with `xor` and `mulWord`, each node's
halves read once. -/
def fwdW : (j : ℕ) → Vector UInt64 (2 ^ j) → K → Vector UInt64 (2 ^ j)
  | 0, m, _ => m
  | j + 1, m, s =>
    let t := toWord (twiddle j s)
    let lo := lowHalf m
    let hi := highHalf m
    let a : Vector UInt64 (2 ^ j) := Vector.ofFn fun i ↦ lo[i] ^^^ mulWord t hi[i]
    let b : Vector UInt64 (2 ^ j) := Vector.ofFn fun i ↦ a[i] ^^^ hi[i]
    joinHalves (fwdW j a s) (fwdW j b (s + domainPt (2 ^ j)))

/-- **The transform on words is the transform over `K`.** -/
private theorem fwdW_map : ∀ (j : ℕ) (m : Vector K (2 ^ j)) (s : K),
    fwdW j (m.map toWord) s = (fwd (RingHom.id K) j m s).map toWord
  | 0, _, _ => rfl
  | j + 1, m, s => by
    let A : Vector K (2 ^ j) := Vector.ofFn fun i ↦
      (lowHalf m)[i] + (RingHom.id K) (twiddle j s) * (highHalf m)[i]
    have ha : (Vector.ofFn fun i : Fin (2 ^ j) ↦ (lowHalf (m.map toWord))[i] ^^^
        mulWord (toWord (twiddle j s)) (highHalf (m.map toWord))[i]) = A.map toWord := by
      ext i hi
      simp [A, toWord_add, toWord_mul]
    have hb : (Vector.ofFn fun i : Fin (2 ^ j) ↦ (A.map toWord)[i] ^^^
        (highHalf (m.map toWord))[i]) =
        (Vector.ofFn fun i : Fin (2 ^ j) ↦ A[i] + (highHalf m)[i]).map toWord := by
      ext i hi
      simp [toWord_add]
    simp only [fwdW, fwd]
    rw [ha, hb, fwdW_map j, fwdW_map j, joinHalves_map]

/-! ## Limb by limb -/

/-- The novel polynomials over `E` are those over `K`, embedded. -/
private theorem novelAt_algebraMap (j : ℕ) (x : K) (u : ℕ) :
    novelAt (algebraMap K E) j x u = ofK (novelAt (RingHom.id K) j x u) := by
  simp only [novelAt, RingHom.id_apply]
  change _ = algebraMap K E _
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  split <;> simp

/-- Limb `l` of a polynomial's value over `E` is the value of its coefficients' limbs. -/
private theorem limb_novelEval (j : ℕ) (m : Vector E (2 ^ j)) (x : K) (l : Fin 3) :
    (novelEval (algebraMap K E) j m x).limb l =
      novelEval (RingHom.id K) j (m.map fun z ↦ z.limb l) x := by
  simp only [novelEval, limb_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  simp [novelAt_algebraMap, limb_ofK_mul]

/-- **The transform acts on each limb.** -/
private theorem limb_fwd {j : ℕ} (hj : j ≤ 64) (m : Vector E (2 ^ j)) (s : K) (w : ℕ)
    (hw : w < 2 ^ j) (l : Fin 3) :
    ((fwd (algebraMap K E) j m s)[w]).limb l =
      (fwd (RingHom.id K) j (m.map fun z ↦ z.limb l) s)[w] := by
  rw [fwd_getElem _ j hj _ _ w hw, fwd_getElem _ j hj _ _ w hw, limb_novelEval]

/-! ## The encoder -/

/-- The encoder by the transform on words: each coset's three limb transforms. -/
def encodeE (κ R : ℕ) (m : Vector E (2 ^ κ)) : Vector E (2 ^ (κ + R)) :=
  let w : Vector (Vector UInt64 (2 ^ κ)) 3 := Vector.ofFn fun l ↦ m.map fun z ↦ toWord (z.limb l)
  let cosets : Vector (Vector (Vector UInt64 (2 ^ κ)) 3) (2 ^ R) :=
    Vector.ofFn fun c ↦ Vector.ofFn fun l ↦ fwdW κ w[l] (domainPt (c.val * 2 ^ κ))
  Vector.ofFn fun y ↦
    let c := cosets[y.val / 2 ^ κ]'(Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact y.isLt))
    let p := y.val % 2 ^ κ
    have hp : p < 2 ^ κ := Nat.mod_lt _ (Nat.two_pow_pos κ)
    E.ofLimbs (ofWord c[0][p]) (ofWord c[1][p]) (ofWord c[2][p])

/-- A limb's transform on words, read back, is the limb of the transform over `E`. -/
private theorem ofWord_fwdW {κ : ℕ} (hκ : κ ≤ 64) (m : Vector E (2 ^ κ)) (l : Fin 3) (s : K)
    (p : ℕ) (hp : p < 2 ^ κ) :
    ofWord (fwdW κ (m.map fun z ↦ toWord (z.limb l)) s)[p] =
      ((fwd (algebraMap K E) κ m s)[p]).limb l := by
  have hm : (m.map fun z ↦ toWord (z.limb l)) = (m.map fun z ↦ z.limb l).map toWord := by
    rw [Vector.map_map]
    rfl
  rw [hm, fwdW_map, Vector.getElem_map, ofWord_toWord, limb_fwd hκ]

/-- **The encoder on words is the encoder**, on `κ + R ≤ 64` positions' bits. -/
theorem encodeE_getElem {κ R : ℕ} (hb : κ + R ≤ 64) (m : CMlPolynomialEval E κ)
    (y : Fin (2 ^ (κ + R))) : (encodeE κ R m)[y] = encode (algebraMap K E) κ R m y := by
  rw [← encodeFast_getElem (algebraMap K E) hb m y]
  apply E.ext
  intro l
  have hp : y.val % 2 ^ κ < 2 ^ κ := Nat.mod_lt _ (Nat.two_pow_pos κ)
  simp only [encodeE, encodeFast, Fin.getElem_fin, Vector.getElem_ofFn,
    ofWord_fwdW (by omega : κ ≤ 64) m _ _ _ hp]
  exact congrArg (fun z : E ↦ z.limb l) (ofLimbs_limb _)

end Whir

end

end LeanerVM.Protocol
