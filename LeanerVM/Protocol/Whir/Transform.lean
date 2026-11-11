/-
  LeanerVM.Protocol.Whir.Transform

  The additive transform of the novel basis: the encoder's values on a coset of a subspace by the
  recursion of Lin, Chung and Han, its inverse, and the encoder by one transform per coset.
-/

module

public import LeanerVM.Protocol.NovelBasis

/-!
# The additive transform

The encoder evaluates the polynomial with novel-basis coefficients `m` on the domain. On a coset
`x_w + s` (`w < 2 ^ (j + 1)`) of `U_{j+1}`, `Ŵ_j` takes the value `Ŵ_j(s)` on the half `w < 2 ^ j`
and `Ŵ_j(s) + 1` on the other, so on each half the polynomial of `j + 1` variables is one of `j`
variables: the additive NTT of Lin, Chung and Han (Annex B, `app:ntt`).

* `fwd φ j m s`: the values of the polynomial with coefficients `m` on the coset of `s`
  (`fwd_getElem`), in `j · 2 ^ (j - 1)` products.
* `inv φ j v s`: the coefficients of the values `v` on the coset of `s`; `fwd` and `inv` are
  inverse (`fwd_inv`, `inv_fwd`).
* `encodeFast φ κ R m`: the encoder by one `fwd` per coset of `U_κ` (`encodeFast_getElem`).

Compiled code runs `fwd` with each half built once a step (`fwd_eq_fwdFast`, a `@[csimp]`
theorem): a half read inside the closure that builds the next vector is rebuilt at every entry,
which makes a step quadratic in its length.

Category A: the encoder `encode` of `LeanerVM.Protocol.NovelBasis` (Annex B, `def:enc`) is the
specification, and `encodeFast_getElem` proves that the transform computes it; the recursion is
Annex B's `app:ntt`, and nothing of an implementation is trusted.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly

@[expose] public section

/-! ## Halves of a vector -/

section Halves

variable {α : Type*} {j : ℕ}

/-- Two halves of `2 ^ (j + 1)`. -/
theorem two_pow_add_two_pow (j : ℕ) : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by
  rw [pow_succ]
  omega

/-- The first half of a vector of `2 ^ (j + 1)` entries. -/
def lowHalf (v : Vector α (2 ^ (j + 1))) : Vector α (2 ^ j) :=
  Vector.ofFn fun i ↦ v[i.val]'(by have := i.isLt; rw [pow_succ]; omega)

/-- The second half. -/
def highHalf (v : Vector α (2 ^ (j + 1))) : Vector α (2 ^ j) :=
  Vector.ofFn fun i ↦ v[i.val + 2 ^ j]'(by have := i.isLt; rw [pow_succ]; omega)

/-- Two halves joined. -/
def joinHalves (a b : Vector α (2 ^ j)) : Vector α (2 ^ (j + 1)) :=
  (a ++ b).cast (two_pow_add_two_pow j)

/-- The entries of the first half. -/
@[simp] theorem lowHalf_getElem (v : Vector α (2 ^ (j + 1))) (i : ℕ) (hi : i < 2 ^ j) :
    (lowHalf v)[i] = v[i]'(by rw [pow_succ]; omega) := by
  simp [lowHalf]

/-- The entries of the second half. -/
@[simp] theorem highHalf_getElem (v : Vector α (2 ^ (j + 1))) (i : ℕ) (hi : i < 2 ^ j) :
    (highHalf v)[i] = v[i + 2 ^ j]'(by rw [pow_succ]; omega) := by
  simp [highHalf]

/-- The entries of two halves joined. -/
theorem joinHalves_getElem (a b : Vector α (2 ^ j)) (w : ℕ) (hw : w < 2 ^ (j + 1)) :
    (joinHalves a b)[w] =
      if h : w < 2 ^ j then a[w] else b[w - 2 ^ j]'(by rw [pow_succ] at hw; omega) := by
  simp [joinHalves, Vector.getElem_append]

/-- The first half of two halves joined. -/
@[simp] theorem lowHalf_join (a b : Vector α (2 ^ j)) : lowHalf (joinHalves a b) = a := by
  ext i hi
  simp [joinHalves_getElem, hi]

/-- The second half of two halves joined. -/
@[simp] theorem highHalf_join (a b : Vector α (2 ^ j)) : highHalf (joinHalves a b) = b := by
  ext i hi
  simp [joinHalves_getElem]

/-- A vector is its two halves joined. -/
@[simp] theorem join_halves (v : Vector α (2 ^ (j + 1))) :
    joinHalves (lowHalf v) (highHalf v) = v := by
  ext w hw
  rw [joinHalves_getElem]
  split
  · simp
  · simp [Nat.sub_add_cancel (Nat.le_of_not_lt ‹_›)]

end Halves

/-! ## The transform -/

section Transform

variable {S : Type*} [CommRing S] (φ : K →+* S)

/-- The value at `x` of the novel polynomial `X_u` of `j` variables. -/
def novelAt (j : ℕ) (x : K) (u : ℕ) : S :=
  ∏ k : Fin j, if u.testBit k then φ (normW k x) else 1

/-- The polynomial with novel-basis coefficients `m` of `j` variables, at `x`. -/
def novelEval (j : ℕ) (m : Vector S (2 ^ j)) (x : K) : S :=
  ∑ u : Fin (2 ^ j), novelAt φ j x u * m[u]

/-- The inverses of the roots `V_k(e_k)`, computed once. -/
def rootInvs : Vector K 64 := Vector.ofFn fun k ↦ (subspaceRoot k)⁻¹

/-- `Ŵ_j(s)`, from the recursion for `V_j` and the stored inverse of `V_j(e_j)`. -/
def twiddle (j : ℕ) (s : K) : K :=
  if h : j < 64 then vanish s j * rootInvs[j] else normW j s

/-- The twiddle is `Ŵ_j(s)`. -/
theorem twiddle_eq (j : ℕ) (s : K) : twiddle j s = normW j s := by
  unfold twiddle normW
  split
  · rw [rootInvs, Vector.getElem_ofFn, div_eq_mul_inv]
  · rfl

/-- The values on the coset of `s` of the polynomial with novel-basis coefficients `m`. -/
def fwd : (j : ℕ) → Vector S (2 ^ j) → K → Vector S (2 ^ j)
  | 0, m, _ => m
  | j + 1, m, s =>
    let t := φ (twiddle j s)
    let a : Vector S (2 ^ j) := Vector.ofFn fun i ↦ (lowHalf m)[i] + t * (highHalf m)[i]
    let b : Vector S (2 ^ j) := Vector.ofFn fun i ↦ a[i] + (highHalf m)[i]
    joinHalves (fwd j a s) (fwd j b (s + domainPt (2 ^ j)))

/-- `fwd` with each half built once a step. -/
def fwdFast : (j : ℕ) → Vector S (2 ^ j) → K → Vector S (2 ^ j)
  | 0, m, _ => m
  | j + 1, m, s =>
    let t := φ (twiddle j s)
    let lo := lowHalf m
    let hi := highHalf m
    let a : Vector S (2 ^ j) := Vector.ofFn fun i ↦ lo[i] + t * hi[i]
    let b : Vector S (2 ^ j) := Vector.ofFn fun i ↦ a[i] + hi[i]
    joinHalves (fwdFast j a s) (fwdFast j b (s + domainPt (2 ^ j)))

/-- Compiled code builds each half once a step. -/
@[csimp] theorem fwd_eq_fwdFast : @fwd = @fwdFast := by
  funext S _ φ j
  induction j with
  | zero => rfl
  | succ j ih => funext m s; simp only [fwd, fwdFast, ih]

/-- The novel-basis coefficients of the values `v` on the coset of `s`. -/
def inv : (j : ℕ) → Vector S (2 ^ j) → K → Vector S (2 ^ j)
  | 0, v, _ => v
  | j + 1, v, s =>
    let t := φ (twiddle j s)
    let a := inv j (lowHalf v) s
    let b := inv j (highHalf v) (s + domainPt (2 ^ j))
    let m₁ : Vector S (2 ^ j) := Vector.ofFn fun i ↦ b[i] - a[i]
    joinHalves (Vector.ofFn fun i ↦ a[i] - t * m₁[i]) m₁

/-- `fwd` after `inv` is the identity. -/
theorem fwd_inv : ∀ (j : ℕ) (v : Vector S (2 ^ j)) (s : K), fwd φ j (inv φ j v s) s = v
  | 0, _, _ => rfl
  | j + 1, v, s => by
    simp only [fwd, inv, lowHalf_join, highHalf_join]
    conv_rhs => rw [← join_halves v, ← fwd_inv j (lowHalf v) s,
      ← fwd_inv j (highHalf v) (s + domainPt (2 ^ j))]
    congr 2 <;> ext i hi <;> simp

/-- `inv` after `fwd` is the identity. -/
theorem inv_fwd : ∀ (j : ℕ) (m : Vector S (2 ^ j)) (s : K), inv φ j (fwd φ j m s) s = m
  | 0, _, _ => rfl
  | j + 1, m, s => by
    have ih := inv_fwd j
    simp only [fwd, inv, lowHalf_join, highHalf_join, ih]
    conv_rhs => rw [← join_halves m]
    congr 1
    · ext i hi
      simp only [Vector.getElem_ofFn, Fin.getElem_fin]
      ring
    · ext i hi
      simp only [Vector.getElem_ofFn, Fin.getElem_fin]
      ring

/-! ## The values -/

/-- `x_v` is additive in the position: `x_{a ⊕ b} = x_a + x_b`. -/
private theorem domainPt_xor' (a b : ℕ) : domainPt (a ^^^ b) = domainPt a + domainPt b := by
  unfold domainPt K.ofBits
  rw [BF64.add_def, BitVec.ofNat_xor]
  rfl

/-- A position below `2 ^ j` plus a multiple of `2 ^ j` adds the points. -/
theorem domainPt_add_mul {w j : ℕ} (hw : w < 2 ^ j) (c : ℕ) :
    domainPt (w + c * 2 ^ j) = domainPt w + domainPt (c * 2 ^ j) := by
  rw [← domainPt_xor', Nat.sum_of_and_eq_zero_is_xor]
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.zero_testBit]
  by_cases h : j ≤ i
  · simp [h, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) h))]
  · simp [h]

/-- A novel polynomial of `j + 1` variables: the one of `j`, times `Ŵ_j` when bit `j` is set. -/
theorem novelAt_succ (j : ℕ) (x : K) (u : ℕ) :
    novelAt φ (j + 1) x u = novelAt φ j x u * if u.testBit j then φ (normW j x) else 1 := by
  unfold novelAt
  rw [Fin.prod_univ_castSucc]
  rfl

/-- Bit `j` does not change the first `j` factors. -/
theorem novelAt_add_two_pow {j i : ℕ} (x : K) :
    novelAt φ j x (i + 2 ^ j) = novelAt φ j x i := by
  unfold novelAt
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [add_comm, Nat.testBit_two_pow_add_gt k.isLt]

/-- The polynomial of `j + 1` variables is its low half plus `Ŵ_j` times its high half. -/
theorem novelEval_succ (j : ℕ) (m : Vector S (2 ^ (j + 1))) (x : K) :
    novelEval φ (j + 1) m x =
      novelEval φ j (lowHalf m) x + φ (normW j x) * novelEval φ j (highHalf m) x := by
  unfold novelEval
  rw [← Fin.sum_congr' _ (two_pow_add_two_pow j), Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Fin.getElem_fin, Fin.val_cast, Fin.val_castAdd, novelAt_succ,
      Nat.testBit_eq_false_of_lt i.isLt, lowHalf_getElem]
    simp
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hbit : (i.val + 2 ^ j).testBit j = true := by
      rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt i.isLt]
      rfl
    simp only [Fin.getElem_fin, Fin.val_cast, Fin.val_natAdd, novelAt_succ, highHalf_getElem,
      Nat.add_comm (2 ^ j) (i : ℕ), novelAt_add_two_pow, hbit, ↓reduceIte]
    ring

/-- The polynomial is linear in its coefficients. -/
theorem novelEval_ofFn_add_mul (j : ℕ) (p q : Fin (2 ^ j) → S) (c : S) (x : K) :
    novelEval φ j (Vector.ofFn fun i ↦ p i + c * q i) x =
      novelEval φ j (Vector.ofFn p) x + c * novelEval φ j (Vector.ofFn q) x := by
  simp only [novelEval, Fin.getElem_fin, Vector.getElem_ofFn, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ ↦ by ring

/-- **The transform evaluates**: position `w` of `fwd φ j m s` is the polynomial with novel-basis
coefficients `m` at `x_w + s`. -/
theorem fwd_getElem : ∀ (j : ℕ), j ≤ 64 → ∀ (m : Vector S (2 ^ j)) (s : K) (w : ℕ)
    (hw : w < 2 ^ j), (fwd φ j m s)[w] = novelEval φ j m (domainPt w + s)
  | 0, _, m, s, w, hw => by
    obtain rfl : w = 0 := by simpa using hw
    simp [fwd, novelEval, novelAt]
  | j + 1, hj, m, s, w, hw => by
    have ih := fwd_getElem j (by omega)
    simp only [fwd]
    rw [joinHalves_getElem, novelEval_succ]
    split
    · rename_i h
      rw [ih _ s w h, normW_add (by omega), normW_domainPt_of_lt (by omega) h, zero_add,
        ← twiddle_eq, novelEval_ofFn_add_mul]
      simp only [Fin.getElem_fin, Vector.ofFn_getElem]
    · rename_i h
      have hw' : w - 2 ^ j < 2 ^ j := by rw [pow_succ] at hw; omega
      rw [ih _ _ (w - 2 ^ j) hw']
      have hx : domainPt w + s = domainPt (w - 2 ^ j) + (s + domainPt (2 ^ j)) := by
        have hw2 : w = (w - 2 ^ j) + 1 * 2 ^ j := by omega
        conv_lhs => rw [hw2]
        rw [domainPt_add_mul hw', one_mul]
        ring
      rw [hx, normW_add (by omega), normW_domainPt_of_lt (by omega) hw', zero_add,
        normW_add (by omega), ← basisElt_eq_domainPt j (by omega), normW_basisElt (by omega),
        ← twiddle_eq, map_add, map_one]
      have hb : (Vector.ofFn fun i : Fin (2 ^ j) ↦
          (Vector.ofFn fun i : Fin (2 ^ j) ↦
            (lowHalf m)[i] + φ (twiddle j s) * (highHalf m)[i])[i] + (highHalf m)[i]) =
          Vector.ofFn fun i ↦ (lowHalf m)[i] + (φ (twiddle j s) + 1) * (highHalf m)[i] := by
        ext i hi
        simp only [Vector.getElem_ofFn, Fin.getElem_fin]
        ring
      rw [hb, novelEval_ofFn_add_mul]
      simp only [Fin.getElem_fin, Vector.ofFn_getElem]

/-- **The encoder by the transform**: the encoding on `2 ^ (κ + R)` positions, one transform per
coset `x_{c 2^κ} + U_κ`. -/
def encodeFast (κ R : ℕ) (m : Vector S (2 ^ κ)) : Vector S (2 ^ (κ + R)) :=
  let cosets : Vector (Vector S (2 ^ κ)) (2 ^ R) :=
    Vector.ofFn fun c ↦ fwd φ κ m (domainPt (c.val * 2 ^ κ))
  Vector.ofFn fun y ↦
    (cosets[y.val / 2 ^ κ]'(Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact y.isLt)))[y.val % 2 ^ κ]'
      (Nat.mod_lt _ (Nat.two_pow_pos κ))

/-- The encoder is the novel-basis polynomial on the domain. -/
theorem encode_eq_novelEval {κ R : ℕ} (m : CMlPolynomialEval S κ) (y : Fin (2 ^ (κ + R))) :
    encode φ κ R m y = novelEval φ κ m (domainPt y) := by
  rw [encode_eq_sum]
  rfl

/-- The fast encoder is the encoder, on `κ + R ≤ 64` variables. -/
theorem encodeFast_getElem {κ R : ℕ} (hb : κ + R ≤ 64) (m : CMlPolynomialEval S κ)
    (y : Fin (2 ^ (κ + R))) : (encodeFast φ κ R m)[y] = encode φ κ R m y := by
  simp only [encodeFast, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [fwd_getElem φ κ (by omega) _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos κ)),
    ← domainPt_add_mul (Nat.mod_lt _ (Nat.two_pow_pos κ)), Nat.mod_add_div' (y : ℕ) (2 ^ κ),
    encode_eq_sum]
  rfl

end Transform

end

end LeanerVM.Protocol
