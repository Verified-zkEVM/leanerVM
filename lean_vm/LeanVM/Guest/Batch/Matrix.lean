/-
  LeanVM.Guest.Batch.Matrix

  The matrices' batching sumcheck: the polynomial it sums over the cube, and that sum.
-/

module

public import LeanVM.Guest.Batch.Cube
public import LeanVM.Spec.Node
public import LeanVM.Protocol.EndToEnd.Front.WalkFaithful

/-!
# The matrices' batching

`batch` combines the children's claims on flock's matrices `A0`, `B0` with the lambdas `lM`, one
triple per child (its proof's claim `e_rowᵀ (A0 + α B0) w_col`, its statement's two values at a
point), and runs a sumcheck of `matrixPoly` over the cube of `2 · blake2sR1csLogSize = 28`
coordinates: the matrices' multilinear extensions (`matrixValues`, the row coordinates first)
times the weights `matrixWeightA` and `matrixWeightB`. Its cube sum is the lambdas' combination of
the true values (`matrix_cubeSum`), and it is quadratic along each coordinate
(`matrix_quadraticIn`). Both rest on the forward walk computing the R1CS's products
(`walkFaithful_blake2sFlockSpec`), so that `matrixValues` is multilinear and a cube sum against a
proof's weights is its bilinear form.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- The batched weight of `A0` at `z`. -/
def matrixWeightA (cs : List ChildClaims) (lM : List (E × E × E)) (z : List E) : E :=
  sumE (List.zipWith (fun c l ↦
    l.1 * freshWeight c.fresh z + l.2.1 * eqEval c.carried.matrixPoint z) cs lM)

/-- The batched weight of `B0` at `z`. -/
def matrixWeightB (cs : List ChildClaims) (lM : List (E × E × E)) (z : List E) : E :=
  sumE (List.zipWith (fun c l ↦
    l.1 * c.fresh.alpha * freshWeight c.fresh z + l.2.2 * eqEval c.carried.matrixPoint z) cs lM)

/-- **The polynomial the matrices' batching sums**: each matrix's multilinear extension times its
batched weight. -/
def matrixPoly (cs : List ChildClaims) (lM : List (E × E × E)) (z : List E) : E :=
  (matrixValues z).1 * matrixWeightA cs lM z + (matrixValues z).2 * matrixWeightB cs lM z

/-- The lambdas' combination of the matrices' true values: a proof's bilinear form, a statement's
values at its point. -/
def matrixTrue (cs : List ChildClaims) (lM : List (E × E × E)) : E :=
  sumE (List.zipWith (fun c l ↦
    l.1 * blake2sBilinear c.fresh.alpha (lincheckRowWeights c.fresh.zSkip c.fresh.rowPoint)
        (lincheckColumnWeights c.fresh.columnPoint c.fresh.slices) +
      l.2.1 * (matrixValues c.carried.matrixPoint).1 +
      l.2.2 * (matrixValues c.carried.matrixPoint).2) cs lM)

/-- The shapes the matrices' identities need: a proof's lincheck points of 8 coordinates and its
64 slices, a statement's point of `2 · blake2sR1csLogSize` coordinates. -/
def MatrixShaped (c : ChildClaims) : Prop :=
  c.fresh.rowPoint.length = 8 ∧ c.fresh.columnPoint.length = 8 ∧ c.fresh.slices.length = 64 ∧
    c.carried.matrixPoint.length = 2 * blake2sR1csLogSize

open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Complete Finset

/-! ## The matrices as linear maps -/

/-- An entry of a matrix on the block's positions, `0` off the block. -/
def matEntry (M : Fin (2 ^ (Flock.kSkip + Flock.kIn)) → Fin (2 ^ (Flock.kSkip + Flock.kIn)) → Bool)
    (r c : ℕ) : E :=
  if h : r < 2 ^ 14 ∧ c < 2 ^ 14 then (if M ⟨r, h.1⟩ ⟨c, h.2⟩ then 1 else 0) else 0

/-- `T` maps tables of `2^14` entries to tables of `2^14` entries by the matrix `a`. -/
def RowLinear (a : ℕ → ℕ → E) (T : List E → List E) : Prop :=
  ∀ w : List E, w.length = 2 ^ 14 → (T w).length = 2 ^ 14 ∧
    ∀ k < 2 ^ 14, (T w).getD k 0 = ∑ j ∈ range (2 ^ 14), a k j * w.getD j 0

/-- The walk's left product is `A0`'s. -/
theorem rowLinear_fst :
    RowLinear (matEntry Blake2sFlock.blake2sFlockSpec.r1cs.A)
      fun w ↦ (blake2sRowValues w).1.toList := by
  intro w hw
  have h := (Front.walkFaithful_blake2sFlockSpec w hw).1
  refine ⟨by simp only [h, List.length_ofFn]; rfl, fun k hk ↦ ?_⟩
  simp only [h]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk), List.getElem_ofFn,
    BlockR1CS.rows_fst, ← Fin.sum_univ_eq_sum_range (fun j ↦ matEntry _ k j * w.getD j 0)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj : (j : ℕ) < 2 ^ 14 := j.isLt
  simp only [matEntry, hk, hj, and_self, ↓reduceDIte]
  split <;> simp [Front.toVec]

/-- The walk's right product is `B0`'s. -/
theorem rowLinear_snd :
    RowLinear (matEntry Blake2sFlock.blake2sFlockSpec.r1cs.B)
      fun w ↦ (blake2sRowValues w).2.toList := by
  intro w hw
  have h := (Front.walkFaithful_blake2sFlockSpec w hw).2
  refine ⟨by simp only [h, List.length_ofFn]; rfl, fun k hk ↦ ?_⟩
  simp only [h]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk), List.getElem_ofFn,
    BlockR1CS.rows_snd, ← Fin.sum_univ_eq_sum_range (fun j ↦ matEntry _ k j * w.getD j 0)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj : (j : ℕ) < 2 ^ 14 := j.isLt
  simp only [matEntry, hk, hj, and_self, ↓reduceDIte]
  split <;> simp [Front.toVec]

/-! ## Cube points -/

/-- The kernel's weight at an index is the equality weight of the index's cube point. -/
private theorem eqKernel_getD_eqEval {m : ℕ} {q : List E} (hq : q.length = m) {c : ℕ}
    (hc : c < 2 ^ m) :
    (eqKernel q).getD c 0 = eqEval (boolPoint m c) q := by
  rw [List.getD_eq_getElem _ _ (by rw [Front.length_eqKernel, hq]; exact hc),
    Front.eqKernel_getElem, EndToEnd.Complete.eqEval_eq_prod_range _ _ m (length_boolPoint m c) hq,
    hq]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  rw [show (boolPoint m c).getD j 0 = if c.testBit j then 1 else 0 by
    simp [boolPoint, List.getD_eq_getElem?_getD, hj']]
  split
  · rw [one_add_one_E, zero_add]
  · rw [add_zero]

/-- The equality weight of two cube points is the indicator of their equality. -/
private theorem eqEval_boolPoint_boolPoint : ∀ (m i j : ℕ), i < 2 ^ m → j < 2 ^ m →
    eqEval (boolPoint m i) (boolPoint m j) = if i = j then 1 else 0
  | 0, i, j, hi, hj => by
    obtain rfl : i = 0 := by simpa using hi
    obtain rfl : j = 0 := by simpa using hj
    simp
  | m + 1, i, j, hi, hj => by
    rw [pow_succ] at hi hj
    rw [boolPoint_succ, boolPoint_succ, eqEval_cons,
      eqEval_boolPoint_boolPoint m (i / 2) (j / 2) (by omega) (by omega)]
    by_cases hij : i = j
    · subst hij
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;>
        simp [h, Nat.testBit_zero, one_add_one_E]
    · by_cases hh : i / 2 = j / 2
      · have hb : i % 2 ≠ j % 2 := fun hb ↦ hij (by omega)
        simp only [hh, ↓reduceIte, mul_one, hij, Nat.testBit_zero]
        rcases Nat.mod_two_eq_zero_or_one i with h1 | h1 <;>
          rcases Nat.mod_two_eq_zero_or_one j with h2 | h2 <;>
          simp_all [one_add_one_E]
      · simp [hh, hij]

/-- A sum over `2^(a+b)` indices, by the low `a` bits and the high `b` bits. -/
private theorem sum_range_two_pow_add (a b : ℕ) (f : ℕ → E) :
    ∑ y ∈ range (2 ^ (a + b)), f y =
      ∑ c ∈ range (2 ^ b), ∑ r ∈ range (2 ^ a), f (r + 2 ^ a * c) := by
  rw [pow_add]
  induction 2 ^ b with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    exact congrArg _ (Finset.sum_congr rfl fun r _ ↦ by rw [add_comm])

/-- A sum over the cube of `28` coordinates, by the row and the column halves. -/
private theorem sum_cube_split (F : List E → E) :
    ∑ y ∈ range (2 ^ (14 + 14)), F (boolPoint (14 + 14) y) =
      ∑ c ∈ range (2 ^ 14), ∑ r ∈ range (2 ^ 14), F (boolPoint 14 r ++ boolPoint 14 c) := by
  rw [sum_range_two_pow_add]
  exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun r hr ↦ by
    rw [boolPoint_add 14 14 r c (Finset.mem_range.mp hr)]

/-! ## The matrices' extensions -/

/-- The extension of the matrix `T` maps by: `T` of the column's kernel, at the row. -/
def matrixExt (T : List E → List E) (z : List E) : E :=
  multilinearEval (T (eqKernel (z.drop 14))) (z.take 14)

/-- `A0`'s extension is the left product's. -/
theorem matrixValues_fst (z : List E) :
    (matrixValues z).1 = matrixExt (fun w ↦ (blake2sRowValues w).1.toList) z := by
  unfold matrixValues matrixExt
  rw [show blake2sR1csLogSize = 14 from rfl]

/-- `B0`'s extension is the right product's. -/
theorem matrixValues_snd (z : List E) :
    (matrixValues z).2 = matrixExt (fun w ↦ (blake2sRowValues w).2.toList) z := by
  unfold matrixValues matrixExt
  rw [show blake2sR1csLogSize = 14 from rfl]

/-- The bilinear form, the pair unfolded. -/
theorem blake2sBilinear_eq (a : E) (u v : List E) : blake2sBilinear a u v =
    dot u (blake2sRowValues v).1.toList + a * dot u (blake2sRowValues v).2.toList := by
  unfold blake2sBilinear
  generalize blake2sRowValues v = p
  cases p
  rfl

/-- The fresh weight, the halves at `14` coordinates. -/
theorem freshWeight_eq (c : FixedClaims) (z : List E) : freshWeight c z =
    multilinearEval (lincheckRowWeights c.zSkip c.rowPoint) (z.take 14) *
      multilinearEval (lincheckColumnWeights c.columnPoint c.slices) (z.drop 14) := rfl

variable {a : ℕ → ℕ → E} {T : List E → List E}

/-- **The extension in closed form**: the matrix's entries against the two halves' equality
weights. -/
theorem matrixExt_eq_sum (hT : RowLinear a T) {z : List E} (hz : z.length = 14 + 14) :
    matrixExt T z = ∑ r ∈ range (2 ^ 14), ∑ c ∈ range (2 ^ 14),
      a r c * (eqEval (boolPoint 14 r) (z.take 14) * eqEval (boolPoint 14 c) (z.drop 14)) := by
  have hd : (z.drop 14).length = 14 := by simp [hz]
  have hK : (eqKernel (z.drop 14)).length = 2 ^ 14 := by rw [Front.length_eqKernel, hd]
  obtain ⟨hlen, hget⟩ := hT _ hK
  rw [matrixExt, multilinearEval_eq_sum 14 _ _ hlen (by simp [hz])]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  rw [hget r (Finset.mem_range.mp hr), Finset.sum_mul]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [eqKernel_getD_eqEval hd (Finset.mem_range.mp hc)]
  ring

/-- A finite sum of multilinear functions is multilinear. -/
private theorem multilinear_finsetSum {ι : Type} {n : ℕ} (s : Finset ι) {g : ι → List E → E}
    (hg : ∀ i ∈ s, Multilinear n (g i)) : Multilinear n fun y ↦ ∑ i ∈ s, g i y := by
  intro pre post h x
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi ↦ hg i hi pre post h x

/-- Multilinearity reads only the points of `n` coordinates. -/
private theorem Multilinear.congr {n : ℕ} {f g : List E → E} (hf : Multilinear n f)
    (h : ∀ z : List E, z.length = n → g z = f z) : Multilinear n g := by
  intro pre post hl x
  have hlen : ∀ y : E, (pre ++ y :: post).length = n := fun y ↦ by simp; omega
  rw [h _ (hlen x), h _ (hlen 0), h _ (hlen 1)]
  exact hf pre post hl x

/-- The extension is multilinear. -/
theorem multilinear_matrixExt (hT : RowLinear a T) : Multilinear (14 + 14) (matrixExt T) := by
  refine Multilinear.congr ?_ fun z hz ↦ matrixExt_eq_sum hT hz
  refine multilinear_finsetSum _ fun r _ ↦ multilinear_finsetSum _ fun c _ ↦ ?_
  exact Multilinear.const_mul _ (multilinear_take_mul_drop
    (multilinear_eqEval (length_boolPoint 14 r)) (multilinear_eqEval (length_boolPoint 14 c)))

/-- The row half of a cube point. -/
theorem take_boolPoint_append (r c : ℕ) :
    (boolPoint 14 r ++ boolPoint 14 c).take 14 = boolPoint 14 r :=
  List.take_left' (length_boolPoint 14 r)

/-- The column half of a cube point. -/
theorem drop_boolPoint_append (r c : ℕ) :
    (boolPoint 14 r ++ boolPoint 14 c).drop 14 = boolPoint 14 c :=
  List.drop_left' (length_boolPoint 14 r)

/-- At a cube point, the extension is the matrix's entry. -/
theorem matrixExt_boolPoint (hT : RowLinear a T) {r c : ℕ} (hr : r < 2 ^ 14) (hc : c < 2 ^ 14) :
    matrixExt T (boolPoint 14 r ++ boolPoint 14 c) = a r c := by
  rw [matrixExt_eq_sum hT (by simp [length_boolPoint]), take_boolPoint_append,
    drop_boolPoint_append, Finset.sum_eq_single r, Finset.sum_eq_single c]
  · rw [eqEval_boolPoint_boolPoint 14 r r hr hr, eqEval_boolPoint_boolPoint 14 c c hc hc]
    simp
  · intro c' hc' hne
    rw [eqEval_boolPoint_boolPoint 14 c' c (Finset.mem_range.mp hc') hc]
    simp [hne]
  · exact fun h ↦ absurd (Finset.mem_range.mpr hc) h
  · intro r' hr' hne
    refine Finset.sum_eq_zero fun c' _ ↦ ?_
    rw [eqEval_boolPoint_boolPoint 14 r' r (Finset.mem_range.mp hr') hr]
    simp [hne]
  · exact fun h ↦ absurd (Finset.mem_range.mpr hr) h

/-- **The cube sum against a proof's weights is the bilinear form.** -/
theorem sum_matrixExt_mul_tensor (hT : RowLinear a T) {u v : List E} (hu : u.length = 2 ^ 14)
    (hv : v.length = 2 ^ 14) :
    ∑ y ∈ range (2 ^ (14 + 14)), matrixExt T (boolPoint (14 + 14) y) *
      (multilinearEval u ((boolPoint (14 + 14) y).take 14) *
        multilinearEval v ((boolPoint (14 + 14) y).drop 14)) = dot u (T v) := by
  refine (sum_cube_split fun z ↦
    matrixExt T z * (multilinearEval u (z.take 14) * multilinearEval v (z.drop 14))).trans ?_
  obtain ⟨hlen, hget⟩ := hT v hv
  rw [Whir.Complete.dot_eq_sum u (T v) (by rw [hu, hlen]), hu]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun r hr ↦ ?_)
  rw [hget r (Finset.mem_range.mp hr), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  have hr' := Finset.mem_range.mp hr
  have hc' := Finset.mem_range.mp hc
  rw [matrixExt_boolPoint hT hr' hc', take_boolPoint_append, drop_boolPoint_append,
    EndToEnd.Complete.multilinearEval_boolPoint_getD 14 u r hu hr',
    EndToEnd.Complete.multilinearEval_boolPoint_getD 14 v c hv hc']
  ring

/-- **The cube sum against a point's equality weight is the extension there.** -/
theorem sum_matrixExt_mul_eqEval (hT : RowLinear a T) {p : List E} (hp : p.length = 14 + 14) :
    ∑ y ∈ range (2 ^ (14 + 14)), matrixExt T (boolPoint (14 + 14) y) *
      eqEval p (boolPoint (14 + 14) y) = matrixExt T p := by
  refine (sum_cube_split fun z ↦ matrixExt T z * eqEval p z).trans ?_
  rw [matrixExt_eq_sum hT hp]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun r hr ↦ Finset.sum_congr rfl fun c hc ↦ ?_)
  have he : eqEval p (boolPoint 14 r ++ boolPoint 14 c) =
      eqEval (p.take 14) (boolPoint 14 r) * eqEval (p.drop 14) (boolPoint 14 c) := by
    conv_lhs => rw [← List.take_append_drop 14 p]
    exact eqEval_append _ _ _ _ (by simp [hp, length_boolPoint])
  rw [he, matrixExt_boolPoint hT (Finset.mem_range.mp hr) (Finset.mem_range.mp hc),
    eqEval_comm (p.take 14), eqEval_comm (p.drop 14)]

/-! ## The batched polynomial -/

/-- The batched polynomial peels its first child. -/
theorem matrixPoly_cons (ch : ChildClaims) (cs : List ChildClaims) (l : E × E × E)
    (lM : List (E × E × E)) (z : List E) :
    matrixPoly (ch :: cs) (l :: lM) z =
      (matrixValues z).1 *
          (l.1 * freshWeight ch.fresh z + l.2.1 * eqEval ch.carried.matrixPoint z) +
        (matrixValues z).2 * (l.1 * ch.fresh.alpha * freshWeight ch.fresh z +
          l.2.2 * eqEval ch.carried.matrixPoint z) + matrixPoly cs lM z := by
  simp only [matrixPoly, matrixWeightA, matrixWeightB, List.zipWith_cons_cons, sumE_eq,
    List.sum_cons]
  ring

/-- The true values' combination peels its first child. -/
theorem matrixTrue_cons (ch : ChildClaims) (cs : List ChildClaims) (l : E × E × E)
    (lM : List (E × E × E)) :
    matrixTrue (ch :: cs) (l :: lM) =
      l.1 * blake2sBilinear ch.fresh.alpha (lincheckRowWeights ch.fresh.zSkip ch.fresh.rowPoint)
          (lincheckColumnWeights ch.fresh.columnPoint ch.fresh.slices) +
        l.2.1 * (matrixValues ch.carried.matrixPoint).1 +
        l.2.2 * (matrixValues ch.carried.matrixPoint).2 + matrixTrue cs lM := by
  simp only [matrixTrue, List.zipWith_cons_cons, sumE_eq, List.sum_cons]

/-- The row weights of an 8-coordinate point have `2^14` entries. -/
theorem length_lincheckRowWeights {zSkip : E} {chi : List E} (h : chi.length = 8) :
    (lincheckRowWeights zSkip chi).length = 2 ^ 14 := by
  rw [lincheckRowWeights, Front.length_flatMap_map, Front.length_eqKernel,
    Front.length_lagrangeWeights, h]
  rfl

/-- The column weights of an 8-coordinate point and 64 slices have `2^14` entries. -/
theorem length_lincheckColumnWeights {chi s : List E} (h : chi.length = 8) (hs : s.length = 64) :
    (lincheckColumnWeights chi s).length = 2 ^ 14 := by
  rw [lincheckColumnWeights, Front.length_flatMap_map, Front.length_eqKernel, h, hs]
  norm_num

/-- A constant factor out of a sum. -/
private theorem sum_mul_const_mul (s : Finset ℕ) (c : E) (f g : ℕ → E) :
    ∑ i ∈ s, f i * (c * g i) = c * ∑ i ∈ s, f i * g i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- A sum over two lists zipped, of multilinear functions, is multilinear. -/
private theorem multilinear_sumE_zipWith {α β : Type} {n : ℕ} (l : List α) (m : List β)
    {g : α → β → List E → E} (hg : ∀ a ∈ l, ∀ b, Multilinear n (g a b)) :
    Multilinear n fun y ↦ sumE (List.zipWith (fun a b ↦ g a b y) l m) := by
  induction l generalizing m with
  | nil => intro pre post _ x; simp [sumE]
  | cons a l ih =>
    cases m with
    | nil => intro pre post _ x; simp [sumE]
    | cons b m =>
      refine ((hg a (by simp) b).add (ih m fun a' ha' ↦ hg a' (by simp [ha']))).congr
        fun z _ ↦ ?_
      simp only [List.zipWith_cons_cons, sumE_eq, List.sum_cons]

/-- A proof's weight is multilinear. -/
theorem multilinear_freshWeight {c : FixedClaims} (hrow : c.rowPoint.length = 8)
    (hcol : c.columnPoint.length = 8) (hsl : c.slices.length = 64) :
    Multilinear (14 + 14) (freshWeight c) :=
  multilinear_take_mul_drop (multilinear_multilinearEval (length_lincheckRowWeights hrow))
    (multilinear_multilinearEval (length_lincheckColumnWeights hcol hsl))

/-- **The cube sum is the true values' combination.** -/
theorem matrix_cubeSum {cs : List ChildClaims} (hs : ∀ c ∈ cs, MatrixShaped c)
    (lM : List (E × E × E)) :
    cubeSum (2 * blake2sR1csLogSize) (matrixPoly cs lM) [] = matrixTrue cs lM := by
  rw [show 2 * blake2sR1csLogSize = 14 + 14 from rfl]
  simp only [cubeSum, List.length_nil, Nat.sub_zero, List.nil_append]
  induction cs generalizing lM with
  | nil => simp [matrixPoly, matrixWeightA, matrixWeightB, matrixTrue, sumE]
  | cons ch cs ih =>
    cases lM with
    | nil => simp [matrixPoly, matrixWeightA, matrixWeightB, matrixTrue, sumE]
    | cons l lM =>
      obtain ⟨hrow, hcol, hsl, hmp⟩ := hs ch (by simp)
      simp only [matrixPoly_cons, Finset.sum_add_distrib, matrixTrue_cons]
      rw [ih (fun c hc ↦ hs c (by simp [hc])), add_left_inj]
      have hu := length_lincheckRowWeights (zSkip := ch.fresh.zSkip) hrow
      have hv := length_lincheckColumnWeights hcol hsl
      have hp : ch.carried.matrixPoint.length = 14 + 14 := hmp
      simp only [matrixValues_fst, matrixValues_snd, freshWeight_eq, blake2sBilinear_eq,
        mul_add, Finset.sum_add_distrib, sum_mul_const_mul]
      rw [sum_matrixExt_mul_tensor rowLinear_fst hu hv,
        sum_matrixExt_mul_tensor rowLinear_snd hu hv,
        sum_matrixExt_mul_eqEval rowLinear_fst hp, sum_matrixExt_mul_eqEval rowLinear_snd hp]
      ring

/-- The matrices' batched polynomial is quadratic along each coordinate. -/
theorem matrix_quadraticIn {cs : List ChildClaims} (hs : ∀ c ∈ cs, MatrixShaped c)
    (lM : List (E × E × E)) :
    QuadraticIn (2 * blake2sR1csLogSize) (matrixPoly cs lM) := by
  show QuadraticIn (14 + 14) fun z ↦
    (matrixValues z).1 * matrixWeightA cs lM z + (matrixValues z).2 * matrixWeightB cs lM z
  have h1 : Multilinear (14 + 14) fun z ↦ (matrixValues z).1 :=
    (multilinear_matrixExt rowLinear_fst).congr fun z _ ↦ matrixValues_fst z
  have h2 : Multilinear (14 + 14) fun z ↦ (matrixValues z).2 :=
    (multilinear_matrixExt rowLinear_snd).congr fun z _ ↦ matrixValues_snd z
  have hA : Multilinear (14 + 14) (matrixWeightA cs lM) :=
    multilinear_sumE_zipWith (g := fun c l z ↦
      l.1 * freshWeight c.fresh z + l.2.1 * eqEval c.carried.matrixPoint z) cs lM
      fun c hc l ↦ by
        obtain ⟨hrow, hcol, hsl, hmp⟩ := hs c hc
        exact ((multilinear_freshWeight hrow hcol hsl).const_mul l.1).add
          ((multilinear_eqEval hmp).const_mul l.2.1)
  have hB : Multilinear (14 + 14) (matrixWeightB cs lM) :=
    multilinear_sumE_zipWith (g := fun c l z ↦
      l.1 * c.fresh.alpha * freshWeight c.fresh z + l.2.2 * eqEval c.carried.matrixPoint z) cs lM
      fun c hc l ↦ by
        obtain ⟨hrow, hcol, hsl, hmp⟩ := hs c hc
        exact ((multilinear_freshWeight hrow hcol hsl).const_mul (l.1 * c.fresh.alpha)).add
          ((multilinear_eqEval hmp).const_mul l.2.2)
  exact (quadraticIn_mul h1 hA).add (quadraticIn_mul h2 hB)

end
end LeanVM.Guest.Batch
