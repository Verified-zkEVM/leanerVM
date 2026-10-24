/-
  LeanerVM.Protocol.Whir.QueryWords

  The query batch's weight values on words: each column weight's values over `K`, combined limb
  by limb with the limbs of the batching powers. Proved to be the batch of the column weights.
-/

module

public import LeanerVM.Protocol.Whir.TransformWords
public import LeanerVM.Protocol.ToArkLib.WeightBatch

/-!
# The query weight on words

The weight of a query batch is `Σ_q λ^q W_{y_q}`, each column weight `W_y(u) = ∏_k Ŵ_k(x_y)^{u_k}`
a product of elements of `K`. Over `E` its values take `2 ^ κ` products of `E` a column and `t`
more an entry. Its values lie in `K` (`columnWeight_onCube_eq_map`), so the batch's limb `l` at
`u` is `Σ_q (λ^q)_l · W_{y_q}(u)`, a sum of products in `K`: `queryCubeW` computes each column's
values over `K` once and these sums on the machine words (`dotW`), and is the batch
(`queryCubeW_eq`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly FastBF64

@[expose] public section

namespace Whir

/-- The values of the column weight at `y`, over `K`, its `κ` factors computed once. -/
private def columnTableK (κ R : ℕ) (v : Fin (2 ^ (κ + R))) : CMlPolynomialEval K κ :=
  let w := Vector.ofFn fun k : Fin κ ↦ normW k (domainPt v)
  bitProductTable fun k b ↦ if b then w[k] else 1

/-- The column weight's values are those over `K`, embedded. -/
private theorem columnWeight_onCube_eq_map (κ R : ℕ) (v : Fin (2 ^ (κ + R))) :
    (columnWeight (algebraMap K E) κ R v).onCube = Vector.map ofK (columnTableK κ R v) := by
  rw [columnWeight_onCube]
  refine Vector.ext fun i hi ↦ ?_
  simp only [Vector.getElem_map, columnTableK, bitProductTable_getElem, Fin.getElem_fin,
    Vector.getElem_ofFn]
  change _ = algebraMap K E _
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  split <;> simp

/-- `Σ_q p_q · c_q` on words: the `xor` of the `mulWord`s. -/
private def dotW {t : ℕ} (p : Vector UInt64 t) (c : Fin t → UInt64) : UInt64 :=
  Fin.foldl t (fun acc q ↦ acc ^^^ mulWord p[q] (c q)) 0

/-- `dotW` is the dot product. -/
private theorem ofWord_dotW {t : ℕ} (p : Vector UInt64 t) (c : Fin t → UInt64) :
    ofWord (dotW p c) = ∑ q, ofWord p[q] * ofWord (c q) := by
  rw [dotW, ofWord_foldl_xor]
  simp only [ofWord_mulWord]
  exact zero_add _

/-- **The query batch's values on words**: each column's values over `K` once, the batch limb by
limb. -/
@[no_expose] def queryCubeW (κ R : ℕ) {t : ℕ} (pos : Fin t → Fin (2 ^ (κ + R))) (lam : E) :
    CMlPolynomialEval E κ :=
  let cs : Vector (Vector UInt64 (2 ^ κ)) t :=
    Vector.ofFn fun q ↦ Vector.map toWord (columnTableK κ R (pos q))
  let pw : Vector E t := Vector.ofFn fun q ↦ lam ^ q.val
  let pl : Vector (Vector UInt64 t) 3 := Vector.ofFn fun l ↦ pw.map fun x ↦ toWord (x.limb l)
  Vector.ofFn fun u ↦
    E.ofLimbs (ofWord (dotW pl[0] fun q ↦ cs[q][u])) (ofWord (dotW pl[1] fun q ↦ cs[q][u]))
      (ofWord (dotW pl[2] fun q ↦ cs[q][u]))

/-- The values on words are the batch of the column weights. -/
theorem queryCubeW_eq (κ R : ℕ) {t : ℕ} (pos : Fin t → Fin (2 ^ (κ + R))) (lam : E) :
    queryCubeW κ R pos lam =
      batchWeight (fun q ↦ (columnWeight (algebraMap K E) κ R (pos q)).onCube) lam := by
  refine Vector.ext fun u hu ↦ ?_
  have key : ∀ l : Fin 3,
      ofWord (dotW (Vector.ofFn fun q : Fin t ↦ toWord ((lam ^ q.val).limb l))
        fun q ↦ toWord (columnTableK κ R (pos q))[u]) =
      (∑ q : Fin t,
        (columnWeight (algebraMap K E) κ R (pos q)).onCube[u] * lam ^ q.val).limb l := by
    intro l
    rw [ofWord_dotW, limb_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [columnWeight_onCube_eq_map, Vector.getElem_map, limb_ofK_mul]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, ofWord_toWord]
    exact mul_comm _ _
  simp only [queryCubeW, batchWeight, powerBatch, Vector.getElem_ofFn, Vector.map_ofFn,
    Function.comp_def, Fin.getElem_fin, Vector.getElem_map, key]
  exact ofLimbs_limb _

end Whir

end

end LeanerVM.Protocol
