/-
  LeanerVM.Protocol.ToCompPoly.EqBatch

  A combination of Lagrange bases `Σ_j c_j · eq(z_j, ·)` computed coordinate by coordinate, the
  terms whose factor at a coordinate is zero dropped there. Candidate for CompPoly.
-/

module

public import LeanerVM.Protocol.ToCompPoly.BitProductTable

/-!
# Combinations of equality kernels

`Σ_j c_j · eq(z_j, x)` over the cube, built from the `2 ^ n`-entry Lagrange bases, takes `J · 2 ^ n`
products. Points read through a layout have Boolean coordinates, the selector bits of a block,
where `eq(z_j, ·)` vanishes off one half of the cube. `eqBatch` splits the cube at its top
coordinate, passes each term to the half where its factor is not zero, scaled by the factor (no
product when it is `1`), and adds the surviving coefficients at the leaves (`eqBatch_getElem`):
its work is the terms' supports, not `J · 2 ^ n`.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {F : Type*} [Field F] [DecidableEq F]

/-- `c · f`, nothing when `f` is `0`, no product when `f` is `1`. -/
def scaleBy (c f : F) : Option F :=
  if f = 0 then none else if f = 1 then some c else some (c * f)

/-- `scaleBy` is the product, nothing standing for `0`. -/
theorem getD_scaleBy (c f : F) : (scaleBy c f).getD 0 = c * f := by
  unfold scaleBy
  split_ifs with h0 h1
  · simp [h0]
  · simp [h1]
  · rfl

/-- The terms on the half of the cube where the top coordinate is `b`: each scaled by its factor
there, the top coordinate dropped. -/
def splitTerms {m : ℕ} (b : Bool) (ts : List (F × Vector F (m + 1))) : List (F × Vector F m) :=
  ts.filterMap fun t ↦ (scaleBy t.1 (if b then t.2[m] else 1 - t.2[m])).map fun c ↦ (c, t.2.pop)

/-- Two halves joined, the first at the low indices. -/
def appendHalves {m : ℕ} (a b : CMlPolynomialEval F m) : CMlPolynomialEval F (m + 1) :=
  (a ++ b).cast (by rw [pow_succ]; omega)

/-- **The combination of equality kernels**, coordinate by coordinate. -/
def eqBatch : (m : ℕ) → List (F × Vector F m) → CMlPolynomialEval F m
  | 0, ts => #v[(ts.map Prod.fst).sum]
  | m + 1, ts =>
    match ts with
    | [] => Vector.replicate _ 0
    | _ :: _ => appendHalves (eqBatch m (splitTerms false ts)) (eqBatch m (splitTerms true ts))

omit [DecidableEq F] in
/-- The Lagrange basis below the top coordinate: the factor `1 - z_m` times the basis of the
rest. -/
private theorem lagrangeBasis_low {m : ℕ} (z : Vector F (m + 1)) {x : ℕ} (hx : x < 2 ^ m) :
    (lagrangeBasis z)[x]'(by rw [pow_succ]; omega) = (1 - z[m]) * (lagrangeBasis z.pop)[x] := by
  rw [lagrangeBasis_getElem_nat z (by rw [pow_succ]; omega), lagrangeBasis_getElem_nat _ hx,
    Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Nat.testBit_lt_two_pow hx, Bool.false_eq_true,
    ite_false, Fin.getElem_fin, Vector.getElem_pop']
  exact mul_comm _ _

omit [DecidableEq F] in
/-- The Lagrange basis above: the factor `z_m` times the basis of the rest. -/
private theorem lagrangeBasis_high {m : ℕ} (z : Vector F (m + 1)) {x : ℕ} (hx : x < 2 ^ m) :
    (lagrangeBasis z)[x + 2 ^ m]'(by rw [pow_succ]; omega) = z[m] * (lagrangeBasis z.pop)[x] := by
  rw [lagrangeBasis_getElem_nat z (by rw [pow_succ]; omega), lagrangeBasis_getElem_nat _ hx,
    Fin.prod_univ_castSucc]
  have htop : (x + 2 ^ m).testBit m = true := by
    rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hx]
    rfl
  have hlow : ∀ k : Fin m, (x + 2 ^ m).testBit k = x.testBit k := fun k ↦ by
    rw [Nat.add_comm, Nat.testBit_two_pow_add_gt k.isLt]
  simp only [Fin.val_castSucc, Fin.val_last, htop, hlow, ite_true, Fin.getElem_fin,
    Vector.getElem_pop']
  exact mul_comm _ _

/-- The terms of a half: the sum over the surviving terms is the sum over all, each scaled by its
factor. -/
private theorem sum_splitTerms {m : ℕ} (b : Bool) (ts : List (F × Vector F (m + 1)))
    (g : Vector F m → F) :
    ((splitTerms b ts).map fun t ↦ t.1 * g t.2).sum =
      (ts.map fun t ↦ t.1 * (if b then t.2[m] else (1 : F) - t.2[m]) * g t.2.pop).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have h := getD_scaleBy t.1 (if b then t.2[m] else (1 : F) - t.2[m])
    rw [List.map_cons, List.sum_cons, ← ih]
    cases hs : scaleBy t.1 (if b then t.2[m] else (1 : F) - t.2[m]) with
    | none =>
      rw [hs, Option.getD_none] at h
      simp only [splitTerms, List.filterMap_cons, hs, Option.map_none]
      rw [← h, zero_mul, zero_add]
    | some c =>
      rw [hs, Option.getD_some] at h
      simp only [splitTerms, List.filterMap_cons, hs, Option.map_some, List.map_cons,
        List.sum_cons, h]

/-- **`eqBatch` is the combination of the terms' Lagrange bases.** -/
theorem eqBatch_getElem : ∀ (m : ℕ) (ts : List (F × Vector F m)) (x : ℕ) (hx : x < 2 ^ m),
    (eqBatch m ts)[x] = (ts.map fun t ↦ t.1 * (lagrangeBasis t.2)[x]).sum
  | 0, ts, x, hx => by
    obtain rfl : x = 0 := by simpa using hx
    have h1 : ∀ z : Vector F 0, (lagrangeBasis z)[0] = 1 := fun z ↦ by
      rw [lagrangeBasis_getElem_nat z (by simp)]
      simp
    simp only [eqBatch, h1, mul_one]
    rfl
  | m + 1, [], x, hx => by simp [eqBatch]
  | m + 1, t :: ts, x, hx => by
    simp only [eqBatch, appendHalves, Vector.getElem_cast, Vector.getElem_append]
    split
    · rename_i h
      rw [eqBatch_getElem m _ x h, sum_splitTerms false (t :: ts) fun v ↦ (lagrangeBasis v)[x]]
      refine congrArg List.sum (List.map_congr_left fun u _ ↦ ?_)
      rw [lagrangeBasis_low u.2 h]
      simp only [Bool.false_eq_true, ite_false]
      ring
    · rename_i h
      have hx' : x - 2 ^ m < 2 ^ m := by rw [pow_succ] at hx; omega
      rw [eqBatch_getElem m _ (x - 2 ^ m) hx',
        sum_splitTerms true (t :: ts) fun v ↦ (lagrangeBasis v)[x - 2 ^ m]]
      refine congrArg List.sum (List.map_congr_left fun u _ ↦ ?_)
      have hu : (lagrangeBasis u.2)[x] = u.2[m] * (lagrangeBasis u.2.pop)[x - 2 ^ m] := by
        have := lagrangeBasis_high u.2 hx'
        simp only [Nat.sub_add_cancel (by omega : 2 ^ m ≤ x)] at this
        exact this
      rw [hu]
      simp only [ite_true]
      ring

end

end LeanerVM.Protocol
