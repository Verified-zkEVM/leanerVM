/-
  LeanerVM.Protocol.ToArkLib.Sumcheck

  The sumcheck of a virtual polynomial (a formula in the values of tables the verifier does not
  evaluate) over a weighted cube, binding the highest variable first, with the tables' values at
  the final point as its last message: the plain variant (unit weights) and the normalized one
  (the weights of an equality polynomial). Definition, perfect completeness, and the decoding of
  a round message sent without one coefficient. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.SumcheckRound
public import LeanerVM.Protocol.ToArkLib.TranscriptMap
public import LeanerVM.Protocol.ToCompPoly.IndividualDegree
public import LeanerVM.Protocol.ToCompPoly.WeightedCube
public import CompPoly.Univariate.Lagrange
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The sumcheck of a virtual polynomial

A *virtual polynomial* on `n` variables (`Virtual`) is `m` tables on the cube, read off the
public data, the oracles' contents and the witness, and a formula: the *summand* at a point `z`
is the formula at `z` and at the values of the tables' multilinear extensions there
(`Virtual.summand`). The verifier never evaluates a table; the formula it evaluates itself, so
factors such as an equality polynomial or a padding product belong to the formula. A weight per
coordinate (`CoordWeights`, the weights of the values `0` and `1`) weighs the cube, and the
claim is `Σ_x (∏_k w_k(x_k)) · summand(x) = T` (`relIn`), beside a side condition on the context
that the sumcheck carries unchanged, for a protocol that has more to say of its statement and
oracles than the claim. Two choices of weights:

* *plain* (`plain`, `unitWeights`): unit weights, the claim `Σ_x summand(x) = T`;
* *normalized* (`normalized`, `eqWeights pt`): the weights `(1 - p_k, p_k)` of a point `p` of the
  public data, the claim `Σ_x eq(p, x) · summand(x) = T`. The round message is then the cofactor
  of the equality factor, and the final check has none.

The sumcheck (`weighted`) binds the highest variable first. After `j` rounds the challenges
`c_0, …, c_{j-1}` hold the top `j` coordinates, `c_0` the highest (`point`), and the running
claim (`claim`) is the weighted sum, over the free coordinates only, of the summand at the point
they complete. Each round is `SumcheckRound.round`: the prover sends the `d + 1` coefficients of
the round polynomial, and the verifier checks `w_k(0) · q(0) + w_k(1) · q(1)` against the running
claim, `k` the coordinate the round binds (`domain`), and moves to `q(c)`. The honest round
polynomial (`roundPoly`) interpolates the next claim at `d + 1` distinct nodes (`nodes`, a
parameter: a field of characteristic two has no `0, 1, …, d`). The last message (`final`) is the
tables' values at the final point, the challenges in coordinate order; the verifier checks that
the formula at the point and the values is the running claim, and outputs them through an output
map, by default the point and the values as claims on the tables (`finalOut`, `relOut`).

Completeness (`weightedComplete`) holds when the summand has degree at most `d` in each variable
(`IndividualDegreeLE`): the round polynomial is then a polynomial of degree at most `d`, which
`d + 1` nodes determine.

*The wire.* A round sent with `d` of its `d + 1` coefficients (`wireSpec`, the coefficients but
coefficient `k`: `encodeWire`) is decoded by deriving the missing one from the running claim, the
value that makes the round's check hold (`decodeRound`, `decodeWire`); this needs the coefficient's
weight in the check, `Σ_x w(x) · x^k` (`coeffWeight`), to be invertible, which is why a plain round
drops `c_1` (the weight of `c_0` is `1 + 1`, zero in characteristic two) and a normalized round
`c_0`. The decoding is injective (`encodeWire_decodeWire`), and every message that passes the
check is the decoding of its wire (`decodeWire_encodeWire`), so the honest prover's message
survives. `transport`: the round's verifier composed with the decoding, a verifier of the wire,
is round-by-round knowledge sound at the round's error, with the extractor and the state function
read on the decoded transcript; it is `Verifier.rbrKnowledgeSoundnessWorstCaseWith_comap` on the
map that decodes the round's wire (`roundDecoding`).
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec
open scoped NNReal Polynomial

@[expose] public section

namespace Sumcheck

section Def

variable {F : Type} [Field F] {X : Type} {ι : Type} {O : ι → Type} {W : Type} {n m : ℕ}

/-! ## Virtual polynomials -/

/-- A virtual polynomial on `n` variables: `m` tables on the cube, read off the public data, the
oracles' contents and the witness, and a formula giving the summand at a point from the public
data, the point and the tables' values there. -/
structure Virtual (F X : Type) {ι : Type} (O : ι → Type) (W : Type) (n m : ℕ) [Field F] where
  /-- The tables. -/
  tables : SumcheckRound.Ctx X O W → Fin m → CMlPolynomialEval F n
  /-- The formula: the summand from the public data, the point and the tables' values. -/
  formula : X → Vector F n → Vector F m → F

namespace Virtual

variable (V : Virtual F X O W n m)

/-- The values of the tables' extensions at a point. -/
def values (ctx : SumcheckRound.Ctx X O W) (z : Vector F n) : Vector F m :=
  Vector.ofFn fun i ↦ evalMle (V.tables ctx i) z

/-- The summand at a point: the formula at the point and the tables' values there. -/
def summand (ctx : SumcheckRound.Ctx X O W) (z : Vector F n) : F :=
  V.formula ctx.1.1 z (V.values ctx z)

end Virtual

/-- The weights of the values `0` and `1` of each coordinate, from the public data. -/
abbrev CoordWeights (F X : Type) (n : ℕ) : Type := X → Fin n → F × F

/-- Unit weights: the plain sum over the cube. -/
def unitWeights : CoordWeights F X n := fun _ _ ↦ (1, 1)

/-- The weights `(1 - p_k, p_k)` of a point `p` of the public data: the sum against
`eq(p, ·)`. -/
def eqWeights (pt : X → Vector F n) : CoordWeights F X n := fun x k ↦ (1 - (pt x)[k], (pt x)[k])

/-- The weighted sum of the summand over the cube. -/
def weightedSum (V : Virtual F X O W n m) (wt : CoordWeights F X n)
    (ctx : SumcheckRound.Ctx X O W) : F :=
  weightedCubeSum (wt ctx.1.1) (V.summand ctx)

/-! ## The claims, highest variable first -/

/-- The point whose low `n - j` coordinates are `x` and whose top `j` are the challenges `c`, the
first challenge the highest coordinate. -/
def point {j : ℕ} (hj : j ≤ n) (c : Vector F j) (x : Vector F (n - j)) : Vector F n :=
  Vector.ofFn fun k ↦ if h : k.val < n - j then x[k.val] else c[n - 1 - k.val]'(by omega)

/-- The running claim after the challenges `c`: the weighted sum, over the free coordinates, of the
summand at the point they complete. -/
def claim (V : Virtual F X O W n m) (wt : CoordWeights F X n) (ctx : SumcheckRound.Ctx X O W)
    (j : ℕ) (c : Vector F j) : F :=
  if hj : j ≤ n then
    weightedCubeSum (fun a : Fin (n - j) ↦ wt ctx.1.1 ⟨a, by omega⟩)
      fun x ↦ V.summand ctx (point hj c x)
  else 0

/-- The verifier's domain at round `j`: the values `0` and `1` of coordinate `n - 1 - j`, with
their weights. -/
def domain (wt : CoordWeights F X n) : SumcheckRound.Weights F X := fun x j ↦
  if h : j < n then
    [(0, (wt x ⟨n - 1 - j, by omega⟩).1), (1, (wt x ⟨n - 1 - j, by omega⟩).2)]
  else []

variable [BEq F] [LawfulBEq F]

/-- The honest round polynomial at round `j`: the interpolation, at the nodes, of the next claim
with the round's coordinate at each node. -/
def roundPoly (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) : SumcheckRound.Polys F X O W d := fun ctx j c ↦
  if j < n then
    SumcheckRound.ofCPolynomial d (CPolynomial.CLagrange.interpolate Finset.univ nodes
      fun i ↦ claim V wt ctx (j + 1) (c.push (nodes i)))
  else SumcheckRound.ofCPolynomial d 0

/-- The family of claims of the sumcheck: the running claims, the honest round polynomials, the
domains, and the side condition on the context, which no challenge changes. -/
def family (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) (side : SumcheckRound.Ctx X O W → Prop) :
    SumcheckRound.Family F X O W d where
  claim := claim V wt
  poly := roundPoly V wt nodes
  weight := domain wt
  inv := fun ctx _ _ ↦ side ctx

/-! ## The relations -/

/-- The output statement: the public data, the final point, and one value per table. -/
abbrev Out (X F : Type) (n m : ℕ) : Type := X × (Vector F n × Vector F m)

/-- The input relation: the claimed sum is the weighted sum of the summand over the cube, and the
side condition holds of the context. -/
def relIn (V : Virtual F X O W n m) (wt : CoordWeights F X n)
    (side : SumcheckRound.Ctx X O W → Prop) : Set ((SumcheckRound.Stmt X F 0 × ∀ i, O i) × W) :=
  {p | p.1.1.2.2 = weightedSum V wt (SumcheckRound.ctxOf p) ∧ side (SumcheckRound.ctxOf p)}

/-- The output relation: each value is its table's extension at the point, and the side condition
holds of the context. -/
def relOut (V : Virtual F X O W n m) (side : SumcheckRound.Ctx X O W → Prop) :
    Set ((Out X F n m × ∀ i, O i) × W) :=
  {p | V.values ((p.1.1.1, p.1.2), p.2) p.1.1.2.1 = p.1.1.2.2 ∧ side ((p.1.1.1, p.1.2), p.2)}

/-! ## The components -/

variable [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)]

/-- The `n` rounds. -/
def rounds (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) :
    Component.Def (SumcheckRound.Stmt X F 0) O W (SumcheckRound.Stmt X F n) O W
      (roundsSpec F d n) :=
  SumcheckRound.rounds (roundPoly V wt nodes) (domain wt) n n 0 (Nat.zero_add n)

/-- The final check: the formula at the final point and the values sent is the running claim. -/
def finalCheck (V : Virtual F X O W n m) (s : SumcheckRound.Stmt X F n) (v : Vector F m) : Bool :=
  decide (V.formula s.1 s.2.1.reverse v = s.2.2)

/-- The default output: the final point, in coordinate order, and the values sent. -/
def finalOut (s : SumcheckRound.Stmt X F n) (v : Vector F m) : Out X F n m :=
  (s.1, (s.2.1.reverse, v))

/-- The last message: the prover sends the tables' values at the final point, the verifier checks
them against the running claim and outputs the statement `out` makes of them. -/
def final (V : Virtual F X O W n m) {T : Type} (out : SumcheckRound.Stmt X F n → Vector F m → T) :
    Component.Def (SumcheckRound.Stmt X F n) O W T O W (say (Vector F m)) :=
  Component.sendChecked O (Vector F m)
    (fun p ↦ V.values (SumcheckRound.ctxOf p) p.1.1.2.1.reverse) (finalCheck V) out

/-- The schedule: `n` rounds of degree `d`, then the `m` values. -/
abbrev spec (F : Type) (d n m : ℕ) : ProtocolSpec (roundsRounds n + 1) :=
  roundsSpec F d n ++ₚ say (Vector F m)

instance instOracleInterfaceSpec (d n m : ℕ) :
    ∀ i, OracleInterface ((spec F d n m).Message i) :=
  msgAppend (instOracleInterfaceRounds F d n) (instOracleInterfaceSay _)

instance instSampleableTypeSpec (d n m : ℕ) :
    ∀ i, SampleableType ((spec F d n m).Challenge i) :=
  chalAppend (instSampleableTypeRounds F d n) (instSampleableTypeSay _)

/-- The sumcheck over a weighted cube: the rounds, then the values. -/
def weighted (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) :
    Component.Def (SumcheckRound.Stmt X F 0) O W (Out X F n m) O W (spec F d n m) :=
  (rounds V wt nodes).append (final V finalOut)

/-- The plain sumcheck: `Σ_x summand(x) = T`. -/
abbrev plain (V : Virtual F X O W n m) {d : ℕ} (nodes : Fin (d + 1) → F) :
    Component.Def (SumcheckRound.Stmt X F 0) O W (Out X F n m) O W (spec F d n m) :=
  weighted V unitWeights nodes

/-- The normalized sumcheck: `Σ_x eq(p, x) · summand(x) = T`, `p` from the public data. -/
abbrev normalized (V : Virtual F X O W n m) (pt : X → Vector F n) {d : ℕ}
    (nodes : Fin (d + 1) → F) :
    Component.Def (SumcheckRound.Stmt X F 0) O W (Out X F n m) O W (spec F d n m) :=
  weighted V (eqWeights pt) nodes

/-- The rounds are front: their verifier reads the transcript, never the oracles. -/
def roundsFront (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) : Component.Front (rounds V wt nodes) :=
  SumcheckRound.roundsFront _ _ n n 0 _

/-- The last message is front. -/
def finalFront (V : Virtual F X O W n m) {T : Type}
    (out : SumcheckRound.Stmt X F n → Vector F m → T) :
    Component.Front (final (W := W) (O := O) V out) :=
  Component.sendCheckedFront _ _ _ _ _

/-- The sumcheck is front: its verifier reads the transcript, never the oracles. -/
def weightedFront (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) : Component.Front (weighted V wt nodes) :=
  (roundsFront V wt nodes).append (finalFront V finalOut)

end Def

section Complete

variable {F : Type} [Field F] {X : Type} {ι : Type} {O : ι → Type} {W : Type} {n m : ℕ}
  (V : Virtual F X O W n m) (wt : CoordWeights F X n)

/-! ## Points -/

omit [Field F] in
/-- One more challenge is one free coordinate fewer: the challenge takes the highest free
coordinate. -/
private theorem point_push {j : ℕ} (hj : j < n) (c : Vector F j) (x : F)
    (v : Vector F (n - (j + 1))) :
    point (Nat.succ_le_of_lt hj) (c.push x) v =
      point hj.le c (Vector.cast (by omega) (v.push x)) := by
  apply Vector.ext
  intro k hk
  simp only [point, Vector.getElem_ofFn, Vector.getElem_cast, Vector.getElem_push]
  by_cases h1 : k < n - (j + 1)
  · simp [h1, show k < n - j by omega]
  · by_cases h2 : k < n - j
    · have hk' : k = n - (j + 1) := by omega
      subst hk'
      have e1 : ¬ n - 1 - (n - (j + 1)) < j := by omega
      simp [e1, h2]
    · simp [h1, h2, show n - 1 - k < j by omega]

omit [Field F] in
/-- The coordinate the next challenge takes, set to `x`. -/
private theorem point_push_set {j : ℕ} (hj : j < n) (c : Vector F j) (x y : F)
    (v : Vector F (n - (j + 1))) :
    point (Nat.succ_le_of_lt hj) (c.push x) v =
      (point (Nat.succ_le_of_lt hj) (c.push y) v).set (n - 1 - j) x (by omega) := by
  apply Vector.ext
  intro k hk
  simp only [point, Vector.getElem_ofFn, Vector.getElem_set, Vector.getElem_push]
  by_cases h : n - 1 - j = k
  · simp [h.symm, show ¬ n - 1 - j < n - (j + 1) by omega, show n - 1 - (n - 1 - j) = j by omega]
  · simp only [h, ite_false]
    by_cases h1 : k < n - (j + 1)
    · simp [h1]
    · simp [h1, show n - 1 - k < j by omega]

omit [Field F] in
/-- With every coordinate bound, the point is the challenges in coordinate order. -/
private theorem point_self (c : Vector F n) (v : Vector F (n - n)) :
    point le_rfl c v = c.reverse := by
  apply Vector.ext
  intro k hk
  simp [point, Vector.getElem_reverse]

omit [Field F] in
/-- With no coordinate bound, the point is the free coordinates. -/
private theorem point_zero (v : Vector F (n - 0)) :
    point (Nat.zero_le n) (#v[] : Vector F 0) v = Vector.cast (Nat.sub_zero n) v := by
  apply Vector.ext
  intro k hk
  simp [point]

/-! ## The claims -/

/-- With no challenge, the claim is the weighted sum of the summand over the cube. -/
theorem claim_zero (ctx : SumcheckRound.Ctx X O W) :
    claim V wt ctx 0 #v[] = weightedSum V wt ctx := by
  rw [claim, dite_eq_left (Nat.zero_le n), weightedSum,
    weightedCubeSum_cast (Nat.sub_zero n)]
  congr 1
  funext v
  rw [point_zero]
  congr 1

/-- With every coordinate bound, the claim is the summand at the challenges in coordinate
order. -/
theorem claim_self (ctx : SumcheckRound.Ctx X O W) (c : Vector F n) :
    claim V wt ctx n c = V.summand ctx c.reverse := by
  rw [claim, dite_eq_left le_rfl, weightedCubeSum_cast (Nat.sub_self n), weightedCubeSum_zero,
    point_self]

/-- Binding one more coordinate: the claim is the next claims at `0` and at `1`, weighted by the
coordinate's weights. -/
private theorem claim_split {j : ℕ} (hj : j < n) (ctx : SumcheckRound.Ctx X O W) (c : Vector F j) :
    claim V wt ctx j c =
      (wt ctx.1.1 ⟨n - 1 - j, by omega⟩).1 * claim V wt ctx (j + 1) (c.push 0) +
        (wt ctx.1.1 ⟨n - 1 - j, by omega⟩).2 * claim V wt ctx (j + 1) (c.push 1) := by
  rw [claim, dite_eq_left hj.le, claim, dite_eq_left (Nat.succ_le_of_lt hj), claim,
    dite_eq_left (Nat.succ_le_of_lt hj),
    weightedCubeSum_cast (show n - j = n - (j + 1) + 1 by omega), weightedCubeSum_succ]
  have hw : (⟨(Fin.cast (show n - (j + 1) + 1 = n - j by omega) (Fin.last (n - (j + 1)))).val,
      by omega⟩ : Fin n) = ⟨n - 1 - j, by omega⟩ := Fin.ext (by simp; omega)
  simp only [hw]
  congr 2 <;> refine congrArg₂ (fun w g ↦ weightedCubeSum w g) rfl (funext fun v ↦ ?_) <;>
    rw [point_push hj]

/-- The next claim, as a function of the round's coordinate, is a polynomial of degree at most
`d` when the summand is. -/
private theorem exists_claim_poly {d : ℕ} (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d) {j : ℕ}
    (hj : j < n) (ctx : SumcheckRound.Ctx X O W) (c : Vector F j) :
    ∃ P : F[X], P.natDegree ≤ d ∧ ∀ x, claim V wt ctx (j + 1) (c.push x) = P.eval x := by
  have hle : j + 1 ≤ n := hj
  choose p hp hpe using fun v : Fin (2 ^ (n - (j + 1))) ↦
    hV ctx (n - 1 - j) (point hle (c.push 0) (boolVec v)) (by omega)
  refine ⟨∑ v, Polynomial.C (cubeWeight (fun a : Fin (n - (j + 1)) ↦ wt ctx.1.1 ⟨a, by omega⟩) v) *
    p v, ?_, fun x ↦ ?_⟩
  · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun v _ ↦
      (Polynomial.natDegree_C_mul_le _ _).trans (hp v)
  · rw [claim, dite_eq_left hle, weightedCubeSum, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [point_push_set hj c x 0, hpe, Polynomial.eval_C_mul]

variable [BEq F] [LawfulBEq F] {d : ℕ} (nodes : Fin (d + 1) → F)

/-- The honest round polynomial evaluates to the next claim: it interpolates, at `d + 1` distinct
nodes, a polynomial of degree at most `d`. -/
private theorem evaluate_roundPoly (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d)
    (hnodes : Function.Injective nodes) {j : ℕ} (hj : j < n) (ctx : SumcheckRound.Ctx X O W)
    (c : Vector F j) (x : F) :
    SumcheckRound.evaluate d (roundPoly V wt nodes ctx j c) x =
      claim V wt ctx (j + 1) (c.push x) := by
  obtain ⟨P, hP, hPe⟩ := exists_claim_poly V wt hV hj ctx c
  have hint : (CPolynomial.CLagrange.interpolate Finset.univ nodes
      fun i ↦ claim V wt ctx (j + 1) (c.push (nodes i))).toPoly = P := by
    rw [CPolynomial.CLagrange.cinterpolate_eq_interpolate]
    refine (Lagrange.eq_interpolate_of_eval_eq _ hnodes.injOn ?_ fun i _ ↦ (hPe _).symm).symm
    rw [Finset.card_univ, Fintype.card_fin]
    exact (Polynomial.degree_le_of_natDegree_le hP).trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))
  simp only [roundPoly, hj, ↓reduceIte]
  rw [SumcheckRound.evaluate_ofCPolynomial, CPolynomial.eval_toPoly, hint, hPe]
  rw [CPolynomial.degree_toPoly, hint]
  exact Polynomial.degree_le_of_natDegree_le hP

/-- The honest round polynomial passes the round's check. -/
private theorem weightedSum_roundPoly (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d)
    (hnodes : Function.Injective nodes) {j : ℕ} (hj : j < n) (ctx : SumcheckRound.Ctx X O W)
    (c : Vector F j) :
    SumcheckRound.weightedSum d (domain wt ctx.1.1 j) (roundPoly V wt nodes ctx j c) =
      claim V wt ctx j c := by
  simp only [domain, dite_eq_left hj, SumcheckRound.weightedSum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rw [evaluate_roundPoly V wt nodes hV hnodes hj, evaluate_roundPoly V wt nodes hV hnodes hj,
    claim_split V wt hj]

variable (side : SumcheckRound.Ctx X O W → Prop)

/-- The family is honest: its round polynomials pass the check and evaluate to the next claim, and
no challenge changes the side condition. -/
theorem family_honest (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d)
    (hnodes : Function.Injective nodes) : (family V wt nodes side).Honest n where
  check := fun ctx _ c hj ↦ weightedSum_roundPoly V wt nodes hV hnodes hj ctx c
  next := fun ctx _ c x hj ↦ evaluate_roundPoly V wt nodes hV hnodes hj ctx c x
  inv_push := fun _ _ _ _ _ h ↦ h

/-- The family's relation before the first round is the input relation. -/
theorem rel_zero : SumcheckRound.rel (family V wt nodes side) 0 = relIn V wt side := by
  ext p
  have hc : p.1.1.2.1 = #v[] := Vector.ext fun i hi ↦ absurd hi (Nat.not_lt_zero i)
  simp only [SumcheckRound.rel, family, relIn, Set.mem_ofPred_eq, hc]
  rw [claim_zero, and_comm]

/-- The family's relation after the last round: the side condition, and the running claim is the
summand at the challenges in coordinate order. -/
theorem mem_rel_self (p : (SumcheckRound.Stmt X F n × ∀ i, O i) × W) :
    p ∈ SumcheckRound.rel (family V wt nodes side) n ↔
      side (SumcheckRound.ctxOf p) ∧
        p.1.1.2.2 = V.summand (SumcheckRound.ctxOf p) p.1.1.2.1.reverse := by
  simp only [SumcheckRound.rel, family, Set.mem_ofPred_eq]
  rw [claim_self]

variable [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)]

/-- The completeness half of the rounds. -/
def roundsComplete (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d)
    (hnodes : Function.Injective nodes) :
    Component.Complete (rounds V wt nodes) (relIn V wt side)
      (SumcheckRound.rel (family V wt nodes side) n) :=
  rel_zero V wt nodes side ▸ SumcheckRound.roundsComplete (family V wt nodes side) n
    (family_honest V wt nodes side hV hnodes) n 0 (Nat.zero_add n)

/-- The completeness half of the last message, for an output map and an output relation that the
true values at the final point land in whenever the side condition holds. -/
def finalComplete {T : Type} (out : SumcheckRound.Stmt X F n → Vector F m → T)
    {relOut' : Set ((T × ∀ i, O i) × W)}
    (h : ∀ s o w, side ((s.1, o), w) →
      ((out s (V.values ((s.1, o), w) s.2.1.reverse), o), w) ∈ relOut') :
    Component.Complete (final V out) (SumcheckRound.rel (family V wt nodes side) n) relOut' :=
  Component.sendCheckedComplete O (Vector F m) _ _ _ fun s o w hin ↦ by
    obtain ⟨hside, hclaim⟩ := (mem_rel_self V wt nodes side _).mp hin
    refine ⟨?_, h s o w hside⟩
    rw [finalCheck, decide_eq_true_eq, hclaim]
    rfl

omit [DecidableEq F] [SampleableType F] in
/-- The final check is load-bearing: the last message without it has no knowledge state function
at all, whatever the extractor, once a statement meets the side condition and its running claim
is not the summand at its point, since the true values then pass and land in the output
relation. -/
theorem final_unchecked_no_stateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) {W' : Fin 2 → Type}
    {E : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
      (SumcheckRound.Stmt X F n × ∀ i, O i) W W (say (Vector F m)) W'}
    (K : (Component.sendCheckedVerifier O (Vector F m) (fun _ _ ↦ true)
      (finalOut (X := X) (F := F) (n := n) (m := m))).toVerifier.KnowledgeStateFunction init impl
      (SumcheckRound.rel (family V wt nodes side) n) (relOut V side) E)
    (s : SumcheckRound.Stmt X F n) (o : ∀ i, O i) (w : W) (hside : side ((s.1, o), w))
    (hs : ∀ w', s.2.2 ≠ V.summand ((s.1, o), w') s.2.1.reverse) : False :=
  Component.sendChecked_no_stateFunction O (Vector F m) (fun _ _ ↦ true) finalOut init impl K s o
    (fun w' h ↦ hs w' ((mem_rel_self V wt nodes side _).mp h).2)
    (V.values ((s.1, o), w) s.2.1.reverse) rfl w ⟨rfl, hside⟩

/-- Perfect completeness of the sumcheck, when the summand has degree at most `d` in each
variable and the nodes are distinct. -/
def weightedComplete (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d)
    (hnodes : Function.Injective nodes) :
    Component.Complete (weighted V wt nodes) (relIn V wt side) (relOut V side) :=
  (roundsComplete V wt nodes side hV hnodes).append
    (finalComplete V wt nodes side finalOut fun _ _ _ hside ↦ ⟨rfl, hside⟩)

/-- Perfect completeness of the plain sumcheck. -/
def plainComplete (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d)
    (hnodes : Function.Injective nodes) :
    Component.Complete (plain V nodes) (relIn V unitWeights side) (relOut V side) :=
  weightedComplete V unitWeights nodes side hV hnodes

/-- Perfect completeness of the normalized sumcheck. -/
def normalizedComplete (pt : X → Vector F n) (hV : ∀ ctx, IndividualDegreeLE (V.summand ctx) d)
    (hnodes : Function.Injective nodes) :
    Component.Complete (normalized V pt nodes) (relIn V (eqWeights pt) side) (relOut V side) :=
  weightedComplete V (eqWeights pt) nodes side hV hnodes

end Complete

section Wire

variable {F : Type} [Field F] {d : ℕ}

/-! ## The wire: a round message without one coefficient -/

/-- The weight of coefficient `i` in a round's check: `Σ_{(x, w)} w · x^i` over the domain. -/
def coeffWeight (dom : SumcheckRound.WeightedDomain F) (i : ℕ) : F :=
  (dom.map fun p ↦ p.2 * p.1 ^ i).sum

/-- The round's check is linear in the coefficients, coefficient `i` weighted by
`coeffWeight dom i`. -/
theorem weightedSum_eq_sum (dom : SumcheckRound.WeightedDomain F) (q : SumcheckRound.Message F d) :
    SumcheckRound.weightedSum d dom q = ∑ i : Fin (d + 1), q[i] * coeffWeight dom i := by
  simp only [SumcheckRound.weightedSum, SumcheckRound.evaluate, coeffWeight]
  induction dom with
  | nil => simp
  | cons p dom ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Finset.mul_sum]
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- In the two-point domain, coefficient `0` weighs the sum of the weights. -/
theorem coeffWeight_pair_zero (a b : F) : coeffWeight [(0, a), (1, b)] 0 = a + b := by
  simp [coeffWeight]

/-- In the two-point domain, every other coefficient weighs the weight of `1`. -/
theorem coeffWeight_pair_succ (a b : F) (i : ℕ) : coeffWeight [(0, a), (1, b)] (i + 1) = b := by
  simp [coeffWeight]

/-- The message with coefficient `k` derived from the running claim: the value that makes the
round's check hold, whatever the message carried there. -/
def decodeRound (dom : SumcheckRound.WeightedDomain F) (k : Fin (d + 1)) (claim : F)
    (q : SumcheckRound.Message F d) : SumcheckRound.Message F d :=
  q.set k ((claim - ∑ i ∈ Finset.univ.erase k, q[i] * coeffWeight dom i) / coeffWeight dom k)

/-- The decoding ignores the coefficient it derives. -/
theorem decodeRound_set (dom : SumcheckRound.WeightedDomain F) (k : Fin (d + 1)) (claim a : F)
    (q : SumcheckRound.Message F d) :
    decodeRound dom k claim (q.set k a) = decodeRound dom k claim q := by
  have h : ∀ i ∈ Finset.univ.erase k, (q.set k a)[i] = q[i] := fun i hi ↦
    Vector.getElem_set_ne _ _ fun h ↦ (Finset.mem_erase.mp hi).1 (Fin.ext h).symm
  rw [decodeRound, decodeRound, Finset.sum_congr rfl fun i hi ↦ by rw [h i hi], Vector.set_set]

/-- A decoded message passes the round's check, when the derived coefficient has an invertible
weight. -/
theorem weightedSum_decodeRound {dom : SumcheckRound.WeightedDomain F} {k : Fin (d + 1)}
    (hk : coeffWeight dom k ≠ 0) (claim : F) (q : SumcheckRound.Message F d) :
    SumcheckRound.weightedSum d dom (decodeRound dom k claim q) = claim := by
  rw [weightedSum_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have h : ∀ i ∈ Finset.univ.erase k, (decodeRound dom k claim q)[i] = q[i] := fun i hi ↦
    Vector.getElem_set_ne _ _ fun h ↦ (Finset.mem_erase.mp hi).1 (Fin.ext h).symm
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [h i hi]]
  simp only [decodeRound, Fin.getElem_fin, Vector.getElem_set_self]
  field_simp
  ring

/-- Decoding a message that passes the round's check returns it: the honest message survives
the wire. -/
theorem decodeRound_of_weightedSum {dom : SumcheckRound.WeightedDomain F} {k : Fin (d + 1)}
    (hk : coeffWeight dom k ≠ 0) {claim : F} {q : SumcheckRound.Message F d}
    (hq : SumcheckRound.weightedSum d dom q = claim) : decodeRound dom k claim q = q := by
  have hval : (claim - ∑ i ∈ Finset.univ.erase k, q[i] * coeffWeight dom i) /
      coeffWeight dom k = q[k] := by
    rw [← hq, weightedSum_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    field_simp
    ring
  rw [decodeRound, hval]
  exact Vector.set_getElem_self _

variable {X : Type} {ι : Type} {O : ι → Type}

/-- The wire's message: the coefficients but coefficient `k`, in order. -/
def encodeWire (k : Fin (d + 1)) (q : SumcheckRound.Message F d) : Vector F d :=
  Vector.ofFn fun i : Fin d ↦ if i.val < k.val then q[i.val] else q[i.val + 1]

/-- The coefficients read off the wire, with `0` in position `k`. -/
def expandWire (k : Fin (d + 1)) (w : Vector F d) : SumcheckRound.Message F d :=
  Vector.ofFn fun i : Fin (d + 1) ↦
    if h : i.val < k.val then w[i.val]'(by omega)
    else if h' : i.val = k.val then 0 else w[i.val - 1]'(by omega)

/-- The round message decoded from the wire: coefficient `k` derived from the running claim. -/
def decodeWire (dom : SumcheckRound.WeightedDomain F) (k : Fin (d + 1)) (claim : F)
    (w : Vector F d) : SumcheckRound.Message F d :=
  decodeRound dom k claim (expandWire k w)

/-- Expanding the wire of a message is the message with coefficient `k` set to `0`. -/
theorem expandWire_encodeWire (k : Fin (d + 1)) (q : SumcheckRound.Message F d) :
    expandWire k (encodeWire k q) = q.set k 0 := by
  apply Vector.ext
  intro i hi
  simp only [expandWire, encodeWire, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h1 : i < k.val
  · simp [h1, show (k : ℕ) ≠ i by omega]
  · by_cases h2 : i = k.val
    · simp [h2]
    · simp only [h1, h2, dite_false, ite_false, show ¬ (i - 1 < k.val) by omega,
        show (k : ℕ) ≠ i by omega]
      congr 1
      omega

/-- The wire of a message that passes the round's check decodes to the message. -/
theorem decodeWire_encodeWire {dom : SumcheckRound.WeightedDomain F} {k : Fin (d + 1)}
    (hk : coeffWeight dom k ≠ 0) {claim : F} {q : SumcheckRound.Message F d}
    (hq : SumcheckRound.weightedSum d dom q = claim) :
    decodeWire dom k claim (encodeWire k q) = q := by
  rw [decodeWire, expandWire_encodeWire, decodeRound_set, decodeRound_of_weightedSum hk hq]

/-- A decoded message passes the round's check, when the derived coefficient has an invertible
weight. -/
theorem weightedSum_decodeWire {dom : SumcheckRound.WeightedDomain F} {k : Fin (d + 1)}
    (hk : coeffWeight dom k ≠ 0) (claim : F) (w : Vector F d) :
    SumcheckRound.weightedSum d dom (decodeWire dom k claim w) = claim :=
  weightedSum_decodeRound hk claim _

/-- The decoded message carries the wire in every other position: the decoding is injective. -/
theorem encodeWire_decodeWire (dom : SumcheckRound.WeightedDomain F) (k : Fin (d + 1))
    (claim : F) (w : Vector F d) : encodeWire k (decodeWire dom k claim w) = w := by
  apply Vector.ext
  intro i hi
  by_cases h1 : i < k.val
  · have h1' : (⟨i, by omega⟩ : Fin (d + 1)) < k := h1
    simp [encodeWire, decodeWire, decodeRound, expandWire, Vector.getElem_set, h1, h1',
      show (k : ℕ) ≠ i by omega]
  · have h1' : ¬ (⟨i + 1, by omega⟩ : Fin (d + 1)) < k := fun h ↦ h1 (by
      have := Fin.lt_def.mp h
      simp only at this
      omega)
    simp [encodeWire, decodeWire, decodeRound, expandWire, Vector.getElem_set, h1, h1',
      show (k : ℕ) ≠ i + 1 by omega, show i + 1 ≠ (k : ℕ) by omega]

/-- The decoding of the wire is injective. -/
theorem decodeWire_injective (dom : SumcheckRound.WeightedDomain F) (k : Fin (d + 1))
    (claim : F) : Function.Injective (decodeWire dom k claim) :=
  Function.LeftInverse.injective (encodeWire_decodeWire dom k claim)

/-- One round on the wire: `d` of the `d + 1` coefficients, then the challenge. -/
abbrev wireSpec (F : Type) (d : ℕ) : ProtocolSpec 2 := say (Vector F d) ++ₚ draw F

instance instOracleInterfaceWire (d : ℕ) : ∀ i, OracleInterface ((wireSpec F d).Message i) :=
  msgAppend (instOracleInterfaceSay _) (instOracleInterfaceDraw F)

instance instSampleableTypeWire [SampleableType F] (d : ℕ) :
    ∀ i, SampleableType ((wireSpec F d).Challenge i) :=
  chalAppend (instSampleableTypeSay _) (instSampleableTypeDraw F)

/-- The decoding of a round's wire: the message decoded from the stage's domain and running claim,
the challenge kept. -/
def roundDecoding (wt : SumcheckRound.Weights F X) (j : ℕ) (k : Fin (d + 1)) :
    TranscriptMap (SumcheckRound.Stmt X F j × ∀ i, O i) (wireSpec F d) (roundSpec F d) :=
  TranscriptMap.ofMessage (fun _ ↦ rfl)
    (fun i ↦ match i with
      | ⟨⟨0, _⟩, h⟩ => nomatch h
      | ⟨⟨1, _⟩, _⟩ => fun c ↦ c)
    (fun i ↦ match i with
      | ⟨⟨0, _⟩, h⟩ => nomatch h
      | ⟨⟨1, _⟩, _⟩ => Function.bijective_id)
    fun s i ↦ match i with
      | ⟨⟨0, _⟩, _⟩ => fun w ↦ decodeWire (wt s.1.1 j) k s.1.2.2 w
      | ⟨⟨1, _⟩, h⟩ => nomatch h

variable {W : Type} [∀ i, OracleInterface (O i)] [DecidableEq F] [SampleableType F]

/-- The transport: a round's verifier that reads the wire, `d` of the `d + 1` coefficients, and
decodes it is round-by-round knowledge sound at the round's error, for the extractor and the state
function read on the decoded transcript. -/
theorem transport {P : SumcheckRound.Polys F X O W d} {wt : SumcheckRound.Weights F X} {j : ℕ}
    {relIn : Set ((SumcheckRound.Stmt X F j × ∀ i, O i) × W)}
    {relOut : Set ((SumcheckRound.Stmt X F (j + 1) × ∀ i, O i) × W)}
    {ε : (roundSpec F d).ChallengeIdx → ℝ≥0}
    (S : Component.Security (SumcheckRound.round P j wt) relIn relOut ε) (k : Fin (d + 1))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (Verifier.comap (SumcheckRound.round P j wt).red.verifier.toVerifier
      (roundDecoding (O := O) wt j k)).rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut
      S.witMid (Extractor.RoundByRound.comap S.extractor (roundDecoding wt j k))
      (Verifier.KnowledgeStateFunction.comap (S.kSF init impl) (roundDecoding wt j k))
      (fun i ↦ ε ((roundDecoding (O := O) wt j k).idx i)) :=
  Verifier.rbrKnowledgeSoundnessWorstCaseWith_comap (S.rbr init impl) _

end Wire

end Sumcheck

end
end LeanerVM.Protocol
