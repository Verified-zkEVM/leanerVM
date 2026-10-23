import LeanerVM.Protocol.ToArkLib.Flock.Rounds
import LeanerVM.Protocol.ToArkLib.ProductSumcheck
import LeanerVMTests.Protocol.TableSumcheck

/-!
# Differential tests of the folded sumcheck provers

`Sumcheck.roundPoly` and `ProductSum.roundPoly` compile, through the `@[csimp]` theorems
`Sumcheck.roundPoly_eq_roundPolyFolded` and `ProductSum.roundPoly_eq_roundPolyFolded`, to
algorithms that bind each table once to the challenges; the Flock rounds, the table sumcheck's
formula, `CMvPolynomial.eval₂` and `SumcheckRound.evaluate` compile to faster equals. The theorems
are proved; these guards run the compiled code against the specification's algorithm, assembled
here from functions no `@[csimp]` theorem replaces (`Sumcheck.claim`, `ProductSum.coef0`, …), at
every round of small instances, past the last round included:

* over `ℚ`, where no characteristic hides a sign, on four variables, with a formula that reads
  the point as well as the tables' values, with unit, equality and arbitrary weights, and with
  nodes that repeat (the theorems hold for every node map);
* over `E`, on the cubic summand of three tables with the weights of an equality polynomial, and
  on the table sumcheck's summand of the two-table instance of `TableSumcheck`'s tests;
* the product sumcheck over `ℚ` on four variables and over `E` on three, and the Flock
  argument's zerocheck and lincheck rounds over `ℚ`;
* the table sumcheck's formula (`formulaFast`) at Boolean points, a point that zeroes one table's
  weight and others; the sparse evaluation of a row polynomial against CompPoly's Horner
  evaluator; `SumcheckRound.evaluate` against the sum of its powers.

A mutation shows that the order in which the challenges bind the coordinates is load-bearing:
binding the tables in the order drawn, the first challenge on the lowest bound coordinate, misses
the running claim.

A plain file, so `#guard` evaluates the compiled definitions.
-/

namespace LeanerVMTests.Protocol.SumcheckFold

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Sumcheck CompPoly CMlPolynomialEval

/-- The specification's round polynomial: `roundPoly`'s body, compiled here, where it names
`claim`, which no `@[csimp]` theorem replaces. -/
def specRoundPoly {F : Type} [Field F] [BEq F] [LawfulBEq F] {X ι : Type} {O : ι → Type}
    {W : Type} {n m d : ℕ} (V : Virtual F X O W n m) (wt : CoordWeights F X n)
    (nodes : Fin (d + 1) → F) (ctx : SumcheckRound.Ctx X O W) (j : ℕ) (c : Vector F j) :
    SumcheckRound.Message F d :=
  if j < n then
    SumcheckRound.ofCPolynomial d (CPolynomial.CLagrange.interpolate Finset.univ nodes
      fun i ↦ claim V wt ctx (j + 1) (c.push (nodes i)))
  else SumcheckRound.ofCPolynomial d 0

/-- The first `j` of a list of challenges. -/
def firstChals {F : Type} [Zero F] (cs : List F) (j : ℕ) : Vector F j :=
  Vector.ofFn fun i ↦ cs.getD i.val 0

/-- The compiled prover and the specification agree at every round `0, …, n`. -/
def agree {F : Type} [Field F] [BEq F] [LawfulBEq F] {X ι : Type} {O : ι → Type} {W : Type}
    {n m d : ℕ} (V : Virtual F X O W n m) (wt : CoordWeights F X n) (nodes : Fin (d + 1) → F)
    (ctx : SumcheckRound.Ctx X O W) (cs : List F) : Bool :=
  (List.range (n + 1)).all fun j ↦
    (roundPoly V wt nodes ctx j (firstChals cs j)).toList ==
      (specRoundPoly V wt nodes ctx j (firstChals cs j)).toList

/-- No oracle. -/
def noO : ∀ i, NoOracle i := fun i ↦ i.elim0

/-- The context with no public data, oracle or witness. -/
def unitCtx : SumcheckRound.Ctx Unit NoOracle Unit := (((), noO), ())

/-! ## Over `ℚ` -/

/-- Three tables on four variables. -/
def qTables : Fin 3 → CMlPolynomialEval ℚ 4 := fun k ↦
  Vector.ofFn fun i ↦ ((i.val * i.val + 3 * k.val + 1 : ℕ) : ℚ) / (k.val + 2 : ℚ) - i.val

/-- A formula that reads the point as well as the values. -/
def qV : Virtual ℚ Unit NoOracle Unit 4 3 where
  tables := fun _ ↦ qTables
  formula := fun _ z v ↦ z[0] * v[0] * v[1] + z[3] * v[2] + v[0] * v[1] * v[2] - 3

/-- Distinct nodes, and nodes that repeat. -/
def qNodes : Fin 4 → ℚ := ![0, 1, 2, -3]
def qNodesRep : Fin 4 → ℚ := ![0, 0, 1, 5]

def qChals : List ℚ := [7, -2, 1 / 3, 5]

/-- Weights that are neither unit nor an equality polynomial's. -/
def qWeights : CoordWeights ℚ Unit 4 := fun _ k ↦ ((k.val + 1 : ℚ), (2 * k.val - 1 : ℚ))

#guard agree qV unitWeights qNodes unitCtx qChals
#guard agree qV (eqWeights fun _ ↦ #v[1 / 2, 2, -1, 3]) qNodes unitCtx qChals
#guard agree qV qWeights qNodes unitCtx qChals
#guard agree qV unitWeights qNodesRep unitCtx qChals
-- A round message is not trivially zero: the comparison sees the values.
#guard (roundPoly qV unitWeights qNodes unitCtx 1 (firstChals qChals 1)).toList.any (· ≠ 0)

/-! ## Over `E` -/

/-- Values of `E`. -/
def a : E := y
def b : E := y * y + 1
def c : E := y * y + y

/-- Three tables on three variables. -/
def eTables : Fin 3 → CMlPolynomialEval E 3 := fun k ↦
  Vector.ofFn fun i ↦ if (i.val + k.val) % 3 = 0 then a * b else if i.val % 2 = 0 then c else b + 1

/-- The cubic summand of three tables, read with the point. -/
def eV : Virtual E Unit NoOracle Unit 3 3 where
  tables := fun _ ↦ eTables
  formula := fun _ z v ↦ v[0] * v[1] * v[2] + z[1] * v[0]

def eChals : List E := [c, a + 1, b * c]

#guard agree eV (eqWeights fun _ ↦ #v[a, b, c]) TableSumcheck.nodes unitCtx eChals

-- The table sumcheck's summand on the two-table instance, at both rounds and past them.
#guard agree (TableSumcheck.tableSummand TableSumcheck.twoTab) unitWeights TableSumcheck.nodes
  TableSumcheck.ctx [TableSumcheck.c0, TableSumcheck.c1]

/-! ## The product sumcheck -/

/-- The specification's product round polynomial: the three coefficient sums. -/
def specProductRound {F : Type} [Field F] {n : ℕ} (A B : CMlPolynomialEval F n) (j : ℕ)
    (c : Vector F j) : SumcheckRound.Message F 2 :=
  if h : j < n then
    #v[ProductSum.coef0 A B h c, ProductSum.coef1 A B h c, ProductSum.coef2 A B h c]
  else #v[0, 0, 0]

/-- The compiled product prover and the specification agree at every round `0, …, n`. -/
def productAgree {F : Type} [Field F] [BEq F] {n : ℕ} (A B : CMlPolynomialEval F n)
    (cs : List F) : Bool :=
  (List.range (n + 1)).all fun j ↦
    (ProductSum.roundPoly A B j (firstChals cs j)).toList ==
      (specProductRound A B j (firstChals cs j)).toList

#guard productAgree (qTables 0) (qTables 2) qChals
#guard productAgree (eTables 1) (eTables 2) eChals

/-! ## The Flock rounds -/

/-- `Flock.normRound`'s body, compiled here, where it names `evalMle`. -/
def specNormRound {F : Type} [Field F] {n : ℕ} (tA tB tC : CMlPolynomialEval F n)
    (r : Vector F n) (j : ℕ) (c : Vector F j) : SumcheckRound.Message F 2 :=
  if hj : j < n then
    let L := lagrangeBasis (r.drop (j + 1))
    let pt := fun (b : Fin (2 ^ (n - (j + 1)))) (X : F) ↦
      (fixLow hj (c.push 0) (boolVec b)).set j X hj
    let e := fun (t : CMlPolynomialEval F n) (b : Fin (2 ^ (n - (j + 1)))) (X : F) ↦
      evalMle t (pt b X)
    #v[∑ b, L[b] * (e tA b 0 * e tB b 0 - e tC b 0),
      ∑ b, L[b] * (e tA b 0 * (e tB b 1 - e tB b 0) + (e tA b 1 - e tA b 0) * e tB b 0 -
        (e tC b 1 - e tC b 0)),
      ∑ b, L[b] * ((e tA b 1 - e tA b 0) * (e tB b 1 - e tB b 0))]
  else 0

/-- `Flock.highRound`'s body, compiled here, where it names `evalMle`. -/
def specHighRound {F : Type} [Field F] {s m : ℕ} (M Z : CMlPolynomialEval F (s + m)) (j : ℕ)
    (c : Vector F j) : SumcheckRound.Message F 2 :=
  if hj : j < m then
    let pt := fun (b : Fin (2 ^ (m - (j + 1)))) (X : F) ↦
      (highFix hj (c.push 0) (boolVec b)).set (m - (j + 1)) X (by omega)
    let e := fun (t : CMlPolynomialEval F (s + m)) (i : Fin (2 ^ s))
      (b : Fin (2 ^ (m - (j + 1)))) (X : F) ↦ evalMle (sliceLow t i) (pt b X)
    #v[∑ b, ∑ i, e M i b 0 * e Z i b 0,
      ∑ b, ∑ i, (e M i b 0 * (e Z i b 1 - e Z i b 0) + (e M i b 1 - e M i b 0) * e Z i b 0),
      ∑ b, ∑ i, (e M i b 1 - e M i b 0) * (e Z i b 1 - e Z i b 0)]
  else 0

/-- The point of the zerocheck's equality weights. -/
def qPoint : Vector ℚ 4 := #v[2, -1 / 2, 3, 5]

#guard (List.range 5).all fun j ↦
  (Flock.normRound (qTables 0) (qTables 1) (qTables 2) qPoint j (firstChals qChals j)).toList ==
    (specNormRound (qTables 0) (qTables 1) (qTables 2) qPoint j (firstChals qChals j)).toList

-- One low coordinate sliced off, three high ones bound by the rounds.
#guard (List.range 4).all fun j ↦
  (Flock.highRound (s := 1) (m := 3) (qTables 0) (qTables 2) j (firstChals qChals j)).toList ==
    (specHighRound (s := 1) (m := 3) (qTables 0) (qTables 2) j (firstChals qChals j)).toList

/-! ## The table sumcheck's formula, row polynomials and round messages' values -/

/-- The two-table instance of `TableSumcheck`'s tests. -/
abbrev twoTab : M3Instance := TableSumcheck.twoTab

/-- The formula's body, compiled here, where it names `prodWeight`, `rowValue` and `tableValues`,
which no `@[csimp]` theorem replaces. -/
def specFormula (x : LeanerVM.Protocol.TableSumcheck.Data twoTab) (z : Vector E twoTab.τmax)
    (v : Vector E twoTab.tableColumns) : E :=
  ∑ t : twoTab.SumcheckTables,
    prodWeight (LeanerVM.Protocol.TableSumcheck.tableWeights twoTab x.1.2.point t) z *
      LeanerVM.Protocol.TableSumcheck.rowValue twoTab x t
        (LeanerVM.Protocol.TableSumcheck.tableValues twoTab v t)

/-- Points of the two coordinates: Boolean ones, which take the shortcuts of `prodWeightFast`, the
padding coordinate of table 1 at `0`, which zeroes its weight, and others. -/
def zs : List (Vector E twoTab.τmax) :=
  [#v[0, 0], #v[0, 1], #v[1, 0], #v[1, 1], #v[a, 0], #v[0, b], #v[a, b], #v[c, 1]]

-- `formula` compiles to `formulaFast`.
#guard zs.all fun z ↦
  LeanerVM.Protocol.TableSumcheck.formula twoTab TableSumcheck.x z #v[a, c] =
    specFormula TableSumcheck.x z #v[a, c]
-- The comparison sees values: the formula is not zero at every point.
#guard zs.any fun z ↦ LeanerVM.Protocol.TableSumcheck.formula twoTab TableSumcheck.x z #v[a, c] ≠ 0

/-- A row polynomial of three variables with absent variables in each monomial. -/
def rowPoly : CPoly.CMvPolynomial 3 K :=
  CPoly.CMvPolynomial.X 0 * CPoly.CMvPolynomial.X 2 * CPoly.CMvPolynomial.X 2 +
    CPoly.CMvPolynomial.X 1 - CPoly.CMvPolynomial.C (K.ofBits 5)

-- `eval₂` compiles to `eval₂Sparse`; CompPoly's Horner evaluator is another algorithm.
#guard [(a, b, c), (0, 1, b), (c, 0, 0)].all fun (p, q, r) ↦
  rowPoly.eval₂ (algebraMap K E) ![p, q, r] = rowPoly.eval₂Horner (algebraMap K E) ![p, q, r]

-- `SumcheckRound.evaluate` compiles to Horner's rule.
#guard [a, b, c, 0, 1].all fun t ↦
  SumcheckRound.evaluate 3 #v[a, b, c, a * b] t = ∑ i : Fin 4, (#v[a, b, c, a * b])[i] * t ^ i.val

/-! ## The order of the challenges -/

/-- The next claim from tables bound in the order the challenges were drawn: the first challenge
on the lowest bound coordinate instead of the highest. -/
def claimDrawnOrder {n m : ℕ} (V : Virtual ℚ Unit NoOracle Unit n m) (wt : CoordWeights ℚ Unit n)
    {j : ℕ} (hj : j < n) (c : Vector ℚ j) (x : ℚ) : ℚ :=
  claimFolded V wt unitCtx hj c
    (Vector.ofFn fun i ↦ bindHighs (Vector.cast (congrArg (2 ^ ·) (by omega)) (V.tables unitCtx i))
      c) x

-- With the challenges reversed, as `boundTables` binds them, the folded claim is the next claim;
-- in the order drawn, it is not.
#guard claimFolded qV unitWeights unitCtx (j := 2) (by decide) (firstChals qChals 2)
    (boundTables qV unitCtx (by decide) (firstChals qChals 2)) 4 =
  claim qV unitWeights unitCtx 3 ((firstChals qChals 2).push 4)
#guard claimDrawnOrder qV unitWeights (j := 2) (by decide) (firstChals qChals 2) 4 ≠
  claim qV unitWeights unitCtx 3 ((firstChals qChals 2).push 4)

end LeanerVMTests.Protocol.SumcheckFold
