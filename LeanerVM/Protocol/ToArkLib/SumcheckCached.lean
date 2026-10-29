/-
  LeanerVM.Protocol.ToArkLib.SumcheckCached

  The sumcheck of a virtual polynomial with a cached honest prover: the tables bound to the
  challenges carried from round to round, each challenge bound once, and the final values read
  off the tables bound on every coordinate. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Sumcheck
public import LeanerVM.Protocol.ToArkLib.CachedRounds
public import LeanerVM.Protocol.ToCompPoly.BindStep

/-!
# The sumcheck with its bound tables cached

`Sumcheck.roundPoly` reads the tables bound to the challenges so far; computed from the context
and the challenges alone, round `j` binds every table afresh, `m · 2 ^ n` work per round. The
cached prover keeps them (`boundCache`: each table bound on its top `j` coordinates to the
challenges, the first the highest), reads each round polynomial off them (`roundFromCache`, the
fold of `roundPolyFolded`), and binds each challenge once, one halving per table
(`stepCache`, by `bindHigh_bindHighs_reverse`): `m · 2 ^ (n - j)` work at round `j`, and the
tables are read off the context once, at the start. `roundCache` packages this as a
`SumcheckRound.RoundCache`; `cachedRounds` is the cached prover of the rounds; `cachedFinal`
reads the final values off the tables bound on every coordinate; `cachedWeighted` is the whole
sumcheck, its cache started from the context.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Sumcheck

variable {F : Type} [Field F] {X : Type} {ι : Type} {O : ι → Type} {W : Type} {n m : ℕ}

/-! ## The bound tables -/

/-- The tables with their top `j` coordinates bound to the challenges `c`, the first the
highest: what the honest prover keeps from round to round. -/
def boundCache (V : Virtual F X O W n m) (ctx : SumcheckRound.Ctx X O W) (j : ℕ)
    (c : Vector F j) : Vector (CMlPolynomialEval F (n - j)) m :=
  if hj : j ≤ n then
    Vector.ofFn fun i ↦ bindHighs (k := n - j)
      (Vector.cast (congrArg (2 ^ ·) (Nat.sub_add_cancel hj).symm) (V.tables ctx i)) c.reverse
  else Vector.replicate m (Vector.replicate _ 0)

/-- Tables on `n - j` variables as tables of round `j`'s coordinate and the free ones below. -/
def nextTables {j : ℕ} (hj : j < n) (ts : Vector (CMlPolynomialEval F (n - j)) m) :
    Vector (CMlPolynomialEval F (n - (j + 1) + 1)) m :=
  ts.map (Vector.cast (congrArg (2 ^ ·) (by omega)))

/-- The bound tables, read at round `j`, are the tables `roundPolyFolded` binds. -/
theorem nextTables_boundCache (V : Virtual F X O W n m) (ctx : SumcheckRound.Ctx X O W)
    {j : ℕ} (hj : j < n) (c : Vector F j) :
    nextTables hj (boundCache V ctx j c) = boundTables V ctx hj c := by
  refine Vector.ext fun i hi ↦ ?_
  rw [boundCache, dite_eq_left hj.le]
  simp only [nextTables, boundTables, bindHighsNext, Vector.getElem_map, Vector.getElem_ofFn]
  rw [bindHighs_cast (by omega), Vector.cast_cast]

/-- The bound tables after one more challenge, `a`: each bound at its top coordinate. -/
def stepCache {j : ℕ} (ts : Vector (CMlPolynomialEval F (n - j)) m) (a : F) :
    Vector (CMlPolynomialEval F (n - (j + 1))) m :=
  if hj : j < n then (nextTables hj ts).map fun t ↦ bindHigh t a
  else Vector.replicate m (Vector.replicate _ 0)

/-- Binding the next challenge updates the bound tables. -/
theorem stepCache_boundCache (V : Virtual F X O W n m) (ctx : SumcheckRound.Ctx X O W)
    {j : ℕ} (hj : j < n) (c : Vector F j) (a : F) :
    stepCache (boundCache V ctx j c) a = boundCache V ctx (j + 1) (c.push a) := by
  rw [stepCache, dite_eq_left hj, nextTables_boundCache]
  refine Vector.ext fun i hi ↦ ?_
  rw [boundCache, dite_eq_left (Nat.succ_le_of_lt hj)]
  simp only [boundTables, bindHighsNext, Vector.getElem_map, Vector.getElem_ofFn]
  rw [bindHigh_bindHighs_reverse, Vector.cast_cast]

/-- The tables' values at the final point, read off the tables bound on every coordinate. -/
def valuesFromCache (ts : Vector (CMlPolynomialEval F (n - n)) m) : Vector F m :=
  Vector.ofFn fun i ↦ ts[i][0]'(Nat.two_pow_pos _)

/-- The tables bound on every coordinate hold the tables' values at the final point, in
coordinate order. -/
theorem valuesFromCache_boundCache (V : Virtual F X O W n m) (ctx : SumcheckRound.Ctx X O W)
    (c : Vector F n) : valuesFromCache (boundCache V ctx n c) = V.values ctx c.reverse := by
  unfold valuesFromCache Virtual.values
  rw [boundCache, dite_eq_left le_rfl]
  refine Vector.ext fun i hi ↦ ?_
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [bindHighs_getElem_zero (Nat.sub_self n), evalMle_cast]

/-! ## The cached rounds -/

variable [BEq F] [LawfulBEq F]

/-- The honest round polynomial of round `j`, read off the bound tables: `roundPolyFolded`'s
interpolation of the folded claims. -/
def roundFromCache (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) (ctx : SumcheckRound.Ctx X O W) (j : ℕ) (c : Vector F j)
    (ts : Vector (CMlPolynomialEval F (n - j)) m) : SumcheckRound.Message F d :=
  if hj : j < n then
    let ts' := nextTables hj ts
    SumcheckRound.ofCPolynomial d (CPolynomial.CLagrange.interpolate Finset.univ nodes
      fun i ↦ claimFolded V wt ctx hj c ts' (nodes i))
  else SumcheckRound.ofCPolynomial d 0

/-- The sumcheck's round cache: the bound tables, the round polynomial read off them, and one
halving per table at each challenge. -/
def roundCache (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) : SumcheckRound.RoundCache (roundPoly V wt nodes) n where
  C j := Vector (CMlPolynomialEval F (n - j)) m
  cache j ctx c := boundCache V ctx j c
  msg j ctx c ts := roundFromCache V wt nodes ctx j c ts
  step _ _ _ ts a := stepCache ts a
  msg_eq j ctx c hj := by
    rw [roundPoly_eq_roundPolyFolded, roundFromCache, roundPolyFolded, dite_eq_left hj,
      dite_eq_left hj, nextTables_boundCache]
  step_eq _ ctx c a hj := stepCache_boundCache V ctx hj c a

variable [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)]

/-- The cached prover of the sumcheck's `n` rounds: the bound tables of the empty challenge
vector taken, those of the final point handed on. -/
def cachedRounds (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) :
    Component.Cached (rounds V wt nodes) ((roundCache V wt nodes).at (j := 0))
      ((roundCache V wt nodes).at (j := n)) :=
  SumcheckRound.cachedRounds (roundCache V wt nodes) (domain wt) n 0 (Nat.zero_add n)

/-- The cached last message: the values read off the tables bound on every coordinate. -/
def cachedFinal (V : Virtual F X O W n m) {T : Type}
    (out : SumcheckRound.Stmt X F n → Vector F m → T) :
    Component.Cached (final (W := W) (O := O) V out)
      (fun p ↦ boundCache V (SumcheckRound.ctxOf p) n p.1.1.2.1) (fun _ ↦ ()) :=
  Component.Cached.sendChecked (msg := fun _ ts ↦ valuesFromCache ts) (upd := fun _ _ _ ↦ ())
    (fun _ ↦ valuesFromCache_boundCache V _ _) fun _ ↦ rfl

/-- The cached prover of the whole sumcheck: the tables read off the context once, bound one
challenge at a time, and the final values read off them. -/
def cachedWeighted (V : Virtual F X O W n m) (wt : CoordWeights F X n) {d : ℕ}
    (nodes : Fin (d + 1) → F) :
    Component.Cached (weighted V wt nodes) (fun _ ↦ ()) (fun _ ↦ ()) :=
  ((cachedRounds V wt nodes).adaptIn (fun p _ ↦ boundCache V (SumcheckRound.ctxOf p) 0 #v[])
    fun p ↦ by
      show _ = boundCache V _ 0 p.1.1.2.1
      rw [Vector.eq_empty (xs := p.1.1.2.1)]).append (cachedFinal V finalOut)

end Sumcheck

end
end LeanerVM.Protocol
