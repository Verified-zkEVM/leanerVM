import LeanerVM.Protocol.HonestProver
import LeanerVMTests.Protocol.Bus

/-!
# Differential tests of the honest provers with state

The cached provers of `LeanerVM.Protocol.ToArkLib.CachedProver` are proved to run as the honest
provers (`Component.Cached.run_eq`, `leanVmFastProver_run`); these `#guard`s check the compiled
code at small sizes, against the stateless definitions it stands for.

* **The sumcheck's bound tables.** The messages of a sumcheck computed from tables bound once and
  updated by each challenge (`Sumcheck.roundFromCache`, `Sumcheck.stepCache`) are the honest
  ones (`Sumcheck.roundPoly`, which binds every table afresh), and so are the final values.
* **The product trees.** The levels built once (`levelsOf`) are `layerTable`'s; the messages of a
  layer's sumcheck from the bound children (`Gkr.roundFromBound`, `Gkr.stepChildren`) are
  `Gkr.roundPoly`'s, and the children bound on every coordinate hold `Gkr.children`.
* **Runs.** On the bus tests' instance, ArkLib's `Prover.run` of the cached bus phase and of the
  cached table sumcheck, at a fixed challenge sequence, outputs what the honest provers output.
* **Mutations.** Binding a challenge at the low end of the sumcheck's tables changes the result.
-/

namespace LeanerVMTests.Protocol.StatefulProvers

open LeanerVM.Parameters LeanerVM.Protocol CompPoly CMlPolynomialEval
open OracleComp OracleSpec ProtocolSpec

/-- A xorshift step. -/
private def xs (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A `K` word from a seed. -/
private def kOf (s : UInt64) : K := BF64.ofBitVec (xs s).toBitVec

/-- An `E` element from a seed. -/
private def eOf (s : UInt64) : E := E.ofLimbs (kOf s) (kOf (s + 1)) (kOf (s + 2))

/-- A point of `E` from a seed. -/
private def pt (n : ℕ) (seed : UInt64) : Vector E n :=
  Vector.ofFn fun i ↦ eOf (seed + 3 * i.val.toUInt64)

/-- A table over `E` from a seed. -/
private def tabE (n : ℕ) (seed : UInt64) : CMlPolynomialEval E n :=
  Vector.ofFn fun i ↦ eOf (seed + 5 * i.val.toUInt64)

/-- The first `j` coordinates of a point. -/
private def firstOf {n : ℕ} (c : Vector E n) (j : ℕ) : Vector E j :=
  Vector.ofFn fun i ↦ c[i.val]?.getD 0

/-- No oracle. -/
private def noO : ∀ i, NoOracle i := fun i ↦ i.elim0

/-! ## The sumcheck's bound tables -/

/-- Three tables on `n` variables and a cubic formula that reads the point. -/
private def cubic (n : ℕ) : Sumcheck.Virtual E Unit NoOracle Unit n 3 where
  tables := fun _ i ↦ tabE n (17 * i.val.toUInt64 + 1)
  formula := fun _ z v ↦ v[0] * v[1] * v[2] + (z.toList.headD 0) * v[0]

/-- The context. -/
private def ctx₀ : SumcheckRound.Ctx Unit NoOracle Unit := (((), noO), ())

/-- Four distinct nodes. -/
private def nodes : Fin 4 → E := TableSumcheck.nodes

/-- The prover with state's messages from stage `j` on, `k` rounds left, from the bound tables
`ts`, and the final values read off the tables bound on every coordinate. -/
private def chain {n m : ℕ} (V : Sumcheck.Virtual E Unit NoOracle Unit n m)
    (wt : Sumcheck.CoordWeights E Unit n) (cs : Vector E n) :
    (k j : ℕ) → Vector (CMlPolynomialEval E (n - j)) m →
      List (SumcheckRound.Message E 3) × Vector E m
  | 0, _, ts => ([], Vector.ofFn fun i ↦ ts[i][0]'(Nat.two_pow_pos _))
  | k + 1, j, ts =>
    let r := chain V wt cs k (j + 1) (Sumcheck.stepCache ts (cs[j]?.getD 0))
    (Sumcheck.roundFromCache V wt nodes ctx₀ j (firstOf cs j) ts :: r.1, r.2)

/-- The honest messages and values. -/
private def specMsgs {n m : ℕ} (V : Sumcheck.Virtual E Unit NoOracle Unit n m)
    (wt : Sumcheck.CoordWeights E Unit n) (cs : Vector E n) :
    List (SumcheckRound.Message E 3) × Vector E m :=
  ((List.range n).map fun j ↦ Sumcheck.roundPoly V wt nodes ctx₀ j (firstOf cs j),
    V.values ctx₀ cs.reverse)

-- Plain and normalized sumchecks of three tables, at every size up to four variables.
#guard (List.range 5).all fun n ↦
  chain (cubic n) Sumcheck.unitWeights (pt n 7) n 0 (Sumcheck.boundCache (cubic n) ctx₀ 0 #v[]) ==
    specMsgs (cubic n) Sumcheck.unitWeights (pt n 7)
#guard (List.range 4).all fun n ↦
  let wt : Sumcheck.CoordWeights E Unit n := Sumcheck.eqWeights fun _ ↦ pt n 9
  chain (cubic n) wt (pt n 11) n 0 (Sumcheck.boundCache (cubic n) ctx₀ 0 #v[]) ==
    specMsgs (cubic n) wt (pt n 11)

/-! ## The product trees -/

-- The levels built once are the tree's, past the leaves included.
#guard (List.range 5).all fun μ ↦ (List.range (μ + 2)).all fun k ↦
  (levelsOf (tabE μ 13)).get k == layerTable (tabE μ 13) k

/-- Three random trees of `2 ^ μ` leaves. -/
private def gkrLeaves (μ : ℕ) : Unit → (∀ i, NoOracle i) → Fin 3 → CMlPolynomialEval E μ :=
  fun _ _ s ↦ tabE μ (31 * s.val.toUInt64)

/-- A context of a step from layer `m`. -/
private def gkrCtx (m : ℕ) : Gkr.LayerCtx Unit E NoOracle 3 m :=
  (((((), (pt m 41, fun _ ↦ 0)), eOf 43), noO), ())

/-- The prover with state's messages of a layer's sumcheck from stage `j` on, and the children
read off the children bound on every coordinate. -/
private def gkrChain (ρ m : ℕ) (cs : Vector E m) : (k j : ℕ) →
    Vector (Vector (CMlPolynomialEval E (m - j)) (2 ^ ρ)) 3 →
      List (SumcheckRound.Message E (2 ^ ρ)) × List (Vector E (2 ^ ρ))
  | 0, j, B => ([], B.toList.map fun row ↦
      row.map fun t : Vector E (2 ^ (m - j)) ↦ t[0]'(Nat.two_pow_pos _))
  | k + 1, j, B =>
    let r := gkrChain ρ m cs k (j + 1) (Gkr.stepChildren 3 ρ m B (cs[j]?.getD 0))
    (Gkr.roundFromBound (gkrCtx m) j B :: r.1, r.2)

/-- The honest messages and children. -/
private def gkrSpec (μ ρ m : ℕ) (cs : Vector E m) :
    List (SumcheckRound.Message E (2 ^ ρ)) × List (Vector E (2 ^ ρ)) :=
  ((List.range m).map fun j ↦ Gkr.roundPoly 3 μ (gkrLeaves μ) ρ m (gkrCtx m) j (firstOf cs j),
    (List.finRange 3).map fun s ↦ Gkr.children 3 μ (gkrLeaves μ) ρ m () noO cs s)

-- Radix-four steps at layers `0, 1, 2`, binary steps at layers `0, 3`.
#guard [(4, 2, 2), (3, 2, 1), (2, 2, 0), (4, 1, 3), (1, 1, 0)].all fun (μ, ρ, m) ↦
  gkrChain ρ m (pt m 47) m 0
      (Gkr.boundChildren 3 ρ m (Gkr.treesOf 3 μ (gkrLeaves μ) () noO) 0 #v[]) ==
    gkrSpec μ ρ m (pt m 47)

/-! ## Runs -/

/-- Uniform samples read off the words of a xorshift. -/
private def xsImpl : QueryImpl unifSpec (StateM UInt64) :=
  fun n st ↦ (Fin.ofNat (n + 1) st.toNat, xs st)

/-- Run a prover at the challenges a xorshift draws from `seed`. -/
private def runAt {S W S' W' : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] (P : Prover []ₒ S W S' W' pSpec) (s : S) (w : W)
    (seed : UInt64) : pSpec.FullTranscript × S' × W' :=
  (simulateQ xsImpl
    (simulateQ (QueryImpl.add (fun t ↦ isEmptyElim t) challengeQueryImpl) (P.run s w))).run' seed

open LeanerVMTests.Protocol.Bus in
/-- The bus phase's output at a seed, by a prover: the point, the totals, the boundary values. -/
private def busRun (P : OracleProver []ₒ busToy.Stmt (TheOracle busToy) Unit
    (busToy.Stmt × BusOut busToy) (TheOracle busToy) Unit (busSpec busToy)) (q : Column busToy.μ)
    (seed : UInt64) : List E :=
  let o := (runAt P ((), fun _ ↦ q) () seed).2.1.1.2
  o.point.toList ++ [o.totals 0, o.totals 1, o.totals 2] ++ o.columns.toList.map (·.value)

/-- A stack of the bus tests' instance that is not honest. -/
private def wild : Column 2 := ⟨Vector.ofFn fun i ↦ kOf (23 + i.val.toUInt64)⟩

open LeanerVMTests.Protocol.Bus in
-- The cached bus phase against the honest one, on the honest stack and another, at two seeds.
#guard [honest, wild].all fun q ↦ [3, 5].all fun seed ↦
  busRun (Bus.busCached busToy conditions).toProver q seed ==
    busRun (busPhase busToy conditions).toDef.red.prover q seed

open LeanerVMTests.Protocol.Bus in
/-- The table sumcheck's output on the bus phase's, by a prover: the column claims' values. -/
private def tableRun (P : OracleProver []ₒ (busToy.Stmt × BusOut busToy) (TheOracle busToy)
    Unit (busToy.Stmt × TableOut busToy) (TheOracle busToy) Unit (tableSpec busToy))
    (seed : UInt64) : List E :=
  let bus := (runAt (Bus.busCached busToy conditions).toProver ((), fun _ ↦ honest) () seed).2.1
  (runAt P bus () (seed + 1)).2.1.1.2.columns.toList.map (·.value)

open LeanerVMTests.Protocol.Bus in
#guard [3, 5].all fun seed ↦
  tableRun (TableSumcheck.tableCached busToy).toProver seed ==
    tableRun (TableSumcheck.tableSumcheck busToy).toDef.red.prover seed

/-! ## Mutations -/

/-- The sumcheck's tables bound at the lowest coordinate instead of the highest. -/
private def stepLow {n m j : ℕ} (ts : Vector (CMlPolynomialEval E (n - j)) m) (a : E) :
    Vector (CMlPolynomialEval E (n - (j + 1))) m :=
  if hj : j < n then (Sumcheck.nextTables hj ts).map fun t ↦ bindLow t a
  else Vector.replicate m (Vector.replicate _ 0)

/-- The chain with the mutated step. -/
private def chainLow {n m : ℕ} (V : Sumcheck.Virtual E Unit NoOracle Unit n m)
    (cs : Vector E n) : (k j : ℕ) → Vector (CMlPolynomialEval E (n - j)) m →
      List (SumcheckRound.Message E 3)
  | 0, _, _ => []
  | k + 1, j, ts => Sumcheck.roundFromCache V Sumcheck.unitWeights nodes ctx₀ j (firstOf cs j) ts ::
    chainLow V cs k (j + 1) (stepLow ts (cs[j]?.getD 0))

#guard chainLow (cubic 3) (pt 3 7) 3 0 (Sumcheck.boundCache (cubic 3) ctx₀ 0 #v[]) !=
  (specMsgs (cubic 3) Sumcheck.unitWeights (pt 3 7)).1

end LeanerVMTests.Protocol.StatefulProvers
