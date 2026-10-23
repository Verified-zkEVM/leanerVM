/-
  LeanerVMBench

  Steady-state timings of the field arithmetic, the BLAKE2s hasher, a Merkle root and a
  multilinear evaluation, the sumcheck provers' round messages, one-shot timings of the honest
  provers' tables (the Lagrange basis, the leanISA stack, the bus leaves, a grand-product layer),
  and runs of the honest provers through ArkLib's `Prover.run`, as compiled into the
  `leanervm-bench` executable.
-/

import LeanerVM.Protocol.Field
import LeanerVM.Protocol.Merkle
import LeanerVM.Protocol.Stack
import LeanerVM.Protocol.TableSumcheck
import LeanerVM.Protocol.ToArkLib.ProductSumcheck
import LeanerVM.Protocol.LeanIsa
import LeanerVM.Protocol.HonestProver
import LeanerVM.Protocol.ToArkLib.AppendLazy
import LeanerVMTests.Arithmetization.Statement

/-!
# The `leanervm-bench` executable

Each arithmetic workload runs a fixed number of iterations, scaled by the first argument, a
percentage (default `100`), on inputs derived from the seed in `LEANERVM_BENCH_SEED` (default
`12345`), so that nothing is evaluated at compile time. Each sumcheck workload computes the honest
prover's message of every round once, at the log-sizes up to `LEANERVM_BENCH_MAXLOG` (default
`20`); the specification's algorithm runs at small sizes beside it. The second argument selects
the group: `arith`, `sumcheck`, `provers` or `all` (the default), or `runs` and `protocol`, which
run provers through ArkLib's `Prover.run` with challenges drawn by `IO.rand`. Each prover workload
runs once, at the sizes in its name; a third argument keeps only the prover workloads whose name
contains it, and for `protocol` names the last phase run. Every result feeds a printed checksum,
and every timed value is passed through the opaque `force` inside the timed interval. See
`bench/README.md`.
-/

namespace LeanerVMBench

open LeanerVM.Parameters LeanerVM.Protocol CompPoly CPoly

/-- A xorshift step, for inputs the compiler cannot precompute. -/
def xs (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A `K` word from a seed. -/
def kOf (s : UInt64) : K := BF64.ofBitVec s.toBitVec

/-- An `E` element from a seed. -/
def eOf (s : UInt64) : E := E.ofLimbs (kOf s) (kOf (xs s)) (kOf (xs (xs s)))

/-- Return a value through an opaque call, so that its computation stays inside the timed
interval. -/
@[noinline] def force {α : Type} (x : α) : IO α := pure x

/-- Print one result line: nanoseconds per operation and a checksum. -/
def report (name : String) (iters : Nat) (t0 t1 : Nat) (check : String) : IO Unit := do
  let ns := (t1 - t0).toFloat / iters.toFloat
  IO.println s!"{name}\t{ns} ns/op\t{iters} iterations\t[{check}]"

/-- Time `iters` runs of a step on an accumulator. -/
def timeLoop {α : Type} (name : String) (iters : Nat) (init : α) (step : Nat → α → α)
    (show_ : α → String) : IO Unit := do
  let mut acc ← force init
  let t0 ← IO.monoNanosNow
  for i in [0:iters] do
    acc ← force (step i acc)
  let t1 ← IO.monoNanosNow
  report name iters t0 t1 (show_ acc)

/-- Time one run of a computation, in seconds. Its argument comes from an opaque call made
after the clock starts, so that the computation cannot be hoisted out of the interval. -/
def timeOnceR {α : Type} (name : String) (f : Unit → α) (show_ : α → String) : IO α := do
  let t0 ← IO.monoNanosNow
  let u ← force ()
  let r ← force (f u)
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}\t{(t1 - t0).toFloat / 1e9} s\t1 run\t[{show_ r}]"
  (← IO.getStdout).flush
  pure r

/-- `timeOnceR`, the value dropped. -/
def timeOnce {α : Type} (name : String) (f : Unit → α) (show_ : α → String) : IO Unit :=
  discard <| timeOnceR name f show_

/-- The sum of a table's entries, as a checksum. -/
def sumTable {R : Type} [Add R] [Zero R] {n : ℕ} (t : Vector R n) : R := t.foldl (· + ·) 0

/-- The inverse through a field dictionary, the way generic code such as interpolation reaches
it. -/
@[noinline, nospecialize] def fieldInv {R : Type} [Field R] (x : R) : R := x⁻¹

/-- Bytes from a seed. -/
def bytesOf (seed : UInt64) (len : Nat) : List UInt8 :=
  (List.range len).map fun i ↦ (xs (seed + i.toUInt64)).toUInt8

/-- The arithmetic workloads, with iteration counts scaled to `percent` per cent. -/
def runArith (seed : UInt64) (percent : Nat) : IO Unit := do
  let n (base : Nat) : Nat := max 1 (base * percent / 100)
  let kHex (a : K) : String := a.toBitVec.toHex
  -- K
  let b := kOf (xs seed)
  timeLoop "K mul" (n 1000000) (kOf seed) (fun _ a ↦ a * b) kHex
  timeLoop "K inv" (n 100000) (kOf seed) (fun _ a ↦ (a + b)⁻¹) kHex
  let bw := xs seed
  timeLoop "K mul on words" (n 1000000) seed (fun _ a ↦ FastBF64.mulWord a bw) toString
  -- E
  let be := eOf (xs (xs (xs seed)))
  timeLoop "E add" (n 1000000) (eOf seed) (fun _ a ↦ a + be) toString
  timeLoop "E mul" (n 100000) (eOf seed) (fun _ a ↦ a * be) toString
  timeLoop "E inv" (n 1000) (eOf seed) (fun _ a ↦ (a + be)⁻¹) toString
  timeLoop "E inv (Field dictionary)" (n 1000) (eOf seed) (fun _ a ↦ fieldInv (a + be)) toString
  -- BLAKE2s
  for len in [64, 512] do
    let data ← force (bytesOf seed len)
    timeLoop s!"BLAKE2s {len} B" (n (if len = 64 then 20000 else 3000))
      (Blake2sHash.blake2sBytes data)
      (fun _ d ↦ Blake2sHash.blake2sBytes (d[0].toUInt8 :: data.tail)) (fun d ↦ toString d[0])
  -- Merkle root over 2^12 rows of 8 words
  let leaves : Vector (List K) (2 ^ 12) ← force <| Vector.ofFn fun i ↦
    (List.range 8).map fun j ↦ kOf (xs (seed + (i.val * 8 + j).toUInt64))
  timeLoop "Merkle root 2^12 rows x 8 K" (n 2) (0 : UInt32)
    (fun i acc ↦ acc ^^^ (merkleRoot (leaves.set 0 [kOf (seed + i.toUInt64)]))[0])
    toString
  -- evalMle of a 2^16 E-table at an E point
  let table : CMlPolynomialEval E 16 ← force <|
    CMlPolynomialEval.mk 16 (Vector.ofFn fun i ↦ eOf (xs (seed + i.val.toUInt64)))
  let point : Vector E 16 ← force <| Vector.ofFn fun i ↦ eOf (xs (xs (seed * 3 + i.val.toUInt64)))
  timeLoop "evalMle 2^16 E-table" (n 2) (0 : E)
    (fun i acc ↦ acc + CMlPolynomialEval.evalMle table (point.set 0 (point[0] + eOf i.toUInt64)))
    toString

/-! ## Sumcheck provers -/

open Sumcheck in
/-- The specification's round polynomial: `roundPoly`'s body, compiled here, where it names
`claim`, which no `@[csimp]` theorem replaces. -/
def specRoundPoly {X ι : Type} {O : ι → Type} {W : Type} {n m d : ℕ}
    (V : Virtual E X O W n m) (wt : CoordWeights E X n) (nodes : Fin (d + 1) → E)
    (ctx : SumcheckRound.Ctx X O W) (j : ℕ) (c : Vector E j) : SumcheckRound.Message E d :=
  if j < n then
    SumcheckRound.ofCPolynomial d (CPolynomial.CLagrange.interpolate Finset.univ nodes
      fun i ↦ claim V wt ctx (j + 1) (c.push (nodes i)))
  else SumcheckRound.ofCPolynomial d 0

/-- The specification's product round polynomial: the three coefficient sums. -/
def specProductRound {n : ℕ} (A B : CMlPolynomialEval E n) (j : ℕ) (c : Vector E j) :
    SumcheckRound.Message E 2 :=
  if h : j < n then
    #v[ProductSum.coef0 A B h c, ProductSum.coef1 A B h c, ProductSum.coef2 A B h c]
  else #v[0, 0, 0]

/-- `E` challenges from a seed. -/
def chalsOf (seed : UInt64) (k : Nat) : Array E :=
  (Array.range k).map fun i ↦ eOf (xs (seed * 7 + i.toUInt64 + 1))

/-- The first `j` challenges: the honest prover's input at round `j`. -/
def firstChals (cs : Array E) (j : Nat) : Vector E j := Vector.ofFn fun i ↦ cs[i.val]!

/-- A table of `E` values on `n` variables from a seed. -/
def tableOf (seed : UInt64) (n : Nat) : CMlPolynomialEval E n :=
  CMlPolynomialEval.mk n (Vector.ofFn fun i ↦ eOf (xs (seed + i.val.toUInt64 * 3)))

/-- Time the honest messages of rounds `0, …, rounds - 1`, one message each, and print the total
with a checksum: the sum of every coefficient. -/
def timeRounds {d : Nat} (name : String) (rounds : Nat) (msg : Nat → Vector E (d + 1)) :
    IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc : E := 0
  for j in [0:rounds] do
    let q ← force (msg j)
    acc := acc + q.toArray.foldl (· + ·) 0
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}\t{(t1 - t0).toFloat / 1e6} ms for {rounds} rounds\t[{acc}]"

/-- No oracle. -/
def noO : ∀ i, NoOracle i := fun i ↦ i.elim0

/-- The context of a sumcheck with no public data, oracle or witness. -/
def unitCtx : SumcheckRound.Ctx Unit NoOracle Unit := (((), noO), ())

/-- The virtual polynomial `t₀ · t₁ · t₂` of three tables: degree three, as the table sumcheck's. -/
def cubic {n : Nat} (ts : Fin 3 → CMlPolynomialEval E n) :
    Sumcheck.Virtual E Unit NoOracle Unit n 3 where
  tables := fun _ ↦ ts
  formula := fun _ _ v ↦ v[0] * v[1] * v[2]

/-! ### A table sumcheck instance: one table of `2 ^ n` rows, four columns -/

/-- The table's shape. -/
abbrev benchShape (n : Nat) : Shape := ⟨1, fun _ ↦ n, fun _ ↦ 4⟩

/-- One block per column, all of height `2 ^ n`. -/
def benchBlocks (n : Nat) : Blocks := ⟨4, fun _ ↦ n, fun _ _ _ ↦ le_rfl⟩

theorem benchBlocks_total (n : Nat) : (benchBlocks n).total ≤ 2 ^ (n + 2) := by
  rw [Blocks.total_eq_sum]
  show ∑ _b : Fin 4, 2 ^ n ≤ 2 ^ (n + 2)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, pow_add]
  omega

/-- Column `i` is block `i` of the stack of `2 ^ (n + 2)` cells. -/
def benchLayout (n : Nat) :
    Layout (n + 2) (benchShape n).ColumnId (fun c ↦ (benchShape n).τ c.1) :=
  ((benchBlocks n).layout (benchBlocks_total n)).comap (fun c ↦ c.2) fun _ ↦ rfl

/-- The row polynomials: a Boolean column, two products, and the form's column. -/
def benchPolys : List (CMvPolynomial 4 K) :=
  [CMvPolynomial.X 0 * CMvPolynomial.X 0 - CMvPolynomial.X 0,
    CMvPolynomial.X 0 * CMvPolynomial.X 1 - CMvPolynomial.X 2,
    CMvPolynomial.X 3 * CMvPolynomial.X 1 + CMvPolynomial.X 2,
    CMvPolynomial.X 1]

/-- The largest total degree of a list of polynomials. -/
def maxDegree {w : Nat} (ps : List (CMvPolynomial w K)) : Nat :=
  ps.foldr (fun p a ↦ max p.totalDegree a) 0

theorem le_maxDegree {w : Nat} : ∀ {ps : List (CMvPolynomial w K)} {p : CMvPolynomial w K},
    p ∈ ps → p.totalDegree ≤ maxDegree ps
  | q :: qs, p, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (le_maxDegree h).trans (le_max_right _ _)

/-- The instance: one table of log-height `n` with the three constraints of `benchPolys`. -/
abbrev benchInst (n : Nat) : M3Instance where
  toShape := benchShape n
  Stmt := Unit
  constraints := fun _ ↦ benchPolys.take 3
  flushes := fun _ ↦ []
  d := maxDegree benchPolys
  constraints_degree := fun _ _ h ↦ le_maxDegree (List.mem_of_mem_take h)
  flushes_degree := fun _ _ h ↦ absurd h List.not_mem_nil
  counts := fun _ ↦ []
  boundary := []
  μ := n + 2
  layout := benchLayout n
  nLines := 0
  publicLines := fun _ ↦ #v[]
  flock := none

/-- The bus phase's output, by hand: a point, one push form `w · X₁`, and a total. -/
def benchBusOut (n : Nat) (seed : UInt64) : BusOut (benchInst n) where
  point := Vector.ofFn fun i ↦ eOf (xs (seed + 101 * i.val.toUInt64))
  forms := fun s _ ↦ if s.val = 0 then
    [(eOf (seed + 5), ⟨CMvPolynomial.X 1, le_maxDegree (by simp [benchPolys])⟩)] else []
  totals := fun _ ↦ eOf (seed + 9)
  columns := #v[]

/-- The table sumcheck's context on a random stack. -/
def benchTableCtx (n : Nat) (seed : UInt64) :
    SumcheckRound.Ctx (TableSumcheck.Data (benchInst n)) (TheOracle (benchInst n)) Unit :=
  let q : Column (n + 2) := ⟨Vector.ofFn fun i ↦ kOf (xs (seed + i.val.toUInt64))⟩
  (((((), benchBusOut n seed), eOf (seed + 77)), fun _ ↦ q), ())

/-- The messages of rounds `j, …` of a sumcheck from its bound tables `ts`, the tables bound to
each challenge in turn (the prover with state), every coefficient summed into `acc`. -/
def chainSum {X ι : Type} {O : ι → Type} {W : Type} {n m d : ℕ}
    (V : Sumcheck.Virtual E X O W n m) (wt : Sumcheck.CoordWeights E X n)
    (nodes : Fin (d + 1) → E) (ctx : SumcheckRound.Ctx X O W) (cs : Array E) :
    (k j : ℕ) → Vector (CMlPolynomialEval E (n - j)) m → E → E
  | 0, _, _, acc => acc
  | k + 1, j, ts, acc =>
    let q := Sumcheck.roundFromCache V wt nodes ctx j (firstChals cs j) ts
    chainSum V wt nodes ctx cs k (j + 1) (Sumcheck.stepCache ts cs[j]!)
      (acc + q.toArray.foldl (· + ·) 0)

/-- Time the messages of every round of a sumcheck with its bound tables carried, the tables
read off the context included, with `timeRounds`' checksum. -/
def timeChain {X ι : Type} {O : ι → Type} {W : Type} {n m d : ℕ} (name : String)
    (V : Sumcheck.Virtual E X O W n m) (wt : Sumcheck.CoordWeights E X n)
    (nodes : Fin (d + 1) → E) (ctx : SumcheckRound.Ctx X O W) (cs : Array E) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let u ← force ()
  let acc ← force (chainSum V wt nodes ctx cs n 0
    (Sumcheck.boundCache V ctx 0 (Vector.ofFn fun i : Fin 0 ↦ (fun _ ↦ i.elim0) u)) 0)
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}\t{(t1 - t0).toFloat / 1e6} ms for {n} rounds\t[{acc}]"

/-- The sumcheck workloads at log-sizes `ns`, and the specification's algorithm at `specNs`. -/
def runSumcheck (seed : UInt64) (ns specNs : List Nat) : IO Unit := do
  let cs := chalsOf seed 32
  let pt := chalsOf (seed + 3) 32
  -- The interpolation of one cubic round polynomial at the table sumcheck's four nodes.
  timeLoop "interpolate 4 nodes over E" 200 (0 : E)
    (fun i acc ↦ acc + (CPolynomial.CLagrange.interpolate Finset.univ TableSumcheck.nodes
      fun k ↦ cs[k.val + i % 8]!).coeff 3) toString
  for (n, spec) in (ns.map (·, false)) ++ (specNs.map (·, true)) do
    let tag := if spec then " (spec)" else ""
    let ts ← force fun i : Fin 3 ↦ tableOf (seed + 1000 * i.val.toUInt64) n
    let V := cubic ts
    let wtEq : Sumcheck.CoordWeights E Unit n := Sumcheck.eqWeights fun _ ↦ firstChals pt n
    timeRounds s!"Sumcheck.plain 2^{n} x 3 tables{tag}" n fun j ↦
      if spec then specRoundPoly V Sumcheck.unitWeights TableSumcheck.nodes unitCtx j
        (firstChals cs j)
      else Sumcheck.roundPoly V Sumcheck.unitWeights TableSumcheck.nodes unitCtx j
        (firstChals cs j)
    if !spec then
      timeChain s!"Sumcheck.plain 2^{n} x 3 tables, with state" V Sumcheck.unitWeights
        TableSumcheck.nodes unitCtx cs
    timeRounds s!"Sumcheck.normalized 2^{n} x 3 tables{tag}" n fun j ↦
      if spec then specRoundPoly V wtEq TableSumcheck.nodes unitCtx j (firstChals cs j)
      else Sumcheck.roundPoly V wtEq TableSumcheck.nodes unitCtx j (firstChals cs j)
    if !spec then
      timeChain s!"Sumcheck.normalized 2^{n} x 3 tables, with state" V wtEq TableSumcheck.nodes
        unitCtx cs
    timeRounds s!"ProductSum 2^{n}{tag}" n fun j ↦
      if spec then specProductRound (ts 0) (ts 1) j (firstChals cs j)
      else ProductSum.roundPoly (ts 0) (ts 1) j (firstChals cs j)
    let I := benchInst n
    let ctx ← force (benchTableCtx n seed)
    timeRounds s!"TableSumcheck 2^{n} rows x 4 columns{tag}" I.τmax fun j ↦
      if spec then
        specRoundPoly (TableSumcheck.tableSummand I) Sumcheck.unitWeights TableSumcheck.nodes ctx
          j (firstChals cs j)
      else
        Sumcheck.roundPoly (TableSumcheck.tableSummand I) Sumcheck.unitWeights
          TableSumcheck.nodes ctx j (firstChals cs j)
    if !spec then
      timeChain s!"TableSumcheck 2^{n} rows x 4 columns, with state"
        (TableSumcheck.tableSummand I) Sumcheck.unitWeights TableSumcheck.nodes ctx cs

/-! ## The honest provers' tables -/

section Provers

open LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol.LeanIsa CMlPolynomialEval
open LeanerVMTests.Arithmetization.Statement
open Air.Flat (EnsembleWitness)

/-- The hand-built leanISA witness of the constraint statement's tests. -/
def fillWitness : EnsembleWitness (leanIsaEnsemble fillProg) := fillW 1 g memCnt

/-- The witness's sizes with the memory log-size replaced by `logMem`: the stack and the bus
leaves grow with it, the memory cells past the witness's reading `0`. -/
def sizesAt (logMem : ℕ) : Sizes :=
  match Sizes.ofWitness fillWitness with
  | some s => { s with logMem := logMem + 1, logMem_pos := Nat.succ_pos _ }
  | none => ⟨logMem + 1, Nat.succ_pos _, fun _ ↦ 0⟩

/-- The leanISA instance at the BLAKE2s inhabitant of `FlockSpec`, built where it is bound: a
workload's timed computation reads it and does not build it. -/
@[noinline] def leanIsaAt (s : Sizes) : M3Instance :=
  leanIsaInstance Blake2sFlock.blake2sFlockSpec fillProg s

/-- Random tables of `2 ^ μ` leaves, one per tree. -/
def randomLeaves (seed : UInt64) (nside μ : ℕ) : Fin nside → CMlPolynomialEval E μ :=
  let t : Vector (CMlPolynomialEval E μ) nside :=
    Vector.ofFn fun s ↦ Vector.ofFn fun i ↦ eOf (xs (seed + (s.val * 2 ^ μ + i.val).toUInt64))
  fun s ↦ t[s]

/-- The messages of the last layer step of the grand-product argument on three random trees of
`2 ^ (m + 2)` leaves: its `m` sumcheck messages at random challenges, and the children. -/
def gkrLastLayer (seed : UInt64) (m : ℕ) (u : Unit) : E :=
  let tabs := randomLeaves seed 3 (m + 2)
  let leaves : Unit → (∀ i, NoOracle i) → Fin 3 → CMlPolynomialEval E (m + 2) := fun _ _ ↦ tabs
  let point : Vector E m := Vector.ofFn fun i ↦ eOf (xs (seed * 5 + i.val.toUInt64))
  let lam := eOf (xs (seed * 7))
  let ctx : Gkr.LayerCtx Unit E NoOracle 3 m :=
    ((((u, (point, fun _ ↦ 0)), lam), fun i ↦ i.elim0), ())
  let chal : Vector E m := Vector.ofFn fun i ↦ eOf (xs (seed * 11 + i.val.toUInt64))
  let msgs := (List.finRange m).map fun j ↦
    Gkr.roundPoly 3 (m + 2) leaves 2 m ctx j.val (Vector.ofFn fun i : Fin j.val ↦ chal[i.val])
  let ch := Gkr.children 3 (m + 2) leaves 2 m () (fun i ↦ i.elim0) chal
  (msgs.map sumTable).foldl (· + ·) 0 + sumTable (ch 0) + sumTable (ch 1) + sumTable (ch 2)

/-- The messages of rounds `j, …` of the last layer's sumcheck from the bound children, each
challenge bound in turn, and the children read off the children bound on every coordinate, every
entry summed into `acc`. -/
def gkrChainSum (m : ℕ) (ctx : Gkr.LayerCtx Unit E NoOracle 3 m) (chal : Vector E m) :
    (k j : ℕ) → Vector (Vector (CMlPolynomialEval E (m - j)) (2 ^ 2)) 3 → E → E
  | 0, j, B, acc => B.toList.foldl (fun a row ↦ row.toList.foldl
      (fun a (t : Vector E (2 ^ (m - j))) ↦ a + t[0]'(Nat.two_pow_pos _)) a) acc
  | k + 1, j, B, acc =>
    gkrChainSum m ctx chal k (j + 1) (Gkr.stepChildren 3 2 m B (chal[j]?.getD 0))
      (acc + sumTable (Gkr.roundFromBound ctx j B))

/-- `gkrLastLayer` with state: the trees' levels built once, the children of the level below
bound one challenge at a time. -/
def gkrLastLayerCached (seed : UInt64) (m : ℕ) (u : Unit) : E :=
  let tabs := randomLeaves seed 3 (m + 2)
  let leaves : Unit → (∀ i, NoOracle i) → Fin 3 → CMlPolynomialEval E (m + 2) := fun _ _ ↦ tabs
  let point : Vector E m := Vector.ofFn fun i ↦ eOf (xs (seed * 5 + i.val.toUInt64))
  let lam := eOf (xs (seed * 7))
  let ctx : Gkr.LayerCtx Unit E NoOracle 3 m :=
    ((((u, (point, fun _ ↦ 0)), lam), fun i ↦ i.elim0), ())
  let chal : Vector E m := Vector.ofFn fun i ↦ eOf (xs (seed * 11 + i.val.toUInt64))
  let T := Gkr.treesOf 3 (m + 2) leaves u (fun i ↦ i.elim0)
  gkrChainSum m ctx chal m 0 (Gkr.boundChildren 3 2 m T 0 #v[]) 0

/-- The prover workloads, each run once. -/
def runProvers (keep : String → Bool) (seed : UInt64) : IO Unit := do
  -- The Lagrange basis (the equality kernel's cube values) at an `E` point.
  for n in [16, 20] do
    let name := s!"lagrangeBasis 2^{n}"
    if keep name then
      let pt : Vector E n ← force <| Vector.ofFn fun i ↦ eOf (xs (seed + 77 + i.val.toUInt64))
      timeOnce name (fun _ ↦ sumTable (lagrangeBasis pt)) toString
  -- The leanISA stack of the hand-built witness.
  for lm in [11, 12, 13, 14] do
    let s := sizesAt lm
    let name := s!"stackOf leanISA 2^{leanIsaμ fillProg s} cells"
    if keep name then
      timeOnce name
        (fun _ ↦ sumTable (stackOf Blake2sFlock.blake2sFlockSpec fillProg s fillWitness).values)
        (fun a ↦ a.toBitVec.toHex)
  -- Of which the Flock region: `F.gen` of the witness's `BLAKE2S` rows, the Flock argument's.
  if keep "stackOf's Flock region" then
    let s := sizesAt 11
    timeOnce s!"stackOf's Flock region, 2^{s.τ 5} compressions"
      (fun _ ↦ sumTable (witnessColumn Blake2sFlock.blake2sFlockSpec fillProg s fillWitness
        flockCol))
      (fun a ↦ a.toBitVec.toHex)
  -- The BLAKE2s circuit compiled for its prover, and one block traced, on words and as bitsets.
  if keep "Flock circuit" then
    let c ← force (Blake2sCircuit.blake2sCircuit : ProductCircuit Blake2sCircuit.m)
    timeOnce "Flock circuit: gates" (fun _ ↦ c.gates.size) toString
    let pc ← timeOnceR "Flock circuit: compile" (fun _ ↦ ProductCircuit.compile c)
      fun pc ↦ toString (pc.gates.foldl (fun a g ↦ a ^^^ g.2.1.foldl (· ^^^ ·) 0) (0 : UInt64))
    let inp := Blake2sFlock.inputForm (fun i ↦ kOf (seed + i.val.toUInt64))
    timeOnce "Flock circuit: one block, on words" (fun _ ↦ pc.traceW inp)
      fun zw ↦ toString (zw.foldl (· ^^^ ·) (0 : UInt64))
    timeOnce "Flock circuit: one block, on bitsets" (fun _ ↦ c.trace inp)
      fun z ↦ toString ((ProductCircuit.wordsOf z).foldl (· ^^^ ·) (0 : UInt64))
  -- The bus leaves of the three sides, on a random stack of the instance's height.
  for lm in [0, 10, 14, 18] do
    let s := sizesAt lm
    let I := leanIsaAt s
    let name := s!"bus leaves leanISA 2^{I.μBus}"
    if keep name then
      let q : Column I.μ ← force ⟨Vector.ofFn fun i ↦ kOf (xs (seed * 19 + i.val.toUInt64))⟩
      let α : Fin 4 → E := fun i ↦ eOf (xs (seed * 13 + i.val.toUInt64))
      let β := eOf (xs (seed * 17))
      timeOnce name (fun _ ↦ sumTable (Bus.sideLeaves I 0 α β q) +
        sumTable (Bus.sideLeaves I 1 α β q) + sumTable (Bus.sideLeaves I 2 α β q)) toString
    -- A cube point and its index, generic and over `E` (what `Layout.readWith` compiles to):
    -- most of a cell read.
    let name := s!"cube point and index, generic, 2^{s.logMem} x 22 coordinates"
    if keep name then
      timeOnce name (fun _ ↦ (List.range (2 ^ s.logMem)).foldl (fun acc x ↦
        acc + (boolIndex (boolVec (⟨x % 2 ^ 22, Nat.mod_lt _ (by norm_num)⟩ : Fin (2 ^ 22)) :
          Vector E 22)).val) 0) toString
    let name := s!"cube point and index over E, 2^{s.logMem} x 22 coordinates"
    if keep name then
      timeOnce name (fun _ ↦ (List.range (2 ^ s.logMem)).foldl (fun acc x ↦
        acc + (boolIndexE (boolVecE (⟨x % 2 ^ 22, Nat.mod_lt _ (by norm_num)⟩ : Fin (2 ^ 22)) :
          Vector E 22)).val) 0) toString
    -- One memory column read off that stack through the layout.
    let name := s!"column read leanISA 2^{s.logMem} cells"
    if keep name then
      let q : Column I.μ ← force ⟨Vector.ofFn fun i ↦ kOf (xs (seed * 23 + i.val.toUInt64))⟩
      timeOnce name (fun _ ↦ sumTable (I.column q (memCol 0)).values) (fun a ↦ a.toBitVec.toHex)
  -- One grand-product layer.
  for m in [6, 10, 14, 18] do
    let name := s!"GKR last layer 3 trees 2^{m + 2}"
    if keep name then
      timeOnce name (gkrLastLayer seed m) toString
    let name := s!"GKR last layer 3 trees 2^{m + 2}, with state"
    if keep name then
      timeOnce name (gkrLastLayerCached seed m) toString

/-! ## The honest provers, run -/

open OracleComp OracleSpec ProtocolSpec in
/-- Run a prover through ArkLib's `Prover.run`, its challenges drawn by `IO.rand` (VCVio's
`OracleComp.runIO`). -/
def runProver {S W S' W' : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] (P : Prover []ₒ S W S' W' pSpec) (s : S) (w : W) :
    IO (pSpec.FullTranscript × S' × W') :=
  simulateQ (spec := unifSpec) (fun n ↦ Fin.ofNat (n + 1) <$> (IO.rand 0 n).toIO)
    (simulateQ (QueryImpl.add (fun t ↦ isEmptyElim t) challengeQueryImpl) (P.run s w))

/-- Time one run of a prover, the random generator seeded first, so that two provers timed at the
same seed draw the same challenges. -/
def timeProver {α : Type} (name : String) (seed : ℕ) (act : Unit → IO α) (show_ : α → String) :
    IO α := do
  IO.setRandSeed seed
  let t0 ← IO.monoNanosNow
  let r ← act (← force ())
  let t1 ← IO.monoNanosNow
  let c ← force (show_ r)
  let t2 ← IO.monoNanosNow
  IO.println s!"{name}\t{(t1 - t0).toFloat / 1e9} s\t1 run\t[{c}]\tchecksum {(t2 - t1).toFloat / 1e9} s"
  (← IO.getStdout).flush
  pure r

/-- Run a step and print its wall-clock time, everything it builds included. -/
def wall {α : Type} (name : String) (act : IO α) : IO α := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}: {(t1 - t0).toFloat / 1e9} s wall-clock"
  (← IO.getStdout).flush
  pure r

/-- The sum of the values of column claims, as a checksum. -/
def claimSum {I : M3Instance} {k : ℕ} (cs : Vector (ColumnClaim I) k) : E :=
  cs.toList.foldl (fun a c ↦ a + c.value) 0

/-- A checksum of the bus phase's output: the point, the totals, the boundary values. -/
def busSum {I : M3Instance} (b : BusOut I) : E :=
  sumTable b.point + b.totals 0 + b.totals 1 + b.totals 2 + claimSum b.columns

/-- The bus phase's provers on the statement and the stack: the one with state, and the honest
one when `spec` holds. Returns the output of the one with state. -/
def runBus (I : M3Instance) (h : Bus.Conditions I) (sd : ℕ) (tag : String) (spec : Bool)
    (x : I.Stmt × ∀ i, TheOracle I i) : IO ((I.Stmt × BusOut I) × ∀ i, TheOracle I i) := do
  let r ← timeProver s!"bus phase, with state, {tag}" sd
    (fun _ ↦ runProver (Bus.busCached I h).toProver x ()) fun r ↦ toString (busSum r.2.1.1.2)
  if spec then
    discard <| timeProver s!"bus phase, honest (spec), {tag}" sd
      (fun _ ↦ runProver (busPhase I h).toDef.red.prover x ())
      fun r ↦ toString (busSum r.2.1.1.2)
  pure r.2.1

/-- The table sumcheck's provers. -/
def runTable (I : M3Instance) (sd : ℕ) (tag : String) (spec : Bool)
    (x : (I.Stmt × BusOut I) × ∀ i, TheOracle I i) :
    IO ((I.Stmt × TableOut I) × ∀ i, TheOracle I i) := do
  let r ← timeProver s!"table sumcheck, with state, {tag}" sd
    (fun _ ↦ runProver (TableSumcheck.tableCached I).toProver x ())
    fun r ↦ toString (claimSum r.2.1.1.2.columns)
  if spec then
    discard <| timeProver s!"table sumcheck, honest (spec), {tag}" sd
      (fun _ ↦ runProver (TableSumcheck.tableSumcheck I).toDef.red.prover x ())
      fun r ↦ toString (claimSum r.2.1.1.2.columns)
  pure r.2.1

/-- The public-input phase's honest prover. -/
def runPub (I : M3Instance) (sd : ℕ) (tag : String)
    (x : (I.Stmt × TableOut I) × ∀ i, TheOracle I i) :
    IO ((I.Stmt × PubOut I) × ∀ i, TheOracle I i) := do
  let r ← timeProver s!"public input, honest, {tag}" sd
    (fun _ ↦ runProver (deployedPublicInputPhase I).toDef.red.prover x ())
    fun r ↦ toString (claimSum r.2.1.1.2.columns)
  pure r.2.1

/-- The Flock phase's honest prover. -/
def runFlock (I : M3Instance) (sd : ℕ) (tag : String)
    (x : (I.Stmt × PubOut I) × ∀ i, TheOracle I i) :
    IO ((I.Stmt × FlockOut I) × ∀ i, TheOracle I i) := do
  let r ← timeProver s!"Flock phase, honest, {tag}" sd
    (fun _ ↦ runProver (flockPhase I).toDef.red.prover x ())
    fun r ↦ toString (claimSum r.2.1.1.2.columns +
      r.2.1.1.2.weighted.toList.foldl (fun a c ↦ a + c.value) 0)
  pure r.2.1

/-- The opening's honest prover. -/
def runOpening (I : M3Instance) (sd : ℕ) (tag : String)
    (x : (I.Stmt × FlockOut I) × ∀ i, TheOracle I i) : IO Unit :=
  discard <| timeProver s!"opening, honest, {tag}" sd
    (fun _ ↦ runProver (openingPhase I).red.prover x ()) fun _ ↦ "-"

/-- The whole protocol's provers. -/
def runWhole (I : M3Instance) (h : Bus.Conditions I) (sd : ℕ) (tag : String) (spec : Bool)
    (stmt : I.Stmt) (q : Column I.μ) : IO Unit := do
  discard <| timeProver s!"whole protocol, with state, {tag}" sd
    (fun _ ↦ runProver (leanVmFastProver I h) (stmt, fun i ↦ i.elim0) q) fun _ ↦ "-"
  if spec then
    discard <| timeProver s!"whole protocol, honest (spec), {tag}" sd
      (fun _ ↦ runProver (leanVmProver (leanVmPhases I h)) (stmt, fun i ↦ i.elim0) q)
      fun _ ↦ "-"

/-- `k` trivial sumcheck rounds, whose schedule is appended on the right once per round. -/
def trivialRounds (k : ℕ) :=
  SumcheckRound.rounds (F := E) (X := Unit) (O := NoOracle) (W := Unit) (d := 0)
    (fun _ _ _ ↦ #v[0]) (fun _ _ ↦ []) k k 0 (Nat.zero_add k)

/-- ArkLib's `Prover.run` of a plain sumcheck of three tables, with state and stateless, at
`n` variables: the run's cost beside its messages'. -/
def runSumcheckProver (seed : UInt64) (n : ℕ) : IO Unit := do
  let ts ← force fun i : Fin 3 ↦ tableOf (seed + 1000 * i.val.toUInt64) n
  let V := cubic ts
  let x : SumcheckRound.Stmt Unit E 0 × ∀ i, NoOracle i := (((), (#v[], 0)), noO)
  discard <| timeProver s!"Prover.run, plain sumcheck 2^{n} x 3 tables, with state" 7
    (fun _ ↦ runProver (Sumcheck.cachedWeighted V Sumcheck.unitWeights TableSumcheck.nodes).toProver
      x ()) fun r ↦ toString (sumTable r.2.1.1.2.2)
  discard <| timeProver s!"Prover.run, plain sumcheck 2^{n} x 3 tables, stateless" 7
    (fun _ ↦ runProver (Sumcheck.weighted V Sumcheck.unitWeights TableSumcheck.nodes).red.prover
      x ()) fun r ↦ toString (sumTable r.2.1.1.2.2)

/-- The leanISA instance's phases at memory log-size `lm + 1`, run one after the other, each
prover with state on the output of the one before, and the honest provers of `leanVmPhases`
beside them on the same input when `spec` holds; the phases after `last` are skipped. Then the
whole protocol's provers, when `whole` holds. The checksums of the two provers of a phase
agree. -/
def runProtocol (seed : UInt64) (lm : ℕ) (spec whole : Bool) (last : String) : IO Unit := do
  let s := sizesAt lm
  let I := leanIsaAt s
  let h : Bus.Conditions I := leanIsa_conditions Blake2sFlock.blake2sFlockSpec fillProg s
  let q : Column I.μ ← timeProver "the stack" 0
    (fun _ ↦ force (stackOf Blake2sFlock.blake2sFlockSpec fillProg s fillWitness))
    fun q ↦ (sumTable q.values).toBitVec.toHex
  let stmt : I.Stmt := ⟨fun i ↦ kOf (xs (seed + 31 * i.val.toUInt64))⟩
  let tag := s!"leanISA 2^{I.μ} cells, 2^{I.μBus} leaves, tau_max {I.τmax}"
  IO.println s!"instance: {tag}"
  (← IO.getStdout).flush
  let sd := seed.toNat
  let bus ← wall "bus phase" (runBus I h sd tag spec (stmt, fun _ ↦ q))
  if last == "bus" then return
  let tab ← wall "table sumcheck" (runTable I (sd + 1) tag spec bus)
  if last == "table" then return
  let pub ← wall "public input" (runPub I (sd + 2) tag tab)
  if last == "pub" then return
  let flk ← wall "Flock phase" (runFlock I (sd + 3) tag pub)
  if last == "flock" then return
  wall "opening" (runOpening I (sd + 4) tag flk)
  if whole then wall "whole protocol" (runWhole I h (sd + 5) tag spec stmt q)

end Provers

end LeanerVMBench

/-- `leanervm-bench [percent] [group] [filter] [lm] [spec]`: run the workloads of `group` (`arith`,
`sumcheck`, `provers` or `all`, the default; or `runs`, or `protocol` up to the phase `filter`, at
memory log-size `lm + 1`, the stateless provers beside when the fifth argument is `spec`),
arithmetic iteration counts scaled to `percent` per cent (default `100`), keeping only the prover
workloads whose name contains `filter`. -/
def main (args : List String) : IO Unit := do
  let seed : UInt64 := ((← IO.getEnv "LEANERVM_BENCH_SEED").getD "12345").toNat!.toUInt64
  let maxLog := ((← IO.getEnv "LEANERVM_BENCH_MAXLOG").getD "20").toNat!
  let percent := ((args.head?.bind String.toNat?).getD 100)
  let group := (args.drop 1).head?.getD "all"
  let filter := (args.drop 2).head?.getD ""
  let keep (name : String) : Bool := filter.isEmpty || (name.splitOn filter).length > 1
  IO.println s!"leanervm-bench: seed {seed}, {percent}% of the base iteration counts, {group}"
  if group == "all" || group == "arith" then LeanerVMBench.runArith seed percent
  if group == "all" || group == "sumcheck" then
    LeanerVMBench.runSumcheck seed ([4, 6, 8, 12, 16, 20].filter (· ≤ maxLog)) [4, 6, 8]
  if group == "all" || group == "provers" then LeanerVMBench.runProvers keep seed
  if group == "runs" then
    -- `runs`: ArkLib's `Prover.run` of trivial sumcheck rounds, and of a plain sumcheck with
    -- state and without.
    for k in [4, 8, 16, 32] do
      discard <| LeanerVMBench.timeProver s!"Prover.run, {k} trivial sumcheck rounds" 3
        (fun _ ↦ LeanerVMBench.runProver (LeanerVMBench.trivialRounds k).red.prover
          (((), (#v[], 0)), LeanerVMBench.noO) ())
        fun r ↦ toString (r.2.1.1.2.1.toList.foldl (· + ·) 0)
    for n in [4, 8, 12, 16] do LeanerVMBench.runSumcheckProver seed n
  if group == "protocol" then
    -- `protocol`: the leanISA phases' provers up to the phase named by the filter (`bus`,
    -- `table`, `pub`, `flock`, or `whole` for every phase and the whole protocol), at memory
    -- log-size `lm + 1` (the fourth argument, default `15`, the smallest admissible), the honest
    -- provers beside them when the fifth argument is `spec`.
    let lm := ((args.drop 3).head?.bind String.toNat?).getD 15
    let spec := (args.drop 4).head? == some "spec"
    LeanerVMBench.runProtocol seed lm spec (filter == "whole") filter
