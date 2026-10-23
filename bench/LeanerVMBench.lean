/-
  LeanerVMBench

  Steady-state timings of the field arithmetic, the BLAKE2s hasher, a Merkle root, a
  multilinear evaluation and the sumcheck provers' round messages, as compiled into the
  `leanervm-bench` executable.
-/

import LeanerVM.Protocol.Field
import LeanerVM.Protocol.Merkle
import LeanerVM.Protocol.Stack
import LeanerVM.Protocol.TableSumcheck
import LeanerVM.Protocol.ToArkLib.ProductSumcheck

/-!
# The `leanervm-bench` executable

Each arithmetic workload runs a fixed number of iterations, scaled by the first argument, a
percentage (default `100`), on inputs derived from the seed in `LEANERVM_BENCH_SEED` (default
`12345`), so that nothing is evaluated at compile time. Each sumcheck workload computes the honest
prover's message of every round once, at the log-sizes up to `LEANERVM_BENCH_MAXLOG` (default
`20`); the specification's algorithm runs at small sizes beside it. The second argument selects
the group: `arith`, `sumcheck` or `all` (the default). Every result feeds a printed checksum, and
every timed value is passed through the opaque `force` inside the timed interval. See
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
    timeRounds s!"Sumcheck.normalized 2^{n} x 3 tables{tag}" n fun j ↦
      if spec then specRoundPoly V wtEq TableSumcheck.nodes unitCtx j (firstChals cs j)
      else Sumcheck.roundPoly V wtEq TableSumcheck.nodes unitCtx j (firstChals cs j)
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

end LeanerVMBench

/-- `leanervm-bench [percent] [group]`: run the workloads of `group` (`arith`, `sumcheck` or
`all`, the default), arithmetic iteration counts scaled to `percent` per cent (default `100`). -/
def main (args : List String) : IO Unit := do
  let seed : UInt64 := ((← IO.getEnv "LEANERVM_BENCH_SEED").getD "12345").toNat!.toUInt64
  let maxLog := ((← IO.getEnv "LEANERVM_BENCH_MAXLOG").getD "20").toNat!
  let percent := ((args.head?.bind String.toNat?).getD 100)
  let group := (args.drop 1).head?.getD "all"
  IO.println s!"leanervm-bench: seed {seed}, {percent}% of the base iteration counts, {group}"
  if group == "all" || group == "arith" then LeanerVMBench.runArith seed percent
  if group == "all" || group == "sumcheck" then
    LeanerVMBench.runSumcheck seed ([4, 6, 8, 12, 16, 20].filter (· ≤ maxLog)) [4, 6, 8]
