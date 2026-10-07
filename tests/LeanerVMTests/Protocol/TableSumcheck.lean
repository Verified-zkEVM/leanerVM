import LeanerVM.Protocol.TableSumcheck
import LeanerVM.Protocol.Stack
import LeanerVM.Protocol.Spine.Toy
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Multivariate.Operations
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Table sumcheck tests

On an instance with two sumcheck tables of log-heights 2 and 1, one column each, both columns
Boolean, the taller table with a second constraint that is the zero polynomial; no bus, so the
bus phase's output is written by hand: a point `ζ`, one form on the push side per table, and the
totals those forms reach on the honest stack.

* **Sizes and positions.** `τ_max = 2`, `B = 3`, two final values; the constraints are numbered
  table by table and the columns too (`constraintPos`, `columnPos`, `position_val`).
* **The weights.** A table's weight at a point is `∏_{m<τ_t} (1 + ζ_m + r_m) · ∏_{m≥τ_t} r_m`,
  the deployed verifier's `weights[t]` (`constraints.rs:271-273` at leanVM `a386121f`).
* **The target** (`tableSummand_target`). On the honest stack the sum of the summand over the
  cube is `Σ_s ξ^(B + s) · total_s`, the batch of the claimed values, nonzero; the true values are
  the claimed ones.
* **An honest run** is accepted: each round's honest polynomial passes its check, the honest
  values pass the final check, and every final claim holds of the stack. On the two-table
  instance, and in one round on the toy instance, whose table has a form on each side of the
  bus.
* **A row violating a constraint** (a non-Boolean cell) makes the true value of that constraint,
  and of no other, nonzero; the honest first round fails its check against the derived target,
  and a prover that repairs each round's check from the wire's derived coefficient is caught by
  the final check.
* **Variable order.** The running claim after the rounds is the summand at
  the challenges in coordinate order, the first challenge the highest coordinate; read in the
  order drawn, the point mismatches `eq(ζ_{<τ_t}, ·)` and the padding.
* **Shared bus powers.** With side `s` of table `t` at its own power instead
  of the shared `ξ^(B + s)`, the sum over the cube is not the target.
* **Column groups.** A table with no constraint, flush or count column
  takes no part: on an instance with a taller column group the number of rounds is the sumcheck
  tables' `τ_max`.
* **Inhabitants.** The phase fills the slot `tableSpec` as a front phase on the toy instance, and
  completeness has inhabitants, as plain definitions, on both instances.

A plain file, so `#guard` evaluates the compiled definitions. Values of `E` written with numerals
are named as definitions before a guard uses them.
-/

namespace LeanerVMTests.Protocol.TableSumcheck

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.TableSumcheck CompPoly CPoly
  CMlPolynomialEval

/-! ## A two-table instance -/

/-- Two tables of log-heights 2 and 1, one column each. -/
abbrev shape : Shape := ⟨2, fun j ↦ if j.val = 0 then 2 else 1, fun _ ↦ 1⟩

/-- Their columns' blocks in the stack, the taller first. -/
def blocks : Blocks := ⟨2, fun b ↦ if b.val = 0 then 2 else 1, fun a b h ↦ by
  fin_cases a <;> fin_cases b <;> simp_all⟩

theorem blocks_total : blocks.total ≤ 2 ^ 3 := by
  simp [blocks, Blocks.total, Blocks.offsetNat]
  decide

/-- Table `j`'s column is block `j`: cells `0–3` and `4–5` of a stack of eight. -/
def layout : Layout 3 shape.ColumnId (fun c ↦ shape.τ c.1) :=
  (blocks.layout blocks_total).comap (fun c ↦ c.1) fun _ ↦ rfl

/-- The column is Boolean. -/
def bool : CMvPolynomial 1 K := CMvPolynomial.X 0 * CMvPolynomial.X 0 - CMvPolynomial.X 0

theorem bool_totalDegree : bool.totalDegree ≤ 2 := by
  rw [totalDegree_equiv (S := K), bool]
  erw [CPoly.map_sub]
  rw [CPoly.map_mul, CMvPolynomial.fromCMvPolynomial_X]
  exact (MvPolynomial.totalDegree_sub _ _).trans
    (max_le ((MvPolynomial.totalDegree_mul _ _).trans (by simp)) (by simp))

theorem zero_totalDegree : (0 : CMvPolynomial 1 K).totalDegree ≤ 2 := by
  rw [totalDegree_equiv (S := K)]
  simp

/-- The instance: table 0 carries `X² − X` and the zero polynomial, table 1 carries `X² − X`. -/
abbrev twoTab : M3Instance where
  toShape := shape
  Stmt := Unit
  constraints := fun j ↦ if j.val = 0 then [bool, 0] else [bool]
  flushes := fun _ ↦ []
  d := 2
  constraints_degree := fun j C h ↦ by
    split at h
    · rcases List.mem_pair.mp h with rfl | rfl
      · exact bool_totalDegree
      · exact zero_totalDegree
    · rw [List.mem_singleton.mp h]; exact bool_totalDegree
  flushes_degree := fun _ f h ↦ absurd h List.not_mem_nil
  counts := fun _ ↦ []
  boundary := []
  μ := 3
  layout := layout
  nLines := 0
  publicLines := fun _ ↦ #v[]
  flock := none

/-- The two sumcheck tables. -/
def t0 : twoTab.SumcheckTables := ⟨0, by decide⟩
def t1 : twoTab.SumcheckTables := ⟨1, by decide⟩

/-! ## Sizes and positions -/

#guard twoTab.τmax = 2
#guard twoTab.B = 3
#guard twoTab.tableColumns = 2
#guard twoTab.busClaims = 0
-- The constraints are numbered table by table: table 0's two, then table 1's.
#guard (constraintPos twoTab ⟨t0, ⟨0, by decide⟩⟩ : ℕ) = 0
#guard (constraintPos twoTab ⟨t0, ⟨1, by decide⟩⟩ : ℕ) = 1
#guard (constraintPos twoTab ⟨t1, ⟨0, by decide⟩⟩ : ℕ) = 2
-- The columns too: one value per column, table by table.
#guard (columnPos twoTab ⟨t0, ⟨0, by decide⟩⟩ : ℕ) = 0
#guard (columnPos twoTab ⟨t1, ⟨0, by decide⟩⟩ : ℕ) = 1

/-! ## The bus phase's output, by hand -/

/-- Values of `E`. -/
def ζ0 : E := y + 1
def ζ1 : E := y * y
def ξ : E := y * y + y + 1
def w0 : E := y
def w1 : E := y * y + 1

/-- The bus point. -/
def ζ : Vector E twoTab.τmax := #v[ζ0, ζ1]

/-- The row polynomial `X`, within the degree bound. -/
def xRow (j : Fin twoTab.ntab) : twoTab.RowPoly j :=
  ⟨CMvPolynomial.X 0, by
    rw [totalDegree_equiv (S := K)]
    simp [CMvPolynomial.fromCMvPolynomial_X]⟩

/-- One push form per table, `w_t · X`; nothing on the pull and count sides. -/
def forms : Fin 3 → (j : twoTab.SumcheckTables) → twoTab.Form j.1 :=
  fun s j ↦ if s.val = 0 then [(if j.1.val = 0 then w0 else w1, xRow j.1)] else []

/-- The honest stack: table 0's column `[1, 0, 1, 1]`, table 1's `[0, 1]`. -/
def honest : Column 3 := ⟨#v[1, 0, 1, 1, 0, 1, 0, 0]⟩

#guard M3Holds twoTab () honest

/-- The bus output on a stack: the point, the forms, and the totals they reach on the stack. -/
def busOutOn (q : Column 3) : BusOut twoTab where
  point := ζ
  forms := forms
  totals := fun s ↦ ∑ t, M3Instance.Form.eval twoTab (forms s t) q (twoTab.lowPoint ζ t)
  columns := #v[]

/-- The oracle: the stack. -/
def oracles (q : Column 3) : ∀ i, TheOracle twoTab i := fun _ ↦ q

def out : BusOut twoTab := busOutOn honest

/-- The sumcheck's data: the statement, the bus output, `ξ`. -/
def x : Data twoTab := (((), out), ξ)

def ctx : SumcheckRound.Ctx (Data twoTab) (TheOracle twoTab) Unit := ((x, oracles honest), ())

/-- The verifier's domain of each round: the points `0, 1` with unit weights. -/
def dom : SumcheckRound.Weights E (Data twoTab) :=
  Sumcheck.domain (n := twoTab.τmax) Sumcheck.unitWeights

/-! ## The weights -/

def r0 : E := y * y * y
def r1 : E := y + y * y

-- A table's weight at `r` is `∏_{m<τ_t} (1 + ζ_m + r_m) · ∏_{m≥τ_t} r_m`: the deployed verifier's
-- `weights[t] *= if tau > m { 1 + ζ_m + r_m } else { r_m }`.
#guard prodWeight (tableWeights twoTab ζ t0) #v[r0, r1] = (1 + ζ0 + r0) * (1 + ζ1 + r1)
#guard prodWeight (tableWeights twoTab ζ t1) #v[r0, r1] = (1 + ζ0 + r0) * r1

/-! ## The target -/

/-- The verifier's target: the claimed values batched by `ξ`. -/
def T : E := powerBatch (claimed twoTab x.1) ξ

-- The target is `Σ_s ξ^(B + s) · total_s`, derived from the bus phase's totals, and not zero.
#guard T = ∑ s : Fin 3, out.totals s * ξ ^ (twoTab.B + s.val)
#guard T ≠ 0
-- On the honest stack the true values are the claimed ones: the constraints' extensions are zero
-- at `ζ` and the forms reach their totals.
#guard ∀ k : Fin (twoTab.B + 3), trueValues twoTab x.1 honest k = claimed twoTab x.1 k
-- The sum of the summand over the cube is the target (`tableSummand_target`).
#guard Sumcheck.weightedSum (tableSummand twoTab) Sumcheck.unitWeights ctx = T

/-! ## Runs of the rounds

The honest prover's round polynomials interpolate over `E`, which the interpreter computes slowly
(seconds per polynomial), and a definition is evaluated again by every guard that reads it, so
each run is computed once, inside one guard. -/

/-- The challenges. -/
def c0 : E := y * y * y + y
def c1 : E := y * y + 1

/-- The rounds of a run at the challenges `c0, c1`: the prover's first polynomial, and the
polynomials sent with the statements they lead to. With `repair`, the prover sends its polynomial
with coefficient 1 derived from the running claim, as the wire's decoder does, so that it passes
the round's check whatever the claim. -/
structure Run where
  /-- The prover's first polynomial, before any repair. -/
  p0 : SumcheckRound.Message E 3
  /-- The first polynomial sent. -/
  q0 : SumcheckRound.Message E 3
  /-- The statement after the first round. -/
  s1 : SumcheckRound.Stmt (Data twoTab) E 1
  /-- The second polynomial sent. -/
  q1 : SumcheckRound.Message E 3
  /-- The statement after the second round. -/
  s2 : SumcheckRound.Stmt (Data twoTab) E 2

/-- The run from a context and a first statement. -/
def run (ctx : SumcheckRound.Ctx (Data twoTab) (TheOracle twoTab) Unit)
    (s0 : SumcheckRound.Stmt (Data twoTab) E 0) (repair : Bool) : Run :=
  let send := fun (j : ℕ) (claim : E) (q : SumcheckRound.Message E 3) ↦
    if repair then Sumcheck.decodeRound (dom s0.1 j) 1 claim q else q
  let p0 := Sumcheck.roundPoly (tableSummand twoTab) Sumcheck.unitWeights nodes ctx 0 #v[]
  let q0 := send 0 s0.2.2 p0
  let s1 := SumcheckRound.next 0 s0 (SumcheckRound.evaluate 3 q0 c0) c0
  let q1 := send 1 s1.2.2
    (Sumcheck.roundPoly (tableSummand twoTab) Sumcheck.unitWeights nodes ctx 1 s1.2.1)
  ⟨p0, q0, s1, q1, SumcheckRound.next 1 s1 (SumcheckRound.evaluate 3 q1 c1) c1⟩

/-- The honest run's first statement: the derived target. -/
def s0 : SumcheckRound.Stmt (Data twoTab) E 0 := start twoTab x.1 ξ T

/-! ## An honest run, and the variable order -/

#guard
  let r := run ctx s0 false
  let vals := (tableSummand twoTab).values ctx r.s2.2.1.reverse
  let claims := (tableOut twoTab r.s2 vals).2.columns.toList
  -- Each round's honest polynomial passes its check, and the honest values the final check.
  SumcheckRound.check 0 dom s0 r.q0 && SumcheckRound.check 1 dom r.s1 r.q1 &&
  Sumcheck.finalCheck (tableSummand twoTab) r.s2 vals &&
  -- The final point is the challenges in coordinate order, the first challenge the highest.
  decide (r.s2.2.1.reverse = #v[c1, c0]) &&
  -- Every claim the phase hands on holds of the stack: table 0's column at `(c1, c0)`, table 1's
  -- at `c1`, the coordinate of the second round, where table 1 joined.
  claims.all (fun c ↦
    decide (eval₂Mle (twoTab.column honest c.col).values (algebraMap K E) c.point = c.value)) &&
  decide (claims.map (fun c ↦ c.point.toList) = [[c1, c0], [c1]]) &&
  -- Variable order: the running claim after the rounds is the summand at the challenges in
  -- coordinate order; read in the order drawn, the point misses it, since `eq(ζ_{<τ_t}, ·)` and
  -- the padding see the wrong coordinates, and the final check rejects the honest values there.
  decide (r.s2.2.2 = (tableSummand twoTab).summand ctx #v[c1, c0]) &&
  decide (r.s2.2.2 ≠ (tableSummand twoTab).summand ctx #v[c0, c1]) &&
  !Sumcheck.finalCheck (tableSummand twoTab) (r.s2.1, (r.s2.2.1.reverse, r.s2.2.2)) vals

/-! ## A row violating a constraint -/

/-- Table 0's third cell is `2`, not Boolean. -/
def bad : Column 3 := ⟨#v[1, 0, K.ofBits 2, 1, 0, 1, 0, 0]⟩

#guard ¬ M3Holds twoTab () bad

def xBad : Data twoTab := (((), busOutOn bad), ξ)
def ctxBad : SumcheckRound.Ctx (Data twoTab) (TheOracle twoTab) Unit := ((xBad, oracles bad), ())
def TBad : E := powerBatch (claimed twoTab xBad.1) ξ

-- The violated constraint's true value is nonzero; the zero constraint's and table 1's are zero;
-- the forms still reach their totals.
#guard trueValues twoTab xBad.1 bad ⟨0, by decide⟩ ≠ 0
#guard trueValues twoTab xBad.1 bad ⟨1, by decide⟩ = 0 ∧
  trueValues twoTab xBad.1 bad ⟨2, by decide⟩ = 0
#guard ∀ s : Fin 3, trueValues twoTab xBad.1 bad (Fin.natAdd twoTab.B s) =
  claimed twoTab xBad.1 (Fin.natAdd twoTab.B s)
-- So the sum over the cube is not the target.
#guard Sumcheck.weightedSum (tableSummand twoTab) Sumcheck.unitWeights ctxBad ≠ TBad

def b0 : SumcheckRound.Stmt (Data twoTab) E 0 := start twoTab xBad.1 ξ TBad

#guard
  let r := run ctxBad b0 true
  -- The honest first polynomial fails its check against the derived target.
  !SumcheckRound.check 0 dom b0 r.p0 &&
  -- Repaired, each round passes its check.
  SumcheckRound.check 0 dom b0 r.q0 && SumcheckRound.check 1 dom r.s1 r.q1 &&
  -- The final check catches it: the true values at the final point miss the running claim.
  !Sumcheck.finalCheck (tableSummand twoTab) r.s2
    ((tableSummand twoTab).values ctxBad r.s2.2.1.reverse)

/-! ## Shared bus powers -/

/-- What table `t` owes with side `s` at the table's own power `ξ^(B + 3t + s)` instead of the
shared `ξ^(B + s)`. -/
def rowValuePerTable (x : Data twoTab) (t : twoTab.SumcheckTables)
    (e : Fin (twoTab.width t.1) → E) : E :=
  (∑ i : Fin (twoTab.constraints t.1).length,
    x.2 ^ (constraintPos twoTab ⟨t, i⟩ : ℕ) * evalRow (twoTab.constraints t.1)[i] e) +
  ∑ s : Fin 3, x.2 ^ (twoTab.B + 3 * t.1.val + s.val) * formAt (x.1.2.forms s t) e

/-- The summand with per-table side powers. -/
def perTable : Sumcheck.Virtual E (Data twoTab) (TheOracle twoTab) Unit twoTab.τmax
    twoTab.tableColumns where
  tables := (tableSummand twoTab).tables
  formula := fun x z v ↦ ∑ t : twoTab.SumcheckTables,
    prodWeight (tableWeights twoTab x.1.2.point t) z * rowValuePerTable x t (tableValues twoTab v t)

-- With per-table powers the honest sum is not the target: the target no longer factors through
-- the totals.
#guard Sumcheck.weightedSum perTable Sumcheck.unitWeights ctx ≠ T

/-! ## Column groups -/

/-- A column group of log-height 3 beside the two sumcheck tables. -/
abbrev groupShape : Shape := ⟨3, fun j ↦ if j.val = 0 then 3 else if j.val = 1 then 2 else 1,
  fun _ ↦ 1⟩

def groupBlocks : Blocks :=
  ⟨3, fun b ↦ if b.val = 0 then 3 else if b.val = 1 then 2 else 1, fun a b h ↦ by
    fin_cases a <;> fin_cases b <;> simp_all⟩

theorem groupBlocks_total : groupBlocks.total ≤ 2 ^ 4 := by
  simp [groupBlocks, Blocks.total, Blocks.offsetNat]
  decide

/-- The instance: table 0 a column group, tables 1 and 2 Boolean. -/
abbrev withGroup : M3Instance where
  toShape := groupShape
  Stmt := Unit
  constraints := fun j ↦ if j.val = 0 then [] else [bool]
  flushes := fun _ ↦ []
  d := 2
  constraints_degree := fun j C h ↦ by
    split at h
    · exact absurd h List.not_mem_nil
    · rw [List.mem_singleton.mp h]; exact bool_totalDegree
  flushes_degree := fun _ f h ↦ absurd h List.not_mem_nil
  counts := fun _ ↦ []
  boundary := []
  μ := 4
  layout := (groupBlocks.layout groupBlocks_total).comap (fun c ↦ c.1) fun _ ↦ rfl
  nLines := 0
  publicLines := fun _ ↦ #v[]
  flock := none

-- The column group is the tallest table, and no sumcheck table: the sumcheck runs `τ_max = 2`
-- rounds, not 3, and sends two values, not three.
#guard ¬ withGroup.SumcheckTable 0
#guard withGroup.τmax = 2
#guard withGroup.tableColumns = 2
example : tableRounds withGroup = 1 + roundsRounds 2 + 1 := by decide

/-! ## A run on the toy instance -/

/-- The row polynomial `X_i` of the toy's table, within the degree bound. -/
def toyRow (i : Fin 3) (j : Fin Toy.toy.ntab) : Toy.toy.RowPoly j :=
  ⟨CMvPolynomial.X i, by
    rw [totalDegree_equiv (S := K)]
    simp [CMvPolynomial.fromCMvPolynomial_X]⟩

/-- One form per side: `w0 · X₀` pushed, `w1 · X₁` pulled, `X₂` on the count side. -/
def toyForms : Fin 3 → (j : Toy.toy.SumcheckTables) → Toy.toy.Form j.1 :=
  fun s j ↦ [(if s.val = 0 then w0 else if s.val = 1 then w1 else 1, toyRow s j.1)]

/-- The toy's bus point. -/
def ζToy : Vector E Toy.toy.τmax := #v[ζ0]

/-- The toy's bus output on its honest stack: the totals its forms reach there. -/
def outToy : BusOut Toy.toy where
  point := ζToy
  forms := toyForms
  totals := fun s ↦
    ∑ t, M3Instance.Form.eval Toy.toy (toyForms s t) Toy.honest (Toy.toy.lowPoint ζToy t)
  columns := #v[]

def xToy : Data Toy.toy := (((1 : K), outToy), ξ)
def ctxToy : SumcheckRound.Ctx (Data Toy.toy) (TheOracle Toy.toy) Unit :=
  ((xToy, fun _ ↦ Toy.honest), ())
def TToy : E := powerBatch (claimed Toy.toy xToy.1) ξ
def s0Toy : SumcheckRound.Stmt (Data Toy.toy) E 0 := start Toy.toy xToy.1 ξ TToy

#guard Toy.toy.τmax = 1 ∧ Toy.toy.B = 1 ∧ Toy.toy.tableColumns = 3 ∧ Toy.toy.busClaims = 0
#guard M3Holds Toy.toy (1 : K) Toy.honest
-- The sum over the cube is the target, which every side's total enters.
#guard Sumcheck.weightedSum (tableSummand Toy.toy) Sumcheck.unitWeights ctxToy = TToy
#guard ∀ s : Fin 3, outToy.totals s ≠ 0

#guard
  let q0 := Sumcheck.roundPoly (tableSummand Toy.toy) Sumcheck.unitWeights nodes ctxToy 0 #v[]
  let s1 := SumcheckRound.next 0 s0Toy (SumcheckRound.evaluate 3 q0 c0) c0
  let vals := (tableSummand Toy.toy).values ctxToy s1.2.1.reverse
  -- The round passes its check, the values the final check, and the three claims hold.
  SumcheckRound.check 0 (Sumcheck.domain (n := Toy.toy.τmax) Sumcheck.unitWeights) s0Toy q0 &&
  Sumcheck.finalCheck (tableSummand Toy.toy) s1 vals &&
  (tableOut Toy.toy s1 vals).2.columns.toList.all (fun c ↦ decide
    (eval₂Mle (Toy.toy.column Toy.honest c.col).values (algebraMap K E) c.point = c.value))

/-! ## Inhabitants -/

-- The phase fills the table slot as a front phase.
example : Phase.FrontDef Toy.toy (Toy.toy.Stmt × BusOut Toy.toy) (Toy.toy.Stmt × TableOut Toy.toy)
    (tableSpec Toy.toy) :=
  tableSumcheck Toy.toy

/-- Completeness on the toy instance. -/
def completeToy :
    Phase.Complete Toy.toy (tableSumcheck Toy.toy).toDef (Seam.bus Toy.toy) (Seam.table Toy.toy) :=
  tableSumcheckComplete Toy.toy le_rfl

/-- Completeness on the two-table instance. -/
def completeTwo :
    Phase.Complete twoTab (tableSumcheck twoTab).toDef (Seam.bus twoTab) (Seam.table twoTab) :=
  tableSumcheckComplete twoTab le_rfl

end LeanerVMTests.Protocol.TableSumcheck
