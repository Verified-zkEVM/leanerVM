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
  the deployed verifier's `weights[t]` (`constraints.rs:274-277`).
* **The target** (`tableSummand_target`, acceptance test 7). On the honest stack the sum of the
  summand over the cube is `Σ_s ξ^(B + s) · total_s`, the batch of the claimed values; the true
  values are the claimed ones.
* **An honest run** is accepted: each round's honest polynomial passes its check, the honest
  values pass the final check, and every final claim holds of the stack.
* **A row violating a constraint** (a non-Boolean cell) makes the true value of that constraint,
  and of no other, nonzero; the honest first round fails its check against the derived target,
  and a prover that repairs each round's check from the wire's derived coefficient is caught by
  the final check.
* **Variable order** (acceptance test 16). The running claim after the rounds is the summand at
  the challenges in coordinate order, the first challenge the highest coordinate; read in the
  order drawn, the point mismatches `eq(ζ_{<τ_t}, ·)` and the padding.
* **Shared bus powers** (acceptance test 9). With side `s` of table `t` at its own power instead
  of the shared `ξ^(B + s)`, the sum over the cube is not the target.
* **Column groups** (acceptance test 30). A table with no constraint, flush or count column
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

-- The target is `Σ_s ξ^(B + s) · total_s`, derived from the bus phase's totals.
#guard T = ∑ s : Fin 3, out.totals s * ξ ^ (twoTab.B + s.val)
-- On the honest stack the true values are the claimed ones: the constraints' extensions are zero
-- at `ζ` and the forms reach their totals.
#guard ∀ k : Fin (twoTab.B + 3), trueValues twoTab x.1 honest k = claimed twoTab x.1 k
-- The sum of the summand over the cube is the target (`tableSummand_target`).
#guard Sumcheck.weightedSum (tableSummand twoTab) Sumcheck.unitWeights ctx = T

/-! ## An honest run -/

def s0 : SumcheckRound.Stmt (Data twoTab) E 0 := start twoTab x.1 ξ T
def q0 : SumcheckRound.Message E 3 :=
  Sumcheck.roundPoly (tableSummand twoTab) Sumcheck.unitWeights nodes ctx 0 #v[]

#guard SumcheckRound.check 0 (dom) s0 q0

def c0 : E := y * y * y + y
def s1 : SumcheckRound.Stmt (Data twoTab) E 1 :=
  SumcheckRound.next 0 s0 (SumcheckRound.evaluate 3 q0 c0) c0
def q1 : SumcheckRound.Message E 3 :=
  Sumcheck.roundPoly (tableSummand twoTab) Sumcheck.unitWeights nodes ctx 1 s1.2.1

#guard SumcheckRound.check 1 (dom) s1 q1

def c1 : E := y * y + 1
def s2 : SumcheckRound.Stmt (Data twoTab) E 2 :=
  SumcheckRound.next 1 s1 (SumcheckRound.evaluate 3 q1 c1) c1

/-- The honest final values: the columns' extensions at the final point. -/
def vals : Vector E twoTab.tableColumns := (tableSummand twoTab).values ctx s2.2.1.reverse

#guard Sumcheck.finalCheck (tableSummand twoTab) s2 vals
-- The final point is the challenges in coordinate order, the first challenge the highest.
#guard s2.2.1.reverse = #v[c1, c0]
-- Every claim the phase hands on holds of the stack: table 0's column at `(c1, c0)`, table 1's at
-- `c1`, which is where table 1 joined, at the second round.
#guard (tableOut twoTab s2 vals).2.columns.toList.all fun c ↦
  decide (eval₂Mle (twoTab.column honest c.col).values (algebraMap K E) c.point = c.value)
#guard (tableOut twoTab s2 vals).2.columns.toList.map (fun c ↦ c.point.toList) =
  [[c1, c0], [c1]]

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
def p0 : SumcheckRound.Message E 3 :=
  Sumcheck.roundPoly (tableSummand twoTab) Sumcheck.unitWeights nodes ctxBad 0 #v[]

-- The honest first round fails its check against the derived target.
#guard ¬ SumcheckRound.check 0 (dom) b0 p0

/-- A prover that repairs each round's check: coefficient 1 derived from the running claim, as
the wire's decoder does. -/
def p0' : SumcheckRound.Message E 3 :=
  Sumcheck.decodeRound (dom xBad 0) 1 TBad p0

#guard SumcheckRound.check 0 (dom) b0 p0'

def b1 : SumcheckRound.Stmt (Data twoTab) E 1 :=
  SumcheckRound.next 0 b0 (SumcheckRound.evaluate 3 p0' c0) c0
def p1' : SumcheckRound.Message E 3 :=
  Sumcheck.decodeRound (dom xBad 1) 1 b1.2.2
    (Sumcheck.roundPoly (tableSummand twoTab) Sumcheck.unitWeights nodes ctxBad 1 b1.2.1)

#guard SumcheckRound.check 1 (dom) b1 p1'

def b2 : SumcheckRound.Stmt (Data twoTab) E 2 :=
  SumcheckRound.next 1 b1 (SumcheckRound.evaluate 3 p1' c1) c1

-- The final check catches it: the true values at the final point miss the running claim.
#guard ¬ Sumcheck.finalCheck (tableSummand twoTab) b2
  ((tableSummand twoTab).values ctxBad b2.2.1.reverse)

/-! ## Variable order -/

-- After the rounds, the running claim is the summand at the challenges in coordinate order.
#guard s2.2.2 = (tableSummand twoTab).summand ctx #v[c1, c0]
-- Read in the order drawn, the point misses it: `eq(ζ_{<τ_t}, ·)` and the padding see the wrong
-- coordinates, with the values the prover would send at that point or at the right one.
#guard s2.2.2 ≠ (tableSummand twoTab).summand ctx #v[c0, c1]
#guard ¬ Sumcheck.finalCheck (tableSummand twoTab) (s2.1, (s2.2.1.reverse, s2.2.2)) vals

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
