import LeanerVM.Protocol.ToArkLib.Sumcheck
import LeanerVM.Protocol.ToArkLib.Oracles
import LeanerVM.Protocol.Field
import LeanerVM.Protocol.Spine.Errors
import LeanerVM.Protocol.Spine.Phase
import LeanerVM.Protocol.Spine.Toy

/-!
# Sumcheck tests

Over `E`, with no public data and no oracle, on a summand of degree two in two variables, the
product of two tables' extensions.

* **The plain sumcheck, by hand.** The claim is the sum of the summand over the cube; each honest
  round polynomial passes the check and evaluates to the next claim; the first challenge is the
  highest coordinate, so the claim after one round sums over the low coordinate with the high
  one at the challenge; the honest values pass the final check, and the output relation holds.
* **The normalized sumcheck, by hand.** The same with the weights of an equality polynomial: the
  claim is `Σ_x eq(p, x) · summand(x)`, the round check weighs `q(0)` and `q(1)` by `1 - p_k` and
  `p_k`, and the final claim is the summand at the challenges, with no equality factor.
* **What is rejected.** A round polynomial with one coefficient changed, a wrong claim, and
  values that are not the tables' at the final point.
* **The wire.** The Rust verifier's decoding of a round (`next_round_poly`,
  `crates/fiat_shamir/src/transcript.rs:288-309` at leanVM `a386121f`): the plain round drops
  `c_1`, recomputed as `claim + c_2 + … + c_d`; the normalized round drops `c_0`, recomputed as
  `claim + r · (c_1 + … + c_d)`. `decodeRound` agrees with both on honest messages of degree two
  and three, and returns the honest message from the wire.
* **The slot.** The table sumcheck's slot `tableSpec` takes the batching challenge followed by the
  rounds and the last message of a plain sumcheck of degree three, as a front phase.
* **Completeness** has an inhabitant for both variants.

A plain file, so `#guard` evaluates the compiled definitions. Values of `E` written with numerals
are named as definitions before a guard uses them.
-/

namespace LeanerVMTests.Protocol.Sumcheck

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Sumcheck CompPoly CMlPolynomialEval

/-- No oracle. -/
def noO : ∀ i, NoOracle i := fun i ↦ i.elim0

/-- Values of `E`. -/
def a : E := y
def b : E := y + 1
def c : E := y * y + y
def one : E := 1
def zero : E := 0

/-- Two tables on two variables. -/
def t₁ : CMlPolynomialEval E 2 := #v[a, b, c, 1]
def t₂ : CMlPolynomialEval E 2 := #v[b, 1, a, c]

/-- The virtual polynomial `t₁ · t₂`. -/
def V : Virtual E Unit NoOracle Unit 2 2 where
  tables := fun _ ↦ ![t₁, t₂]
  formula := fun _ _ v ↦ v[0] * v[1]

/-- The context: no public data, no oracle, no witness. -/
def ctx : SumcheckRound.Ctx Unit NoOracle Unit := (((), noO), ())

/-- Three distinct nodes. -/
def nodes : Fin 3 → E := ![0, 1, y]

/-- Unit weights on two coordinates. -/
def wtOne : CoordWeights E Unit 2 := unitWeights

/-! ## The plain sumcheck, by hand -/

/-- The claimed sum. -/
def T : E := weightedSum V wtOne ctx

-- The claim is the sum of `t₁ · t₂` over the cube.
#guard T = a * b + b * 1 + c * a + 1 * c

def s0 : SumcheckRound.Stmt Unit E 0 := ((), (#v[], T))
def q0 : SumcheckRound.Message E 2 := roundPoly V wtOne nodes ctx 0 #v[]

-- The honest polynomial passes the check `q(0) + q(1) = T`.
#guard SumcheckRound.check 0 (domain wtOne) s0 q0
#guard SumcheckRound.evaluate 2 q0 0 + SumcheckRound.evaluate 2 q0 1 = T

def r0 : E := c
def s1 : SumcheckRound.Stmt Unit E 1 :=
  SumcheckRound.next 0 s0 (SumcheckRound.evaluate 2 q0 r0) r0

-- The first challenge is the highest coordinate: the new claim sums over coordinate 0 with
-- coordinate 1 at `r0`.
#guard s1.2.2 = V.summand ctx #v[0, r0] + V.summand ctx #v[1, r0]
#guard s1.2.2 = claim V wtOne ctx 1 #v[r0]

def q1 : SumcheckRound.Message E 2 := roundPoly V wtOne nodes ctx 1 s1.2.1

#guard SumcheckRound.check 1 (domain wtOne) s1 q1

def r1 : E := a + 1
def s2 : SumcheckRound.Stmt Unit E 2 :=
  SumcheckRound.next 1 s1 (SumcheckRound.evaluate 2 q1 r1) r1

-- The final claim is the summand at the final point `(r1, r0)`, coordinate 0 the last challenge.
#guard s2.2.2 = V.summand ctx #v[r1, r0]

/-- The honest values at the final point. -/
def vals : Vector E 2 := V.values ctx s2.2.1.reverse

#guard finalCheck V s2 vals
#guard (finalOut s2 vals).2.1.toList = [r1, r0]
-- The output relation: each value is its table's extension at the point.
#guard V.values ((((finalOut s2 vals).1, noO), ())) (finalOut s2 vals).2.1 = (finalOut s2 vals).2.2
#guard vals[0] = evalMle t₁ #v[r1, r0] ∧ vals[1] = evalMle t₂ #v[r1, r0]

/-! ## What is rejected -/

-- A round polynomial with its top coefficient changed.
#guard ¬ SumcheckRound.check 0 (domain wtOne) s0 (q0.set 2 (q0[2] + 1))
-- A wrong claim.
#guard ¬ SumcheckRound.check 0 (domain wtOne) ((), (#v[], T + 1)) q0
-- Values other than the tables' at the final point.
#guard ¬ finalCheck V s2 (vals.set 0 (vals[0] + 1))

/-! ## The normalized sumcheck, by hand -/

/-- The point of the equality polynomial. -/
def p : Vector E 2 := #v[a, c]

/-- The weights of `eq(p, ·)`. -/
def wtEq : CoordWeights E Unit 2 := eqWeights fun _ ↦ p

def Tn : E := weightedSum V wtEq ctx

-- The claim is `Σ_x eq(p, x) · t₁(x) t₂(x)`, coordinate 0 the low bit.
#guard Tn = (1 - a) * (1 - c) * (a * b) + a * (1 - c) * (b * 1) + (1 - a) * c * (c * a) +
  a * c * (1 * c)

def n0 : SumcheckRound.Stmt Unit E 0 := ((), (#v[], Tn))
def h0 : SumcheckRound.Message E 2 := roundPoly V wtEq nodes ctx 0 #v[]

-- The round binds coordinate 1 first: the check weighs `h(0)` and `h(1)` by `1 - p_1`, `p_1`.
#guard SumcheckRound.check 0 (domain wtEq) n0 h0
#guard (1 - c) * SumcheckRound.evaluate 2 h0 0 + c * SumcheckRound.evaluate 2 h0 1 = Tn

def n1 : SumcheckRound.Stmt Unit E 1 :=
  SumcheckRound.next 0 n0 (SumcheckRound.evaluate 2 h0 r0) r0
def h1 : SumcheckRound.Message E 2 := roundPoly V wtEq nodes ctx 1 n1.2.1

#guard SumcheckRound.check 1 (domain wtEq) n1 h1
#guard ¬ SumcheckRound.check 1 (domain wtEq) n1 (h1.set 0 (h1[0] + 1))

def n2 : SumcheckRound.Stmt Unit E 2 :=
  SumcheckRound.next 1 n1 (SumcheckRound.evaluate 2 h1 r1) r1

-- The final claim is the summand at the challenges, with no equality factor.
#guard n2.2.2 = V.summand ctx #v[r1, r0]
#guard finalCheck V n2 (V.values ctx n2.2.1.reverse)

/-! ## The wire -/

-- The plain round drops `c_1`: it is `claim + c_2` (the Rust's `claim + sum_from(2)`).
#guard decodeRound (domain wtOne () 0) 1 T (q0.set 1 0) = q0
#guard (decodeRound (domain wtOne () 0) 1 T (q0.set 1 0))[1] = T + q0[2]
-- The normalized round drops `c_0`: it is `claim + r·(c_1 + c_2)`, `r = p_1` for the first
-- round (the Rust's `claim + r * sum_from(1)`).
#guard decodeRound (domain wtEq () 0) 0 Tn (h0.set 0 0) = h0
#guard (decodeRound (domain wtEq () 0) 0 Tn (h0.set 0 0))[0] = Tn + c * (h0[1] + h0[2])
-- A message that fails the check is not returned: the decoding makes it pass.
#guard decodeRound (domain wtOne () 0) 1 T (q0.set 2 (q0[2] + 1)) ≠ q0.set 2 (q0[2] + 1)
#guard SumcheckRound.check 0 (domain wtOne) s0
  (decodeRound (domain wtOne () 0) 1 T (q0.set 2 (q0[2] + 1)))

/-- A third table, for a cubic summand like the table sumcheck's. -/
def t₃ : CMlPolynomialEval E 2 := #v[c, a, 1, b]

/-- The cubic virtual polynomial `t₁ · t₂ · t₃`. -/
def V3 : Virtual E Unit NoOracle Unit 2 3 where
  tables := fun _ ↦ ![t₁, t₂, t₃]
  formula := fun _ _ v ↦ v[0] * v[1] * v[2]

/-- Four distinct nodes. -/
def nodes4 : Fin 4 → E := ![0, 1, y, y + 1]

def T3 : E := weightedSum V3 wtOne ctx
def k0 : SumcheckRound.Message E 3 := roundPoly V3 wtOne nodes4 ctx 0 #v[]

-- The cubic round: four coefficients, `c_1` dropped on the wire and recomputed from the claim as
-- `claim + c_2 + c_3`.
#guard SumcheckRound.check 0 (domain wtOne) ((), (#v[], T3)) k0
#guard decodeRound (domain wtOne () 0) 1 T3 (k0.set 1 0) = k0
#guard (decodeRound (domain wtOne () 0) 1 T3 (k0.set 1 0))[1] = T3 + k0[2] + k0[3]

/-! ## The slot of the table sumcheck -/

/-- The public data of the table sumcheck after its batching challenge. -/
abbrev TableX : Type := (Toy.toy.Stmt × BusOut Toy.toy) × E

/-- A plain virtual polynomial of degree three over the toy's stack: the three columns of its
table, lifted to `E`, under a formula of the shape of a constraint. -/
def Vtoy : Virtual E TableX (TheOracle Toy.toy) Unit Toy.toy.τmax Toy.toy.tableColumns where
  tables := fun ctx i ↦ CMlPolynomialEval.map (algebraMap K E)
    (Toy.slice (ctx.1.2 0) ⟨0, ⟨i.val, i.isLt⟩⟩).values
  formula := fun _ _ v ↦ v[2] * v[2] + v[2]

instance : ∀ i, OracleInterface ((draw E ++ₚ roundsSpec E 3 Toy.toy.τmax).Message i) :=
  msgAppend (instOracleInterfaceDraw E) (instOracleInterfaceRounds E 3 _)

instance : ∀ i, SampleableType ((draw E ++ₚ roundsSpec E 3 Toy.toy.τmax).Challenge i) :=
  chalAppend (instSampleableTypeDraw E) (instSampleableTypeRounds E 3 _)

/-- The table sumcheck's shape: the batching challenge, then the rounds and the last message of
the plain sumcheck. -/
def tableShape : Phase.Def Toy.toy (Toy.toy.Stmt × BusOut Toy.toy)
    (Out TableX E Toy.toy.τmax Toy.toy.tableColumns) (tableSpec Toy.toy) :=
  ((Component.sampleChallenge (TheOracle Toy.toy) E (fun _ ↦ true)
      fun s ξ ↦ (((s, ξ), (#v[], 0)) : SumcheckRound.Stmt TableX E 0)).append
    (rounds Vtoy unitWeights nodes4)).append (final Vtoy)

-- The slot takes it as a front phase, by definitional equality of the schedules.
example : Phase.FrontDef Toy.toy (Toy.toy.Stmt × BusOut Toy.toy)
    (Out TableX E Toy.toy.τmax Toy.toy.tableColumns) (tableSpec Toy.toy) :=
  ⟨tableShape,
    ((Component.sampleFront _ _ _ _).append (roundsFront Vtoy unitWeights nodes4)).append
      (finalFront Vtoy)⟩

/-! ## Completeness -/

theorem y_ne_zero : y ≠ 0 := by
  intro h
  have h3 := y_pow_three
  rw [h] at h3
  simp at h3

theorem y_ne_one : y ≠ 1 := by
  intro h
  have h3 := y_pow_three
  rw [h] at h3
  simp at h3

theorem nodes_injective : Function.Injective nodes := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [nodes, y_ne_zero, y_ne_one, y_ne_zero.symm, y_ne_one.symm]

theorem V_degree : ∀ ctx, IndividualDegreeLE (V.summand ctx) 2 := fun ctx ↦ by
  have e : V.summand ctx = fun z ↦ evalMle t₁ z * evalMle t₂ z := by
    funext z
    simp only [Virtual.summand, Virtual.values, V, Vector.getElem_ofFn]
    rfl
  rw [e]
  exact (IndividualDegreeLE.evalMle t₁).mul (IndividualDegreeLE.evalMle t₂)

-- Completeness of both variants on `t₁ · t₂`, as plain definitions: they compute.
def completePlain : Component.Complete (plain V nodes) (relIn V unitWeights) (relOut V) :=
  plainComplete V nodes V_degree nodes_injective

def completeNormalized :
    Component.Complete (normalized V (fun _ ↦ p) nodes) (relIn V wtEq) (relOut V) :=
  normalizedComplete V nodes (fun _ ↦ p) V_degree nodes_injective

end LeanerVMTests.Protocol.Sumcheck
