/-
  LeanerVM.Protocol.ToArkLib.SumcheckRound

  One round of a sumcheck as a component: the prover sends the coefficients of a univariate
  polynomial, the verifier checks its weighted sum over a domain against the running claim,
  draws a challenge and carries the polynomial's value there as the next claim. Generic over
  the family of claims it reduces, with the rounds of a whole sumcheck composed from it.
  Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.SampleChallenge
public import LeanerVM.Protocol.ToArkLib.SendChecked
public import LeanerVM.Protocol.ToArkLib.PassThrough
public import CompPoly.Univariate.ToPoly.Impl

/-!
# A sumcheck round

A sumcheck reduces a claim about a sum over the cube to a claim about one point, one variable at
a time. After `j` rounds the statement is the public data, the `j` challenges drawn so far and
the running claim (`Stmt`); a `Family` says what the claim should be at every stage (`claim`),
which polynomial the honest prover sends (`poly`), the weighted domain the verifier sums the
polynomial over (`weight`), and a side condition on the context and the challenges (`inv`), which
a protocol uses to carry facts the round does not touch. Two domains give the two usual rounds:

* *plain*: the points `0, 1` with unit weights; the message is the round polynomial itself;
* *normalized* (`normalizedWeights`): the points `0, 1` with the weights `1 - r_j, r_j`, for a
  sum `Σ_x eq(r, x) g(x)`; the message is the cofactor of the equality factor, the running claim
  leaves out the equality factor of the coordinates already bound, and the final claim is `g` at
  the challenges, with no equality factor.

A round message is the `d + 1` coefficients of a polynomial of degree at most `d`, low degree
first (`Message`, the type `roundSpec` names), read whole; `evaluate` is its value at a point,
and `ofCPolynomial` reads the coefficients off a computable polynomial of that degree. The
degree bound is the length of the message: a prover cannot send more coefficients.

`round P wt j` is the round from stage `j` to stage `j + 1`, at the schedule `roundSpec F d`,
in two components: `sendPoly` (the prover's polynomial, which the verifier records in the
statement) and `drawChallenge` (the verifier rejects unless the recorded polynomial's weighted
sum over the domain is the running claim, draws the challenge, and carries the polynomial's
value there as the next claim). It is built from the honest polynomials `P` and the weights
`wt` alone, so that a family's claims and invariant, which only the relations mention, never
enter a definition. `rounds P wt m i j` is the `i` rounds from stage `j` to stage `m = j + i`
at `roundsSpec F d i`, so that a sumcheck of `m` rounds is `rounds P wt m m 0`. The relations
are `rel Φ j`: the invariant holds and the running claim is the family's; between the two
components of a round, `relMid Φ j` adds that the recorded polynomial is the honest one.
Completeness needs the family to be honest (`Family.Honest`): the honest polynomial passes the
check and evaluates to the next claim, and the invariant survives every challenge. The oracles
and the witness are passed through untouched.

ArkLib's computable sumcheck (`Sumcheck.Impl.Representation.Message`, a polynomial with a
degree bound queried by evaluation) sums its message over a unit-weight domain and is not an
oracle reduction; this round sends coefficients, as the deployed verifiers read them, and
weights the domain.
-/

namespace LeanerVM.Protocol

open CompPoly OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace SumcheckRound

section Data

variable {F : Type} [Field F] {X : Type} {ι : Type} {O : ι → Type} {W : Type}

/-! ## Messages: the coefficients of a polynomial -/

/-- A round message: the `d + 1` coefficients of a polynomial of degree at most `d`, low degree
first. -/
abbrev Message (F : Type) (d : ℕ) : Type := Vector F (d + 1)

/-- The value of a message at a point, `Σ_i q_i · x^i`. -/
def evaluate (d : ℕ) (q : Message F d) (x : F) : F := ∑ i : Fin (d + 1), q[i] * x ^ (i : ℕ)

/-- The coefficients of a computable polynomial, as a message. -/
def ofCPolynomial (d : ℕ) (p : CPolynomial F) : Message F d := Vector.ofFn fun i ↦ p.coeff i

/-- On a polynomial of degree at most `d`, the message evaluates as the polynomial. -/
theorem evaluate_ofCPolynomial [BEq F] [LawfulBEq F] (d : ℕ) (p : CPolynomial F)
    (hp : p.degree ≤ (d : WithBot ℕ)) (x : F) : evaluate d (ofCPolynomial d p) x = p.eval x := by
  rw [CPolynomial.eval_toPoly, CPolynomial.degree_toPoly] at *
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (Polynomial.natDegree_le_of_degree_le hp)),
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [ofCPolynomial, Fin.getElem_fin, Vector.getElem_ofFn, CPolynomial.coeff_toPoly]

/-- The verifier's domain: points with weights. Unit weights on `0, 1` are the plain sumcheck;
`1 - r_j, r_j` on `0, 1` keep an `eq(r, ·)` factor outside the polynomial. -/
abbrev WeightedDomain (F : Type) : Type := List (F × F)

/-- The weighted sum of a message over the domain. -/
def weightedSum (d : ℕ) (dom : WeightedDomain F) (q : Message F d) : F :=
  (dom.map fun p ↦ p.2 * evaluate d q p.1).sum

/-! ## Families of claims -/

/-- What a round reads: the public data, the oracles' contents and the witness. -/
abbrev Ctx (X : Type) {ι : Type} (O : ι → Type) (W : Type) : Type := (X × ∀ i, O i) × W

/-- The honest polynomials: at every stage, from the context and the challenges so far. -/
abbrev Polys (F X : Type) {ι : Type} (O : ι → Type) (W : Type) (d : ℕ) : Type :=
  Ctx X O W → (j : ℕ) → Vector F j → Message F d

/-- The verifier's weighted domain, per stage. -/
abbrev Weights (F X : Type) : Type := X → ℕ → WeightedDomain F

/-- The domain of the normalized round against the point `pt x`: at stage `j`, the points `0, 1`
with the weights `1 - r_j, r_j` (`1 + r_j, r_j` in characteristic two), the check a cofactor of
`eq(r, ·)` meets; past the point, the weights `1, 0`. -/
def normalizedWeights {m : ℕ} (pt : X → Vector F m) : Weights F X :=
  fun x j ↦ if h : j < m then [(0, 1 - (pt x)[j]), (1, (pt x)[j])] else [(0, 1), (1, 0)]

/-- A family of claims to reduce, one stage per number of challenges drawn. -/
structure Family (F X : Type) [Field F] {ι : Type} (O : ι → Type) (W : Type) (d : ℕ) where
  /-- The true claim at stage `j`, given the challenges so far. -/
  claim : Ctx X O W → (j : ℕ) → Vector F j → F
  /-- The honest round polynomial at stage `j`. -/
  poly : Polys F X O W d
  /-- The verifier's weighted domain at stage `j`. -/
  weight : Weights F X
  /-- The side invariant on the challenges. -/
  inv : Ctx X O W → (j : ℕ) → Vector F j → Prop

variable {d : ℕ}

/-- The statement at stage `j`: the public data, the challenges so far, the running claim. -/
abbrev Stmt (X F : Type) (j : ℕ) : Type := X × (Vector F j × F)

/-- The statement between a round's message and its challenge: the stage's statement and the
polynomial received. -/
abbrev MidStmt (X F : Type) (j d : ℕ) : Type := Stmt X F j × Message F d

/-- The context of a stage's input. -/
abbrev ctxOf {j : ℕ} (p : (Stmt X F j × ∀ i, O i) × W) : Ctx X O W := ((p.1.1.1, p.1.2), p.2)

/-- The relation at stage `j`: the invariant holds of the challenges, and the running claim is
the family's. -/
def rel (Φ : Family F X O W d) (j : ℕ) : Set ((Stmt X F j × ∀ i, O i) × W) :=
  {p | Φ.inv (ctxOf p) j p.1.1.2.1 ∧ p.1.1.2.2 = Φ.claim (ctxOf p) j p.1.1.2.1}

/-- The relation between a round's message and its challenge: the stage's relation, and the
polynomial received is the honest one. -/
def relMid (Φ : Family F X O W d) (j : ℕ) : Set ((MidStmt X F j d × ∀ i, O i) × W) :=
  {p | ((p.1.1.1, p.1.2), p.2) ∈ rel Φ j ∧
    p.1.1.2 = Φ.poly (ctxOf ((p.1.1.1, p.1.2), p.2)) j p.1.1.1.2.1}

/-- An honest family, up to stage `m`: the honest polynomial passes the check and evaluates to
the next claim, and the invariant survives every challenge. -/
structure Family.Honest (Φ : Family F X O W d) (m : ℕ) : Prop where
  /-- The honest polynomial's weighted sum over the domain is the claim. -/
  check : ∀ ctx j (c : Vector F j), j < m →
    weightedSum d (Φ.weight ctx.1.1 j) (Φ.poly ctx j c) = Φ.claim ctx j c
  /-- The honest polynomial's value at the challenge is the next claim. -/
  next : ∀ ctx j (c : Vector F j) (x : F), j < m →
    evaluate d (Φ.poly ctx j c) x = Φ.claim ctx (j + 1) (c.push x)
  /-- The invariant survives a challenge. -/
  inv_push : ∀ ctx j (c : Vector F j) (x : F), j < m → Φ.inv ctx j c → Φ.inv ctx (j + 1) (c.push x)

/-! ## The round -/

variable [∀ i, OracleInterface (O i)] (P : Polys F X O W d) (j : ℕ)

/-- The next statement: the challenge appended, the claim replaced by the value `v` of the
polynomial at the challenge. -/
def next (s : Stmt X F j) (v c : F) : Stmt X F (j + 1) := (s.1, (s.2.1.push c, v))

/-- The message: the prover sends the honest polynomial, the verifier records it in the
statement. -/
def sendPoly : Component.Def (Stmt X F j) O W (MidStmt X F j d) O W (say (Message F d)) :=
  Component.sendChecked O (Message F d) (fun p ↦ P (ctxOf p) j p.1.1.2.1) (fun _ _ ↦ true)
    (fun s q ↦ (s, q))

variable [DecidableEq F] (wt : Weights F X)

/-- The verifier's check: the weighted sum of the polynomial over the domain is the running
claim. -/
def check (s : Stmt X F j) (q : Message F d) : Bool :=
  decide (weightedSum d (wt s.1 j) q = s.2.2)

variable [SampleableType F]

/-- The challenge: the verifier rejects unless the recorded polynomial passes the check, draws
the challenge, and carries the polynomial's value there as the next claim. -/
def drawChallenge : Component.Def (MidStmt X F j d) O W (Stmt X F (j + 1)) O W (draw F) :=
  Component.sampleChallenge O F (fun p ↦ check j wt p.1 p.2)
    (fun p c ↦ next j p.1 (evaluate d p.2 c) c)

/-- The round: the message, then the challenge. -/
def round : Component.Def (Stmt X F j) O W (Stmt X F (j + 1)) O W (roundSpec F d) :=
  (sendPoly P j).append (drawChallenge j wt)

/-- Completeness of the message: the honest polynomial is recorded. -/
def sendPolyComplete (Φ : Family F X O W d) :
    Component.Complete (sendPoly Φ.poly j) (rel Φ j) (relMid Φ j) :=
  Component.sendCheckedComplete O (Message F d) _ _ _ fun _ _ _ h ↦ ⟨rfl, h, rfl⟩

/-- Completeness of the challenge of an honest family: the recorded polynomial passes the check
and the next statement is at stage `j + 1`. -/
def drawChallengeComplete (Φ : Family F X O W d) {m : ℕ} (H : Φ.Honest m) (hj : j < m) :
    Component.Complete (drawChallenge j Φ.weight) (relMid Φ j) (rel Φ (j + 1)) :=
  Component.sampleChallengeComplete O F _ _ fun p o w ⟨⟨hinv, hclaim⟩, hq⟩ ↦ by
    refine ⟨?_, fun c ↦ ⟨H.inv_push _ j _ c hj hinv, ?_⟩⟩
    · show check j Φ.weight p.1 p.2 = true
      rw [check, decide_eq_true_eq, hq, hclaim]
      exact H.check _ j _ hj
    · show evaluate d p.2 c = Φ.claim _ (j + 1) (p.1.2.1.push c)
      rw [hq]
      exact H.next _ j _ c hj

/-- The completeness half of a round. -/
def roundComplete (Φ : Family F X O W d) {m : ℕ} (H : Φ.Honest m) (hj : j < m) :
    Component.Complete (round Φ.poly j Φ.weight) (rel Φ j) (rel Φ (j + 1)) :=
  (sendPolyComplete j Φ).append (drawChallengeComplete j Φ H hj)

/-! ## The rounds of a sumcheck -/

/-- The `i` rounds from stage `j` to stage `m = j + i`. With no round left, the statement is
carried across the equality of stages. -/
def rounds (m : ℕ) : (i j : ℕ) → j + i = m →
    Component.Def (Stmt X F j) O W (Stmt X F m) O W (roundsSpec F d i)
  | 0, j, h => Component.passThrough O fun s ↦ (s.1, (Vector.cast (by omega) s.2.1, s.2.2))
  | i + 1, j, h => (round P j wt).append (rounds m i (j + 1) (by omega))

/-- Completeness of the rounds, from those of each round. -/
def roundsComplete (Φ : Family F X O W d) (m : ℕ) (H : Φ.Honest m) :
    (i j : ℕ) → (h : j + i = m) →
      Component.Complete (rounds Φ.poly Φ.weight m i j h) (rel Φ j) (rel Φ m)
  | 0, j, h => Component.passThroughComplete O _ fun s o w hin ↦ by
    have hjm : j = m := by omega
    subst hjm
    simpa only [Vector.cast_rfl] using hin
  | i + 1, j, h =>
    (roundComplete j Φ H (by omega)).append (roundsComplete Φ m H i (j + 1) (by omega))

end Data

end SumcheckRound

end
end LeanerVM.Protocol
