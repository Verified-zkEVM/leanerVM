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
check and evaluates to the next claim (`Family.Consistent`), and the invariant survives every
challenge. Knowledge soundness (`roundSecurity`, `roundsSecurity`, at `d / |F|` per challenge,
for a round that carries no witness) needs it consistent and sound (`Family.Sound`: a challenge
restores a broken invariant at `d` values at most): a recorded polynomial that passes the check
at a wrong claim is not the honest one, and two polynomials of degree `d` agree at `d` points at
most (`card_filter_evaluate_eq_le`; batching by powers is the same count,
`card_filter_powerSum_eq_le`). Without the check, no extractor and state function make the
challenge knowledge sound below error one (`drawChallenge_unchecked_not_rbr`). The oracles and
the witness are passed through untouched.

ArkLib's computable sumcheck (`Sumcheck.Impl.Representation.Message`, a polynomial with a
degree bound queried by evaluation) sums its message over a unit-weight domain and is not an
oracle reduction; this round sends coefficients, as a verifier reading them off a wire does, and
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
`eq(r, ·)` meets; past the point, no domain. -/
def normalizedWeights {m : ℕ} (pt : X → Vector F m) : Weights F X :=
  fun x j ↦ if h : j < m then [(0, 1 - (pt x)[j]), (1, (pt x)[j])] else []

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

/-- A consistent family, up to stage `m`: the honest polynomial passes the check and evaluates
to the next claim. What knowledge soundness needs of the honest polynomials. -/
structure Family.Consistent (Φ : Family F X O W d) (m : ℕ) : Prop where
  /-- The honest polynomial's weighted sum over the domain is the claim. -/
  check : ∀ ctx j (c : Vector F j), j < m →
    weightedSum d (Φ.weight ctx.1.1 j) (Φ.poly ctx j c) = Φ.claim ctx j c
  /-- The honest polynomial's value at the challenge is the next claim. -/
  next : ∀ ctx j (c : Vector F j) (x : F), j < m →
    evaluate d (Φ.poly ctx j c) x = Φ.claim ctx (j + 1) (c.push x)

/-- An honest family, up to stage `m`: consistent, and the invariant survives every
challenge. What completeness needs. -/
structure Family.Honest (Φ : Family F X O W d) (m : ℕ) : Prop extends Family.Consistent Φ m where
  /-- The invariant survives a challenge. -/
  inv_push : ∀ ctx j (c : Vector F j) (x : F), j < m → Φ.inv ctx j c → Φ.inv ctx (j + 1) (c.push x)

/-- A sound family over a finite field, up to stage `m`: a challenge restores a broken invariant
at `d` values at most. What knowledge soundness needs of the invariant. -/
def Family.Sound [Finite F] (Φ : Family F X O W d) (m : ℕ) : Prop :=
  ∀ ctx j (c : Vector F j), j < m → ¬ Φ.inv ctx j c →
    Nat.card {x // Φ.inv ctx (j + 1) (c.push x)} ≤ d

/-- Two distinct messages take the same value at `d` points at most: their difference is a
nonzero polynomial of degree at most `d`. -/
theorem card_filter_evaluate_eq_le [Fintype F] [DecidableEq F] (q q' : Message F d)
    (hne : q ≠ q') :
    (Finset.univ.filter fun x ↦ evaluate d q x = evaluate d q' x).card ≤ d := by
  let p : Polynomial F := ∑ i : Fin (d + 1), Polynomial.monomial (i : ℕ) (q[i] - q'[i])
  have hcoeff : ∀ i : Fin (d + 1), p.coeff i = q[i] - q'[i] := fun i ↦ by
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [ite_eq_right fun h ↦ hji (Fin.ext h)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hp0 : p ≠ 0 := by
    intro hp
    apply hne
    ext i hi
    have := hcoeff ⟨i, hi⟩
    rw [hp, Polynomial.coeff_zero] at this
    exact (sub_eq_zero.mp this.symm)
  have hdeg : p.natDegree ≤ d := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ ↦ ?_
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ i.isLt)
  have heval : ∀ x : F, p.eval x = evaluate d q x - evaluate d q' x := fun x ↦ by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial, evaluate,
      ← Finset.sum_sub_distrib, sub_mul]
  refine (Polynomial.card_le_degree_of_subset_roots (p := p) ?_).trans hdeg
  intro x hx
  rw [Finset.mem_val, Finset.mem_filter] at hx
  rw [Polynomial.mem_roots hp0, Polynomial.IsRoot, heval, hx.2, sub_self]

/-- Two different value vectors combine to the same scalar, by the powers of the combiner, at
`n - 1` combiners at most: the escape count of batching by powers. -/
theorem card_filter_powerSum_eq_le [Fintype F] [DecidableEq F] {n : ℕ} (a b : Fin n → F)
    (hne : a ≠ b) :
    (Finset.univ.filter fun l : F ↦ ∑ t, l ^ t.val * a t = ∑ t, l ^ t.val * b t).card ≤
      n - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero => exact absurd (funext fun t ↦ t.elim0) hne
    | succ k => exact ⟨k, rfl⟩
  have hne' : (Vector.ofFn a : Message F k) ≠ Vector.ofFn b := fun h ↦
    hne (funext fun t ↦ by simpa using congrArg (fun v : Vector F (k + 1) ↦ v[t]) h)
  have hev : ∀ (f : Fin (k + 1) → F) (l : F),
      evaluate k (Vector.ofFn f) l = ∑ t, l ^ t.val * f t := fun f l ↦
    Finset.sum_congr rfl fun t _ ↦ by simp [mul_comm]
  have hfilter : (Finset.univ.filter fun l : F ↦ ∑ t, l ^ t.val * a t = ∑ t, l ^ t.val * b t) =
      Finset.univ.filter fun l ↦ evaluate k (Vector.ofFn a) l = evaluate k (Vector.ofFn b) l := by
    refine Finset.filter_congr fun l _ ↦ ?_
    rw [hev, hev]
  rw [hfilter, Nat.add_sub_cancel]
  exact card_filter_evaluate_eq_le _ _ hne'

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

/-- A round is front: its verifier reads the polynomial and the challenge off the transcript. -/
def roundFront : Component.Front (round P j wt) :=
  (Component.sendCheckedFront O (Message F d) _ _ _).append (Component.sampleFront O F _ _)

/-! ## The round's knowledge soundness -/

/-- The security half of the message: no challenge, the polynomial recorded. -/
def sendPolySecurity (Φ : Family F X O W d) :
    Component.Security (sendPoly Φ.poly j) (rel Φ j) (relMid Φ j) (sayError (Message F d)) :=
  Component.sendCheckedSecurity O (Message F d) _ _ _ fun _ _ _ _ _ h ↦ h.1

variable [Finite F] [Subsingleton W]

omit [∀ i, OracleInterface (O i)] [SampleableType F] in
/-- From a recorded polynomial that passes the check, a challenge lands in the next relation
while the stage's relation failed at `d` values at most: if the invariant failed, by the family's
soundness; otherwise the polynomial is not the honest one, since the honest one sums to the
honest claim and the running claim differs or the polynomial does, and two distinct polynomials
agree at `d` points at most. The round carries no witness. -/
theorem card_badChallenge_le (Φ : Family F X O W d) {m : ℕ} (H : Φ.Consistent m) (S : Φ.Sound m)
    (hj : j < m) (p : MidStmt X F j d) (o : ∀ i, O i) (hc : check j Φ.weight p.1 p.2 = true) :
    Nat.card {x // Component.badChallenge O F (fun p c ↦ next j p.1 (evaluate d p.2 c) c)
      (relIn := relMid Φ j) (relOut := rel Φ (j + 1)) p o x} ≤ d := by
  have := Fintype.ofFinite F
  classical
  rw [natCard_subtype_eq_card_filter]
  by_cases hW : Nonempty W
  · obtain ⟨w⟩ := hW
    obtain ⟨s, q⟩ := p
    have hbad : ∀ x, Component.badChallenge O F (fun p c ↦ next j p.1 (evaluate d p.2 c) c)
        (relIn := relMid Φ j) (relOut := rel Φ (j + 1)) (s, q) o x ↔
        ((((s, q), o), w) ∉ relMid Φ j ∧
          ((next j s (evaluate d q x) x, o), w) ∈ rel Φ (j + 1)) := by
      intro x
      constructor
      · rintro ⟨w', h₁, h₂⟩
        rw [Subsingleton.elim w' w] at h₁ h₂
        exact ⟨h₁, h₂⟩
      · exact fun h ↦ ⟨w, h⟩
    simp only [hbad]
    rw [check, decide_eq_true_eq] at hc
    by_cases hinv : Φ.inv ((s.1, o), w) j s.2.1
    · by_cases hqh : q = Φ.poly ((s.1, o), w) j s.2.1
      · -- The honest polynomial passing the check at the running claim: the stage's relation
        -- holds, so no challenge is bad.
        refine le_trans (le_of_eq ?_) (Nat.zero_le d)
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro x _ ⟨hmid, -⟩
        refine hmid ⟨⟨hinv, ?_⟩, hqh⟩
        show s.2.2 = Φ.claim ((s.1, o), w) j s.2.1
        rw [← H.check ((s.1, o), w) j s.2.1 hj, ← hqh]
        exact hc.symm
      · -- Another polynomial: bad challenges are where it agrees with the honest one.
        refine (Finset.card_le_card fun x hx ↦ ?_).trans
          (card_filter_evaluate_eq_le q (Φ.poly ((s.1, o), w) j s.2.1) hqh)
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have hnext : evaluate d q x = Φ.claim ((s.1, o), w) (j + 1) (s.2.1.push x) := hx.2.2.2
        rw [hnext, H.next ((s.1, o), w) j s.2.1 x hj]
    · -- The invariant fails: a bad challenge restores it.
      refine (Finset.card_le_card fun x hx ↦ ?_).trans
        ((natCard_subtype_eq_card_filter _).symm.trans_le
          (S ((s.1, o), w) j s.2.1 hj hinv))
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, hx.2.2.1⟩
  · refine le_trans (le_of_eq ?_) (Nat.zero_le d)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x _ ⟨w, -⟩
    exact hW ⟨w⟩

/-- The security half of the challenge, at `d / |F|`. -/
def drawChallengeSecurity (Φ : Family F X O W d) {m : ℕ} (H : Φ.Consistent m)
    (S : Φ.Sound m) (hj : j < m) :
    Component.Security (drawChallenge j Φ.weight) (relMid Φ j) (rel Φ (j + 1))
      (drawError F ((d : ℝ≥0) / (Nat.card F : ℝ≥0))) :=
  Component.sampleChallengeSecurity O F _ _ d fun p o hc ↦ card_badChallenge_le j Φ H S hj p o hc

/-- The security half of a round of a consistent, sound family: the message's then the
challenge's, the error on the challenge. -/
def roundSecurity (Φ : Family F X O W d) {m : ℕ} (H : Φ.Consistent m)
    (S : Φ.Sound m) (hj : j < m) :
    Component.Security (round Φ.poly j Φ.weight) (rel Φ j) (rel Φ (j + 1))
      (errAppend (sayError (Message F d)) (drawError F ((d : ℝ≥0) / (Nat.card F : ℝ≥0)))) :=
  (sendPolySecurity j Φ).append (drawChallengeSecurity j Φ H S hj)

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

omit [DecidableEq F] [Finite F] in
/-- Without its check, the challenge is not knowledge sound below error one, whatever the
extractor and the state function: from the honest polynomial at a wrong running claim, every
challenge lands in the next relation. The check is load-bearing. -/
theorem drawChallenge_unchecked_not_rbr (Φ : Family F X O W d) {m : ℕ} (H : Φ.Consistent m)
    (hj : j < m) {WitMid : Fin 2 → Type}
    {E : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) (MidStmt X F j d × ∀ i, O i) W W
      (draw F) WitMid}
    {kSF : Verifier.KnowledgeStateFunction init impl (relMid Φ j) (rel Φ (j + 1))
      (Component.sampleVerifier O F (fun _ ↦ true)
        (fun p : MidStmt X F j d ↦ fun c ↦ next j p.1 (evaluate d p.2 c) c)).toVerifier E}
    {ε : (draw F).ChallengeIdx → ℝ≥0}
    (h : Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl (relMid Φ j) (rel Φ (j + 1))
      (Component.sampleVerifier O F (fun _ ↦ true)
        (fun p : MidStmt X F j d ↦ fun c ↦ next j p.1 (evaluate d p.2 c) c)).toVerifier
      WitMid E kSF ε)
    (s : Stmt X F j) (o : ∀ i, O i) (w : W) (hclaim : s.2.2 ≠ Φ.claim ((s.1, o), w) j s.2.1)
    (hinv : ∀ x, Φ.inv ((s.1, o), w) (j + 1) (s.2.1.push x)) : 1 ≤ ε ⟨0, rfl⟩ :=
  Component.sampleChallenge_not_rbr O F _ _ init impl h (s, Φ.poly ((s.1, o), w) j s.2.1) o
    (fun w' hmid ↦ by
      rw [Subsingleton.elim w' w] at hmid
      exact hclaim hmid.1.2)
    rfl w fun x ↦ ⟨hinv x, H.next ((s.1, o), w) j s.2.1 x hj⟩

/-! ## The rounds of a sumcheck -/

/-- The `i` rounds from stage `j` to stage `m = j + i`. With no round left, the statement is
carried across the equality of stages. -/
def rounds (m : ℕ) : (i j : ℕ) → j + i = m →
    Component.Def (Stmt X F j) O W (Stmt X F m) O W (roundsSpec F d i)
  | 0, j, h => Component.passThrough O fun s ↦ (s.1, (Vector.cast (by omega) s.2.1, s.2.2))
  | i + 1, j, h => (round P j wt).append (rounds m i (j + 1) (by omega))

/-- The rounds are front, from each round's. -/
def roundsFront (m : ℕ) : (i j : ℕ) → (h : j + i = m) → Component.Front (rounds P wt m i j h)
  | 0, _, _ => Component.passThroughFront O _
  | i + 1, j, _ => (roundFront P j wt).append (roundsFront m i (j + 1) (by omega))

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

/-- The security half of the rounds, from each round's, at `d / |F|` per challenge. -/
def roundsSecurity (Φ : Family F X O W d) (m : ℕ) (H : Φ.Consistent m) (S : Φ.Sound m) :
    (i j : ℕ) → (h : j + i = m) →
      Component.Security (rounds Φ.poly Φ.weight m i j h) (rel Φ j) (rel Φ m)
        (roundsError F d ((d : ℝ≥0) / (Nat.card F : ℝ≥0)) i)
  | 0, j, h =>
    Component.passThroughSecurity O _
      (fun s o w hout ↦ by
        have hjm : j = m := by omega
        subst hjm
        simpa only [Vector.cast_rfl] using hout)
      (fun s o w hin ↦ by
        have hjm : j = m := by omega
        subst hjm
        simpa only [Vector.cast_rfl] using hin)
  | i + 1, j, h =>
    (roundSecurity j Φ H S (by omega)).append (roundsSecurity Φ m H S i (j + 1) (by omega))

end Data

end SumcheckRound

end
end LeanerVM.Protocol
