import LeanerVM.Protocol.PublicInput
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.ToArkLib.Refutation

/-!
# Public-input phase tests

Every guard changes one thing.

* **The point.** `linePoint` is `(r, 0)` on two variables, and the extension there is the line
  through cells 0 and 1, not through cells 2 and 3.
* **The check**, on the toy, whose one public line is column 2 with cells `(statement, 0)`: it
  accepts the line's value and rejects a wrong value, a missing value and an extra value.
* **A wrong stack.** On `badLine`, whose cell 1 differs from the statement's, a prover that sends
  its column's true evaluation is rejected by the check, except at the one bad challenge
  `r = 0`; and the pooled claim is false of that stack, except at that challenge. A wrong
  statement behaves the same way, with bad challenge `r = 1`.
* **Which values are sent.** With no value sent the message is empty and the line is still
  pooled. On three lines shaped like the memory limbs, two values sent and a third line with
  cells `(0, 0)`, a stack with a nonzero top cell passes the check and fails the third claim,
  and the pool without the third claim accepts it.
* **The two checks differ.** At one challenge the equation on the two public words holds of a
  wrong stack's true evaluations, and the check per limb rejects them.
* **The pool reads the message.** A wrong value that passes no check is what the pool would
  carry; at the expected values the pool from the message is the pool of the lines' claims; a
  message without one value per sent line is rejected before any check.
* **The phase** fills its slot: two rounds, a challenge then a message, its verifier never
  reads the stack, and its two halves typecheck against the spine's seams at the slot's error.
* **The check is load-bearing.** On a statement outside the table seam, a prover that sends its
  stack's true values is accepted with a pool inside the public seam by the verifier without
  the check, by the verifier that checks the first value only, and by the verifier that pools
  an unsent line's claim at zero; so none of the three has a round-by-round knowledge error
  below one, whatever extractor and state function it is given. The verifier whose check swaps
  the two cells, and the one with an extra check on the message's length, reject the honest
  prover: neither is perfectly complete.

The toy's table seam carries three received claims, one per column of its table; the fixtures
give them true values at a cube point. A plain file, so `#guard` evaluates the compiled
definitions. Values of `E` written with numerals are named as definitions before a guard uses
them.
-/

namespace LeanerVMTests.Protocol.PublicInput

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.PublicInput LeanerVM.Protocol.Toy
  CompPoly OracleComp

/-- A column claim is decided by evaluating the column's extension. Spelled with
`inferInstanceAs` on the unfolded equation: the instance `by unfold ColumnClaim.Holds;
infer_instance` elaborates but does not terminate under `#guard`. -/
instance {I : M3Instance} (q : Column I.μ) (c : ColumnClaim I) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable (CMlPolynomialEval.eval₂Mle (I.column q c.col).values
    (algebraMap K E) c.point = c.value))

/-- What a prover that answers truthfully sends: the extensions of its own columns at
`(r, 0, …, 0)`, for the lines whose value is sent. -/
def trueValues (I : M3Instance) (q : Column I.μ) (input : I.Stmt) (r : E) : List E :=
  ((I.publicLines input).toList.filter (·.sent)).map fun l ↦
    CMlPolynomialEval.eval₂Mle (I.column q l.col).values (algebraMap K E) (linePoint l.pos r)

/-- A truthful prover's message has one value per sent line. -/
theorem trueValues_length (I : M3Instance) (q : Column I.μ) (input : I.Stmt) (r : E) :
    (trueValues I q input r).length = sentCount I (I.publicLines input) :=
  List.length_map ..

/-- Three received claims on the three columns of an instance's first table, at the cube point
`x`, with the given values: what the table seam carries into the phase. -/
def received (I : M3Instance) (h : I.tableClaims = 3) (h0 : 0 < I.ntab)
    (hw : 3 ≤ I.width ⟨0, h0⟩) (hτ : I.τ ⟨0, h0⟩ = 1) (x : Fin 2) (v : Fin 3 → K) :
    Vector (ColumnClaim I) I.tableClaims :=
  Vector.cast h.symm (Vector.ofFn fun i ↦
    ⟨⟨⟨0, h0⟩, ⟨i.val, by omega⟩⟩, Vector.cast hτ.symm (boolVec x), ofK (v i)⟩)

/-! ## The point -/

/-- The table `[1, 2, 3, 4]` on two variables. -/
def table : CMlPolynomialEval K 2 := #v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4]

/-- The point `(y, 0)`. -/
def onLine : List E := [y, 0]

/-- The point `(y, 1)`: second coordinate `1`. -/
def offLine : Vector E 2 := #v[y, ofK 1]

#guard (linePoint (n := 2) (by decide) y).toList = onLine
-- On the line: `(1 - y)·1 + y·2`, the line through cells 0 and 1.
#guard CMlPolynomialEval.eval₂Mle table (algebraMap K E) (linePoint (n := 2) (by decide) y) =
  (1 - y) * ofK 1 + y * ofK (K.ofBits 2)
-- Off the line the second coordinate selects cells 2 and 3.
#guard CMlPolynomialEval.eval₂Mle table (algebraMap K E) offLine =
  (1 - y) * ofK (K.ofBits 3) + y * ofK (K.ofBits 4)
#guard CMlPolynomialEval.eval₂Mle table (algebraMap K E) offLine ≠
  (1 - y) * ofK 1 + y * ofK (K.ofBits 2)

/-! ## The check -/

/-- A second sampled challenge, `y² + 1`. -/
def r₂ : E := y * y + 1

/-- The toy's statement `1` with the three columns' cells 0 received. -/
def stmt1 : K × TableOut toy :=
  (1, ⟨received toy (by decide) (by decide) (by decide) (by decide) 0 ![1, 1, 1]⟩)

/-- The toy's statement `0` with the same received claims. -/
def stmt0 : K × TableOut toy :=
  (0, ⟨received toy (by decide) (by decide) (by decide) (by decide) 0 ![1, 1, 1]⟩)

/-- The value of the toy's line at statement `1` and challenge `y`: `(1 + y)·1 + y·0`. -/
def good : List E := [1 + y]

/-- A wrong value. -/
def wrong : List E := [y]

/-- One value too many. -/
def extra : List E := [1 + y, 0]

-- The expected value of the one line, and the check on it.
#guard expectedValues toy (1: K) y = good
-- The check accepts the value and rejects a wrong, a missing and an extra value.
#guard check toy stmt1 y good
#guard ¬ check toy stmt1 y wrong
#guard ¬ check toy stmt1 y []
#guard ¬ check toy stmt1 y extra

-- On the honest stack, a prover that answers truthfully sends the expected values.
#guard trueValues toy honest (1: K) y = expectedValues toy (1: K) y
#guard trueValues toy honest (1: K) r₂ = expectedValues toy (1: K) r₂
#guard trueValues toy honest (1: K) 0 = expectedValues toy (1: K) 0

/-! ## A wrong stack -/

/-- Column 2 changed to `[1, 1]`: cell 1 is not the statement's `0`. -/
def badLine : Column 3 := ⟨#v[1, 1, 1, 1, 1, 1, 0, 0]⟩

-- A prover that sends its column's true evaluation is rejected by the check at a sampled
-- challenge, and accepted at the one bad challenge `r = 0`, where the line is cell 0 alone.
#guard ¬ check toy stmt1 y (trueValues toy badLine 1 y)
#guard ¬ check toy stmt1 r₂ (trueValues toy badLine 1 r₂)
#guard check toy stmt1 0 (trueValues toy badLine 1 0)

-- The same event on the claims: every pooled claim holds of the honest stack; of the wrong
-- stack one fails at a sampled challenge, and all hold at the bad challenge. So the bound
-- `1/|E|` is attained, and a prover that sends the expected value passes the check with a
-- claim that is false of its stack.
#guard ∀ c ∈ (pooled toy stmt1 y).2.columns.toList, c.Holds honest
#guard ¬ ∀ c ∈ (pooled toy stmt1 y).2.columns.toList, c.Holds badLine
#guard ∀ c ∈ (pooled toy stmt1 0).2.columns.toList, c.Holds badLine

-- A wrong statement (cell 0 is `0`, the honest stack's is `1`): rejected at a sampled
-- challenge, accepted at the one bad challenge `r = 1`, where `(1 + r)·cell0` vanishes.
#guard ¬ check toy stmt0 y (trueValues toy honest 0 y)
#guard check toy stmt0 1 (trueValues toy honest 0 1)

/-! ## The pool -/

-- The verifier keeps the statement and pools the received claims first, then the line.
#guard (pooled toy stmt1 y).1 = 1
#guard ((pooled toy stmt1 y).2.columns.toList.map fun c ↦ c.col) =
  [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 2⟩]
#guard ((pooled toy stmt1 y).2.columns.toList.map fun c ↦ c.value) = [1, 1, 1] ++ good
-- The pool the verifier builds reads the message: at the expected values it is the pool of
-- the lines' claims, and at a wrong value it carries that value, which is why the check must
-- reject it.
#guard ((pooledFrom toy stmt1 y good rfl).2.columns.toList.map fun c ↦ c.value) =
  ((pooled toy stmt1 y).2.columns.toList.map fun c ↦ c.value)
#guard ((pooledFrom toy stmt1 y wrong rfl).2.columns.toList.map fun c ↦ c.value) =
  [1, 1, 1] ++ wrong
#guard ¬ ∀ c ∈ (pooledFrom toy stmt1 y wrong rfl).2.columns.toList, c.Holds honest
-- A message without one value per sent line is rejected by every verifier of the phase's
-- shape, the one without a check included.
#guard accepts toy (check toy) stmt1 y good
#guard ¬ accepts toy (fun _ _ _ ↦ true) stmt1 y extra
#guard ¬ accepts toy (fun _ _ _ ↦ true) stmt1 y []

/-! ## Which values are sent -/

/-- The toy with its line's value not sent. -/
abbrev noneSent : M3Instance :=
  { toy with publicLines := fun v ↦ #v[⟨⟨0, 2⟩, v, 0, false, by decide⟩] }

/-- Its statement `1` with the received claims. -/
def stmtNone : K × TableOut noneSent :=
  (1, ⟨received noneSent (by decide) (by decide) (by decide) (by decide) 0 ![1, 1, 1]⟩)

-- The message is empty, a value is rejected, and the line is pooled all the same.
#guard expectedValues noneSent (1: K) y = []
#guard check noneSent stmtNone y []
#guard ¬ check noneSent stmtNone y good
#guard ((pooled noneSent stmtNone y).2.columns.toList.map fun c ↦ c.value) = [1, 1, 1] ++ good
#guard ¬ ∀ c ∈ (pooled noneSent stmtNone y).2.columns.toList, c.Holds badLine

/-- Three lines shaped like the memory limbs: two with their value sent, and a third with cells
`(0, 0)` and no value sent. -/
abbrev threeLimbs : M3Instance :=
  { toy with
    nLines := 3
    publicLines := fun v ↦
      #v[⟨⟨0, 0⟩, v, 1, true, by decide⟩, ⟨⟨0, 1⟩, 1, 1, true, by decide⟩,
        ⟨⟨0, 2⟩, 0, 0, false, by decide⟩] }

/-- Its statement `1` with the three columns' cells 1 received. -/
def stmtLimbs : K × TableOut threeLimbs :=
  (1, ⟨received threeLimbs (by decide) (by decide) (by decide) (by decide) 1 ![1, 1, 0]⟩)

/-- A stack whose three columns hold their lines: `[1, 1]`, `[1, 1]`, `[0, 0]`. -/
def goodLimbs : Column 3 := ⟨#v[1, 1, 1, 1, 0, 0, 0, 0]⟩

/-- The top column's cell 0 changed to `1`. -/
def badTopLimb : Column 3 := ⟨#v[1, 1, 1, 1, 1, 0, 0, 0]⟩

/-- The three lines' values at any challenge: `(1 + r) + r`, twice, and `0`. -/
def limbValues : List E := [1, 1, 0]

-- Two values are sent and three claims are pooled after the received ones, the third with
-- value `0`.
#guard (expectedValues threeLimbs (1: K) y).length = 2
#guard ((pooled threeLimbs stmtLimbs y).2.columns.toList.map fun c ↦ c.value).drop 3 =
  limbValues
#guard ((pooled threeLimbs stmtLimbs y).2.columns.toList.map fun c ↦ c.col).drop 3 =
  [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩]
#guard ∀ c ∈ (pooled threeLimbs stmtLimbs y).2.columns.toList, c.Holds goodLimbs
-- The wrong top cell passes the check, which sees the two sent values only, and fails the third
-- claim; the pool without the third claim accepts the stack.
#guard check threeLimbs stmtLimbs y (trueValues threeLimbs badTopLimb 1 y)
#guard ¬ ∀ c ∈ (pooled threeLimbs stmtLimbs y).2.columns.toList, c.Holds badTopLimb
#guard ∀ c ∈ ((pooled threeLimbs stmtLimbs y).2.columns.toList.take 5), c.Holds badTopLimb

/-! ## The check per limb and the check on the words differ -/

/-- Two limbs with zero public words, both values sent. -/
abbrev twoLimbs : M3Instance :=
  { toy with
    nLines := 2
    publicLines := fun _ ↦
      #v[⟨⟨0, 0⟩, 0, 0, true, by decide⟩, ⟨⟨0, 1⟩, 0, 0, true, by decide⟩] }

/-- Its statement with the received claims. -/
def stmtTwo : K × TableOut twoLimbs :=
  (0, ⟨received twoLimbs (by decide) (by decide) (by decide) (by decide) 0 ![0, 1, 0]⟩)

/-- A stack whose two limbs are `[0, 1]` and `[1, 0]`: both violate the public input. -/
def badLimbs : Column 3 := ⟨#v[0, 1, 1, 0, 0, 0, 0, 0]⟩

/-- The challenge `y / (1 + y)`. -/
def rStar : E := y / (1 + y)

/-- The two true evaluations at that challenge: `r` and `1 + r`. -/
def atStar : List E := [rStar, 1 + rStar]

/-- The equation on the two public words, `c₀ + y·c₁ = (1 + r)·w₀ + r·w₁`, at zero words. -/
def wordsEquation (c₀ c₁ : E) : Bool := c₀ + y * c₁ == 0

#guard trueValues twoLimbs badLimbs 0 rStar = atStar
-- The equation on the words holds of the true evaluations; the check per limb rejects them.
#guard wordsEquation rStar (1 + rStar)
#guard ¬ check twoLimbs stmtTwo rStar atStar
-- At a sampled challenge both reject.
#guard ¬ wordsEquation y (1 + y)
#guard ¬ check twoLimbs stmtTwo y (trueValues twoLimbs badLimbs 0 y)

/-! ## The phase in its slot -/

/-- Two rounds: the challenge, then the prover's values. -/
example : pubSpec.dir 0 = .V_to_P := rfl

example : pubSpec.dir 1 = .P_to_V := rfl

/-- The slot's error is `1/|E|` on the one challenge. -/
example (i : pubSpec.ChallengeIdx) : pubError i = overE 1 := rfl

/-- The verifier never reads the stack: it is a front verifier. -/
example : FrontVerifier []ₒ (K × TableOut toy) (K × PubOut toy) pubSpec :=
  PublicInput.verifier toy

/-- The two halves typecheck against the two seams, at the slot's error. -/
example : Phase.Complete toy (publicInputPhase toy).toDef (Seam.table toy) (Seam.pub toy) :=
  publicInputComplete toy

example : Phase.Security toy (publicInputPhase toy).toDef (Seam.table toy) (Seam.pub toy)
    pubError :=
  publicInputSecurity toy

/-- The phase is one field of a bundle: with the four other phases and their proofs, the master
completeness theorem applies. -/
example (P : Phases toy) (C : P.Complete) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop P).perfectCompleteness init impl (M3Rel toy) (Seam.done toy) :=
  piop_perfectCompleteness P C init impl

/-! ## The check is load-bearing -/

section Refutations

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

/-- Three received claims true of a stack by construction: the three columns of the first
table at the cube point `0`, each at the value its extension takes there. -/
def receivedTrue (I : M3Instance) (h : I.tableClaims = 3) (h0 : 0 < I.ntab)
    (hw : 3 ≤ I.width ⟨0, h0⟩) (hτ : I.τ ⟨0, h0⟩ = 1) (q : Column I.μ) :
    Vector (ColumnClaim I) I.tableClaims :=
  Vector.cast h.symm (Vector.ofFn fun i : Fin 3 ↦
    ⟨⟨⟨0, h0⟩, ⟨i.val, by omega⟩⟩, Vector.cast hτ.symm (boolVec 0),
      CMlPolynomialEval.eval₂Mle (I.column q ⟨⟨0, h0⟩, ⟨i.val, by omega⟩⟩).values
        (algebraMap K E) (Vector.cast hτ.symm (boolVec 0))⟩)

theorem receivedTrue_holds (I : M3Instance) (h : I.tableClaims = 3) (h0 : 0 < I.ntab)
    (hw : 3 ≤ I.width ⟨0, h0⟩) (hτ : I.τ ⟨0, h0⟩ = 1) (q : Column I.μ) :
    ∀ c ∈ (receivedTrue I h h0 hw hτ q).toList, c.Holds q := by
  intro c hc
  simp only [receivedTrue, Vector.toList_cast, Vector.toList_ofFn, List.mem_ofFn] at hc
  obtain ⟨i, rfl⟩ := hc
  rfl

/-- A stack as the one oracle. -/
def oracleOf {I : M3Instance} (q : Column I.μ) : ∀ i, TheOracle I i := fun _ ↦ q

/-- An instance without a Flock region has nothing to hold there. -/
theorem aux_of_none {I : M3Instance} (h : I.flock = none) (q : Column I.μ) : I.aux q := by
  intro r hr
  rw [h] at hr
  exact (Option.not_mem_none r hr).elim

/-- Rounds after the challenge are the prover's. -/
theorem later_P_to_V : ∀ j : Fin 2, 0 < j.val → pubSpec.dir j = .P_to_V := by
  intro j hj
  fin_cases j
  · exact absurd hj (Nat.lt_irrefl 0)
  · rfl

/-- The full transcript with challenge `c` and message `m`, as the prefix of length one
followed by the message. -/
abbrev fullOf (c : pubSpec.Challenge ⟨0, rfl⟩) (m : List E) : pubSpec.FullTranscript :=
  Fin.snoc (Transcript.concat c fun j ↦ Fin.elim0 j) m

theorem fullOf_take (c : pubSpec.Challenge ⟨0, rfl⟩) (m : List E) :
    (fullOf c m).take 1 (by decide) = Transcript.concat c fun j ↦ Fin.elim0 j := by
  funext j
  show Fin.snoc (α := fun i ↦ pubSpec.Type i) (Transcript.concat c fun j ↦ Fin.elim0 j) m
    (Fin.castSucc j) = _
  exact Fin.snoc_castSucc _ _ j

/-! ### The check removed -/

/-- The verifier that accepts every message and pools the values sent. -/
abbrev noCheck : FrontVerifier []ₒ (K × TableOut toy) (K × PubOut toy) pubSpec :=
  verifierWith toy (fun _ _ _ ↦ true) (pooledFrom toy)

/-- The statement `1` with the received claims true of `badLine`, whose line fails. -/
def stmtBad : K × TableOut toy :=
  (1, ⟨receivedTrue toy (by decide) (by decide) (by decide) (by decide) badLine⟩)

theorem stmtBad_not_table : ((stmtBad, oracleOf badLine), ()) ∉ Seam.table toy :=
  fun h ↦ absurd (h.2.1 ⟨⟨0, 2⟩, 1, 0, true, by decide⟩ (by simp [stmtBad])).2 (by decide)

/-- At every challenge, the verdict on the true values of `badLine` is in the public seam. -/
theorem noCheck_pub (c : E) :
    ((verdict toy (pooledFrom toy) stmtBad c (trueValues toy badLine 1 c), oracleOf badLine),
      ()) ∈ Seam.pub toy := by
  refine ⟨fun cl hcl ↦ ?_, aux_of_none rfl _⟩
  rw [verdict, dite_eq_left (show (trueValues toy badLine 1 c).length =
    sentCount toy (toy.publicLines stmtBad.1) from trueValues_length toy badLine 1 c)] at hcl
  simp only [pooledFrom, Vector.toList_append, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · exact receivedTrue_holds toy (by decide) (by decide) (by decide) (by decide) badLine cl hcl
  · simp only [claimsFrom, claimsWith, Vector.toList_ofFn, List.mem_ofFn] at hcl
    obtain ⟨i, rfl⟩ := hcl
    fin_cases i
    rfl

/-- Without the check there is no round-by-round knowledge error below one: at `stmtBad`, a
prover that sends its stack's true value at any challenge is accepted with a pool inside the
public seam. Whatever the extractor and the state function. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    {WitMid : Fin 3 → Type}
    (Ext : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
      ((K × TableOut toy) × ∀ i, TheOracle toy i) Unit Unit pubSpec WitMid)
    (kSF : (noCheck.toOracleVerifier (TheOracle toy)).toVerifier.KnowledgeStateFunction init
      impl (Seam.table toy) (Seam.pub toy) Ext)
    (ε : pubSpec.ChallengeIdx → ℝ≥0)
    (h : (noCheck.toOracleVerifier (TheOracle toy)).toVerifier.rbrKnowledgeSoundnessWorstCaseWith
      init impl (Seam.table toy) (Seam.pub toy) WitMid Ext kSF ε) :
    1 ≤ ε ⟨0, rfl⟩ :=
  Verifier.not_rbr_zero h ⟨0, rfl⟩ rfl later_P_to_V (stmtBad, oracleOf badLine)
    (fun _ h ↦ stmtBad_not_table h) (fun j ↦ Fin.elim0 j) fun c ↦
      ⟨fullOf c (trueValues toy badLine 1 c), fullOf_take c _, (),
        Verifier.GuardedForm.probEvent_pos_of_check (guardedWith toy _ _) init impl _ _ _
          (by
            show accepts toy (fun _ _ _ ↦ true) stmtBad c (trueValues toy badLine 1 c) = true
            simp only [accepts, Bool.and_true, decide_eq_true_eq]
            exact trueValues_length toy badLine 1 c)
          (noCheck_pub c)⟩

/-! ### The check weakened to its first value -/

/-- The verifier that checks the first value only, on `twoLimbs`. -/
abbrev firstOnly : FrontVerifier []ₒ (K × TableOut twoLimbs) (K × PubOut twoLimbs) pubSpec :=
  verifierWith twoLimbs
    (fun s r cs ↦ decide (cs.head? = (expectedValues twoLimbs s.1 r).head?))
    (pooledFrom twoLimbs)

/-- Limb 0 is `[0, 0]`, as its line says; limb 1 is `[1, 0]`, against its line. -/
def oneBadLimb : Column 3 := ⟨#v[0, 0, 1, 0, 0, 0, 0, 0]⟩

/-- The statement `0` with the received claims true of `oneBadLimb`. -/
def stmtOneBad : K × TableOut twoLimbs :=
  (0, ⟨receivedTrue twoLimbs (by decide) (by decide) (by decide) (by decide) oneBadLimb⟩)

theorem stmtOneBad_not_table : ((stmtOneBad, oracleOf oneBadLimb), ()) ∉ Seam.table twoLimbs :=
  fun h ↦ absurd (h.2.1 ⟨⟨0, 1⟩, 0, 0, true, by decide⟩ (by simp)).1 (by decide)

/-- The message that passes the first-value check: the expected value of limb 0, then the true
value of limb 1 on `oneBadLimb`, the line through its cells `1, 0` at `c`. -/
def firstOnlyMsg (c : E) : List E :=
  [lineValue twoLimbs c ⟨⟨0, 0⟩, 0, 0, true, by decide⟩, 1 - c]

theorem firstOnly_pub (c : E) :
    ((verdict twoLimbs (pooledFrom twoLimbs) stmtOneBad c (firstOnlyMsg c), oracleOf oneBadLimb),
      ()) ∈ Seam.pub twoLimbs := by
  have c0 : (twoLimbs.column oneBadLimb ⟨0, 0⟩).values.get ⟨0, by decide⟩ = 0 := by decide
  have c1 : (twoLimbs.column oneBadLimb ⟨0, 0⟩).values.get ⟨1, by decide⟩ = 0 := by decide
  have d0 : (twoLimbs.column oneBadLimb ⟨0, 1⟩).values.get ⟨0, by decide⟩ = 1 := by decide
  have d1 : (twoLimbs.column oneBadLimb ⟨0, 1⟩).values.get ⟨1, by decide⟩ = 0 := by decide
  refine ⟨fun cl hcl ↦ ?_, aux_of_none rfl _⟩
  rw [verdict, dite_eq_left (show (firstOnlyMsg c).length =
    sentCount twoLimbs (twoLimbs.publicLines stmtOneBad.1) from rfl)] at hcl
  simp only [pooledFrom, Vector.toList_append, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · exact receivedTrue_holds twoLimbs (by decide) (by decide) (by decide) (by decide) oneBadLimb
      cl hcl
  · simp only [claimsFrom, claimsWith, Vector.toList_ofFn, List.mem_ofFn] at hcl
    obtain ⟨i, rfl⟩ := hcl
    fin_cases i
    · show CMlPolynomialEval.eval₂Mle (twoLimbs.column oneBadLimb ⟨0, 0⟩).values
        (algebraMap K E) (linePoint (by decide) c) = lineValue twoLimbs c _
      rw [eval₂Mle_linePoint, c0, c1]
      simp [lineValue]
    · show CMlPolynomialEval.eval₂Mle (twoLimbs.column oneBadLimb ⟨0, 1⟩).values
        (algebraMap K E) (linePoint (by decide) c) = 1 - c
      rw [eval₂Mle_linePoint, d0, d1]
      simp

/-- Checking the first value only leaves no round-by-round knowledge error below one: the
second value is pooled unchecked. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    {WitMid : Fin 3 → Type}
    (Ext : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
      ((K × TableOut twoLimbs) × ∀ i, TheOracle twoLimbs i) Unit Unit pubSpec WitMid)
    (kSF : (firstOnly.toOracleVerifier (TheOracle twoLimbs)).toVerifier.KnowledgeStateFunction
      init impl (Seam.table twoLimbs) (Seam.pub twoLimbs) Ext)
    (ε : pubSpec.ChallengeIdx → ℝ≥0)
    (h : (firstOnly.toOracleVerifier
      (TheOracle twoLimbs)).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
        (Seam.table twoLimbs) (Seam.pub twoLimbs) WitMid Ext kSF ε) :
    1 ≤ ε ⟨0, rfl⟩ :=
  Verifier.not_rbr_zero h ⟨0, rfl⟩ rfl later_P_to_V (stmtOneBad, oracleOf oneBadLimb)
    (fun _ h ↦ stmtOneBad_not_table h) (fun j ↦ Fin.elim0 j) fun c ↦
      ⟨fullOf c (firstOnlyMsg c), fullOf_take c _, (),
        Verifier.GuardedForm.probEvent_pos_of_check (guardedWith twoLimbs _ _) init impl _ _ _
          (by
            show accepts twoLimbs
              (fun s r cs ↦ decide (cs.head? = (expectedValues twoLimbs s.1 r).head?))
              stmtOneBad c (firstOnlyMsg c) = true
            simp only [accepts, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨rfl, by simp [firstOnlyMsg, expectedValues]⟩)
          (firstOnly_pub c)⟩

/-! ### An unsent line's claim dropped -/

/-- The pool with an unsent line's claim at zero, as if that claim were dropped, on
`noneSent`. -/
def poolDropped (s : K × TableOut noneSent) (r : E) (cs : List E)
    (h : cs.length = sentCount noneSent (noneSent.publicLines s.1)) : K × PubOut noneSent :=
  (s.1, ⟨s.2.columns ++ claimsWith noneSent r (fun _ ↦ 0) (noneSent.publicLines s.1) cs h⟩)

/-- The verifier with the check and the dropped claim. -/
abbrev dropped : FrontVerifier []ₒ (K × TableOut noneSent) (K × PubOut noneSent) pubSpec :=
  verifierWith noneSent (check noneSent) poolDropped

/-- The statement `1` with the received claims true of `goodLimbs`, whose column 2 is `[0, 0]`
against the line's cells `(1, 0)`. -/
def stmtDropped : K × TableOut noneSent :=
  (1, ⟨receivedTrue noneSent (by decide) (by decide) (by decide) (by decide) goodLimbs⟩)

theorem stmtDropped_not_table :
    ((stmtDropped, oracleOf goodLimbs), ()) ∉ Seam.table noneSent :=
  fun h ↦ absurd (h.2.1 ⟨⟨0, 2⟩, 1, 0, false, by decide⟩ (by simp [stmtDropped])).1 (by decide)

theorem dropped_pub (c : E) :
    ((verdict noneSent poolDropped stmtDropped c [], oracleOf goodLimbs), ()) ∈
      Seam.pub noneSent := by
  have c0 : (noneSent.column goodLimbs ⟨0, 2⟩).values.get ⟨0, by decide⟩ = 0 := by decide
  have c1 : (noneSent.column goodLimbs ⟨0, 2⟩).values.get ⟨1, by decide⟩ = 0 := by decide
  refine ⟨fun cl hcl ↦ ?_, aux_of_none rfl _⟩
  rw [verdict, dite_eq_left (show ([] : List E).length =
    sentCount noneSent (noneSent.publicLines stmtDropped.1) from rfl)] at hcl
  simp only [poolDropped, Vector.toList_append, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · exact receivedTrue_holds noneSent (by decide) (by decide) (by decide) (by decide) goodLimbs
      cl hcl
  · simp only [claimsWith, Vector.toList_ofFn, List.mem_ofFn] at hcl
    obtain ⟨i, rfl⟩ := hcl
    fin_cases i
    show CMlPolynomialEval.eval₂Mle (noneSent.column goodLimbs ⟨0, 2⟩).values (algebraMap K E)
      (linePoint (by decide) c) = 0
    rw [eval₂Mle_linePoint, c0, c1]
    simp

/-- Dropping an unsent line's claim leaves no round-by-round knowledge error below one: the
empty message passes the check and the pool says nothing of the line. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    {WitMid : Fin 3 → Type}
    (Ext : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
      ((K × TableOut noneSent) × ∀ i, TheOracle noneSent i) Unit Unit pubSpec WitMid)
    (kSF : (dropped.toOracleVerifier (TheOracle noneSent)).toVerifier.KnowledgeStateFunction
      init impl (Seam.table noneSent) (Seam.pub noneSent) Ext)
    (ε : pubSpec.ChallengeIdx → ℝ≥0)
    (h : (dropped.toOracleVerifier
      (TheOracle noneSent)).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
        (Seam.table noneSent) (Seam.pub noneSent) WitMid Ext kSF ε) :
    1 ≤ ε ⟨0, rfl⟩ :=
  Verifier.not_rbr_zero h ⟨0, rfl⟩ rfl later_P_to_V (stmtDropped, oracleOf goodLimbs)
    (fun _ h ↦ stmtDropped_not_table h) (fun j ↦ Fin.elim0 j) fun c ↦
      ⟨fullOf c [], fullOf_take c _, (),
        Verifier.GuardedForm.probEvent_pos_of_check (guardedWith noneSent _ _) init impl _ _ _
          (by
            show accepts noneSent (check noneSent) stmtDropped c [] = true
            rfl)
          (dropped_pub c)⟩

/-! ### A check the honest prover fails -/

/-- The statement `1` with the received claims true of the honest stack: in the table seam. -/
def stmtHonest : K × TableOut toy :=
  (1, ⟨receivedTrue toy (by decide) (by decide) (by decide) (by decide) honest⟩)

theorem stmtHonest_table : ((stmtHonest, oracleOf honest), ()) ∈ Seam.table toy :=
  ⟨receivedTrue_holds toy (by decide) (by decide) (by decide) (by decide) honest, by decide,
    aux_of_none rfl _⟩

/-- The check with the two cells swapped: `(1 + r)·cell1 + r·cell0`. -/
def swappedValues (input : K) (r : E) : List E :=
  ((toy.publicLines input).toList.filter (·.sent)).map fun l ↦
    (1 + r) * ofK l.cell1 + r * ofK l.cell0

/-- The verifier with the swapped check. -/
abbrev swapped : FrontVerifier []ₒ (K × TableOut toy) (K × PubOut toy) pubSpec :=
  verifierWith toy (fun s r cs ↦ decide (cs = swappedValues s.1 r)) (pooledFrom toy)

/-- The swapped check rejects the honest prover at the challenge `y`: the line's value is
`1 + y` and the swapped one `y`. So the phase is not perfectly complete. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ¬ (OracleReduction.mk (PublicInput.prover toy)
      (swapped.toOracleVerifier (TheOracle toy))).perfectCompleteness init impl
        (Seam.table toy) (Seam.pub toy) :=
  let ⟨pr, hpr, h0, h1, _⟩ := exists_mem_support_prover_run toy stmtHonest (oracleOf honest) y
  Reduction.not_perfectCompleteness_of_reject' _ (guardedWith toy _ _) init impl _ _
    stmtHonest_table ⟨pr, hpr, Or.inl (by
      show (decide ((pr.1 1 : List E).length = sentCount toy (toy.publicLines stmtHonest.1)) &&
        decide (@Eq (List E) (pr.1 1) (swappedValues stmtHonest.1 (pr.1 0)))) = false
      rw [h0, h1, show decide (expectedValues toy stmtHonest.1 y = swappedValues stmtHonest.1 y) =
        false from decide_eq_false fun h ↦ by
          simp [expectedValues, swappedValues, lineValue, stmtHonest] at h, Bool.and_false])⟩

/-- The verifier with an extra check: the message has two values. -/
abbrev extraCheck : FrontVerifier []ₒ (K × TableOut toy) (K × PubOut toy) pubSpec :=
  verifierWith toy (fun s r cs ↦ check toy s r cs && decide (cs.length = 2)) (pooledFrom toy)

/-- The extra check rejects the honest prover, whose message has one value. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ¬ (OracleReduction.mk (PublicInput.prover toy)
      (extraCheck.toOracleVerifier (TheOracle toy))).perfectCompleteness init impl
        (Seam.table toy) (Seam.pub toy) :=
  let ⟨pr, hpr, h0, h1, _⟩ := exists_mem_support_prover_run toy stmtHonest (oracleOf honest) y
  Reduction.not_perfectCompleteness_of_reject' _ (guardedWith toy _ _) init impl _ _
    stmtHonest_table ⟨pr, hpr, Or.inl (by
      show (decide ((pr.1 1 : List E).length = sentCount toy (toy.publicLines stmtHonest.1)) &&
        (check toy stmtHonest (pr.1 0 : E) (pr.1 1 : List E) &&
          decide ((pr.1 1 : List E).length = 2))) = false
      rw [h0, h1, show decide ((expectedValues toy stmtHonest.1 y).length = 2) = false from rfl,
        Bool.and_false, Bool.and_false])⟩

end Refutations

end LeanerVMTests.Protocol.PublicInput
