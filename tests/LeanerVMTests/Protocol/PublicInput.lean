import LeanerVM.Protocol.PublicInput
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose

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
* **The phase** has two rounds, a challenge then a message, and error `1/|E|`; with four
  pass-through phases it inhabits `Phases.Complete` against the spine's seams.

A plain file, so `#guard` evaluates the compiled definitions. Values of `E` written with
numerals are named as definitions before a guard uses them.
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
  ((I.publicLines input).filter (·.sent)).map fun l ↦
    CMlPolynomialEval.eval₂Mle (I.column q l.col).values (algebraMap K E) (linePoint l.pos r)

/-! ## The point -/

/-- The table `[1, 2, 3, 4]` on two variables. -/
def table : CMlPolynomialEval K 2 := #v[1, 2, 3, 4]

/-- The point `(y, 0)`. -/
def onLine : List E := [y, 0]

/-- The point `(y, 1)`: second coordinate `1`. -/
def offLine : Vector E 2 := #v[y, ofK 1]

#guard (linePoint (n := 2) (by decide) y).toList = onLine
-- The extension at `(y, 0)` is the line through cells 0 and 1.
#guard CMlPolynomialEval.eval₂Mle table (algebraMap K E) (linePoint (n := 2) (by decide) y) =
  (1 - y) * ofK 1 + y * ofK 2
-- With the second coordinate `1` it is the line through cells 2 and 3 instead.
#guard CMlPolynomialEval.eval₂Mle table (algebraMap K E) offLine = (1 - y) * ofK 3 + y * ofK 4
#guard CMlPolynomialEval.eval₂Mle table (algebraMap K E) offLine ≠ (1 - y) * ofK 1 + y * ofK 2

/-! ## The check -/

/-- A second sampled challenge, `y² + 1`. -/
def r₂ : E := y * y + 1

/-- The toy's statement `1` with an empty pool. -/
def stmt1 : K × TableOut toy := (1, ⟨[]⟩)

/-- The toy's statement `0` with an empty pool. -/
def stmt0 : K × TableOut toy := (0, ⟨[]⟩)

/-- The value of the toy's line at statement `1` and challenge `y`: `(1 + y)·1 + y·0`. -/
def good : List E := [1 + y]

/-- A wrong value. -/
def wrong : List E := [y]

/-- One value too many. -/
def extra : List E := [1 + y, 0]

-- The verifier expects one value, the line's.
#guard expectedValues toy (1 : K) y = good
-- The check accepts it, and rejects a wrong value, a missing value and an extra value.
#guard check toy stmt1 y good
#guard ¬ check toy stmt1 y wrong
#guard ¬ check toy stmt1 y []
#guard ¬ check toy stmt1 y extra

-- On the honest stack the true evaluation is the line's value, at every sampled challenge.
#guard trueValues toy honest (1 : K) y = expectedValues toy (1 : K) y
#guard trueValues toy honest (1 : K) r₂ = expectedValues toy (1 : K) r₂
#guard trueValues toy honest (1 : K) 0 = expectedValues toy (1 : K) 0

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
#guard ∀ c ∈ (pooled toy stmt1 y).2.columns, c.Holds honest
#guard ¬ ∀ c ∈ (pooled toy stmt1 y).2.columns, c.Holds badLine
#guard ∀ c ∈ (pooled toy stmt1 0).2.columns, c.Holds badLine

-- A wrong statement (cell 0 is `0`, the honest stack's is `1`): rejected at a sampled
-- challenge, accepted at the one bad challenge `r = 1`, where `(1 + r)·cell0` vanishes.
#guard ¬ check toy stmt0 y (trueValues toy honest 0 y)
#guard check toy stmt0 1 (trueValues toy honest 0 1)

/-! ## The pool -/

/-- A pool with one received claim. -/
def stmtWithClaim : K × TableOut toy := (1, ⟨[⟨⟨0, 0⟩, #v[y], 1⟩]⟩)

-- The verifier keeps the statement and pools the received claims first, then the line.
#guard (pooled toy stmt1 y).1 = 1
#guard ((pooled toy stmtWithClaim y).2.columns.map fun c ↦ c.col) = [⟨0, 0⟩, ⟨0, 2⟩]
#guard ((pooled toy stmt1 y).2.columns.map fun c ↦ c.value) = good

/-! ## Which values are sent -/

/-- The toy with its line's value not sent. -/
abbrev noneSent : M3Instance :=
  { toy with publicLines := fun v ↦ [⟨⟨0, 2⟩, v, 0, false, by decide⟩] }

/-- Its statement `1` with an empty pool. -/
def stmtNone : K × TableOut noneSent := (1, ⟨[]⟩)

-- The message is empty, a value is rejected, and the line is pooled all the same.
#guard expectedValues noneSent (1 : K) y = []
#guard check noneSent stmtNone y []
#guard ¬ check noneSent stmtNone y good
#guard ((pooled noneSent stmtNone y).2.columns.map fun c ↦ c.value) = good
#guard ¬ ∀ c ∈ (pooled noneSent stmtNone y).2.columns, c.Holds badLine

/-- Three lines shaped like the memory limbs: two with their value sent, and a third with cells
`(0, 0)` and no value sent. -/
abbrev threeLimbs : M3Instance :=
  { toy with publicLines := fun v ↦
      [⟨⟨0, 0⟩, v, 1, true, by decide⟩, ⟨⟨0, 1⟩, 1, 1, true, by decide⟩,
        ⟨⟨0, 2⟩, 0, 0, false, by decide⟩] }

/-- Its statement `1` with an empty pool. -/
def stmtLimbs : K × TableOut threeLimbs := (1, ⟨[]⟩)

/-- A stack whose three columns hold their lines: `[1, 1]`, `[1, 1]`, `[0, 0]`. -/
def goodLimbs : Column 3 := ⟨#v[1, 1, 1, 1, 0, 0, 0, 0]⟩

/-- The top column's cell 0 changed to `1`. -/
def badTopLimb : Column 3 := ⟨#v[1, 1, 1, 1, 1, 0, 0, 0]⟩

/-- The three lines' values at any challenge: `(1 + r) + r`, twice, and `0`. -/
def limbValues : List E := [1, 1, 0]

-- Two values are sent and three claims are pooled, the third with value `0`.
#guard (expectedValues threeLimbs (1 : K) y).length = 2
#guard ((pooled threeLimbs stmtLimbs y).2.columns.map fun c ↦ c.value) = limbValues
#guard ((pooled threeLimbs stmtLimbs y).2.columns.map fun c ↦ c.col) =
  [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩]
#guard ∀ c ∈ (pooled threeLimbs stmtLimbs y).2.columns, c.Holds goodLimbs
-- The wrong top cell passes the check, which sees the two sent values only, and fails the third
-- claim; the pool without the third claim accepts the stack.
#guard check threeLimbs stmtLimbs y (trueValues threeLimbs badTopLimb 1 y)
#guard ¬ ∀ c ∈ (pooled threeLimbs stmtLimbs y).2.columns, c.Holds badTopLimb
#guard ∀ c ∈ ((pooled threeLimbs stmtLimbs y).2.columns.take 2), c.Holds badTopLimb

/-! ## The check per limb and the check on the words differ -/

/-- Two limbs with zero public words, both values sent. -/
abbrev twoLimbs : M3Instance :=
  { toy with publicLines := fun _ ↦
      [⟨⟨0, 0⟩, 0, 0, true, by decide⟩, ⟨⟨0, 1⟩, 0, 0, true, by decide⟩] }

/-- Its statement with an empty pool. -/
def stmtTwo : K × TableOut twoLimbs := (0, ⟨[]⟩)

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

/-! ## The phase against the seams -/

/-- Two rounds: the challenge, then the prover's values. -/
example : (publicInputPhase toy).n = 2 := rfl

example : (publicInputPhase toy).pSpec = pSpec := rfl

example : pSpec.dir 0 = .V_to_P := rfl

example : pSpec.dir 1 = .P_to_V := rfl

/-- The error is `1/|E|` on the one challenge. -/
example (i : (publicInputPhase toy).pSpec.ChallengeIdx) :
    (publicInputPhase toy).err i = 1 / Fintype.card E := rfl

/-- The security half typechecks against the two seams. -/
example : Phase.Security toy (publicInputPhase toy) (Seam.table toy) (Seam.pub toy) :=
  publicInputSecurity toy

/-- The public-input phase among four pass-through phases. -/
noncomputable def phases : Phases toy where
  bus := Phase.passThrough toy fun s ↦ (s, ⟨[], []⟩)
  table := Phase.passThrough toy fun p ↦ (p.1, ⟨[]⟩)
  pub := publicInputPhase toy
  flock := Phase.passThrough toy fun p ↦ (p.1, ⟨[], []⟩)
  opening := Phase.passThrough toy fun _ ↦ ()

/-- Their completeness against the seams, with the real phase's in the middle. -/
noncomputable def complete : phases.Complete where
  bus := Phase.passThroughComplete toy _ fun _ _ h ↦
    ⟨by simp, by simp, by simp, h.2.2.2.1, h.2.2.2.2⟩
  table := Phase.passThroughComplete toy _ fun _ _ h ↦ ⟨by simp, h.2.2.2.1, h.2.2.2.2⟩
  pub := publicInputComplete toy
  flock := Phase.passThroughComplete toy _ fun _ _ _ ↦ ⟨by simp, by simp⟩
  opening := Phase.passThroughComplete toy _ fun _ _ _ ↦ trivial

/-- The master completeness theorem has an instance with a real phase in it. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop phases).perfectCompleteness init impl (M3Rel toy) (Seam.done toy) :=
  piop_perfectCompleteness phases complete init impl

/-- The composed protocol has three rounds: the commit message, the public-input challenge and
the prover's values. -/
example : phases.toDef.n = 3 := rfl

end LeanerVMTests.Protocol.PublicInput
