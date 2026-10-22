import LeanerVM.Protocol.Whir.Open

/-!
# The opening of WHIR: an honest run on a toy

The opening on a stack of `4` variables, two levels at rate `2⁻¹`: the first folds two lanes (two
fold rounds, `lm1 = 1`) with two queries and leaves `2` variables, the last folds one lane with one
query and leaves a plaintext table of `1` variable (`nf = 0`). A level with two folds runs the
chained fold rounds through the verifier, and a level with two queries makes the powers of the
batching challenge visible: with one fold or one query neither shows. The verifier of `whirOpen`
is read off the completeness half
(`(whirOpenComplete ..).guarded`): its check on the statement, the oracle and a full transcript.
The transcript of the honest prover is built here, step by step, from the honest values the
components compute (`firstPoly`, `wordOf`, `foldTable`, `foldWeight`, `gluedWeight`), with fixed
challenges. A plain file, so `#guard` evaluates the compiled definitions.

* **The honest run is accepted**, by the whole opening and by the last level alone.
* **Each mutation of the prover's messages is rejected**, one at a time: the opening claim's
  polynomial, the second fold round's polynomial, a residual polynomial at either level, the
  out-of-domain value, the out-of-domain and query polynomials swapped, a query polynomial at
  either level, the commitment of another table, the plaintext table; the two fold challenges of
  the first level swapped in the transcript; the query batch's polynomial at the other power
  scheme (`λ^(1+q)` for `λ^q`); the next level's prover working from the out-of-domain and query
  claims glued at the other powers (`λ²` and `λ`). Each makes a check fail that the honest run
  passes, so none of the checks is vacuous.
* **The nonce is not checked here**: a transcript with a nonzero nonce at either level is still
  accepted (the check is the compiled verifier's, against the hash chain).
* **A wrong statement or oracle is rejected**: another value of the claim, the word of another
  stack.
* **The relayout is a rotation.** The stack's weight is evaluated at the lanes-first point
  rotated, and not at the unrotated point; the weighted claim is the same on both layouts.

The transcripts are built with `appendTr`, not ArkLib's `FullTranscript.append`: that one is a
recursion on the length of the second transcript, and nested to the right, as `seqSpec` nests,
evaluating one entry costs more than the test can afford.
-/

namespace LeanerVMTests.Protocol.WhirOpenToy

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Whir LeanerVM.Protocol.StepSchedule
  CompPoly CMlPolynomialEval
  OracleComp OracleSpec ProtocolSpec

/-! ## Transcripts of a list of steps -/

/-- The values of a step's rounds. -/
def stepVal : Step → Type
  | .msg M => M
  | .oracle M _ => M
  | .chal C _ => C
  | .chals C _ k => Fin k → C
  | .rds C _ d m => Fin m → Vector C (d + 1) × C
  | .skip => Unit

/-- The values of a list of steps' rounds. -/
def ValList : List Step → Type
  | [] => Unit
  | a :: l => stepVal a × ValList l

/-- Two transcripts appended, by case analysis on the index. ArkLib's `FullTranscript.append` is
a recursion on the length of the second transcript, which nested to the right (as `seqSpec` does)
costs more than evaluation can afford; the values are the same. -/
def appendTr {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n}
    (T₁ : p₁.FullTranscript) (T₂ : p₂.FullTranscript) :
    (p₁ ++ₚ p₂).FullTranscript := fun i ↦
  Fin.addCases (motive := fun i ↦ (p₁ ++ₚ p₂).«Type» i)
    (fun j ↦ cast (by simp) (T₁ j))
    (fun j ↦ cast (by simp) (T₂ j)) i

/-- The transcript of `k` challenges. -/
def drawsTr (C : Type) : (k : ℕ) → (Fin k → C) → (draws C k).FullTranscript
  | 0, _ => fun i ↦ Fin.elim0 i
  | k + 1, f => appendTr (drawsTr C k fun i ↦ f i.castSucc)
      (fun | ⟨0, _⟩ => f (Fin.last k))

/-- The transcript of `m` sumcheck rounds. -/
def roundsTr (C : Type) (d : ℕ) : (m : ℕ) → (Fin m → Vector C (d + 1) × C) →
    (roundsSpec C d m).FullTranscript
  | 0, _ => fun i ↦ Fin.elim0 i
  | m + 1, f => appendTr
      (appendTr (fun | ⟨0, _⟩ => (f 0).1) (fun | ⟨0, _⟩ => (f 0).2))
      (roundsTr C d m fun i ↦ f i.succ)

/-- The transcript of a step. -/
def stepTr : (a : Step) → stepVal a → a.spec.FullTranscript
  | .msg _, v => fun | ⟨0, _⟩ => v
  | .oracle _ _, v => fun | ⟨0, _⟩ => v
  | .chal _ _, v => fun | ⟨0, _⟩ => v
  | .chals C _ k, v => drawsTr C k v
  | .rds C _ d m, v => roundsTr C d m v
  | .skip, _ => fun i ↦ Fin.elim0 i

/-- The transcript of a list of steps. -/
def seqTr : (l : List Step) → ValList l → (seqSpec l).FullTranscript
  | [], _ => fun i ↦ Fin.elim0 i
  | a :: l, v => appendTr (stepTr a v.1) (seqTr l v.2)

/-! ## The toy -/

/-- An element of `E`. -/
def ee (a b : ℕ) : E := algebraMap K E (K.ofBits a) + y * algebraMap K E (K.ofBits b)

/-- The first level: two fold rounds, rate `2⁻¹`, two queries. -/
def sh0 : Shape := ⟨1, 1, 2⟩

/-- The last level: one lane, rate `2⁻¹`, one query. -/
def sh1 : Shape := ⟨0, 1, 1⟩

/-- The chain: a level, then the last level, leaving a plaintext table of one variable. -/
def ladder : Ladder sh0 (Kap sh1 (0 + 1)) := .cons sh0 (.last sh1 0)

/-- The variables the first level leaves after its fold. -/
abbrev κ0 : ℕ := Kap sh1 (0 + 1)

/-- The stack: `κ0 + 2 = 4` variables, lanes on top. -/
def stackQ : Tab (κ0 + sh0.ℓ) :=
  Vector.ofFn fun i ↦ algebraMap K E (K.ofBits (0x9e3779b97f4a7c15 * (i.val + 1) + 5))

/-- The opening phase's weight on the stack. -/
def stackW : Weight E (κ0 + sh0.ℓ) :=
  let t : Tab (κ0 + sh0.ℓ) :=
    Vector.ofFn fun i ↦ algebraMap K E (K.ofBits (0x243f6a8885a308d3 * (i.val + 3) + 11))
  ⟨t, evalMle t, fun _ ↦ rfl⟩

/-- The opening claim's value. -/
def stackC : E := stackW.pair (RingHom.id E) stackQ

/-- The statement the opening reads. -/
def stmt0 : Weight E (κ0 + sh0.ℓ) × E := (stackW, stackC)

/-- The one oracle: the honest word of the stack, lanes first. -/
def oracle0 : ∀ i, OneW sh0 κ0 i := fun _ ↦ wordOf sh0.ℓ κ0 sh0.R sh0.t (relayout stackQ)

/-! ### The honest prover's values -/

/-- The first level's table and weight, lanes first. -/
def f0 : Tab (sh0.ℓ + κ0) := relayout stackQ
def W0 : Weight E (sh0.ℓ + κ0) := relayoutWeight stackW

/-- The first level's fold point, the folded table and the residual weight. -/
def r0 : Vector E sh0.ℓ := #v[ee 0x1d 0x3, ee 0x2b 0x6]
def g0 : Tab κ0 := foldTable f0 r0
def V0 : Weight E κ0 := foldWeight W0 r0

/-- The out-of-domain point, the positions and the batching challenge of the first level. -/
def z0 : Vector E κ0 := #v[ee 0x77 0x1, ee 0x5 0x9]
def pos0 : Fin sh0.t → Fin (2 ^ (κ0 + sh0.R)) := fun q ↦
  if q.val = 0 then ⟨5, by decide⟩ else ⟨3, by decide⟩
def lam0 : E := ee 0x21 0x7

/-- The first level's folded symbols and its glued claim. -/
def cq0 : Fin sh0.t → E := fun q ↦ foldRow r0 ((oracle0 0).row (pos0 q))
def W1 : Weight E κ0 := gluedWeight V0 z0 pos0 lam0
def c1 : E := powerBatch ![V0.pair (RingHom.id E) g0, evalMle g0 z0, powerBatch cq0 lam0] lam0
def m1 : SumcheckRound.Message E 2 :=
  batchMessage ![firstPoly V0 g0, firstPoly (eqWeight z0) g0,
    firstPoly (queryWeight κ0 sh0.R pos0 lam0) g0] lam0

/-- The last level: its fold point, plaintext table, positions and batching challenge. -/
def r1 : Vector E sh1.ℓ := #v[ee 0x4b 0x2]
def ff : Tab (0 + 1) := foldTable g0 r1
def V1 : Weight E (0 + 1) := foldWeight W1 r1
def pos1 : Fin sh1.t → Fin (2 ^ ((0 + 1) + sh1.R)) := fun _ ↦ ⟨2, by decide⟩
def lam1 : E := ee 0x13 0x5
def word1 : Word sh1.ℓ ((0 + 1) + sh1.R) sh1.t := wordOf sh1.ℓ (0 + 1) sh1.R sh1.t g0
def cq1 : Fin sh1.t → E := fun q ↦ foldRow r1 (word1.row (pos1 q))
def tail0 : E := ee 0x6f 0x4

/-- The last level's start: its claim and first-round polynomial. -/
def stmtF : SumcheckRound.MidStmt (Weight E (sh1.ℓ + (0 + 1))) E 0 2 := ((W1, (#v[], c1)), m1)

def oF : ∀ i, OneW sh1 (0 + 1) i := fun _ ↦ word1

/-- The messages of the prover that the mutations change; the challenges are fixed. -/
structure Msgs where
  /-- The first-round polynomial of the opening claim. -/
  first : SumcheckRound.Message E 2
  /-- The first level's fold challenges, as they stand in the transcript. -/
  ch0 : Vector E sh0.ℓ
  /-- The polynomial of the first level's second fold round. -/
  fold1 : SumcheckRound.Message E 2
  /-- The first level's residual polynomial. -/
  p1a : SumcheckRound.Message E 2
  /-- The first level's grinding nonce. -/
  nonce0 : E
  /-- The last level's grinding nonce. -/
  nonce1 : E
  /-- The commitment to the first level's folded table. -/
  word : Word sh1.ℓ ((0 + 1) + sh1.R) sh1.t
  /-- The out-of-domain value. -/
  cood : E
  /-- The out-of-domain claim's polynomial. -/
  p2 : SumcheckRound.Message E 2
  /-- The first level's query batch polynomial. -/
  p3a : SumcheckRound.Message E 2
  /-- The last level's residual polynomial. -/
  p1b : SumcheckRound.Message E 2
  /-- The plaintext table. -/
  ff : Tab (0 + 1)
  /-- The last level's query batch polynomial. -/
  p3b : SumcheckRound.Message E 2

/-- The honest prover's messages. -/
def honest : Msgs where
  first := firstPoly W0 f0
  ch0 := r0
  fold1 := ProductSum.roundPoly W0.onCube f0 1 #v[r0[0]]
  nonce0 := 0
  nonce1 := 0
  p1a := firstPoly V0 g0
  word := word1
  cood := evalMle g0 z0
  p2 := firstPoly (eqWeight z0) g0
  p3a := firstPoly (queryWeight κ0 sh0.R pos0 lam0) g0
  p1b := firstPoly V1 ff
  ff := ff
  p3b := firstPoly (queryWeight (0 + 1) sh1.R pos1 lam1) ff

/-- The transcript values, in the order of the steps after the relayout and the first
polynomial: the opening claim's polynomial, the first level's rounds, the last level's. -/
def Msgs.vals (m : Msgs) :
    ValList (.skip :: .msg (SumcheckRound.Message E 2) :: ladder.steps) :=
  ⟨(), m.first,
    m.ch0[0]!, (fun _ ↦ (m.fold1, m.ch0[1]!)), m.p1a, m.word, (fun i ↦ z0[i]), (m.cood : E), m.p2,
    m.nonce0, pos0, lam0, (), m.p3a, (),
    r1[0]!, (fun i ↦ Fin.elim0 i), m.p1b, m.ff, m.nonce1, pos1, lam1, (), m.p3b, (), tail0,
    (fun i ↦ Fin.elim0 i), ()⟩

/-- The verifier of the opening, read off its completeness half. -/
abbrev verifier := (whirOpenComplete sh0 κ0 ladder).guarded

/-- Whether the verifier accepts the messages, on the statement and the oracle. -/
def accepts (m : Msgs) (st : Weight E (κ0 + sh0.ℓ) × E := stmt0)
    (o : ∀ i, OneW sh0 κ0 i := oracle0) : Bool :=
  verifier.check (st, o) (seqTr _ m.vals)

/-- A polynomial with its linear coefficient changed. -/
def bump (q : SumcheckRound.Message E 2) : SumcheckRound.Message E 2 := q.set 1 (q[1] + 1)

/-- A polynomial times a scalar: the polynomial of a weight scaled by it. -/
def scale (c : E) (q : SumcheckRound.Message E 2) : SumcheckRound.Message E 2 := q.map (· * c)

/-- An out-of-domain point other than the drawn one: a prover that ignores the sample. -/
def zAlt : Vector E κ0 := #v[ee 0x31 0x3, ee 0x44 0x9]

/-- The out-of-domain and query weights glued in the other order: the query weight at `λ` and
the out-of-domain weight at `λ²`. -/
def W1alt : Weight E κ0 := Weight.batch ![V0, queryWeight κ0 sh0.R pos0 lam0, eqWeight z0] lam0

/-! ## The honest run -/

#guard accepts honest = true

/-! ## The order of the messages is the schedule's

A transcript is typed by the schedule, so a nonce sent after the positions, or a dropped
out-of-domain sample, is not a transcript that can be written: it is a different schedule. What can
be checked is the schedule itself, in the deployed verifier's order. -/

/-- A step's kind and its number of rounds: a message `0`, a queried message `1`, a challenge `2`, a
run of challenges `3`, a run of sumcheck rounds `4`, a step with no round `5`. -/
def tag : Step → ℕ × ℕ
  | .msg _ => (0, 1)
  | .oracle _ _ => (1, 1)
  | .chal _ _ => (2, 1)
  | .chals _ _ k => (3, k)
  | .rds _ _ _ m => (4, m)
  | .skip => (5, 0)

-- the first level: the first fold challenge, the other fold round, the residual polynomial, the
-- commitment, the out-of-domain point (`κ0 = 2` challenges), its answer and polynomial, the nonce,
-- the positions, the batching challenge, the reading (no round), the query batch's polynomial, the
-- glue (no round); then the last level: the fold challenge, no further fold round, the residual
-- polynomial, the plaintext table, the nonce, the positions, the batching challenge, the reading
-- (no round), the query batch's polynomial, the glue (no round), the tail's first challenge and
-- its remaining rounds. The nonce precedes the positions at both levels.
#guard ladder.steps.map tag =
  [(2, 1), (4, 1), (0, 1), (1, 1), (3, 2), (0, 1), (0, 1), (0, 1), (2, 1), (2, 1), (5, 0), (0, 1),
    (5, 0),
   (2, 1), (4, 0), (0, 1), (0, 1), (0, 1), (2, 1), (2, 1), (5, 0), (0, 1), (5, 0), (2, 1), (4, 0)]

/-! ## Mutations of the prover's messages: each is rejected -/

-- the opening claim's polynomial
#guard accepts { honest with first := bump honest.first } = false
-- the second fold round's polynomial of the first level
#guard accepts { honest with fold1 := bump honest.fold1 } = false
-- the two fold challenges of the first level swapped in the transcript
#guard accepts { honest with ch0 := #v[r0[1], r0[0]] } = false
-- the residual polynomial at either level
#guard accepts { honest with p1a := bump honest.p1a } = false
#guard accepts { honest with p1b := bump honest.p1b } = false
-- the out-of-domain value, with the polynomial of the honest claim
#guard accepts { honest with cood := honest.cood + 1 } = false
-- the intro polynomials swapped: the out-of-domain claim's and the query batch's
#guard accepts { honest with p2 := honest.p3a, p3a := honest.p2 } = false
-- the query batch's polynomial, at either level
#guard accepts { honest with p3a := bump honest.p3a } = false
#guard accepts { honest with p3b := bump honest.p3b } = false
-- the query batch's polynomial at the other power scheme: `λ^(1+q)` for `λ^q`
#guard accepts { honest with p3a := scale lam0 honest.p3a } = false
-- a prover that ignores the out-of-domain sample: it answers and proves at its own point
#guard accepts
  { honest with
    cood := evalMle g0 zAlt
    p2 := firstPoly (eqWeight zAlt) g0
    p1b := firstPoly (foldWeight (gluedWeight V0 zAlt pos0 lam0) r1) ff } = false
-- the next level's prover works from the out-of-domain and query claims glued at other powers
#guard accepts { honest with p1b := firstPoly (foldWeight W1alt r1) ff } = false
-- the commitment of another table: the last level's queries read rows that are not the fold's
#guard accepts { honest with word := wordOf sh1.ℓ (0 + 1) sh1.R sh1.t (g0.set 0 (g0[0] + 1)) } =
  false
-- the plaintext table with one entry changed: only the terminal check sees it
#guard accepts { honest with ff := ff.set 0 (ff[0] + 1) } = false

/-! ## The nonce is not checked here -/

-- a nonzero nonce at either level is accepted: its check is the compiled verifier's
#guard accepts { honest with nonce0 := ee 0x31 0x4 } = true
#guard accepts { honest with nonce1 := ee 0x2 0x8 } = true

/-! ## Mutations of the statement and the oracle -/

-- another value of the claim
#guard accepts honest (stackW, stackC + 1) = false
-- the word of another stack
#guard accepts honest stmt0 (fun _ ↦ wordOf sh0.ℓ κ0 sh0.R sh0.t
  (relayout (stackQ.set 0 (stackQ[0] + 1)))) = false

/-! ## The relayout -/

/-- A point of the first level's table, lanes first. -/
def pt : Vector E (sh0.ℓ + κ0) := #v[ee 3 1, ee 5 2, ee 7 3, ee 9 4]

-- the weight on the relayout is the stack's weight at the rotated point
#guard (relayoutWeight stackW).mle pt = stackW.mle (highVec pt ++ lowVec pt)
-- and not at the unrotated one
#guard (relayoutWeight stackW).mle pt ≠ stackW.mle (pt.cast (by omega))
-- the weighted claim is the same on both layouts
#guard (relayoutWeight stackW).pair (RingHom.id E) (relayout stackQ) = stackC

end LeanerVMTests.Protocol.WhirOpenToy
