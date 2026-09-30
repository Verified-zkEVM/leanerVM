import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput

/-!
Probe P3a (code-spine): each seam on the toy instance, an inhabitant and near misses; the
zerocheck escape; the commit phase's state function and extractor; the type of the composed
extractor's output when a phase has rounds.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp

namespace Probe

/-! ## Decision procedures for the claims and the seams (the repository has none)

Spelled with `inferInstanceAs` on the unfolded proposition, as the repository's public-input
test does: the instance `by unfold …; infer_instance` elaborates and then exhausts the memory
under `#guard` (observed: exit 137 on the first version of this probe). -/

instance {I : M3Instance} (q : Column I.μ) (c : ColumnClaim I) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable (CMlPolynomialEval.eval₂Mle (I.column q c.col).values
    (algebraMap K E) c.point = c.value))

instance {I : M3Instance} (q : Column I.μ) (c : LinearClaim I) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable ((c.terms.map fun t ↦ t.eval q).sum = c.value))

instance {I : M3Instance} (q : Column I.μ) (c : WeightedClaim I) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable (c.weight.pair q = c.value))

/-- The predicate of the bus seam, on a statement and a stack. -/
def busPred (I : M3Instance) (s : I.Stmt × BusOut I) (q : Column I.μ) : Prop :=
  (∀ c ∈ s.2.linear, c.Holds q) ∧
  (∀ c ∈ s.2.linear, ∀ t ∈ c.terms, t.poly.totalDegree ≤ I.d) ∧
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q

/-- It is the bus seam, by definition. -/
example (I : M3Instance) (s : I.Stmt × BusOut I) (o : ∀ i, TheOracle I i) :
    ((s, o), ()) ∈ Seam.bus I ↔ busPred I s (o 0) := Iff.rfl

instance (I : M3Instance) (s : I.Stmt × BusOut I) (q : Column I.μ) :
    Decidable (busPred I s q) :=
  inferInstanceAs (Decidable ((∀ c ∈ s.2.linear, c.Holds q) ∧
    (∀ c ∈ s.2.linear, ∀ t ∈ c.terms, t.poly.totalDegree ≤ I.d) ∧
    (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q))

def tablePred (I : M3Instance) (s : I.Stmt × TableOut I) (q : Column I.μ) : Prop :=
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q

example (I : M3Instance) (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i) :
    ((s, o), ()) ∈ Seam.table I ↔ tablePred I s (o 0) := Iff.rfl

instance (I : M3Instance) (s : I.Stmt × TableOut I) (q : Column I.μ) :
    Decidable (tablePred I s q) :=
  inferInstanceAs (Decidable ((∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧
    I.aux q))

def pubPred (I : M3Instance) (s : I.Stmt × PubOut I) (q : Column I.μ) : Prop :=
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.aux q

example (I : M3Instance) (s : I.Stmt × PubOut I) (o : ∀ i, TheOracle I i) :
    ((s, o), ()) ∈ Seam.pub I ↔ pubPred I s (o 0) := Iff.rfl

instance (I : M3Instance) (s : I.Stmt × PubOut I) (q : Column I.μ) :
    Decidable (pubPred I s q) :=
  inferInstanceAs (Decidable ((∀ c ∈ s.2.columns, c.Holds q) ∧ I.aux q))

def flockPred (I : M3Instance) (s : I.Stmt × FlockOut I) (q : Column I.μ) : Prop :=
  (∀ c ∈ s.2.columns, c.Holds q) ∧ ∀ c ∈ s.2.weighted, c.Holds q

example (I : M3Instance) (s : I.Stmt × FlockOut I) (o : ∀ i, TheOracle I i) :
    ((s, o), ()) ∈ Seam.flock I ↔ flockPred I s (o 0) := Iff.rfl

instance (I : M3Instance) (s : I.Stmt × FlockOut I) (q : Column I.μ) :
    Decidable (flockPred I s q) :=
  inferInstanceAs (Decidable ((∀ c ∈ s.2.columns, c.Holds q) ∧ ∀ c ∈ s.2.weighted, c.Holds q))

/-! ## The claims of the probe -/

def eZero : E := 0
def eOne : E := 1
/-- A point of `E` outside `{0, 1}`: the image of `2 : K` (the polynomial `x`). -/
def eTwo : E := ofK (K.ofBits 2)

/-- Column 0 of the honest stack is `[1, 1]`: its extension is `1` everywhere. -/
def col0One : ColumnClaim toy := ⟨⟨0, 0⟩, #v[eTwo], eOne⟩
def col0Zero : ColumnClaim toy := ⟨⟨0, 0⟩, #v[eTwo], eZero⟩

/-- The zerocheck claim of the toy's constraint at the point `(0)`: value `0`. -/
def zeroAt0 : LinearClaim toy :=
  ⟨[⟨eOne, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[eZero]⟩], eZero⟩
/-- The same at the point `(1)`. -/
def zeroAt1 : LinearClaim toy :=
  ⟨[⟨eOne, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[eOne]⟩], eZero⟩
/-- The same with the wrong value. -/
def zeroWrong : LinearClaim toy :=
  ⟨[⟨eOne, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[eZero]⟩], eOne⟩
/-- A cubic term, whose claim is true of the honest stack (column 2 is `[1, 0]`, so `X₂³` is
`[1, 0]` and its extension at `(0)` is `1`). -/
def cubicTrue : LinearClaim toy :=
  ⟨[⟨eOne, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 * CMvPolynomial.X 2, #v[eZero]⟩], eOne⟩

/-- The stack of the repository's test `badConstraint`: column 2 is `[2, 0]`, not Boolean. -/
def badConstraint : Column 3 := ⟨#v[1, 1, 1, 1, K.ofBits 2, 0, 0, 0]⟩

/-! ## The bus seam -/

-- An inhabitant: the zerocheck claim and a column claim, on the honest stack at statement 1.
#guard busPred toy ((1 : K), ⟨[zeroAt0, zeroAt1], [col0One]⟩) honest
-- Near misses, one per conjunct.
#guard ¬ busPred toy ((1 : K), ⟨[zeroWrong], [col0One]⟩) honest          -- a false linear claim
#guard ¬ busPred toy ((1 : K), ⟨[cubicTrue], [col0One]⟩) honest          -- a true cubic claim
#guard cubicTrue.Holds honest                                            -- (it is true)
#guard ¬ busPred toy ((1 : K), ⟨[zeroAt0], [col0Zero]⟩) honest           -- a false column claim
#guard ¬ busPred toy ((0 : K), ⟨[zeroAt0], [col0One]⟩) honest            -- the wrong statement

-- The zerocheck escape: on `badConstraint` the constraint is violated on the cube (row 0), so
-- the claim at the point `(0)` is false, and the claim at the point `(1)` is true. The bus seam
-- holds of a stack outside `M3Holds`; the bus phase's error is what pays for it.
#guard ¬ toy.ConstraintsVanish badConstraint
#guard ¬ zeroAt0.Holds badConstraint
#guard zeroAt1.Holds badConstraint
#guard busPred toy ((K.ofBits 2 : K), ⟨[zeroAt1], [col0One]⟩) badConstraint
#guard ¬ M3Holds toy (K.ofBits 2 : K) badConstraint

-- A bus statement with no claim holds of every stack whose public line holds: the seam does
-- not say which claims are emitted.
#guard busPred toy ((K.ofBits 2 : K), ⟨[], []⟩) badConstraint

/-! ## The table and public-input seams -/

#guard tablePred toy ((1 : K), ⟨[col0One]⟩) honest
#guard ¬ tablePred toy ((1 : K), ⟨[col0Zero]⟩) honest
#guard ¬ tablePred toy ((0 : K), ⟨[col0One]⟩) honest
#guard pubPred toy ((1 : K), ⟨[col0One]⟩) honest
#guard ¬ pubPred toy ((1 : K), ⟨[col0Zero]⟩) honest
-- The public seam no longer sees the statement: the wrong statement is inside it.
#guard pubPred toy ((0 : K), ⟨[col0One]⟩) honest

/-! ## The Flock seam -/

/-- The weight that selects cell 0 of the stack. -/
def cell0Weight : Weight 3 where
  onCube := Vector.ofFn fun i ↦ if i.val = 0 then 1 else 0
  mle := fun r ↦ CMlPolynomialEval.evalMle (Vector.ofFn fun i ↦ if i.val = 0 then 1 else 0) r
  mle_eq := fun _ ↦ rfl

def w0One : WeightedClaim toy := ⟨cell0Weight, eOne⟩
def w0Zero : WeightedClaim toy := ⟨cell0Weight, eZero⟩

#guard flockPred toy ((1 : K), ⟨[col0One], [w0One]⟩) honest
#guard ¬ flockPred toy ((1 : K), ⟨[col0One], [w0Zero]⟩) honest
#guard ¬ flockPred toy ((1 : K), ⟨[col0Zero], [w0One]⟩) honest

/-! ## The last seam has no near miss: it is the whole set -/

example : Seam.done toy = Set.univ := Set.eq_univ_of_forall fun _ ↦ trivial

#guard ¬ busPred toy ((1 : K), ⟨[zeroAt0, zeroAt1], [col0One]⟩) honest
#guard busPred toy ((K.ofBits 2 : K), ⟨[zeroAt1], [col0One]⟩) honest
end Probe
