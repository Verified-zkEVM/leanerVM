/-
  LeanerVM.Protocol.Whir.Level

  One level of WHIR's opening that is followed by another: the fold rounds, the commitment of the
  next word, the out-of-domain claim, the queries of this level's word, and the glue into the next
  level's running claim; definition and perfect completeness.
-/

module

public import LeanerVM.Protocol.Field
public import LeanerVM.Protocol.Whir.Glue
public import LeanerVM.Protocol.ToArkLib.Whir.Schedule
public import LeanerVM.Protocol.ToArkLib.MapWitness
public import LeanerVM.Protocol.ToArkLib.QueryRecord
public import LeanerVM.Protocol.ToArkLib.SendOracleBeside
public import LeanerVM.Protocol.ToArkLib.SendChecked
public import LeanerVM.Protocol.ToArkLib.SampleChallenge

/-!
# A level of WHIR's opening

Category B: Annex B, Protocol 1 (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`,
`fig:protocol`), steps 1 to 3, in the transcript order of the deployed verifier
(`python-verifier/verifier.py`, `verify_whir`).

A level starts with a running claim `<W, f> = c` on its table `f` of `ℓ + κ` variables, the first
round polynomial of its sumcheck already received, and the honest word of `f` as its one oracle.
Its rounds, as components (`levelSteps` lists their schedules):

1. the `ℓ` fold rounds, binding the lane coordinates in round order: the first challenge, then
   each next polynomial and challenge (`foldFirst`, `foldRest`);
2. the residual claim's first-round polynomial, on the table folded at the fold point and the
   weight folded likewise (`sendResidual`; the residual claim is `claim_fold`);
3. the commitment of the folded table's word beside the level's word (`commitNext`);
4. the out-of-domain point, the folded table's value there and the first-round polynomial of that
   claim (`drawPoint`, `sendOod`, `sendOodPoly`);
5. the grinding nonce (`sendNonce`), the sampled positions and the batching challenge
   (`drawPositions`, `drawBatch`);
6. the reading of the level's word at the positions, each row folded at the fold point, which
   drops the level's word (`readOld`, no round);
7. the query batch's first-round polynomial (`sendQueryPoly`);
8. the glue (`glue`, no round): the residual, out-of-domain and query claims summed with the
   scalars `1, λ, λ²` into the next level's running claim, and the prover's table the folded one.

The statement the verifier keeps between its steps is `Bd`; `Bd.F1` to `Bd.F5` are the facts the
honest prover establishes in it, one step at a time (`relOld`, `relBoth`, `relNew` add the
oracles'). Each step is a generic component with its completeness proof; the level is their
composition (`levelDef`, `levelComplete`), followed by the rest of the opening, which is a
parameter, so that the levels chain (`Ladder`, `LeanerVM.Protocol.Whir.Open`).

## Deviations from the Annex, and why

* **The first-round polynomials.** The Annex's step 1 sends one polynomial for the batched claim.
  The deployed verifier receives the residual's, the out-of-domain claim's and the query batch's
  separately, checks each against its own claim value and sums them with the scalars, and the
  proof format the compiled verifier decodes is that one, so the schedule is the deployed one.
* **The nonce** is a message with no check here: the deployed verifier checks it against the
  hash chain (`grind_check`), which the compiled verifier does. The honest prover sends zero.
* **The positions** are one challenge of type `Fin t → Fin (2 ^ (κ + R))`; the deployed verifier
  derives them from squeezes of the transcript, which the compiled verifier reproduces.
* **The round polynomials** are three coefficients here, with the check that its values at `0` and
  `1` sum to the claim. The deployed stream carries two scalars per round polynomial and derives
  the linear coefficient from the running claim, so the two are equivalent and the decoder of the
  compiled verifier owes the derivation.
* **The level-0 word** is `E`-valued here; its `K`-valuedness is an invariant of the input
  relation that the verifier never checks (`isInK_encode_ofK`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Whir

/-- The shape of one level: its fold count less one, the rate exponent of its word and its query
count. The fold count is kept as `lm1 + 1` so that a level folds at least once by construction:
the first round polynomial of a level is checked against its claim only if there is a variable
left to sum over, and `derive_config` never produces a level that does not fold. -/
structure Shape where
  /-- The number of fold rounds, less one. -/
  lm1 : ℕ
  /-- The rate exponent `R` of the level's word, of rate `2 ^ (-R)`. -/
  R : ℕ
  /-- The number of queries at the level. -/
  t : ℕ

/-- The number of fold rounds. -/
abbrev Shape.ℓ (s : Shape) : ℕ := s.lm1 + 1

/-- The shape of a level from its fold count, rate exponent and query count, the three numbers a
parameter set gives: the glue from a level of the parameters (`fold ≥ 1`) to a `Shape`. -/
def Shape.ofFold (fold R t : ℕ) : Shape := ⟨fold - 1, R, t⟩

/-- A level of the parameters with at least one fold has that many folds as a `Shape`. -/
theorem Shape.ofFold_ℓ {fold : ℕ} (h : 0 < fold) (R t : ℕ) : (Shape.ofFold fold R t).ℓ = fold := by
  simp only [Shape.ofFold, Shape.ℓ]; omega

/-- The tables of `n` variables. -/
abbrev Tab (n : ℕ) : Type := CMlPolynomialEval E n

/-! ## The data of a level -/

/-- The variables the folded table has, when the next level folds `s'.ℓ` times and leaves `κ'`:
the message variables of the level's word. -/
abbrev Kap (s' : Shape) (κ' : ℕ) : ℕ := s'.ℓ + κ'

/-- The word a level reads: `2 ^ ℓ` lanes, `2 ^ (κ + R)` positions, `t` positions a question. -/
abbrev WordOf (sh : Shape) (κ : ℕ) : Type := Word sh.ℓ (κ + sh.R) sh.t

/-- A level's one oracle: its word. -/
abbrev OneW (sh : Shape) (κ : ℕ) : Fin 1 → Type := OneOracle (WordOf sh κ)

/-- The unit-weight domain `0, 1` of a plain sumcheck round. -/
abbrev unitDom : SumcheckRound.WeightedDomain E := [(0, 1), (1, 1)]

/-- The check on a received first-round polynomial: its values at `0` and `1` sum to the claim
it was sent for. -/
def chk (q : SumcheckRound.Message E 2) (v : E) : Bool :=
  decide (SumcheckRound.weightedSum 2 unitDom q = v)

/-- The family of claims of a level's fold rounds: the plain sumcheck of the claim's weight and
the level's table, with the side invariant that the oracle is the honest word of the table. -/
def levelFamily (sh : Shape) (κ : ℕ) :
    SumcheckRound.Family E (Weight E (sh.ℓ + κ)) (OneW sh κ) (Tab (sh.ℓ + κ)) 2 where
  claim := fun ctx j c ↦ ProductSum.claim ctx.1.1.onCube ctx.2 j c
  poly := fun ctx j c ↦ ProductSum.roundPoly ctx.1.1.onCube ctx.2 j c
  weight := fun _ _ ↦ unitDom
  inv := fun ctx _ _ ↦ ctx.1.2 0 = wordOf sh.ℓ κ sh.R sh.t ctx.2

/-- The level's family is honest up to its last variable. -/
private theorem levelFamily_honest (sh : Shape) (κ : ℕ) {m : ℕ} (hm : m ≤ sh.ℓ + κ) :
    (levelFamily sh κ).Honest m where
  check := fun _ _ c hj ↦ ProductSum.roundPoly_check _ _ (lt_of_lt_of_le hj hm) c
  next := fun _ _ c x hj ↦ ProductSum.roundPoly_eval _ _ (lt_of_lt_of_le hj hm) c x
  inv_push := fun _ _ _ _ _ h ↦ h

/-- The relation at the start of a level: the claim `(W, c)` with the polynomial of its first
round recorded, the table `f` the witness, the oracle its honest word. -/
def startRel (sh : Shape) (κ : ℕ) :
    Set ((SumcheckRound.MidStmt (Weight E (sh.ℓ + κ)) E 0 2 × ∀ i, OneW sh κ i) ×
      Tab (sh.ℓ + κ)) :=
  SumcheckRound.relMid (levelFamily sh κ) 0

/-- The record a level keeps between its fold rounds and its glue: the claim's weight, the fold
point, the residual claim, and the messages and challenges of the boundary as they arrive. -/
structure Bd (sh : Shape) (κ : ℕ) where
  /-- The claim's weight. -/
  W : Weight E (sh.ℓ + κ)
  /-- The fold point. -/
  r : Vector E sh.ℓ
  /-- The residual claim's value. -/
  c : E
  /-- The residual claim's first-round polynomial for the next sumcheck. -/
  p1 : SumcheckRound.Message E 2
  /-- The out-of-domain point. -/
  z : Vector E κ
  /-- The out-of-domain answer. -/
  cood : E
  /-- The out-of-domain claim's first-round polynomial. -/
  p2 : SumcheckRound.Message E 2
  /-- The grinding nonce. -/
  nonce : E
  /-- The sampled positions. -/
  pos : Fin sh.t → Fin (2 ^ (κ + sh.R))
  /-- The batching challenge. -/
  lam : E
  /-- The folded symbols at the positions. -/
  cq : Fin sh.t → E
  /-- The query batch's first-round polynomial. -/
  p3 : SumcheckRound.Message E 2

/-- A record with the claim set and the rest blank. -/
def Bd.start {sh : Shape} {κ : ℕ} (W : Weight E (sh.ℓ + κ)) (r : Vector E sh.ℓ) (c : E)
    (p1 : SumcheckRound.Message E 2) : Bd sh κ where
  W := W
  r := r
  c := c
  p1 := p1
  z := Vector.replicate κ 0
  cood := 0
  p2 := 0
  nonce := 0
  pos := fun _ ↦ ⟨0, Nat.two_pow_pos _⟩
  lam := 0
  cq := fun _ ↦ 0
  p3 := 0

/-! ## What has been established at each step of a level -/

section Facts

variable {sh : Shape} {κ : ℕ}

/-- The level's table folded by its fold point. -/
def Bd.fold (s : Bd sh κ) (f : Tab (sh.ℓ + κ)) : Tab κ := foldTable f s.r

/-- The residual weight: the claim's weight folded by the fold point. -/
def Bd.resid (s : Bd sh κ) : Weight E κ := foldWeight s.W s.r

/-- The honest first-round polynomial of a weight against the folded table. -/
def firstPoly (A : Weight E κ) (g : Tab κ) : SumcheckRound.Message E 2 :=
  ProductSum.roundPoly A.onCube g 0 #v[]

/-- The residual claim, and its first-round polynomial. -/
def Bd.F1 (s : Bd sh κ) (f : Tab (sh.ℓ + κ)) : Prop :=
  s.c = s.resid.pair (RingHom.id E) (s.fold f) ∧ s.p1 = firstPoly s.resid (s.fold f)

/-- And the out-of-domain answer. -/
private def Bd.F2 (s : Bd sh κ) (f : Tab (sh.ℓ + κ)) : Prop :=
  s.F1 f ∧ s.cood = evalMle (s.fold f) s.z

/-- And the out-of-domain claim's first-round polynomial. -/
private def Bd.F3 (s : Bd sh κ) (f : Tab (sh.ℓ + κ)) : Prop :=
  s.F2 f ∧ s.p2 = firstPoly (eqWeight s.z) (s.fold f)

/-- The folded symbols at the sampled positions are the folded table's encodings there. -/
def Bd.Cq (s : Bd sh κ) (f : Tab (sh.ℓ + κ)) : Prop :=
  ∀ q, s.cq q = encode (algebraMap K E) κ sh.R (s.fold f) (s.pos q)

/-- The query batch's first-round polynomial is the honest one. -/
def Bd.P3 (s : Bd sh κ) (f : Tab (sh.ℓ + κ)) : Prop :=
  s.p3 = firstPoly (queryWeight κ sh.R s.pos s.lam) (s.fold f)

/-- And the folded symbols. -/
private def Bd.F4 (s : Bd sh κ) (f : Tab (sh.ℓ + κ)) : Prop := s.F3 f ∧ s.Cq f

/-- And the query batch's first-round polynomial. -/
private def Bd.F5 (s : Bd sh κ) (f : Tab (sh.ℓ + κ)) : Prop := s.F4 f ∧ s.P3 f

end Facts

/-! ## The relations of a level -/

/-- The inclusion of the next level's word, the message, in the oracles beside the old word. -/
def keepNew : Fin 1 ↪ Fin 1 ⊕ Unit :=
  ⟨fun _ ↦ .inr (), fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- Before the commitment: the level's word is the one oracle, the honest word of the table, and
the facts `P` hold. -/
def relOld {S : Type} (sh : Shape) (κ : ℕ) (P : S → Tab (sh.ℓ + κ) → Prop) :
    Set ((S × ∀ i, OneW sh κ i) × Tab (sh.ℓ + κ)) :=
  {p | p.1.2 0 = wordOf sh.ℓ κ sh.R sh.t p.2 ∧ P p.1.1 p.2}

section Relations

variable (sh sh' : Shape) (κ' : ℕ)

/-- Between the commitment and the reading of the old word: the old word and the next level's
word, the honest words of the table and of its fold, and the facts `P` of the statement's
record. -/
private def relBoth {S : Type} (bd : S → Bd sh (Kap sh' κ'))
    (P : Bd sh (Kap sh' κ') → Tab (sh.ℓ + Kap sh' κ') → Prop) :
    Set ((S × ∀ i, Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ') i) ×
      Tab (sh.ℓ + Kap sh' κ')) :=
  {p | p.1.2 (.inl 0) = wordOf sh.ℓ (Kap sh' κ') sh.R sh.t p.2 ∧
    p.1.2 (.inr ()) = wordOf sh'.ℓ κ' sh'.R sh'.t (foldTable p.2 (bd p.1.1).r) ∧
    P (bd p.1.1) p.2}

/-- After the old word is dropped: the next level's word is the one oracle, and the facts `P`
hold. -/
private def relNew (P : Bd sh (Kap sh' κ') → Tab (sh.ℓ + Kap sh' κ') → Prop) :
    Set ((Bd sh (Kap sh' κ') × ∀ i, Component.keptOracles
        (Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) keepNew i) ×
      Tab (sh.ℓ + Kap sh' κ')) :=
  {p | p.1.2 0 = wordOf sh'.ℓ κ' sh'.R sh'.t (foldTable p.2 p.1.1.r) ∧ P p.1.1 p.2}

end Relations

/-! ## The components of a level -/

/-- A first-round polynomial of an honest claim passes the check at the claim's value. -/
theorem chk_firstPoly {κ : ℕ} (hκ : 0 < κ) (A : Weight E κ) (g : Tab κ) :
    chk (firstPoly A g) (A.pair (RingHom.id E) g) = true := by
  unfold chk firstPoly
  rw [decide_eq_true_eq, ProductSum.roundPoly_check _ _ hκ, claim_zero]

/-- The next level's table has at least one variable: a level folds at least once. -/
private theorem kap_pos (sh' : Shape) (κ' : ℕ) : 0 < Kap sh' κ' :=
  Nat.add_pos_left (Nat.succ_pos _) _

section Folds

variable (sh : Shape) (κ : ℕ)

/-- The first fold challenge: the polynomial of the first round is already received. -/
def foldFirst : Component.Def (SumcheckRound.MidStmt (Weight E (sh.ℓ + κ)) E 0 2)
    (OneW sh κ) (Tab (sh.ℓ + κ)) (SumcheckRound.Stmt (Weight E (sh.ℓ + κ)) E 1)
    (OneW sh κ) (Tab (sh.ℓ + κ)) (draw E) :=
  SumcheckRound.drawChallenge 0 (levelFamily sh κ).weight

/-- The remaining fold rounds. -/
def foldRest : Component.Def (SumcheckRound.Stmt (Weight E (sh.ℓ + κ)) E 1)
    (OneW sh κ) (Tab (sh.ℓ + κ)) (SumcheckRound.Stmt (Weight E (sh.ℓ + κ)) E sh.ℓ)
    (OneW sh κ) (Tab (sh.ℓ + κ)) (roundsSpec E 2 sh.lm1) :=
  SumcheckRound.rounds (levelFamily sh κ).poly (levelFamily sh κ).weight sh.ℓ sh.lm1 1
    (by simp only [Shape.ℓ]; omega)

/-- The first message after the folds: the residual claim's first-round polynomial. -/
def sendResidual :=
  Component.sendChecked (StmtIn := SumcheckRound.Stmt (Weight E (sh.ℓ + κ)) E sh.ℓ)
    (StmtOut := Bd sh κ) (W := Tab (sh.ℓ + κ)) (OneW sh κ) (SumcheckRound.Message E 2)
    (fun p ↦ firstPoly (foldWeight p.1.1.1 p.1.1.2.1) (foldTable p.2 p.1.1.2.1))
    (fun s m ↦ chk m s.2.2) (fun s m ↦ Bd.start s.1 s.2.1 s.2.2 m)

/-- The fold rounds are honest up to the last lane. -/
private theorem levelHonest : (levelFamily sh κ).Honest sh.ℓ :=
  levelFamily_honest sh κ (by omega)

/-- Completeness of the first fold challenge. -/
@[no_expose] def foldFirstComplete : Component.Complete (foldFirst sh κ)
    (SumcheckRound.relMid (levelFamily sh κ) 0) (SumcheckRound.rel (levelFamily sh κ) 1) :=
  SumcheckRound.drawChallengeComplete 0 _ (levelHonest sh κ) (by simp [Shape.ℓ])

/-- Completeness of the remaining fold rounds. -/
@[no_expose] def foldRestComplete : Component.Complete (foldRest sh κ)
    (SumcheckRound.rel (levelFamily sh κ) 1) (SumcheckRound.rel (levelFamily sh κ) sh.ℓ) :=
  SumcheckRound.roundsComplete (levelFamily sh κ) sh.ℓ (levelHonest sh κ) sh.lm1 1
    (by simp only [Shape.ℓ]; omega)

/-- Completeness of the first message after the folds: the fold's claim is the residual claim. -/
@[no_expose] def sendResidualComplete (hκ : 0 < κ) : Component.Complete (sendResidual sh κ)
    (SumcheckRound.rel (levelFamily sh κ) sh.ℓ) (relOld sh κ Bd.F1) :=
  Component.sendCheckedComplete _ _ _ _ _ fun s o w h ↦ by
    obtain ⟨hinv, hclaim⟩ := h
    have hc : s.2.2 = (foldWeight s.1 s.2.1).pair (RingHom.id E) (foldTable w s.2.1) :=
      hclaim.trans (claim_fold s.1 w s.2.1)
    refine ⟨?_, hinv, hc, rfl⟩
    show chk _ s.2.2 = true
    rw [hc]
    exact chk_firstPoly hκ _ _

end Folds

section Generic

variable {ι : Type} (O : ι → Type) [∀ i, OracleInterface (O i)] (sh : Shape) (κ : ℕ)

/-- The grinding nonce: a message the deployed verifier absorbs into the transcript and checks
against the hash chain, not here. The honest prover sends zero. -/
def sendNonce :=
  Component.sendChecked (StmtIn := Bd sh κ) (StmtOut := Bd sh κ) (W := Tab (sh.ℓ + κ)) O E
    (fun _ ↦ 0) (fun _ _ ↦ true) (fun s m ↦ { s with nonce := m })

/-- The sampled positions of the level's word, one challenge. -/
def drawPositions :=
  Component.sampleChallenge (StmtIn := Bd sh κ) (StmtOut := Bd sh κ) (W := Tab (sh.ℓ + κ)) O
    (Fin sh.t → Fin (2 ^ (κ + sh.R))) (fun _ ↦ true) (fun s x ↦ { s with pos := x })

/-- The batching challenge. -/
def drawBatch :=
  Component.sampleChallenge (StmtIn := Bd sh κ) (StmtOut := Bd sh κ) (W := Tab (sh.ℓ + κ)) O E
    (fun _ ↦ true) (fun s x ↦ { s with lam := x })

/-- The query batch's first-round polynomial, checked against the batch of the folded symbols. -/
def sendQueryPoly :=
  Component.sendChecked (StmtIn := Bd sh κ) (StmtOut := Bd sh κ) (W := Tab (sh.ℓ + κ)) O
    (SumcheckRound.Message E 2)
    (fun p ↦ firstPoly (queryWeight κ sh.R p.1.1.pos p.1.1.lam) (foldTable p.2 p.1.1.r))
    (fun s m ↦ chk m (powerBatch s.cq s.lam)) (fun s m ↦ { s with p3 := m })

variable {rel rel' : Set ((Bd sh κ × ∀ i, O i) × Tab (sh.ℓ + κ))}

/-- Completeness of the nonce, whenever any nonce keeps the relation. -/
private def sendNonceComplete
    (h : ∀ s o w m, ((s, o), w) ∈ rel → (({ s with nonce := m }, o), w) ∈ rel') :
    Component.Complete (sendNonce O sh κ) rel rel' :=
  Component.sendCheckedComplete _ _ _ _ _ fun s o w hin ↦ ⟨rfl, h s o w 0 hin⟩

/-- Completeness of the positions, whenever any positions keep the relation. -/
private def drawPositionsComplete
    (h : ∀ s o w x, ((s, o), w) ∈ rel → (({ s with pos := x }, o), w) ∈ rel') :
    Component.Complete (drawPositions O sh κ) rel rel' :=
  Component.sampleChallengeComplete _ _ _ _ fun s o w hin ↦ ⟨rfl, fun x ↦ h s o w x hin⟩

/-- Completeness of the batching challenge, whenever any challenge keeps the relation. -/
private def drawBatchComplete
    (h : ∀ s o w x, ((s, o), w) ∈ rel → (({ s with lam := x }, o), w) ∈ rel') :
    Component.Complete (drawBatch O sh κ) rel rel' :=
  Component.sampleChallengeComplete _ _ _ _ fun s o w hin ↦ ⟨rfl, fun x ↦ h s o w x hin⟩

/-- Completeness of the query batch's polynomial: when the relation holds the folded symbols are
the folded table's encodings, so the polynomial sums to their batch; and the honest polynomial
recorded lands in the output relation. -/
private def sendQueryPolyComplete (hκ : 0 < κ)
    (h : ∀ s o w, ((s, o), w) ∈ rel → s.Cq w ∧
      (({ s with p3 := firstPoly (queryWeight κ sh.R s.pos s.lam) (s.fold w) }, o), w) ∈ rel') :
    Component.Complete (sendQueryPoly O sh κ) rel rel' :=
  Component.sendCheckedComplete _ _ _ _ _ fun s o w hin ↦ by
    refine ⟨?_, (h s o w hin).2⟩
    have hcq : s.cq = fun q ↦ encode (algebraMap K E) κ sh.R (foldTable w s.r) (s.pos q) :=
      funext (h s o w hin).1
    show chk _ (powerBatch s.cq s.lam) = true
    rw [hcq, ← pair_queryWeight]
    exact chk_firstPoly hκ _ _

end Generic

section Components

variable (sh sh' : Shape) (κ' : ℕ)

/-- The commitment of the next level's word, the encoding of the folded table, beside the
level's word. -/
def commitNext :=
  Component.sendOracleBeside (S := Bd sh (Kap sh' κ')) (S' := Bd sh (Kap sh' κ'))
    (W := Tab (sh.ℓ + Kap sh' κ')) (OneW sh (Kap sh' κ')) (WordOf sh' κ')
    (fun p ↦ wordOf sh'.ℓ κ' sh'.R sh'.t (foldTable p.2 p.1.1.r)) _root_.id

/-- The out-of-domain point, drawn one coordinate at a time. -/
def drawPoint :=
  Component.drawPushes (S := Bd sh (Kap sh' κ')) (W := Tab (sh.ℓ + Kap sh' κ'))
    (Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) E (Kap sh' κ')

/-- The out-of-domain answer: the folded table's extension at the point. -/
def sendOod :=
  Component.sendChecked (StmtIn := Bd sh (Kap sh' κ') × Vector E (Kap sh' κ'))
    (StmtOut := Bd sh (Kap sh' κ')) (W := Tab (sh.ℓ + Kap sh' κ'))
    (Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) E
    (fun p ↦ evalMle (foldTable p.2 p.1.1.1.r) p.1.1.2) (fun _ _ ↦ true)
    (fun s m ↦ { s.1 with z := s.2, cood := m })

/-- The out-of-domain claim's first-round polynomial, checked against the answer. -/
def sendOodPoly :=
  Component.sendChecked (StmtIn := Bd sh (Kap sh' κ')) (StmtOut := Bd sh (Kap sh' κ'))
    (W := Tab (sh.ℓ + Kap sh' κ'))
    (Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) (SumcheckRound.Message E 2)
    (fun p ↦ firstPoly (eqWeight p.1.1.z) (foldTable p.2 p.1.1.r)) (fun s m ↦ chk m s.cood)
    (fun s m ↦ { s with p2 := m })

/-- The question to the level's word: the sampled positions. -/
def readQuery (s : Bd sh (Kap sh' κ')) :
    [Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')]ₒ.Domain :=
  ⟨.inl 0, s.pos⟩

/-- The record of the answer: each row folded by the fold point. -/
def readOut (s : Bd sh (Kap sh' κ'))
    (a : [Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')]ₒ.Range
      (readQuery sh sh' κ' s)) : Bd sh (Kap sh' κ') :=
  { s with cq := fun q ↦ foldRow s.r ((a : Fin sh.t → Vector E (2 ^ sh.ℓ)) q) }

/-- The reading of the level's word at the positions, which then drops it. -/
def readOld :=
  Component.queryRecord (StmtIn := Bd sh (Kap sh' κ')) (StmtOut := Bd sh (Kap sh' κ'))
    (W := Tab (sh.ℓ + Kap sh' κ'))
    (Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) keepNew
    (readQuery sh sh' κ') (fun _ _ ↦ true) (readOut sh sh' κ')

/-- The glued claim: its weight, its value and its first-round polynomial, from the three
claims; the prover's table is the folded one. -/
def glue :=
  Component.mapWitness (StmtIn := Bd sh (Kap sh' κ'))
    (StmtOut := SumcheckRound.MidStmt (Weight E (sh'.ℓ + κ')) E 0 2)
    (W := Tab (sh.ℓ + Kap sh' κ')) (W' := Tab (sh'.ℓ + κ'))
    (Component.keptOracles (Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ'))
      keepNew)
    (fun s ↦ ((gluedWeight s.resid s.z s.pos s.lam,
      (#v[], powerBatch ![s.c, s.cood, powerBatch s.cq s.lam] s.lam)),
      batchMessage ![s.p1, s.p2, s.p3] s.lam))
    (fun p ↦ foldTable p.2 p.1.1.r)

/-- Completeness of the commitment: the new word is the honest word of the folded table. -/
private def commitNextComplete : Component.Complete (commitNext sh sh' κ')
    (relOld sh (Kap sh' κ') Bd.F1) (relBoth sh sh' κ' _root_.id Bd.F1) :=
  Component.sendOracleBesideComplete _ _ _ _ fun _ _ _ h ↦ ⟨h.1, rfl, h.2⟩

/-- Completeness of the point's draws: the relation does not read the point. -/
private def drawPointComplete : Component.Complete (drawPoint sh sh' κ')
    (relBoth sh sh' κ' _root_.id Bd.F1)
    (relBoth sh sh' κ' (Prod.fst : Bd sh (Kap sh' κ') × Vector E (Kap sh' κ') → _) Bd.F1) :=
  Component.drawPushesComplete (S := Bd sh (Kap sh' κ')) (W := Tab (sh.ℓ + Kap sh' κ'))
    (Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) E
    (fun j ↦ relBoth sh sh' κ' (Prod.fst : Bd sh (Kap sh' κ') × Vector E j → _) Bd.F1)
    (fun _ _ _ h ↦ h)
    (fun _ _ ↦ Component.sampleChallengeComplete _ _ _ _ fun _ _ _ h ↦ ⟨rfl, fun _ ↦ h⟩)
    (Kap sh' κ') le_rfl

/-- Completeness of the out-of-domain answer: the folded table's extension at the point. -/
private def sendOodComplete : Component.Complete (sendOod sh sh' κ')
    (relBoth sh sh' κ' (Prod.fst : Bd sh (Kap sh' κ') × Vector E (Kap sh' κ') → _) Bd.F1)
    (relBoth sh sh' κ' _root_.id Bd.F2) :=
  Component.sendCheckedComplete _ _ _ _ _ fun _ _ _ h ↦ ⟨rfl, h.1, h.2.1, h.2.2, rfl⟩

/-- Completeness of the out-of-domain claim's polynomial: it sums to the answer. -/
private def sendOodPolyComplete : Component.Complete (sendOodPoly sh sh' κ')
    (relBoth sh sh' κ' _root_.id Bd.F2) (relBoth sh sh' κ' _root_.id Bd.F3) :=
  Component.sendCheckedComplete _ _ _ _ _ fun s o w h ↦ by
    refine ⟨?_, h.1, h.2.1, h.2.2, rfl⟩
    have hc : s.cood = (eqWeight s.z).pair (RingHom.id E) (foldTable w s.r) :=
      h.2.2.2.trans (pair_eqWeight_id _ _).symm
    show chk (firstPoly (eqWeight s.z) (foldTable w s.r)) s.cood = true
    rw [hc]
    exact chk_firstPoly (kap_pos sh' κ') _ _

/-- Completeness of the reading: the old word's rows at the positions, folded, are the folded
table's encodings there. -/
private def readOldComplete : Component.Complete (readOld sh sh' κ')
    (relBoth sh sh' κ' _root_.id Bd.F3) (relNew sh sh' κ' Bd.F4) :=
  Component.queryRecordComplete _ _ _ _ _ fun s o w h ↦ by
    obtain ⟨h1, h2, h3⟩ := h
    have h1' : (o (.inl 0) : Word sh.ℓ (Kap sh' κ' + sh.R) sh.t) =
        wordOf sh.ℓ (Kap sh' κ') sh.R sh.t w := h1
    have hans : (Component.answerOf (Component.besideOracles (OneW sh (Kap sh' κ'))
        (WordOf sh' κ')) o (readQuery sh sh' κ' s) : Fin sh.t → Vector E (2 ^ sh.ℓ)) =
        fun k ↦ (wordOf sh.ℓ (Kap sh' κ') sh.R sh.t w).row (s.pos k) := by
      have h0 : (Component.answerOf (Component.besideOracles (OneW sh (Kap sh' κ'))
          (WordOf sh' κ')) o (readQuery sh sh' κ' s) : Fin sh.t → Vector E (2 ^ sh.ℓ)) =
          fun k ↦ (o (.inl 0) : Word sh.ℓ (Kap sh' κ' + sh.R) sh.t).row (s.pos k) := rfl
      rw [h0, h1']
    refine ⟨rfl, h2, ?_⟩
    refine ⟨h3, fun q ↦ ?_⟩
    show foldRow s.r ((Component.answerOf _ o (readQuery sh sh' κ' s) :
      Fin sh.t → Vector E (2 ^ sh.ℓ)) q) = _
    rw [hans]
    exact foldRow_wordOf sh.R sh.t w s.r (s.pos q)

/-- Completeness of the glue: the glued claim, polynomial and weight are those of the glued
claims, on the folded table (`pair_gluedWeight`, `roundPoly_batch`), and the next level's word is
the honest word of that table. -/
private def glueComplete : Component.Complete (glue sh sh' κ') (relNew sh sh' κ' Bd.F5)
    (startRel sh' κ') :=
  Component.mapWitnessComplete _ _ _ fun s o w h ↦ by
    obtain ⟨h2, ⟨⟨⟨⟨⟨hc, hp1⟩, hcood⟩, hp2⟩, hcq⟩, hp3⟩⟩ := h
    have hcqf : s.cq = fun q ↦ encode (algebraMap K E) (Kap sh' κ') sh.R (foldTable w s.r)
        (s.pos q) := funext hcq
    refine ⟨⟨h2, ?_⟩, ?_⟩
    · show powerBatch ![s.c, s.cood, powerBatch s.cq s.lam] s.lam =
        ProductSum.claim (gluedWeight s.resid s.z s.pos s.lam).onCube (foldTable w s.r) 0 #v[]
      rw [claim_zero, pair_gluedWeight, hc, hcood, hcqf]
      rfl
    · show batchMessage ![s.p1, s.p2, s.p3] s.lam =
        ProductSum.roundPoly (gluedWeight s.resid s.z s.pos s.lam).onCube (foldTable w s.r) 0 #v[]
      rw [show (gluedWeight s.resid s.z s.pos s.lam).onCube = batchWeight (fun j ↦
        (![s.resid, eqWeight s.z, queryWeight (Kap sh' κ') sh.R s.pos s.lam] j).onCube) s.lam
        from rfl, roundPoly_batch]
      congr 1
      funext i
      fin_cases i
      · exact hp1
      · exact hp2
      · exact hp3

/-! ## The level -/

/-- The steps of a level, in the deployed verifier's order, followed by the steps `k` of the rest
of the opening: the first fold challenge, the other fold rounds, the residual claim's polynomial,
the commitment, the out-of-domain point, answer and polynomial, the grinding nonce, the positions
and the batching challenge, the reading of the old word (no round), the query batch's polynomial,
and the glue (no round). -/
abbrev levelSteps (k : List Step) : List Step :=
  .chal E inferInstance :: .rds E inferInstance 2 sh.lm1 :: .msg (SumcheckRound.Message E 2) ::
    .oracle (WordOf sh' κ') inferInstance :: .chals E inferInstance (Kap sh' κ') :: .msg E ::
    .msg (SumcheckRound.Message E 2) :: .msg E ::
    .chal (Fin sh.t → Fin (2 ^ (Kap sh' κ' + sh.R))) inferInstance :: .chal E inferInstance ::
    .skip :: .msg (SumcheckRound.Message E 2) :: .skip :: k

variable {ι₃ : Type} {O₃ : ι₃ → Type} [∀ i, OracleInterface (O₃ i)] {S₃ W₃ : Type}
  {k : List Step}

/-- One level of WHIR's opening, from the running claim with its first-round polynomial received
to the glued running claim of the next level, followed by `R`, the opening from the next level
on. -/
def levelDef
    (R : Component.Def (SumcheckRound.MidStmt (Weight E (sh'.ℓ + κ')) E 0 2) (OneW sh' κ')
      (Tab (sh'.ℓ + κ')) S₃ O₃ W₃ (seqSpec k)) :
    Component.Def (SumcheckRound.MidStmt (Weight E (sh.ℓ + Kap sh' κ')) E 0 2)
      (OneW sh (Kap sh' κ')) (Tab (sh.ℓ + Kap sh' κ')) S₃ O₃ W₃
      (seqSpec (levelSteps sh sh' κ' k)) :=
  (foldFirst sh (Kap sh' κ')).append <| (foldRest sh (Kap sh' κ')).append <|
  (sendResidual sh (Kap sh' κ')).append <| (commitNext sh sh' κ').append <|
  (drawPoint sh sh' κ').append <| (sendOod sh sh' κ').append <|
  (sendOodPoly sh sh' κ').append <| (sendNonce _ sh (Kap sh' κ')).append <|
  (drawPositions _ sh (Kap sh' κ')).append <| (drawBatch _ sh (Kap sh' κ')).append <|
  (readOld sh sh' κ').append <| (sendQueryPoly _ sh (Kap sh' κ')).append <|
  (glue sh sh' κ').append R

variable {rel₃ : Set ((S₃ × ∀ i, O₃ i) × W₃)}

/-- Perfect completeness of a level followed by the opening from the next level on: from an
honest running claim on a table and its honest word to the opening's final relation, given the
completeness of the rest. Its body uses the per-step completeness definitions, which are private,
so it is not exposed. -/
@[no_expose] def levelComplete {R : Component.Def (SumcheckRound.MidStmt (Weight E (sh'.ℓ + κ')) E 0 2)
      (OneW sh' κ') (Tab (sh'.ℓ + κ')) S₃ O₃ W₃ (seqSpec k)}
    (CR : Component.Complete R (startRel sh' κ') rel₃) :
    Component.Complete (levelDef sh sh' κ' R) (startRel sh (Kap sh' κ')) rel₃ :=
  (foldFirstComplete sh (Kap sh' κ')).append <|
  (foldRestComplete sh (Kap sh' κ')).append <|
  (sendResidualComplete sh (Kap sh' κ') (kap_pos sh' κ')).append <|
  (commitNextComplete sh sh' κ').append <|
  (drawPointComplete sh sh' κ').append <| (sendOodComplete sh sh' κ').append <|
  (sendOodPolyComplete sh sh' κ').append <|
  (sendNonceComplete _ sh (Kap sh' κ') (rel := relBoth sh sh' κ' _root_.id Bd.F3)
    (rel' := relBoth sh sh' κ' _root_.id Bd.F3) (fun _ _ _ _ h ↦ h)).append <|
  (drawPositionsComplete _ sh (Kap sh' κ') (rel := relBoth sh sh' κ' _root_.id Bd.F3)
    (rel' := relBoth sh sh' κ' _root_.id Bd.F3) (fun _ _ _ _ h ↦ h)).append <|
  (drawBatchComplete _ sh (Kap sh' κ') (rel := relBoth sh sh' κ' _root_.id Bd.F3)
    (rel' := relBoth sh sh' κ' _root_.id Bd.F3) (fun _ _ _ _ h ↦ h)).append <|
  (readOldComplete sh sh' κ').append <|
  (sendQueryPolyComplete _ sh (Kap sh' κ') (kap_pos sh' κ') (rel := relNew sh sh' κ' Bd.F4)
    (rel' := relNew sh sh' κ' Bd.F5) (fun _ _ _ h ↦ ⟨h.2.2, h.1, h.2, rfl⟩)).append <|
  (glueComplete sh sh' κ').append CR

end Components

end Whir

end

end LeanerVM.Protocol
