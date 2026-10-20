/-
  LeanerVM.Protocol.Whir.OpenSound

  `whirOpen` is round-by-round sound for the list relation: the parameters of a chain of levels,
  the errors its schedule assigns, and the security of the opening. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.Whir.LevelSound
public import LeanerVM.Protocol.Whir.FinalSound
public import LeanerVM.Protocol.Whir.Open

/-!
# The opening of WHIR is round-by-round sound

Category B: `whirOpen_rbrSoundness`, `thm:rbr` of Annex B at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, for the schedule `whirOpen` has (the deployed one).

**What it says.** The input relation (`relOpen`) is the list relation `relopen`: some interleaved
codeword within the first level's threshold of the committed word decodes to a table whose
weighted claim is the statement's value. The theorem says that the verifier of `whirOpen`, from a
statement outside it, reaches acceptance with a probability bounded by the sum of the errors of its
challenges (`Component.Security`, round by round), the errors being those of `thm:rbr` in the
form this repository's components assign them:

| challenge | error | where |
| --- | --- | --- |
| the `j`-th fold challenge of a level | `(2 L + 2 ^ (ℓ - j - 1) N) / |E|` | `foldErr` |
| each coordinate of the out-of-domain point | `C(L', 2) / |E|` | `pointSecurity` |
| the query positions | `a ^ t / (2 ^ (κ + R)) ^ t = (1 - γ) ^ t` | `positionsSecurity` |
| the batching challenge | `(t + 1) L' / |E|` | `batchingSecurity` |
| the last level's batching challenge | `t / |E|` | `finalBatchingSecurity` |
| each round of the tail | `2 / |E|` | `tailFirstSecurity`, `tailRestSecurity` |

`L` is the list bound of the level's own code, `L'` the next level's; `N` the bad folds of mutual
correlated agreement. The out-of-domain point is `κ` challenges here, drawn one at a time, and
each costs `C(L', 2) / |E|`; their sum is `thm:rbr`'s `C(L', 2) κ / |E|`, which the pinned theorem
charges to one message, so the per-round error is smaller than the pinned entry.

**What it assumes.** The two interfaces of `LeanerVM.Protocol.Whir.Lanes`, per level, in
the parameters (`Par`, `Ladder.Pars`): the list bound (the Johnson bound) and mutual correlated
agreement up to the Johnson bound. They are theorems of coding theory that this repository consumes
(`McaJohnson`, Annex B's `thm:mca-johnson`); proved here is everything else, from the encoder's
distance: the fold-list lemma, the counting, the composition. Two letters differ from the Annex:
`a` is the agreement threshold `(1 - γ) 2 ^ (κ + R)` of a level, and the numerator of
`thm:mca-johnson`'s error, which the Annex calls `a`, is `N`.

**What it is not.** Knowledge soundness: the language is the list relation, nothing is extracted
(extraction from list binding is a further step), and the witness is read back by an arbitrary
function.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec
  StepSchedule
open scoped NNReal

@[expose] public section

namespace Whir

namespace Ladder

/-- The parameters of every level of a chain. -/
def Pars : {sh : Shape} → {κ : ℕ} → Ladder sh κ → Type
  | _, _, .last sh nf => Par sh (nf + 1)
  | _, _, @cons sh sh' κ' L => Par sh (Kap sh' κ') × L.Pars

/-- The parameters of the first level. -/
def headPar : {sh : Shape} → {κ : ℕ} → (L : Ladder sh κ) → L.Pars → Par sh κ
  | _, _, .last _ _, P => P
  | _, _, .cons _ _, P => P.1

/-- The errors of the chain's challenges. -/
noncomputable def err : {sh : Shape} → {κ : ℕ} → (L : Ladder sh κ) → L.Pars →
    (seqSpec L.steps).ChallengeIdx → ℝ≥0
  | _, _, .last _ _, P => finalErr P
  | _, _, @cons _ _ _ L, P => levelErr P.1 (L.headPar P.2) (L.err P.2)

/-- **The chain is sound for the list relation**, from the language at the start of its first level
to acceptance. -/
noncomputable def compSecurity : {sh : Shape} → {κ : ℕ} → (L : Ladder sh κ) → (ps : L.Pars) →
    Component.Security L.comp (foldRelMid (L.headPar ps) 0) Set.univ (L.err ps)
  | _, _, .last _ _, P => finalSecurity P
  | _, _, @cons _ _ _ L, P => levelSecurity P.1 (L.headPar P.2) (L.compSecurity P.2)

end Ladder

section Open

variable {sh : Shape} {κ : ℕ} (P : Par sh κ)

/-- The list relation of the opening, on the stack's weight and value and the committed word:
some interleaved codeword within the threshold of the word decodes to a table whose weighted claim,
read on the relayout of the stack, is the value. -/
def OpenLang (W : Weight E (κ + sh.ℓ)) (C : E) (o : ∀ i, OneW sh κ i) : Prop :=
  FoldLang P 0 (relayoutWeight W) (#v[] : Vector E 0) C o

/-- The list relation, ignoring the witness. -/
def relOpen : Set (((Weight E (κ + sh.ℓ) × E) × ∀ i, OneW sh κ i) × Tab (κ + sh.ℓ)) :=
  Component.indep _ _ _ fun p ↦ OpenLang P p.1.1 p.1.2 p.2

/-- The list relation after the relayout of the stack. -/
def relLane : Set (((Weight E (sh.ℓ + κ) × E) × ∀ i, OneW sh κ i) × Tab (sh.ℓ + κ)) :=
  Component.indep _ _ _ fun p ↦ FoldLang P 0 p.1.1 (#v[] : Vector E 0) p.1.2 p.2

/-- The relayout of the stack carries the list relation across. -/
def stackRelayoutSecurity : Component.Security (stackRelayout sh κ) (relOpen P) (relLane P)
    (fun i ↦ Fin.elim0 i.1) :=
  Component.mapWitnessSecurity _ _ _ (fun _ ↦ Vector.replicate _ 0) fun _ _ _ h ↦ h

/-- The opening claim's first-round polynomial: the message carries nothing into the language. -/
def sendFirstSecurity : Component.Security (sendFirst sh κ) (relLane P) (foldRelMid P 0)
    (sayError (SumcheckRound.Message E 2)) :=
  Component.sendCheckedSecurity (OneW sh κ) (SumcheckRound.Message E 2) _ _ _ fun _ _ _ _ _ h ↦ by
    rcases h with ⟨g, hg, hc, -⟩ | hn
    · exact Or.inl ⟨g, hg, hc⟩
    · exact Or.inr hn

/-- The errors of the opening: the chain's, after the relayout and the opening claim's
polynomial. -/
noncomputable def openErr (L : Ladder sh κ) (ps : L.Pars) :
    (seqSpec (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps)).ChallengeIdx → ℝ≥0 :=
  errAppend (fun i ↦ Fin.elim0 i.1) <| errAppend (sayError (SumcheckRound.Message E 2)) <|
    L.err ps

end Open

/-- **`whirOpen` is round-by-round sound for the list relation** (`thm:rbr`): for a chain of levels
with its parameters, the opening's verifier, from a statement outside the list relation of the
committed word, reaches acceptance with probability at most the sum of the errors of its challenges
(`openErr`): the fold challenges, the coordinates of the out-of-domain points, the query positions,
the batching challenges, and the tail. -/
noncomputable def whirOpen_rbrSoundness {sh : Shape} {κ : ℕ} (L : Ladder sh κ) (ps : L.Pars) :
    Component.Security (whirOpen sh κ L) (relOpen (L.headPar ps)) Set.univ (openErr L ps) := by
  unfold whirOpen
  exact (stackRelayoutSecurity (L.headPar ps)).append <|
    (sendFirstSecurity (L.headPar ps)).append (L.compSecurity ps)

end Whir

end

end LeanerVM.Protocol
