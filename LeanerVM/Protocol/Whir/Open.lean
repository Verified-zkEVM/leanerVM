/-
  LeanerVM.Protocol.Whir.Open

  The opening of WHIR as an oracle reduction: a chain of levels, generic over its parameters, from
  the opening claim on the committed stack to acceptance; definition and perfect completeness.
-/

module

public import LeanerVM.Protocol.Whir.Final
public import LeanerVM.Protocol.Whir.Stack

/-!
# The opening of WHIR

Category B: Annex B, Protocol 1, in the transcript order of `python-verifier/verifier.py`
(`verify_whir`). `whirOpen L` is the whole opening, from one weighted claim `<W, q> = C` on the
committed stack `q`, with the stack's honest word as the one oracle, to the verifier's acceptance.

* A `Ladder sh κ` is a chain of levels, generic over the parameters: `last sh nf` is the final
  level, folding `sh.ℓ` times and leaving a plaintext table of `nf + 1` variables
  (`LeanerVM.Protocol.Whir.Final`); `cons sh L` puts a level of shape `sh`
  (`LeanerVM.Protocol.Whir.Level`) before the chain `L` of the next level. The index `κ`
  is the number of variables left after the level's folds, so a level's table has `sh.ℓ + κ`, and
  the consistency of the chain's variable counts is by construction, not a hypothesis.
* `Ladder.comp L` is the chain's component, at the schedule of its steps (`Ladder.steps`), and
  `Ladder.compComplete` its perfect completeness: from the running claim of the first level with
  its first round polynomial received and its honest word, to acceptance.
* `whirOpen L` adds what precedes the first level: the relayout of the stack (the stack's lanes are
  its top coordinates, the first level's its low ones; `LeanerVM.Protocol.WhirFold`), and the
  first-round polynomial of the opening claim, the one message the levels receive already when they
  begin. Its input relation is `stackRel`: the oracle is the honest word of the stack and the
  statement's value is the weighted claim of the stack; `whirOpen_perfectCompleteness` says the
  honest run is accepted with probability one.

`whirOpen` takes the one batched claim, not a list of claims: the opening phase hands WHIR a
single claim, as the deployed prover does (`Component.batch` runs before it).

The committed stack, its relation and the witness are `E`-valued here, while the opening phase
hands over a `K`-valued column and queries it through `pair (algebraMap K E)`. `E`-valued is a
superset, so completeness holds for the `K`-valued stack; what is owed to the pull request that
wires this opening into the opening phase is the lift of the `K`-valued witness to `E` and, for
soundness, that every codeword in the list of a `K`-valued word is `K`-valued (two codewords
that agree on `2 ^ κ` positions are equal, `encode_eq_of_agree`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec
  StepSchedule

@[expose] public section

namespace Whir

/-- A chain of levels, from a level of shape `sh` that leaves `κ` variables after its folds. -/
inductive Ladder : Shape → ℕ → Type
  /-- The final level, leaving a plaintext table of `nf + 1` variables. The table has at least one
  variable: `derive_config` never leaves fewer than two, and the first-round polynomial of the
  tail is checked against its claim only if there is a variable left to sum over
  (`roundPoly` is zero past the last variable, `chk_firstPoly` needs `0 < κ`). -/
  | last (sh : Shape) (nf : ℕ) : Ladder sh (nf + 1)
  /-- A level of shape `sh` before the chain from the next level on. -/
  | cons (sh : Shape) {sh' : Shape} {κ' : ℕ} : Ladder sh' κ' → Ladder sh (Kap sh' κ')

namespace Ladder

/-- The shape of the final level. -/
def finShape : {sh : Shape} → {κ : ℕ} → Ladder sh κ → Shape
  | sh, _, last _ _ => sh
  | _, _, cons _ L => L.finShape

/-- The variables the final level leaves, the plaintext table's. -/
def finN : {sh : Shape} → {κ : ℕ} → Ladder sh κ → ℕ
  | _, _, last _ nf => nf + 1
  | _, _, cons _ L => L.finN

/-- The schedule steps of the chain. -/
def steps : {sh : Shape} → {κ : ℕ} → Ladder sh κ → List Step
  | _, _, last sh nf => finalSteps sh nf
  | _, _, @cons sh sh' κ' L => levelSteps sh sh' κ' L.steps

/-- The chain as a component: from the running claim of its first level, its first-round
polynomial received, to acceptance; the last word is the one oracle left. -/
def comp : {sh : Shape} → {κ : ℕ} → (L : Ladder sh κ) →
    Component.Def (SumcheckRound.MidStmt (Weight E (sh.ℓ + κ)) E 0 2) (OneW sh κ)
      (Tab (sh.ℓ + κ)) Unit (OneW L.finShape L.finN) Unit (seqSpec L.steps)
  | _, _, last sh nf => finalDef sh nf
  | _, _, @cons sh sh' κ' L => levelDef sh sh' κ' L.comp

/-- Perfect completeness of the chain: from an honest running claim on a table and its honest
word, the verifier accepts. -/
def compComplete : {sh : Shape} → {κ : ℕ} → (L : Ladder sh κ) →
    Component.Complete L.comp (startRel sh κ) Set.univ
  | _, _, last sh nf => finalComplete sh nf
  | _, _, @cons sh sh' κ' L => levelComplete sh sh' κ' L.compComplete

end Ladder

section Open

variable (sh : Shape) (κ : ℕ)

/-- The relation the opening's input satisfies: the oracle is the honest word of the stack, lanes
first, and the statement's value is the weighted claim of the weight against the stack. -/
def stackRel : Set (((Weight E (κ + sh.ℓ) × E) × ∀ i, OneW sh κ i) × Tab (κ + sh.ℓ)) :=
  {p | p.1.2 0 = wordOf sh.ℓ κ sh.R sh.t (relayout p.2) ∧
    p.1.1.2 = p.1.1.1.pair (RingHom.id E) p.2}

/-- The relation after the relayout: the same, on the relayout of the stack. -/
private def laneRel : Set (((Weight E (sh.ℓ + κ) × E) × ∀ i, OneW sh κ i) × Tab (sh.ℓ + κ)) :=
  {p | p.1.2 0 = wordOf sh.ℓ κ sh.R sh.t p.2 ∧ p.1.1.2 = p.1.1.1.pair (RingHom.id E) p.2}

/-- The relayout of the stack, in the weight and in the prover's table, no round. -/
def stackRelayout :=
  Component.mapWitness (StmtIn := Weight E (κ + sh.ℓ) × E)
    (StmtOut := Weight E (sh.ℓ + κ) × E) (W := Tab (κ + sh.ℓ)) (W' := Tab (sh.ℓ + κ))
    (OneW sh κ)
    (fun s ↦ (relayoutWeight s.1, s.2)) (fun p ↦ relayout p.2)

/-- The first message: the first-round polynomial of the opening claim, checked against its
value. -/
def sendFirst :=
  Component.sendChecked (StmtIn := Weight E (sh.ℓ + κ) × E)
    (StmtOut := SumcheckRound.MidStmt (Weight E (sh.ℓ + κ)) E 0 2) (W := Tab (sh.ℓ + κ))
    (OneW sh κ) (SumcheckRound.Message E 2) (fun p ↦ firstPoly p.1.1.1 p.2)
    (fun s m ↦ chk m s.2) (fun s m ↦ ((s.1, (#v[], s.2)), m))

/-- Completeness of the relayout: the claim is the same, summed in another order. -/
private def stackRelayoutComplete : Component.Complete (stackRelayout sh κ) (stackRel sh κ)
    (laneRel sh κ) :=
  Component.mapWitnessComplete _ _ _ fun s _ w h ↦ ⟨h.1, by
    show s.2 = (relayoutWeight s.1).pair (RingHom.id E) (relayout w)
    rw [pair_relayoutWeight]
    exact h.2⟩

/-- Completeness of the first message: the opening claim's polynomial sums to its value. -/
private def sendFirstComplete :
    Component.Complete (sendFirst sh κ) (laneRel sh κ) (startRel sh κ) :=
  Component.sendCheckedComplete _ _ _ _ _ fun s o w h ↦ by
    refine ⟨?_, ⟨h.1, ?_⟩, rfl⟩
    · show chk _ s.2 = true
      rw [h.2]
      exact chk_firstPoly (Nat.add_pos_left (Nat.succ_pos _) _) _ _
    · show s.2 = ProductSum.claim s.1.onCube w 0 #v[]
      rw [claim_zero]
      exact h.2

/-- The opening of WHIR: the relayout of the stack, the first-round polynomial of the opening
claim, and the chain of levels. -/
def whirOpen (L : Ladder sh κ) : Component.Def (Weight E (κ + sh.ℓ) × E) (OneW sh κ)
    (Tab (κ + sh.ℓ)) Unit (OneW L.finShape L.finN) Unit
    (seqSpec (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps)) :=
  (stackRelayout sh κ).append <| (sendFirst sh κ).append L.comp

/-- The opening's completeness half. Its body uses the private completeness definitions of the
first two steps, so it is not exposed. -/
@[no_expose] def whirOpenComplete (L : Ladder sh κ) :
    Component.Complete (whirOpen sh κ L) (stackRel sh κ) Set.univ :=
  (stackRelayoutComplete sh κ).append <| (sendFirstComplete sh κ).append L.compComplete

/-- Perfect completeness of the opening: on the honest word of a stack and the weighted claim of
a weight against it, the honest run is accepted with probability one. -/
theorem whirOpen_perfectCompleteness (L : Ladder sh κ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (whirOpen sh κ L).red.perfectCompleteness init impl (stackRel sh κ) Set.univ :=
  (whirOpenComplete sh κ L).complete init impl

end Open

end Whir

end

end LeanerVM.Protocol
