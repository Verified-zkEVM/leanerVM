import LeanerVM.Protocol.ToArkLib.GrandProductSecurity
import LeanerVM.Protocol.ToArkLib.Oracles
import LeanerVM.Protocol.Spine.Errors
import LeanerVMTests.Protocol.GrandProduct

/-!
# Grand-product knowledge-soundness tests

Over `E`, on the trees of the grand-product tests.

* **The theorem has an inhabitant** at the slot's error: `gkrSecurity 3 4 sixteen noRiders` at
  the unit `overE 1`, with riders, and for an odd `μ`.
* **The round check is load-bearing.** Without it, the challenge of the second step's first
  round is not knowledge sound below error one, whatever the extractor and the state function:
  from a statement whose running claim is the family's plus one, the honest polynomial lands in
  the next relation at every challenge.
* **The descendants' check is load-bearing.** Without it, no knowledge state function exists for
  the descendants' message, whatever the extractor: from a statement whose final claim is the
  family's plus one, the honest descendants are accepted into the relation after the message.
* **Partial points.** The coordinates the state function tracks: the sumcheck challenges fill
  `ρ, …, ρ + j − 1`, the combination challenges `0, …, i − 1`, and together the whole new point.

The refutations take their statement at a variable layer statement and point: a statement
built from the hand run's values puts the trees' evaluation over `E` into a definitional
comparison, which does not finish (`tests/README.md`).
-/

namespace LeanerVMTests.Protocol.GrandProductSecurity

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Gkr LeanerVM.Protocol.SumcheckRound
  LeanerVMTests.Protocol.GrandProduct CompPoly CMlPolynomialEval
open scoped NNReal

/-! ## The theorem has an inhabitant -/

/-- The slot's unit is at least `1 / |E|`. -/
theorem overE_one : (1 : ℝ≥0) / (Fintype.card E : ℝ≥0) ≤ overE 1 := by
  rw [overE, Nat.cast_one]

/-- Knowledge soundness of `gkr 3 4` at the slot's error, without riders. -/
noncomputable example : Component.Security (gkr 3 4 sixteen) (relIn 3 4 sixteen noRiders)
    (relOut 3 4 sixteen noRiders) (gkrError E (overE 1) 3 4) :=
  gkrSecurity 3 4 sixteen noRiders (overE 1) overE_one

/-- With a rider. -/
noncomputable example : Component.Security (gkr 1 2 four) (relIn 1 2 four rider)
    (relOut 1 2 four rider) (gkrError E (overE 1) 1 2) :=
  gkrSecurity 1 2 four rider (overE 1) overE_one

/-- For an odd `μ`, where the binary layer comes first. -/
noncomputable example : Component.Security (gkr 3 3 eight) (relIn 3 3 eight noRiders)
    (relOut 3 3 eight noRiders) (gkrError E (overE 1) 3 3) :=
  gkrSecurity 3 3 eight noRiders (overE 1) overE_one

/-! ## The round check is load-bearing -/

/-- The second step's family, on the tests' three sixteen-leaf trees. -/
def Φ : SumcheckRound.Family E (LayerX Unit E 3 2) NoOracle Unit 4 :=
  family 3 4 sixteen noRiders 2 2

/-- The map of the first round's challenge: the polynomial's value at it is the next claim. -/
def nextClaim (p : MidStmt (LayerX Unit E 3 2) E 0 4) (c : E) :
    SumcheckRound.Stmt (LayerX Unit E 3 2) E 1 :=
  SumcheckRound.next 0 p.1 (SumcheckRound.evaluate 4 p.2 c) c

/-- A verifier that draws the first round's challenge without checking the polynomial has no
knowledge error below one, whatever the extractor and the state function: from a running claim
off by one, the honest polynomial is accepted at every challenge. -/
theorem unchecked_round_not_rbr {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) {WitMid : Fin 2 → Type}
    {Ex : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
      (MidStmt (LayerX Unit E 3 2) E 0 4 × ∀ i, NoOracle i) Unit Unit (draw E) WitMid}
    {kSF : Verifier.KnowledgeStateFunction init impl (relMid Φ 0) (rel Φ 1)
      (Component.sampleVerifier NoOracle E (fun _ ↦ true) nextClaim).toVerifier Ex}
    {ε : (draw E).ChallengeIdx → ℝ≥0}
    (h : Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl (relMid Φ 0) (rel Φ 1)
      (Component.sampleVerifier NoOracle E (fun _ ↦ true) nextClaim).toVerifier WitMid Ex kSF ε) :
    1 ≤ ε ⟨0, rfl⟩ := by
  obtain ⟨x⟩ : Nonempty (LayerX Unit E 3 2) := ⟨(((), (#v[0, 0], fun _ ↦ 0)), 0)⟩
  exact drawChallenge_unchecked_not_rbr 0 init impl Φ
    (family_honest 3 4 sixteen noRiders 2 2).toConsistent (by decide) h
    (x, (#v[], Φ.claim ((x, noO), ()) 0 #v[] + 1)) noO ()
    (fun h ↦ one_ne_zero (add_eq_left.mp h))
    (fun _ r hr ↦ absurd hr List.not_mem_nil)

/-! ## The descendants' check is load-bearing -/

/-- A verifier that reads the descendants without checking them has no knowledge state function
from the sumcheck's final relation to the relation after the message, whatever the extractor:
from a final claim off by one, the honest descendants are accepted. -/
theorem unchecked_children_no_stateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) {W' : Fin 2 → Type}
    {Ex : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
      (SumcheckRound.Stmt (LayerX Unit E 3 2) E 2 × ∀ i, NoOracle i) Unit Unit
      (say (Fin 3 → Vector E 4)) W'}
    (K : (Component.sendCheckedVerifier NoOracle (Fin 3 → Vector E 4) (fun _ _ ↦ true)
      (childNext 3 2 2)).toVerifier.KnowledgeStateFunction init impl (rel Φ 2)
      (childRel 3 4 sixteen noRiders 2 2 0) Ex) : False := by
  obtain ⟨x⟩ : Nonempty (LayerX Unit E 3 2) := ⟨(((), (#v[0, 0], fun _ ↦ 0)), 0)⟩
  obtain ⟨cv⟩ : Nonempty (Vector E 2) := ⟨#v[0, 0]⟩
  exact Component.sendChecked_no_stateFunction NoOracle (Fin 3 → Vector E 4) _ _ init impl K
    (x, (cv, Φ.claim ((x, noO), ()) 2 cv + 1)) noO
    (fun w hmem ↦ by
      cases w
      exact one_ne_zero (add_eq_left.mp hmem.2))
    (children 3 4 sixteen 2 2 x.1.1 noO cv) rfl () ⟨fun r hr ↦ absurd hr List.not_mem_nil, rfl⟩

/-! ## Partial points -/

/-- Two sumcheck challenges of a radix-four layer. -/
def χ : Vector E 2 := #v[a, b]

/-- Two combination challenges. -/
def u : Vector E 2 := #v[c, one]

-- The sumcheck challenges fill coordinates `2` and `3`; nothing else is fixed.
#guard (List.range 6).map (roundsPartial 2 χ) = [none, none, some a, some b, none, none]
-- One combination challenge fills coordinate `0` as well.
#guard (List.range 6).map (interpPartial 2 χ (#v[c] : Vector E 1)) =
  [some c, none, some a, some b, none, none]
-- Both fill the whole new point `(u, χ)`.
#guard (List.range 6).map (interpPartial 2 χ u) = [some c, some one, some a, some b, none, none]
-- The descendants' coordinates, by the combination challenges alone.
#guard (List.range 3).map (combPartial u) = [some c, some one, none]

end LeanerVMTests.Protocol.GrandProductSecurity
