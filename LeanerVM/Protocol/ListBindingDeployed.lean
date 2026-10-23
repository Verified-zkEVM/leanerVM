/-
  LeanerVM.Protocol.ListBindingDeployed

  The list-binding compilation at leanVM: the leanISA instance, its phases, WHIR's chain and
  parameters at every admissible stack size and rate, and the decoder that takes the transform's
  exact path before brute force; its knowledge soundness and completeness with no hypothesis.
-/

module

public import LeanerVM.Protocol.ListBinding
public import LeanerVM.Protocol.LeanIsa
public import LeanerVM.Protocol.Piop
public import LeanerVM.Protocol.Whir.Deployed
public import LeanerVM.Protocol.Whir.DecodeNtt

/-!
# The list-binding compilation at leanVM

Category A: the statements are the authority; the parameters are those of
`LeanerVM.Protocol.Whir.Deployed` (Category B there).

* `admissible_of_sizes`: an admissible announcement and a valid rate give an admissible stack
  size and rate for WHIR's parameters, so `deployedChain` is defined on them.
* `deployedHead`: level 0 of the deployed chain, computed: its shape, the variables it leaves and
  its threshold `johnsonPar`'s `⌈(√ρ + η) n⌉₊`; `deployedChain_head` decides on the window that
  the chain's level 0 is this one.
* `deployedDecoder`: the decoder at level 0, `ListDecoder.nttFirst` over `ListDecoder.bruteForce`:
  the transform's exact path, which every codeword takes, then the brute force, which is exact
  and computable but runs on toy words only. It is a definition with no `noncomputable`, at the
  computed indices, carried to the chain's.
* `listBinding_deployed`: `listBinding_compile` at the leanISA instance of `prog` at the sizes
  `s`, with leanVM's phases and their securities, the deployed chain and its parameters, and
  `deployedDecoder`; `listBinding_deployed_rbrKnowledgeSoundness` and
  `listBinding_deployed_perfectCompleteness` are its two halves. No hypothesis beyond the
  admissibility of `s` and the rate.

`listBinding_deployed` is `noncomputable`, as `deployed_rbrSoundness` is: the parameters of a
level carry the bound `N = ⌊mcaConstant n D η⌋₊` on the bad folds, a real number's floor, and
WHIR's security takes the parameters as data. The decoder, which is the extractor's work beyond
deciding `M3Holds`, is computable; `listBinding_extractedStack_eq` reads the extracted stack off
it.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Parameters.Whir LeanerVM.Semantics Whir LeanIsa OracleComp
  OracleSpec
open scoped NNReal

@[expose] public section

/-! ## The window -/

/-- An admissible announcement at a valid rate is in the window of WHIR's parameters. -/
theorem admissible_of_sizes {prog : Program} {s : Sizes} (hs : s.Admissible prog)
    {ρ : ℕ} (hρ : validRate ρ) : Whir.Admissible (leanIsaμ prog s) ρ :=
  ⟨le_max_right _ _, hs.2.2.2.2, hρ.1, hρ.2⟩

/-! ## Level 0 of the deployed chain -/

namespace Whir

/-- Level 0 of the ladder of a stack size and rate, with its slack. -/
def deployedLevel0 (μ r : ℕ) : Level × ℚ :=
  (((ladder μ r).getD []).zip ((slacks μ r).getD [])).headD (⟨1, 1, 1⟩, 1)

/-- The shape of level 0. -/
def deployedHeadShape (μ r : ℕ) : Shape :=
  Shape.ofFold (deployedLevel0 μ r).1.fold (deployedLevel0 μ r).1.logInvRate
    (deployedLevel0 μ r).1.queries

/-- The variables level 0 leaves. -/
def deployedHeadKap (μ r : ℕ) : ℕ := μ - (deployedLevel0 μ r).1.fold

/-- The threshold of level 0. -/
def deployedHeadThreshold (μ r : ℕ) : ℕ :=
  threshold (deployedHeadKap μ r) (deployedHeadShape μ r).R (deployedLevel0 μ r).2

/-- The chain's level 0 matches the computed one, as a check. -/
def headMatches (μ r : ℕ) (c : Chain) : Bool :=
  c.sh.lm1 == (deployedHeadShape μ r).lm1 && c.sh.R == (deployedHeadShape μ r).R &&
    c.sh.t == (deployedHeadShape μ r).t && c.κ == deployedHeadKap μ r &&
    (c.ladder.headPar c.pars).a == deployedHeadThreshold μ r

/-- Every admissible chain's level 0 is the computed one: one decision on the window. -/
private theorem deployed_head {μ r : ℕ} (h : Admissible μ r) :
    (deployed μ r).all (headMatches μ r) := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r →
      (deployed μ r).all (headMatches μ r) := by decide +kernel
  exact key μ (Nat.lt_succ_of_le h.2.1) r (Nat.lt_succ_of_le h.2.2.2) h

/-- A property every member of `deployed` has, the deployed chain has. -/
private theorem deployedChain_of_all {μ r : ℕ} (h : Admissible μ r) {p : Chain → Bool}
    (hp : (deployed μ r).all p) : p (deployedChain μ r h) :=
  (Option.all_eq_true_iff_get p _).mp hp (deployed_isSome h)

/-- Shapes with equal fields are equal. -/
private theorem shape_ext {a b : Shape} (h₁ : a.lm1 = b.lm1) (h₂ : a.R = b.R) (h₃ : a.t = b.t) :
    a = b := by
  cases a
  cases b
  simp_all

/-- **Level 0 of the deployed chain** is the computed one: its shape, the variables it leaves and
its threshold. -/
theorem deployedChain_head {μ r : ℕ} (h : Admissible μ r) :
    (deployedChain μ r h).sh = deployedHeadShape μ r ∧
      (deployedChain μ r h).κ = deployedHeadKap μ r ∧
      ((deployedChain μ r h).ladder.headPar (deployedChain μ r h).pars).a =
        deployedHeadThreshold μ r := by
  have hm := deployedChain_of_all h (deployed_head h)
  simp only [headMatches, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hm
  exact ⟨shape_ext h1 h2 h3, h4, h5⟩

/-- The deployed chain's stack has `μ` variables. -/
theorem deployedChain_height {μ r : ℕ} (h : Admissible μ r) :
    (deployedChain μ r h).κ + (deployedChain μ r h).sh.ℓ = μ := by
  have := deployedChain_of_all h (deployed_vars h)
  simpa using this

/-! ## The decoder at level 0 -/

/-- A decoder carried along equal indices. Inlined, so that the indices are never computed. -/
@[macro_inline]
def ListDecoder.cast {κ R a ℓ κ' R' a' ℓ' : ℕ} (hκ : κ = κ') (hR : R = R') (ha : a = a')
    (hℓ : ℓ = ℓ') (D : ListDecoder κ R a ℓ) : ListDecoder κ' R' a' ℓ' := by
  subst hκ hR ha hℓ
  exact D

/-- The decoder at level 0 of the deployed chain, at the computed indices: the transform's exact
path, then the brute force. -/
def deployedHeadDecoder {μ r : ℕ} (h : Admissible μ r) :
    ListDecoder (deployedHeadKap μ r) (deployedHeadShape μ r).R (deployedHeadThreshold μ r)
      (deployedHeadShape μ r).ℓ :=
  have hd := deployedChain_head h
  have hdist : 2 ^ deployedHeadKap μ r ≤ deployedHeadThreshold μ r := by
    rw [← hd.2.1, ← hd.2.2]
    exact ((deployedChain μ r h).ladder.headPar (deployedChain μ r h).pars).hdist
  have hle : deployedHeadThreshold μ r ≤ 2 ^ (deployedHeadKap μ r + (deployedHeadShape μ r).R) := by
    rw [← hd.1, ← hd.2.1, ← hd.2.2]
    exact ((deployedChain μ r h).ladder.headPar (deployedChain μ r h).pars).hle
  have hb : deployedHeadKap μ r + (deployedHeadShape μ r).R ≤ 64 := by
    rw [← hd.1, ← hd.2.1]
    exact ((deployedChain μ r h).ladder.headPar (deployedChain μ r h).pars).hb
  (ListDecoder.bruteForce hdist hb).nttFirst hdist hle hb

/-- **The decoder at level 0 of the deployed chain**, at the chain's indices: computable, by the
transform's exact path, then the brute force. -/
def deployedDecoder {μ r : ℕ} (h : Admissible μ r) :
    ListDecoder (deployedChain μ r h).κ (deployedChain μ r h).sh.R
      ((deployedChain μ r h).ladder.headPar (deployedChain μ r h).pars).a
      (deployedChain μ r h).sh.ℓ :=
  ListDecoder.cast (deployedChain_head h).2.1.symm (congrArg Shape.R (deployedChain_head h).1).symm
    (deployedChain_head h).2.2.symm (congrArg Shape.ℓ (deployedChain_head h).1).symm
    (deployedHeadDecoder h)

end Whir

/-! ## The compilation at leanVM -/

section Deployed

variable (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
  (hρ : validRate ρ)

/-- The deployed chain of the instance's stack at the rate `ρ`. -/
noncomputable abbrev leanIsaChain : Chain :=
  deployedChain (leanIsaμ prog s) ρ (admissible_of_sizes hs hρ)

/-- The heights agree. -/
theorem leanIsaChain_height :
    (leanIsaChain prog s hs ρ hρ).κ + (leanIsaChain prog s hs ρ hρ).sh.ℓ =
      (leanIsaInstance F prog s).μ :=
  deployedChain_height _

/-- **The list-binding compilation at leanVM**, for every admissible announcement and rate: the
leanISA instance, leanVM's phases, WHIR's deployed chain and parameters, and `deployedDecoder`. -/
noncomputable def listBinding_deployed :
    Component.Security
      (listBindingDef (leanVmPhases (leanIsaInstance F prog s) (leanIsa_conditions F prog s))
        (leanIsaChain_height F prog s hs ρ hρ) (leanIsaChain prog s hs ρ hρ).ladder)
      (M3Rel (leanIsaInstance F prog s)) Set.univ
      (listBindingError (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).ladder
        (leanIsaChain prog s hs ρ hρ).pars) :=
  listBinding_compile _ (leanVmSecurity _ (leanIsa_conditions F prog s) le_rfl) _ _ _
    (deployedDecoder (admissible_of_sizes hs hρ))

/-- **Round-by-round knowledge soundness at leanVM**, as a statement about the compiled verifier:
with the extractor and state function of `listBinding_deployed`. -/
theorem listBinding_deployed_rbrKnowledgeSoundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (listBindingDef (leanVmPhases (leanIsaInstance F prog s) (leanIsa_conditions F prog s))
        (leanIsaChain_height F prog s hs ρ hρ) (leanIsaChain prog s hs ρ hρ).ladder).red.verifier
      |>.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
        (M3Rel (leanIsaInstance F prog s)) Set.univ
        (listBinding_deployed F prog s hs ρ hρ).witMid
        (listBinding_deployed F prog s hs ρ hρ).extractor
        ((listBinding_deployed F prog s hs ρ hρ).kSF init impl)
        (listBindingError (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).ladder
          (leanIsaChain prog s hs ρ hρ).pars) :=
  (listBinding_deployed F prog s hs ρ hρ).rbr init impl

/-- **Perfect completeness at leanVM**: on every statement and stack with `M3Holds`, the honest
prover convinces the compiled verifier at the deployed chain surely. -/
theorem listBinding_deployed_perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (listBindingDef (leanVmPhases (leanIsaInstance F prog s) (leanIsa_conditions F prog s))
        (leanIsaChain_height F prog s hs ρ hρ) (leanIsaChain prog s hs ρ hρ).ladder).red
      |>.perfectCompleteness init impl (M3Rel (leanIsaInstance F prog s)) Set.univ :=
  listBinding_perfectCompleteness _ _
    (leanVmComplete _ (leanIsa_conditions F prog s) le_rfl) _ init impl

end Deployed

end

end LeanerVM.Protocol
