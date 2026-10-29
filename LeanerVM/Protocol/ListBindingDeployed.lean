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
`LeanerVM.Protocol.Whir.Deployed` (Category B there). The result contributes to T4 in the ideal
oracle model, in both directions, at leanVM's instance and parameters.

* `admissible_of_sizes`: an admissible announcement and a valid rate give an admissible stack
  size and rate for WHIR's parameters, so `deployedChain` is defined on them.
* `deployedDecoder`: the decoder at level 0, `ListDecoder.nttFirst` over `ListDecoder.bruteForce`:
  the transform's exact path, which every codeword takes, then the brute force, which is exact
  and computable but runs on toy words only. It is built at level 0's computed indices
  (`deployedChain_head`) and carried to the chain's.
* `listBinding_deployed`: `listBinding_compile` at the leanISA instance of `prog` at the sizes
  `s`, with leanVM's phases and their securities, the deployed chain and its parameters, and
  `deployedDecoder`; `listBinding_deployed_rbrKnowledgeSoundness` and
  `listBinding_deployed_perfectCompleteness` are its two halves. No hypothesis beyond the
  admissibility of `s` and the rate. It is a definition with no `noncomputable`, so its extractor
  compiles.
* `deployedPick`: the commitment's extractor at level 0's computed indices, which compiles without
  building the chain; `deployedPick_eq_commitPick` relates it to the pick at the chain's indices.
  `listBinding_deployed_kSF_one` (past the commitment, the state function holds exactly when the
  pick succeeds) and `listBinding_deployed_extractedStack_eq` (the extracted stack is the pick) are
  the two facts about the extractor that `core` reads, stated with it.
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

namespace Whir

/-! ## The decoder at level 0 -/

/-- A decoder carried along equal indices. Inlined, so that the indices are never computed. -/
@[macro_inline]
def ListDecoder.cast {κ R a ℓ κ' R' a' ℓ' : ℕ} (hκ : κ = κ') (hR : R = R') (ha : a = a')
    (hℓ : ℓ = ℓ') (D : ListDecoder κ R a ℓ) : ListDecoder κ' R' a' ℓ' := by
  subst hκ hR ha hℓ
  exact D

/-- A `K` word carried along equal indices. Inlined, so that the indices are never computed. -/
@[macro_inline]
def KWord.cast {ℓ b t ℓ' b' t' : ℕ} (hℓ : ℓ = ℓ') (hb : b = b') (ht : t = t')
    (w : KWord ℓ b t) : KWord ℓ' b' t' := by
  subst hℓ hb ht
  exact w

/-- The decoder at level 0 of the deployed chain, at the computed indices: the transform's exact
path, then the brute force. -/
def deployedHeadDecoder {μ r : ℕ} (h : Admissible μ r) :
    ListDecoder (deployedHeadKap μ r) (deployedHeadShape μ r).R (deployedHeadThreshold μ r)
      (deployedHeadShape μ r).ℓ :=
  have hd := deployedChain_head h
  have hdist : 2 ^ deployedHeadKap μ r ≤ deployedHeadThreshold μ r :=
    hd.2.1 ▸ hd.2.2 ▸ ((deployedChain μ r h).ladder.headPar (deployedChain μ r h).pars).hdist
  have hle : deployedHeadThreshold μ r ≤ 2 ^ (deployedHeadKap μ r + (deployedHeadShape μ r).R) :=
    hd.1 ▸ hd.2.1 ▸ hd.2.2 ▸ ((deployedChain μ r h).ladder.headPar (deployedChain μ r h).pars).hle
  have hb : deployedHeadKap μ r + (deployedHeadShape μ r).R ≤ 64 :=
    hd.1 ▸ hd.2.1 ▸ ((deployedChain μ r h).ladder.headPar (deployedChain μ r h).pars).hb
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

/-- The commitment's pick with a decoder carried along equal indices is the pick at the original
indices, on the word carried along with it. -/
theorem commitPick_cast (I : M3Instance) {sh sh' : Shape} {κ κ' a a' : ℕ} (hsh : sh = sh')
    (hκ : κ = κ') (ha : a = a') (D : ListDecoder κ' sh'.R a' sh'.ℓ) (hμ : κ + sh.ℓ = I.μ)
    (hμ' : κ' + sh'.ℓ = I.μ) (s : I.Stmt) (w : KWord sh.ℓ (κ + sh.R) sh.t) :
    commitPick I (ListDecoder.cast hκ.symm (congrArg Shape.R hsh).symm ha.symm
        (congrArg Shape.ℓ hsh).symm D) hμ s w =
      commitPick I D hμ' s
        (KWord.cast (congrArg Shape.ℓ hsh) (by rw [hκ, hsh]) (congrArg Shape.t hsh) w) := by
  subst hsh hκ ha
  rfl

/-- A word of the deployed chain's level 0, read at the computed indices. -/
@[macro_inline]
def headWord {μ r : ℕ} (h : Admissible μ r)
    (w : KWord (deployedChain μ r h).sh.ℓ ((deployedChain μ r h).κ + (deployedChain μ r h).sh.R)
      (deployedChain μ r h).sh.t) :
    KWord (deployedHeadShape μ r).ℓ (deployedHeadKap μ r + (deployedHeadShape μ r).R)
      (deployedHeadShape μ r).t :=
  KWord.cast (congrArg Shape.ℓ (deployedChain_head h).1)
    (by rw [(deployedChain_head h).2.1, (deployedChain_head h).1])
    (congrArg Shape.t (deployedChain_head h).1) w

/-- **The commitment's pick at leanVM**, at level 0's computed indices: it compiles without
building the chain. -/
def deployedPick (I : M3Instance) {r : ℕ} (h : Admissible I.μ r) (s : I.Stmt)
    (w : KWord (deployedHeadShape I.μ r).ℓ (deployedHeadKap I.μ r + (deployedHeadShape I.μ r).R)
      (deployedHeadShape I.μ r).t) : Option (Column I.μ) :=
  commitPick I (deployedHeadDecoder h) (deployedHead_height h) s w

/-- The pick at the chain's indices is `deployedPick`, on the word read at the computed ones. -/
theorem deployedPick_eq_commitPick (I : M3Instance) {r : ℕ} (h : Admissible I.μ r) (s : I.Stmt)
    (w : KWord (deployedChain I.μ r h).sh.ℓ
      ((deployedChain I.μ r h).κ + (deployedChain I.μ r h).sh.R) (deployedChain I.μ r h).sh.t) :
    commitPick I (deployedDecoder h) (deployedChain_height h) s w =
      deployedPick I h s (headWord h w) :=
  commitPick_cast I (deployedChain_head h).1 (deployedChain_head h).2.1 (deployedChain_head h).2.2
    (deployedHeadDecoder h) _ _ s w

end Whir

/-! ## The compilation at leanVM -/

section Deployed

variable (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
  (hρ : validRate ρ)

/-- The deployed chain of the instance's stack at the rate `ρ`. -/
def leanIsaChain : Chain :=
  deployedChain (leanIsaμ prog s) ρ (admissible_of_sizes hs hρ)

/-- The heights agree. -/
theorem leanIsaChain_height :
    (leanIsaChain prog s hs ρ hρ).κ + (leanIsaChain prog s hs ρ hρ).sh.ℓ =
      (leanIsaInstance F prog s).μ :=
  deployedChain_height _

/-- **The list-binding compilation at leanVM**, for every admissible announcement and rate: the
leanISA instance, leanVM's phases, WHIR's deployed chain and parameters, and `deployedDecoder`. -/
def listBinding_deployed :
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

/-- The pick at the instance's chain is `deployedPick`, on the word read at the computed
indices. -/
theorem leanIsa_commitPick_eq (st : (leanIsaInstance F prog s).Stmt)
    (x : KWord (leanIsaChain prog s hs ρ hρ).sh.ℓ
      ((leanIsaChain prog s hs ρ hρ).κ + (leanIsaChain prog s hs ρ hρ).sh.R)
      (leanIsaChain prog s hs ρ hρ).sh.t) :
    commitPick (leanIsaInstance F prog s) (deployedDecoder (admissible_of_sizes hs hρ))
        (leanIsaChain_height F prog s hs ρ hρ) st x =
      deployedPick (leanIsaInstance F prog s) (admissible_of_sizes hs hρ) st
        (headWord (admissible_of_sizes hs hρ) x) :=
  deployedPick_eq_commitPick (leanIsaInstance F prog s) (admissible_of_sizes hs hρ) st x

/-- **Past the commitment, the state function at leanVM holds exactly when the pick succeeds**: at
round `1`, for every witness, it is "`deployedPick` finds a stack with `M3Holds`". -/
theorem listBinding_deployed_kSF_one {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (st : (leanIsaInstance F prog s).Stmt × ∀ i, NoOracle i) (k : Fin _) (hk : k.val = 1)
    (tr : (listBindingSpec (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).Transcript k)
    (w : (listBinding_deployed F prog s hs ρ hρ).witMid k) :
    ((listBinding_deployed F prog s hs ρ hρ).kSF init impl).toFun k st tr w ↔
      (deployedPick (leanIsaInstance F prog s) (admissible_of_sizes hs hρ) st.1
        (headWord (admissible_of_sizes hs hρ) (committedWord tr (by omega)))).isSome :=
  (listBinding_kSF_one _ _ _ _ _ _ init impl st k hk tr w).trans <| iff_of_eq <|
    congrArg (fun o ↦ o.isSome = true)
      (leanIsa_commitPick_eq F prog s hs ρ hρ st.1 (committedWord tr (by omega)))

/-- **The stack extracted at leanVM is the pick**: whenever `deployedPick` finds a stack with
`M3Holds` in the committed word's list, the extractor of `listBinding_deployed` returns it. -/
theorem listBinding_deployed_extractedStack_eq
    (st : (leanIsaInstance F prog s).Stmt × ∀ i, NoOracle i)
    (tr : (listBindingSpec (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).FullTranscript)
    (q : Column (leanIsaInstance F prog s).μ)
    (hq : deployedPick (leanIsaInstance F prog s) (admissible_of_sizes hs hρ) st.1
      (headWord (admissible_of_sizes hs hρ) (committedWord (k := Fin.last _) tr (by simp))) =
        some q) :
    Extractor.RoundByRound.extractIn (listBinding_deployed F prog s hs ρ hρ).extractor st tr () =
      q :=
  listBinding_extractedStack_eq _ _ _ _ _ _ st tr q
    ((leanIsa_commitPick_eq F prog s hs ρ hρ st.1
      (committedWord (k := Fin.last _) tr (by simp))).trans hq)

end Deployed

end

end LeanerVM.Protocol
