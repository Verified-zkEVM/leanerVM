/-
  LeanerVM.Protocol.Piop

  leanVM's oracle protocol: the commitment, then the bus phase, the table sumcheck, the
  public-input phase, the Flock phase and the opening, with their completeness and their
  round-by-round knowledge soundness, and the two master theorems at every instance.
-/

module

public import LeanerVM.Protocol.BusSecurity
public import LeanerVM.Protocol.Flock
public import LeanerVM.Protocol.Opening
public import LeanerVM.Protocol.PublicInput
public import LeanerVM.Protocol.Spine.Compose
public import LeanerVM.Protocol.TableSumcheck

/-!
# The oracle protocol

The specification's unrolled protocol (§8, `doc/leanvm/body/08-end-to-end-protocol.tex` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) after the commitment is five phases, each a typed
front component from one seam to the next: the bus phase (`busPhaseT`), the table sumcheck
(`tableSumcheckT`), the public-input phase (`PublicInput.phaseT`, the deployed verifiers' since
they compute every limb's claim themselves), the Flock phase (`flockPhaseT`) and the opening's
batching (`openingT`), after which the protocol asks the stack the batched claim.
`leanVmPhases` fills the spine's five slots with them, `leanVmComplete` and `leanVmSecurity` fill
the two bundles with their halves, and the spine's master theorems give the protocol's:

* `leanVm_perfectCompleteness`: on every statement and stack with `M3Holds`, the honest prover
  convinces the verifier with probability one;
* `leanVm_knowledgeSoundness`: round-by-round knowledge soundness at `piopErrors I`, with the
  composed extractor, whose stack is the committed message (`piopExtractedStack_eq`).

Two side conditions of the instance, which the adaptor is to prove of the leanISA instance: the
bus phase's (`Bus.Conditions`: the count columns' degree, the zerocheck point covering every
constrained table, and the two other sides fitting in the push side's depth) and the degree bound
`I.d ≤ 2` of the table sumcheck. No further hypothesis: the Flock phase holds for every circuit,
and the empty component stands in for it on an instance with no Flock region.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec

@[expose] public section

section Phases

variable (I : M3Instance) (h : Bus.Conditions I)

/-- leanVM's five phases after the commitment, as typed front components. -/
def leanVmPhases : Phases I where
  bus := busPhaseT I h
  table := TableSumcheck.tableSumcheckT I
  pub := PublicInput.phaseT I
  flock := flockPhaseT I
  opening := openingT I

/-- Their typed completeness halves. -/
theorem leanVmComplete (hd : I.d ≤ 2) : (leanVmPhases I h).Complete where
  bus := busCompleteT I h
  table := TableSumcheck.tableSumcheckCompleteT I hd
  pub := PublicInput.completeT I
  flock := flockCompleteT I
  opening := openingCompleteT I

/-- Their typed knowledge-soundness halves, each at its slot's errors. -/
def leanVmSecurity (hd : I.d ≤ 2) : (leanVmPhases I h).Security where
  bus := busSecurityT I h
  table := TableSumcheck.tableSumcheckSecurityT I hd
  pub := PublicInput.securityT I
  flock := flockSecurityT I
  opening := openingSecurityT I

end Phases

/-- **Perfect completeness of leanVM's oracle protocol**, typed: on every statement and stack with
`M3Holds`, the honest prover convinces the verifier with probability one. -/
theorem leanVm_perfectCompleteness (I : M3Instance) (h : Bus.Conditions I) (hd : I.d ≤ 2)
    (initial : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (input : I.Stmt)
    (q : Column I.μ) (hq : ((input, fun i ↦ i.elim0), q) ∈ M3Rel I) :
    Pr{let x ← (leanVmPiop (leanVmPhases I h) initial).execute impl input q}[x.2.2 = some ()] =
      1 :=
  piop_perfectCompleteness _ (leanVmComplete I h hd) initial impl input q hq

/-- **Round-by-round knowledge soundness of leanVM's oracle protocol**, typed, at `piopErrors I`,
with the composed extractor: a knowledge certificate from `M3Holds` whose challenges the verifier
draws, each turning the extractor's state from false to true with probability at most its slot's
error. -/
theorem leanVm_knowledgeSoundness (I : M3Instance) (h : Bus.Conditions I) (hd : I.d ≤ 2)
    (initial : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (s : I.Stmt) :
    ∃ cert : Interaction.Oracle.Security.KnowledgeCertificate (piopSlot I).tree (piopSlot I).roles
        ⟨Column I.μ, M3Holds I s⟩,
      cert.extractor = piopExtractor _ (leanVmSecurity I h hd) s ∧
      cert.challenges = Typed.schedule (piopSlot I).tree (piopSlot I).roles (piopSlot I).samplers
        (piopErrors I) ∧
      Interaction.Oracle.Security.SamplesChallenges unifSpec (QueryImpl.id' unifSpec)
        (piopSlot I).tree (piopSlot I).roles (piopSlot I).oracles initial impl _
        (leanVmVerifier (leanVmPhases I h) initial s) cert.challenges :=
  piop_knowledgeSoundness _ (leanVmSecurity I h hd) initial impl s

end
end LeanerVM.Protocol
