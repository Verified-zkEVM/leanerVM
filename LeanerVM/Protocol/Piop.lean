/-
  LeanerVM.Protocol.Piop

  leanVM's oracle protocol: the commitment, then the bus phase, the table sumcheck, the deployed
  public-input check, the Flock phase and the opening, with their completeness and their
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
`a386121f84292f6fa663aaa3e570c15bc0240ea2`) after the commitment is five phases, each a reduction
from one seam to the next: the bus phase (`busPhase`), the table sumcheck (`tableSumcheck`), the
public-input check of the deployed verifiers (`deployedPublicInputPhase`), the Flock phase
(`flockPhase`) and the opening (`openingPhase`). `leanVmPhases` fills the spine's five slots with
them, `leanVmComplete` and `leanVmSecurity` fill the two bundles with their halves, and the
spine's master theorems give the protocol's:

* `leanVm_perfectCompleteness`: on every statement and stack with `M3Holds`, the honest prover
  convinces the verifier with probability one;
* `leanVm_rbrKnowledgeSoundness`: round-by-round knowledge soundness at `piopError I`, with the
  composed extractor, whose stack is the committed message.

Two side conditions of the instance, which the adaptor is to prove of the leanISA instance: the
bus phase's
(`Bus.Conditions`: the count columns' degree, the zerocheck point covering every constrained
table, and the two other sides fitting in the push side's depth) and the degree bound `I.d ≤ 2`
of the table sumcheck. No further hypothesis: the Flock phase holds for every circuit, and the
pass-through stands in for it on an instance with no Flock region.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

section Phases

variable (I : M3Instance) (h : Bus.Conditions I) (hd : I.d ≤ 2)

/-- leanVM's five phases after the commitment. -/
def leanVmPhases : Phases I where
  bus := busPhase I h
  table := TableSumcheck.tableSumcheck I
  pub := deployedPublicInputPhase I
  flock := flockPhase I
  opening := openingPhase I

/-- Their completeness halves. -/
def leanVmComplete : (leanVmPhases I h).Complete where
  bus := busComplete I h
  table := TableSumcheck.tableSumcheckComplete I hd
  pub := deployedPublicInputComplete I
  flock := flockComplete I
  opening := openingComplete I

/-- Their knowledge-soundness halves, each at its slot's error. -/
def leanVmSecurity : (leanVmPhases I h).Security where
  bus := busSecurity I h
  table := TableSumcheck.tableSumcheckSecurity I hd
  pub := deployedPublicInputSecurity I
  flock := flockSecurity I
  opening := openingSecurity I

end Phases

/-- **Perfect completeness of leanVM's oracle protocol**: on every statement and stack with
`M3Holds`, the honest prover convinces the verifier with probability one. -/
theorem leanVm_perfectCompleteness (I : M3Instance) (h : Bus.Conditions I) (hd : I.d ≤ 2)
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop (leanVmPhases I h)).perfectCompleteness init impl (M3Rel I) (Seam.done I) :=
  piop_perfectCompleteness _ (leanVmComplete I h hd) init impl

/-- **Round-by-round knowledge soundness of leanVM's oracle protocol** at `piopError I`, with the
composed extractor and knowledge state function: each challenge turns the state from false to
true with probability at most its slot's error. -/
theorem leanVm_rbrKnowledgeSoundness (I : M3Instance) (h : Bus.Conditions I) (hd : I.d ≤ 2)
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier (leanVmPhases I h)).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (M3Rel I) (Seam.done I) (leanVmSecurity I h hd).extraction.witMid
      (piopExtractor _ (leanVmSecurity I h hd))
      ((leanVmSecurity I h hd).extraction.kSF init impl) (piopError I) :=
  piop_rbrKnowledgeSoundness _ (leanVmSecurity I h hd) init impl

end
end LeanerVM.Protocol
