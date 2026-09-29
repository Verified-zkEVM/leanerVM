import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput

/-! Probe D6, expected to fail: without `noncomputable`, Lean refuses the extractor that
chooses a witness, and refuses a definition built on the public-input phase's definition (which
holds a real number). -/

open OracleComp OracleSpec ProtocolSpec LeanerVM.Protocol

namespace Probe

def chooser' (R : Set (Bool × ℕ)) :
    Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) Bool ℕ Unit !p[] (fun _ => ℕ) where
  eqIn := rfl
  extractMid := fun i => i.elim0
  extractOut := fun s _ _ => open Classical in if h : ∃ w, (s, w) ∈ R then h.choose else 0

/-- The verifier of the public-input phase, reached through the phase's definition. -/
def publicInputVerifierThroughPhase (I : M3Instance) := (publicInputPhase I).red.verifier

/-- The same verifier, reached directly. -/
def publicInputVerifierDirect (I : M3Instance) := PublicInput.verifier I

/-- The shape of `piopExtractor`: the extractor of a security bundle, with the phase's definition
as an explicit argument. -/
def extractorOf {I : M3Instance} {A B : Type} (D : Phase.Def I A B)
    {relIn : Set ((A × ∀ i, TheOracle I i) × Unit)} {relOut : Set ((B × ∀ i, TheOracle I i) × Unit)}
    (S : Phase.Security I D relIn relOut) := S.extractor

/-- Applied to the public-input phase: rejected, although the extractor itself is compiled. -/
def publicInputExtractorThroughPhase (I : M3Instance) :=
  extractorOf (publicInputPhase I) (publicInputSecurity I)

end Probe
