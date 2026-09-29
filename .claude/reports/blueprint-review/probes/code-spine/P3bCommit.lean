import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput

/-!
Probe P3b (code-spine): each seam on the toy instance, an inhabitant and near misses; the
zerocheck escape; the commit phase's state function and extractor; the type of the composed
extractor's output when a phase has rounds.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp

namespace Probe

/-! ## The commit phase: state function and extractor -/

section Commit

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

-- Before the message: `M3Holds` of the candidate witness.
example (s : K) (o : ∀ i, NoOracle i) (w : Column 3) :
    ((commitSecurity toy).kSF init impl).toFun 0 (s, o) default w ↔ M3Holds toy s w := Iff.rfl

-- After the message: `M3Holds` of the message, whatever the candidate witness.
example (s : K) (o : ∀ i, NoOracle i) (tr : (commitSpec toy).FullTranscript) (w : Column 3) :
    ((commitSecurity toy).kSF init impl).toFun (Fin.last 1) (s, o) tr w ↔
      M3Holds toy s (tr 0) := Iff.rfl

-- The extractor: both maps return the message.
example (s : K) (o : ∀ i, NoOracle i) (tr : (commitSpec toy).FullTranscript) :
    (commitExtractor toy).extractOut (s, o) tr () = tr 0 := rfl
example (s : K) (o : ∀ i, NoOracle i) (tr : (commitSpec toy).FullTranscript) (w : Column 3) :
    (commitExtractor toy).extractMid 0 (s, o) tr w = tr 0 := rfl

-- The commit phase's security is the one the composition starts from.
example : (commitSecurity toy).extractor = commitExtractor toy := rfl
example : (commitDef toy).n = 1 := rfl

end Commit

end Probe
