import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput
import LeanerVM.Protocol.Spine.Toy

/-! Probe D6: what makes an `Extractor.RoundByRound` an algorithm, and the check applied to the
three extractors of leanerVM. ArkLib at the pin `dca90385`, leanerVM at `b435631`. -/

open OracleComp OracleSpec ProtocolSpec LeanerVM.Protocol LeanerVM.Parameters
open scoped NNReal

namespace Probe

/-! ## 1. ArkLib's extractor type accepts a classical choice of witness

A relation `R` on a bit and a natural number, a verifier with no round that accepts the statements
of a decidable language `L`, and the hypothesis that `L` is the language of `R`. The extractor
below *chooses* a witness. It is round-by-round knowledge sound at error zero, for every `R`. -/

variable (R : Set (Bool × ℕ)) (L : Bool → Bool) (hL : ∀ s, L s = true ↔ ∃ w, (s, w) ∈ R)

noncomputable def chooser :
    Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) Bool ℕ Unit !p[] (fun _ => ℕ) where
  eqIn := rfl
  extractMid := fun i => i.elim0
  extractOut := fun s _ _ => open Classical in if h : ∃ w, (s, w) ∈ R then h.choose else 0

def decideLanguage : Verifier []ₒ Bool Unit !p[] where
  verify := fun s _ => if L s then pure () else failure

def decideLanguage_guarded : (decideLanguage L).GuardedForm where
  check := fun s _ => L s
  out := fun _ _ => ()
  verify_eq := fun s tr => by simp [decideLanguage]

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

include hL in
theorem chooser_valid (s : Bool) (tr : (!p[]).FullTranscript) (hs : L s = true) :
    (s, (chooser R).extractOut s tr ()) ∈ R := by
  have h : ∃ w, (s, w) ∈ R := (hL s).mp hs
  simp only [chooser, h, dite_true]
  exact h.choose_spec

noncomputable def chooser_stateFunction :
    (decideLanguage L).KnowledgeStateFunction init impl R (Set.univ : Set (Unit × Unit))
      (chooser R) where
  toFun := fun _ s _ w => (s, w) ∈ R
  toFun_empty := fun _ _ => Iff.rfl
  toFun_next := fun i => i.elim0
  toFun_full := fun s tr _ h =>
    chooser_valid R L hL s tr
      (Verifier.GuardedForm.of_probEvent_pos (decideLanguage_guarded L) init impl s tr _ h).1

/-- Knowledge soundness at error zero with an extractor that computes nothing. -/
theorem chooser_sound :
    (decideLanguage L).rbrKnowledgeSoundnessWorstCaseWith init impl R Set.univ (fun _ => ℕ)
      (chooser R) (chooser_stateFunction R L hL init impl) (fun _ => 0) :=
  fun _ i => i.1.elim0

/-! ## 2. The three extractors of leanerVM are compiled definitions

Each `def` below has no `noncomputable`: Lean compiles it, so the extractor it names has code.
(The same line on `chooser` is rejected: see `ExtractorsExpectedFailure.lean`.) -/

def commitExtractorCode (I : M3Instance) := commitExtractor I
def publicInputExtractorCode (I : M3Instance) := PublicInput.extractor I
def piopExtractorCode {I : M3Instance} (P : Phases I) (S : P.Security) := piopExtractor P S
def commitSecurityExtractorCode (I : M3Instance) := (commitSecurity I).extractor
def publicInputSecurityExtractorCode (I : M3Instance) := (publicInputSecurity I).extractor

/-- The composition of two extractors is compiled too. -/
def appendedExtractorCode {I : M3Instance} {D : Phase.Def I I.Stmt (I.Stmt × BusOut I)}
    (S : Phase.Security I D (Seam.commit I) (Seam.bus I)) :=
  ((commitSecurity I).append S).extractor

/-! ## 3. They run: the commit extractor returns the stack that was sent -/

open Toy in
/-- A transcript of the commit phase: the honest stack of the toy instance. -/
def commitTranscript : (commitSpec toy).FullTranscript := fun | ⟨0, _⟩ => honest

open Toy in
#eval ((commitExtractor toy).extractOut ((1 : K), fun i => i.elim0) commitTranscript ()).values.toList
  == honest.values.toList

open Toy in
#eval ((commitSecurity toy).extractor.extractMid (⟨0, Nat.zero_lt_one⟩ : Fin 1)
  ((1 : K), fun i => i.elim0) commitTranscript honest).values.toList == honest.values.toList

open Toy in
#eval (PublicInput.extractor toy).extractOut
  ((((1 : K), (⟨[]⟩ : TableOut toy)), fun _ => honest)) (fun | ⟨0, _⟩ => (0 : E) | ⟨1, _⟩ => ([] : List E)) ()

end Probe

#print axioms Probe.chooser_sound
