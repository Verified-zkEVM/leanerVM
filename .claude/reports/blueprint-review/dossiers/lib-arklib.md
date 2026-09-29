# Dossier `lib-arklib`: ArkLib's framework for interactive oracle reductions at the pin

Reviewed: ArkLib at the pin `dca90385` (sources read in `.lake/packages/Arklib/`), leanerVM `main`
at `b435631`, ArkLib `origin/main` at `7653a901e` (fetched 2026-09-29, 347 commits after the pin),
ArkLib pull request #615 at its head `ca7a2577`. Every Lean statement below is copied from the
file named with it. Every probe is reproduced in the appendix with its command and its output.

**PRELIMINARY VERSION, being extended section by section. The summary is rewritten last.**

## Results established so far (evidence in the sections and the appendix)

1. leanerVM's master theorems and everything they are built from depend on the three standard
   axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx` (probe `AxiomsLeanerVM`).
2. ArkLib at the pin admits the composition of soundness, knowledge soundness and both
   round-by-round notions (`Verifier.append_*`, `Verifier.seqCompose_*`), and the implications
   from round-by-round knowledge soundness to plain knowledge soundness and soundness
   (`#print axioms` shows `sorryAx`; probe `AxiomsArkLibBuilt`; source `Security/Implications.lean`).
   They are still admitted on `origin/main`.
3. The local file `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean` is the file of pull request
   #615 at `ca7a2577` up to the header, the module keywords, a namespace, added docstrings, two
   lemmas replaced by references to ArkLib's own, two names qualified, and the omission of the
   four wrapper theorems. Pull request #615 is open, not merged, and in conflict with `main`.
4. The notion is not vacuous: a verifier that accepts everything has no knowledge state
   function (no round), and is not knowledge sound at error 0 (one challenge), whatever the
   extractor; it is knowledge sound at error 1, as every verifier is (probe `NonVacuity`).
5. ArkLib's extractor type accepts an extractor that chooses a witness by classical choice, and
   such an extractor is "knowledge sound at error 0" for every relation whose language the
   verifier decides (probe `Extractors`): the existential form of the notion is soundness, not
   knowledge. The named form is meaningful only if the named extractor is read.
6. The three extractors of leanerVM are compiled definitions and run (probe `Extractors`).
7. `Component.Def` carries the real-valued error, so every phase definition with a challenge is
   `noncomputable`, and neither the verifier nor the extractor can be compiled when reached
   through the phase definition (probe `ExtractorsExpectedFailure`).

## Appendix: probes

All probes were run from the root of leanerVM (`main` at `b435631`) with
`flock .claude/reports/blueprint-review/logs/lean.lock lake env lean <file>`.

### Probe `AxiomsLeanerVM`

File `.claude/reports/blueprint-review/probes/lib-arklib/AxiomsLeanerVM.lean`:

```lean
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput

/-! Probe B1: `#print axioms` of leanerVM's master theorems, phases and composition. -/

open LeanerVM.Protocol

#print axioms LeanerVM.Protocol.piop_perfectCompleteness
#print axioms LeanerVM.Protocol.piop_rbrKnowledgeSoundness
#print axioms LeanerVM.Protocol.piop_rbrKnowledgeSoundness_exists
#print axioms LeanerVM.Protocol.commitSecurity
#print axioms LeanerVM.Protocol.commitComplete
#print axioms LeanerVM.Protocol.publicInputSecurity
#print axioms LeanerVM.Protocol.publicInputComplete
#print axioms LeanerVM.Protocol.Component.Security.append
#print axioms LeanerVM.Protocol.Component.Complete.append
#print axioms LeanerVM.Protocol.Verifier.KnowledgeStateFunction.appendGuarded
#print axioms LeanerVM.Protocol.Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
#print axioms LeanerVM.Protocol.piopExtractor
#print axioms LeanerVM.Protocol.commitExtractor
#print axioms LeanerVM.Protocol.PublicInput.extractor
#print axioms LeanerVM.Protocol.Component.sendExtractor
#print axioms LeanerVM.Protocol.Phases.Security.toDef
#print axioms LeanerVM.Protocol.Phases.Complete.toDef
```

### Probe `AxiomsArkLibBuilt`

File `.claude/reports/blueprint-review/probes/lib-arklib/AxiomsArkLibBuilt.lean`:

```lean
import LeanerVM.Protocol.Spine.Compose
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.GuardedNary
import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
import ArkLib.OracleReduction.Composition.Sequential.Append.RoundByRound
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-! Probe B2: `#print axioms` of the ArkLib declarations the blueprint cites, for the modules
that leanerVM's build contains (ArkLib at the pin `dca90385`). -/

-- definitions
#print axioms Reduction.completeness
#print axioms Reduction.perfectCompleteness
#print axioms OracleReduction.perfectCompleteness
#print axioms Verifier.soundness
#print axioms Verifier.knowledgeSoundness
#print axioms Extractor.Straightline
#print axioms Verifier.StateFunction
#print axioms Verifier.KnowledgeStateFunction
#print axioms Extractor.RoundByRound
#print axioms Verifier.rbrSoundness
#print axioms Verifier.rbrKnowledgeSoundness
#print axioms Verifier.rbrKnowledgeSoundnessWorstCase
#print axioms Verifier.rbrKnowledgeSoundnessWorstCaseWith
#print axioms Verifier.GuardedForm
#print axioms Prover.OutputIsPure
#print axioms OracleVerifier.toVerifier
#print axioms OracleReduction.append
#print axioms OracleReduction.seqCompose
#print axioms ProtocolSpec.seqCompose
#print axioms Extractor.RoundByRound.append
#print axioms Verifier.StateFunction.append
#print axioms Verifier.GuardedForm.append
-- proved theorems
#print axioms Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
#print axioms Verifier.rbrSoundnessWorstCase_implies_rbrSoundness
#print axioms Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith
#print axioms ProtocolSpec.probEvent_simulateQ_addLift_getChallenge_bind_le
#print axioms Reduction.perfectCompleteness_of_run_support
#print axioms OracleReduction.append_perfectCompleteness_of_pure_verifiers
#print axioms OracleReduction.append_perfectCompleteness_of_guarded_verifiers
#print axioms OracleReduction.append_completeness_of_guarded_verifiers
#print axioms OracleReduction.seqCompose_completeness_of_guarded_verifiers
#print axioms OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers
#print axioms Reduction.seqCompose_completeness_of_guarded_verifiers
#print axioms Reduction.append_completeness_of_guarded_verifiers
#print axioms Reduction.append_completeness_of_guarded_prover_factorization
#print axioms Verifier.append_rbrSoundnessWorstCase_of_pure_first
#print axioms Prover.OutputIsPure.append
#print axioms OracleVerifier.append_toVerifier
#print axioms MvPolynomial.schwartz_zippel_counting
#print axioms prob_eval_zero_le_div
#print axioms MvPolynomial.prob_eval_zero_le_div
-- admitted at the pin
#print axioms Verifier.append_soundness
#print axioms Verifier.append_knowledgeSoundness
#print axioms Verifier.append_rbrSoundness
#print axioms Verifier.append_rbrKnowledgeSoundness
#print axioms OracleVerifier.append_rbrKnowledgeSoundness
#print axioms Verifier.seqCompose_soundness
#print axioms Verifier.seqCompose_knowledgeSoundness
#print axioms Verifier.seqCompose_rbrSoundness
#print axioms Verifier.seqCompose_rbrKnowledgeSoundness
#print axioms OracleVerifier.seqCompose_rbrKnowledgeSoundness
#print axioms OracleVerifier.numQueries
```

### Probe `NonVacuity`

File `.claude/reports/blueprint-review/probes/lib-arklib/NonVacuity.lean`:

```lean
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
import LeanerVM.Protocol.ToArkLib.GuardedVerdict

/-! Probe D4: non-vacuity of ArkLib's round-by-round knowledge soundness (pin `dca90385`).

Relation: the statement is a bit, and only `true` has a witness. -/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Probe

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Only the statement `true` has a witness. -/
def relIn : Set (Bool × Unit) := {p | p.1 = true}

/-- The trivial output relation: everything. -/
def relOut : Set (Unit × Unit) := Set.univ

/-! ## (a0) No round: the accept-everything verifier has no knowledge state function at all. -/

/-- The verifier with no round that accepts every statement. -/
def acceptAll0 : Verifier oSpec Bool Unit !p[] where
  verify := fun _ _ => pure ()

theorem acceptAll0_no_stateFunction {W : Fin 1 → Type}
    (E : Extractor.RoundByRound oSpec Bool Unit Unit !p[] W) :
    IsEmpty ((acceptAll0 (oSpec := oSpec)).KnowledgeStateFunction init impl relIn relOut E) := by
  refine ⟨fun K => ?_⟩
  have hacc : Pr[fun t => (t, ()) ∈ relOut | OptionT.mk do
      (simulateQ impl ((acceptAll0 (oSpec := oSpec)).run false default)).run' (← init)] > 0 := by
    have h1 := Verifier.guarded_accepting_of_mem init impl (acceptAll0 (oSpec := oSpec))
      (fun _ _ => true) (fun _ _ => ()) (fun _ _ => by simp [acceptAll0]) false default rfl
      {t | (t, ()) ∈ relOut} (by simp [relOut])
    exact lt_of_lt_of_eq zero_lt_one h1.symm
  have hfull := K.toFun_full false default () hacc
  have hin := (K.toFun_empty false (E.extractOut false default ())).mpr hfull
  simp [relIn] at hin

/-! ## (a1) One challenge: the accept-everything verifier is not knowledge sound at error 0,
whatever the extractor and the state function. -/

/-- One verifier challenge, a bit. -/
@[reducible] def pSpec1 : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Bool]⟩

instance : ∀ i, SampleableType (pSpec1.Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType Bool)

/-- The verifier with one challenge that accepts every statement. -/
def acceptAll1 : Verifier oSpec Bool Unit pSpec1 where
  verify := fun _ _ => pure ()

theorem acceptAll1_full {W : Fin 2 → Type}
    {E : Extractor.RoundByRound oSpec Bool Unit Unit pSpec1 W}
    (K : (acceptAll1 (oSpec := oSpec)).KnowledgeStateFunction init impl relIn relOut E)
    (s : Bool) (tr : pSpec1.FullTranscript) :
    K (Fin.last 1) s tr (E.extractOut s tr ()) := by
  apply K.toFun_full
  have h1 := Verifier.guarded_accepting_of_mem init impl (acceptAll1 (oSpec := oSpec))
    (fun _ _ => true) (fun _ _ => ()) (fun _ _ => by simp [acceptAll1]) s tr rfl
    {t | (t, ()) ∈ relOut} (by simp [relOut])
  exact lt_of_lt_of_eq zero_lt_one h1.symm

theorem acceptAll1_not_sound_at_zero {W : Fin 2 → Type}
    (E : Extractor.RoundByRound oSpec Bool Unit Unit pSpec1 W)
    (K : (acceptAll1 (oSpec := oSpec)).KnowledgeStateFunction init impl relIn relOut E) :
    ¬ (acceptAll1 (oSpec := oSpec)).rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut
      W E K (fun _ => 0) := by
  intro h
  have h0 := h false ⟨0, rfl⟩ (show Transcript (0 : Fin 2) pSpec1 from default)
  simp only [ENNReal.coe_zero, nonpos_iff_eq_zero] at h0
  rw [probEvent_eq_zero_iff] at h0
  refine h0 true (by rw [support_uniformSample]; trivial) ?_
  refine ⟨E.extractOut false _ (), ?_, acceptAll1_full init impl K false _⟩
  intro hk
  have hin := (K.toFun_empty false _).mpr hk
  simp [relIn] at hin

/-- It is knowledge sound at error 1, as every verifier with a challenge is: the error is what
carries the content. -/
def acceptAll1_extractor : Extractor.RoundByRound oSpec Bool Unit Unit pSpec1 (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

def acceptAll1_stateFunction :
    (acceptAll1 (oSpec := oSpec)).KnowledgeStateFunction init impl relIn relOut
      acceptAll1_extractor where
  toFun := fun m s _ _ => if m.val = 0 then s = true else True
  toFun_empty := fun s w => by simp [relIn]
  toFun_next := fun m hm => by
    have : m = 0 := Subsingleton.elim _ _
    subst this
    exact absurd hm (by decide)
  toFun_full := fun s tr w _ => by simp

theorem acceptAll1_sound_at_one :
    (acceptAll1 (oSpec := oSpec)).rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut
      (fun _ => Unit) acceptAll1_extractor (acceptAll1_stateFunction init impl) (fun _ => 1) := by
  intro s i tr
  simp

/-! ## Positive control: the verifier that checks the bit is knowledge sound at error 0. -/

/-- The verifier with one challenge that accepts `true` only. -/
def checkBit : Verifier oSpec Bool Unit pSpec1 where
  verify := fun s _ => if s then pure () else failure

def checkBit_guarded : (checkBit (oSpec := oSpec)).GuardedForm where
  check := fun s _ => s
  out := fun _ _ => ()
  verify_eq := fun s tr => by simp [checkBit]

def checkBit_stateFunction :
    (checkBit (oSpec := oSpec)).KnowledgeStateFunction init impl relIn relOut
      acceptAll1_extractor where
  toFun := fun _ s _ _ => s = true
  toFun_empty := fun s w => by simp [relIn]
  toFun_next := fun m hm => by
    have : m = 0 := Subsingleton.elim _ _
    subst this
    exact absurd hm (by decide)
  toFun_full := fun s tr w h =>
    (LeanerVM.Protocol.Verifier.GuardedForm.of_probEvent_pos checkBit_guarded init impl s tr _ h).1

theorem checkBit_sound_at_zero :
    (checkBit (oSpec := oSpec)).rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut
      (fun _ => Unit) acceptAll1_extractor (checkBit_stateFunction init impl) (fun _ => 0) := by
  intro s i tr
  simp only [ENNReal.coe_zero, nonpos_iff_eq_zero]
  rw [probEvent_eq_zero_iff]
  rintro c - ⟨w, h1, h2⟩
  exact h1 h2

/-! ## (b) A knowledge state function is neither constantly true nor constantly false, as soon
as the relation has a statement with a witness and one without. -/

theorem stateFunction_false_at {S WI T WO : Type} {n : ℕ} {p : ProtocolSpec n}
    {V : Verifier oSpec S T p} {W : Fin (n + 1) → Type} {R : Set (S × WI)} {R' : Set (T × WO)}
    {E : Extractor.RoundByRound oSpec S WI WO p W}
    (K : V.KnowledgeStateFunction init impl R R' E) (s : S) (hs : ∀ w, (s, w) ∉ R)
    (w : W 0) : ¬ K 0 s default w :=
  fun h => hs _ ((K.toFun_empty s w).mpr h)

theorem stateFunction_true_at {S WI T WO : Type} {n : ℕ} {p : ProtocolSpec n}
    {V : Verifier oSpec S T p} {W : Fin (n + 1) → Type} {R : Set (S × WI)} {R' : Set (T × WO)}
    {E : Extractor.RoundByRound oSpec S WI WO p W}
    (K : V.KnowledgeStateFunction init impl R R' E) (s : S) (w : W 0)
    (h : (s, cast E.eqIn w) ∈ R) : K 0 s default w :=
  (K.toFun_empty s w).mp h

/-! ## (c) With the output relation everything, the last law of a knowledge state function of
a guarded verifier says exactly: if the check passes, the state is true at the extracted
witness. -/

theorem full_iff_of_univ {S WI T WO : Type} {n : ℕ} {p : ProtocolSpec n}
    [∀ i, SampleableType (p.Challenge i)] {V : Verifier oSpec S T p} (G : V.GuardedForm) {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec S WI WO p W}
    (F : S → p.FullTranscript → W (Fin.last n) → Prop) :
    (∀ s tr w, Pr[fun t => (t, w) ∈ (Set.univ : Set (T × WO)) | OptionT.mk do
        (simulateQ impl (V.run s tr)).run' (← init)] > 0 → F s tr (E.extractOut s tr w)) ↔
      ∀ s tr w, G.check s tr = true → F s tr (E.extractOut s tr w) := by
  constructor
  · intro h s tr w hc
    apply h
    have h1 := Verifier.guarded_accepting_of_mem init impl V G.check G.out G.verify_eq s tr hc
      {t | (t, w) ∈ (Set.univ : Set (T × WO))} (by simp)
    exact lt_of_lt_of_eq zero_lt_one h1.symm
  · intro h s tr w hp
    exact h s tr w
      (LeanerVM.Protocol.Verifier.GuardedForm.of_probEvent_pos G init impl s tr _ hp).1

end Probe

#print axioms Probe.acceptAll0_no_stateFunction
#print axioms Probe.acceptAll1_not_sound_at_zero
#print axioms Probe.acceptAll1_sound_at_one
#print axioms Probe.checkBit_sound_at_zero
#print axioms Probe.full_iff_of_univ
```

### Probe `Extractors`

File `.claude/reports/blueprint-review/probes/lib-arklib/Extractors.lean`:

```lean
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
```

### Probe `ExtractorsExpectedFailure`

File `.claude/reports/blueprint-review/probes/lib-arklib/ExtractorsExpectedFailure.lean`:

```lean
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
```
