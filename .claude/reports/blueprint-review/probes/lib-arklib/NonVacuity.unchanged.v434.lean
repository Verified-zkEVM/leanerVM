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
