import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.ToArkLib.GuardedVerdict
import LeanerVM.Protocol.ToArkLib.KeepOracles

/-!
Probe P4 (code-spine): `Phases.Security` of the toy instance is inhabited by five phases that
check nothing, each with one wasted challenge whose declared error is `1`.

A phase `wasted f ε`: the verifier draws one challenge in `E`, ignores it, and maps the
statement by `f`. It is complete whenever `f` carries the input seam into the output seam
(the pass-through's completeness). With declared error `ε = 1` it is round-by-round knowledge
sound for *any* two seams: the state is the input seam before the challenge and `True` after
it, and a probability is at most `1`.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp
  OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Probe

variable (I : M3Instance) {StmtIn StmtOut : Type}

/-- One round: a challenge in `E`. -/
@[reducible]
def wSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[E]⟩

instance : ∀ i, OracleInterface (wSpec.Message i)
  | ⟨0, h⟩ => nomatch h

instance : ∀ i, SampleableType (wSpec.Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType E)

/-- The prover receives the challenge and outputs the mapped statement. -/
def wProver (f : StmtIn → StmtOut) :
    OracleProver []ₒ StmtIn (TheOracle I) Unit StmtOut (TheOracle I) Unit wSpec where
  PrvState := fun _ ↦ (StmtIn × ∀ i, TheOracle I i) × Unit
  input := _root_.id
  receiveChallenge
    | ⟨0, _⟩ => fun st ↦ pure fun _ ↦ st
  sendMessage
    | ⟨0, h⟩ => nomatch h
  output := fun st ↦ pure ((f st.1.1, st.1.2), ())

/-- The verifier ignores the challenge, queries nothing and maps the statement. -/
def wVerifier (f : StmtIn → StmtOut) :
    OracleVerifier []ₒ StmtIn (TheOracle I) StmtOut (TheOracle I) wSpec where
  verify := fun s _ ↦ pure (f s)
  outputOracle := .inl (keepOracles (TheOracle I) wSpec)

theorem wVerifier_run (f : StmtIn → StmtOut) (s : StmtIn) (o : ∀ i, TheOracle I i)
    (tr : wSpec.FullTranscript) :
    (wVerifier I f).toVerifier.run (s, o) tr = pure (f s, o) := by
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [OracleVerifier.materializeOutput_of_keepOracles _ rfl]
  rfl

/-- The verifier accepts every transcript. -/
def wPure (f : StmtIn → StmtOut) : (wVerifier I f).toVerifier.PureForm where
  verify := fun p _ ↦ (f p.1, p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ wVerifier_run I f s o tr

/-- The phase, with a declared error `ε` on its one challenge. -/
noncomputable def wasted (f : StmtIn → StmtOut) (ε : ℝ≥0) : Phase.Def I StmtIn StmtOut where
  n := 1
  pSpec := wSpec
  red := ⟨wProver I f, wVerifier I f⟩
  err := fun _ ↦ ε

theorem wProver_run_support (f : StmtIn → StmtOut) (s : StmtIn) (o : ∀ i, TheOracle I i)
    (pr : wSpec.FullTranscript × (StmtOut × ∀ i, TheOracle I i) × Unit)
    (hpr : pr ∈ support ((wProver I f).run (s, o) ())) : pr.2 = ((f s, o), ()) := by
  have h0 : wSpec.dir 0 = .V_to_P := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_one,
    Prover.processRound_of_dir_eq_V_to_P 0 h0] at hpr
  simp only [ChallengeIdx, Challenge, wProver, id_eq, liftM_pure, bind_pure_comp, map_pure,
    pure_bind, Functor.map_map, support_map, Set.mem_image] at hpr
  obtain ⟨r, -, rfl⟩ := hpr
  rfl

variable {relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit)}
  {relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)}

/-- Completeness, under the pass-through's hypothesis. -/
noncomputable def wastedComplete (f : StmtIn → StmtOut) (ε : ℝ≥0)
    (hc : ∀ s o, ((s, o), ()) ∈ relIn → ((f s, o), ()) ∈ relOut) :
    Phase.Complete I (wasted I f ε) relIn relOut where
  outputPure := ⟨_, fun _ ↦ rfl⟩
  guarded := (wPure I f).toGuardedForm
  complete := fun init impl ↦ by
    apply Reduction.perfectCompleteness_of_run_support
    intro stmtIn witIn hIn x hx
    obtain ⟨s, o⟩ := stmtIn
    obtain ⟨pr, hpr, rfl⟩ :=
      Reduction.mem_support_run_of_guarded _ (wPure I f).toGuardedForm (s, o) witIn hx
    have hout := wProver_run_support I f s o pr hpr
    have hc' : (wPure I f).toGuardedForm.check (s, o) pr.1 = true := rfl
    rw [if_pos hc']
    refine ⟨_, rfl, ?_, congrArg Prod.fst hout⟩
    have hw : pr.2.2 = () := rfl
    exact hw ▸ hc s o hIn

/-- The extractor keeps the trivial witness. -/
def wExtractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
    (StmtIn × ∀ i, TheOracle I i) Unit Unit wSpec (fun _ ↦ Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ _ ↦ ()
  extractOut := fun _ _ _ ↦ ()

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- A knowledge state function for ANY two seams: the input seam before the challenge, `True`
after it. No hypothesis on `f`, `relIn`, `relOut`. -/
def wState (f : StmtIn → StmtOut) :
    (wVerifier I f).toVerifier.KnowledgeStateFunction init impl relIn relOut
      (wExtractor I (StmtIn := StmtIn)) where
  toFun := fun m stmt _ _ ↦ if m.val = 0 then (stmt, ()) ∈ relIn else True
  toFun_empty := fun _ _ ↦ by simp
  toFun_next := fun m hm ↦ by
    fin_cases m
    exact absurd hm (by decide)
  toFun_full := fun _ _ _ _ ↦ by simp

/-- Round-by-round knowledge soundness at declared error `1`: a probability is at most one. -/
theorem w_rbr (f : StmtIn → StmtOut) :
    (wVerifier I f).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut
      (fun _ ↦ Unit) (wExtractor I) (wState I init impl f) (fun _ ↦ 1) := by
  intro stmtIn i tr
  simp

/-- The security half at declared error `1`, under the completeness hypothesis alone. -/
noncomputable def wastedSecurity (f : StmtIn → StmtOut)
    (hc : ∀ s o, ((s, o), ()) ∈ relIn → ((f s, o), ()) ∈ relOut) :
    Phase.Security I (wasted I f 1) relIn relOut where
  toComplete := wastedComplete I f 1 hc
  witMid := fun _ ↦ Unit
  extractor := wExtractor I
  kSF := fun init impl ↦ wState I init impl f
  rbr := fun init impl ↦ w_rbr I init impl f

/-! ## The toy's five phases, checking nothing -/

/-- Five phases that draw a challenge and drop every claim. -/
noncomputable def junkPhases : Phases toy where
  bus := wasted toy (fun s ↦ (s, ⟨[], []⟩)) 1
  table := wasted toy (fun p ↦ (p.1, ⟨[]⟩)) 1
  pub := wasted toy (fun p ↦ (p.1, ⟨[]⟩)) 1
  flock := wasted toy (fun p ↦ (p.1, ⟨[], []⟩)) 1
  opening := wasted toy (fun _ ↦ ()) 1

/-- `Phases.Security` of the toy is inhabited by them. -/
noncomputable def junkSecurity : junkPhases.Security where
  bus := wastedSecurity toy _ fun _ _ h ↦ ⟨by simp, by simp, by simp, h.2.2.2.1, h.2.2.2.2⟩
  table := wastedSecurity toy _ fun _ _ h ↦ ⟨by simp, h.2.2.2.1, h.2.2.2.2⟩
  pub := wastedSecurity toy _ fun _ _ h ↦ ⟨by simp, h.2.2⟩
  flock := wastedSecurity toy _ fun _ _ _ ↦ ⟨by simp, by simp⟩
  opening := wastedSecurity toy _ fun _ _ _ ↦ trivial

example : junkPhases.toDef.n = 6 := rfl

/-- Their completeness halves. -/
noncomputable def junkComplete : junkPhases.Complete :=
  ⟨junkSecurity.bus.toComplete, junkSecurity.table.toComplete, junkSecurity.pub.toComplete,
    junkSecurity.flock.toComplete, junkSecurity.opening.toComplete⟩

/-- Both master theorems hold of the junk protocol. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop junkPhases).perfectCompleteness init impl (M3Rel toy) (Seam.done toy) :=
  piop_perfectCompleteness junkPhases junkComplete init impl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier junkPhases).toVerifier.rbrKnowledgeSoundnessWorstCase init impl (M3Rel toy)
      (Seam.done toy) (piopError junkPhases) :=
  piop_rbrKnowledgeSoundness_exists junkPhases junkSecurity init impl

/-- Appending keeps a constant declared error. -/
theorem append_err_const {S₁ S₂ S₃ W₁ W₂ W₃ : Type} {ι₁ ι₂ ι₃ : Type} {O₁ : ι₁ → Type}
    {O₂ : ι₂ → Type} {O₃ : ι₃ → Type} [∀ i, OracleInterface (O₁ i)]
    [∀ i, OracleInterface (O₂ i)] [∀ i, OracleInterface (O₃ i)]
    (D₁ : Component.Def S₁ O₁ W₁ S₂ O₂ W₂) (D₂ : Component.Def S₂ O₂ W₂ S₃ O₃ W₃) (c : ℝ≥0)
    (h₁ : ∀ i, D₁.err i = c) (h₂ : ∀ i, D₂.err i = c) : ∀ i, (D₁.append D₂).err i = c := by
  intro i
  change Sum.elim D₁.err D₂.err (ChallengeIdx.sumEquiv.symm i) = c
  cases ChallengeIdx.sumEquiv.symm i with
  | inl a => exact h₁ a
  | inr b => exact h₂ b

/-- Every challenge of the junk protocol carries the declared error `1`. -/
theorem piopError_junk (i : junkPhases.toDef.pSpec.ChallengeIdx) : piopError junkPhases i = 1 := by
  unfold piopError Phases.toDef
  refine append_err_const _ _ 1 (append_err_const _ _ 1 (append_err_const _ _ 1
    (append_err_const _ _ 1 (append_err_const _ _ 1 ?_ ?_) ?_) ?_) ?_) ?_ i
  · rintro ⟨j, hj⟩
    fin_cases j
    exact absurd hj (by decide)
  all_goals intro _; rfl

#print axioms junkSecurity
#print axioms piopError_junk

end Probe
