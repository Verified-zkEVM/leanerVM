# The phase with an arbitrary message and an arbitrary check the message passes; the lines' values pooled.
exec(open('.claude/reports/blueprint-review/probes/code-pubinput/tools/lib.py').read())
EDITS = []
TAIL = OPEN + """
/-! ## Any message, any check the message passes -/

variable (I : M3Instance)
  (msg : I.Stmt → E → List E)
  (chk : (I.Stmt × TableOut I) → E → List E → Bool)

/-- The prover sends `msg`. -/
def proverG : OracleProver []ₒ (I.Stmt × TableOut I) (TheOracle I) Unit
    (I.Stmt × PubOut I) (TheOracle I) Unit pSpec where
  PrvState
    | ⟨0, _⟩ => ((I.Stmt × TableOut I) × ∀ i, TheOracle I i) × Unit
    | _ => E × (((I.Stmt × TableOut I) × ∀ i, TheOracle I i) × Unit)
  input := _root_.id
  receiveChallenge
    | ⟨0, _⟩ => fun st ↦ pure fun r ↦ (r, st)
    | ⟨1, h⟩ => nomatch h
  sendMessage
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st ↦ pure (msg st.2.1.1.1 st.1, st)
  output := fun st ↦ pure ((pooled I st.2.1.1 st.1, st.2.1.2), ())

/-- The verifier checks `chk` and pools the lines' values. -/
def verifierG : OracleVerifier []ₒ (I.Stmt × TableOut I) (TheOracle I)
    (I.Stmt × PubOut I) (TheOracle I) pSpec where
  verify := fun s chals ↦ do
    let cs ← liftM queryValues
    if chk s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
  outputOracle := .inl (keepOracles (TheOracle I) pSpec)

theorem verifierG_verify (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (tr : pSpec.FullTranscript) :
    (verifierG I chk).toVerifier.verify (s, o) tr =
      if chk s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
  simp only [OracleVerifier.toVerifier]
  rw [OracleVerifier.materializeOutput_of_keepOracles _ rfl]
  simp only [verifierG]
  rw [show (liftM queryValues :
        OptionT (OracleComp ([]ₒ + ([TheOracle I]ₒ + [pSpec.Message]ₒ))) (List E)) =
      OptionT.lift (liftM queryValues :
        OracleComp ([]ₒ + ([TheOracle I]ₒ + [pSpec.Message]ₒ)) (List E)) from
    (OracleComp.monadLift_liftM_OptionT _).symm]
  rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]
  by_cases h : chk s (tr 0) (tr 1) = true
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

def guardedG : (verifierG I chk).toVerifier.GuardedForm where
  check := fun p tr ↦ chk p.1 (tr 0) (tr 1)
  out := fun p tr ↦ (pooled I p.1 (tr 0), p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ verifierG_verify I chk s o tr

theorem proverG_run_support (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (pr : pSpec.FullTranscript × ((I.Stmt × PubOut I) × ∀ i, TheOracle I i) × Unit)
    (hpr : pr ∈ support ((proverG I msg).run (s, o) ())) :
    pr.1 1 = msg s.1 (pr.1 0) ∧ pr.2 = ((pooled I s (pr.1 0), o), ()) := by
  have h0 : pSpec.dir 0 = .V_to_P := rfl
  have h1 : pSpec.dir 1 = .P_to_V := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_two,
    Prover.processRound_of_dir_eq_V_to_P 0 h0, Prover.processRound_of_dir_eq_P_to_V 1 h1] at hpr
  simp only [ChallengeIdx, Fin.vcons_fin_zero, Nat.reduceAdd, Challenge, Fin.reduceLast, proverG,
    Fin.isValue, MessageIdx, Message, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one,
    Fin.succ_one_eq_two, id_eq, HasQuery.instOfMonadLift_query, toPFunctor_emptySpec, liftM_pure,
    bind_pure_comp, map_pure, pure_bind, Functor.map_map, support_map, Set.mem_image] at hpr
  obtain ⟨r, -, rfl⟩ := hpr
  exact ⟨rfl, rfl⟩

variable (hchk : ∀ s r, chk s r (msg s.1 r) = true)

include hchk in
/-- Perfect completeness, whatever the message and the check, as long as the one passes the
other. -/
theorem completeG {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (OracleReduction.mk (proverG I msg) (verifierG I chk)).perfectCompleteness init impl
      (Seam.table I) (Seam.pub I) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨pr, hpr, rfl⟩ :=
    Reduction.mem_support_run_of_guarded _ (guardedG I chk) (s, o) witIn hx
  obtain ⟨hmsg, hout⟩ := proverG_run_support I msg s o pr hpr
  have hc : (guardedG I chk).check (s, o) pr.1 = true := by
    show chk s (pr.1 0) (pr.1 1) = true
    rw [hmsg]
    exact hchk s (pr.1 0)
  rw [if_pos hc]
  exact ⟨_, rfl, pooled_mem_pub I s o hIn (pr.1 0), congrArg Prod.fst hout⟩

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

def stateFunctionG :
    (verifierG I chk).toVerifier.KnowledgeStateFunction init impl (Seam.table I) (Seam.pub I)
      (extractor I) where
  toFun := fun m stmt tr _ ↦
    if h0 : m.val = 0 then ((stmt, ()) ∈ Seam.table I)
    else if h1 : m.val = 1 then
      ((pooled I stmt.1 (tr ⟨0, by omega⟩), stmt.2), ()) ∈ Seam.pub I
    else
      chk stmt.1 (tr ⟨0, by omega⟩) (tr ⟨1, by omega⟩) = true ∧
        ((pooled I stmt.1 (tr ⟨0, by omega⟩), stmt.2), ()) ∈ Seam.pub I
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m hm stmt tr msg w h ↦ by
    have hm1 : m = 1 := by
      fin_cases m
      · exact absurd hm (by decide)
      · rfl
    subst hm1
    exact h.2
  toFun_full := fun stmt tr _ h ↦
    Verifier.GuardedForm.of_probEvent_pos (guardedG I chk) init impl stmt tr _ h

/-- Round-by-round knowledge soundness at `1/|E|`, whatever the check: no hypothesis on
`chk`. -/
theorem rbrG :
    (verifierG I chk).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (Seam.table I)
      (Seam.pub I) (fun _ ↦ Unit) (extractor I) (stateFunctionG I chk init impl)
      (fun _ ↦ error) := by
  intro stmtIn i tr
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨i, hi⟩ := i
  have hi0 : i = 0 := by
    fin_cases i
    · rfl
    · exact absurd hi (by decide)
  subst hi0
  refine le_trans (probEvent_mono ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
    (fun r ↦ ((s, o), ()) ∉ Seam.table I ∧ ((pooled I s r, o), ()) ∈ Seam.pub I)
    fun r₁ r₂ h₁ h₂ ↦ bad_challenge_unique I s o h₁.1 h₁.2 h₂.2)
  rintro r - ⟨_, hin, hout⟩
  exact ⟨hin, hout⟩

end PublicInput

/-- The phase with the message `msg` and the check `chk`. -/
noncomputable def phaseG (I : M3Instance) (msg : I.Stmt → E → List E)
    (chk : (I.Stmt × TableOut I) → E → List E → Bool) :
    Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I) where
  n := 2
  pSpec := PublicInput.pSpec
  red := ⟨PublicInput.proverG I msg, PublicInput.verifierG I chk⟩
  err := fun _ ↦ PublicInput.error

/-- Both halves, for every message and every check the message passes. -/
def securityG (I : M3Instance) (msg : I.Stmt → E → List E)
    (chk : (I.Stmt × TableOut I) → E → List E → Bool)
    (hchk : ∀ s r, chk s r (msg s.1 r) = true) :
    Phase.Security I (phaseG I msg chk) (Seam.table I) (Seam.pub I) where
  outputPure := ⟨_, fun _ ↦ rfl⟩
  guarded := PublicInput.guardedG I chk
  complete := PublicInput.completeG I msg chk hchk
  witMid := fun _ ↦ Unit
  extractor := PublicInput.extractor I
  kSF := PublicInput.stateFunctionG I chk
  rbr := PublicInput.rbrG I chk

/-! ### Instances: each is a phase with both halves proved -/

/-- No check at all, and a prover that sends nothing. -/
def noCheckNoMessage (I : M3Instance) := securityG I (fun _ _ ↦ []) (fun _ _ _ ↦ true)
  fun _ _ ↦ rfl

/-- No check at all, and a prover that sends forty-two zeros. -/
def noCheckJunk (I : M3Instance) :=
  securityG I (fun _ _ ↦ List.replicate 42 0) (fun _ _ _ ↦ true) fun _ _ ↦ rfl

/-- The values of the lines with their cells swapped. -/
def swappedValues (I : M3Instance) (input : I.Stmt) (r : E) : List E :=
  ((I.publicLines input).filter (·.sent)).map fun l ↦ (1 + r) * ofK l.cell1 + r * ofK l.cell0

/-- A wrong check, the cells swapped, with a prover that sends what the wrong check expects. -/
def swappedCheck (I : M3Instance) :=
  securityG I (swappedValues I) (fun s r cs ↦ decide (cs = swappedValues I s.1 r))
    fun _ _ ↦ decide_eq_true rfl

/-- The specification's phase is the instance with the expected values and their check. -/
def specification (I : M3Instance) :=
  securityG I (PublicInput.expectedValues I) (PublicInput.check I) fun _ _ ↦ decide_eq_true rfl

namespace PublicInput
""" + CLOSE + """
#print axioms LeanerVM.Protocol.@NS@.securityG
#print axioms LeanerVM.Protocol.@NS@.noCheckNoMessage
#print axioms LeanerVM.Protocol.@NS@.noCheckJunk
#print axioms LeanerVM.Protocol.@NS@.swappedCheck
#print axioms LeanerVM.Protocol.@NS@.specification
"""
