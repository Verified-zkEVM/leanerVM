# Mutation 1: the check removed; the verifier reads the message, ignores it, pools the lines' values.
EDITS = [
# the verifier
("""  verify := fun s chals ↦ do
    let cs ← liftM queryValues
    if check I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
""",
"""  verify := fun s chals ↦ do
    let _cs ← liftM queryValues
    pure (pooled I s (chals ⟨0, rfl⟩))
"""),
# the verdict lemma, restated for the mutated verifier
("""    (verifier I).toVerifier.verify (s, o) tr =
      if check I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
""",
"""    (verifier I).toVerifier.verify (s, o) tr = pure (pooled I s (tr 0), o) := by
"""),
("""  rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]
  by_cases h : check I s (tr 0) (tr 1) = true
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]
    rfl
""",
"""  rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]
  rfl
"""),
# the guarded form: the check is constantly true
("""  check := fun p tr ↦ check I p.1 (tr 0) (tr 1)
  out := fun p tr ↦ (pooled I p.1 (tr 0), p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ verifier_verify I s o tr
""",
"""  check := fun _ _ ↦ true
  out := fun p tr ↦ (pooled I p.1 (tr 0), p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ (verifier_verify I s o tr).trans (ite_eq_left rfl).symm
"""),
# completeness: the guard passes by definition
("""  have hc : (guarded I).check (s, o) pr.1 = true := decide_eq_true hmsg
""",
"""  have hc : (guarded I).check (s, o) pr.1 = true := rfl
"""),
]
TAIL = """
/-! ## Repair: a state function whose last round does not mention the check -/

namespace LeanerVM.Protocol.@NS@

open LeanerVM.Parameters CompPoly OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

@[expose] public section

namespace PublicInput

variable (I : M3Instance)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- Before the challenge, the table seam; after it, and after the message, the public seam of
the pool. -/
def stateFunction' :
    (verifier I).toVerifier.KnowledgeStateFunction init impl (Seam.table I) (Seam.pub I)
      (extractor I) where
  toFun := fun m stmt tr _ ↦
    if h0 : m.val = 0 then ((stmt, ()) ∈ Seam.table I)
    else ((pooled I stmt.1 (tr ⟨0, by omega⟩), stmt.2), ()) ∈ Seam.pub I
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m hm stmt tr msg w h ↦ by
    have hm1 : m = 1 := by
      fin_cases m
      · exact absurd hm (by decide)
      · rfl
    subst hm1
    exact h
  toFun_full := fun stmt tr _ h ↦
    (Verifier.GuardedForm.of_probEvent_pos (guarded I) init impl stmt tr _ h).2

/-- The mutated verifier is round-by-round knowledge sound at the same error `1/|E|`. -/
theorem rbr' :
    (verifier I).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (Seam.table I)
      (Seam.pub I) (fun _ ↦ Unit) (extractor I) (stateFunction' I init impl)
      (fun _ ↦ error) := by
  intro stmtIn i tr
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨i, hi⟩ := i
  have hi0 : i = 0 := by
    fin_cases i
    · rfl
    · exact absurd hi (by decide)
  subst hi0
  refine le_trans (prEvent_mono _ _ _ ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
    (fun r ↦ ((s, o), ()) ∉ Seam.table I ∧ ((pooled I s r, o), ()) ∈ Seam.pub I)
    fun r₁ r₂ h₁ h₂ ↦ bad_challenge_unique I s o h₁.1 h₁.2 h₂.2)
  rintro r ⟨_, hin, hout⟩
  exact ⟨hin, hout⟩

end PublicInput

/-- The security half of the mutated phase, against the same two seams, at the same error. -/
def publicInputSecurity' (I : M3Instance) :
    Phase.Security I (publicInputPhase I) (Seam.table I) (Seam.pub I) where
  toComplete := publicInputComplete I
  witMid := fun _ ↦ Unit
  extractor := PublicInput.extractor I
  kSF := PublicInput.stateFunction' I
  rbr := PublicInput.rbr' I

end
end LeanerVM.Protocol.@NS@

#print axioms LeanerVM.Protocol.@NS@.PublicInput.verifier_verify
#print axioms LeanerVM.Protocol.@NS@.publicInputComplete
#print axioms LeanerVM.Protocol.@NS@.publicInputSecurity
#print axioms LeanerVM.Protocol.@NS@.publicInputSecurity'
"""
