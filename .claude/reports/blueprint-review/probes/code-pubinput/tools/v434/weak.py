# Shared by mutations 3a and 4a: a weaker check `CHECK` (defined by DEFCHECK), the lines' values pooled.
exec(open('.claude/reports/blueprint-review/probes/code-pubinput/tools/v434/lib.py').read())

def weak_edits(DEFCHECK, HONEST):
    return [
("""/-- A line's claim holds of the stack exactly when""", DEFCHECK + """
/-- A line's claim holds of the stack exactly when"""),
("""    if check I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
""",
"""    if checkWeak I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
"""),
("""      if check I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
""",
"""      if checkWeak I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
"""),
("""  by_cases h : check I s (tr 0) (tr 1) = true
""",
"""  by_cases h : checkWeak I s (tr 0) (tr 1) = true
"""),
("""  check := fun p tr ↦ check I p.1 (tr 0) (tr 1)
""",
"""  check := fun p tr ↦ checkWeak I p.1 (tr 0) (tr 1)
"""),
("""  have hc : (guarded I).check (s, o) pr.1 = true := decide_eq_true hmsg
""",
"""  have hc : (guarded I).check (s, o) pr.1 = true := by
    show checkWeak I s (pr.1 0) (pr.1 1) = true
    rw [hmsg]
""" + HONEST),
]

WEAK_TAIL = AXIOMS + OPEN + """
variable (I : M3Instance)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The state function with the weak check in its last round. -/
def stateFunction' :
    (verifier I).toVerifier.KnowledgeStateFunction init impl (Seam.table I) (Seam.pub I)
      (extractor I) where
  toFun := fun m stmt tr _ ↦
    if h0 : m.val = 0 then ((stmt, ()) ∈ Seam.table I)
    else if h1 : m.val = 1 then
      ((pooled I stmt.1 (tr ⟨0, by omega⟩), stmt.2), ()) ∈ Seam.pub I
    else
      checkWeak I stmt.1 (tr ⟨0, by omega⟩) (tr ⟨1, by omega⟩) = true ∧
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
    Verifier.GuardedForm.of_probEvent_pos (guarded I) init impl stmt tr _ h

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
  refine le_trans (probEvent_mono ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
    (fun r ↦ ((s, o), ()) ∉ Seam.table I ∧ ((pooled I s r, o), ()) ∈ Seam.pub I)
    fun r₁ r₂ h₁ h₂ ↦ bad_challenge_unique I s o h₁.1 h₁.2 h₂.2)
  rintro r - ⟨_, hin, hout⟩
  exact ⟨hin, hout⟩
""" + CLOSE + """
#print axioms LeanerVM.Protocol.@NS@.PublicInput.rbr'
"""
