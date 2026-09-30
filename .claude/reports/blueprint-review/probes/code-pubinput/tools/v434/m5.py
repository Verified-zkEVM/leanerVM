# Mutation 5: only the lines whose value is sent are pooled.
exec(open('.claude/reports/blueprint-review/probes/code-pubinput/tools/v434/lib.py').read())
EDITS = [
IMPORT_TOY,
("""/-- A line's claim holds of the stack exactly when""", """
/-- The mutated pool: the claims received, then one claim per line whose value is sent. -/
def pooledSent (s : I.Stmt × TableOut I) (r : E) : I.Stmt × PubOut I :=
  (s.1, ⟨s.2.columns ++ ((I.publicLines s.1).filter (·.sent)).map (lineClaim I r)⟩)

/-- A line's claim holds of the stack exactly when"""),
# the prover outputs the mutated pool as well, so that the two outputs agree
("""  output := fun st ↦ pure ((pooled I st.2.1.1 st.1, st.2.1.2), ())
""",
"""  output := fun st ↦ pure ((pooledSent I st.2.1.1 st.1, st.2.1.2), ())
"""),
("""    if check I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
""",
"""    if check I s (chals ⟨0, rfl⟩) cs then pure (pooledSent I s (chals ⟨0, rfl⟩)) else failure
"""),
("""      if check I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
""",
"""      if check I s (tr 0) (tr 1) then pure (pooledSent I s (tr 0), o) else failure := by
"""),
("""  check := fun p tr ↦ check I p.1 (tr 0) (tr 1)
  out := fun p tr ↦ (pooled I p.1 (tr 0), p.2)
""",
"""  check := fun p tr ↦ check I p.1 (tr 0) (tr 1)
  out := fun p tr ↦ (pooledSent I p.1 (tr 0), p.2)
"""),
("""    pr.1 1 = expectedValues I s.1 (pr.1 0) ∧ pr.2 = ((pooled I s (pr.1 0), o), ()) := by
""",
"""    pr.1 1 = expectedValues I s.1 (pr.1 0) ∧ pr.2 = ((pooledSent I s (pr.1 0), o), ()) := by
"""),
("""  rw [if_pos hc]
  exact ⟨_, rfl, pooled_mem_pub I s o hIn (pr.1 0), congrArg Prod.fst hout⟩
""",
"""  rw [if_pos hc]
  have hsub : ((pooledSent I s (pr.1 0), o), ()) ∈ Seam.pub I := by
    obtain ⟨hcols, haux⟩ := pooled_mem_pub I s o hIn (pr.1 0)
    refine ⟨fun c hc ↦ hcols c ?_, haux⟩
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
      exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mp hl).1)
  exact ⟨_, rfl, hsub, congrArg Prod.fst hout⟩
"""),
]
TAIL = AXIOMS + OPEN + REFUTE + """
/-! ## The mutated verifier is not knowledge sound: a line whose value is not sent -/

open Toy

/-- The toy with its line's value not sent. -/
abbrev noneSent : M3Instance :=
  { toy with publicLines := fun v ↦ [⟨⟨0, 2⟩, v, 0, false, by decide⟩] }

/-- Column 2 changed to `[1, 1]`: cell 1 is not the statement's `0`. -/
abbrev badLine : Column 3 := ⟨#v[1, 1, 1, 1, 1, 1, 0, 0]⟩

/-- The statement `1`, no earlier claim, the wrong stack. -/
abbrev badStmt : (K × TableOut noneSent) × (∀ i, TheOracle noneSent i) :=
  (((1 : K), ⟨[]⟩), fun _ ↦ badLine)

/-- The wrong stack is outside the table seam. -/
theorem badStmt_not_mem : (badStmt, ()) ∉ Seam.table noneSent := by
  rintro ⟨-, hl, -⟩
  have h := (hl _ (List.mem_singleton_self _)).2
  exact one_ne_zero h

/-- The mutated verifier accepts the empty message at every challenge, with an empty pool. -/
theorem accepts (r : E) :
    (guarded noneSent).check badStmt (tr2 r []) = true ∧
      ((guarded noneSent).out badStmt (tr2 r []), ()) ∈ Seam.pub noneSent := by
  have hcheck : (guarded noneSent).check badStmt (tr2 r []) = true := by
    show decide (([] : List E) = expectedValues noneSent (1 : K) r) = true
    exact decide_eq_true rfl
  refine ⟨hcheck, ?_, trivial⟩
  intro c hc
  change c ∈ ([] : List (ColumnClaim noneSent)) at hc
  exact absurd hc List.not_mem_nil

/-- No extractor, no state function and no error below one make the mutated verifier
round-by-round knowledge sound against the two seams. -/
theorem not_knowledgeSound (ε : pSpec.ChallengeIdx → ℝ≥0) (hε : ε ⟨0, rfl⟩ < 1) :
    ¬ (verifier noneSent).toVerifier.rbrKnowledgeSoundnessWorstCase (pure ()) noOracle
      (Seam.table noneSent) (Seam.pub noneSent) ε :=
  not_rbr _ (guarded noneSent) noOracle badStmt badStmt_not_mem (fun _ ↦ []) accepts ε hε
""" + CLOSE + """
#print axioms LeanerVM.Protocol.@NS@.PublicInput.not_knowledgeSound
"""
