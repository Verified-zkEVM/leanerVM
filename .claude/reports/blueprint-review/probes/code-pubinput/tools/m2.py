# Mutation 2: no check, and the pooled values are the prover's.
exec(open('.claude/reports/blueprint-review/probes/code-pubinput/tools/lib.py').read())
EDITS = [
IMPORT_TOY,
("""/-- A line's claim holds of the stack exactly when""", POOLFROM + """
/-- A line's claim holds of the stack exactly when"""),
("""  verify := fun s chals ↦ do
    let cs ← liftM queryValues
    if check I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
""",
"""  verify := fun s chals ↦ do
    let cs ← liftM queryValues
    pure (pooledFrom I s (chals ⟨0, rfl⟩) cs)
"""),
("""    (verifier I).toVerifier.verify (s, o) tr =
      if check I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
""",
"""    (verifier I).toVerifier.verify (s, o) tr = pure (pooledFrom I s (tr 0) (tr 1), o) := by
"""),
("""  rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]
  by_cases h : check I s (tr 0) (tr 1) = true
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl
""",
"""  rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]
  rfl
"""),
("""  check := fun p tr ↦ check I p.1 (tr 0) (tr 1)
  out := fun p tr ↦ (pooled I p.1 (tr 0), p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ verifier_verify I s o tr
""",
"""  check := fun _ _ ↦ true
  out := fun p tr ↦ (pooledFrom I p.1 (tr 0) (tr 1), p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ (verifier_verify I s o tr).trans (if_pos rfl).symm
"""),
("""  have hc : (guarded I).check (s, o) pr.1 = true := decide_eq_true hmsg
  rw [if_pos hc]
  exact ⟨_, rfl, pooled_mem_pub I s o hIn (pr.1 0), congrArg Prod.fst hout⟩
""",
"""  have hc : (guarded I).check (s, o) pr.1 = true := rfl
  rw [if_pos hc]
  have hpool : (guarded I).out (s, o) pr.1 = (pooled I s (pr.1 0), o) := by
    show (pooledFrom I s (pr.1 0) (pr.1 1), o) = (pooled I s (pr.1 0), o)
    rw [hmsg, pooledFrom_expected]
  rw [hpool]
  exact ⟨_, rfl, pooled_mem_pub I s o hIn (pr.1 0), congrArg Prod.fst hout⟩
"""),
]
TAIL = AXIOMS + OPEN + REFUTE + """
/-! ## The mutated verifier is not knowledge sound: the toy, a wrong stack, a truthful prover -/

open Toy

/-- Column 2 changed to `[1, 1]`: cell 1 is not the statement's `0`. -/
abbrev badLine : Column 3 := ⟨#v[1, 1, 1, 1, 1, 1, 0, 0]⟩

/-- The statement `1`, no earlier claim, the wrong stack. -/
abbrev badStmt : (K × TableOut toy) × (∀ i, TheOracle toy i) := (((1 : K), ⟨[]⟩), fun _ ↦ badLine)

/-- The wrong stack is outside the table seam. -/
theorem badStmt_not_mem : (badStmt, ()) ∉ Seam.table toy := by
  rintro ⟨-, hl, -⟩
  have h := (hl _ (List.mem_singleton_self _)).2
  exact one_ne_zero h

/-- What a truthful prover sends: the extension of its column 2 at `(r)`. -/
def trueValue (r : E) : E :=
  CMlPolynomialEval.eval₂Mle (toy.column badLine ⟨0, 2⟩).values (algebraMap K E)
    (linePoint (n := 1) (by decide) r)

/-- The mutated verifier accepts it at every challenge, with a pool that holds of the wrong
stack. -/
theorem accepts (r : E) :
    (guarded toy).check badStmt (tr2 r [trueValue r]) = true ∧
      ((guarded toy).out badStmt (tr2 r [trueValue r]), ()) ∈ Seam.pub toy := by
  refine ⟨rfl, ?_, trivial⟩
  intro c hc
  change c ∈ [(⟨⟨0, 2⟩, linePoint (n := 1) (by decide) r, trueValue r⟩ : ColumnClaim toy)] at hc
  rw [List.mem_singleton] at hc
  subst hc
  rfl

/-- No extractor, no state function and no error below one make the mutated verifier
round-by-round knowledge sound against the two seams. -/
theorem not_knowledgeSound (ε : pSpec.ChallengeIdx → ℝ≥0) (hε : ε ⟨0, rfl⟩ < 1) :
    ¬ (verifier toy).toVerifier.rbrKnowledgeSoundnessWorstCase (pure ()) noOracle
      (Seam.table toy) (Seam.pub toy) ε :=
  not_rbr _ (guarded toy) noOracle badStmt badStmt_not_mem (fun r ↦ [trueValue r]) accepts ε hε
""" + CLOSE + """
#print axioms LeanerVM.Protocol.@NS@.PublicInput.not_knowledgeSound
"""
