# Mutation 8: an extra check leanVM does not make: the message's first value is nonzero.
exec(open('.claude/reports/blueprint-review/probes/code-pubinput/tools/lib.py').read())
EDITS = [
IMPORT_TOY,
("""/-- A line's claim holds of the stack exactly when""", """
/-- The check with an extra condition: the first value of the message is nonzero. -/
def checkExtra (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  check I s r cs && decide (cs.headD 0 ≠ 0)

/-- A line's claim holds of the stack exactly when"""),
("""    if check I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
""",
"""    if checkExtra I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
"""),
("""      if check I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
""",
"""      if checkExtra I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
"""),
("""  by_cases h : check I s (tr 0) (tr 1) = true
""",
"""  by_cases h : checkExtra I s (tr 0) (tr 1) = true
"""),
("""  check := fun p tr ↦ check I p.1 (tr 0) (tr 1)
""",
"""  check := fun p tr ↦ checkExtra I p.1 (tr 0) (tr 1)
"""),
]
TAIL = AXIOMS + OPEN + REFUTE + """
/-! ## The mutated verifier is not complete: the toy at statement `0`, whose line's value is
zero at every challenge -/

open Toy

/-- The honest stack for the statement `0`: column 2 is `[0, 0]`. -/
abbrev honest0 : Column 3 := ⟨#v[1, 1, 1, 1, 0, 0, 0, 0]⟩

/-- The statement `0`, no earlier claim, its honest stack. -/
abbrev honestStmt : (K × TableOut toy) × (∀ i, TheOracle toy i) :=
  (((0 : K), ⟨[]⟩), fun _ ↦ honest0)

/-- The honest stack is in the table seam. -/
theorem honestStmt_mem : (honestStmt, ()) ∈ Seam.table toy := by
  refine ⟨fun c hc ↦ absurd hc List.not_mem_nil, ?_, trivial⟩
  intro l hl
  rw [List.mem_singleton] at hl
  subst hl
  exact ⟨rfl, rfl⟩

/-- The line's value is `(1 + r)·0 + r·0 = 0`, so the extra check rejects the honest message at
every challenge (and every other message fails the check proper). -/
theorem honest_rejected (r : E) :
    checkExtra toy honestStmt.1 r (expectedValues toy 0 r) = false := by
  unfold checkExtra
  rw [Bool.and_eq_false_iff]
  right
  apply decide_eq_false
  intro h
  apply h
  change (1 + r) * ofK 0 + r * ofK 0 = 0
  have h0 : ofK (0 : K) = 0 := map_zero (algebraMap K E)
  rw [h0, mul_zero, mul_zero, add_zero]

/-- Not perfectly complete, for every initial state and implementation of the shared oracle. -/
theorem not_complete {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ¬ (OracleReduction.mk (prover toy) (verifier toy)).perfectCompleteness init impl
      (Seam.table toy) (Seam.pub toy) := by
  refine not_perfectCompleteness init impl _ honestStmt () honestStmt_mem ?_
  intro x hx result hres
  obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _ (guarded toy) honestStmt () hx
  obtain ⟨hmsg, -⟩ := prover_run_support toy honestStmt.1 honestStmt.2 pr hpr
  have hc : (guarded toy).check honestStmt pr.1 = false := by
    show checkExtra toy honestStmt.1 (pr.1 0) (pr.1 1) = false
    rw [hmsg]
    exact honest_rejected (pr.1 0)
  rw [hc] at hres
  exact absurd hres (by simp)
""" + CLOSE + """
#print axioms LeanerVM.Protocol.@NS@.PublicInput.not_complete
"""
