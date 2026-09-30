# Mutation 7a: a wrong check (the cells swapped); the honest prover unchanged; the lines' values pooled.
exec(open('.claude/reports/blueprint-review/probes/code-pubinput/tools/lib.py').read())
EDITS = [
IMPORT_TOY,
("""/-- A line's claim holds of the stack exactly when""", """
/-- The values of the lines with their cells swapped: `(1 + r)·cell1 + r·cell0`. -/
def swappedValues (input : I.Stmt) (r : E) : List E :=
  ((I.publicLines input).filter (·.sent)).map fun l ↦ (1 + r) * ofK l.cell1 + r * ofK l.cell0

/-- The wrong check: the message is the swapped values. -/
def checkWrong (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  decide (cs = swappedValues I s.1 r)

/-- A line's claim holds of the stack exactly when"""),
("""    if check I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
""",
"""    if checkWrong I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
"""),
("""      if check I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
""",
"""      if checkWrong I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
"""),
("""  by_cases h : check I s (tr 0) (tr 1) = true
""",
"""  by_cases h : checkWrong I s (tr 0) (tr 1) = true
"""),
("""  check := fun p tr ↦ check I p.1 (tr 0) (tr 1)
""",
"""  check := fun p tr ↦ checkWrong I p.1 (tr 0) (tr 1)
"""),
]
TAIL = AXIOMS + OPEN + REFUTE + """
/-! ## The mutated verifier is not complete: the toy, the honest stack, the honest prover -/

open Toy

/-- The statement `1`, no earlier claim, the honest stack (column 2 is `[1, 0]`). -/
abbrev honestStmt : (K × TableOut toy) × (∀ i, TheOracle toy i) :=
  (((1 : K), ⟨[]⟩), fun _ ↦ honest)

/-- The honest stack is in the table seam. -/
theorem honestStmt_mem : (honestStmt, ()) ∈ Seam.table toy := by
  refine ⟨fun c hc ↦ absurd hc List.not_mem_nil, ?_, trivial⟩
  intro l hl
  rw [List.mem_singleton] at hl
  subst hl
  exact ⟨rfl, rfl⟩

/-- At every challenge the honest message, `(1 + r)·1 + r·0`, is not the swapped value,
`(1 + r)·0 + r·1`: the wrong check rejects the honest prover. -/
theorem honest_rejected (r : E) : checkWrong toy honestStmt.1 r (expectedValues toy 1 r) = false := by
  apply decide_eq_false
  intro h
  change [(1 + r) * ofK 1 + r * ofK 0] = [(1 + r) * ofK 0 + r * ofK 1] at h
  have h1 : ofK (1 : K) = 1 := map_one (algebraMap K E)
  have h0 : ofK (0 : K) = 0 := map_zero (algebraMap K E)
  rw [h0, h1, List.cons.injEq] at h
  have : (1 : E) = 0 := by linear_combination h.1
  exact one_ne_zero this

/-- Not perfectly complete, for every initial state and implementation of the shared oracle. -/
theorem not_complete {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ¬ (OracleReduction.mk (prover toy) (verifier toy)).perfectCompleteness init impl
      (Seam.table toy) (Seam.pub toy) := by
  refine not_perfectCompleteness init impl _ honestStmt () honestStmt_mem ?_
  intro x hx result hres
  obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _ (guarded toy) honestStmt () hx
  obtain ⟨hmsg, -⟩ := prover_run_support toy honestStmt.1 honestStmt.2 pr hpr
  have hc : (guarded toy).check honestStmt pr.1 = false := by
    show checkWrong toy honestStmt.1 (pr.1 0) (pr.1 1) = false
    rw [hmsg]
    exact honest_rejected (pr.1 0)
  rw [hc] at hres
  exact absurd hres (by simp)
""" + CLOSE + """
#print axioms LeanerVM.Protocol.@NS@.PublicInput.not_complete
"""
