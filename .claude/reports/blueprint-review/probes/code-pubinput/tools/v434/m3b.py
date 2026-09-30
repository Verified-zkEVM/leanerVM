# Mutation 3b: the check weakened to the first value, and the pooled values are the prover's.
exec(open('.claude/reports/blueprint-review/probes/code-pubinput/tools/v434/lib.py').read())
EDITS = [
IMPORT_TOY,
("""/-- A line's claim holds of the stack exactly when""", POOLFROM + """
/-- The weakened check: the first value only. -/
def checkWeak (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  decide (cs.head? = (expectedValues I s.1 r).head?)

/-- A line's claim holds of the stack exactly when"""),
("""    if check I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
""",
"""    if checkWeak I s (chals ⟨0, rfl⟩) cs then pure (pooledFrom I s (chals ⟨0, rfl⟩) cs)
    else failure
"""),
("""      if check I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
""",
"""      if checkWeak I s (tr 0) (tr 1) then pure (pooledFrom I s (tr 0) (tr 1), o)
      else failure := by
"""),
("""  by_cases h : check I s (tr 0) (tr 1) = true
""",
"""  by_cases h : checkWeak I s (tr 0) (tr 1) = true
"""),
("""  check := fun p tr ↦ check I p.1 (tr 0) (tr 1)
  out := fun p tr ↦ (pooled I p.1 (tr 0), p.2)
""",
"""  check := fun p tr ↦ checkWeak I p.1 (tr 0) (tr 1)
  out := fun p tr ↦ (pooledFrom I p.1 (tr 0) (tr 1), p.2)
"""),
("""  have hc : (guarded I).check (s, o) pr.1 = true := decide_eq_true hmsg
  rw [if_pos hc]
  exact ⟨_, rfl, pooled_mem_pub I s o hIn (pr.1 0), congrArg Prod.fst hout⟩
""",
"""  have hc : (guarded I).check (s, o) pr.1 = true := by
    show checkWeak I s (pr.1 0) (pr.1 1) = true
    rw [hmsg]
    exact decide_eq_true rfl
  rw [if_pos hc]
  have hpool : (guarded I).out (s, o) pr.1 = (pooled I s (pr.1 0), o) := by
    show (pooledFrom I s (pr.1 0) (pr.1 1), o) = (pooled I s (pr.1 0), o)
    rw [hmsg, pooledFrom_expected]
  rw [hpool]
  exact ⟨_, rfl, pooled_mem_pub I s o hIn (pr.1 0), congrArg Prod.fst hout⟩
"""),
]
TAIL = AXIOMS + OPEN + REFUTE + """
/-! ## The mutated verifier is not knowledge sound: two lines with their value sent, a stack
wrong on the second -/

open Toy

/-- The toy with two lines, both with their value sent: column 0 with cells `(v, 1)` and
column 1 with cells `(1, 1)`. -/
abbrev twoSent : M3Instance :=
  { toy with publicLines := fun v ↦
      [⟨⟨0, 0⟩, v, 1, true, by decide⟩, ⟨⟨0, 1⟩, 1, 1, true, by decide⟩] }

/-- Column 0 is `[1, 1]`, as the statement `1` says; column 1 is `[1, 0]`, not `[1, 1]`. -/
abbrev badSecond : Column 3 := ⟨#v[1, 1, 1, 0, 1, 0, 0, 0]⟩

/-- The statement `1`, no earlier claim, the wrong stack. -/
abbrev badStmt : (K × TableOut twoSent) × (∀ i, TheOracle twoSent i) :=
  (((1 : K), ⟨[]⟩), fun _ ↦ badSecond)

/-- The wrong stack is outside the table seam. -/
theorem badStmt_not_mem : (badStmt, ()) ∉ Seam.table twoSent := by
  rintro ⟨-, hl, -⟩
  have h := (hl _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))).2
  exact zero_ne_one h

/-- The extension of column `i` of the wrong stack at `(r)`. -/
def trueValue (i : Fin 3) (r : E) : E :=
  CMlPolynomialEval.eval₂Mle (twoSent.column badSecond ⟨0, i⟩).values (algebraMap K E)
    (linePoint (n := 1) (by decide) r)

/-- On column 0, which is right, the extension is the line's value. -/
theorem trueValue_zero (r : E) : trueValue 0 r = (1 + r) * ofK 1 + r * ofK 1 := by
  unfold trueValue
  rw [eval₂Mle_linePoint, CharTwo.sub_eq_add]
  rfl

/-- What the prover sends: the first line's value, which the check reads, and the true
extension of its wrong column 1, which nothing checks. -/
def cheat (r : E) : List E := [(1 + r) * ofK 1 + r * ofK 1, trueValue 1 r]

/-- The mutated verifier accepts it at every challenge, with a pool that holds of the wrong
stack. -/
theorem accepts (r : E) :
    (guarded twoSent).check badStmt (tr2 r (cheat r)) = true ∧
      ((guarded twoSent).out badStmt (tr2 r (cheat r)), ()) ∈ Seam.pub twoSent := by
  refine ⟨decide_eq_true rfl, ?_, trivial⟩
  intro c hc
  change c ∈ [(⟨⟨0, 0⟩, linePoint (n := 1) (by decide) r, (1 + r) * ofK 1 + r * ofK 1⟩ :
      ColumnClaim twoSent),
    ⟨⟨0, 1⟩, linePoint (n := 1) (by decide) r, trueValue 1 r⟩] at hc
  rw [List.mem_cons, List.mem_singleton] at hc
  rcases hc with rfl | rfl
  · exact trueValue_zero r
  · rfl

/-- No extractor, no state function and no error below one make the mutated verifier
round-by-round knowledge sound against the two seams. -/
theorem not_knowledgeSound (ε : pSpec.ChallengeIdx → ℝ≥0) (hε : ε ⟨0, rfl⟩ < 1) :
    ¬ (verifier twoSent).toVerifier.rbrKnowledgeSoundnessWorstCase (pure ()) noOracle
      (Seam.table twoSent) (Seam.pub twoSent) ε :=
  not_rbr _ (guarded twoSent) noOracle badStmt badStmt_not_mem cheat accepts ε hε
""" + CLOSE + """
#print axioms LeanerVM.Protocol.@NS@.PublicInput.not_knowledgeSound
"""
