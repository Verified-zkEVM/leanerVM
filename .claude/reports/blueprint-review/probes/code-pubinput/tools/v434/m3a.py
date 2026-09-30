# Mutation 3a: the check weakened to the first value; the lines' values pooled.
exec(open('.claude/reports/blueprint-review/probes/code-pubinput/tools/v434/weak.py').read())
EDITS = weak_edits("""
/-- The weakened check: the first value only. -/
def checkWeak (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  decide (cs.head? = (expectedValues I s.1 r).head?)
""", """    exact decide_eq_true rfl
""")
TAIL = WEAK_TAIL
