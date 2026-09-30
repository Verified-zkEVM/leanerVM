# Mutation 4a: the pinned verifiers' equation on two values; the lines' values pooled.
exec(open('.claude/reports/blueprint-review/probes/code-pubinput/tools/v434/weak.py').read())
EDITS = weak_edits("""
/-- The pinned verifiers' check: with two lines whose value is sent, one equation on the two
values, `c₀ + y·c₁ = e₀ + y·e₁`; with any other number, the check per value. -/
def checkWeak (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  match (I.publicLines s.1).filter (·.sent), cs with
  | [l₀, l₁], [c₀, c₁] => decide (c₀ + y * c₁ = lineValue I r l₀ + y * lineValue I r l₁)
  | ls, cs => decide (cs = ls.map (lineValue I r))
""", """    unfold checkWeak expectedValues
    split
    · rename_i h₁ h₂
      rw [h₁, List.map_cons, List.map_cons, List.map_nil] at h₂
      injection h₂ with h₂ h₃
      injection h₃ with h₃ _
      subst h₂ h₃
      exact decide_eq_true rfl
    · exact decide_eq_true rfl
""")
TAIL = WEAK_TAIL
