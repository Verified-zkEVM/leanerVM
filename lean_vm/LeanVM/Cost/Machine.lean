module

public import Statement.CostMachine

/-!
# The cost machine

The machine (`Val`, `Op`, `Term`, `Program`, `eval`, `run`, `outputWithin`, `Program.size`) is
the statement's, `Statement/CostMachine.lean`, where `LeanVM.extractorOf` runs a program; its
specification by rules is `Cost/Spec.lean`.
-/
