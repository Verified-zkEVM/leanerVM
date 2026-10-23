/-
  LeanVM.Guest.ExpTables

  The exponent tables `exponent_tables` fills, as a relation on the memory: B1's `ExpTables`
  (`B1/Bits/Meaning.lean`), which the guest's shared check context (`Glob`) reads.
-/

module

public import LeanVM.Guest.B1.Bits.Meaning
