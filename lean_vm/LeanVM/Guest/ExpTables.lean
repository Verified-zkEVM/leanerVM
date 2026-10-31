/-
  LeanVM.Guest.ExpTables

  The exponent tables `exponent_tables` fills (`B1.ExpTables`), for the guest's shared check
  context (`Glob`) and B1's meaning of `exponent_tables` (`B1/Bits/Meaning.lean`).
-/

module

public import LeanVM.Guest.Core
public import Statement.Field

/-!
# The exponent tables

Defined here, apart from B1's proofs, so that the check context, and with it the kernel-checked
certificates of the compiled functions (`B2C`), do not import them.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `SIZE_BITS`: the exponent tables' length. -/
abbrev sizeBits : ℕ := 34

/-- The two exponent tables at `p`, `q`: `p[g^j] = E(2^j)`, `q[g^j] = g^(2^j)`, `j < 34`. -/
def ExpTables (rd : Reader) (p q : E) : Prop :=
  ∀ j < sizeBits, LoadHolds rd p j (eOfNat (2 ^ j)) ∧ LoadHolds rd q j (gen ^ 2 ^ j)

end
end LeanVM.Guest.B1
