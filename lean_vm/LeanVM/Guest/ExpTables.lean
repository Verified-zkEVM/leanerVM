/-
  LeanVM.Guest.ExpTables

  The exponent tables `exponent_tables` fills, as a relation on the memory: a definition of its
  own so that the guest's shared check context (`Glob`) does not import the guest's proofs.
-/

module

public import LeanVM.Guest.Core
public import LeanVM.Guest.Value.Tables

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-- The two exponent tables at `p`, `q`: `p[g^j] = E(2^j)`, `q[g^j] = g^(2^j)`, `j < 34`. -/
def ExpTables (rd : Reader) (p q : E) : Prop :=
  ∀ j < sizeBits, LoadHolds rd p j (eOfNat (2 ^ j)) ∧ LoadHolds rd q j (gen ^ 2 ^ j)

end
end LeanVM.Guest.B1
