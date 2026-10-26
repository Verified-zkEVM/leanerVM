module

public import Statement.LeanVmVerifier
public import Statement.Prover.Script

/-!
# The public-input phase, executable

The prover of the verifier's public-input phase (`publicInputPhase`, `LeanVmVerifier.lean`;
`r_pi`, nothing transmitted): it receives the challenge `r` and sends nothing; its claims are the
three memory limbs' values at the public point `(r, 0, …, 0)`, each the line through the limb's
cells `0` and `1`, `(1 + r)·m[0] + r·m[1]`: two cells read per limb.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- The value at `(r, 0, …, 0)` of a column, from its cells `0, 1`. -/
def lineAt (col : Array K) (r : E) : E := (1 + r) * ofK (col.getD 0 0) + r * ofK (col.getD 1 0)

/-- **The public-input phase**: receive `r`, send nothing; the claims of the three memory limbs
at the public point. -/
def pubFast (layout : Layout) (cols : Array (Array K)) : Script (List ColumnClaim) :=
  Script.sampleE.bind fun r ↦
    .ret (List.zipWith
      (fun column value ↦
        ⟨column, r :: List.replicate ((layout.placement memory0).vars - 1) 0, value⟩)
      [memory0, memory1, memory2]
      [lineAt (cols.getD memory0 #[]) r, lineAt (cols.getD memory1 #[]) r,
        lineAt (cols.getD memory2 #[]) r])

end LeanVM.Prover

end
