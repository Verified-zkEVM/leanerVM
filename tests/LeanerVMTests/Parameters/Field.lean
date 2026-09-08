module

public import LeanerVM.Parameters.Field
meta import LeanerVM.Parameters.Field
meta import CompPoly.Fields.Binary.BF64

/-!
# Layer 0 tests: fields and limbs

Executable checks (`#guard`, compiled) of the limb view, the defining relation, and the two
predicates on concrete words, with one mutated word per predicate; and kernel checks
(`decide +kernel`) of what the kernel can reduce from a `module` file: literal words and the
predicates on them.
-/

namespace LeanerVMTests.Parameters

open LeanerVM.Parameters

public section

/-! ## Limbs and the defining relation -/

#guard (E.ofLimbs 1 2 3).limb 0 = 1
#guard (E.ofLimbs 1 2 3).limb 1 = 2
#guard (E.ofLimbs 1 2 3).limb 2 = 3
#guard E.ofLimbs 1 2 3 = ofK 1 + ofK 2 * y + ofK 3 * y ^ 2
#guard y ^ 3 = E.ofLimbs 1 1 0
#guard toString (E.ofLimbs 1 2 3) = "E(0x000000000000000300000000000000020000000000000001)"

/-! ## `IsInK` and `IsCanonical128` -/

#guard IsInK (ofK 5)
#guard IsInK (E.ofLimbs 7 0 0)
-- Mutations: a `y` limb, then a `y²` limb.
#guard ¬ IsInK (E.ofLimbs 7 1 0)
#guard ¬ IsInK (E.ofLimbs 7 0 1)
#guard IsCanonical128 (E.ofLimbs 1 2 0)
#guard ¬ IsCanonical128 (E.ofLimbs 0 0 1)
#guard ¬ IsCanonical128 (y ^ 2)

/-- The predicates decide in the kernel on literal words. -/
example : IsInK (E.ofLimbs 7 0 0) ∧ ¬ IsInK (E.ofLimbs 7 1 0) ∧
    IsCanonical128 (E.ofLimbs 1 2 0) ∧ ¬ IsCanonical128 (E.ofLimbs 0 0 1) := by
  decide +kernel

/-! ## Field structure -/

/-- Instance search finds CompPoly's field structure on `K`; nothing else is installed. -/
example : (inferInstance : Field K) = BF64.instField := rfl

end
end LeanerVMTests.Parameters
