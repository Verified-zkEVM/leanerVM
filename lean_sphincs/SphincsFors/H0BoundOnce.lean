import SphincsFors.H0Bound
import SphincsFors.H0Once

/-! The one-coin Poisson rate at budget `q`, the rate of the signatures plus one coin per future
pair (no inflation of the signature loads by the cached share), is below the rational bound
`muOnceQ` at the right end of a budget interval. -/

open ENNReal

namespace SphincsFors.Security.H0

open Concrete Domination ForsPrice

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512

/-! ### The rational rate bound -/

/-- Upper bound for the one-coin Poisson rate at the right end `qb` of an interval. -/
def muOnceQ (b N qb R : ℕ) : ℚ :=
  (N : ℚ) / 2 ^ b +
    ((qb : ℚ) / ((2 : ℚ) ^ 128 - qb - 2 ^ 32)) * (1 + 2 ^ 26 / ((2 : ℚ) ^ 128 - qb - 2 ^ 32)) ^ (24 * R) / 2 ^ b

variable [Params]

end SphincsFors.Security.H0
