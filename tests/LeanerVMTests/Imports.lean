import LeanerVM

/-!
# Import smoke test

Checks that the production aggregate is available through the test-library root.
-/

namespace LeanerVMTests

/-- The test library elaborates through the complete production import surface. -/
example : True := by
  trivial

end LeanerVMTests
