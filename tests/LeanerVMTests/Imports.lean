module

public import LeanerVM

/-!
# Public import smoke test

Checks that the production aggregate is available through the test-library root.
-/

namespace LeanerVMTests

public section

/-- The initial test library elaborates through the complete public import surface. -/
example : True := by
  trivial

end
end LeanerVMTests
