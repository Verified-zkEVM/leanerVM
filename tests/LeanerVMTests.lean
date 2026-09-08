import LeanerVMTests.Imports
import LeanerVMTests.Parameters.CleanField
import LeanerVMTests.Parameters.Field
import LeanerVMTests.Parameters.Generator

/-!
# leanerVM test aggregate

Every Lean test module other than the elaboration root is imported here. Repository validation
checks that this aggregate remains complete. It is a plain file because `LeanerVM.lean` is one
(see `CONTRIBUTING.md`).
-/
