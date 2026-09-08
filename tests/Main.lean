import LeanerVMTests

/-- Elaboration root of the test surface; `scripts/validate.sh` checks it with warnings as
errors. -/
def main : IO Unit := do
  IO.println "leanerVM smoke test passed"
