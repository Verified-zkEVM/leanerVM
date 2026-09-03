module

public import LeanerVMTests

public section

/-- Executable smoke test for the aggregate test surface. -/
def main : IO Unit := do
  IO.println "leanerVM smoke test passed"

end
