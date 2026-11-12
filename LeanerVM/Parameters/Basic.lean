module

/-!
# Concrete parameters

This layer binds versioned constants and encodings to their authoritative upstream sources: the
fields and the generator (`Field`, `Generator`), the BLAKE2s constants (`Blake2s`), and the
opcode codes and instance caps (`Isa`). Generic VM semantics and proof-system theory should not
depend on these concrete bindings unless the statement is intentionally deployment-specific.
-/

namespace LeanerVM.Parameters

public section

end
end LeanerVM.Parameters
