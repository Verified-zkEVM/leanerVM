import SphincsBase.Scheme
import Mathlib.Tactic.IrreducibleDef

/-!
# Hypertree hash costs

The oracle calls an honest computation of the hypertree makes, as formulas in the parameters of `Scheme.lean`. They are sealed, so the accounting carries them symbolically and never evaluates them.
-/

namespace SphincsBase.Concrete

/-- A one-time public key: every chain walked to its end. -/
irreducible_def oneTimeKeyHashCost : Nat := numChains * (chainLength - 1)

/-- A node at `level` of a layer tree, the leaves being level `0`: each leaf is a one-time public key and its leaf hash. -/
irreducible_def treeNodeHashCost (level : Nat) : Nat := (oneTimeKeyHashCost + 2) * 2 ^ level - 1

/-- Key generation: the root of the top layer's tree. -/
irreducible_def keygenHashCost : Nat := treeNodeHashCost (layerHeight topLayer)

end SphincsBase.Concrete
