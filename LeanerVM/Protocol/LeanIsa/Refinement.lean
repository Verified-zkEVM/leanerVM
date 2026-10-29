/-
  LeanerVM.Protocol.LeanIsa.Refinement

  The adaptor's soundness direction as the spine's refinement from the M3 relation to leanISA's
  constraint system.
-/

module

public import LeanerVM.Protocol.LeanIsa.Sound
public import LeanerVM.Protocol.ToArkLib.Refinement

/-!
# The adaptor as a refinement

`leanIsaRefinement` packages `satisfiedBy_witnessOf` as the spine's `Refinement` from `M3Rel` to
`SatisfiedBy` at the announced memory log-size, the witness map the knowledge transport needs. A
module of its own, so that the adaptor's two directions import no module of the oracle protocol.
-/

namespace LeanerVM.Protocol.LeanIsa

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- `SatisfiedBy` as a relation on the protocol's statements at memory log-size `κ`: the public
input, no oracle. -/
def satisfiedByRel (prog : Program) (κ : ℕ) :
    Set ((PublicInput × ∀ i, NoOracle i) × EnsembleWitness (leanIsaEnsemble prog κ)) :=
  {p | SatisfiedBy prog p.1.1 p.2}

/-- The adaptor as a refinement: on admissible sizes, reading the witness off the stack maps the
protocol's relation into leanISA's at the announced memory log-size. -/
def leanIsaRefinement (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog) :
    Refinement (M3Rel (leanIsaInstance F prog s)) (satisfiedByRel prog s.logMem) where
  map _ q := witnessOf F prog s q
  map_valid _ q h := satisfiedBy_witnessOf F prog s q hs h

end

end LeanerVM.Protocol.LeanIsa
