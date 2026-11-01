module

public import LeanVM.Cost.Extractor.Top
public import LeanVM.Guest.Fast.DiscreteLog

/-!
# The guest decoder's compiled chain: the exponent of a power of `g`

The guest decoder's readers read counts and positions as exponents (`B1.Main.gLog`: the `i < 2^34`
with `g^i` the word's low limb, `0` otherwise). Compiled here through a discrete logarithm
(`gLog_discreteLog`: `Located.gLogWith Extraction.Fast.discreteLog`, Pohlig–Hellman over the
factors of `2^64 − 1`, `Guest/Fast/DiscreteLog.lean`'s `gLog_eq_discreteLog`). This module is the
decoder chain's one point of contact with the logarithm.

Every module of the chain imports `LeanVM.Cost.Extractor.Top` first, through this one: the
compiler allocates function indices from its imports, so the decoder's functions follow the
extractor's and share its compiled library.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.B1 LeanVM.Guest.B1.Main

@[expose] public section

/-- `gLog` through the discrete logarithm. -/
theorem gLog_discreteLog (x : E) :
    gLog x = LeanVM.Guest.Located.gLogWith LeanVM.Extraction.Fast.discreteLog x :=
  congrFun LeanVM.Guest.Fast.gLog_eq_discreteLog x

cost_rewrite gLog_discreteLog


end

end LeanVM.Cost.Decoder
