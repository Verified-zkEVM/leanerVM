module

public import LeanVM.Cost.Extractor.Rewrites
import all CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohann
import all CompPoly.LinearAlgebra.PolynomialMatrix.Shifted
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Fields.Binary.BF64.Impl
import all Init.Data.Array.Basic

/-!
# The extractor, compiled: Mulders–Storjohann's reduction over `K`

CompPoly's `muldersStorjohannReduceFast` (github.com/Verified-zkEVM/CompPoly, Apache-2.0,
"Copyright (c) 2026 CompPoly Contributors"; compiled, not copied), the reducer of the decoder's
Lee–O'Sullivan interpolation: while two nonzero rows share a shifted leading position
(`cachedLeadingConflict?` over `rowLeadingPositions`), one step (`muldersStorjohannStepFast`).
The later modules of `Cost/Extractor/` reuse these functions (`findCompiled?`).
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters

public section

cost_compile msReduceK := CompPoly.PolynomialMatrix.muldersStorjohannReduceFast (F := K)

end

end LeanVM.Cost.Extractor
