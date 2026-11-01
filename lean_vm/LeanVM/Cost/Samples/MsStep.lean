module

public import LeanVM.Cost.Extractor.MsReduce
import all CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohann
import all CompPoly.LinearAlgebra.PolynomialMatrix.Shifted
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Fields.Binary.BF64.Impl
import all Init.Data.Array.Basic

/-!
# Sample: one Mulders–Storjohann step over `K`, compiled

CompPoly's `muldersStorjohannStepFast` (github.com/Verified-zkEVM/CompPoly, Apache-2.0,
"Copyright (c) 2026 CompPoly Contributors"; compiled, not copied): find the shifted degrees of
two rows, cancel the leading term of the one of larger degree by the other (a field division, the
fused `a - c·X^d·b` per entry, trimming), replace the row. One `cost_compile` line; CompPoly's
equations for the compiler are in `Cost/CompPolyLib.lean`. Its callees are the extractor's
(`Cost/Extractor/MsReduce.lean`, reused), so their bounds serve both.
-/

namespace LeanVM.Cost.Samples

open LeanVM.Cost LeanVM.Parameters

cost_compile msStepK := CompPoly.PolynomialMatrix.muldersStorjohannStepFast (F := K)

end LeanVM.Cost.Samples
