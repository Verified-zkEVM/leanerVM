module

public import LeanVM.Cost.Extractor.MsReduce
public import LeanVM.Protocol.Extraction.Fast.DecoderFast
import all LeanVM.Cost.FastLib
import all CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohann
import all CompPoly.LinearAlgebra.PolynomialMatrix.Shifted
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Context
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Vanishing
import all CompPoly.Univariate.Context
import all CompPoly.Univariate.BatchEval.Context
import all CompPoly.Bivariate.Basic
import all CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic
import all CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Basic
import all CompPoly.Fields.Binary.BF64.Impl
import all CompPoly.Data.Array.Lemmas
import all Init.Data.Array.Basic

/-!
# The extractor, compiled: the decoder's interpolation

`interpolateDistinct` (`Fast/DecoderFast.lean`): Lee–O'Sullivan's basis (the vanishing polynomial,
the interpolating polynomial, the rows `leeRowsFast`), its reduction by Mulders–Storjohann (the
functions of `MsReduce.lean`, reused), the least row and its normalization.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction.Fast

public section

set_option maxHeartbeats 4000000 in
cost_compile interpolateDistinctC := interpolateDistinct

end

end LeanVM.Cost.Extractor
