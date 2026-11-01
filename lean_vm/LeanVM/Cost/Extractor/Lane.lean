module

public import LeanVM.Cost.Extractor.GsRun
public import LeanVM.Protocol.Extraction.Fast.DecodeAdmissible
import all CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohann
import all CompPoly.LinearAlgebra.PolynomialMatrix.Shifted
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Context
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Raw.Modular
import all CompPoly.Univariate.Vanishing
import all CompPoly.Univariate.Context
import all CompPoly.Univariate.Roots.Backend
import all CompPoly.Univariate.Roots.Context
import all CompPoly.Univariate.Roots.Extraction
import all CompPoly.Univariate.Roots.RootProduct
import all CompPoly.Univariate.Roots.Splitter
import all CompPoly.Univariate.Roots.Shoup
import all CompPoly.Bivariate.Basic
import all CompPoly.Bivariate.GuruswamiSudan.Root.Common
import all CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots
import all CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
import all CompPoly.Fields.Binary.BF64.Impl
import all CompPoly.Data.Array.Lemmas
import all Init.Data.Array.Basic
import all LeanVM.Cost.FastLib

import all CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Algorithm
import all CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness

import all LeanVM.Protocol.Extraction.Extractor
import all Init.Data.List.Sort.Basic

/-!
# The extractor, compiled: one lane's candidates

`laneEncodedDistinct` (`Fast/DecodeAdmissible.lean`): the lane's points, its Guruswami–Sudan run
(`GsRun.lean`, reused), the candidates in the novel basis (`toNovelFast`), deduplicated and
sorted, each with its re-encoding (`novelFwd`).
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction.Fast

public section

cost_compile laneEncodedDistinctC := laneEncodedDistinct

end

end LeanVM.Cost.Extractor
