module

public import LeanerVM.Protocol.Field
meta import LeanerVM.Protocol.Field
meta import LeanerVM.Parameters.Field
meta import CompPoly.Multilinear.Basic

/-!
# Protocol Layer 0 tests: samplers and the evaluation oracle

Compiled checks (`#guard`) that the evaluation oracle on a two-variable column answers the
multilinear extension, on cube points and off them; code-generation probes that the two
samplers have compiler IR (a sampler built from `Fintype` would be noncomputable, or would
enumerate the field); and the cardinality of `E`.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Parameters LeanerVM.Protocol CompPoly OracleComp

public section

/-! ## The evaluation oracle -/

/-- The column `[1, 2, 3, 4]` on two variables: `q(0,0) = 1`, `q(1,0) = 2`, `q(0,1) = 3`,
`q(1,1) = 4`. -/
def col : Column 2 := ⟨#v[1, 2, 3, 4]⟩

/-- The oracle's answer, typed as the field element it is. -/
def answer (q : Column 2) (r : Vector E 2) : E := OracleInterface.answer q r

-- On the cube the oracle returns the table entry.
#guard answer col #v[ofK 0, ofK 0] = ofK 1
#guard answer col #v[ofK 1, ofK 0] = ofK 2
#guard answer col #v[ofK 0, ofK 1] = ofK 3
#guard answer col #v[ofK 1, ofK 1] = ofK 4
-- Off the cube it is the multilinear extension: at `(y, 0)` the value is `1 + y·(1 + 2) = 1 + 3y`
-- in characteristic two (`(1 - y)·1 + y·2`, with `-1 = 1` and `2 = x`).
#guard answer col #v[y, ofK 0] = ofK 1 + ofK 3 * y
-- And it agrees with CompPoly's evaluation of the lifted table.
#guard answer col #v[y, y ^ 2] =
  CMlPolynomialEval.evalMle (CMlPolynomialEval.map (algebraMap K E) col.values) #v[y, y ^ 2]
-- Mutation: a different column answers differently at the same point.
#guard answer ⟨#v[1, 2, 3, 5]⟩ #v[y, y ^ 2] ≠ answer col #v[y, y ^ 2]

/-! ## Samplers have compiler IR -/

/-- Compiles only if the `K` sampler is computable: a sampler through `Fintype` would not be. -/
def sampleK : ProbComp K := $ᵗ K

/-- Compiles only if the `E` sampler is computable. -/
def sampleE : ProbComp E := $ᵗ E

/-! ## Cardinality -/

example : Fintype.card E = 2 ^ 192 := card_E

end
end LeanerVMTests.Protocol
