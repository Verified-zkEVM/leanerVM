/-
  LeanVM.Guest.Lift.SphincsLeaf

  `verify_sig_lean_sphincs`'s body is a leaf body: atoms, branches and arms, placing nothing.
-/

module

public import LeanVM.Guest.Lift.SphincsLeaf.Part0
public import LeanVM.Guest.Lift.SphincsLeaf.Part1
public import LeanVM.Guest.Lift.SphincsLeaf.Part2
public import LeanVM.Guest.Lift.SphincsLeaf.Part3

namespace LeanVM.Guest.Lift

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

set_option maxRecDepth 100000 in
/-- **`verify_sig_lean_sphincs`'s body is a leaf**: atoms, branches and arms, placing nothing,
checked by the kernel on ranges of its statements (those of its well-formedness check). -/
theorem sphincs_leafOk : Stmt.leafOkList anyAtom Data.core20.body = true := by
  have h914 : Stmt.leafOkList anyAtom (Data.core20.body.drop 914) = true :=
    leafOk_end (l := Data.core20.body) (by decide +kernel)
  have h910 : Stmt.leafOkList anyAtom (Data.core20.body.drop 910) = true :=
    leafOk_drop (l := Data.core20.body) (a := 910) (n := 4) sphincsLeaf_910 h914
  have h760 : Stmt.leafOkList anyAtom (Data.core20.body.drop 760) = true :=
    leafOk_drop (l := Data.core20.body) (a := 760) (n := 150) sphincsLeaf_760 h910
  have h610 : Stmt.leafOkList anyAtom (Data.core20.body.drop 610) = true :=
    leafOk_drop (l := Data.core20.body) (a := 610) (n := 150) sphincsLeaf_610 h760
  have h574 : Stmt.leafOkList anyAtom (Data.core20.body.drop 574) = true :=
    leafOk_drop (l := Data.core20.body) (a := 574) (n := 36) sphincsLeaf_574 h610
  have h538 : Stmt.leafOkList anyAtom (Data.core20.body.drop 538) = true :=
    leafOk_drop (l := Data.core20.body) (a := 538) (n := 36) sphincsLeaf_538 h574
  have h457 : Stmt.leafOkList anyAtom (Data.core20.body.drop 457) = true :=
    leafOk_drop (l := Data.core20.body) (a := 457) (n := 81) sphincsLeaf_457 h538
  have h420 : Stmt.leafOkList anyAtom (Data.core20.body.drop 420) = true :=
    leafOk_drop (l := Data.core20.body) (a := 420) (n := 37) sphincsLeaf_420 h457
  have h383 : Stmt.leafOkList anyAtom (Data.core20.body.drop 383) = true :=
    leafOk_drop (l := Data.core20.body) (a := 383) (n := 37) sphincsLeaf_383 h420
  have h346 : Stmt.leafOkList anyAtom (Data.core20.body.drop 346) = true :=
    leafOk_drop (l := Data.core20.body) (a := 346) (n := 37) sphincsLeaf_346 h383
  have h309 : Stmt.leafOkList anyAtom (Data.core20.body.drop 309) = true :=
    leafOk_drop (l := Data.core20.body) (a := 309) (n := 37) sphincsLeaf_309 h346
  have h272 : Stmt.leafOkList anyAtom (Data.core20.body.drop 272) = true :=
    leafOk_drop (l := Data.core20.body) (a := 272) (n := 37) sphincsLeaf_272 h309
  have h235 : Stmt.leafOkList anyAtom (Data.core20.body.drop 235) = true :=
    leafOk_drop (l := Data.core20.body) (a := 235) (n := 37) sphincsLeaf_235 h272
  have h150 : Stmt.leafOkList anyAtom (Data.core20.body.drop 150) = true :=
    leafOk_drop (l := Data.core20.body) (a := 150) (n := 85) sphincsLeaf_150 h235
  have h0 : Stmt.leafOkList anyAtom (Data.core20.body.drop 0) = true :=
    leafOk_drop (l := Data.core20.body) (a := 0) (n := 150) sphincsLeaf_0 h150
  simpa using h0

end
end LeanVM.Guest.Lift
