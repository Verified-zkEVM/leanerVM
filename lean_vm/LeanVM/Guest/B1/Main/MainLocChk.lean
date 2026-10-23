/-
  LeanVM.Guest.B1.Main.MainLocChk

  Where `main`'s evaluated block defines the values its completeness reads (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Main.MainCChk

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem mOrcStmts_ok : mOrcStmts.all (fun s => mFlatE.any (stmtEqb · s)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mDefAtoms_ok : mDefAtoms.all (fun a => (atomsIn mFlatE).any (atomEqb a)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mStores_eq : mStores = mStoresL := by decide +kernel

set_option maxRecDepth 100000 in
theorem mPair_out : (pairSpec (.n 81) (.n 82) (.n 83) (.n 84) (atomsIn mPre)).outV
    ((pairSpec (.n 81) (.n 82) (.n 83) (.n 84) (atomsIn mPre)).nb - 1) 0 = .n 103 ∧
    (pairSpec (.n 81) (.n 82) (.n 83) (.n 84) (atomsIn mPre)).outV
    ((pairSpec (.n 81) (.n 82) (.n 83) (.n 84) (atomsIn mPre)).nb - 1) 1 = .n 104 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mByte_ok : (List.range 256).all (fun v =>
    (atomsIn mFlatE).any (atomEqb (.const (.n (120 + v)) (word v 0 0)))) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mLeafC_ok : (List.range 23).all (fun k =>
    (atomsIn mFlatE).any (atomEqb (.const (.n (421 + k)) (word 0 0 0)))) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mPair_ok : pairHashOk (atomsIn mPre) (.n 81) (.n 82) (.n 83) (.n 84) (.n 116) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mNoLeafStore : ((atomsIn (mPre ++ mMid ++ mPost)).all fun a => !isLeafStore a) = true ∧
    ((atomsIn mDa).all fun a => !isLeafStore a) = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
