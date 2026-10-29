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
theorem mByte_ok : (List.range 256).all (fun v =>
    (atomsIn mFlatE).any (atomEqb (.const (.n (69 + v)) (word v 0 0)))) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mLeafC_ok : (List.range 23).all (fun k =>
    (atomsIn mFlatE).any (atomEqb (.const (.n (406 + k)) (word 0 0 0)))) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Each block's stores. -/
theorem mStoresIn :
    (atomsIn (mPre ++ mMid ++ mPost)).filter (fun a => decide (a ∈ mStoresL)) =
      (List.range 256).map (fun v => .load (.n (69 + v)) (.n 68) v) ++ [.load (.n 381) (.n 380) 0] ∧
    (atomsIn mDa).filter (fun a => decide (a ∈ mStoresL)) =
      [.load (.n 349) (.n 336) 0, .load (.n 350) (.n 336) 1] ∧
    (atomsIn mDaZ).filter (fun a => decide (a ∈ mStoresL)) =
      [.load (.n 362) (.n 336) 0, .load (.n 363) (.n 336) 1] ∧
    (atomsIn mLeaf).filter (fun a => decide (a ∈ mStoresL)) =
      (List.range 23).map (fun k => .load (.n (406 + k)) (.n 402) k) ++
        [.load (.n 405) (.n 402) 23] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mDaZC_ok : (atomsIn mDaZ).any (atomEqb (.const (.n 362) (word 0 0 0))) = true ∧
    (atomsIn mDaZ).any (atomEqb (.const (.n 363) (word 0 0 0))) = true := by decide +kernel

/-- The own DA claim's digest, its chain on `mDa`'s atoms but the stores. -/
noncomputable def daSpec : ChainSpec := pairSpec (.n 339) (.n 340) (.n 341) (.n 342) (noStores mDa)

set_option maxRecDepth 100000 in
theorem daSpec_ok : daSpec.check (noStores mDa) = true ∧
    daSpec.outV (daSpec.nb - 1) 0 = .n 349 ∧ daSpec.outV (daSpec.nb - 1) 1 = .n 350 := by
  decide +kernel

end
end LeanVM.Guest.B1.Main
