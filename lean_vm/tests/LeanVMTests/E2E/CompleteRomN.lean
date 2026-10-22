import LeanVM.E2E.Complete.Rom.End

/-!
# Tests: T6-prob's H-oblivious prover and T6-det without G3

`docs/roadmap/t6-prob.md` §3, §4.2–§4.5: the oblivious choices (`execOf`, `freshRun`), the
prover's failures (`honestOutN_ne_stuck`), T6-det with no good event on roots
(`idealVerify_complete_N`, decision E2E-8) and T6-prob over its pieces
(`idealVerify_complete_rom_of`, `prEvent_reject_le_not_completeOK`) rest on Lean's three axioms.
-/

namespace LeanVMTests.E2E.CompleteRomN

/-- info: 'LeanVM.E2E.Complete.chainSem_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.chainSem_congr

/-- info: 'LeanVM.E2E.Complete.execOf_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.execOf_isSome

/-- info: 'LeanVM.E2E.Complete.exists_deferred_honest_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.exists_deferred_honest_run

/-- info: 'LeanVM.E2E.Complete.honestDefer_of_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestDefer_of_N

/-- info: 'LeanVM.E2E.Complete.honestDeferN_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestDeferN_of

/-- info: 'LeanVM.E2E.Complete.honestOutN_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestOutN_child

/-- info: 'LeanVM.E2E.Complete.honestOutN_ne_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestOutN_ne_stuck

/-- info: 'LeanVM.E2E.Complete.idealOfN_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealOfN_rep

/-- info: 'LeanVM.E2E.Complete.honestOutN_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestOutN_good

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_N

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_genProve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.isTotalQueryBound_genProve

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_rom_of

/-- info: 'LeanVM.E2E.Complete.prEvent_reject_le_not_completeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.prEvent_reject_le_not_completeOK

/-- info: 'LeanVM.E2E.Complete.romPieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.romPieces

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_rom

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_rom_run

/-- info: 'LeanVM.E2E.Complete.xmssLeaf_queries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.xmssLeaf_queries_le

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_xmssLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.idealVerify_complete_rom_xmssLeaf

/-! The end theorem's statement, locked. -/

open LeanVM.E2E.Complete OracleComp OracleSpec in
example {ρ pfuel N QG QP fuel : ℕ} (hρ : LeanVM.Protocol.LeanIsa.validRate ρ) (hpf : pfuel ≤ 2 ^ 64)
    (gen : OracleComp LeanVM.HashSpec (Option HonestTree)) (hQG : IsTotalQueryBound gen QG)
    (hgen : ValidGen ρ pfuel N QP gen) (hfuel : N ≤ fuel) :
    Pr{let z ← completeExp ρ pfuel gen}[¬ CompleteOK fuel z] ≤ completeError (QG + QP) pfuel :=
  idealVerify_complete_rom hρ hpf gen hQG hgen hfuel

end LeanVMTests.E2E.CompleteRomN
