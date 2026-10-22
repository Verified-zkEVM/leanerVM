import LeanVM.E2E.Headline
import LeanVM.E2E.Complete.Rom.PadRec
import LeanVM.E2E.Complete.Rom.RootGen

/-!
# T6-prob at any depth, locked

Statement locks of `LeanVM/E2E/Complete/Rom/PadRec.lean`: from L2 padded
(`guestCompleteModel_big`), every node has an execution of at least 22 stacked variables, every
output of the H-oblivious prover announces a stack log in `[22, 28]`, the limits on the tree give
the prover's with no depth restriction, and T6-prob (unbudgeted, with the game's budget, at the
headline's `viCost N`) holds for every generator of valid trees of any depth within `LimitsT`
(`ValidGenR`); each at Lean's three axioms. `ValidGenR` is `ValidGenT` without `KidsLeaves`,
inhabited by the two-level generator.
-/

open LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Rom
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.Blake2sHash LeanVM.Semantics
open LeanVM.Node LeanVM.Guest LeanVM.E2E LeanVM.E2E.Complete
open OracleComp OracleSpec
open scoped ENNReal

/-! ## L2, padded -/

example : GuestCompleteModelBig := guestCompleteModel_big

/-- info: 'LeanVM.E2E.Complete.guestCompleteModel_big' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guestCompleteModel_big

/-! ## Every node has a big execution -/

example (H : Bytes → Digest) {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow
      End.bytecode (seedOf H) s w) (hlim : End.Limits s w) (hcaps : CapsAgreeWith H (seedOf H) w)
    (hbud : B2C.b2cBudget'.size (End.work s w) ≤ 2 ^ 28) :
    ∃ e : NodeExecOn (nodeLog H s w) H (digestOf H s) w, 22 ≤ leanIsaμ guest e.1.sz :=
  nodeExec_nodeLog_bigG H hrel hlim hcaps hbud

/-- info: 'LeanVM.E2E.Complete.nodeExec_nodeLog_bigG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeExec_nodeLog_bigG

/-! ## Every child announces a stack log in `[22, 28]` -/

example (H : Bytes → Digest) {ρ : ℕ} (pfuel : ℕ)
    (hρ : validRate ρ) (T : HonestTree) (hv : T.AllNodes (HonestTree.ValidAt H))
    (hl : T.AllNodes HonestTree.LimitsT) (o : HonestOutN) (h : honestOutN H ρ pfuel T = .ok o)
    (layout : Layout) (r : ℕ)
    (hann : Verifier.announced End.bytecode o.proof.stream = some (layout, r)) :
    22 ≤ layout.stackLog ∧ layout.stackLog ≤ 28 :=
  honestOutN_stackLog H ρ pfuel hρ T hv hl o h layout r hann

/-- info: 'LeanVM.E2E.Complete.honestOutN_stackLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honestOutN_stackLog

/-! ## The limits on the tree give the prover's, at any depth -/

example (H : Bytes → Digest) {ρ : ℕ} (pfuel : ℕ)
    (hρ : validRate ρ) (T : HonestTree) (hv : T.AllNodes (HonestTree.ValidAt H))
    (hl : T.AllNodes HonestTree.LimitsT) : T.WithinLimitsN H ρ pfuel :=
  withinLimitsN_of_TR H ρ pfuel hρ T hv hl

/-- info: 'LeanVM.E2E.Complete.withinLimitsN_of_TR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinLimitsN_of_TR

/-! ## Generators of trees of any depth -/

example (ρ pfuel N QP : ℕ) (gen : OracleComp HashSpec (Option HonestTree)) :
    ValidGenR ρ pfuel N QP gen ↔
      (∀ T, some T ∈ support gen → T.proverQueries ρ pfuel ≤ QP) ∧
      ∀ z ∈ support ((simulateQ loggedRO gen).run []), ∀ T, z.1 = some T →
        T.size ≤ N ∧ T.AllNodes HonestTree.ShapeOK ∧ T.AllNodes HonestTree.LimitsT ∧
          ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) → T.Valid Ht :=
  Iff.rfl

example {ρ pfuel N QP : ℕ} {gen : OracleComp HashSpec (Option HonestTree)}
    (h : ValidGenT ρ pfuel N QP gen) : ValidGenR ρ pfuel N QP gen :=
  validGenR_of_T h

/-- `ValidGenR` is inhabited: the two-level generator. -/
example (ρ pfuel : ℕ) : ValidGenR ρ pfuel 2 (2 * nodeQueries pfuel) xmssRootGen :=
  validGenR_of_T (validGenT_xmssRootGen ρ pfuel)

example {ρ pfuel N QP : ℕ} (hρ : validRate ρ)
    {gen : OracleComp HashSpec (Option HonestTree)} (h : ValidGenR ρ pfuel N QP gen) :
    ValidGen ρ pfuel N QP gen :=
  validGen_of_R hρ h

/-- info: 'LeanVM.E2E.Complete.validGen_of_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validGen_of_R

/-! ## T6-prob at any depth -/

example {ρ pfuel N QG QP fuel : ℕ} (hρ : validRate ρ)
    (hpf : pfuel ≤ 2 ^ 64) (gen : OracleComp HashSpec (Option HonestTree))
    (hQG : IsTotalQueryBound gen QG) (hgen : ValidGenR ρ pfuel N QP gen) (hfuel : N ≤ fuel) :
    Pr{let z ← completeExp ρ pfuel gen}[¬ CompleteOK fuel z] ≤ completeError (QG + QP) pfuel :=
  idealVerify_complete_rom_rec hρ hpf gen hQG hgen hfuel

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealVerify_complete_rom_rec

example {nx ns ρ pfuel N QG QP budget : ℕ} (hρ : validRate ρ)
    (hpf : pfuel ≤ 2 ^ 64) (gen : OracleComp HashSpec (Option HonestTree))
    (hQG : IsTotalQueryBound gen QG) (hgen : ValidGenR ρ pfuel N QP gen)
    (hB : N * viNodeBound ≤ budget) :
    Pr{let z ← completeRunGame (nx := nx) (ns := ns) ρ pfuel gen N budget}[z.1 = some false] ≤
      completeError (QG + QP) pfuel :=
  idealVerify_complete_rom_rec_budget hρ hpf gen hQG hgen hB

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_rec_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealVerify_complete_rom_rec_budget

example {nx ns ρ pfuel N QG QP : ℕ} (hρ : validRate ρ)
    (hpf : pfuel ≤ 2 ^ 64) (gen : OracleComp HashSpec (Option HonestTree))
    (hQG : IsTotalQueryBound gen QG) (hgen : ValidGenR ρ pfuel N QP gen) :
    Pr{let z ← completeRunGame (nx := nx) (ns := ns) ρ pfuel gen N (viCost N)}[z.1 = some false] ≤
      completeError (QG + QP) pfuel :=
  idealVerify_complete_rom_rec_budget hρ hpf gen hQG hgen (by rw [viCost, viNodeCost_eq])
