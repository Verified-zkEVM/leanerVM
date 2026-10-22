import LeanVM.E2E.Complete.Rom.RootGen

/-!
# T6-prob's recursion, locked

Statement locks of `LeanVM/E2E/Complete/Rom/{StreamCap,Pad,LimitsT,RootGen}.lean`: an accepted
proof's stream within the guest's cap; a node without children has a padded execution of at least
22 stacked variables, which the chooser takes; the limits as a condition on the tree; the two-level
inhabitant (a root over the honest leanXMSS leaf) and its bound; each at Lean's three axioms.
-/

open LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Rom
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.LeanIsa
open LeanVM.Node LeanVM.Guest LeanVM.E2E LeanVM.E2E.Complete
open OracleComp OracleSpec
open scoped ENNReal

/-! ## The stream cap -/

example (H : Bytes → Digest) {ρ pfuel : ℕ} (hρ : validRate ρ) {T : HonestTree} {o : HonestOutN}
    (h : honestOutN H ρ pfuel T = .ok o) : o.proof.stream.length ≤ Hints.streamCap :=
  honestOutN_stream_le H hρ h

/-- info: 'LeanVM.E2E.Complete.honestOutN_stream_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honestOutN_stream_le

/-! ## The padded execution -/

example (H : Bytes → Digest) {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow
      End.bytecode (seedOf H) s w) (hlim : End.Limits s w) (hcaps : CapsAgreeWith H (seedOf H) w)
    (hbud : B2C.b2cBudget'.size (End.work s w) ≤ 2 ^ 28) (hleaf : w.children = []) :
    ∃ e : NodeExecOn (nodeLog H s w) H (digestOf H s) w, 22 ≤ leanIsaμ guest e.1.sz :=
  nodeExec_nodeLog_big H hrel hlim hcaps hbud hleaf

/-- info: 'LeanVM.E2E.Complete.nodeExec_nodeLog_big' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeExec_nodeLog_big

/-! ## The limits on the tree -/

example (H : Bytes → Digest) (ρ pfuel : ℕ) (hρ : validRate ρ) (T : HonestTree)
    (hv : T.AllNodes (HonestTree.ValidAt H)) (hl : T.AllNodes HonestTree.LimitsT)
    (hk : T.AllNodes HonestTree.KidsLeaves) : T.WithinLimitsN H ρ pfuel :=
  withinLimitsN_of_T H ρ pfuel hρ T hv hl hk

/-- info: 'LeanVM.E2E.Complete.withinLimitsN_of_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinLimitsN_of_T

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealVerify_complete_rom_T

/-! ## The two-level inhabitant -/

example (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    xmssRoot pk σ = .node ⟨[(pk, 0)], [], []⟩ [.child 0] [] [] [xmssLeaf pk σ] := rfl

example (ρ pfuel : ℕ) : ValidGenT ρ pfuel 2 (2 * nodeQueries pfuel) xmssRootGen :=
  validGenT_xmssRootGen ρ pfuel

/-- info: 'LeanVM.E2E.Complete.validGenT_xmssRootGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validGenT_xmssRootGen

example : Pr{let z ← completeExp 1 (2 ^ 25) xmssRootGen}[¬ CompleteOK 2 z] ≤ (2 : ℝ≥0∞)⁻¹ ^ 124 :=
  idealVerify_complete_rom_xmssRoot

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_rom_xmssRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealVerify_complete_rom_xmssRoot
