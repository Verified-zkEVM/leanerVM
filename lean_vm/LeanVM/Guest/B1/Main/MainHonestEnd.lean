/-
  LeanVM.Guest.B1.Main.MainHonestEnd

  `main` placed on a node's honest run, its callees discharged: the list, digest and loop callees
  (`MainGoalsF`), the raw signatures' and the direct DA claim's (`MainGoalsG`), the children's
  loop and the aggregation taken as hypotheses.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestAt
public import LeanVM.Guest.B1.Main.MainGoalsFCl
public import LeanVM.Guest.B1.Main.MainGoalsG

/-!
# `main` on an honest run, its callees discharged

`mainGoals_of`: `MainGoals` from `NodeRel`, `Limits`, a bytecode of `2^23` words, the signature
schemes' completeness (B1-e), the frame runs' certificate facts (`Lift.RunsFit`), and the
children's loop and aggregation (`MainGoalL5`, `MainGoalAg`). `main_honest_end`:
`main_honest_relAtInW` on those.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

theorem log2_of_length (hbl : bytecode.length = 2 ^ 23) : Nat.log2 bytecode.length = 23 := by
  rw [hbl]; exact Nat.log2_two_pow

/-- **`main`'s callees on the honest run**, but the children's loop and the aggregation. -/
theorem mainGoals_of (hbl : bytecode.length = 2 ^ 23) (hr : NodeRel bytecode seed s w)
    (hl : Limits bytecode s w) (hxc : Sig.verify_lean_xmss_complete_Spec)
    (hsc : Sig.verify_sig_lean_sphincs_complete_loads_Spec) (hrf : Lift.RunsFit fs cert)
    (hl5 : MainGoalL5 fs cert fp seed s w) (hag : MainGoalAg fs cert fp seed s w) :
    MainGoals fs cert fp seed s w where
  l0 := mainGoalL0 fs cert fp seed s w
  dl := mainGoalDl fs cert fp seed s w hl
  clx := mainGoalClX fs cert fp seed s w hl
  cls := mainGoalClS fs cert fp seed s w hl
  l1 := mainGoalL1 fs cert fp seed s w
  l2 := mainGoalL2 fs cert fp seed s w
  l3 := mainGoalL3 (fs := fs) (cert := cert) (fp := fp) hr hl hxc
  l4 := mainGoalL4 (fs := fs) (cert := cert) (fp := fp) hr hl hsc
  dv := mainGoalDv (fs := fs) (cert := cert) (fp := fp) hr hrf
  cv := mainGoalCv (fs := fs) (cert := cert) (fp := fp) hl
  l5 := hl5
  ag := hag
  st := mainGoalSt fs cert fp seed s w hr hbl

/-- **`main` at `fp` on the honest run**: `main_honest_relAtInW`, its callees discharged but the
children's loop and the aggregation. -/
theorem main_honest_end (hbl : bytecode.length = 2 ^ 23) (hr : NodeRel bytecode seed s w)
    (hl : Limits bytecode s w) (hf : FreshShaped w) (hxc : Sig.verify_lean_xmss_complete_Spec)
    (hsc : Sig.verify_sig_lean_sphincs_complete_loads_Spec) (hrf : Lift.RunsFit fs cert)
    (hl5 : MainGoalL5 fs cert fp seed s w) (hag : MainGoalAg fs cert fp seed s w) :
    ∃ (n : ℕ) (L : B1.Main.Layout), Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ hLmain fs fp seed s w, q ∈ L) ∧
      ∀ rd, LowDef 16 rd → B1.Main.MemL rd L →
        LoadHolds rd 1 0 (digestScalars (statementDigest seed s)).1 →
        LoadHolds rd gen 0 (digestScalars (statementDigest seed s)).2 →
        RelAtInW coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun σ => MVals rd σ (hm fs fp seed s w)) :=
  main_honest_relAtInW (log2_of_length hbl) hr hl hf
    (mainGoals_of hbl hr hl hxc hsc hrf hl5 hag)

end
end LeanVM.Guest.B1.Main
