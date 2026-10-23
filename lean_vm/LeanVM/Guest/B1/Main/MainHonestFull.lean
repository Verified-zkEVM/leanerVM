/-
  LeanVM.Guest.B1.Main.MainHonestFull

  **`main`'s completeness on a node's honest run**, every callee discharged but each child's
  `verify_sub` and the signature schemes, with `main`'s tree exposed: its node's valuation holds
  `main`'s honest values, and its children's loop's tree the children's counts.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5T

/-!
# `main` on an honest run, its tree exposed

`main_honest_fullT`: for `NodeRel` within `Limits` and a bytecode of `2^23` words, from the
signature schemes' completeness (B1-e), the frame runs' certificate facts and each child's
`verify_sub` (`VerifySubGoals`, B1-d): a layout `L` within `[fp, fp + n)`, above `main`'s frame,
pairwise disjoint, containing `main`'s honest words; on every memory holding `L` and the
statement's digest at words `0`, `1`, `main` holds at `fp` by a tree `.node "main" σ bufs ks`
with `MVals rd σ` of the honest oracle (its hinted counts among them) and its callees' trees
satisfying `mTs … (L5Hinted w)`: the children's loop's iterations hold each child's counts.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- **`main`'s completeness on the honest run, its tree exposed.** -/
theorem main_honest_fullT (hbl : bytecode.length = 2 ^ 23) (hr : NodeRel bytecode seed s w)
    (hl : Limits bytecode s w) (hxc : Sig.verify_lean_xmss_complete_Spec)
    (hsc : Sig.verify_sig_lean_sphincs_complete_loads_Spec) (hrf : Lift.RunsFit fs cert)
    (hV : VerifySubGoals fs cert fp seed s w) :
    ∃ (n : ℕ) (L : B1.Main.Layout), Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ hLmain fs fp seed s w, q ∈ L) ∧
      ∀ rd, LowDef 16 rd → B1.Main.MemL rd L →
        LoadHolds rd 1 0 (digestScalars (statementDigest seed s)).1 →
        LoadHolds rd gen 0 (digestScalars (statementDigest seed s)).2 →
        RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧ MVals rd σ (hm fs fp seed s w) ∧
            KidsT (mCalls σ (hm fs fp seed s w))
              ((fun _ => True) :: mTs (hm fs fp seed s w) (L5Hinted w)) ks) :=
  main_honest_relAtInT hbl hr hl hxc hsc hrf (mainGoalL5T hbl hr hl hV)
    (mainGoalAg (fs := fs) (fp := fp) (cert := cert) hbl hr hl)

end
end LeanVM.Guest.B1.Main
