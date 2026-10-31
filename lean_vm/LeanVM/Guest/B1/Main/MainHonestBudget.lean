/-
  LeanVM.Guest.B1.Main.MainHonestBudget

  `main`'s completeness on a node's honest run, its callees' trees of honest shape where the
  budget needs them: its claim lists' digests (`clHonest`), each child's (`ccHonest`),
  `aggregate_claims` (`aggHonest`); `da_verify`'s and each `verify_sub`'s by given predicates.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestFull
public import LeanVM.Guest.B1.Main.MainGoalsHClT
public import LeanVM.Guest.B1.Main.MainGoalsHAgT
public import LeanVM.Guest.B1.Main.MainGoalsDvT

/-!
# `main` on an honest run, for the budget

`mainPredsH w Pd Pvs`: `main`'s callees' predicates, of honest shape on its claim lists' digests,
each child's and `aggregate_claims`; `Pd` on `da_verify`'s, `Pvs c` on child `c`'s
`verify_sub`'s. `main_honest_budget`: `main_honest_fullT` with those.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within CompleteAtDT Returns)

@[expose] public section

/-- **`main`'s callees' predicates for the budget.** -/
def mainPredsH (s : NodeStatement) (w : NodeWitness) (Pd : Tree → Prop) (Pvs : ℕ → Tree → Prop) :
    MainPreds :=
  ⟨clHonest s.claims.xmss.length, clHonest s.claims.sphincs.length, Pd, aggHonest w.children.length,
    L5Hinted w (fun c => ccHonest (hKid s w c).ex) (fun c => ccHonest (hKid s w c).es) Pvs⟩

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- **`main`'s completeness on the honest run, for the budget**: `main_honest_fullT`, its claim
lists' digests', each child's and `aggregate_claims`' trees of honest shape, `da_verify`'s
satisfying `Pd`, child `c`'s `verify_sub`'s `Pvs c`. -/
theorem main_honest_budget (hbl : bytecode.length = 2 ^ 23) (hr : NodeRelation bytecode seed s w)
    (hl : Limits s w) (hxc : Sig.verify_lean_xmss_complete_Spec)
    (hsc : Sig.verify_sig_lean_sphincs_complete_loads_Spec) (hrf : Lift.RunsFit fs cert)
    {Pd : Tree → Prop} {Pvs : ℕ → Tree → Prop} (hV : VerifySubGoalsT fs cert fp seed s w Pvs)
    (hdv : (hm fs fp seed s w).nd = 1 →
      CompleteAtDT fs cert 16 "da_verify" (hLmain fs fp seed s w) [(hm fs fp seed s w).et2]
        (Returns (hm fs fp seed s w).daR) Pd) :
    ∃ (n : ℕ) (L : B1.Main.Layout), Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ hLmain fs fp seed s w, q ∈ L) ∧
      ∀ rd, LowDef 16 rd → B1.Main.MemL rd L →
        LoadHolds rd 1 0 (digestScalars (statementDigest seed s)).1 →
        LoadHolds rd gen 0 (digestScalars (statementDigest seed s)).2 →
        RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧ MVals rd σ (hm fs fp seed s w) ∧
            KidsT (mCalls σ (hm fs fp seed s w))
              ((fun _ => True) :: mTs (hm fs fp seed s w) (mainPredsH s w Pd Pvs)) ks ∧
            calls (mEvs σ) = mCalls σ (hm fs fp seed s w) ∧ bufs = mSizes (hData seed s w)) :=
  main_honest_fullT hbl hr hl hxc hsc hrf hV (childListGoalsT_honest cert hl)
    (mainGoalClXT fs cert fp seed s w hl) (mainGoalClST fs cert fp seed s w hl) hdv
    (mainGoalAgT fs fp cert hbl hr hl)

end
end LeanVM.Guest.B1.Main
