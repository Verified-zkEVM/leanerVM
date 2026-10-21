/-
  LeanVM.Guest.Located.MainB

  `main`'s callees on the located call relation under a hash model's semantics, their witnesses
  read off the memory (`Located/Main.lean` over a `HashModel`).
-/

module

public import LeanVM.Guest.Located.SigB
public import LeanVM.Guest.Located.InterfaceM
public import LeanVM.Guest.Located.Main
public import LeanVM.Guest.B1.Main.SoundWM
public import LeanVM.Guest.B1.Main.DischargeM

/-!
# `main`'s callees, located, over a hash model

`calleesW_located` over a hash model `M`: on the located relation under `M.sem`
(`Check.RLB M.sem coreProgram L certByName`) every callee of `main` holds its outcome over the
model (`B1.Main.CalleesWM`) at the witnesses decoded under `M.sem`:

* the signatures by `xmssWitB`, `sphincsWitB`, the blob matrix by `wDaLB` (`Located/SigB.lean`,
  `Located/DaB.lean`), at any named frames `fr` (decision E2E-5);
* the batching's hints by `wALB`, those of the `aggregate_claims` call's frame, closing the
  batching from the baked start `aggSeedD` over the model (`Main.aggregate_claims_sound_wM`);
* the child proofs by any `wV` for which `verify_sub`'s located calls verify over the model
  (`calleesWM_located`'s hypothesis, discharged by `vsWit_outM`);

and the callees without a hash witness by the model lemmas of `Main.DischargeM`.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Value LeanVM.Guest.B1 LeanVM.Guest.B1.Main

@[expose] public section

/-- **The batching's hints of an `aggregate_claims` call, under `S`** (`wAL`). -/
noncomputable def wALB (S : BlakeSem) (fr : String → List E → Option ℕ) {κ : ℕ} (L : MemImage κ)
    (args rets : List E) : BatchHints :=
  frameDecB S fr L "aggregate_claims" (aggHints L.read) args rets

theorem wALB_deployed {κ : ℕ} (L : MemImage κ) : wALB blakeDeployed (fun _ _ ↦ none) L = wAL L := by
  funext args rets
  simp only [wALB, wAL, frameDecB_deployed]

variable {M : HashModel} {fr : String → List E → Option ℕ}

/-- **A located call of `aggregate_claims` under the model's semantics** (`wAL_out`): the batching
from the baked start closes over the model with the decoded hints. -/
theorem wAL_outM {κ : ℕ} {L : MemImage κ} (hbs : BatchSumcheckM M L.read) {args rets : List E}
    (h : RLB M.sem coreProgram L certByName "aggregate_claims" args rets) :
    MeaningAggWM M aggSeedD L.read args rets (wALB M.sem fr L args rets) :=
  frameDecB_spec find_aggregate_claims h fun _ hp hb ↦
    aggregate_claims_sound_wM hbs hp (holdsListB_mono (relLB_le_rel _) _ id (fun _ h ↦ h) hb)

/-- **`main`'s callees, located, over a hash model** (`calleesW_located`): on a memory of a valid
execution, with `batch_sumcheck` sound over the model and the child proofs of `wV` accepted over
the model on every located call of `verify_sub`. -/
theorem calleesWM_located {κ : ℕ} {L : MemImage κ} (hm : MemOk L.read)
    (hbs : BatchSumcheckM M L.read) {wV : List E → Proof}
    (hvs : ∀ pi0 pi1 s0 s1 glp gsq out, ExpTables L.read glp gsq →
      RLB M.sem coreProgram L certByName "verify_sub" [pi0, pi1, s0, s1, glp, gsq, out] [] →
        ∃ (pi iv : Digest) (fresh : FixedClaims), (pi0, pi1) = digestScalars pi ∧
          (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧ ReadsAt L.read out (fixedCells fresh) ∧
          verifyDeferredWith M.H End.bytecode iv pi fresh (wV [pi0, pi1, s0, s1, glp, gsq, out]) =
            some true) :
    CalleesWM M aggSeedD End.bytecode L.read (RLB M.sem coreProgram L certByName)
      (xmssWitB M.sem fr L) (sphincsWitB M.sem fr L) (wDaLB M.sem fr L) wV (wALB M.sem fr L) where
  exponent_tables := exponent_tables_soundM (relLB_le_rel _)
  verify_lean_xmss _ h := xmssWit_outM h
  verify_sig_lean_sphincs _ h := sphincsWit_outM h
  statement_digest := statement_digest_soundM (relLB_le_rel _)
  claim_list_digest := claim_list_digest_soundM hm (relLB_le_rel _)
  child_claim_list_digest := child_claim_list_digest_soundM hm (relLB_le_rel _)
  da_list_digest := da_list_digest_soundM (relLB_le_rel _)
  cover_da_root := cover_da_root_soundM hm (relLB_le_rel _)
  da_verify _ _ _ _ _ hsq h := daWit_outM hm (squaresAt_of_table hsq) h
  verify_sub := hvs
  aggregate_claims _ _ h := wAL_outM hbs h

end
end LeanVM.Guest.Located
