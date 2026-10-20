/-
  LeanVM.Guest.Located.Main

  `main`'s callees on the located call relation, their witnesses read off the memory.
-/

module

public import LeanVM.Guest.Located.Xmss
public import LeanVM.Guest.Located.Sphincs
public import LeanVM.Guest.Located.Da
public import LeanVM.Guest.B1.Main.SoundW
public import LeanVM.Guest.B1.Main.Discharge
public import LeanVM.Guest.End

/-!
# `main`'s callees, located

`B1.Main.main_sound_w` takes `main`'s callees for a call relation `C` with their hash witnesses
given by functions of the calls' words (`B1.Main.CalleesW`). On the located relation
(`Check.RL coreProgram L certByName`) every one of them is read off the memory:

* the signatures by `xmssWit`, `sphincsWit`, the blob matrix by `wDaL`;
* the batching's hints by `wAL`, those of the `aggregate_claims` call's frame;
* the child proofs by any `wV` for which `verify_sub`'s located calls verify (`calleesW_located`'s
  hypothesis, discharged by `Located.VerifySub`);

and the callees without a hash witness are the ones B1 proves (`callees_proved`), a located call
being a call (`relL_le_rel`).
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 LeanVM.Guest.B1.Main

@[expose] public section

/-- **The batching's hints of an `aggregate_claims` call**: those of the call's frame. -/
noncomputable def wAL {κ : ℕ} (L : MemImage κ) (args rets : List E) : BatchHints :=
  frameDec L "aggregate_claims" (aggHints L.read) args rets

theorem wAL_out {κ : ℕ} {L : MemImage κ} {args rets : List E}
    (h : RL coreProgram L certByName "aggregate_claims" args rets) :
    MeaningAggW L.read args rets (wAL L args rets) := by
  exact frameDec_spec find_aggregate_claims h fun _ hp hb ↦
    aggregate_claims_sound_w hp (holdsList_mono (relL_le_rel _) _ id (fun _ h ↦ h) hb)

/-- **`main`'s callees, located**: on a memory of a valid execution, with the child proofs of `wV`
verifying on every located call of `verify_sub`. -/
theorem calleesW_located {κ : ℕ} {L : MemImage κ} (hm : MemOk L.read) {wV : List E → Proof}
    (hvs : ∀ pi0 pi1 s0 s1 glp gsq out, ExpTables L.read glp gsq →
      RL coreProgram L certByName "verify_sub" [pi0, pi1, s0, s1, glp, gsq, out] [] →
        ∃ (pi iv : Digest) (fresh : FixedClaims), (pi0, pi1) = digestScalars pi ∧
          (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧ ReadsAt L.read out (fixedCells fresh) ∧
          verifyDeferred End.bytecode iv pi fresh (wV [pi0, pi1, s0, s1, glp, gsq, out]) = true) :
    CalleesW End.bytecode L.read (RL coreProgram L certByName) (xmssWit L) (sphincsWit L) (wDaL L)
      wV (wAL L) where
  exponent_tables p q h := (exponent_tables_iff L.read [] [p, q]).mp (relL_le_rel _ _ _ _ h)
  verify_lean_xmss _ h := xmssWit_out h
  verify_sig_lean_sphincs _ h := sphincsWit_out h
  statement_digest _ _ _ _ _ _ _ _ h :=
    (callees_proved End.bytecode_length _ hm).statement_digest _ _ _ _ _ _ _ _ (relL_le_rel _ _ _ _ h)
  claim_list_digest _ _ _ _ _ hsq h :=
    (callees_proved End.bytecode_length _ hm).claim_list_digest _ _ _ _ _ hsq (relL_le_rel _ _ _ _ h)
  child_claim_list_digest _ _ _ _ _ _ _ _ _ hsq h :=
    (callees_proved End.bytecode_length _ hm).child_claim_list_digest _ _ _ _ _ _ _ _ _ hsq
      (relL_le_rel _ _ _ _ h)
  da_list_digest _ _ _ _ h :=
    (callees_proved End.bytecode_length _ hm).da_list_digest _ _ _ _ (relL_le_rel _ _ _ _ h)
  cover_da_root _ _ _ _ _ _ _ _ h :=
    (callees_proved End.bytecode_length _ hm).cover_da_root _ _ _ _ _ _ _ _ (relL_le_rel _ _ _ _ h)
  da_verify _ _ _ _ _ hsq h := daWit_out hm (squaresAt_of_table hsq) h
  verify_sub := hvs
  aggregate_claims _ _ h := wAL_out h

end
end LeanVM.Guest.Located
