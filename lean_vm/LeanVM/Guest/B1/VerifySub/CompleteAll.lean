/-
  LeanVM.Guest.B1.VerifySub.CompleteAll

  `verify_sub` is complete with no hypothesis left: `verify_keccak`'s completeness discharged.
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteB
public import LeanVM.Guest.B1.KeccakGkr.VkCV
public import LeanVM.Guest.B1.KeccakGkr.VkCW

/-!
# `verify_sub`, complete

* `verify_sub_complete_all`: `verify_sub_complete_Spec` for the guest's `2^23` bytecode words,
  `verify_keccak`'s placed completeness (`verify_keccak_completeAt`) discharging the last callee.
* `verify_sub_completeB_fs`: the bounded form at the deployed frame sizes `B2C.fs`, within
  `vsBound W vkBound` words for the callees' words facts `W : VsWords B2C.fs`
  (`verify_keccak_completeAtB_fs`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main

@[expose] public section

/-- **`verify_sub` is complete on every honest child.** -/
theorem verify_sub_complete_all {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) :
    verify_sub_complete_Spec bytecode :=
  verify_sub_complete hbl fun _ _ _ _ κ _ ↦ verify_keccak_completeAt κ

/-- **`verify_sub` is complete within its words** at the deployed frame sizes. -/
theorem verify_sub_completeB_fs {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {cert : String → V → ℕ} (hrf : Lift.RunsFit LeanVM.Guest.B2C.fs cert)
    (hap : Lift.RunsApart cert) (W : VsWords LeanVM.Guest.B2C.fs) {κ : ℕ} (hκ : 16 ≤ κ)
    (seed : Digest) (c : Child) (lpE sqE outE : ℕ) (Lin : Main.Layout)
    (hmu : ∀ layout r, Verifier.announced bytecode c.proof.stream = some (layout, r) →
      Hints.muMin ≤ layout.stackLog)
    (hst : c.proof.stream.length ≤ Hints.streamCap)
    (hnz : Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.fresh
      c.proof = true)
    (hcaps : ∀ b ∈ Limits.queriesOf (deferredProgram c.fresh bytecode
      (statementDigest seed c.statement)) (Hints.childStart seed c), Limits.BatchAgrees b.1 b.2)
    (hexpL : ∀ q ∈ log2Lin lpE sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.fresh) ∈ Lin) :
    CompleteAtDTB LeanVM.Guest.B2C.fs cert κ "verify_sub" Lin
      [(digestScalars (statementDigest seed c.statement)).1,
        (digestScalars (statementDigest seed c.statement)).2, (digestScalars seed).1,
        (digestScalars seed).2, ofK (gpow lpE), ofK (gpow sqE), ofK (gpow outE)] (Returns [])
      (fun _ ↦ True) (vsBound W vkBound) :=
  verify_sub_completeB hbl hrf hap W hκ (verify_keccak_completeAtB_fs κ) seed c lpE sqE outE Lin
    hmu hst hnz hcaps hexpL hout

end
end LeanVM.Guest.B1.VerifySub
