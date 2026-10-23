/-
  LeanVM.Guest.B1.Main.Composed

  `main`'s soundness with its callees' statements discharged by their proofs, but `verify_sub`'s.
-/

module

public import LeanVM.Guest.B1.Main.Callees
public import LeanVM.Guest.B1.Main.Aggregate
public import LeanVM.Guest.B1.Da.Verify
public import LeanVM.Guest.B1.Sig.XmssSound
public import LeanVM.Guest.B1.Sig.SphincsSound

/-!
# `main`, composed

`main_sound_sub`: a run of `main`'s body whose public input cells hold the digest `D` decodes to
a statement of digest `D` held by some witness (`NodeRel`), given only `verify_sub`'s contract
(`SubSound`, B1-d's `verify_sub` statement): the signature checks (B1-e's
`verify_lean_xmss_sound_holds`, `verify_sig_lean_sphincs_sound_holds`), the DA check
(`da_verify_holds`) and the batching (`aggregate_claims_holds`) are proved.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- **A run of `main` decodes to a statement of the public input's digest, held by a witness**,
given `verify_sub`'s contract. -/
theorem main_sound_sub {bytecode : List K} (hv : SubSound bytecode)
    (hbl : bytecode.length = 2 ^ bytecodeVars) {rd : Reader} (hm : MemOk rd) {D : Digest}
    {σ : Val} (hp0 : LoadHolds rd 1 0 (digestScalars D).1) (hp1 : LoadHolds rd 1 1 (digestScalars D).2)
    (hb : Stmt.HoldsList (coreProgram.Rel rd) rd σ Data.core0.body False (fun rs => rs = [])) :
    statementDigest (decSeed σ) (decStmt σ rd) = D ∧
      ∃ w, NodeRel bytecode (decSeed σ) (decStmt σ rd) w :=
  haveI : Nonempty LeanXmss.Signature := ⟨Sig.xmssSigOf fun _ => 0⟩
  haveI : Nonempty Sphincs.Signature := ⟨Sig.sphincsSigOf fun _ => 0⟩
  haveI : Nonempty Proof := ⟨⟨[], []⟩⟩
  main_sound_exists Sig.verify_lean_xmss_sound_holds Sig.verify_sig_lean_sphincs_sound_holds hv
    Da.da_verify_holds aggregate_claims_holds hbl hm hp0 hp1 hb

end
end LeanVM.Guest.B1.Main
