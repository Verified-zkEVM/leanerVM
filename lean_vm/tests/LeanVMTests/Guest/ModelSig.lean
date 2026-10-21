import LeanVM.Guest.B1.Sig.Model.Callees
import LeanVM.E2E.Runs

/-!
# Tests: the signature verifiers under a hash model (W2, `B1/Sig`)

* The model lemmas of `B1/Sig/Model/` (the compressions as answered hashes, the WOTS+C codeword,
  `hash_values`, the Merkle paths, the forest, the schemes run in `Option`, both verifiers and their
  meanings as `main`'s callees) rest on Lean's three axioms.
* **At the deployed model they are the deployed statements**: with `xmssVerifyWith_some_blake2s`
  and `sphincsVerifyWith_some_blake2s` (`E2E/Runs.lean`) the model meanings at
  `HashModel.deployed` give `Meaning_verify_lean_xmss` and `Meaning_verify_sig_lean_sphincs` from
  the deployed relation; the answered chain, tip and fold are `some` of the deployed ones.
-/

namespace LeanVMTests.Guest.ModelSig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.E2E

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.B1.Sig.compress_final_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress_final_model

/-- info: 'LeanVM.Guest.B1.Sig.compress_two_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress_two_model

/-- info: 'LeanVM.Guest.B1.Sig.compress4_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress4_model

/-- info: 'LeanVM.Guest.B1.Sig.compress3_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress3_model

/-- info: 'LeanVM.Guest.B1.Sig.cCodeword_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.cCodeword_model

/-- info: 'LeanVM.Guest.B1.Sig.hashValues_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.hashValues_model

/-- info: 'LeanVM.Guest.B1.Sig.merkle_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.merkle_model

/-- info: 'LeanVM.Guest.B1.Sig.verify_of_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.verify_of_roots

/-- info: 'LeanVM.Guest.B1.Sig.xTail_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.xTail_model

/-- info: 'LeanVM.Guest.B1.Sig.xLayer0_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.xLayer0_model

/-- info: 'LeanVM.Guest.B1.Sig.xLayer1_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.xLayer1_model

/-- info: 'LeanVM.Guest.B1.Sig.verify_lean_xmss_model_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.verify_lean_xmss_model_w

/-- info: 'LeanVM.Guest.B1.verify_lean_xmss_meaning_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_lean_xmss_meaning_model

/-- info: 'LeanVM.Guest.B1.Sig.sVerify_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sVerify_of

/-- info: 'LeanVM.Guest.B1.Sig.sp_forest_key_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sp_forest_key_model

/-- info: 'LeanVM.Guest.B1.Sig.sCoords_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sCoords_model

/-- info: 'LeanVM.Guest.B1.Sig.sPrologue_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sPrologue_model

/-- info: 'LeanVM.Guest.B1.Sig.sCounter_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.sCounter_model

/-- info: 'LeanVM.Guest.B1.Sig.verify_sig_lean_sphincs_model_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.verify_sig_lean_sphincs_model_w

/-- info: 'LeanVM.Guest.B1.verify_sig_lean_sphincs_meaning_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_sig_lean_sphincs_meaning_model

/-- info: 'LeanVM.Guest.B1.verify_lean_xmss_signed_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_lean_xmss_signed_model

/-- info: 'LeanVM.Guest.B1.verify_sig_lean_sphincs_signed_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_sig_lean_sphincs_signed_model

/-! ## The deployed model -/

/-- The model meaning of `verify_lean_xmss` at the deployed model is the deployed one. -/
theorem xmss_meaning_deployed {rd : Reader} {args rets : List E}
    (h : Meaning_verify_lean_xmssWith HashModel.deployed.H rd args rets) : Meaning_verify_lean_xmss rd args rets := by
  obtain ⟨p, ha, hr, pk, m, hc, σ, hv⟩ := h
  have hv : LeanVM.Node.xmssVerifyWith (fun x ↦ some (blake2sBytes x)) pk m σ = some true := hv
  rw [xmssVerifyWith_some_blake2s] at hv
  exact ⟨p, ha, hr, pk, m, hc, σ, Option.some.inj hv⟩

/-- The model meaning of `verify_sig_lean_sphincs` at the deployed model is the deployed one. -/
theorem sphincs_meaning_deployed {rd : Reader} {args rets : List E}
    (h : Meaning_verify_sig_lean_sphincsWith HashModel.deployed.H rd args rets) :
    Meaning_verify_sig_lean_sphincs rd args rets := by
  obtain ⟨p, ha, hr, pk, m, hc, σ, hv⟩ := h
  have hv : LeanVM.Node.sphincsVerifyWith (fun x ↦ some (blake2sBytes x)) pk m σ = some true := hv
  rw [sphincsVerifyWith_some_blake2s] at hv
  exact ⟨p, ha, hr, pk, m, hc, σ, Option.some.inj hv⟩

/-- **`verify_lean_xmss_meaning` from the model lemma at the deployed model.** -/
example {rd : Reader} {args rets : List E} (h : coreProgram.Rel rd "verify_lean_xmss" args rets) :
    Meaning_verify_lean_xmss rd args rets :=
  xmss_meaning_deployed (verify_lean_xmss_meaning_model (M := HashModel.deployed) (by
    rw [show HashModel.deployed.sem = blakeDeployed from rfl, relB_deployed]; exact h))

/-- **`verify_sig_lean_sphincs_meaning` from the model lemma at the deployed model.** -/
example {rd : Reader} {args rets : List E} (h : coreProgram.Rel rd "verify_sig_lean_sphincs" args rets) :
    Meaning_verify_sig_lean_sphincs rd args rets :=
  sphincs_meaning_deployed (verify_sig_lean_sphincs_meaning_model (M := HashModel.deployed) (by
    rw [show HashModel.deployed.sem = blakeDeployed from rfl, relB_deployed]; exact h))

example (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i d : Nat) (x : E) :
    Sig.tipPairWith HashModel.deployed.H lx pp adr idx i d x = some (Sig.tipPair lx pp adr idx i d x) :=
  Sig.tipPairWith_deployed lx pp adr idx i d x

example (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) (m l : Nat) (x : E) :
    Sig.mFoldWith HashModel.deployed.H pp A bits sibs m l x = some (Sig.mFold pp A bits sibs m l x) :=
  Sig.mFoldWith_deployed pp A bits sibs m l x

end LeanVMTests.Guest.ModelSig
