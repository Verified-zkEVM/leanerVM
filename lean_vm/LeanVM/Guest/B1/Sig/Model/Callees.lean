/-
  LeanVM.Guest.B1.Sig.Model.Callees

  The signature verifiers as `main`'s callees under a hash model (`Sig/Callees.lean` over
  `coreProgram.RelB M.sem`): the claim's four words at the pointer, and a signature verifying it
  with the model's answered hash.
-/

module

public import LeanVM.Guest.B1.Sig.Callees
public import LeanVM.Guest.B1.Sig.Model.Xmss
public import LeanVM.Guest.B1.Sig.Model.Sphincs

/-!
# The signature callees under a hash model

`verify_lean_xmss_signed_model` and `verify_sig_lean_sphincs_signed_model` are
`verify_lean_xmss_signed` and `verify_sig_lean_sphincs_signed` over `M.sem`: the conclusions are
`Main.XmssSigned` and `Main.SphincsSigned` with the verification `xmssVerifyWith M.H … = some true`
and `sphincsVerifyWith M.H … = some true` (`Spec/NodeWith.lean`), the form `NodeRelWith M.H`
reads.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {M : HashModel} {rd : Reader}

/-- **`main`'s callee `verify_lean_xmss` under a model** (`verify_lean_xmss_signed`). -/
theorem verify_lean_xmss_signed_model (p : E) (h : coreProgram.RelB M.sem rd "verify_lean_xmss" [p] []) :
    ∃ a b c d, ReadsAt rd p [a, b, c, d] ∧
      ∃ σ, Node.xmssVerifyWith M.H (Main.xmssOf a b c d).1 (Main.xmssOf a b c d).2 σ = some true := by
  obtain ⟨q, hq, -, pk, m, hc, sig, hv⟩ := verify_lean_xmss_meaning_model h
  cases hq
  refine ⟨_, _, _, _, Sig.readsAt_claim hc, sig, ?_⟩
  rw [Sig.xmssOf_claim]
  exact hv

/-- **`main`'s callee `verify_sig_lean_sphincs` under a model** (`verify_sig_lean_sphincs_signed`). -/
theorem verify_sig_lean_sphincs_signed_model (p : E)
    (h : coreProgram.RelB M.sem rd "verify_sig_lean_sphincs" [p] []) :
    ∃ a b c d, ReadsAt rd p [a, b, c, d] ∧
      ∃ σ, Node.sphincsVerifyWith M.H (Main.sphincsOf a b c d).1 (Main.sphincsOf a b c d).2 σ = some true := by
  obtain ⟨q, hq, -, pk, m, hc, sig, hv⟩ := verify_sig_lean_sphincs_meaning_model h
  cases hq
  refine ⟨_, _, _, _, Sig.readsAt_claim hc, sig, ?_⟩
  rw [Sig.sphincsOf_claim]
  exact hv

end
end LeanVM.Guest.B1
