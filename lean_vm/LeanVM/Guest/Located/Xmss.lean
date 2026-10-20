/-
  LeanVM.Guest.Located.Xmss

  The leanXMSS signature a located call to `verify_lean_xmss` checks, read off the memory.
-/

module

public import LeanVM.Guest.Located.Basic
public import LeanVM.Guest.B1.Sig.XmssOut

/-!
# leanXMSS, located

A located call `verify_lean_xmss [p] []` (`Check.RL`) runs at a frame `g^a` of the memory, and its
body there checks the signature `Sig.xmssSigOf` of the frame's valuation against the claim at `p`
(`Sig.verify_lean_xmss_out`). `xmssWit L p` is the signature that frame holds, the frame being the
first at which `verify_lean_xmss`'s code holds on the call's words (`frameOf`): nothing is verified
to find it.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.B1

@[expose] public section

variable {κ : ℕ} (L : MemImage κ)

/-- **The leanXMSS signature of the claim at `p`**: the one `verify_lean_xmss`'s frame for the call
holds (`frameOf`). -/
noncomputable def xmssWit (p : E) : LeanXmss.Signature :=
  Sig.xmssSigOf (valAt L "verify_lean_xmss" (frameOf L "verify_lean_xmss" [p] []))

variable {L}

/-- **A located call to `verify_lean_xmss` on `p`**: the claim at `p` is signed by `xmssWit L p`. -/
theorem xmssWit_out {p : E} (h : RL coreProgram L certByName "verify_lean_xmss" [p] []) :
    Sig.XmssOut L.read p (xmssWit L p) := by
  obtain ⟨hp, hb⟩ := body_frameOf Sig.find_verify_lean_xmss h
  have hout := (Sig.verify_lean_xmss_out hb).2
  have hp0 : valAt L "verify_lean_xmss" (frameOf L "verify_lean_xmss" [p] []) (.n 0) = p := by
    simpa using hp
  rw [hp0] at hout
  exact hout

end
end LeanVM.Guest.Located
