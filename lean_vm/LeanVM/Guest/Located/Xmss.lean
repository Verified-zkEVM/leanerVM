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
(`Sig.verify_lean_xmss_out`). `xmssWit L p` is the signature of the first frame `a < 2^κ` whose
valuation's signature checks against the claim at `p` (`Sig.xmssOutB`, a Boolean test): a function
of the memory, found by a scan as long as the memory.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.B1

@[expose] public section

variable {κ : ℕ} (L : MemImage κ)

/-- **The leanXMSS signature of the claim at `p`**: that of the first frame checking it. -/
noncomputable def xmssWit (p : E) : LeanXmss.Signature :=
  let t := fun a ↦ Sig.xmssOutB L.read p (Sig.xmssSigOf (valAt L "verify_lean_xmss" a))
  match firstFrame κ t with
  | some a => Sig.xmssSigOf (valAt L "verify_lean_xmss" a)
  | none => Sig.xmssSigOf (fun _ ↦ 0)

variable {L}

/-- **A located call to `verify_lean_xmss` on `p`**: the claim at `p` is signed by `xmssWit L p`. -/
theorem xmssWit_out {p : E} (h : RL coreProgram L certByName "verify_lean_xmss" [p] []) :
    Sig.XmssOut L.read p (xmssWit L p) := by
  obtain ⟨fn, fp, hf, ⟨a, ha, rfl⟩, hp, hb⟩ := (relL_iff coreProgram _ _ _).mp h
  rw [Sig.find_verify_lean_xmss] at hf
  cases hf
  have hout := (Sig.verify_lean_xmss_out hb).2
  have hp0 : frameVal L certByName "verify_lean_xmss" (gpow a) (.n 0) = p := by
    simpa using hp
  rw [hp0] at hout
  obtain ⟨b, hb', ht⟩ := firstFrame_some (t := fun a ↦ Sig.xmssOutB L.read p
    (Sig.xmssSigOf (valAt L "verify_lean_xmss" a))) ha ((Sig.xmssOut_iff).mp hout)
  unfold xmssWit
  simp only [hb']
  exact (Sig.xmssOut_iff).mpr ht

end
end LeanVM.Guest.Located
