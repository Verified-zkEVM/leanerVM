/-
  LeanVM.Guest.Located.SigB

  The leanXMSS and leanSPHINCS signatures the located calls check, read off the memory under any
  semantics of `BLAKE2S`, verifying over a hash model (`Located/Xmss.lean`, `Located/Sphincs.lean`
  over `S` and a `HashModel`).
-/

module

public import LeanVM.Guest.Located.BasicB
public import LeanVM.Guest.Located.Xmss
public import LeanVM.Guest.Located.Sphincs
public import LeanVM.Guest.B1.Sig.Model.Callees
public import LeanVM.Guest.B1.Main.CalleesWM

/-!
# The signatures, located, under any semantics

`xmssWitB S L p`, `sphincsWitB S L p`: `xmssWit`, `sphincsWit` with the frames under `S`
(`frameOfB S`) and the forest keys' located relation under `S` (`fkKeyB S`); at `blakeDeployed`
they are the deployed decoders (`xmssWitB_deployed`, `sphincsWitB_deployed`). Over a hash model,
a located call under `M.sem` verifies the claim at `p` with the decoded signature over the model's
hash (`xmssWit_outM`, `sphincsWit_outM`: `Main.XmssOutM`, `Main.SphincsOutM`), by the Sig group's
model lemmas (`verify_lean_xmss_model_w`, `verify_sig_lean_sphincs_model_w`, `fkBody_model`).
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.B1 LeanVM.Guest.Value

@[expose] public section

variable (S : BlakeSem) {κ : ℕ} (L : MemImage κ)

/-- **The leanXMSS signature of the claim at `p`, under `S`** (`xmssWit`). -/
noncomputable def xmssWitB (p : E) : LeanXmss.Signature :=
  Sig.xmssSigOf (valAt L "verify_lean_xmss" (frameOfB S L "verify_lean_xmss" [p] []))

open Classical in
/-- The key of a forest key's call under `S` (`fkKey`). -/
noncomputable def fkKeyB (args rets : List E) : ℕ :=
  ((List.range 256).find? fun t ↦
    decide (RLB S coreProgram L certByName (Sig.fkNames.getD t "") args rets)).getD 0

/-- The chain values a forest key's call returns from, under `S` (`fkWit`). -/
noncomputable def fkWitB (args rets : List E) : ℕ → E :=
  let t := fkKeyB S L args rets
  Sig.fkVals t (valAt L (Sig.fkNames.getD t "") (frameOfB S L (Sig.fkNames.getD t "") args rets))

/-- **The leanSPHINCS signature of the claim at `p`, under `S`** (`sphincsWit`). -/
noncomputable def sphincsWitB (p : E) : Sphincs.Signature :=
  Sig.sphincsSigOf (fkWitB S L)
    (valAt L "verify_sig_lean_sphincs" (frameOfB S L "verify_sig_lean_sphincs" [p] []))

/-! ## At the deployed semantics -/

theorem xmssWitB_deployed : xmssWitB blakeDeployed L = xmssWit L := by
  funext p
  simp only [xmssWitB, xmssWit, frameOfB_deployed]

theorem fkKeyB_deployed : fkKeyB blakeDeployed L = fkKey L := by
  funext args rets
  unfold fkKeyB fkKey
  congr 2
  funext t
  rw [rlB_deployed]

theorem sphincsWitB_deployed : sphincsWitB blakeDeployed L = sphincsWit L := by
  have hfk : fkWitB blakeDeployed L = fkWit L := by
    funext args rets
    simp only [fkWitB, fkWit, fkKeyB_deployed, frameOfB_deployed]
  funext p
  simp only [sphincsWitB, sphincsWit, hfk, frameOfB_deployed]

/-! ## Over a hash model -/

variable {S L} {M : HashModel}

/-- **A located call to `verify_lean_xmss` on `p` under the model's semantics** (`xmssWit_out`):
the claim at `p` is signed by `xmssWitB M.sem L p` over the model's hash. -/
theorem xmssWit_outM {p : E}
    (h : RLB M.sem coreProgram L certByName "verify_lean_xmss" [p] []) :
    Main.XmssOutM M L.read p (xmssWitB M.sem L p) := by
  obtain ⟨hp, hb⟩ := body_frameOfB Sig.find_verify_lean_xmss h
  obtain ⟨-, hc, hv⟩ := Sig.verify_lean_xmss_model_w hb
  have hp0 : valAt L "verify_lean_xmss" (frameOfB M.sem L "verify_lean_xmss" [p] []) (.n 0) = p := by
    simpa using hp
  rw [hp0] at hc
  refine ⟨_, _, _, _, Sig.readsAt_claim hc, ?_⟩
  rw [Sig.xmssOf_claim]
  exact hv

theorem fkKeyB_spec {t : ℕ} (ht : t < 256) {args rets : List E}
    (h : RLB M.sem coreProgram L certByName (Sig.fkNames.getD t "") args rets) :
    fkKeyB M.sem L args rets < 256 ∧
      RLB M.sem coreProgram L certByName (Sig.fkNames.getD (fkKeyB M.sem L args rets) "") args rets := by
  classical
  unfold fkKeyB
  rcases hfind : (List.range 256).find? (fun t ↦
      decide (RLB M.sem coreProgram L certByName (Sig.fkNames.getD t "") args rets)) with _ | u
  · exact absurd (decide_eq_true h) (by
      simpa using List.find?_eq_none.mp hfind t (List.mem_range.mpr ht))
  · exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some hfind),
      of_decide_eq_true (List.find?_some (p := fun x ↦
        decide (RLB M.sem coreProgram L certByName (Sig.fkNames.getD x "") args rets)) hfind)⟩

/-- **The forest keys, located, over a model** (`fkWit_sound`). -/
theorem fkWit_soundM :
    Sig.FkSoundWWith M (RLB M.sem coreProgram L certByName) (fkWitB M.sem L) := by
  intro t ht args rets h
  obtain ⟨hu, hu'⟩ := fkKeyB_spec ht h
  set u := fkKeyB M.sem L args rets with hu_def
  obtain ⟨hp, hb⟩ := body_frameOfB (Sig.find_fk hu) hu'
  have hout := Sig.fkBody_model u hb
  rw [show [valAt L (Sig.fkNames.getD u "") (frameOfB M.sem L (Sig.fkNames.getD u "") args rets) (.n 0),
    valAt L (Sig.fkNames.getD u "") (frameOfB M.sem L (Sig.fkNames.getD u "") args rets) (.n 1)] = args
    from hp] at hout
  obtain ⟨hp', hb'⟩ := body_frameOfB (Sig.find_fk ht) h
  have hout' := Sig.fkBody_model t hb'
  rw [show [valAt L (Sig.fkNames.getD t "") (frameOfB M.sem L (Sig.fkNames.getD t "") args rets) (.n 0),
    valAt L (Sig.fkNames.getD t "") (frameOfB M.sem L (Sig.fkNames.getD t "") args rets) (.n 1)] = args
    from hp'] at hout'
  have htu : u = t := by
    obtain ⟨_, _, -, _, -, hr⟩ := hout
    obtain ⟨_, _, -, _, -, hr'⟩ := hout'
    rw [hr] at hr'
    simp only [List.cons.injEq, Sig.word_eq_eOfNat] at hr'
    exact Value.eOfNat_inj (by omega) (by omega) hr'.2.1
  show Sig.FkOutWith M.H t args rets (Sig.fkVals u _)
  rw [← htu]
  exact hout

/-- **A located call to `verify_sig_lean_sphincs` on `p` under the model's semantics**
(`sphincsWit_out`): the claim at `p` is signed by `sphincsWitB M.sem L p` over the model's hash. -/
theorem sphincsWit_outM {p : E}
    (h : RLB M.sem coreProgram L certByName "verify_sig_lean_sphincs" [p] []) :
    Main.SphincsOutM M L.read p (sphincsWitB M.sem L p) := by
  obtain ⟨hp, hb⟩ := body_frameOfB Sig.find_verify_sig_lean_sphincs h
  obtain ⟨-, pk, m, hc, hv⟩ := Sig.verify_sig_lean_sphincs_model_w fkWit_soundM hb
  have hp0 : valAt L "verify_sig_lean_sphincs"
      (frameOfB M.sem L "verify_sig_lean_sphincs" [p] []) (.n 0) = p := by
    simpa using hp
  rw [hp0] at hc
  refine ⟨_, _, _, _, Sig.readsAt_claim hc, ?_⟩
  rw [Sig.sphincsOf_claim]
  exact hv

end
end LeanVM.Guest.Located
