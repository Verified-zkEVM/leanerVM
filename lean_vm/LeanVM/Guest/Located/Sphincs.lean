/-
  LeanVM.Guest.Located.Sphincs

  The leanSPHINCS signature a located call to `verify_sig_lean_sphincs` checks, read off the memory.
-/

module

public import LeanVM.Guest.Located.Basic
public import LeanVM.Guest.B1.Sig.SphincsOut

/-!
# leanSPHINCS, located

A located call to `verify_sig_lean_sphincs` runs at a frame of the memory, and its body there checks
the signature `Sig.sphincsSigOf wfk` of the frame's valuation, `wfk` giving the chain values each
forest key it calls returns (`Sig.verify_sig_lean_sphincs_out`).

* `fkWit L args rets`: the chain values the frame of a forest key's call holds, its key the first
  `t < 256` whose located relation holds on the call's words; the return words name the key, so it
  is the call's (`fkWit_sound`).
* `sphincsWit L p`: the signature `verify_sig_lean_sphincs`'s frame for the call holds, its forest
  keys' values read the same way. Nothing is verified to find either.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.B1

@[expose] public section

variable {κ : ℕ} (L : MemImage κ)

open Classical in
/-- The key of a forest key's call: the first `t < 256` whose function's located relation holds on
the call's words. -/
noncomputable def fkKey (args rets : List E) : ℕ :=
  ((List.range 256).find? fun t ↦
    decide (RL coreProgram L certByName (Sig.fkNames.getD t "") args rets)).getD 0

/-- **The chain values a forest key's call returns from**: those its key's frame holds. -/
noncomputable def fkWit (args rets : List E) : ℕ → E :=
  let t := fkKey L args rets
  Sig.fkVals t (valAt L (Sig.fkNames.getD t "") (frameOf L (Sig.fkNames.getD t "") args rets))

/-- **The leanSPHINCS signature of the claim at `p`**: the one `verify_sig_lean_sphincs`'s frame
for the call holds, its forest keys' values read the same way. -/
noncomputable def sphincsWit (p : E) : Sphincs.Signature :=
  Sig.sphincsSigOf (fkWit L)
    (valAt L "verify_sig_lean_sphincs" (frameOf L "verify_sig_lean_sphincs" [p] []))

variable {L}

theorem fkKey_spec {t : ℕ} (ht : t < 256) {args rets : List E}
    (h : RL coreProgram L certByName (Sig.fkNames.getD t "") args rets) :
    fkKey L args rets < 256 ∧
      RL coreProgram L certByName (Sig.fkNames.getD (fkKey L args rets) "") args rets := by
  classical
  unfold fkKey
  rcases hfind : (List.range 256).find? (fun t ↦
      decide (RL coreProgram L certByName (Sig.fkNames.getD t "") args rets)) with _ | u
  · exact absurd (decide_eq_true h) (by
      simpa using List.find?_eq_none.mp hfind t (List.mem_range.mpr ht))
  · exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some hfind),
      of_decide_eq_true (List.find?_some (p := fun x ↦
        decide (RL coreProgram L certByName (Sig.fkNames.getD x "") args rets)) hfind)⟩

/-- **The forest keys, located**: every located call of a forest key returns from `fkWit`'s values. -/
theorem fkWit_sound : Sig.FkSoundW (RL coreProgram L certByName) L.read (fkWit L) := by
  intro t ht args rets h
  obtain ⟨hu, hu'⟩ := fkKey_spec ht h
  set u := fkKey L args rets with hu_def
  obtain ⟨hp, hb⟩ := body_frameOf (Sig.find_fk hu) hu'
  have hout := Sig.fkBody_out_w u hb
  rw [show [valAt L (Sig.fkNames.getD u "") (frameOf L (Sig.fkNames.getD u "") args rets) (.n 0),
    valAt L (Sig.fkNames.getD u "") (frameOf L (Sig.fkNames.getD u "") args rets) (.n 1)] = args
    from hp] at hout
  obtain ⟨hp', hb'⟩ := body_frameOf (Sig.find_fk ht) h
  have hout' := Sig.fkBody_out_w t hb'
  rw [show [valAt L (Sig.fkNames.getD t "") (frameOf L (Sig.fkNames.getD t "") args rets) (.n 0),
    valAt L (Sig.fkNames.getD t "") (frameOf L (Sig.fkNames.getD t "") args rets) (.n 1)] = args
    from hp'] at hout'
  have htu : u = t := by
    obtain ⟨_, _, -, hr⟩ := hout
    obtain ⟨_, _, -, hr'⟩ := hout'
    rw [hr] at hr'
    simp only [List.cons.injEq, Sig.word_eq_eOfNat] at hr'
    exact Value.eOfNat_inj (by omega) (by omega) hr'.2.1
  show Sig.FkOut t args rets (Sig.fkVals u _)
  rw [← htu]
  exact hout

/-- **A located call to `verify_sig_lean_sphincs` on `p`**: the claim at `p` is signed by
`sphincsWit L p`. -/
theorem sphincsWit_out {p : E}
    (h : RL coreProgram L certByName "verify_sig_lean_sphincs" [p] []) :
    Sig.SphincsOut L.read p (sphincsWit L p) := by
  obtain ⟨hp, hb⟩ := body_frameOf Sig.find_verify_sig_lean_sphincs h
  have hout := (Sig.verify_sig_lean_sphincs_out fkWit_sound hb).2
  have hp0 : valAt L "verify_sig_lean_sphincs" (frameOf L "verify_sig_lean_sphincs" [p] []) (.n 0) = p := by
    simpa using hp
  rw [hp0] at hout
  exact hout

end
end LeanVM.Guest.Located
