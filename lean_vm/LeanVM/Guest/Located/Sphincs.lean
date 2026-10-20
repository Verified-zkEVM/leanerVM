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

* `fkWit L args rets`: the chain values of the first key `t < 256` and frame `a` of the memory whose
  valuation returns the call's words (`Sig.FkOut`); the return words name the key, so it is the
  call's (`fkWit_sound`).
* `sphincsWit L p`: the signature of the first frame whose valuation's signature, its forest keys'
  values read the same way, checks against the claim at `p` (`Sig.sphincsOutB`).
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.B1

@[expose] public section

/-- The (key, frame) pairs a forest key's call is scanned over. -/
def fkPairs (κ : ℕ) : List (ℕ × ℕ) :=
  (List.range 256).flatMap fun t ↦ (List.range (2 ^ κ)).map (t, ·)

theorem mem_fkPairs {κ t a : ℕ} : (t, a) ∈ fkPairs κ ↔ t < 256 ∧ a < 2 ^ κ := by
  simp [fkPairs]

variable {κ : ℕ} (L : MemImage κ)

/-- The chain values of key `t`'s function at the memory's frame `a`. -/
noncomputable def fkValsAt (q : ℕ × ℕ) : ℕ → E :=
  Sig.fkVals q.1 (valAt L (Sig.fkNames.getD q.1 "") q.2)

/-- The test of a forest key's call at key `q.1` and frame `q.2`: the frame's values return the
call's words (`Sig.fkOut_iff`). -/
noncomputable def fkTest (args rets : List E) (q : ℕ × ℕ) : Bool :=
  args.length == 2 &&
    rets == [Sig.fkLeaf q.1 (args.getD 1 0) (args.getD 0 0) (fkValsAt L q), word q.1 0 0]

theorem fkTest_iff (args rets : List E) (q : ℕ × ℕ) :
    fkTest L args rets q = true ↔ Sig.FkOut q.1 args rets (fkValsAt L q) := by
  rw [Sig.fkOut_iff, fkTest, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]

/-- **The chain values a forest key's call returns from**: those of the first key and frame whose
valuation returns the call's words. -/
noncomputable def fkWit (args rets : List E) : ℕ → E :=
  match (fkPairs κ).find? (fkTest L args rets) with
  | some q => fkValsAt L q
  | none => fun _ ↦ 0

/-- **The leanSPHINCS signature of the claim at `p`**: that of the first frame checking it. -/
noncomputable def sphincsWit (p : E) : Sphincs.Signature :=
  let t := fun a ↦ Sig.sphincsOutB L.read p
    (Sig.sphincsSigOf (fkWit L) (valAt L "verify_sig_lean_sphincs" a))
  match firstFrame κ t with
  | some a => Sig.sphincsSigOf (fkWit L) (valAt L "verify_sig_lean_sphincs" a)
  | none => Sig.sphincsSigOf (fkWit L) (fun _ ↦ 0)

variable {L}

/-- **The forest keys, located**: every located call of a forest key returns from `fkWit`'s values. -/
theorem fkWit_sound : Sig.FkSoundW (RL coreProgram L certByName) L.read (fkWit L) := by
  intro t ht args rets h
  obtain ⟨fn, fp, hf, ⟨a, ha, rfl⟩, hp, hb⟩ := (relL_iff coreProgram _ _ _).mp h
  rw [Sig.find_fk ht] at hf
  cases hf
  have hout := Sig.fkBody_out_w t hb
  rw [show [frameVal L certByName (Sig.fkNames.getD t "") (gpow a) (.n 0),
    frameVal L certByName (Sig.fkNames.getD t "") (gpow a) (.n 1)] = args from hp] at hout
  have htest : fkTest L args rets (t, a) = true := (fkTest_iff L _ _ _).mpr hout
  rcases hfind : (fkPairs κ).find? (fkTest L args rets) with _ | q
  · exact absurd htest (by
      simpa using List.find?_eq_none.mp hfind (t, a) (mem_fkPairs.mpr ⟨ht, ha⟩))
  · have hq := (fkTest_iff L _ _ _).mp (List.find?_some hfind)
    have hq1 : q.1 < 256 := (mem_fkPairs.mp (List.mem_of_find?_eq_some hfind)).1
    have htq : q.1 = t := by
      obtain ⟨_, _, -, hr⟩ := hq
      obtain ⟨_, _, -, hr'⟩ := hout
      rw [hr] at hr'
      simp only [List.cons.injEq, Sig.word_eq_eOfNat] at hr'
      exact Value.eOfNat_inj (by omega) (by omega) hr'.2.1
    unfold fkWit
    rw [hfind]
    rw [← htq]
    exact hq

/-- **A located call to `verify_sig_lean_sphincs` on `p`**: the claim at `p` is signed by
`sphincsWit L p`. -/
theorem sphincsWit_out {p : E}
    (h : RL coreProgram L certByName "verify_sig_lean_sphincs" [p] []) :
    Sig.SphincsOut L.read p (sphincsWit L p) := by
  obtain ⟨fn, fp, hf, ⟨a, ha, rfl⟩, hp, hb⟩ := (relL_iff coreProgram _ _ _).mp h
  rw [Sig.find_verify_sig_lean_sphincs] at hf
  cases hf
  have hout := (Sig.verify_sig_lean_sphincs_out fkWit_sound hb).2
  have hp0 : frameVal L certByName "verify_sig_lean_sphincs" (gpow a) (.n 0) = p := by
    simpa using hp
  rw [hp0] at hout
  obtain ⟨b, hb', ht⟩ := firstFrame_some (t := fun a ↦ Sig.sphincsOutB L.read p
    (Sig.sphincsSigOf (fkWit L) (valAt L "verify_sig_lean_sphincs" a))) ha
    ((Sig.sphincsOut_iff).mp hout)
  unfold sphincsWit
  simp only [hb']
  exact (Sig.sphincsOut_iff).mpr ht

end
end LeanVM.Guest.Located
