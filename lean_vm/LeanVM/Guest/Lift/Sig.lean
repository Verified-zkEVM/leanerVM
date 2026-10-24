/-
  LeanVM.Guest.Lift.Sig

  The signature verifiers' completeness in the uniform placed form (`CompleteAtD`), from B1's
  `Rel`-level completeness: they place nothing and call nothing, and their loads read the caller's
  words.
-/

module

public import LeanVM.Guest.Lift.SphincsLeaf
public import LeanVM.Guest.B1.Sig.SphincsLoads
public import LeanVM.Guest.B1.Sig.Interface

/-!
# The signature verifiers, placed

**`verify_lean_xmss`** is a leaf body (`Memory/LiftPure.lean`) whose only loads are the claim's four
words at its argument (`claimLoad`, by the kernel: `xmss_leafOk`). With B1's completeness
(`verify_lean_xmss_rel`), on a memory defined below `2^κ`, `κ ≥ 6`, holding a signed claim at `p`
whose four words lie in the caller's words, it is complete placed (`verify_lean_xmss_completeAtD`).

**`verify_sig_lean_sphincs`** is a leaf body too (`sphincs_leafOk`, on ranges of its statements),
but loads the byte table through computed pointers, so its loads are B1's
(`verify_sig_lean_sphincs_complete_loads`: the claim's four words and the table's 256): with the
claim and the table among the caller's words, on a memory defined below `2^κ`, `κ ≥ 8`, it is
complete placed (`verify_sig_lean_sphincs_completeAtD`).
-/

namespace LeanVM.Guest.Lift

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 (LowDef Within CompleteAtD Returns disj_nil relAtIn_dmono)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## `verify_lean_xmss` -/

/-- A load of the argument `.n 0` at an offset below 4; no other load. -/
def claimLoad : Atom → Bool
  | .load _ p off => decide (p = .n 0) && decide (off < 4)
  | _ => true

set_option maxRecDepth 100000 in
/-- **`verify_lean_xmss`'s body**: atoms, branches and arms, its loads the claim's words. -/
theorem xmss_leafOk : Stmt.leafOkList claimLoad Data.core19.body = true := by decide +kernel

theorem loads_claim {σ : Val} {es : List Ev} (h : ∀ e ∈ es, EvLeafOk claimLoad e) :
    ∀ A ∈ loadAddrs σ es, ∃ off < 4, A = (σ (.n 0)).limb 0 * gpow off := by
  intro A hA
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := h e he
  cases e with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      simp only [EvLeafOk, claimLoad, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact ⟨off, hok.2, by rw [← hea, hok.1]⟩
    | _ => simp [Ev.loadAddr?] at hea
  | _ => simp [Ev.loadAddr?] at hea

theorem xmss_pure : coreProgram.PureIn ["verify_lean_xmss"] :=
  pureIn_of_leafOk B1.Sig.find_verify_lean_xmss xmss_leafOk

set_option maxRecDepth 100000 in
/-- **`verify_lean_xmss` loads only the claim**, from B1's completeness. -/
theorem verify_lean_xmss_relIn (hc : B1.Sig.verify_lean_xmss_complete_Spec) {rd : Reader}
    {R : ℕ → Prop} {p : E} {pk : LeanXmss.PublicKey} {m : LeanXmss.Message}
    {sig : LeanXmss.Signature} (hrd : B1.Sig.MemOK rd 64)
    (hat : B1.Sig.ClaimAt rd p (B1.Sig.cellOf128 pk.root) (B1.Sig.cellOf128 pk.parameter)
      (B1.Sig.cellOf128 (m.extractLsb' 0 128)) (B1.Sig.cellOf128 (m.extractLsb' 128 128)))
    (hv : Node.xmssVerify pk m sig = true)
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ R i) :
    coreProgram.RelIn rd R "verify_lean_xmss" [p] [] :=
  relIn_of_leaf B1.Sig.find_verify_lean_xmss xmss_leafOk
    (fun σ es vs hp hw A hA => by
      have hall : (Out.ret es vs).All (EvLeafOk claimLoad) := by
        have := walk_leafOk (σ := σ) Data.core19.body xmss_leafOk
        exact (show walk σ Data.core19.body = .ret es vs from hw) ▸ this
      obtain ⟨off, hoff, rfl⟩ := loads_claim hall A hA
      rw [B1.Sig.core19_params] at hp
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
      rw [hp]
      exact hreg off hoff)
    (B1.Sig.verify_lean_xmss_rel hc hrd hat hv)

/-- **`verify_lean_xmss` is complete, placed**: on memories defined below `2^κ`, `κ ≥ 6`, holding
the caller's words `Lin`, among them the four words of a claim at `p` that `sig` verifies. -/
theorem verify_lean_xmss_completeAtD (hc : B1.Sig.verify_lean_xmss_complete_Spec) {κ : ℕ}
    (hκ : 6 ≤ κ) {Lin : Layout} {p : E} {pk : LeanXmss.PublicKey} {m : LeanXmss.Message}
    {sig : LeanXmss.Signature} (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ RegionL Lin i)
    (hat : ∀ rd, LowDef κ rd → MemL rd Lin →
      B1.Sig.ClaimAt rd p (B1.Sig.cellOf128 pk.root) (B1.Sig.cellOf128 pk.parameter)
        (B1.Sig.cellOf128 (m.extractLsb' 0 128)) (B1.Sig.cellOf128 (m.extractLsb' 128 128)))
    (hv : Node.xmssVerify pk m sig = true) :
    CompleteAtD fs cert κ "verify_lean_xmss" Lin [p] (Returns []) :=
  completeAtD_of_relIn xmss_pure (List.mem_singleton_self _) fun rd hl hL =>
    verify_lean_xmss_relIn hc
      (fun i hi => hl i (lt_of_lt_of_le hi (show 64 ≤ 2 ^ κ from
        (show (64 : ℕ) = 2 ^ 6 from rfl) ▸ Nat.pow_le_pow_right (by decide) hκ)))
      (hat rd hl hL) hv hreg

/-! ## `verify_sig_lean_sphincs` -/

theorem sphincs_pure : coreProgram.PureIn ["verify_sig_lean_sphincs"] :=
  pureIn_of_leafOk B1.Sig.find_verify_sig_lean_sphincs sphincs_leafOk

set_option maxRecDepth 100000 in
/-- **`verify_sig_lean_sphincs` loads only the claim and the byte table**, from B1's completeness
with its loads. -/
theorem verify_sig_lean_sphincs_relIn (hc : B1.Sig.verify_sig_lean_sphincs_complete_loads_Spec)
    {rd : Reader} {R : ℕ → Prop} {p bb : E} {pk : Sphincs.PublicKey} {m : Sphincs.Message}
    {sig : Sphincs.Signature} (hrd : B1.Sig.MemOK rd 256) (hbb : B1.Sig.ByteBits rd bb)
    (hat : B1.Sig.ClaimAt rd p (B1.Sig.cellOf128 pk.root) (B1.Sig.cellOf128 pk.parameter)
      (B1.Sig.cellOf128 (m.extractLsb' 0 128)) (B1.Sig.cellOf128 (m.extractLsb' 128 128)))
    (hv : Node.sphincsVerify pk m sig = true)
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ R i)
    (hregb : ∀ v < 256, ∃ i, bb.limb 0 * gpow v = gpow i ∧ R i) :
    coreProgram.RelIn rd R "verify_sig_lean_sphincs" [p, bb] [] := by
  obtain ⟨σ, h0, h1, hb, hloads⟩ := hc (coreProgram.Rel rd) rd p bb pk m sig hrd hbb hat hv
  have hsat := walk_sat (P := coreProgram) Data.core20.body core20_wf hb
  have hall := walk_leafOk (σ := σ) Data.core20.body sphincs_leafOk
  cases hw : walk σ Data.core20.body with
  | fall es => rw [hw] at hsat; exact hsat.2.elim
  | stuck => rw [hw] at hsat; exact hsat.elim
  | ret es vs =>
    rw [hw] at hsat hall
    obtain ⟨hok, hr⟩ := hsat
    refine relIn_of_walk coreProgram_wf B1.Sig.find_verify_sig_lean_sphincs
      (by rw [B1.Sig.core20_params]; simp [h0, h1]) hw hr (fun e he ↦ (hok e he).1)
      (fun A hA ↦ ?_) (fun c hc ↦ by rw [calls_nil_of_leafOk hall] at hc; cases hc)
    rcases hloads es vs hw A hA with ⟨k, hk, rfl⟩ | ⟨v, hv', rfl⟩
    · exact hreg k hk
    · exact hregb v hv'

/-- **`verify_sig_lean_sphincs` is complete, placed**: on memories defined below `2^κ`, `κ ≥ 8`,
holding the caller's words `Lin`, among them the four words of a claim at `p` that `sig`
verifies and the byte table at `bb`. -/
theorem verify_sig_lean_sphincs_completeAtD
    (hc : B1.Sig.verify_sig_lean_sphincs_complete_loads_Spec) {κ : ℕ} (hκ : 8 ≤ κ) {Lin : Layout}
    {p bb : E} {pk : Sphincs.PublicKey} {m : Sphincs.Message} {sig : Sphincs.Signature}
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ RegionL Lin i)
    (hregb : ∀ v < 256, ∃ i, bb.limb 0 * gpow v = gpow i ∧ RegionL Lin i)
    (hbb : ∀ rd, LowDef κ rd → MemL rd Lin → B1.Sig.ByteBits rd bb)
    (hat : ∀ rd, LowDef κ rd → MemL rd Lin →
      B1.Sig.ClaimAt rd p (B1.Sig.cellOf128 pk.root) (B1.Sig.cellOf128 pk.parameter)
        (B1.Sig.cellOf128 (m.extractLsb' 0 128)) (B1.Sig.cellOf128 (m.extractLsb' 128 128)))
    (hv : Node.sphincsVerify pk m sig = true) :
    CompleteAtD fs cert κ "verify_sig_lean_sphincs" Lin [p, bb] (Returns []) :=
  completeAtD_of_relIn sphincs_pure (List.mem_singleton_self _) fun rd hl hL =>
    verify_sig_lean_sphincs_relIn hc
      (fun i hi => hl i (lt_of_lt_of_le hi (show 256 ≤ 2 ^ κ from
        (show (256 : ℕ) = 2 ^ 8 from rfl) ▸ Nat.pow_le_pow_right (by decide) hκ)))
      (hbb rd hl hL) (hat rd hl hL) hv hreg hregb

end
end LeanVM.Guest.Lift
