/-
  LeanVM.Guest.Lift.Sig

  The signature verifiers' completeness in the uniform placed form (`CompleteAtD`), from B1's
  `Rel`-level completeness: they place nothing and call nothing, and their loads read the caller's
  words.
-/

module

public import LeanVM.Guest.Lift.SpWotsLeaf
public import LeanVM.Guest.B1.Sig.Interface

/-!
# The signature verifiers, placed

**`verify_lean_xmss`** is a leaf body (`Memory/LiftPure.lean`) whose only loads are the claim's four
words at its argument (`claimLoad`, by the kernel: `xmss_leafOk`). With B1's completeness
(`verify_lean_xmss_rel`), on a memory defined below `2^κ`, `κ ≥ 6`, holding a signed claim at `p`
whose four words lie in the caller's words, it is complete placed (`verify_lean_xmss_completeAtD`).

**`sp_wots`** is a leaf body loading nothing (`spWots_leafOk`): with B1's completeness
(`sp_wots_complete_Spec`), on a memory defined below `2^6`, every honest call of it holds in any
region (`sp_wots_relIn`).

**`verify_sig_lean_sphincs`** calls `sp_wots` three times and loads the byte table through computed
pointers, so its loads are B1's (`verify_sig_lean_sphincs_complete_loads_Spec`: the claim's four
words and the table's 256), its body holding under the call relation `RelIn` of the region, which
holds of every honest call of `sp_wots`: with the claim and the table among the caller's words, on
a memory defined below `2^8`, it holds by a tree loading from them (`verify_sig_lean_sphincs_relIn`).
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
    ∀ A ∈ loadAddrs σ es, ∃ off < 4, A = (σ (.n 0)).limb 0 * addressOfIndex off := by
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

set_option maxRecDepth 100000 in
/-- **`verify_lean_xmss` loads only the claim**, from B1's completeness. -/
theorem verify_lean_xmss_relIn (hc : B1.Sig.verify_lean_xmss_complete_Spec) {rd : Reader}
    {R : ℕ → Prop} {p : E} {pk : HashSig.PublicKey} {m : HashSig.Message}
    {sig : LeanXmss.Signature} (hrd : B1.Sig.MemOK rd 64)
    (hat : B1.Sig.ClaimAt rd p (B1.Sig.cellOf128 pk.root) (B1.Sig.cellOf128 pk.parameter)
      (B1.Sig.cellOf128 (m.extractLsb' 0 128)) (B1.Sig.cellOf128 (m.extractLsb' 128 128)))
    (hv : LeanXmss.verifyWithKeccak pk m sig = true)
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * addressOfIndex k = addressOfIndex i ∧ R i) :
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

/-! ## `sp_wots` -/

set_option maxRecDepth 100000 in
/-- **An honest call of `sp_wots` loads nothing**, from B1's completeness, in any region. -/
theorem sp_wots_relIn (hc : B1.Sig.sp_wots_complete_Spec) {rd : Reader} (R : ℕ → Prop)
    (hrd : B1.Sig.MemOK rd 64) : B1.Sig.SpWotsCalls (coreProgram.RelIn rd R) := by
  intro parameter layer tree leaf digest values hv
  obtain ⟨σ, h0, h1, h2, hb⟩ := hc (coreProgram.Rel rd) rd parameter layer tree leaf digest values
    hrd hv
  refine relIn_of_leaf B1.Sig.find_sp_wots spWots_leafOk (fun σ' es vs _ hw A hA => ?_)
    ((B1.Sig.rel_iff_body B1.Sig.find_sp_wots _ _).mpr
      ⟨σ, by rw [B1.Sig.sp_wots_params]; simp [h0, h1, h2], hb⟩)
  have hall : (Out.ret es vs).All (EvLeafOk noLoad) := by
    have := walk_leafOk (σ := σ') Data.core20.body spWots_leafOk
    exact (show walk σ' Data.core20.body = .ret es vs from hw) ▸ this
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := hall e he
  cases e with
  | atom a =>
    cases a with
    | load => simp [EvLeafOk, noLoad] at hok
    | _ => simp [Ev.loadAddr?] at hea
  | _ => simp [Ev.loadAddr?] at hea

/-! ## `verify_sig_lean_sphincs` -/

set_option maxRecDepth 100000 in
/-- **`verify_sig_lean_sphincs` loads only the claim and the byte table**, its calls of `sp_wots`
loading nothing, from B1's completeness with its loads. -/
theorem verify_sig_lean_sphincs_relIn (hc : B1.Sig.SphincsCompleteSpecs)
    {rd : Reader} {R : ℕ → Prop} {p bb : E} {pk : HashSig.PublicKey} {m : HashSig.Message}
    {sig : Sphincs.Signature} (hrd : B1.Sig.MemOK rd 256) (hbb : B1.Sig.ByteBits rd bb)
    (hat : B1.Sig.ClaimAt rd p (B1.Sig.cellOf128 pk.root) (B1.Sig.cellOf128 pk.parameter)
      (B1.Sig.cellOf128 (m.extractLsb' 0 128)) (B1.Sig.cellOf128 (m.extractLsb' 128 128)))
    (hv : Sphincs.verifyWithKeccak pk m sig = true)
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * addressOfIndex k = addressOfIndex i ∧ R i)
    (hregb : ∀ v < 256, ∃ i, bb.limb 0 * addressOfIndex v = addressOfIndex i ∧ R i) :
    coreProgram.RelIn rd R "verify_sig_lean_sphincs" [p, bb] [] := by
  obtain ⟨σ, h0, h1, hb, hloads⟩ := hc.verify (coreProgram.RelIn rd R) rd p bb pk m sig
    (sp_wots_relIn hc.sp_wots R fun i hi => hrd i (by omega)) hrd hbb hat hv
  have hsat := walk_sat (P := coreProgram) Data.core21.body
    (coreProgram_wf _ (List.mem_of_find?_eq_some B1.Sig.find_verify_sig_lean_sphincs)) hb
  cases hw : walk σ Data.core21.body with
  | fall es => rw [hw] at hsat; exact hsat.2.elim
  | stuck => rw [hw] at hsat; exact hsat.elim
  | ret es vs =>
    rw [hw] at hsat
    obtain ⟨hok, hr⟩ := hsat
    refine relIn_of_walk coreProgram_wf B1.Sig.find_verify_sig_lean_sphincs
      (by rw [B1.Sig.verify_sig_lean_sphincs_params]; simp [h0, h1]) hw hr (fun e he ↦ (hok e he).1)
      (fun A hA ↦ ?_) (fun c hc ht ↦ ?_)
    · rcases hloads es vs hw A hA with ⟨k, hk, rfl⟩ | ⟨v, hv', rfl⟩
      · exact hreg k hk
      · exact hregb v hv'
    · obtain ⟨e, he, hec⟩ := List.mem_filterMap.mp hc
      cases e with
      | call f args rets =>
        simp only [Ev.call?, Option.some.injEq] at hec
        subst hec
        exact (hok _ he).2 f args rets rfl
      | skip f args =>
        simp only [Ev.call?, Option.some.injEq] at hec
        subst hec
        cases ht
      | _ => simp [Ev.call?] at hec

end
end LeanVM.Guest.Lift
