/-
  LeanVM.Guest.B1.Sig.SphincsOut

  What a call `verify_sig_lean_sphincs(p)` establishes for a given signature, as a decidable
  predicate of the call's words and the signature, and that the signature of the callee's own
  valuation (and its forest keys' witness) satisfies it.
-/

module

public import LeanVM.Guest.B1.Sig.Callees

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **What `verify_sig_lean_sphincs(p)` establishes for the signature `sig`**: the four words at
`p` are a leanSPHINCS claim (`Main.sphincsOf`) that `sig` verifies under BLAKE2s.
`Main.SphincsSigned` is its existential over `sig`. -/
def SphincsOut (rd : Reader) (p : E) (sig : Sphincs.Signature) : Prop :=
  ∃ a b c d, ReadsAt rd p [a, b, c, d] ∧
    Node.sphincsVerify (Main.sphincsOf a b c d).1 (Main.sphincsOf a b c d).2 sig = true

/-- The outcome of a call of `verify_sig_lean_sphincs` with the argument words `args` and the
return words `rets`, for the signature `sig`. -/
def SphincsCallOut (rd : Reader) (args rets : List E) (sig : Sphincs.Signature) : Prop :=
  ∃ p, args = [p] ∧ rets = [] ∧ SphincsOut rd p sig

theorem SphincsOut.signed {rd : Reader} {p : E} {sig : Sphincs.Signature} (h : SphincsOut rd p sig) :
    Main.SphincsSigned rd p :=
  let ⟨a, b, c, d, hr, hv⟩ := h
  ⟨a, b, c, d, hr, sig, hv⟩

/-- **`verify_sig_lean_sphincs` establishes its outcome for the signature it hints**, its forest
keys' chain values from the witness `wfk`. -/
theorem verify_sig_lean_sphincs_out {rd : Reader} {C : CallRel} {wfk : List E → List E → Nat → E}
    (hfk : FkSoundW C rd wfk) {σ : Val} {rets : List E}
    (h : Stmt.HoldsList C rd σ sBody False (fun rs => rs = rets)) :
    rets = [] ∧ SphincsOut rd (σ (.n 0)) (sphincsSigOf wfk σ) := by
  obtain ⟨hr, pk, m, hc, hv⟩ := verify_sig_lean_sphincs_sound_w hfk h
  refine ⟨hr, _, _, _, _, readsAt_claim hc, ?_⟩
  rw [sphincsOf_claim]
  exact hv

/-- The outcome of a call, from the body holding over the call's frame. -/
theorem verify_sig_lean_sphincs_callOut {rd : Reader} {C : CallRel} {wfk : List E → List E → Nat → E}
    (hfk : FkSoundW C rd wfk) {σ : Val} {args rets : List E} (hargs : args = [σ (.n 0)])
    (h : Stmt.HoldsList C rd σ sBody False (fun rs => rs = rets)) :
    SphincsCallOut rd args rets (sphincsSigOf wfk σ) :=
  let ⟨hr, ho⟩ := verify_sig_lean_sphincs_out hfk h
  ⟨σ (.n 0), hargs, hr, ho⟩

/-! ## Deciding the outcome -/

/-- `SphincsOut` as a Boolean: the four reads at `p`, then the verification. -/
def sphincsOutB (rd : Reader) (p : E) (sig : Sphincs.Signature) : Bool :=
  decide (p.limb 1 = 0 ∧ p.limb 2 = 0) &&
    match rd (p.limb 0 * Parameters.gpow 0), rd (p.limb 0 * Parameters.gpow 1),
        rd (p.limb 0 * Parameters.gpow 2), rd (p.limb 0 * Parameters.gpow 3) with
    | some a, some b, some c, some d => Node.sphincsVerify (Main.sphincsOf a b c d).1 (Main.sphincsOf a b c d).2 sig
    | _, _, _, _ => false

theorem sphincsOut_iff {rd : Reader} {p : E} {sig : Sphincs.Signature} :
    SphincsOut rd p sig ↔ sphincsOutB rd p sig = true := by
  unfold SphincsOut sphincsOutB
  simp only [Main.readsAt_four, LoadHolds, IsInK, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, c, d, ⟨⟨hk, h0⟩, ⟨-, h1⟩, ⟨-, h2⟩, ⟨-, h3⟩⟩, hv⟩
    rw [h0, h1, h2, h3]
    exact ⟨hk, hv⟩
  · rintro ⟨hk, h⟩
    revert h
    cases h0 : rd (p.limb 0 * Parameters.gpow 0) <;> cases h1 : rd (p.limb 0 * Parameters.gpow 1) <;>
      cases h2 : rd (p.limb 0 * Parameters.gpow 2) <;> cases h3 : rd (p.limb 0 * Parameters.gpow 3) <;>
      simp only [Bool.false_eq_true, false_imp_iff]
    exact fun hv => ⟨_, _, _, _, ⟨⟨hk, rfl⟩, ⟨hk, rfl⟩, ⟨hk, rfl⟩, ⟨hk, rfl⟩⟩, hv⟩

instance {rd : Reader} {p : E} {sig : Sphincs.Signature} : Decidable (SphincsOut rd p sig) :=
  decidable_of_iff _ sphincsOut_iff.symm

end
end LeanVM.Guest.B1.Sig
