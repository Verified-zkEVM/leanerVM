/-
  LeanVM.Guest.B1.Sig.XmssOut

  What a call `verify_lean_xmss(p)` establishes for a given signature, as a decidable predicate of
  the call's words and the signature, and that the signature of the callee's own valuation
  satisfies it.
-/

module

public import LeanVM.Guest.B1.Sig.Callees

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **What `verify_lean_xmss(p)` establishes for the signature `sig`**: the four words at `p` are a
leanXMSS claim (`Main.xmssOf`) that `sig` verifies under BLAKE2s. `Main.XmssSigned` is its
existential over `sig`. -/
def XmssOut (rd : Reader) (p : E) (sig : LeanXmss.Signature) : Prop :=
  ∃ a b c d, ReadsAt rd p [a, b, c, d] ∧
    Node.xmssVerify (Main.xmssOf a b c d).1 (Main.xmssOf a b c d).2 sig = true

/-- The outcome of a call of `verify_lean_xmss` with the argument words `args` and the return
words `rets`, for the signature `sig`. -/
def XmssCallOut (rd : Reader) (args rets : List E) (sig : LeanXmss.Signature) : Prop :=
  ∃ p, args = [p] ∧ rets = [] ∧ XmssOut rd p sig

theorem XmssOut.signed {rd : Reader} {p : E} {sig : LeanXmss.Signature} (h : XmssOut rd p sig) :
    Main.XmssSigned rd p :=
  let ⟨a, b, c, d, hr, hv⟩ := h
  ⟨a, b, c, d, hr, sig, hv⟩

/-- **`verify_lean_xmss` establishes its outcome for the signature it hints.** -/
theorem verify_lean_xmss_out {rd : Reader} {C : CallRel} {σ : Val} {rets : List E}
    (h : Stmt.HoldsList C rd σ xBody False (fun rs => rs = rets)) :
    rets = [] ∧ XmssOut rd (σ (.n 0)) (xmssSigOf σ) := by
  obtain ⟨hr, hc, hv⟩ := verify_lean_xmss_sound_w h
  refine ⟨hr, _, _, _, _, readsAt_claim hc, ?_⟩
  rw [xmssOf_claim]
  exact hv

/-- The outcome of a call, from the body holding over the call's frame. -/
theorem verify_lean_xmss_callOut {rd : Reader} {C : CallRel} {σ : Val} {args rets : List E}
    (hargs : args = [σ (.n 0)]) (h : Stmt.HoldsList C rd σ xBody False (fun rs => rs = rets)) :
    XmssCallOut rd args rets (xmssSigOf σ) :=
  let ⟨hr, ho⟩ := verify_lean_xmss_out h
  ⟨σ (.n 0), hargs, hr, ho⟩

/-! ## Deciding the outcome -/

/-- `XmssOut` as a Boolean: the four reads at `p`, then the verification. -/
def xmssOutB (rd : Reader) (p : E) (sig : LeanXmss.Signature) : Bool :=
  decide (p.limb 1 = 0 ∧ p.limb 2 = 0) &&
    match rd (p.limb 0 * Parameters.gpow 0), rd (p.limb 0 * Parameters.gpow 1),
        rd (p.limb 0 * Parameters.gpow 2), rd (p.limb 0 * Parameters.gpow 3) with
    | some a, some b, some c, some d => Node.xmssVerify (Main.xmssOf a b c d).1 (Main.xmssOf a b c d).2 sig
    | _, _, _, _ => false

theorem xmssOut_iff {rd : Reader} {p : E} {sig : LeanXmss.Signature} :
    XmssOut rd p sig ↔ xmssOutB rd p sig = true := by
  unfold XmssOut xmssOutB
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

instance {rd : Reader} {p : E} {sig : LeanXmss.Signature} : Decidable (XmssOut rd p sig) :=
  decidable_of_iff _ xmssOut_iff.symm

end
end LeanVM.Guest.B1.Sig
