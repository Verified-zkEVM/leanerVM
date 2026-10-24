/-
  LeanVM.Guest.Budget.LiftB

  G7's lifts of pure callees (the signature verifiers, `open_stacked`'s leaf callees) within the
  static words bound of their valid trees (`CompleteAtDTB`).
-/

module

public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.Lift.Sig
public import LeanVM.Guest.Lift.OsCallees
public import LeanVM.Guest.Memory.Size

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- The words bound of every valid tree of `f` at `args`, as `completeAtDTB_of_relIn` takes it
(`TotalLe` at `args`). -/
def TotalAt (fs : String → ℕ) (f : String) (args : List E) (B : ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (rets : List E), t.name = f → t.Valid coreProgram rd args rets →
    t.BufsOk coreProgram → t.total fs ≤ B

theorem TotalLe.at {f : String} {B : List E → ℕ} (h : TotalLe coreProgram fs f B) (args : List E) :
    TotalAt fs f args (B args) := fun rd t rets hn hv hb => h rd t args rets hn hv hb

/-- **`verify_lean_xmss`, placed within its words bound.** -/
theorem verify_lean_xmss_completeAtDTB (hc : B1.Sig.verify_lean_xmss_complete_Spec) {κ : ℕ}
    (hκ : 6 ≤ κ) {Lin : Layout} {p : E} {pk : LeanXmss.PublicKey} {m : LeanXmss.Message}
    {sig : LeanXmss.Signature} (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ RegionL Lin i)
    (hat : ∀ rd, LowDef κ rd → MemL rd Lin →
      B1.Sig.ClaimAt rd p (B1.Sig.cellOf128 pk.root) (B1.Sig.cellOf128 pk.parameter)
        (B1.Sig.cellOf128 (m.extractLsb' 0 128)) (B1.Sig.cellOf128 (m.extractLsb' 128 128)))
    (hv : Node.xmssVerify pk m sig = true) {B : ℕ} (hB : TotalAt fs "verify_lean_xmss" [p] B) :
    CompleteAtDTB fs cert κ "verify_lean_xmss" Lin [p] (Returns []) (fun _ => True) B :=
  completeAtDTB_of_relIn Lift.xmss_pure (List.mem_singleton_self _) hB fun rd hl hL =>
    Lift.verify_lean_xmss_relIn hc
      (fun i hi => hl i (lt_of_lt_of_le hi (show 64 ≤ 2 ^ κ from
        (show (64 : ℕ) = 2 ^ 6 from rfl) ▸ Nat.pow_le_pow_right (by decide) hκ)))
      (hat rd hl hL) hv hreg

/-- **`verify_sig_lean_sphincs`, placed within its words bound.** -/
theorem verify_sig_lean_sphincs_completeAtDTB
    (hc : B1.Sig.verify_sig_lean_sphincs_complete_loads_Spec) {κ : ℕ} (hκ : 8 ≤ κ) {Lin : Layout}
    {p bb : E} {pk : Sphincs.PublicKey} {m : Sphincs.Message} {sig : Sphincs.Signature}
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ RegionL Lin i)
    (hregb : ∀ v < 256, ∃ i, bb.limb 0 * gpow v = gpow i ∧ RegionL Lin i)
    (hbb : ∀ rd, LowDef κ rd → MemL rd Lin → B1.Sig.ByteBits rd bb)
    (hat : ∀ rd, LowDef κ rd → MemL rd Lin →
      B1.Sig.ClaimAt rd p (B1.Sig.cellOf128 pk.root) (B1.Sig.cellOf128 pk.parameter)
        (B1.Sig.cellOf128 (m.extractLsb' 0 128)) (B1.Sig.cellOf128 (m.extractLsb' 128 128)))
    (hv : Node.sphincsVerify pk m sig = true) {B : ℕ}
    (hB : TotalAt fs "verify_sig_lean_sphincs" [p, bb] B) :
    CompleteAtDTB fs cert κ "verify_sig_lean_sphincs" Lin [p, bb] (Returns []) (fun _ => True) B :=
  completeAtDTB_of_relIn Lift.sphincs_pure (List.mem_singleton_self _) hB fun rd hl hL =>
    Lift.verify_sig_lean_sphincs_relIn hc
      (fun i hi => hl i (lt_of_lt_of_le hi (show 256 ≤ 2 ^ κ from
        (show (256 : ℕ) = 2 ^ 8 from rfl) ▸ Nat.pow_le_pow_right (by decide) hκ)))
      (hbb rd hl hL) (hat rd hl hL) hv hreg hregb

/-- `CompleteRelRegD` within the words bound `B args`. -/
def CompleteRelRegDB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) (Reg : List E → (ℕ → Prop) → Prop) (B : List E → ℕ) :
    Prop :=
  ∀ args rets Lin, Reg args (RegionL Lin) → (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) →
    CompleteAtDTB fs cert k f Lin args (Returns rets) (fun _ => True) (B args)

/-- **A leaf callee whose relation is its meaning, placed on its regions within its words
bound.** -/
theorem completeRelRegDB_of_iff {f : String} {spec : List (ℕ × ℕ)}
    {Pre : Reader → List E → List E → Prop} (hok : LeafSpecOk f spec)
    (hiff : ∀ rd args rets, coreProgram.Rel rd f args rets ↔ Pre rd args rets) (k : ℕ)
    {B : List E → ℕ} (hB : TotalLe coreProgram fs f B) :
    CompleteRelRegDB fs cert k f Pre (RegPtrs spec) B := by
  obtain ⟨fn, hf, hpar, hleaf⟩ := hok
  intro args rets Lin hreg hpre
  refine completeAtDTB_of_relIn (Lift.pureIn_of_leafOk hf hleaf) (List.mem_singleton_self _)
    (TotalLe.at hB args) fun rd hl hL => Lift.relIn_of_leaf hf hleaf (fun σ es vs hp hw A hA => ?_)
      ((hiff rd args rets).mpr (hpre rd hl hL))
  have hall := Lift.walk_leafOk (σ := σ) fn.body hleaf
  rw [hw] at hall
  obtain ⟨q, hq, off, hoff, rfl⟩ := loads_spec hall A hA
  have hσ : σ (.n q.1) = args.getD q.1 0 := by
    have h1 := hpar q hq
    have h2 : (fn.params.map σ)[q.1]? = args[q.1]? := by rw [hp]
    rw [List.getElem?_map, h1] at h2
    simp only [Option.map_some] at h2
    rw [List.getD_eq_getElem?_getD, ← h2]
    rfl
  rw [hσ]
  exact hreg q hq off hoff

end
end LeanVM.Guest.B1
