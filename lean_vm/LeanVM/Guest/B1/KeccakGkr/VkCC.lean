/-
  LeanVM.Guest.B1.KeccakGkr.VkCC

  `verify_keccak`'s steps, completely: the claim's segment weights, the flips, the `ι` term.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK

/-!
# A step's core, completely

`stepCore_of_flips`: with the claim's point in memory, its segment weights stored at `b + 1` and
the flips holding with their values (`flips0_complete`, `flipsL_complete`), the `ι` term is the
claim's and the core holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Fwd Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val}

theorem mem_stepCoreA {s b : ℕ} {st : Stmt}
    (h : st ∈ [Stmt.atom (.load (.n b) (.n 201) (22 * s + 2)), .atom (.hint (.alloc (.n (b + 1)) 2)),
      .atom (.mul (.n (b + 2)) (.n b) (.n 17))]) : st ∈ stepCore s b :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))

theorem mem_stepCoreE {s b : ℕ} {st : Stmt} (h : st ∈ eqtreeT (.n (b + 2)) (.n (b + 1)) 0 (b + 3) 1) :
    st ∈ stepCore s b :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))

theorem mem_stepCoreF {s b : ℕ} {st : Stmt} (h : st ∈ flipsT s (b + 6)) : st ∈ stepCore s b :=
  List.mem_append_left _ (List.mem_append_right _ h)

theorem mem_stepCoreI {s b : ℕ} {st : Stmt}
    (h : st ∈ iotaSegT s (b + 6) (b + 6 + flipSz s * (iotaUsed s).length) (b + 1)) :
    st ∈ stepCore s b :=
  List.mem_append_right _ h

set_option maxHeartbeats 1000000 in
/-- **A step's core, completely**, given its flips. -/
theorem stepCore_of_flips {s b : ℕ} (hs : s < 12) (hb : 17 ≤ b) (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ st ∈ stepCore s b, GoodS rd vkSt w σ st) (hk : stepKer s b)
    {τ : ℕ} (hτ1 : 9 ≤ τ) (h17 : σ (.n 17) = gen ^ (τ - 4)) {c : KeccakClaim} {pp : E}
    (hpp : LoadHolds rd (σ (.n 201)) (22 * s + 2) pp) (hpt : ReadsAt rd pp c.point)
    (hptL : c.point.length = τ - 3)
    (hT : ∀ i < 2, LoadHolds rd (σ (.n (b + 1))) i ((eqKernel [c.point.getD (τ - 4) 0]).getD i 0))
    (hF : ∀ i ∈ iotaUsed s, σ (.n (flipOf s (b + 6) i)) = c.weights.getD (2 ^ i - 1) 0)
    (HF : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (flipsT s (b + 6)) next kret) :
    σ (.n (stepT0 s b - 1)) = keccakIota τ s c ∧
      ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ (stepCore s b) next kret := by
  obtain ⟨k1, k2, -, -, -, -, k7, k8, k9, k10⟩ := hk
  have gA : ∀ a, Stmt.atom a ∈ stepCore s b → Good rd vkSt w σ a := fun a h ↦ hg _ h
  have e0 : σ (.n b) = pp :=
    load_val (gA _ (mem_stepCoreA (by simp))) (not_mem_of_noneIn k1 _ (by simp)) hpp
  have m2 := mulG (by omega) (by omega) (gA (.mul (.n (b + 2)) (.n b) (.n 17)) (mem_stepCoreA (by simp)))
  -- the segment weights
  have hr : LoadHolds rd (σ (.n (b + 2))) (0 + 0) (c.point.getD (τ - 4) 0) := by
    rw [m2, e0, h17, loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ (by omega)]
    exact hpt _ (by omega)
  have HE : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (eqtreeT (.n (b + 2)) (.n (b + 1)) 0 (b + 3) 1) next kret :=
    fun hn ↦ eqtree_complete le_rfl (fun st h ↦ hg st (mem_stepCoreE h)) (not_mem_of_noneIn k2)
      (rs := [c.point.getD (τ - 4) 0]) rfl
      (fun t ht ↦ by obtain rfl : t = 0 := by omega
                     exact hr)
      (fun t h1 h2 i hi ↦ by
        obtain rfl : t = 1 := by omega
        simpa using hT i hi) hn
  -- the `ι` term
  have HI : ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ
      (iotaSegT s (b + 6) (b + 6 + flipSz s * (iotaUsed s).length) (b + 1)) next kret :=
    fun hn ↦ loads_complete k7 hσ k8 (fun st h ↦ hg st (mem_stepCoreI h)) k9 k10
      (fun q hq off h1 h2 ↦ by
        simp only [List.mem_singleton] at hq
        subst hq
        exact ⟨_, hT off h2⟩) hn
  obtain ⟨hio, -⟩ := iotaSegT_holds (F := fun i ↦ c.weights.getD (2 ^ i - 1) 0)
    (g0 := (eqKernel [c.point.getD (τ - 4) 0]).getD 0 0)
    (g1 := (eqKernel [c.point.getD (τ - 4) 0]).getD 1 0) hs hF
    (fun v hv ↦ loadHolds_unique hv (hT 0 (by norm_num)))
    (fun v hv ↦ loadHolds_unique hv (hT 1 (by norm_num))) (HI (next := True) (kret := fun _ ↦ True) trivial)
  rw [← keccakIota_eq hs (by omega) hptL] at hio
  refine ⟨hio, fun {next kret} hn ↦ ?_⟩
  rw [stepCore]
  simp only [holdsList_append]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  exact ⟨by rw [e0]; exact hpp, trivial, m2, HE (HF (HI hn))⟩

end
end LeanVM.Guest.B1.VerifySub
