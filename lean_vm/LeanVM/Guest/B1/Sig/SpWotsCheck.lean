/-
  LeanVM.Guest.B1.Sig.SpWotsCheck

  The facts about numbers `sp_wots`'s soundness reads off its template, checked by the kernel:
  every arm's layout, and where the leaf's padding run is.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsArms

/-!
# `sp_wots`'s template, checked

* `spLayout_all`: every arm of every group has its layout (`spLayoutOK`, `SpWotsArms`);
* `spLeafCells_eq`: the leaf's cells are `P`, the leaf's address and the 64 tips `spTip i`, the
  slot of chain `i`'s last step in its group;
* `spTarget_eq`: the target's word is `g^128`;
* `spLeafPad`: the leaf's `keccak_cells` allocates its padding run at its first `KECCAK`, above
  every cell it hashes and at most at its output run, which lies below the virtual run.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- Every arm of group `p` has its layout. -/
def spGroupLayoutOK (p : Nat) : Bool :=
  (List.range (4 ^ spN p)).all fun k =>
    spLayoutOK (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k
      (spArmB (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k)

theorem spGroupLayoutOK_all : (List.range 22).all spGroupLayoutOK = true := by decide +kernel

/-- **Every arm of every group has its layout.** -/
theorem spLayout_all {p k : Nat} (hp : p < 22) (hk : k < 4 ^ spN p) :
    spLayoutOK (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k
      (spArmB (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k) = true := by
  have h := spGroupLayoutOK_all
  simp only [List.all_eq_true, List.mem_range] at h
  have h2 := h p hp
  simp only [spGroupLayoutOK, List.all_eq_true, List.mem_range] at h2
  exact h2 k hk

/-- The slot of chain `i`'s last step, in its group. -/
def spTip (i : Nat) : V := .n (spSlot (i / 3 == 0) (spState (i / 3)).2.2 (i % 3) 2)

theorem spLeafCells_eq : spLeafCells = .n 0 :: .n (spC + 2) :: (List.range 64).map spTip := by
  decide +kernel

/-- **Where the leaf's padding run is**: inserted, above the cells, at most at the output run, and
the output run below the virtual run. -/
theorem spLeafPad :
    (spLeafM.1.findIdx? isKeccak).isSome = true ∧
      (∀ v ∈ spLeafCells, v = .n v.idx ∧ v.idx < padBase isKeccak spLeafM.1) ∧
      padBase isKeccak spLeafM.1 ≤ spLeafM.2.2 ∧ spLeafM.2.2 + 1 < spVPad := by
  decide +kernel

/-- `g^128`, the target sum in the exponent. -/
theorem spTarget_eq : spTarget = gen ^ 128 := by
  rw [Value.gen_pow_eq_ofK, spTarget, word, Value.ofBits_zero]
  rw [← ofK_eq_ofLimbs]
  exact congrArg ofK (by decide +kernel)

end
end LeanVM.Guest.B1.Sig
