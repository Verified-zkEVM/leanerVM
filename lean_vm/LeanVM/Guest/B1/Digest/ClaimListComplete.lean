/-
  LeanVM.Guest.B1.Digest.ClaimListComplete

  `claim_list_digest`, completely: its meaning's claims, and the memory an honest run leaves at
  its chain buffer, give its core IR relation.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCLast
public import LeanVM.Guest.B1.Digest.CompleteSmall

/-!
# `claim_list_digest`, completely

`ClaimChainMem rd chain entries n`: the memory an honest run leaves at its chain buffer `chain`,
the sponge state after each group of `17` claims (`68` cells) at `chain · g^(13q)`.
`claim_list_digest_complete`: on a memory image, `n < 17 · 2^16` claims at `entries`
(`ClaimListOut`) and that memory give the relation. Each branch is evaluated on its own
(`Fwd.ev` of `clZEval`, `clEEval`): the empty list hashes the empty string; the nonempty one splits
`n = 17a + b` (`list_split_complete`), runs the groups (`guard_complete`, `l16_block`) and the last
`b` claims (`claimLast_complete`), the oracle naming the split, the buffer and the digest.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

/-- **The memory an honest run of `claim_list_digest` leaves** at its chain buffer `chain`: after
`q ≤ n / 17` groups, the sponge state after the first `68q` cells at `entries`, at
`chain · g^(13q)`. -/
def ClaimChainMem (rd : Reader) (chain entries : E) (n : ℕ) : Prop :=
  ∀ q ≤ n / 17, StateAt rd (chain * gen ^ (13 * q)) 0
    (absorbChunks (8 * q) zeroState (cellsBytes (memRun rd entries (68 * q))))

theorem readsAt_take' {p : E} {cells : List E} (hr : ReadsAt rd p cells) (k : ℕ) :
    ReadsAt rd p (cells.take k) := fun i hi => by
  rw [List.getElem_take]; exact hr i (by simp at hi; omega)

theorem readsAt_drop' {p : E} {cells : List E} (hr : ReadsAt rd p cells) (k : ℕ) :
    ReadsAt rd (p * gen ^ k) (cells.drop k) := fun i hi => by
  rw [loadHolds_mul_gen_pow, List.getElem_drop]; exact hr _ (by simp at hi; omega)

theorem memRun_take {p : E} {cells : List E} (hr : ReadsAt rd p cells) {k : ℕ}
    (hk : k ≤ cells.length) : memRun rd p k = cells.take k := by
  rw [readsAt_memRun (readsAt_take' hr k), List.length_take, Nat.min_eq_left hk]

theorem canon_take {cells : List E} (hc : AllCanonical cells) (k : ℕ) : AllCanonical (cells.take k) :=
  fun c h => hc c (List.mem_of_mem_take h)

theorem canon_drop {cells : List E} (hc : AllCanonical cells) (k : ℕ) : AllCanonical (cells.drop k) :=
  fun c h => hc c (List.mem_of_mem_drop h)

theorem l16_shapeF : loopShapeF (coreProgram.getD 320 default) "__loop15" = true := by
  have h := l16c_ok
  simp only [l16cOk, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1

/-- The groups of claims: `__loop15`'s block at every group below `a`. -/
theorem cl_blocks {chain entries : E} {n : ℕ} {cells : List E} (hl : cells.length = 4 * n)
    (hr : ReadsAt rd entries cells) (hc : AllCanonical cells) (hmem : ClaimChainMem rd chain entries n) :
    ∀ j < n / 17, LoopBlock rd (coreProgram.getD 320 default) (gen ^ j) (gen ^ (n / 17))
      [chain, entries] := by
  intro j hj
  have h68 : 68 * j + 68 ≤ cells.length := by omega
  have hS := hmem j (by omega)
  have hS1 := hmem (j + 1) (by omega)
  rw [memRun_take hr (by omega)] at hS
  rw [memRun_take hr (by omega), show 68 * (j + 1) = 68 * j + 68 by ring, List.take_add,
    cellsBytes_append] at hS1
  have hpre : (cellsBytes (cells.take (68 * j))).length = rate * (8 * j) := by
    rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
    show 16 * (68 * j) = 136 * (8 * j); omega
  refine l16_block hpre (by rw [gen_pow_pow]; exact hS) (cells := ((cells.drop (68 * j)).take 68))
    (by simp; omega) ?_ (canon_take (canon_drop hc _) _) fun c => ?_
  · rw [gen_pow_pow]; exact readsAt_take' (readsAt_drop' hr _) _
  · have := hS1 c
    rw [gen_pow_pow, loadHolds_mul_gen_pow]
    rw [loadHolds_mul_gen_pow, show 13 * (j + 1) + (0 + c.val) = 13 * j + (13 + c.val) by ring,
      show 8 * (j + 1) = 8 * j + 8 by ring] at this
    exact this

theorem cl_param (σ : Val) : (Fn.params Data.core23).map σ = [σ (.n 0), σ (.n 1)] := rfl

end
end LeanVM.Guest.B1.Digest
