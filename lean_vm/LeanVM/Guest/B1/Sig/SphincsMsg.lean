/-
  LeanVM.Guest.B1.Sig.SphincsMsg

  The facts `verify_sig_lean_sphincs`'s soundness glues: the encoding's tail cells and the bytes
  past its 292, the message's bytes, the chains, the tops' list and the end state.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsForest

/-!
# Glue

* `kXorByte_getD_ne`, `tailCells_292`: the encoding's first block reads cells `4 … 7` as cells;
* `bytes_past_counter`: past byte `292`, the cells end in a counter below `2^32`, whose bytes past
  the fourth are zero;
* `sphincs_bytesLE_cellPairVal`: a message's bytes are its two cells';
* `chainT_eq_sChain`: the codeword's chains are the scheme's;
* `getD_pairs`: the tops' list of pairs;
* `cSt_eight`: the encoding ends in `n17` and the bound in `n18`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

theorem kXorByte_getD_ne (cs : List KC) (pos v b i : Nat) (hi : i ≠ pos / 16) :
    (kXorByte cs pos v b).2.1.getD i .zero = cs.getD i .zero := by
  unfold kXorByte
  simp only
  split <;> simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hi)]

theorem getD_append_replicate (cs : List KC) (n i : Nat) (hi : i < cs.length) :
    (cs ++ List.replicate n KC.zero).getD i .zero = cs.getD i .zero := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- **The encoding's first block reads its cells `4 … 7` as cells.** -/
theorem tailCells_292 (cells : List V) (hl : 8 ≤ cells.length) (b : Nat) :
    TailCells (blockOf (kMsgCells (cells.map KC.cell) 292 b) 0) := by
  have key : ∀ k, 4 ≤ k → k < 8 → (blockOf (kMsgCells (cells.map KC.cell) 292 b) 0).getD k .zero =
      .cell (cells.getD k (.n 0)) := by
    intro k hk4 hk8
    simp only [blockOf, Nat.mul_zero, Nat.zero_div, List.drop_zero]
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), ← List.getD_eq_getElem?_getD]
    simp only [kMsgCells, kBlocksOf]
    rw [kXorByte_getD_ne _ _ _ _ _ (by omega), kXorByte_getD_ne _ _ _ _ _ (by omega),
      getD_append_replicate _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by omega : k < cells.length)]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨_, key 4 (by norm_num) (by norm_num)⟩
  · exact ⟨_, key 5 (by norm_num) (by norm_num)⟩
  · exact ⟨_, key 6 (by norm_num) (by norm_num)⟩
  · exact ⟨_, key 7 (by norm_num) (by norm_num)⟩

/-- **Past byte `292`**, the cells end in a counter below `2^32`. -/
theorem bytes_past_counter (cs : List E) (hl : cs.length = 18) {N : Nat} (hN : N < 2 ^ 32) :
    ∀ j, 292 ≤ j → (cellsBytes (cs ++ [eOfNat N])).getD j 0 = 0 := by
  intro j hj
  rw [cellsBytes_eq_flatMap, List.flatMap_append, List.getD_eq_getElem?_getD]
  have hlen : (cs.flatMap cellBytes).length = 16 * 18 := by
    rw [← cellsBytes_eq_flatMap, length_cellsBytes, hl]
  rw [List.getElem?_append_right (by omega), hlen]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [cellBytes_eOfNat (by omega)]
  by_cases hk : j - 16 * 18 < 16
  · rw [List.getElem?_eq_getElem (by simp [leBytes]; omega), Option.getD_some, getElem_leBytes]
    have : N / 256 ^ (j - 16 * 18) = 0 := by
      apply Nat.div_eq_of_lt
      calc N < 2 ^ 32 := hN
        _ = 256 ^ 4 := by norm_num
        _ ≤ 256 ^ (j - 16 * 18) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [this]
    rfl
  · rw [List.getElem?_eq_none (by simp [leBytes]; omega)]
    rfl

/-- A message's bytes are its two cells', the first low. -/
theorem sphincs_bytesLE_cellPairVal (c d : E) :
    Sphincs.bytesLE 32 (cellPairVal c d) = cellBytes c ++ cellBytes d := by
  have h0 := cellNat_lt c
  have h1 := cellNat_lt d
  have ht : (cellPairVal c d).toNat = cellNat c + 2 ^ 128 * cellNat d := by
    rw [cellPairVal, BitVec.toNat_append, toNat_cellVal, toNat_cellVal, Nat.shiftLeft_eq, mul_comm,
      two_pow_mul_or h0]
    ring
  rw [sphincs_bytesLE_eq, ht, cellBytes_eq_leBytes, cellBytes_eq_leBytes,
    show (2 : Nat) ^ 128 = 256 ^ 16 by norm_num, show 32 = 16 + 16 from rfl,
    leBytes_add_mul _ _ _ _ (by norm_num; omega)]

theorem chainT_eq_sChain {f : Nat → Nat → E → E} {pp : E} {adr : Nat → E} {i : Nat}
    (hf : ∀ s y, f i s y = (hcell [pp, adr s, y]).1) :
    ∀ (m s : Nat) (x : E), chainT f i m s x = sChain pp adr m s x
  | 0, _, _ => rfl
  | m + 1, s, x => by
      rw [chainT, sChain, hf]
      exact chainT_eq_sChain hf m (s + 1) _

/-- The pairs' list. -/
theorem getD_pairs {α : Type} (x y : Nat → α) (d : α) :
    ∀ n c, c < n → ((List.range n).flatMap fun k => [x k, y k]).getD (2 * c) d = x c ∧
      ((List.range n).flatMap fun k => [x k, y k]).getD (2 * c + 1) d = y c
  | 0, _, h => absurd h (by omega)
  | n + 1, c, h => by
      rw [List.range_succ, List.flatMap_append]
      have hlen : ((List.range n).flatMap fun k => [x k, y k]).length = 2 * n := by
        simp [List.length_flatMap]; ring
      rcases Nat.lt_or_ge c n with hc | hc
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
        exact getD_pairs x y d n c hc
      · have hcn : c = n := by omega
        subst hcn
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
          List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
        simp

theorem pairs_length {α : Type} (x y : Nat → α) (n : Nat) :
    ((List.range n).flatMap fun k => [x k, y k]).length = 2 * n := by
  simp [List.length_flatMap]; ring

/-- **The end state**: the encoding ends in `n17`, the bound in `n18`. -/
theorem cSt_eight : (cSt 8).1 = some (.n 17) ∧ (cSt 8).2.1 = .n 18 := ⟨rfl, rfl⟩

end
end LeanVM.Guest.B1.Sig
