/-
  LeanVM.Guest.Value.ModelChain

  Chains of `BLAKE2S` rows under a hash model: the guest's chain lemmas (`Value/Hash.lean`) in
  the form a `HashModel` supports, every hash an answered one.
-/

module

public import LeanVM.Guest.Value.HashModel

/-!
# Chains under a hash model

`Value/Hash.lean` proves that the guest's chains of `BLAKE2S` rows compute `blake2sBytes`. Over a
`HashModel` the same chains give an *answered* hash: `M.H x = some d` with the last row's output
the digest's cells. The intermediate chaining values are never named: a run of non-final blocks
only extends a prefix (`HashModel.prefix_run`), and only a prefix's last block is read
(`HashModel.final`). The forms the guest uses:

| deployed (`Value/Hash.lean`) | here |
|---|---|
| `blake2s_default` (one block under the IV) | `HashModel.one_block` |
| `blake2s_empty` (the empty input) | `HashModel.empty` |
| `chain_nonfinal` from the IV, or from any prefix | `HashModel.prefix_run` |
| `chain_final` after whole blocks | `HashModel.final_block` (and `HashModel.final`) |
| `chain_eq_blake2sBytes_blocks` | `HashModel.chain_blocks` |
| `chain_eq_blake2sBytes` | `HashModel.chain_bytes` |

At `HashModel.deployed` an answered hash is `blake2sBytes` (`deployed_H`), which recovers the
deployed lemmas' conclusions.
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash

@[expose] public section

namespace HashModel

variable (M : HashModel)

/-- **The deployed model answers BLAKE2s-256.** -/
theorem deployed_H {x : List UInt8} {d : Digest} : deployed.H x = some d ↔ d = blake2sBytes x := by
  show some (blake2sBytes x) = some d ↔ _
  rw [Option.some.injEq, eq_comm]

variable {M}

/-- **A run of non-final blocks extends a prefix**: from a prefix `bs` at `st 0`, `n` blocks at
the counters `64·(bs.length + j + 1)` with no flag reach a prefix of `bs` and their bytes
(`chain_nonfinal`, the chaining value left unnamed). -/
theorem prefix_run {bs : List (List UInt8)} {n : ℕ} {blocks : ℕ → Fin 4 → E} {st : ℕ → E × E}
    {md : ℕ → E} (h0 : M.Prefix bs (st 0))
    (hmd : ∀ j < n, md j = metadataCell (64 * (bs.length + j + 1)) false)
    (hc : ∀ j < n, M.sem.check (blocks j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2 (md j)) :
    M.Prefix (bs ++ (List.range n).map fun j ↦ blockBytes (blocks j)) (st n) := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have ih := ih (fun j hj ↦ hmd j (by omega)) (fun j hj ↦ hc j (by omega))
    have hcn := hc n (by omega)
    rw [hmd n (by omega)] at hcn
    have hlen : (bs ++ (List.range n).map fun j ↦ blockBytes (blocks j)).length + 1 =
        bs.length + n + 1 := by simp [Nat.add_assoc]
    have := M.prefix_step (st' := st (n + 1)) ih (by rw [hlen]; exact hcn)
    rwa [List.range_succ, List.map_append, List.map_singleton, ← List.append_assoc]

/-- **The last block after whole blocks**: a prefix `bs` and a last block of 64 data bytes at the
counter `64·(bs.length + 1)` with the flag: the model answers the hash of the bytes, and the
output is its cells (`chain_final` after whole blocks). -/
theorem final_block {bs : List (List UInt8)} {st : E × E} {m : Fin 4 → E} {out0 out1 : E}
    (h : M.Prefix bs st)
    (hc : M.sem.check m st.1 st.2 out0 out1 (metadataCell (64 * (bs.length + 1)) true)) :
    ∃ d, M.H (bs.flatten ++ blockBytes m) = some d ∧ (out0, out1) = digestScalars d := by
  refine M.final (m := m) (r := blockBytes m) h (by rw [length_blockBytes]) (Or.inr ?_)
    (by simp [length_blockBytes]) ?_
  · intro he
    have := congrArg List.length he
    rw [length_blockBytes] at this
    exact absurd this (by simp)
  · rw [length_blockBytes, show 64 * bs.length + 64 = 64 * (bs.length + 1) by ring]
    exact hc

/-- **One block under the IV** (`blake2s_default`; every Fiat-Shamir step and Merkle node): the
model answers the hash of the block's 64 bytes, and the output is its cells. -/
theorem one_block {m : Fin 4 → E} {out0 out1 : E}
    (hc : M.sem.check m ivCells.1 ivCells.2 out0 out1 (metadataCell 64 true)) :
    ∃ d, M.H (blockBytes m) = some d ∧ (out0, out1) = digestScalars d := by
  have := final_block (M := M) (bs := []) (st := ivCells) M.prefix_nil (by simpa using hc)
  simpa using this

/-- **The empty input** (`blake2s_empty`): one zero block at counter 0 with the flag under the
IV: the model answers the hash of `[]`. -/
theorem empty {out0 out1 : E}
    (hc : M.sem.check ![0, 0, 0, 0] ivCells.1 ivCells.2 out0 out1 (metadataCell 0 true)) :
    ∃ d, M.H [] = some d ∧ (out0, out1) = digestScalars d := by
  have hz : ∀ i, (![0, 0, 0, 0] : Fin 4 → E) i = 0 := by
    intro i
    fin_cases i <;> rfl
  have hb : blockBytes ![0, 0, 0, 0] = [] ++ List.replicate (64 - ([] : List UInt8).length) 0 := by
    simp only [blockBytes, hz, cellBytes_zero, List.nil_append, List.length_nil, Nat.sub_zero,
      ← List.replicate_add]
  simpa using M.final (bs := []) (st := ivCells) (r := []) M.prefix_nil (by simp) (Or.inl rfl) hb
    (by simpa using hc)

/-- **Whole blocks from the IV** (`chain_eq_blake2sBytes_blocks`; `statement_digest`,
`da_hash_roots`, `da_verify_cell`): `n + 1` blocks of data bytes, the last at the counter
`64·(n + 1)` with the flag: the model answers the hash of their bytes, and the last output is
its cells. -/
theorem chain_blocks {n : ℕ} {blocks : ℕ → Fin 4 → E} {st : ℕ → E × E} {md : ℕ → E}
    (h0 : st 0 = ivCells)
    (hmd : ∀ j < n, md j = metadataCell (64 * (j + 1)) false)
    (hfin : md n = metadataCell (64 * (n + 1)) true)
    (hc : ∀ j ≤ n, M.sem.check (blocks j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2 (md j)) :
    ∃ d, M.H ((List.range (n + 1)).flatMap fun j ↦ blockBytes (blocks j)) = some d ∧
      st (n + 1) = digestScalars d := by
  have hp := prefix_run (M := M) (bs := []) (n := n) (blocks := blocks) (st := st) (md := md)
    (by rw [h0]; exact M.prefix_nil) (fun j hj ↦ by rw [hmd j hj]; simp)
    (fun j hj ↦ hc j (by omega))
  rw [List.nil_append] at hp
  have hcn := hc n le_rfl
  rw [hfin] at hcn
  obtain ⟨d, hd, hout⟩ := final_block hp (by simpa using hcn)
  refine ⟨d, ?_, by rw [← hout]⟩
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.flatMap_def]
  exact hd

/-- **A whole chain from the IV over any bytes** (`chain_eq_blake2sBytes`): the `n + 1` blocks of
a byte string `d` zero-filled to whole blocks, the non-final ones at the cumulative counters,
the last at `d.length` with the flag: the model answers the hash of `d`, and the last output is
its cells. -/
theorem chain_bytes {n : ℕ} {blocks : ℕ → Fin 4 → E} {st : ℕ → E × E} {md : ℕ → E}
    {d : List UInt8} (hn : (d.length - 1) / 64 = n)
    (hbytes : (List.range (n + 1)).flatMap (fun j ↦ blockBytes (blocks j)) =
      d ++ List.replicate (64 * (n + 1) - d.length) 0)
    (h0 : st 0 = ivCells)
    (hmd : ∀ j < n, md j = metadataCell (64 * (j + 1)) false)
    (hfin : md n = metadataCell d.length true)
    (hc : ∀ j ≤ n, M.sem.check (blocks j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2 (md j)) :
    ∃ dg, M.H d = some dg ∧ st (n + 1) = digestScalars dg := by
  have hlo : 64 * n ≤ d.length := by
    rcases Nat.eq_zero_or_pos d.length with h | h
    · rw [h] at hn ⊢
      simp at hn
      omega
    · omega
  set bs := (List.range n).map fun j ↦ blockBytes (blocks j) with hbs_def
  have hbs : ∀ b ∈ bs, b.length = 64 := by
    intro b hb
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
    exact length_blockBytes _
  have hblen : bs.length = n := by simp [bs]
  have hflat : bs.flatten.length = 64 * n := by rw [length_flatten_of_64 bs hbs, hblen]
  have hsplit : (List.range (n + 1)).flatMap (fun j ↦ blockBytes (blocks j)) =
      bs.flatten ++ blockBytes (blocks n) := by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.flatMap_def]
  rw [hsplit] at hbytes
  have hpre : bs.flatten = d.take (64 * n) := by
    have := congrArg (List.take (64 * n)) hbytes
    rwa [List.take_left' hflat, List.take_append_of_le_length hlo] at this
  have hlast : blockBytes (blocks n) =
      d.drop (64 * n) ++ List.replicate (64 - (d.drop (64 * n)).length) 0 := by
    have := congrArg (List.drop (64 * n)) hbytes
    rw [List.drop_left' hflat, List.drop_append_of_le_length hlo] at this
    rw [this, List.length_drop]
    congr 2
    omega
  have hhi : d.length ≤ 64 * (n + 1) := by
    have := congrArg List.length hbytes
    simp only [List.length_append, length_blockBytes, List.length_replicate, hflat] at this
    omega
  have hp := prefix_run (M := M) (bs := []) (n := n) (blocks := blocks) (st := st) (md := md)
    (by rw [h0]; exact M.prefix_nil) (fun j hj ↦ by rw [hmd j hj]; simp)
    (fun j hj ↦ hc j (by omega))
  rw [List.nil_append, ← hbs_def] at hp
  have hcn := hc n le_rfl
  rw [hfin] at hcn
  have hne : bs = [] ∨ d.drop (64 * n) ≠ [] := by
    rcases Nat.eq_zero_or_pos n with h | h
    · left
      rw [← List.length_eq_zero_iff, hblen, h]
    · right
      intro he
      have := congrArg List.length he
      rw [List.length_drop] at this
      simp only [List.length_nil] at this
      have : d.length ≥ 64 * n + 1 := by
        have h1 : 1 ≤ (d.length - 1) / 64 := by omega
        have := (Nat.le_div_iff_mul_le (by norm_num)).mp h1
        omega
      omega
  obtain ⟨dg, hdg, hout⟩ := M.final hp (by rw [List.length_drop]; omega) hne hlast (by
    rw [hblen, List.length_drop, show 64 * n + (d.length - 64 * n) = d.length by omega]
    exact hcn)
  refine ⟨dg, ?_, by rw [← hout]⟩
  rw [hpre, List.take_append_drop] at hdg
  exact hdg

end HashModel

end
end LeanVM.Guest.Value
