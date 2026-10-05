/-
  LeanerVM.Semantics.FillPlan

  The arithmetic of filling a table to a power of two: the target height, the traversals of the
  fill blocks that deliver it, and what the `JUMP` table can be filled to.
-/

module

public import LeanerVM.Semantics.FillBlocks
import Mathlib.Data.Nat.Log

/-!
# The fill plan

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category B, the arithmetic of
`crates/lean_vm/src/cpu/filler.rs:112-177` (`decompose`, `decompose_jump`, `solve`), identical at
leanVM `48a904208d682848dac0e18ef8b01ebfc40df9ad`. Only the arithmetic is here; the rows a plan
delivers are `Semantics.PaddedRows`.

**Every table but `JUMP`.** A table with `n` rows is filled to `fillTarget n (minRows op)`, the
least power of two at least `n`, the table's floor and `1` (`cpu/filler.rs:123-126`, `:163`; the
floor is `8` for `BLAKE2S` only, `:43`). The fill `p = target - n` is delivered by traversals of
the blocks of `fillSizes`: `fillGreedy p` is as many of the largest block as fit, then the binary
digits of the rest (`:112-121`). A traversal of the size-`s` block gives the table `s` rows and
the `JUMP` table one (the closing jump), so the traversals of one table cost `fillTraversals p`
`JUMP` rows, at most one per `128` rows of fill plus seven.

**The `JUMP` table.** It receives a closing jump from every traversal of every other table, and
its own fill is delivered by its own blocks, whose traversals give it `s + 1` rows
(`s` dummies that fall through, and the closing jump). The smallest traversal gives two rows, so a
gap of exactly one row is the one amount that cannot be delivered, and every other gap is a sum of
twos and threes (`jump_gap_decomp`). `JumpFeasible owed` says some power of two within the row cap
is at least the rows owed and is not one more than them (`cpu/filler.rs:131-132`, `:169-176`).

This is a plan, not the Rust's `solve`: Layer 10 needs the existence of one, and matching the
Rust's choices (its greedy loop for `JUMP`) is the witness generator's job (T2).

## Wrong readings excluded

* A table already on a power of two is not entered: `fillTarget` of a power of two at least the
  floor is itself, and the fill is `0`.
* The `JUMP` table is not independent of the others: its owed rows include one closing jump per
  traversal elsewhere, so its feasibility is a condition on the whole plan (`JumpFeasible`).
* A gap of one row is not deliverable: `JumpFeasible` excludes it, which is why a `JUMP` table
  owing `2^32 - 1` rows has no plan inside the cap.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-- The least number of rows a table can be proven over: `1`, and `8` for `BLAKE2S`, whose
argument Flock sizes to at least eight instances (`cpu/filler.rs:40-43`, `MIN_ROWS`). -/
def minRows : Opcode → ℕ
  | .blake2s => 8
  | _ => 1

/-- The height a table with `n` rows is filled to: the least power of two at least `n`, `floor`
and `1` (`cpu/filler.rs:123-126`, `ceil_pow2`, and `:163`). -/
def fillTarget (n floor : ℕ) : ℕ := 2 ^ Nat.clog 2 (max (max n floor) 1)

/-- The traversals that deliver a fill of `p` rows, per size of `fillSizes`: as many of the
largest block as fit, then one per set bit of the remainder (`cpu/filler.rs:112-121`). -/
def fillGreedy (p : ℕ) : List ℕ :=
  [p / 128, p % 128 / 64, p % 64 / 32, p % 32 / 16, p % 16 / 8, p % 8 / 4, p % 4 / 2, p % 2]

/-- The traversals in all: also the closing jumps the fill adds to the `JUMP` table. -/
def fillTraversals (p : ℕ) : ℕ := (fillGreedy p).sum

/-- The rows the `JUMP` table owes before its own fill, given the rows `rows` each table has: its
own, and one closing jump for every traversal of the fill of every other table
(`cpu/filler.rs:166-167`, `owed`). -/
def jumpOwed (rows : Opcode → ℕ) : ℕ :=
  rows .jump + ((fillTables.filter (· ≠ .jump)).map fun op ↦
    fillTraversals (fillTarget (rows op) (minRows op) - rows op)).sum

/-- The `JUMP` table owing `owed` rows can be filled within the row cap: some power of two at most
`2^maxLogRows` is at least `owed` and is not `owed + 1`, since no traversal delivers a single row
(`cpu/filler.rs:131-132`). -/
def JumpFeasible (owed : ℕ) : Prop :=
  ∃ τ ≤ maxLogRows, owed ≤ 2 ^ τ ∧ 2 ^ τ ≠ owed + 1

/-! ## Load-bearing lemmas -/

/-- The target holds the rows the table already has. -/
theorem le_fillTarget (n floor : ℕ) : n ≤ fillTarget n floor :=
  (le_max_left n floor).trans <| (le_max_left _ 1).trans (Nat.le_pow_clog (by norm_num) _)

/-- The target holds the table's floor. -/
theorem floor_le_fillTarget (n floor : ℕ) : floor ≤ fillTarget n floor :=
  (le_max_right n floor).trans <| (le_max_left _ 1).trans (Nat.le_pow_clog (by norm_num) _)

/-- The target is a power of two. -/
theorem fillTarget_pow (n floor : ℕ) : ∃ τ, fillTarget n floor = 2 ^ τ := ⟨_, rfl⟩

/-- The target is positive. -/
theorem fillTarget_pos (n floor : ℕ) : 0 < fillTarget n floor := Nat.two_pow_pos _

/-- A power of two that holds the rows and the floor holds the target. -/
theorem fillTarget_le {n floor τ : ℕ} (hn : n ≤ 2 ^ τ) (hf : floor ≤ 2 ^ τ) :
    fillTarget n floor ≤ 2 ^ τ :=
  Nat.pow_le_pow_right (by norm_num)
    ((Nat.clog_le_iff_le_pow (by norm_num)).mpr (max_le (max_le hn hf) (Nat.one_le_two_pow)))

/-- The target of a count that is already a power of two, above the floor, is that count. -/
theorem fillTarget_eq {n floor τ : ℕ} (h : max (max n floor) 1 = 2 ^ τ) :
    fillTarget n floor = 2 ^ τ := by
  rw [fillTarget, h, Nat.clog_pow _ _ (by norm_num)]

/-- The traversals deliver the fill exactly: the size-`s` blocks, traversed as `fillGreedy p`
says, hold `p` rows in all. -/
theorem fillGreedy_sum (p : ℕ) : (List.zipWith (· * ·) (fillGreedy p) fillSizes).sum = p := by
  simp only [fillGreedy, fillSizes, List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons,
    List.sum_nil]
  omega

/-- A table with `n` rows reaches its target: its rows and the rows of the traversals add up. -/
theorem fill_rows_sum (n floor : ℕ) :
    n + (List.zipWith (· * ·) (fillGreedy (fillTarget n floor - n)) fillSizes).sum =
      fillTarget n floor := by
  rw [fillGreedy_sum]
  exact Nat.add_sub_cancel' (le_fillTarget n floor)

/-- The bulk of a fill rides the largest block: one closing jump per `128` rows, and at most seven
more for the remainder (`cpu/filler.rs:262-275`, `fill_uses_bulk_blocks`). -/
theorem fillTraversals_le (p : ℕ) : fillTraversals p ≤ p / 128 + 7 := by
  -- Each remaining digit is at most one. Proved one at a time: `omega` over all of the nested
  -- quotients and remainders at once does not terminate in reasonable time.
  have h1 : p % 128 / 64 ≤ 1 := by omega
  have h2 : p % 64 / 32 ≤ 1 := by omega
  have h3 : p % 32 / 16 ≤ 1 := by omega
  have h4 : p % 16 / 8 ≤ 1 := by omega
  have h5 : p % 8 / 4 ≤ 1 := by omega
  have h6 : p % 4 / 2 ≤ 1 := by omega
  have h7 : p % 2 ≤ 1 := by omega
  simp only [fillTraversals, fillGreedy, List.sum_cons, List.sum_nil]
  exact Nat.add_le_add_left
    ((add_le_add h1 (add_le_add h2 (add_le_add h3 (add_le_add h4 (add_le_add h5
      (add_le_add h6 (add_le_add h7 (le_refl 0)))))))).trans (by norm_num)) _

/-- The traversals that deliver a `JUMP` gap, as the pair (size-one, size-two): a gap is twos from
the size-one block (a dummy jump and the closing jump) and threes from the size-two block, so an
even gap is all twos and an odd one takes one three (`cpu/filler.rs:128-147`). -/
def jumpMix (gap : ℕ) : ℕ × ℕ :=
  if gap % 2 = 0 then (gap / 2, 0) else ((gap - 3) / 2, 1)

/-- Every gap but one is delivered by the mix: `2a + 3b` rows. -/
theorem jumpMix_spec {gap : ℕ} (h : gap ≠ 1) :
    2 * (jumpMix gap).1 + 3 * (jumpMix gap).2 = gap := by
  unfold jumpMix
  split_ifs with he <;> simp only <;> omega

/-- Every gap but one is a sum of twos and threes, the rows of a traversal of the size-one and the
size-two `JUMP` block (`cpu/filler.rs:128-147`). -/
theorem jump_gap_decomp (gap : ℕ) (h : gap ≠ 1) : ∃ a b : ℕ, gap = 2 * a + 3 * b :=
  ⟨_, _, (jumpMix_spec h).symm⟩

/-- A `JUMP` table owing at most `2^31` rows can be filled: the cap `2^32` is a power of two
that is neither too small nor one more than the rows owed. -/
theorem jumpFeasible_of_le {owed : ℕ} (h : owed ≤ 2 ^ 31) : JumpFeasible owed :=
  ⟨32, by decide, h.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)), by omega⟩

/-- A table with at most `2^k` rows, `k` at least `3`, owes the `JUMP` table at most its own `2^k`
rows and one closing jump per traversal elsewhere, which is at most `2^k / 128 + 7` for each of
the five other tables. -/
theorem jumpOwed_le {rows : Opcode → ℕ} {k : ℕ} (hk : 3 ≤ k) (h : ∀ op, rows op ≤ 2 ^ k) :
    jumpOwed rows ≤ 2 ^ k + 5 * (2 ^ k / 128 + 7) := by
  have hfloor : ∀ op, minRows op ≤ 2 ^ k := fun op ↦ by
    have h8 : 8 ≤ 2 ^ k := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    cases op <;> simp only [minRows] <;> omega
  have hterm : ∀ op, fillTraversals (fillTarget (rows op) (minRows op) - rows op) ≤
      2 ^ k / 128 + 7 := fun op ↦ by
    have hle : fillTarget (rows op) (minRows op) - rows op ≤ 2 ^ k :=
      (Nat.sub_le _ _).trans (fillTarget_le (h op) (hfloor op))
    exact (fillTraversals_le _).trans (by have := Nat.div_le_div_right (c := 128) hle; omega)
  have hsum := List.sum_le_length_nsmul
    ((fillTables.filter (· ≠ .jump)).map fun op ↦
      fillTraversals (fillTarget (rows op) (minRows op) - rows op)) (2 ^ k / 128 + 7)
    (fun x hx ↦ by
      obtain ⟨op, -, rfl⟩ := List.mem_map.mp hx
      exact hterm op)
  have hlen : (fillTables.filter (· ≠ .jump)).length = 5 := by decide
  rw [List.length_map, hlen, smul_eq_mul] at hsum
  unfold jumpOwed
  exact Nat.add_le_add (h .jump) hsum

end
end LeanerVM.Semantics
