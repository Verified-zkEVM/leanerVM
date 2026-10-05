import LeanerVM.Semantics.FillBlocks

/-!
# Layer 10 tests: the fill block shape

The ladder is `crates/lean_compiler/src/lower.rs:462-533` and `crates/lean_vm/src/cpu/filler.rs`
at leanVM `a386121f`: each dummy is checked operand by operand against the compiler. Two
rejections: a program with no block has no `HasFillBlocks`, and a block whose closing jump is the
sentinel slot fails `IsFillBlock.below` alone (its dummies and its closing jump are fetched).
-/

namespace LeanerVMTests.Semantics.FillBlocks

open LeanerVM.Parameters LeanerVM.Semantics

/-! ## The ladder -/

example : fillSizes = [128, 64, 32, 16, 8, 4, 2, 1] := rfl

/-- A fill of `f` rows is delivered exactly by the ladder: the sizes add to `255`, one less than
the next power of two above the largest block. -/
example : fillSizes.sum = 255 := by decide

example : fillTables.length = 6 := rfl

-- The order is the order of the bus codes: `JUMP` is the fifth, which the fill plan and the frame
-- layout rely on.
example : fillTables = [.xor, .mulNative, .setConstant, .deref, .jump, .blake2s] := rfl

example : fillTables.Nodup := by decide

example (t : Opcode) : t ∈ fillTables := mem_fillTables t

/-! ## The dummies, as the compiler emits them -/

example : fillDummy .xor = .xor (gpow 4) (gpow 4) (gpow 4) := rfl

example : fillDummy .mulNative = .mulNative (gpow 4) (gpow 4) (gpow 4) := rfl

example : fillDummy .setConstant = .setConstant (gpow 4) 0 := rfl

example : fillDummy .deref = .deref (gpow 2) (gpow 0) (gpow 4) .cell := rfl

example : fillDummy .jump = .jump (gpow 3) (gpow 3) (gpow 3) := rfl

example : fillDummy .blake2s =
    .blake2s ![gpow 8, gpow 9, gpow 10, gpow 11] (gpow 4) (gpow 6) (gpow 3) := rfl

example : fillClose = .jump (gpow 0) (gpow 0) (gpow 1) := rfl

example (t : Opcode) : (fillDummy t).opcode = t := fillDummy_opcode t

/-! ## A program with no block -/

/-- Two slots, every one a `SET_CONSTANT`. -/
def blankProg : Program := ⟨1, by decide, fun _ ↦ .setConstant (gpow 0) 0⟩

/-- No block is present: the first dummy of any block would have to be fetched. -/
theorem blank_has_no_blocks : ¬ HasFillBlocks blankProg := by
  intro h
  obtain ⟨p, hp⟩ := h .xor 128 (by simp [fillSizes])
  obtain ⟨i, -, hi⟩ := (blankProg.fetch_eq_some_iff).mp (hp.dummies 0 (by norm_num))
  exact absurd hi (by simp [blankProg, fillDummy])

/-! ## The block must lie below the sentinel -/

/-- A size-one `XOR` block in a two-slot program: the dummy at slot `0`, the closing jump at slot
`1`, which is the sentinel slot. -/
def tinyProg : Program := ⟨1, by decide, ![fillDummy .xor, fillClose]⟩

/-- The dummy is fetched. -/
theorem tiny_dummies : ∀ i, i < 1 → tinyProg.fetch (gpow (0 + i)) = some (fillDummy .xor) := by
  intro i hi
  obtain rfl : i = 0 := by omega
  exact tinyProg.fetch_gpow ⟨0, by decide⟩

/-- The closing jump is fetched. -/
theorem tiny_close : tinyProg.fetch (gpow (0 + 1)) = some fillClose := by
  simpa [tinyProg] using tinyProg.fetch_gpow ⟨1, by decide⟩

/-- Both fetch conditions hold, and the block is rejected on `below` alone: the closing jump
would sit in the sentinel slot, where a row is acceptance test 20. -/
theorem tiny_block_not_below : ¬ IsFillBlock tinyProg .xor 1 0 := fun h ↦ by
  have := h.below
  revert this
  decide

/-! ## A program with every block

The compiler's layout, as in `tests/rust/leanisa_contracts.rs`: `main`'s halting jump, then for
each of the six tables its blocks of sizes `128 .. 1` back to back (`263` slots, `255` dummies and
eight closing jumps), then `SET_CONSTANT` up to the bytecode size `2048`, the sentinel slot
included. -/

/-- The table whose blocks occupy slots `1 + 263 k ..`: the `k`-th of the six. -/
def tableOf (k : ℕ) : Opcode := fillTables.getD k .xor

/-- Within a table's `263` slots, the offsets of the closing jumps of the sizes `128 .. 1`. -/
def closeOffsets : List ℕ := [128, 193, 226, 243, 252, 257, 260, 262]

/-- The instruction at slot `i`. -/
def ladderCode (i : ℕ) : Instr :=
  if i = 0 then .jump (gpow 0) (gpow 1) (gpow 0)
  else if i ≤ 1578 then
    (if (i - 1) % 263 ∈ closeOffsets then fillClose else fillDummy (tableOf ((i - 1) / 263)))
  else .setConstant (gpow 0) 0

/-- `1 + 6 * 263 = 1579` slots padded to `2^11`. -/
def ladderProg : Program := ⟨11, by decide, fun i ↦ ladderCode i⟩

/-- The instruction at a slot of the ladder program, fetched through the address of the slot. -/
theorem ladder_fetch (n : ℕ) (hn : n < 2048) : ladderProg.fetch (gpow n) = some (ladderCode n) :=
  ladderProg.fetch_gpow ⟨n, hn⟩

/-- A block of the layout: size `s` at offset `c` of the `k`-th table's slots, whose closing jump
is at an offset of `closeOffsets` and none of whose dummies is. -/
theorem ladder_block (t : Opcode) (k : ℕ) (hk : k < 6) (ht : tableOf k = t) (s c : ℕ)
    (hc : c + s < 263) (hclose : c + s ∈ closeOffsets)
    (hdummy : ∀ j, j < s → c + j ∉ closeOffsets) :
    IsFillBlock ladderProg t s (1 + 263 * k + c) := by
  refine ⟨?_, ?_, ?_⟩
  · show 1 + 263 * k + c + s + 1 < 2 ^ 11
    norm_num
    omega
  · intro j hj
    have hn : 1 + 263 * k + c + j < 2048 := by omega
    rw [ladder_fetch _ hn]
    congr 1
    unfold ladderCode
    have h0 : 1 + 263 * k + c + j ≠ 0 := by omega
    have h1 : 1 + 263 * k + c + j ≤ 1578 := by omega
    have h2 : (1 + 263 * k + c + j - 1) % 263 = c + j := by omega
    have h3 : (1 + 263 * k + c + j - 1) / 263 = k := by omega
    simp only [h0, h1, h2, h3, hdummy j hj, ht, ↓reduceIte]
  · have hn : 1 + 263 * k + c + s < 2048 := by omega
    rw [ladder_fetch _ hn]
    congr 1
    unfold ladderCode
    have h0 : 1 + 263 * k + c + s ≠ 0 := by omega
    have h1 : 1 + 263 * k + c + s ≤ 1578 := by omega
    have h2 : (1 + 263 * k + c + s - 1) % 263 = c + s := by omega
    simp only [h0, h1, h2, hclose, ↓reduceIte]

/-- Every table has a block of every size. -/
theorem ladder_hasFillBlocks : HasFillBlocks ladderProg := by
  intro t s hs
  obtain ⟨k, hk, ht⟩ : ∃ k, k < 6 ∧ tableOf k = t := by
    cases t
    exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩,
      ⟨3, by decide, rfl⟩, ⟨4, by decide, rfl⟩, ⟨5, by decide, rfl⟩]
  simp only [fillSizes, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, ladder_block t k hk ht 128 0 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, ladder_block t k hk ht 64 129 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, ladder_block t k hk ht 32 194 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, ladder_block t k hk ht 16 227 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, ladder_block t k hk ht 8 244 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, ladder_block t k hk ht 4 253 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, ladder_block t k hk ht 2 258 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, ladder_block t k hk ht 1 261 (by norm_num) (by decide) (by decide)⟩

/-- The sentinel slot holds a `SET_CONSTANT`, as `lib.rs:162` pads it. -/
theorem ladder_sentinelSafe : SentinelSafe ladderProg := by decide

/-- The layout is well formed bytecode: the inhabitant of both fields. -/
theorem ladder_wellFormed : WellFormedBytecode ladderProg :=
  ⟨ladder_sentinelSafe, ladder_hasFillBlocks⟩

/-- Every size of the ladder is required, the largest and the smallest included. -/
example (prog : Program) (h : HasFillBlocks prog) (t : Opcode) :
    (∃ p, IsFillBlock prog t 128 p) ∧ (∃ p, IsFillBlock prog t 1 p) :=
  ⟨h t 128 (by simp [fillSizes]), h t 1 (by simp [fillSizes])⟩

/-! ## The predicate tells blocks apart -/

/-- A block shifted by one slot is not a block: its last dummy would be a closing jump. -/
theorem ladder_shifted_not_block : ¬ IsFillBlock ladderProg .xor 128 2 := fun h ↦ by
  have h127 := h.dummies 127 (by norm_num)
  rw [show (2 + 127 : ℕ) = 129 from rfl, ladder_fetch 129 (by norm_num)] at h127
  have hc : ladderCode 129 = fillClose := by
    simp [ladderCode, closeOffsets]
  rw [hc] at h127
  have := congrArg Instr.opcode (Option.some.inj h127)
  rw [fillClose_opcode, fillDummy_opcode] at this
  exact absurd this (by decide)

/-- A block one dummy short is not a block: its closing jump would be a dummy, so the `close` field
fails while the `dummies` field holds. -/
theorem ladder_short_block_not_block : ¬ IsFillBlock ladderProg .xor 127 1 := fun h ↦ by
  have hc := h.close
  rw [show (1 + 127 : ℕ) = 128 from rfl, ladder_fetch 128 (by norm_num)] at hc
  have hd : ladderCode 128 = fillDummy .xor := by
    simp [ladderCode, closeOffsets, tableOf, fillTables]
  rw [hd] at hc
  have := congrArg Instr.opcode (Option.some.inj hc)
  rw [fillDummy_opcode, fillClose_opcode] at this
  exact absurd this (by decide)

/-- A block of one table is not a block of another: the first slot holds the `XOR` dummy. -/
theorem ladder_wrong_table_not_block : ¬ IsFillBlock ladderProg .mulNative 128 1 := fun h ↦ by
  have h0 := h.dummies 0 (by norm_num)
  rw [show (1 + 0 : ℕ) = 1 from rfl, ladder_fetch 1 (by norm_num)] at h0
  have hc : ladderCode 1 = fillDummy .xor := by
    simp [ladderCode, closeOffsets, tableOf, fillTables]
  rw [hc] at h0
  have := congrArg Instr.opcode (Option.some.inj h0)
  rw [fillDummy_opcode, fillDummy_opcode] at this
  exact absurd this (by decide)

/-- The layout with every `XOR` instruction replaced by a `SET_CONSTANT`: the `XOR` blocks
are gone. -/
def ladderNoXor : Program :=
  ⟨11, by decide, fun i ↦
    if (ladderCode i).opcode = .xor then .setConstant (gpow 0) 0 else ladderCode i⟩

/-- Acceptance test 15, as a program: with no `XOR` block the program is not well formed. -/
theorem ladderNoXor_no_blocks : ¬ HasFillBlocks ladderNoXor := by
  intro h
  obtain ⟨p, hp⟩ := h .xor 1 (by simp [fillSizes])
  obtain ⟨i, -, hi⟩ := (ladderNoXor.fetch_eq_some_iff).mp (hp.dummies 0 (by norm_num))
  have hop := congrArg Instr.opcode hi
  rw [fillDummy_opcode] at hop
  simp only [ladderNoXor] at hop
  by_cases h1 : (ladderCode i).opcode = Opcode.xor
  · simp only [h1, ↓reduceIte] at hop
    exact absurd hop (by decide)
  · simp only [h1, ↓reduceIte] at hop

end LeanerVMTests.Semantics.FillBlocks
