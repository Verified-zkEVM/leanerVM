import LeanVM.Protocol.LeanIsa

/-!
# Tests: the leanISA instance

* **The stack against the pinned Python.** For two announced size vectors, the stacked size and
  every column's offset (a `KECCAK` input lane: `QKECCAK`'s offset plus its slot times the
  table's height; an output lane, derived: none) equal the placement indices of the pinned verifier's `build_layout`
  (`python-verifier/verifier.py` at leanVM `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462`, for a
  program of four `XOR` instructions; driver `layout_driver.py` of the port). The first has a
  table as tall as the memory and three more, and a `KECCAK` table of `2^16` rows: ties go to the
  lower global index, the shared columns first. The second mixes heights and has a `KECCAK`
  table of eight rows, which takes the floor height `2^9`. Both announce full tables (`2^τ`
  rows); a table's height is the least power of two holding its rows (and at least the table's
  floor), so the stack is the same for any row count of the same height.
* **Admissible sizes.** The first vector is admissible, and so is one with row counts that are
  not powers of two, an empty table among them, and a `KECCAK` table of five rows (below its
  floor); the memory below `2^16`, a table above `2^32` rows and a stack above `2^28` are
  rejected, and so is the WHIR rate `5`.
* **The public lines and the bus.** The third line is `MEM_TOP` with cells `0, 0`, not sent;
  six boundary blocks, three per side; the Keccak region is `QKECCAK` with `2^τ_KECCAK` steps.
* **The relation is decidable, and the instance meets the bus phase's conditions.**
* **Not evaluated: a witness stacked and read back.** Even the smallest shape is too slow to
  evaluate: the stacking and the column reads are written for proofs, not for speed. The
  read-back is a theorem of the adaptor instead.
-/

namespace LeanVMTests.Protocol.LeanIsa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa

/-- Four `XOR` instructions: a bytecode of log-size `2`. -/
def prog4 : Program := ⟨2, by decide, fun _ ↦ .xor 0 0 0⟩

/-- A table as tall as the memory, and three more. -/
def s₁ : Sizes := ⟨16, by decide, ![2 ^ 16, 2 ^ 3, 2 ^ 16, 2 ^ 4, 2 ^ 16, 2 ^ 16]⟩

/-- Mixed heights, the `KECCAK` table of eight rows. -/
def s₂ : Sizes := ⟨18, by decide, ![2 ^ 2, 2 ^ 18, 2 ^ 5, 2 ^ 0, 2 ^ 7, 2 ^ 3]⟩

/-- The heights of `s₂`, from row counts that are not powers of two, an empty table among them,
and a `KECCAK` table of five rows. -/
def s₃ : Sizes := ⟨18, by decide, ![3, 2 ^ 17 + 1, 17, 0, 100, 5]⟩

-- A table's height is the least power of two holding its rows, `KECCAK`'s at least `2^9`; an
-- empty table has one row, a padding row.
#guard (List.finRange 6).map s₃.τ = (List.finRange 6).map s₂.τ
#guard (List.finRange 6).map s₂.τ = [2, 18, 5, 0, 7, 9]

/-- Every column's offset in the stack, in global order: its block's; a `KECCAK` input lane's,
`QKECCAK`'s offset plus its slot times the table's height (the lane is the column of `QKECCAK`'s
block at that slot); `none` for an output lane, which is derived. -/
def offsets (prog : Program) (s : Sizes) : List (Option ℕ) :=
  columns.map fun c ↦
    if IsOut c then none
    else if h : IsLane c then
      some ((blocks prog s).offset (keccakBlock prog s) + (laneSlot c).val * 2 ^ s.τ 5)
    else some ((blocks prog s).offset (blockOf c h))

#guard leanIsaμ prog4 s₁ = 24
#guard offsets prog4 s₁ =
    [some 4194304, some 4259840, some 4325376, some 4390912, some 9503080, some 0, some 4456448,
     some 4521984, some 4587520, some 4653056, some 4718592, some 4784128, some 4849664,
     some 4915200, some 4980736, some 5046272, some 5111808, some 5177344, some 5242880,
     some 5308416, some 5373952, some 9502960, some 9502968, some 9502976, some 9502984,
     some 9502992, some 9503000, some 9503008, some 9503016, some 9503024, some 9503032,
     some 9503040, some 9503048, some 9503056, some 9503064, some 9503072, some 5439488,
     some 5505024, some 5570560, some 5636096, some 5701632, some 5767168, some 5832704,
     some 5898240, some 9502720, some 9502736, some 9502752, some 9502768, some 9502784,
     some 9502800, some 9502816, some 9502832, some 9502848, some 9502864, some 9502880,
     some 9502896, some 9502912, some 9502928, some 9502944, some 5963776, some 6029312,
     some 6094848, some 6160384, some 6225920, some 6291456, some 6356992, some 6422528,
     some 6488064, some 6553600, some 6619136, some 6684672, some 6750208, some 6815744,
     some 6881280, some 6946816, some 7012352, some 7077888, some 7143424, some 7208960,
     some 7274496, some 7340032, some 7405568, some 7471104, some 7536640, some 7602176,
     some 7667712, some 0, some 65536, some 131072, some 196608, some 262144, some 327680,
     some 393216, some 458752, some 524288, some 589824, some 655360, some 720896, some 786432,
     some 851968, some 917504, some 983040, some 1048576, some 1114112, some 1179648,
     some 1245184, some 1310720, some 1376256, some 1441792, some 1507328, some 1572864, none,
     none, none, none, none, none, none, none, none, none, none, none, none, none, none, none,
     none, none, none, none, none, none, none, none, none, some 7733248, some 7798784,
     some 7864320, some 7929856, some 7995392, some 8060928, some 8126464, some 8192000,
     some 8257536, some 8323072, some 8388608, some 8454144, some 8519680, some 8585216,
     some 8650752, some 8716288, some 8781824, some 8847360, some 8912896, some 8978432,
     some 9043968, some 9109504, some 9175040, some 9240576, some 9306112, some 9371648,
     some 9437184]

#guard leanIsaμ prog4 s₂ = 23
#guard offsets prog4 s₂ =
    [some 0, some 262144, some 524288, some 786432, some 5036032, some 4980736, some 5036036,
     some 5036040, some 5036044, some 5036048, some 5036052, some 5036056, some 5036060,
     some 5036064, some 5036068, some 5036072, some 5036076, some 5036080, some 5036084,
     some 5036088, some 5036092, some 1048576, some 1310720, some 1572864, some 1835008,
     some 2097152, some 2359296, some 2621440, some 2883584, some 3145728, some 3407872,
     some 3670016, some 3932160, some 4194304, some 4456448, some 4718592, some 5035776,
     some 5035808, some 5035840, some 5035872, some 5035904, some 5035936, some 5035968,
     some 5036000, some 5036096, some 5036097, some 5036098, some 5036099, some 5036100,
     some 5036101, some 5036102, some 5036103, some 5036104, some 5036105, some 5036106,
     some 5036107, some 5036108, some 5036109, some 5036110, some 5033984, some 5034112,
     some 5034240, some 5034368, some 5034496, some 5034624, some 5034752, some 5034880,
     some 5035008, some 5035136, some 5035264, some 5035392, some 5035520, some 5035648,
     some 5013504, some 5014016, some 5014528, some 5015040, some 5015552, some 5016064,
     some 5016576, some 5017088, some 5017600, some 5018112, some 5018624, some 5019136,
     some 5019648, some 4980736, some 4981248, some 4981760, some 4982272, some 4982784,
     some 4983296, some 4983808, some 4984320, some 4984832, some 4985344, some 4985856,
     some 4986368, some 4986880, some 4987392, some 4987904, some 4988416, some 4988928,
     some 4989440, some 4989952, some 4990464, some 4990976, some 4991488, some 4992000,
     some 4992512, some 4993024, none, none, none, none, none, none, none, none, none, none,
     none, none, none, none, none, none, none, none, none, none, none, none, none, none, none,
     some 5020160, some 5020672, some 5021184, some 5021696, some 5022208, some 5022720,
     some 5023232, some 5023744, some 5024256, some 5024768, some 5025280, some 5025792,
     some 5026304, some 5026816, some 5027328, some 5027840, some 5028352, some 5028864,
     some 5029376, some 5029888, some 5030400, some 5030912, some 5031424, some 5031936,
     some 5032448, some 5032960, some 5033472]

/-! ## Admissible sizes -/

#guard decide (s₁.Admissible prog4)
#guard decide (s₂.Admissible prog4)
#guard decide (s₃.Admissible prog4)
#guard leanIsaμ prog4 s₃ = leanIsaμ prog4 s₂
#guard !decide (Sizes.Admissible prog4 ⟨15, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩)
#guard !decide (Sizes.Admissible prog4 ⟨16, by decide, ![2 ^ 32 + 1, 8, 1, 1, 1, 1]⟩)
#guard !decide (Sizes.Admissible prog4 ⟨28, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩)
#guard leanIsaμ prog4 ⟨28, by decide, ![2 ^ 16, 8, 2 ^ 16, 16, 2 ^ 16, 2 ^ 16]⟩ = 31
#guard (List.range 6).map (fun ρ ↦ decide (validRate ρ)) = [false, true, true, true, true, false]

/-! ## The public lines, the bus, the Keccak region -/

#guard ((publicLines prog4 s₁ ⟨![1, 2, 3, 4]⟩).toList.map fun l ↦
    (l.col == memCol 0, l.col == memCol 1, l.col == memCol 2, l.cell0, l.cell1, l.sent)) =
  [(true, false, false, 1, 3, false), (false, true, false, 2, 4, false),
    (false, false, true, 0, 0, false)]

#guard (boundary prog4 s₁).map (fun b ↦ (b.κ, b.side)) =
  [(0, .push), (16, .push), (2, .push), (0, .pull), (16, .pull), (2, .pull)]

#guard (keccakRegion prog4 s₂).logSteps = 9
#guard (keccakRegion prog4 s₂).col == keccakCol

-- The instance's count columns are the opcode tables' read counts.
#guard (List.finRange 9).map (fun j ↦ (counts j).length) = [0, 0, 0, 4, 4, 2, 4, 4, 27]

/-- The instance meets the bus phase's conditions and the degree bound at every size. -/
example (prog : Program) (s : Sizes) :
    Bus.Conditions (leanIsaInstance prog s) ∧ (leanIsaInstance prog s).d ≤ 2 :=
  ⟨leanIsa_conditions prog s, le_rfl⟩

/-- The relation is decidable, by instance search. -/
example (prog : Program) (s : Sizes) (input : PublicInput)
    (q : Column (leanIsaInstance prog s).μ) :
    Decidable (M3Holds (leanIsaInstance prog s) input q) :=
  inferInstance

end LeanVMTests.Protocol.LeanIsa
