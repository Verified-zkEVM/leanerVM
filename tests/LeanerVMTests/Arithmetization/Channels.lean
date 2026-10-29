import LeanerVM.Arithmetization.Channels
import LeanerVM.Semantics.Execution
import Clean.Air.Balance

/-!
# Layer 5 tests: the bus channels

A classic test for kernel evaluation. The three channels' separators are pinned against
specification §5.1 and `tables.rs:90-92`, the three element orders against §6.1, §6.2, §6.4 and
the flush builders of `tables.rs:127-166`, on literal messages, and the sixteen-slot tuples
against §5.1. The read gadgets are checked to emit a `pull` then a `push` on one channel, both of
multiplicity `1` and told apart by their direction tags, with the count advanced by `g`.
`imageOf` is read off literal prover data, the memory block's rows under its name, and a correct
memory read satisfies `MemChannel.Guarantees` while a wrong word does not; a three-row store and
the empty store are shown truncated. The bytecode guarantee is decodability alone, program- and
data-free (decision 14): an instruction's entry passes on every data, a flag pair that is no
store mode and a nonzero spare slot fail at every counter, and the guarantee is the same
proposition on any two data.

The last section pins Clean's direction-tagged bus over `K` (roadmap acceptance tests 13 and
14): a direction is an interaction's tag, independent of `-1 = 1`; a pull of multiplicity `1`
is granted the channel's guarantee and an active push owes it; `Balance.logUp`, whose
characteristic bound is `ringChar K = 2`, admits at most one interaction, while
`Balance.multiset`, the check the statement uses, rejects a message pushed twice and never
pulled, which the field sum `1 + 1 = 0` would accept.
-/
namespace LeanerVMTests.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization

/-! ## Separators (specification §5.1; `tables.rs:90-92`) -/

#guard channelSep StateChannel.toRaw = gpow 0
#guard channelSep MemChannel.toRaw = gpow 1
#guard channelSep BytecodeChannel.toRaw = gpow 2

-- The separators are the words `1, 2, 4`: `g^0, g^1, g^2` with `g = 0x2`.
#guard channelSep StateChannel.toRaw = 0x1
#guard channelSep MemChannel.toRaw = K.ofBits 0x2
#guard channelSep BytecodeChannel.toRaw = K.ofBits 0x4

/-- Separators decide in the kernel. -/
example : channelSep MemChannel.toRaw = gpow 1 ∧ channelSep BytecodeChannel.toRaw = gpow 2 := by
  decide +kernel

/-- The three channels are distinct raw channels, by name. -/
example : StateChannel.toRaw ≠ MemChannel.toRaw ∧ MemChannel.toRaw ≠ BytecodeChannel.toRaw :=
  ⟨fun h ↦ absurd (congrArg RawChannel.name h) (by decide),
    fun h ↦ absurd (congrArg RawChannel.name h) (by decide)⟩

/-- A channel that is none of the three has separator `0`, which is no separator. -/
def foreign : RawChannel K where
  name := "other"
  arity := 0
  Guarantees _ _ _ := True
  Requirements _ _ _ _ := True

#guard channelSep foreign = 0
example : channelSep foreign ≠ channelSep MemChannel.toRaw := by decide

/-! ## Element orders (specification §6.1, §6.2, §6.4; `tables.rs:127-166`) -/

def st : Regs K := ⟨gpow 3, gpow 5⟩
def mm : MemMsg K := ⟨gpow 3 * gpow 5, gpow 2, #v[K.ofBits 7, K.ofBits 8, K.ofBits 9]⟩
def bm : BytecodeMsg K := ⟨gpow 3, gpow 4, Opcode.deref.code, #v[gpow 4, 1, gpow 5, 1, 0, 0, 0]⟩

#guard (toElements st).toList = [gpow 3, gpow 5]
#guard (toElements mm).toList = [gpow 3 * gpow 5, gpow 2, K.ofBits 7, K.ofBits 8, K.ofBits 9]
#guard (toElements bm).toList =
  [gpow 3, gpow 4, Opcode.deref.code, gpow 4, 1, gpow 5, 1, 0, 0, 0]

/-- The orders as theorems, through the three `toElements` lemmas. -/
example : (toElements st).toList = [gpow 3, gpow 5] := regs_toElements st
example : (toElements mm).toList = [gpow 3 * gpow 5, gpow 2, K.ofBits 7, K.ofBits 8, K.ofBits 9] := by
  rw [memMsg_toElements]; rfl
example : (toElements bm).toList =
    [gpow 3, gpow 4, Opcode.deref.code, gpow 4, 1, gpow 5, 1, 0, 0, 0] := by
  rw [bytecodeMsg_toElements]; rfl

-- Sizes: two, five, and ten coordinates after the separator.
example : size Regs = 2 := rfl
example : size MemMsg = 5 := rfl
example : size BytecodeMsg = 10 := rfl

/-- The state message is the machine's register pair: `Regs.initial` is a message. -/
example : (toElements Regs.initial).toList = [1, 1] := by
  rw [regs_toElements]
  rfl

/-! ## The sixteen-slot tuples (specification §5.1) -/

#guard (busTuple StateChannel.toRaw (toElements st).toList).toList =
  [1, gpow 3, gpow 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (busTuple MemChannel.toRaw (toElements mm).toList).toList =
  [g, gpow 3 * gpow 5, gpow 2, K.ofBits 7, K.ofBits 8, K.ofBits 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (busTuple BytecodeChannel.toRaw (toElements bm).toList).toList =
  [g ^ 2, gpow 3, gpow 4, Opcode.deref.code, gpow 4, 1, gpow 5, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Slot `0` is the separator, slot `3` the first limb, slot `6` the padding. -/
example : (busTuple MemChannel.toRaw (toElements mm).toList)[0] = g ∧
    (busTuple MemChannel.toRaw (toElements mm).toList)[3] = K.ofBits 7 ∧
    (busTuple MemChannel.toRaw (toElements mm).toList)[6] = 0 := by
  simp only [busTuple_getElem, memMsg_toElements]
  decide

/-! ## The read gadgets (specification §6.2 "Flush rules") -/

/-- `memRead` is a `pull` then a `push` on the memory channel, both of multiplicity `1`, the
count advanced by `g`. -/
example (a c : Expression K) (v : Vector (Expression K) 3) :
    (memRead a c v).operations 0 =
      [.interact ⟨MemChannel.toRaw, .pull, 1, toElements (⟨a, c, v⟩ : MemMsg (Expression K))⟩,
       .interact ⟨MemChannel.toRaw, .push, 1,
         toElements (⟨a, Expression.const g * c, v⟩ : MemMsg (Expression K))⟩] :=
  rfl

/-- `bytecodeRead` likewise, on the bytecode channel. -/
example (pc c o : Expression K) (op : Vector (Expression K) 7) :
    (bytecodeRead pc c o op).operations 0 =
      [.interact ⟨BytecodeChannel.toRaw, .pull, 1,
         toElements (⟨pc, c, o, op⟩ : BytecodeMsg (Expression K))⟩,
       .interact ⟨BytecodeChannel.toRaw, .push, 1,
         toElements (⟨pc, Expression.const g * c, o, op⟩ : BytecodeMsg (Expression K))⟩] :=
  rfl

/-! ## The image in the prover data -/

/-- Two memory block rows `(idx, cntFin, m)`, matched on arity so that the kernel never
compares table names. The program has no table: it is public (decision 14). -/
def sampleData : ProverData K := fun _ n ↦
  match n with
  | 5 => #[#v[1, 1, 1, K.ofBits 2, K.ofBits 3], #v[g, 1, K.ofBits 4, K.ofBits 5, K.ofBits 6]]
  | _ => #[]

/-- A store whose table is told apart by name: `imageOf` reads the memory block's `"mem"`. -/
def namedData : ProverData K := fun name n ↦
  match name, n with
  | "mem", 5 => #[#v[1, 1, K.ofBits 9, K.ofBits 9, K.ofBits 9]]
  | _, _ => #[]

/-- Three memory rows: not a power of two. -/
def threeRows : ProverData K := fun _ n ↦
  match n with
  | 5 => #[#v[1, 1, 1, K.ofBits 2, K.ofBits 3], #v[g, 1, K.ofBits 4, K.ofBits 5, K.ofBits 6],
      #v[g ^ 2, 1, K.ofBits 7, K.ofBits 8, K.ofBits 9]]
  | _ => #[]

/-- The empty store. -/
def emptyData : ProverData K := fun _ _ ↦ #[]

#guard (imageOf sampleData).1 = 1
#guard (imageOf sampleData).2 0 = E.ofLimbs 1 (K.ofBits 2) (K.ofBits 3)
#guard (imageOf sampleData).2 1 = E.ofLimbs (K.ofBits 4) (K.ofBits 5) (K.ofBits 6)
#guard (imageOf namedData).1 = 0
#guard (imageOf namedData).2 0 = E.ofLimbs (K.ofBits 9) (K.ofBits 9) (K.ofBits 9)

-- The floor logarithm truncates: three rows give a one-bit image without the third word.
#guard (imageOf threeRows).1 = 1
#guard (imageOf threeRows).2 1 = E.ofLimbs (K.ofBits 4) (K.ofBits 5) (K.ofBits 6)
-- The empty store: one word `0`.
#guard (imageOf emptyData).1 = 0
#guard (imageOf emptyData).2 0 = 0

/-- The log-size of two rows is `1`, through `imageOf_fst`, under the cap. -/
theorem sampleData_logSize : (imageOf sampleData).1 = 1 :=
  imageOf_fst (by decide) (by decide +kernel)

/-- The floor logarithm of three rows is `1`, under the cap: the third row is dropped. -/
theorem threeRows_logSize : (imageOf threeRows).1 = 1 := by
  show min (Nat.log 2 (memRows threeRows).size) maxLogMem = 1
  rw [Nat.log_eq_of_pow_le_of_lt_pow (b := 2) (m := 1) (n := (memRows threeRows).size)
    (by decide +kernel) (by decide +kernel)]
  decide

/-- Three rows are more than the image holds. -/
example : 2 ^ (imageOf threeRows).1 < (memRows threeRows).size := by
  rw [threeRows_logSize]
  decide +kernel

/-- The empty store's image still has one word. -/
example : (imageOf emptyData).1 = 0 ∧ (memRows emptyData).size = 0 := by
  refine ⟨?_, by decide +kernel⟩
  show min (Nat.log 2 (memRows emptyData).size) maxLogMem = 0
  rw [show (memRows emptyData).size = 0 by decide +kernel, Nat.log_zero_right]
  decide

/-- Index `1` of the sample image. -/
def one : Fin (2 ^ (imageOf sampleData).1) := ⟨1, by rw [sampleData_logSize]; decide⟩

/-- A correct read satisfies the memory guarantee: word `1` sits at `g^1`. -/
example : MemChannel.Guarantees ⟨gpow 1, gpow 0, #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]⟩ sampleData := by
  show (imageOf sampleData).2.read (gpow 1) = some (E.ofLimbs (K.ofBits 4) (K.ofBits 5) (K.ofBits 6))
  rw [show gpow 1 = gpow (one : ℕ) from rfl,
    MemImage.read_gpow (by rw [sampleData_logSize]; decide),
    imageOf_apply one (v := #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]) (by decide +kernel)]
  rfl

/-- A wrong word does not: the guarantee is a statement about the committed image. -/
example : ¬ MemChannel.Guarantees ⟨gpow 1, gpow 0, #v[K.ofBits 4, K.ofBits 5, K.ofBits 7]⟩ sampleData := by
  show ¬ (imageOf sampleData).2.read (gpow 1) = some (E.ofLimbs (K.ofBits 4) (K.ofBits 5) (K.ofBits 7))
  rw [show gpow 1 = gpow (one : ℕ) from rfl,
    MemImage.read_gpow (by rw [sampleData_logSize]; decide),
    imageOf_apply one (v := #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]) (by decide +kernel)]
  decide +kernel

/-- The bytecode guarantee is decodability alone: an instruction's entry passes, at any counter
and with any count, over every data (the guarantee reads no data, decision 14). -/
example (pc c : K) (data : ProverData K) :
    BytecodeChannel.Guarantees ⟨pc, c, Opcode.jump.code, #v[1, 1, 1, 0, 0, 0, 0]⟩ data :=
  ⟨_, decode_entry (.jump 1 1 1)⟩

/-- An entry that decodes to nothing is no bytecode read at any counter: the flag pair `(1, 1)`
is no store mode (acceptance test 18). -/
example (pc c : K) (data : ProverData K) :
    ¬ BytecodeChannel.Guarantees ⟨pc, c, Opcode.deref.code, #v[1, 1, 1, 1, 1, 0, 0]⟩ data := by
  rintro ⟨ins, hdec⟩
  have h : decode (#v[Opcode.deref.code] ++ #v[(1: K), 1, 1, 1, 1, 0, 0]) = none := by
    decide +kernel
  exact nomatch h.symm.trans hdec

/-- Nor is a nonzero spare slot (acceptance test 16). -/
example (pc c : K) (data : ProverData K) :
    ¬ BytecodeChannel.Guarantees ⟨pc, c, Opcode.xor.code, #v[1, 1, 1, 0, 0, 0, 1]⟩ data := by
  rintro ⟨ins, hdec⟩
  have h : decode (#v[Opcode.xor.code] ++ #v[(1: K), 1, 1, 0, 0, 0, 1]) = none := by
    decide +kernel
  exact nomatch h.symm.trans hdec

/-- The guarantee names no program and reads no data: it is the same proposition on any two
data, where the memory guarantee reads its image off the data. -/
example (b : BytecodeMsg K) (data data' : ProverData K) :
    BytecodeChannel.Guarantees b data ↔ BytecodeChannel.Guarantees b data' :=
  Iff.rfl

/-- The state pull guarantees nothing (acceptance test 21). -/
example (s : Regs K) (data : ProverData K) : StateChannel.Guarantees s data := trivial

/-! ## Clean's direction-tagged bus over `K` (acceptance tests 13 and 14) -/

/-- `-1 = 1` in `K`: a multiplicity carries no direction … -/
example : (-1 : K) = 1 := by decide

/-- … the direction is the interaction's tag: a pull and a push of one message, both of
multiplicity `1`, are different interactions. -/
example (m : MemMsg K) : MemChannel.pulledValue m ≠ MemChannel.pushedValue m := fun h ↦
  nomatch congrArg Interaction.direction h

/-- A pull of multiplicity `1` is granted the channel's guarantee. -/
example (v : Vector K 5) (data : ProverData K) :
    MemChannel.toRaw.Guarantees 1 v data ↔ MemChannel.Guarantees (fromElements v) data :=
  ⟨fun f ↦ f rfl, fun h _ ↦ h⟩

/-- A push is granted nothing: only pulls get guarantees. -/
example (m : MemMsg K) (data : ProverData K) : (MemChannel.pushedValue m).Guarantees data :=
  fun h ↦ nomatch h

/-- An active push owes the channel's guarantee … -/
example (v : Vector K 5) (data : ProverData K) :
    MemChannel.toRaw.Requirements .push 1 v data ↔ MemChannel.Guarantees (fromElements v) data :=
  ⟨fun f ↦ f (by decide), fun h _ ↦ h⟩

/-- … an inactive push owes nothing, and a pull owes only a multiplicity `0` or `1`. -/
example (v : Vector K 5) (data : ProverData K) :
    MemChannel.toRaw.Requirements .push 0 v data ∧ MemChannel.toRaw.Requirements .pull 1 v data :=
  ⟨fun h ↦ absurd rfl h, Or.inr rfl⟩

/-- The characteristic of `K` is `2`. -/
example : ringChar K = 2 := ringChar.eq K 2

/-- `Balance.logUp` admits at most one interaction over `K`: its bound is the characteristic. -/
example (i j : Interaction K) (rest : List (Interaction K)) :
    ¬ Balance.logUp.Balanced (i :: j :: rest) := by
  rintro ⟨h, -⟩
  rw [ringChar.eq K 2] at h
  simp at h

/-- A message pushed twice and never pulled. -/
def twicePushed : List (Interaction K) := [MemChannel.pushedValue mm, MemChannel.pushedValue mm]

/-- Its signed multiplicities sum to `1 + 1 = 0` over `K`: the field sum alone would accept it. -/
example (msg : Array K) : balanceOf twicePushed msg = 0 := by
  rw [twicePushed, balanceOf_cons, balanceOf_cons,
    show balanceOf ([] : List (Interaction K)) msg = 0 from rfl]
  by_cases h : (MemChannel.pushedValue mm).msg = msg
  · simp only [h, ↓reduceIte]
    decide +kernel
  · simp only [h, ↓reduceIte, add_zero]

/-- `Balance.multiset` rejects it: its pushes are no permutation of its pulls. -/
example : ¬ Balance.multiset.Balanced twicePushed := by
  rintro ⟨-, -, h⟩
  have hl := h.length_eq
  simp [twicePushed, activeMessages, Channel.pushedValue] at hl

end LeanerVMTests.Arithmetization
