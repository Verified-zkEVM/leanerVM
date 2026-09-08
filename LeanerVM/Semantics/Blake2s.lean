/-
  LeanerVM.Semantics.Blake2s

  The BLAKE2s compression function with both finalization flags, the packing of 128-bit memory
  cells into 32-bit words, the metadata cell, and the nine-cell relation of the `BLAKE2S` opcode.
-/

module

public import LeanerVM.Parameters.Blake2s
public import LeanerVM.Parameters.Field

/-!
# BLAKE2s compression and the cell encoding

Category B, in two parts.

**The compression function** is RFC 7693 §3.1 (the mixing function `G`) and §3.2 (the
compression function `F`) with `w = 32`, ten rounds, and rotations `(16, 12, 8, 7)` (§2.1),
extended by the tree-mode *last node* flag of the BLAKE2 specification (Aumasson, Neves,
Wilcox-O'Hearn, Winnerlein, *BLAKE2: simpler, smaller, fast as MD5*, §2.3–§2.4): the reference
implementation `blake2s-ref.c` initialises `v[14] = f[0] ^ IV[6]` and `v[15] = f[1] ^ IV[7]`,
where `f[0]` (last block) and `f[1]` (last node) are 32-bit words equal to `0xFFFFFFFF` when set.
The pinned leanVM computes exactly this function, taking both flags as words:
`crates/flock/src/hash.rs:191-231` (`g_fn`, `initial_state`, `blake2s_compress`) at
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. The RFC's Boolean `f` is the word `0xFFFFFFFF`.

**The cell encoding** is transcribed from `crates/lean_vm/src/hash_flock.rs:117-139` and
`:162-185` (`words_of`, `pack_words`, `metadata`, `unpack_metadata`, `compression`, `digest`)
and `crates/lean_vm/src/cpu/execute.rs:779-812` at the pin, and agrees with specification §2
(`doc/leanvm/body/02-vm-specification.tex:90-93`) and §7 (`07-instruction-tables.tex:114-123`):

* a canonical cell `a0 + a1·y` is the little-endian 128-bit value `a0 ‖ a1`, read as four 32-bit
  words, low word of `a0` first (`cellWords`);
* the sixteen message words are the four message cells in operand order, the eight
  chaining-value words are the two chaining-value cells, first cell first, and the eight output
  words fill the two output cells the same way;
* the metadata cell is `counter ‖ final ‖ last_node`: the 64-bit counter is limb 0, the two
  flag words are the low and high halves of limb 1 (`unpackMetadata`);
* all nine cells are canonical. The Rust executor checks the seven cells it reads and constructs
  the two outputs canonical; the constraints force all nine (§7: the eighteen low limbs are the
  values committed to Flock), and `CompressCells` follows the constraints.

## Deviation from the roadmap

`docs/roadmap/leanisa-blueprint.md` (Layer 1) types the two flags as `Bool`. The pinned Rust and
the Flock relation take them as the two 32-bit halves of limb 1 of the metadata cell, XORed into
`v[14]` and `v[15]` whatever their value, and a metadata cell with a flag word other than `0` or
`0xFFFFFFFF` satisfies the constraints. `compress` and `unpackMetadata` therefore carry `UInt32`
flags, so that `CompressCells` says what the constraints check on every metadata cell; the
Boolean form is `compress h m t (if f0 then 0xFFFFFFFF else 0) (if f1 then 0xFFFFFFFF else 0)`.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## Compression -/

namespace Blake2s

/-- Rotate a 32-bit word right by `n` bits (RFC 7693 §2.3, `>>>`). -/
def rotr (x : UInt32) (n : ℕ) : UInt32 := ⟨x.toBitVec.rotateRight n⟩

/-- The mixing function `G` (RFC 7693 §3.1) with the BLAKE2s rotations `(16, 12, 8, 7)` (§2.1). -/
def mix (v : Vector UInt32 16) (a b c d : Fin 16) (x y : UInt32) : Vector UInt32 16 :=
  let va := v[a] + v[b] + x
  let vd := rotr (v[d] ^^^ va) 16
  let vc := v[c] + vd
  let vb := rotr (v[b] ^^^ vc) 12
  let va := va + vb + y
  let vd := rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 7
  (((v.set a va).set b vb).set c vc).set d vd

/-- One round of `F` (RFC 7693 §3.2): the four column and the four diagonal `G` calls, with the
message words selected by the schedule row `s`. -/
def round (v m : Vector UInt32 16) (s : Vector (Fin 16) 16) : Vector UInt32 16 :=
  let v := mix v 0 4 8 12 m[s[0]] m[s[1]]
  let v := mix v 1 5 9 13 m[s[2]] m[s[3]]
  let v := mix v 2 6 10 14 m[s[4]] m[s[5]]
  let v := mix v 3 7 11 15 m[s[6]] m[s[7]]
  let v := mix v 0 5 10 15 m[s[8]] m[s[9]]
  let v := mix v 1 6 11 12 m[s[10]] m[s[11]]
  let v := mix v 2 7 8 13 m[s[12]] m[s[13]]
  mix v 3 4 9 14 m[s[14]] m[s[15]]

/-- The initial working vector of `F`: `h`, then `iv` with the two counter words and the two
flag words XORed into its last four words (RFC 7693 §3.2; `blake2s-ref.c` for `v[15]`). -/
def initialState (h : Vector UInt32 8) (t : UInt64) (f0 f1 : UInt32) : Vector UInt32 16 :=
  let v : Vector UInt32 16 := h ++ iv
  let v := v.set 12 (v[12] ^^^ t.toUInt32)
  let v := v.set 13 (v[13] ^^^ (t >>> 32).toUInt32)
  let v := v.set 14 (v[14] ^^^ f0)
  v.set 15 (v[15] ^^^ f1)

end Blake2s

/-- The BLAKE2s compression function `F` (RFC 7693 §3.2) with the tree-mode last-node flag:
`t` is the 64-bit offset counter, `f0` the last-block flag and `f1` the last-node flag, each
`0xFFFFFFFF` when set. Ten rounds under `sigma`, then `h[i] ^ v[i] ^ v[i + 8]`. -/
def compress (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    Vector UInt32 8 :=
  let v := sigma.foldl (fun v s ↦ Blake2s.round v m s) (Blake2s.initialState h t f0 f1)
  #v[h[0] ^^^ v[0] ^^^ v[8], h[1] ^^^ v[1] ^^^ v[9], h[2] ^^^ v[2] ^^^ v[10],
     h[3] ^^^ v[3] ^^^ v[11], h[4] ^^^ v[4] ^^^ v[12], h[5] ^^^ v[5] ^^^ v[13],
     h[6] ^^^ v[6] ^^^ v[14], h[7] ^^^ v[7] ^^^ v[15]]

/-! ## Cells -/

/-- The low 32 bits of a `K` element. -/
def lowWord (a : K) : UInt32 := ⟨a.extractLsb' 0 32⟩

/-- The high 32 bits of a `K` element. -/
def highWord (a : K) : UInt32 := ⟨a.extractLsb' 32 32⟩

/-- The `K` element with the given low and high words. -/
def ofWords (lo hi : UInt32) : K := hi.toBitVec ++ lo.toBitVec

/-- The four little-endian words of a canonical cell `a0 + a1·y`: the low and high words of `a0`,
then those of `a1` (`hash_flock.rs:117-121`, `words_of`; the top limb is ignored). -/
def cellWords (x : E) : Vector UInt32 4 :=
  #v[lowWord (x.limb 0), highWord (x.limb 0), lowWord (x.limb 1), highWord (x.limb 1)]

/-- The canonical cell holding four little-endian words (`hash_flock.rs:123-126`,
`pack_words`). -/
def wordsCell (w : Vector UInt32 4) : E :=
  E.ofLimbs (ofWords w[0] w[1]) (ofWords w[2] w[3]) 0

/-- The metadata cell `counter ‖ final ‖ last_node` (`hash_flock.rs:128-139`; specification §2):
the counter is limb 0, the last-block and last-node flag words are the low and high halves of
limb 1. -/
def unpackMetadata (md : E) : UInt64 × UInt32 × UInt32 :=
  (⟨md.limb 0⟩, lowWord (md.limb 1), highWord (md.limb 1))

/-- The sixteen message words of the four message cells, in operand order
(`hash_flock.rs:162-172`). -/
def messageWords (m : Fin 4 → E) : Vector UInt32 16 :=
  cellWords (m 0) ++ cellWords (m 1) ++ cellWords (m 2) ++ cellWords (m 3)

/-- The `BLAKE2S` relation on its nine cells (specification §2 and
`07-instruction-tables.tex:114-123`): every cell is canonical, and
the two output cells hold the compression of the four message cells under the two chaining-value
cells and the metadata cell. -/
def CompressCells (m : Fin 4 → E) (cv0 cv1 out0 out1 md : E) : Prop :=
  (∀ i, IsCanonical128 (m i)) ∧ IsCanonical128 cv0 ∧ IsCanonical128 cv1 ∧
    IsCanonical128 out0 ∧ IsCanonical128 out1 ∧ IsCanonical128 md ∧
    cellWords out0 ++ cellWords out1 =
      compress (cellWords cv0 ++ cellWords cv1) (messageWords m) (unpackMetadata md).1
        (unpackMetadata md).2.1 (unpackMetadata md).2.2

/-- `CompressCells` is decided by comparing the output *lists* of words: core's `DecidableEq` for
`Vector` is not exposed to module-system importers, so neither `decide` nor the kernel can reduce
it there, while `List` equality reduces. -/
instance {m : Fin 4 → E} {cv0 cv1 out0 out1 md : E} :
    Decidable (CompressCells m cv0 cv1 out0 out1 md) :=
  decidable_of_iff
    ((∀ i, IsCanonical128 (m i)) ∧ IsCanonical128 cv0 ∧ IsCanonical128 cv1 ∧
      IsCanonical128 out0 ∧ IsCanonical128 out1 ∧ IsCanonical128 md ∧
      (cellWords out0 ++ cellWords out1).toList =
        (compress (cellWords cv0 ++ cellWords cv1) (messageWords m) (unpackMetadata md).1
          (unpackMetadata md).2.1 (unpackMetadata md).2.2).toList)
    (by simp only [CompressCells, Vector.toList_inj])

/-! ## Proof helpers -/

/-- Splitting a `K` element into its two words and joining them again is the identity. -/
private theorem ofWords_lowWord_highWord (a : K) : ofWords (lowWord a) (highWord a) = a := by
  have := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := a) (start₁ := 0) (len₁ := 32)
    (start₂ := 32) (len₂ := 32) rfl
  simpa [ofWords, lowWord, highWord] using this

/-! ## Load-bearing lemmas -/

/-- Packing the words of a canonical cell gives the cell back. -/
theorem wordsCell_cellWords {x : E} (h : IsCanonical128 x) : wordsCell (cellWords x) = x := by
  have h2 : x.limb 2 = 0 := h
  apply E.ext; intro i
  rw [wordsCell, limb_ofLimbs]
  fin_cases i <;> simp [cellWords, ofWords_lowWord_highWord, h2]

end
end LeanerVM.Semantics
