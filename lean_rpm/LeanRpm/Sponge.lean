import LeanRpm.Model

/-!
# The sponge construction and Keccak-256

The sponge construction of Bertoni, Daemen, Peeters and Van Assche ("On the indifferentiability
of the sponge construction", EUROCRYPT 2008) over a permutation `π` of a state split into an
outer part, the *rate*, and an inner part, the *capacity*. A message is padded into rate-sized
blocks; each block is XORed into the rate and the state is permuted; the output is a prefix of
the rate of the final state.

The abstract sponge here (`absorbAll`, `spongeWith`) works over states `(Dg × E) × C`: the rate
is `Dg × E`, of which the output is the first component `Dg`, and the capacity is `C`. The
padding is any injective map from messages to nonempty block lists with a decoder
(`Padding`). The monad `m` is arbitrary: `π` may be a pure function (`Id`), a query to a random
permutation oracle (`OracleComp`), or any other effect.

The concrete instance is Keccak-256, as leanVM computes it (`crates/verifier/src/hash.rs`,
`keccak_hash`; `python-verifier/verifier.py`): the state is 200 bytes, the 25 little-endian
64-bit lanes of Keccak-f[1600]; the rate is its first 136 bytes, the capacity its last 64 bytes
(512 bits); the digest is its first 32 bytes; the padding is `0x01 ‖ 0^* ‖ 0x80` (Keccak's
domain byte `0x01`, not SHA-3's `0x06`), merged into `0x81` when one byte is left in the last
block. `keccak256With π` is this sponge over any permutation `π` of the 200-byte state, and
`keccak256` is it over Keccak-f[1600] (`keccakF`, transcribed from `keccak_f`); the `#guard`s
below check it against the test vectors of `hash.rs`.

The padding is injective with a computable decoder (`keccakPadding`): the decoder strips the
padding and accepts exactly the padded messages.
-/

namespace LeanRpm

/-! ## Exclusive-or with cancellation -/

/-- A type with an exclusive-or such that `a ^^^ (a ^^^ b) = b`: absorbing a block into a state
is invertible, and the block is recovered from the states before and after. -/
class XorCancel (α : Type) extends XorOp α where
  /-- XOR with `a` is an involution. -/
  xor_cancel : ∀ a b : α, a ^^^ (a ^^^ b) = b

/-- Byte vectors XOR bytewise. -/
instance (n : ℕ) : XorCancel (Vector UInt8 n) where
  xor a b := Vector.zipWith (· ^^^ ·) a b
  xor_cancel a b := by
    apply Vector.ext
    intro i hi
    change (Vector.zipWith (· ^^^ ·) a (Vector.zipWith (· ^^^ ·) a b))[i] = b[i]
    simp only [Vector.getElem_zipWith]
    rw [← UInt8.xor_assoc, UInt8.xor_self, UInt8.zero_xor]

/-! ## The abstract sponge -/

variable {Dg E C : Type}

/-- The state of a sponge with digest part `Dg`, rest of the rate `E` and capacity `C`. -/
abbrev SpState (Dg E C : Type) := (Dg × E) × C

/-- The rate part of a state. -/
abbrev SpState.rate (s : SpState Dg E C) : Dg × E := s.1

/-- The capacity part of a state. -/
abbrev SpState.cap (s : SpState Dg E C) : C := s.2

/-- The digest part of a state: the first component of the rate. -/
abbrev SpState.out (s : SpState Dg E C) : Dg := s.1.1

section Xor

variable [XorCancel Dg] [XorCancel E]

/-- XOR on the rate, componentwise. -/
def rxor (a b : Dg × E) : Dg × E := (a.1 ^^^ b.1, a.2 ^^^ b.2)

/-- XOR on the rate is an involution in its second argument. -/
theorem rxor_cancel (a b : Dg × E) : rxor a (rxor a b) = b := by
  simp [rxor, XorCancel.xor_cancel]

/-- XOR on the rate is injective in its second argument. -/
theorem rxor_injective (a : Dg × E) : Function.Injective (rxor a) := fun b b' h ↦ by
  rw [← rxor_cancel a b, h, rxor_cancel]

/-- Absorbing a block: XOR it into the rate, keep the capacity. -/
def absorb (s : SpState Dg E C) (B : Dg × E) : SpState Dg E C := (rxor s.1 B, s.2)

/-- The block that takes the state `s` to the state `x` with the same capacity. -/
def blockTo (s x : SpState Dg E C) : Dg × E := rxor s.1 x.1

/-- Absorbing `blockTo s x` into `s` gives `x` when `s` and `x` share their capacity. -/
theorem absorb_blockTo {s x : SpState Dg E C} (h : s.2 = x.2) : absorb s (blockTo s x) = x := by
  obtain ⟨⟨a, b⟩, c⟩ := s
  obtain ⟨⟨a', b'⟩, c'⟩ := x
  simp only at h
  subst h
  simp only [absorb, blockTo]
  rw [rxor_cancel]

/-- The block absorbed into `s` is recovered from the result. -/
theorem blockTo_absorb (s : SpState Dg E C) (B : Dg × E) : blockTo s (absorb s B) = B :=
  rxor_cancel s.1 B

/-- Absorbing keeps the capacity. -/
@[simp] theorem absorb_cap (s : SpState Dg E C) (B : Dg × E) : (absorb s B).2 = s.2 := rfl

/-- Absorbing is injective in the block. -/
theorem absorb_injective (s : SpState Dg E C) : Function.Injective (absorb s) := by
  intro B B' h
  rw [← blockTo_absorb s B, h, blockTo_absorb]

/-- Absorb the blocks `bs` from the state `s`: XOR each into the rate and permute with `π`. -/
def absorbAll {m : Type → Type} [Monad m] (π : SpState Dg E C → m (SpState Dg E C)) :
    SpState Dg E C → List (Dg × E) → m (SpState Dg E C)
  | s, [] => pure s
  | s, B :: bs => do
    let y ← π (absorb s B)
    absorbAll π y bs

@[simp] theorem absorbAll_nil {m : Type → Type} [Monad m] (π : SpState Dg E C → m (SpState Dg E C))
    (s : SpState Dg E C) : absorbAll π s [] = pure s := rfl

theorem absorbAll_cons {m : Type → Type} [Monad m] (π : SpState Dg E C → m (SpState Dg E C))
    (s : SpState Dg E C) (B : Dg × E) (bs : List (Dg × E)) :
    absorbAll π s (B :: bs) = (π (absorb s B) >>= fun y ↦ absorbAll π y bs) := rfl

/-- Absorbing a concatenation absorbs the first part, then the second. -/
theorem absorbAll_append {m : Type → Type} [Monad m] [LawfulMonad m]
    (π : SpState Dg E C → m (SpState Dg E C)) (s : SpState Dg E C) (bs bs' : List (Dg × E)) :
    absorbAll π s (bs ++ bs') = (absorbAll π s bs >>= fun y ↦ absorbAll π y bs') := by
  induction bs generalizing s with
  | nil => simp
  | cons B bs ih => simp [absorbAll_cons, ih]

end Xor

/-- A sponge padding: an injective map from messages to nonempty lists of blocks, with a decoder
that recognises exactly the padded messages. -/
structure Padding (Msg Blk : Type) where
  /-- The padded message, as a list of blocks. -/
  pad : Msg → List Blk
  /-- The decoder: the message whose padding is the given block list, if any. -/
  unpad : List Blk → Option Msg
  /-- The decoder recognises exactly the paddings. -/
  unpad_eq_some_iff : ∀ β m, unpad β = some m ↔ pad m = β
  /-- A padded message has at least one block. -/
  pad_ne_nil : ∀ m, pad m ≠ []

namespace Padding

variable {Msg Blk : Type}

/-- Padding is injective. -/
theorem pad_injective (P : Padding Msg Blk) : Function.Injective P.pad := fun m m' h ↦ by
  have h1 := (P.unpad_eq_some_iff (P.pad m') m).mpr h
  have h2 := (P.unpad_eq_some_iff (P.pad m') m').mpr rfl
  rw [h1] at h2
  exact Option.some.inj h2

/-- The decoder inverts the padding. -/
@[simp] theorem unpad_pad (P : Padding Msg Blk) (m : Msg) : P.unpad (P.pad m) = some m :=
  (P.unpad_eq_some_iff _ m).mpr rfl

end Padding

variable [XorCancel Dg] [XorCancel E]

/-- **The sponge.** Absorb the padded message from the initial state `iv` with `π`, and output the
digest part of the final state. -/
def spongeWith {Msg : Type} {m : Type → Type} [Monad m] (P : Padding Msg (Dg × E))
    (iv : SpState Dg E C) (π : SpState Dg E C → m (SpState Dg E C)) (msg : Msg) : m Dg :=
  SpState.out <$> absorbAll π iv (P.pad msg)

/-! ## Keccak-256 -/

/-- A 32-byte Keccak-256 digest. -/
abbrev KDigest := Vector UInt8 32

/-- The rate bytes of the Keccak state after the digest: bytes 32 to 135. -/
abbrev KRest := Vector UInt8 104

/-- The capacity of the Keccak state: bytes 136 to 199 (512 bits). -/
abbrev KCap := Vector UInt8 64

/-- The Keccak-f[1600] state as 200 bytes, split into digest, rest of the rate and capacity.
Byte `i` of the state is byte `i % 8` of lane `i / 8`, little-endian, as in `keccak_hash`. -/
abbrev KState := SpState KDigest KRest KCap

/-- A Keccak-256 block: the 136 rate bytes. -/
abbrev KBlock := KDigest × KRest

/-- The rate of Keccak-256 in bytes. -/
def keccakRate : ℕ := 136

/-- The 200 bytes of a Keccak state, in order. -/
def KState.toBytes (s : KState) : List UInt8 := s.1.1.toList ++ s.1.2.toList ++ s.2.toList

/-- The Keccak state of 200 bytes (missing bytes read as zero). -/
def KState.ofBytes (bs : List UInt8) : KState :=
  ((Vector.ofFn fun i : Fin 32 ↦ bs.getD i 0, Vector.ofFn fun i : Fin 104 ↦ bs.getD (32 + i) 0),
    Vector.ofFn fun i : Fin 64 ↦ bs.getD (136 + i) 0)

/-- The all-zero initial state. -/
def KState.zero : KState := ((Vector.replicate 32 0, Vector.replicate 104 0), Vector.replicate 64 0)

/-- The block of the 136 bytes `bs` (missing bytes read as zero). -/
def KBlock.ofBytes (bs : List UInt8) : KBlock :=
  (Vector.ofFn fun i : Fin 32 ↦ bs.getD i 0, Vector.ofFn fun i : Fin 104 ↦ bs.getD (32 + i) 0)

/-- The 136 bytes of a block. -/
def KBlock.toBytes (B : KBlock) : List UInt8 := B.1.toList ++ B.2.toList

/-- The padded message: `msg ‖ 0x01 ‖ 0^* ‖ 0x80`, with `0x01` and `0x80` merged into `0x81` when
`msg` leaves one byte in its last block; the length is the next multiple of 136. -/
def keccakPadBytes (msg : List UInt8) : List UInt8 :=
  if msg.length % 136 = 135 then msg ++ [0x81]
  else msg ++ [0x01] ++ List.replicate (134 - msg.length % 136) 0 ++ [0x80]

/-- Split a byte list into 136-byte blocks. -/
def toBlocks : List UInt8 → List KBlock
  | [] => []
  | b :: bs => KBlock.ofBytes ((b :: bs).take 136) :: toBlocks ((b :: bs).drop 136)
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- The bytes of a block list. -/
def blocksToBytes (β : List KBlock) : List UInt8 := β.flatMap KBlock.toBytes

/-- Undo the padding of a padded byte list (arbitrary on other inputs). -/
def stripPad (bs : List UInt8) : List UInt8 :=
  match bs.reverse with
  | 0x81 :: rest => rest.reverse
  | _ :: rest => (((rest.dropWhile (· = 0)).drop 1)).reverse
  | [] => []

/-- The Keccak-256 padding of a message into blocks. -/
def keccakPad (msg : List UInt8) : List KBlock := toBlocks (keccakPadBytes msg)

/-- The Keccak-256 decoder: strip the padding, and accept when it pads back. -/
def keccakUnpad (β : List KBlock) : Option (List UInt8) :=
  let msg := stripPad (blocksToBytes β)
  if keccakPad msg = β then some msg else none

/-- The bytes of a block made of 136 bytes are those bytes. -/
theorem KBlock.toBytes_ofBytes {bs : List UInt8} (h : bs.length = 136) :
    (KBlock.ofBytes bs).toBytes = bs := by
  apply List.ext_getElem
  · simp [KBlock.toBytes, KBlock.ofBytes, h]
  intro i h1 h2
  simp only [KBlock.toBytes, KBlock.ofBytes] at h1 ⊢
  rw [List.getElem_append]
  split_ifs with hi
  · simp only [Vector.toList_ofFn, List.getElem_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  · simp only [Vector.toList_ofFn, List.getElem_ofFn, List.length_ofFn]
    simp only [Vector.toList_ofFn, List.length_ofFn] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1
    omega

/-- Splitting a list whose length is a multiple of 136 into blocks and back gives the list. -/
theorem blocksToBytes_toBlocks (bs : List UInt8) (h : bs.length % 136 = 0) :
    blocksToBytes (toBlocks bs) = bs := by
  induction bs using toBlocks.induct with
  | case1 => simp [toBlocks, blocksToBytes]
  | case2 b bs ih =>
    rw [toBlocks]
    simp only [blocksToBytes, List.flatMap_cons] at ih ⊢
    have hlen : 136 ≤ (b :: bs).length := by
      have : 0 < (b :: bs).length := by simp
      omega
    rw [KBlock.toBytes_ofBytes (by simp only [List.length_take]; omega),
      ih (by simp only [List.length_drop]; omega), List.take_append_drop]

/-- The padded bytes have a length that is a positive multiple of 136. -/
theorem keccakPadBytes_length (msg : List UInt8) :
    (keccakPadBytes msg).length = 136 * (msg.length / 136 + 1) := by
  unfold keccakPadBytes
  split_ifs with h
  · simp; omega
  · simp; omega

/-- Stripping the padding recovers the message. -/
theorem stripPad_keccakPadBytes (msg : List UInt8) : stripPad (keccakPadBytes msg) = msg := by
  unfold keccakPadBytes
  split_ifs with h
  · simp [stripPad]
  · have hz : ∀ k, List.dropWhile (· = (0 : UInt8)) (List.replicate k 0 ++ (1 :: msg.reverse)) =
        1 :: msg.reverse := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => simp [List.replicate_succ, ih]
    simp only [stripPad, List.append_assoc, List.cons_append, List.nil_append,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_replicate]
    simp [hz]

/-- Padded block lists are never empty. -/
theorem keccakPad_ne_nil (msg : List UInt8) : keccakPad msg ≠ [] := by
  unfold keccakPad
  have hlen := keccakPadBytes_length msg
  cases h : keccakPadBytes msg with
  | nil => rw [h] at hlen; simp at hlen
  | cons b bs => rw [toBlocks]; exact List.cons_ne_nil _ _

/-- The decoder inverts the padding. -/
theorem keccakUnpad_keccakPad (msg : List UInt8) : keccakUnpad (keccakPad msg) = some msg := by
  have hb : blocksToBytes (keccakPad msg) = keccakPadBytes msg :=
    blocksToBytes_toBlocks _ (by rw [keccakPadBytes_length]; omega)
  simp [keccakUnpad, hb, stripPad_keccakPadBytes]

/-- **The Keccak-256 padding**, with its decoder. -/
def keccakPadding : Padding (List UInt8) KBlock where
  pad := keccakPad
  unpad := keccakUnpad
  unpad_eq_some_iff β m := by
    constructor
    · intro h
      simp only [keccakUnpad] at h
      split_ifs at h with hp
      · cases h; exact hp
    · rintro rfl
      exact keccakUnpad_keccakPad m
  pad_ne_nil := keccakPad_ne_nil

/-- **Keccak-256 over a permutation `π` of the state**, in any monad: the sponge with rate 136
bytes, capacity 64 bytes, the Keccak padding, the all-zero initial state, and the first 32 bytes of
the final state as the digest. -/
def keccak256With {m : Type → Type} [Monad m] (π : KState → m KState) (msg : List UInt8) :
    m KDigest :=
  spongeWith keccakPadding KState.zero π msg

/-! ## Keccak-f[1600] -/

/-- The round constants of Keccak-f[1600] (`KECCAK_RC`). -/
def keccakRC : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The rotation offsets of Keccak-f[1600] (`KECCAK_RHO`), by lane. -/
def keccakRho : Array UInt64 := #[
  0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- Where lane `i = x + 5y` lands under π (`KECCAK_PI`). -/
def keccakPi (i : ℕ) : ℕ := i / 5 + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5)

/-- Rotate a lane left. -/
def rotl64 (x n : UInt64) : UInt64 := if n = 0 then x else (x <<< n) ||| (x >>> (64 - n))

/-- One round of Keccak-f[1600] on the 25 lanes, transcribed from `keccak_f`. -/
def keccakRound (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  let c : Array UInt64 := Array.ofFn fun x : Fin 5 ↦
    a[x.1]! ^^^ a[x.1 + 5]! ^^^ a[x.1 + 10]! ^^^ a[x.1 + 15]! ^^^ a[x.1 + 20]!
  let d : Array UInt64 := Array.ofFn fun x : Fin 5 ↦
    c[(x.1 + 4) % 5]! ^^^ rotl64 c[(x.1 + 1) % 5]! 1
  let a : Array UInt64 := Array.ofFn fun i : Fin 25 ↦ a[i.1]! ^^^ d[i.1 % 5]!
  let mut b : Array UInt64 := Array.replicate 25 0
  for i in [0:25] do
    b := b.set! (keccakPi i) (rotl64 a[i]! keccakRho[i]!)
  let a : Array UInt64 := Array.ofFn fun i : Fin 25 ↦
    let r := i.1 - i.1 % 5
    b[i.1]! ^^^ ((~~~ b[r + (i.1 % 5 + 1) % 5]!) &&& b[r + (i.1 % 5 + 2) % 5]!)
  return a.set! 0 (a[0]! ^^^ rc)

/-- Keccak-f[1600] on the 25 lanes: 24 rounds. -/
def keccakFLanes (a : Array UInt64) : Array UInt64 := keccakRC.foldl keccakRound a

/-- The 25 little-endian lanes of 200 bytes. -/
def lanesOfBytes (bs : List UInt8) : Array UInt64 :=
  Array.ofFn fun i : Fin 25 ↦ (List.range 8).foldr
    (fun j acc ↦ acc ||| ((bs.getD (8 * i.1 + j) 0).toUInt64 <<< (8 * j).toUInt64)) 0

/-- The 200 bytes of 25 little-endian lanes. -/
def bytesOfLanes (a : Array UInt64) : List UInt8 :=
  (List.range 200).map fun k ↦ (a[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8

/-- **Keccak-f[1600]** on the byte state. -/
def keccakF (s : KState) : KState :=
  KState.ofBytes (bytesOfLanes (keccakFLanes (lanesOfBytes s.toBytes)))

/-- **Keccak-256**: the sponge over Keccak-f[1600]. -/
def keccak256 (msg : List UInt8) : KDigest := keccak256With (m := Id) keccakF msg

/-- Hexadecimal rendering of bytes, for the test vectors. -/
def hexOfBytes (bs : List UInt8) : String :=
  String.join (bs.map fun b ↦
    let h := "0123456789abcdef".toList
    String.ofList [h.getD (b.toNat / 16) '0', h.getD (b.toNat % 16) '0'])

/-- The bytes `0, 1, …, n - 1` (mod 256) of the test vectors. -/
def countingBytes (n : ℕ) : List UInt8 := (List.range n).map fun i ↦ i.toUInt8

/-! The test vectors of `hash.rs` (from the `sha3` crate's `Keccak256`), on each side of a block
boundary. -/

#guard hexOfBytes (keccak256 (countingBytes 0)).toList ==
  "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
#guard hexOfBytes (keccak256 (countingBytes 1)).toList ==
  "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a"
#guard hexOfBytes (keccak256 (countingBytes 135)).toList ==
  "cbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62"
#guard hexOfBytes (keccak256 (countingBytes 136)).toList ==
  "7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e"
#guard hexOfBytes (keccak256 (countingBytes 137)).toList ==
  "ac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db"
#guard hexOfBytes (keccak256 (countingBytes 272)).toList ==
  "fdf2ec49e749960d3c8521a0219af8d03e30e2b3bf19bd16150ee0eaf133d66e"

end LeanRpm
