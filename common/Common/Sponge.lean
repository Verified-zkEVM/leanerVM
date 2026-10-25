import Common.Model
import Statement.RandomPermutation

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

namespace Common

/-! ## Exclusive-or with cancellation -/

/-! ## The abstract sponge -/

variable {Dg E C : Type}

/-- The rate part of a state. -/
abbrev SpState.rate (s : SpState Dg E C) : Dg × E := s.1

/-- The capacity part of a state. -/
abbrev SpState.cap (s : SpState Dg E C) : C := s.2

section Xor

variable [XorCancel Dg] [XorCancel E]

/-- XOR on the rate is an involution in its second argument. -/
theorem rxor_cancel (a b : Dg × E) : rxor a (rxor a b) = b := by
  simp [rxor, XorCancel.xor_cancel]

/-- XOR on the rate is injective in its second argument. -/
theorem rxor_injective (a : Dg × E) : Function.Injective (rxor a) := fun b b' h ↦ by
  rw [← rxor_cancel a b, h, rxor_cancel]

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

/-! ## Keccak-256 -/

/-- The rate of Keccak-256 in bytes. -/
def keccakRate : ℕ := 136

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

end Common
