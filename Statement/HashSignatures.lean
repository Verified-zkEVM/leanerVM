module

public import Statement.SufCma
public import Statement.Fast.Keccak

/-!
# Hash-based signatures: what leanXMSS and leanSPHINCS share

Read before the two schemes: the tweakable hash `Th(P, A, M) = Truncate_n(H(P ‖ A ‖ M))`, its
16-byte address and the types around it, which `crates/signatures/src/tweak.rs` gives both schemes
(namespace `HashSig`); the hash `H`, Keccak-256 over a permutation `π` of the Keccak state in any
monad (`keccakHash`), and the hash chains, Merkle paths and Merkle trees every chain, path and tree
of both schemes instantiates (`walkChain`, `foldPath`, `buildTree`, namespace
`HashSig.OverPermutation`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace HashSig

/-! ## The sizes and types both schemes share -/

/-- `n`: a digest's bits (`128`, `16` bytes). -/
def digestBits : Nat := 128
/-- `w`: the bits of a Winternitz digit (`2`). -/
def winternitzBits : Nat := 2
/-- A hash chain's positions, `2^w` (`4`): a digit's values. -/
def chainLength : Nat := 2 ^ winternitzBits
/-- The key's secret seed `S_0`, `256` bits. -/
abbrev MasterSeed := BitVec 256
/-- A digest: a tweakable hash's output, `n` bits (a chain value, a Merkle node, a root). -/
abbrev Digest := BitVec digestBits
/-- The hash `H`'s output, `256` bits, before truncation to a digest. -/
abbrev HashOutput := BitVec 256
/-- A message to sign, `256` bits. -/
abbrev Message := BitVec 256
/-- The public parameter `P`, `128` bits, prefixed to every hash call. -/
abbrev PublicParameter := BitVec 128
/-- A signature's randomizer, one digest. -/
abbrev Randomizer := Digest
/-- A Winternitz digit, a chain's position: `0` to `chainLength - 1`. -/
abbrev WinternitzDigit := Fin chainLength
/-- A step along a chain, from position `t` to `t + 1`: `0` to `chainLength - 2`. -/
abbrev ChainStep := Fin (chainLength - 1)
/-- A hash call's input bytes. -/
abbrev HashInput := List UInt8

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- The second 16 bytes of a hash output. Only the seed derivations of chain starts (and of
leanSPHINCS's FORS secrets) use them. -/
def upperHalfOfHash (output : HashOutput) : Digest :=
  output.extractLsb' digestBits digestBits

/-- The half of a hash output that starts chain `chainIndex`: the first for even `chainIndex`, the
second for odd `chainIndex`. -/
def hashHalfForChain (chainIndex : Nat) (output : HashOutput) : Digest :=
  if chainIndex % 2 = 0 then truncateHash output else upperHalfOfHash output

/-- `pk = (root, P)`. -/
structure PublicKey where
  /-- The Merkle root over the key's one-time public keys. -/
  root : Digest
  /-- The public parameter `P`. -/
  parameter : PublicParameter
deriving DecidableEq

/-- The secret key: the key's seed `S_0`, all of the key (`LeanXmssSecretKey`,
`lean_xmss/scheme.rs:98-106`, which also caches what key generation derived from it, and
`LeanSphincsSecretKey`, `lean_sphincs/scheme.rs:40-42`). Every secret derives from the scheme seed
`S = H(seedTag ‖ S_0)` (`seedTag` the scheme's name, `leanXMSS` or `leanSPHINCS`), which the signer
derives again at each signature, as the crates' do (`scheme_seed`). -/
abbrev SecretKey := MasterSeed

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def littleEndianBytes (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- `d_0 || ... || d_{n-1}`, 16 bytes each: a one-time key's chain ends, which its leaf hashes. -/
def digestsPayload {n : Nat} (digests : Fin n → Digest) : HashInput :=
  (List.ofFn digests).flatMap (littleEndianBytes 16)

/-- The first `n` base-`2^w` digits of a digest, little endian: digit `i` is bits `w i` to
`w i + w - 1`, how far a WOTS+C signature opens chain `i`. -/
def digestDigits {n : Nat} (digest : Digest) (i : Fin n) : WinternitzDigit :=
  (digest.extractLsb' (winternitzBits * i.val) winternitzBits).toFin

/-- The address of a hash call (`Tweak`, `crates/signatures/src/tweak.rs:32-40`): its type
`tag < 32`, a chain step `step < 8`, a hypertree layer (counted from the bottom) and tree, and two
fields `hi < 2^24` and `lo < 2^32`. leanXMSS's layer and tree are always zero. -/
structure TweakFields where
  /-- The hash call's type. -/
  tag : BitVec 5
  /-- The chain step, for a chain's hash. -/
  step : BitVec 3
  /-- The hypertree layer, from the bottom (leanSPHINCS's; zero for leanXMSS). -/
  layer : BitVec 8
  /-- The tree on that layer (leanSPHINCS's; zero for leanXMSS). -/
  tree : BitVec 32
  /-- The high field, `24` bits, which each hash type fills (each scheme's `hashDomainFields`). -/
  hi : BitVec 24
  /-- The low field, `32` bits, likewise (a leaf, key or node index). -/
  lo : BitVec 32
deriving DecidableEq

/-- The 16 address bytes `lo || hi || (tag + 32 * step) || layer || tree || 0^24` (`address`,
`tweak.rs:78-86`). -/
def addressBytes (fields : TweakFields) : HashInput :=
  littleEndianBytes 4 fields.lo ++ littleEndianBytes 3 fields.hi ++
    littleEndianBytes 1 (fields.step ++ fields.tag) ++ littleEndianBytes 1 fields.layer ++
    littleEndianBytes 4 fields.tree ++ littleEndianBytes 3 0

/-- Convert the four integer fields to their fixed widths, layer and tree zero (`tweak`,
`tweak.rs:42-52`, with the step of `Tweak::step`). -/
def tweakFields (tag step hi lo : Nat) : TweakFields :=
  ⟨BitVec.ofNat 5 tag, BitVec.ofNat 3 step, 0, 0, BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩

/-- The same address in tree `tree` of hypertree layer `layer` (`Tweak::at`, `tweak.rs:66-72`). -/
def TweakFields.at (fields : TweakFields) (layer tree : Nat) : TweakFields :=
  { fields with layer := BitVec.ofNat 8 layer, tree := BitVec.ofNat 32 tree }

/-- `P || A || payload`, the input of every tweakable hash call at the address `fields`
(`hasher`, `tweak.rs:95-99`). -/
def thInput (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    HashInput :=
  littleEndianBytes 16 parameter ++ addressBytes fields ++ payload

/-- **The key's seed `S_0`**, sampled uniformly. -/
noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace OverPermutation

open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)

/-! ## Chains, Merkle paths and trees, and the hash, over a permutation `π` -/

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

/-- `steps` steps of a hash chain from position `start`: the step leaving position
`t < stepFunctionCount` is `step t`, and a walk past position `stepFunctionCount` gives `0`. -/
def walkChain {m : Type → Type} [Monad m] {stepFunctionCount : Nat}
    (step : Fin stepFunctionCount → Digest → m Digest) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← walkChain step start steps value
      if h : start + steps < stepFunctionCount then step ⟨start + steps, h⟩ previous else pure 0

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  littleEndianBytes 16 left ++ littleEndianBytes 16 right

/-- Fold the leaf at index `leafIndex` and its path, the sibling at level `l` being
`siblingAtLevel l`, up `levels` levels: the node at level `l + 1` is
`node l (leafIndex / 2^(l + 1))` of its children in index order. -/
def foldPath {m : Type → Type} [Monad m] (node : Nat → Nat → HashInput → m Digest)
    (leafIndex : Nat) (siblingAtLevel : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | l + 1, value => do
      let current ← foldPath node leafIndex siblingAtLevel l value
      node l (leafIndex / 2 ^ (l + 1))
        (if leafIndex.testBit l then nodePayload (siblingAtLevel l) current
          else nodePayload current (siblingAtLevel l))

/-- Node `index` at level `level` of the Merkle tree over the leaves `leaf i`: the node at level
`l + 1` is `node l index` of its two children. -/
def buildTree {m : Type → Type} [Monad m] (leaf : Nat → m Digest)
    (node : Nat → Nat → HashInput → m Digest) : Nat → Nat → m Digest
  | 0, index => leaf index
  | l + 1, index => do
      let left ← buildTree leaf node l (2 * index)
      let right ← buildTree leaf node l (2 * index + 1)
      node l index (nodePayload left right)

/-- `buildTree` with the authentication path of the leaf `target`: node `index` at level `level`,
each node computed once, and the siblings of `target`'s path below it (`path l` the sibling at level
`l < level`, for a node above `target`). -/
def buildTreeWithPath {m : Type → Type} [Monad m] (leaf : Nat → m Digest)
    (node : Nat → Nat → HashInput → m Digest) (target : Nat) :
    Nat → Nat → m (Digest × (Nat → Digest))
  | 0, index => do return (← leaf index, fun _ ↦ 0)
  | l + 1, index => do
      let left ← buildTreeWithPath leaf node target l (2 * index)
      let right ← buildTreeWithPath leaf node target l (2 * index + 1)
      let value ← node l index (nodePayload left.1 right.1)
      return (value, if target.testBit l then Function.update right.2 l left.1
        else Function.update left.2 l right.1)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- **The hash `H`**: Keccak-256 over the permutation `π` (`keccak256With`), its digest's 32 bytes
(`digestBytes`) read as a little-endian number. -/
def keccakHash (input : HashInput) : m HashOutput :=
  (fun digest ↦ BitVec.ofNat 256 ((digestBytes digest).foldr (fun b acc ↦ b.toNat + 256 * acc) 0))
    <$> keccak256With π input

/-- `Th(P, A, M) = Truncate_n(H(P || A || M))` (`th`, `tweak.rs:102-104`). -/
def th (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) : m Digest := do
  return truncateHash (← keccakHash π (thInput parameter fields payload))

/-- `H(P || A || M)`, untruncated: two secrets for one hash (`th_pair`,
`tweak.rs:112-115`). -/
def thPair (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    m HashOutput :=
  keccakHash π (thInput parameter fields payload)

/-- `H(tag || S_0)`, all 32 bytes (`tagged_seed`, `tweak.rs:130-132`): the seed `S` a scheme
derives from. -/
def taggedSeed (tag : HashInput) (seed : MasterSeed) : m MasterSeed :=
  keccakHash π (tag ++ littleEndianBytes 32 seed)

end OverPermutation

end HashSig
