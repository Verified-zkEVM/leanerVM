module

public import Statement.SufCma
public import Statement.Fast.Keccak
public import Statement.Fast.SufCma

/-!
# Hash-based signatures: what leanXMSS and leanSPHINCS share

Read before the two schemes: the tweakable hash `Th(P, A, M) = Truncate_n(H(P ‖ A ‖ M))`, its
16-byte address and the types around it, which `crates/signatures/src/tweak.rs` gives both schemes
(namespace `HashSig`); the hash `H`, Keccak-256 over a permutation `π` of the Keccak state in any
monad (`keccakHash`), and the hash chains, Merkle paths and Merkle trees every chain, path and tree
of both schemes instantiates (`walkChain`, `foldPath`, `buildTree`, namespace `HashSig.Concrete`).
`Statement/LeanSphincs.lean` exports them into `Sphincs`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace HashSig

def digestBits : Nat := 128
def winternitzBits : Nat := 2
def chainLength : Nat := 2 ^ winternitzBits
abbrev MasterSeed := BitVec 256
abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec 256
abbrev Message := BitVec 256
abbrev PublicParameter := BitVec 128
abbrev Randomness := Digest
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
abbrev HashInput := List UInt8

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- The second 16 bytes of a hash output. Only the seed derivations of chain starts use them. -/
def upperHash (output : HashOutput) : Digest :=
  output.extractLsb' digestBits digestBits

/-- The half of a hash output that starts chain `n`: the first for even `n`, the second for odd `n`. -/
def hashHalf (n : Nat) (output : HashOutput) : Digest :=
  if n % 2 = 0 then truncateHash output else upperHash output

/-- `pk = (root, P)`. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The address of a hash call (`Tweak`, `crates/signatures/src/tweak.rs`): its type `tag < 32`, a
chain step `step < 8`, and two fields `hi < 2^24` and `lo < 2^32`. -/
structure TweakFields where
  tag : BitVec 5
  step : BitVec 3
  hi : BitVec 24
  lo : BitVec 32
deriving DecidableEq

/-- The 16 address bytes `lo || hi || (tag + 32 * step) || 0^8`. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  bytesLE 4 fields.lo ++ bytesLE 3 fields.hi ++ bytesLE 1 (fields.step ++ fields.tag) ++ bytesLE 8 0

/-- Convert the four integer fields to their fixed widths. -/
def tweakFields (tag step hi lo : Nat) : TweakFields :=
  ⟨BitVec.ofNat 5 tag, BitVec.ofNat 3 step, BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩

/-- `P || A || payload`, the input of every tweakable hash call at the address `fields`
(`hasher`, `tweak.rs`). -/
def thInput (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    HashInput :=
  bytesLE 16 parameter ++ fieldBytes fields ++ payload

/-- The key's seed `S_0`, uniform. -/
noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Concrete

open LeanVM.Semantics (KeccakState)

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

/-- `steps` steps of a hash chain from position `start`: the step leaving position `t < top` is
`step t`, and a walk past position `top` gives `0`. -/
def walkChain {m : Type → Type} [Monad m] {top : Nat} (step : Fin top → Digest → m Digest) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← walkChain step start steps value
      if h : start + steps < top then step ⟨start + steps, h⟩ previous else pure 0

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

/-- Fold the leaf at index `idx` and its path, the sibling at level `l` being `path l`, up `levels`
levels: the node at level `l + 1` is `node l (idx / 2^(l + 1))` of its children in index order. -/
def foldPath {m : Type → Type} [Monad m] (node : Nat → Nat → HashInput → m Digest) (idx : Nat)
    (path : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | l + 1, value => do
      let current ← foldPath node idx path l value
      node l (idx / 2 ^ (l + 1))
        (if idx.testBit l then nodePayload (path l) current else nodePayload current (path l))

/-- Node `index` at level `level` of the Merkle tree over the leaves `leaf i`: the node at level
`l + 1` is `node l index` of its two children. -/
def buildTree {m : Type → Type} [Monad m] (leaf : Nat → m Digest)
    (node : Nat → Nat → HashInput → m Digest) : Nat → Nat → m Digest
  | 0, index => leaf index
  | l + 1, index => do
      let left ← buildTree leaf node l (2 * index)
      let right ← buildTree leaf node l (2 * index + 1)
      node l index (nodePayload left right)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- **The hash `H`**: Keccak-256 over the permutation `π` (`keccak256With`), its digest's 32 bytes
read as a little-endian number (`Common.SufCma.digestBitVec`). -/
def keccakHash (input : HashInput) : m HashOutput :=
  (fun d ↦ Common.SufCma.digestBitVec d.toBytes) <$>
    LeanVM.Protocol.KeccakHash.keccak256With π input

/-- `Th(P, A, M) = Truncate_n(H(P || A || M))` (`th`, `tweak.rs`). -/
def th (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) : m Digest := do
  return truncateHash (← keccakHash π (thInput parameter fields payload))

/-- `H(P || A || M)`, untruncated: two secrets for one hash (`th_pair`). -/
def thPair (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    m HashOutput :=
  keccakHash π (thInput parameter fields payload)

/-- `H(tag || S_0)`, all 32 bytes (`tagged_seed`): the seed `S` a scheme derives from. -/
def taggedSeed (tag : HashInput) (seed : MasterSeed) : m MasterSeed :=
  keccakHash π (tag ++ bytesLE 32 seed)

end Concrete

end HashSig
