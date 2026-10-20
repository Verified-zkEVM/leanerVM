import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# XMSS scheme

Parameters, serialized hash inputs, key generation, signing, and verification for the instance defined in `doc/xmss/main.tex`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-! ## The instance: parameters, types, and hash-input layout -/

def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def randomnessBits : Nat := 192
/-- Encoding attempts per signature, `A_max`. -/
def signingAttemptLimit : Nat := 2 ^ 32
/-- The Merkle tree height `h`; the lifetime is `L = 2^h` leaf indices. -/
def treeHeight : Nat := 32
def lifetime : Nat := 2 ^ treeHeight
def winternitzBits : Nat := 3
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 42
def targetSum : Nat := 195

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := BitVec randomnessBits
/-- `idx < L`. -/
abbrev LeafIndex := Fin lifetime
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
/-- A chain step; the tweak carries `2^w * i + step`. -/
abbrev ChainStep := Fin (chainLength - 1)
/-- A level of the stored tree, `0` the leaves and `h` the root. -/
abbrev MerkleHeight := Fin (treeHeight + 1)
/-- A level of the authentication path, below the root; the tweak carries `level + 1`. -/
abbrev MerkleLevel := Fin treeHeight
/-- A node within a level. Level `ℓ` only uses the values below `2^(h - ℓ)`. -/
abbrev MerkleNode := Fin lifetime
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- `pk = (root, P)`. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- Cached chain starts, chain values and Merkle nodes, together with the public parameter. -/
structure SecretKey where
  parameter : PublicParameter
  chainStart : LeafIndex → ChainIndex → Digest
  chainValue : LeafIndex → ChainIndex → Digit → Digest
  treeValue : MerkleHeight → MerkleNode → Digest

/-- `sigma = (rho, sigma_OTS, path_ep)`: the encoding randomness, the `v` chain values and the `h` authentication nodes. -/
structure Signature where
  randomness : Randomness
  chainValue : ChainIndex → Digest
  authPath : Fin treeHeight → Digest
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The three fields of the specification's `enc(t, p, j)`. -/
structure TweakFields where
  tag : BitVec 8
  position : BitVec 32
  leafIndex : BitVec 32
deriving DecidableEq

/-- The protocol domain separator. -/
def protocolDomainSep : UInt8 := 0

/-- The specification's 16 tweak bytes `protocol_domain_sep || tag || 0 || 0 || position || 0^4 || leafIndex`, each field serialized least significant byte first. -/
def fieldBytes (fields : TweakFields) : List UInt8 :=
  [protocolDomainSep] ++ bytesLE 1 fields.tag ++ [0, 0] ++ bytesLE 4 fields.position ++
    List.replicate 4 0 ++ bytesLE 4 fields.leafIndex

/-- Convert the specification's three integer fields to their fixed widths. -/
def tweakFields (tag position leafIndex : Nat) : TweakFields :=
  ⟨BitVec.ofNat 8 tag, BitVec.ofNat 32 position, BitVec.ofNat 32 leafIndex⟩

/-- The verification hash domains, tweak types `1` to `4`. -/
inductive HashDomain where
  | chain (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
  | leaf (leafIndex : LeafIndex)
  | merkle (level : MerkleLevel) (node : MerkleNode)
  | encoding (leafIndex : LeafIndex)
deriving DecidableEq

/-- Serialize a typed hash domain into the fields of a tweak. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain leafIndex chain step => tweakFields 1 (chainLength * chain + step) leafIndex
  | .leaf leafIndex => tweakFields 2 0 leafIndex
  | .merkle level node => tweakFields 3 (level.val + 1) node
  | .encoding leafIndex => tweakFields 4 0 leafIndex

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : List UInt8 :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `tweak || parameter || message` used by every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message

/-- `tweak(7, trial, leafIndex) || P || S || m`. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (leafIndex : LeafIndex) (message : Message) (trial : BitVec 32) : HashInput :=
  fieldBytes ⟨7#8, trial, BitVec.ofNat 32 leafIndex.val⟩ ++
    bytesLE 16 parameter ++ bytesLE 32 seed ++ bytesLE 32 message

inductive KeygenDomain where
  | parameter
  | chain (leafIndex : LeafIndex) (chain : ChainIndex)
deriving DecidableEq

def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0
  | .chain leafIndex chain => tweakFields 0 chain leafIndex

/-- `tweak || P || S`; parameter derivation uses `P = 0`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  fieldBytes (keygenDomainFields domain) ++ bytesLE 16 parameter ++ bytesLE 32 seed

/-! ### The target-sum code

`v = 42` chunks of `w = 3` bits, 21 in each half of the digest, one pinned bit per half, and the code is the words of digit sum `T = 195`. -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- `v / 2 = 21` digits in each half of the digest. -/
def digitsPerHalf : Nat := numChains / 2

/-- Offset of a three-bit digit, skipping padding bits 63 and 127. -/
def digitOffset (i : ChainIndex) : Nat :=
  winternitzBits * i.val + if i.val < digitsPerHalf then 0 else 1

/-- `x_i`, the three bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- Decode the concrete little-endian layout used by `IncEnc`: 21 three-bit digits, padding bit 63, 21 digits, and padding bit 127. A digest decodes exactly when both padding bits are clear and the digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none

end TargetSum

/-! ## The algorithms

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and signing. Hashing routines work in any monad with access to `HashSpec`. The experiment samples the master seed and charges every hash call, including repeated calls. Out-of-range branches only make the definitions total; honest algorithms never reach them. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- Private uniform sampling and the shared hash oracle. Only hash calls count toward the query budget. -/
abbrev OracleWorld := unifSpec + HashSpec

/-- Enter a query log into a cache, in order. -/
def extendHashCacheWithLog (initialCache : QueryCache HashSpec) :
    QueryLog HashSpec → QueryCache HashSpec
  | [] => initialCache
  | ⟨input, output⟩ :: tail =>
      extendHashCacheWithLog (initialCache.cacheQuery input output) tail

/-- The cache a query log records. -/
def hashCacheOfLog (log : QueryLog HashSpec) : QueryCache HashSpec :=
  extendHashCacheWithLog ∅ log

namespace Concrete

/-- `m || rho || 0^64`. -/
def encodingPayload (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 32 message ++ bytesLE 24 randomness ++ List.replicate 8 0

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One query to the random oracle `H`. -/
def oracleHash (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

/-- `Th(P, tw, M) = Truncate_n(H(tw || P || M))`. -/
def tweakableHash
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) : m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

/-- The digest `D` of `IncEnc(P, m, rho, idx)`. -/
def encodingHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) : m Digest :=
  tweakableHash parameter (.encoding leafIndex) (encodingPayload message randomness)

/-- One chain step, under `tweak_chain(idx, i, step + 1)`. -/
def chainHash (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) : m Digest :=
  tweakableHash parameter (.chain leafIndex chain step) (bytesLE 16 value)

/-- `X_{0,idx}`, the hash of the `v` public values. -/
def leafHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf leafIndex) (leafPayload endpoints)

/-- `X_{level+1,node}` from its two children. -/
def nodeHash (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) : m Digest :=
  tweakableHash parameter (.merkle level node) (nodePayload left right)

/-! ### Verification -/

/-- `A_level`, or `0` above the tree. -/
def signaturePath (signature : Signature) (level : Nat) : Digest :=
  if hlevel : level < treeHeight then signature.authPath ⟨level, hlevel⟩ else 0

/-- `Chain_{i,idx}(P, start, steps, value)`: the step onto position `start + steps + 1` carries tweak position `2^w * i + start + steps`. -/
def chainWalk (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | position, steps + 1, value => do
      let previous ← chainWalk parameter leafIndex chain position steps value
      if hposition : position + steps < chainLength - 1 then
        chainHash parameter leafIndex chain ⟨position + steps, hposition⟩ previous
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `2^w - 1 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter leafIndex chain digit.val (chainLength - 1 - digit.val) value

/-- `pk'_{idx,i}` for every chain. -/
def recoverEndpoints (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding) (signature : Signature) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    recoverChain parameter leafIndex chain (encoding chain) (signature.chainValue chain)

/-- The index of the Merkle node on the path of `leafIndex` one level above `level`. -/
def nodeIndex (leafIndex : LeafIndex) (level : Nat) : MerkleNode :=
  ⟨leafIndex.val / 2 ^ (level + 1), by
    have hle := Nat.div_le_self leafIndex.val (2 ^ (level + 1))
    exact hle.trans_lt leafIndex.isLt⟩

/-- `Z_{level+1}` from `Z_level` and `A_level`, in the order bit `level` of the leaf index dictates. -/
def authenticationNodeHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (level : Nat) (current sibling : Digest) : m Digest :=
  if hlevel : level < treeHeight then
    if leafIndex.val.testBit level then
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex leafIndex level) sibling current
    else
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex leafIndex level) current sibling
  else
    pure 0

/-- `Z_levels`, folded up from the leaf `Z_0`. -/
def authenticationRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) : Nat → Digest → m Digest
  | 0, leaf => pure leaf
  | levels + 1, leaf => do
      let current ← authenticationRoot parameter leafIndex signature levels leaf
      authenticationNodeHash parameter leafIndex levels current (signaturePath signature levels)

/-- Accept exactly when `Z_h = root`. -/
def verifyAfterLeaf
    (publicKey : PublicKey) (leafIndex : LeafIndex) (signature : Signature) (leaf : Digest) : m Bool := do
  let root ← authenticationRoot publicKey.parameter leafIndex signature treeHeight leaf
  return decide (root = publicKey.root)

/-- `Ver(pk, idx, m, sigma)`. -/
def verify (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) : m Bool := do
  let digest ← encodingHash publicKey.parameter leafIndex message signature.randomness
  let some encoding := TargetSum.decodeDigest digest | return false
  let endpoints ← recoverEndpoints publicKey.parameter leafIndex encoding signature
  let leaf ← leafHash publicKey.parameter leafIndex endpoints
  verifyAfterLeaf publicKey leafIndex signature leaf

/-! ### Precomputed chains and tree -/

/-- `pk_{idx,i} = Chain(P, 0, 2^w - 1, sk_{idx,i})` for every chain. -/
def oneTimePublicKey (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) : m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    chainWalk parameter leafIndex chain 0 (chainLength - 1) (secret leafIndex chain)

/-- `X_{0,idx}` from the secrets. -/
def leafAt (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) : m Digest := do
  let endpoints ← oneTimePublicKey parameter secret leafIndex
  leafHash parameter leafIndex endpoints

/-- A natural read as a node index. -/
def merkleNodeOfNat (value : Nat) : MerkleNode :=
  ⟨value % lifetime,
    Nat.mod_lt _ (by simp [lifetime])⟩

/-- `2j` or `2j + 1`. -/
def childNode (node : MerkleNode) (right : Bool) : MerkleNode :=
  merkleNodeOfNat (2 * node.val + if right then 1 else 0)

/-- `X_{levels,node}`, the Merkle tree over the one-time leaves. -/
def treeNode (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    Nat → MerkleNode → m Digest
  | 0, node => leafAt parameter secret node
  | levels + 1, node => do
      let left ← treeNode parameter secret levels (childNode node false)
      let right ← treeNode parameter secret levels (childNode node true)
      if hlevel : levels < treeHeight then
        nodeHash parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0

/-- The root is node `0` of level `h`. -/
def rootNode : MerkleNode :=
  ⟨0, by simp [lifetime]⟩

/-- Answer a hash query from a recorded query cache, and by 0 for an unrecorded input. -/
def replayHash (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0

/-- Compute the stored chain values and Merkle nodes by replaying the key-generation query log. -/
def precomputedSecretKey (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (cache : QueryCache HashSpec) :
    SecretKey where
  parameter := parameter
  chainStart := secret
  chainValue := fun leafIndex chain digit =>
    evalWithAnswerFn (replayHash cache)
      (chainWalk parameter leafIndex chain 0 digit.val (secret leafIndex chain) :
        OracleComp HashSpec Digest)
  treeValue := fun height node =>
    evalWithAnswerFn (replayHash cache)
      (treeNode parameter secret height.val node : OracleComp HashSpec Digest)

/-! ### Signing -/

/-- `floor(idx / 2^level) xor 1`, the sibling on the path. -/
def authenticationPathNode (leafIndex : LeafIndex) (level : MerkleLevel) : MerkleNode :=
  merkleNodeOfNat (Nat.xor (leafIndex.val / 2 ^ level.val) 1)

/-- The signature once the encoding is found. -/
def precomputedSignWithEncoding (secretKey : SecretKey) (leafIndex : LeafIndex)
    (randomness : Randomness) (encoding : Encoding) : Signature :=
  { randomness := randomness
    chainValue := fun chain => secretKey.chainValue leafIndex chain (encoding chain)
    authPath := fun level => secretKey.treeValue level.castSucc (authenticationPathNode leafIndex level) }

/-- One attempt: hash once, and sign if the digest encodes. -/
def precomputedSignAttempt (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter leafIndex message randomness
  let some encoding := TargetSum.decodeDigest digest | return none
  return some (precomputedSignWithEncoding secretKey leafIndex randomness encoding)

attribute [irreducible] verifyAfterLeaf treeNode

end Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

def deriveRandomizer (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) (trial : BitVec 32) : m Randomness := do
  return (← Concrete.oracleHash (randomizerHashInput parameter seed leafIndex message trial)).extractLsb' 0 randomnessBits

noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

/-- The seed and the chain and tree values computed during key generation. -/
structure SecretKey where
  seed : MasterSeed
  precomputed : XmssSecurity.SecretKey

def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let parameter ← deriveKey 0 .parameter seed
  let secret ← Concrete.sequenceFin fun leafIndex => Concrete.sequenceFin fun chain =>
    deriveKey parameter (.chain leafIndex chain) seed
  let result ← (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
    OracleComp HashSpec Digest).withQueryLog
  let precomputed := Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)
  return (⟨result.1, parameter⟩, ⟨seed, precomputed⟩)

/-- Derive trials in increasing order, stopping at the first admissible encoding. -/
def signFrom (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) : Nat → Nat → m (Option Signature)
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness ← deriveRandomizer secretKey.precomputed.parameter secretKey.seed leafIndex message (BitVec.ofNat 32 trial)
      match ← Concrete.precomputedSignAttempt secretKey.precomputed leafIndex message randomness with
      | some signature => return some signature
      | none => signFrom secretKey leafIndex message attempts (trial + 1)

def sign (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) : m (Option Signature) :=
  signFrom secretKey leafIndex message signingAttemptLimit 0

end Seeded

end XmssSecurity
