module

public import Statement.HashSignatures
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# leanXMSS

The leanXMSS scheme (key generation, signing, verification, hashing with Keccak-256 over a
permutation `π`), on what it shares with leanSPHINCS (`Statement/HashSignatures.lean`, namespace
`HashSig`), the SUF-CMA game of `Statement/SufCma.lean` instantiated with it, and the end statement
`LeanXmss.RandomPermutationModel.LeanXmssStronglyUnforgeable`, proved by
`XmssSecurity.leanXmss_rpm_security` (`lean_xmss`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

/-!
## leanXMSS

The scheme of `crates/signatures/src/lean_xmss`, specified in `doc/lean_xmss`: two layers of XMSS of
height 16 over WOTS+C one-time keys. Key `b` of the top tree signs the root of bottom tree `b`; a
leaf index `idx < 2^32` signs with bottom key `idx`, in bottom tree `idx / 2^16`.

* WOTS+C: 58 chains of 4 positions. A 16-byte digest is read as 64 base-4 digits, little endian; it
  is a codeword when the last 6 digits are zero and the other 58 sum to 106.
* Every hash input is `P || A || payload`: the 16-byte public parameter, the 16-byte address
  `lo (4 bytes) || hi (3 bytes) || (type + 32 step) || layer || tree (4 bytes) || 0^24`, its layer
  and tree zero (leanSPHINCS's hypertree fills them), then the payload. The top layer sets
  bit 23 of `hi`. A chain step's address carries the step but not the chain, whose index follows the
  value in the payload.
* `H` is the leanVM hash, Keccak-256 on the bytes of its input, over a permutation `π` of the Keccak
  state (`keccakHash`): in the end statement (the last section) the random permutation.
* The secret key is a 32-byte seed `S_0` (`HashSig.SecretKey`). Every secret derives from
  `S = H("leanXMSS" || S_0)`, all 32 bytes, which the signer derives again at each signature, as the
  crate's does, and the public parameter from `S`, which the crate's key keeps from key generation.
* Signing a message `M` with key `e` of layer `l`: `R0 = Th(P, A_rnd(l, e), S || M)`, then the least
  `c < 2^32` such that `Th(P, A_msg(l, e), M || (R0 + c))` is a codeword.
-/

namespace LeanXmss

open HashSig

/-! ### leanXMSS's parameters, types and hash-input layout -/

/-- `v`, the chains of a one-time key. -/
def chainCount : Nat := 58
/-- `T`, the sum of a codeword's `v` digits. -/
def targetSum : Nat := 106
/-- The layers of XMSS trees: `2`. -/
def layerCount : Nat := 2
/-- `h`, the height of each layer's trees. -/
def layerHeight : Nat := 16
/-- Leaf indices `idx < 2^32`. -/
def lifetime : Nat := 2 ^ (layerCount * layerHeight)
/-- Randomizer trials per one-time signature, `A_max`. -/
def randomizerAttemptLimit : Nat := 2 ^ 32

/-- `l`: `0` the bottom layer, `1` the top. -/
abbrev Layer := Fin layerCount
/-- `idx`, a leaf index. -/
abbrev LeafIndex := Fin lifetime
/-- `e`, a one-time key of a layer: below `2^32` on the bottom layer, below `2^16` on the top. -/
abbrev KeyIndex := Fin lifetime
/-- `i`, a chain of a one-time key. -/
abbrev ChainIndex := Fin chainCount
/-- A pair of chains `(2t, 2t + 1)`, `t < 29`: one seed derivation. -/
abbrev ChainPairIndex := Fin (chainCount / 2)
/-- The `v` digits a codeword assigns to the chains: how far each chain is opened. -/
abbrev Encoding := ChainIndex → WinternitzDigit

/-- The bottom layer, whose keys sign messages. -/
def bottomLayer : Layer := ⟨0, by decide⟩
/-- The top layer, whose keys sign the bottom trees' roots. -/
def topLayer : Layer := ⟨1, by decide⟩

/-- The key of layer `l` a leaf index signs with: `idx` at the bottom, `idx / 2^16` at the top. -/
def keyIndexOnLayer (leafIndex : LeafIndex) (layer : Layer) : KeyIndex :=
  ⟨leafIndex.val / 2 ^ (layerHeight * layer.val),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leafIndex.isLt⟩

/-- One layer's signature: the randomizer, the `v` revealed chain values and the authentication
path. -/
structure LayerSignature where
  /-- The randomizer `R0 + c` that makes the message digest a codeword. -/
  randomizer : Randomizer
  /-- Chain `i` opened to its codeword digit. -/
  chainValues : ChainIndex → Digest
  /-- The siblings from the leaf up to the tree's root, one per level. -/
  authenticationPath : Fin layerHeight → Digest
deriving DecidableEq

/-- The leaf index, then the bottom layer's signature and the top layer's: 2404 bytes. -/
structure Signature where
  /-- The leaf index `idx` it signs with. -/
  leafIndex : LeafIndex
  /-- Each layer's signature. -/
  layers : Layer → LayerSignature
deriving DecidableEq

/-- `hi` on layer `l`: the top layer sets bit 23 (`layer_hi`). -/
def layerHi (layer : Layer) (field : Nat) : Nat := field + 2 ^ 23 * layer.val

/-- The verification hash domains. A node at `level` is the node of tree level `level`, its index
global on the bottom layer (`idx / 2^level`). -/
inductive HashDomain where
  /-- A step of a chain of key `key`. -/
  | chain (layer : Layer) (key : KeyIndex) (step : ChainStep)
  /-- Key `key`'s leaf, the hash of its chain ends. -/
  | leaf (layer : Layer) (key : KeyIndex)
  /-- A tree's node at `level`, index `nodeIndex`. -/
  | node (layer : Layer) (level : Nat) (nodeIndex : Nat)
  /-- The message digest under key `key`. -/
  | message (layer : Layer) (key : KeyIndex)
deriving DecidableEq

/-- Types `TWEAK_CHAIN = 1`, `TWEAK_LEAF = 2`, `TWEAK_NODE = 3`, `TWEAK_MSG = 12`. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain layer key step => tweakFields 1 step (layerHi layer 0) key
  | .leaf layer key => tweakFields 2 0 (layerHi layer 0) key
  | .node layer level nodeIndex => tweakFields 3 0 (layerHi layer level) nodeIndex
  | .message layer key => tweakFields 12 0 (layerHi layer 0) key

/-- `leanXMSS`, the 8 ASCII bytes hashed before the key's seed (`SEED_TAG`). -/
def seedTag : HashInput := [0x6c, 0x65, 0x61, 0x6e, 0x58, 0x4d, 0x53, 0x53]

/-- The seed derivations: the parameter (under `P = 0`), and the starts of chains `2t` and `2t + 1`
of a one-time key, the two halves of one hash. -/
inductive KeygenDomain where
  /-- The public parameter `P`. -/
  | parameter
  /-- The starts of chains `2t` and `2t + 1` of key `key`, `t = chainPairIndex`. -/
  | oneTimeChainPair (layer : Layer) (key : KeyIndex) (chainPairIndex : ChainPairIndex)
deriving DecidableEq

/-- `TWEAK_PARAMETER = 5`, `TWEAK_PRF = 0` (`hi` the pair of chains, `lo` the key). -/
def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0 0
  | .oneTimeChainPair layer key chainPairIndex => tweakFields 0 0 (layerHi layer chainPairIndex) key

/-- The pair of chains a chain belongs to. -/
def chainPair (chain : ChainIndex) : ChainPairIndex :=
  ⟨chain.val / 2, by have h : chain.val < 58 := chain.isLt; show chain.val / 2 < 29; omega⟩

/-! #### The codeword -/

namespace Codeword

/-- The sum of a word's digits. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- A codeword: of its 64 digits (`digestDigits`), the last `64 - v` are zero and the first `v` sum
to `T`. -/
abbrev Valid (digest : Digest) : Prop :=
  digest.toNat / 2 ^ (winternitzBits * chainCount) = 0 ∧ sum (digestDigits digest) = targetSum

/-- The word a digest encodes, its first `v` digits, if it is a codeword. -/
def decode (digest : Digest) : Option Encoding :=
  if Valid digest then some (digestDigits digest) else none

end Codeword

/-! ### The algorithms, over a permutation `π` of the Keccak state in any monad -/

namespace Verification

open LeanVM.Semantics (KeccakState)
open HashSig.OverPermutation

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- The tweakable hash at a hash domain's address. -/
abbrev tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest :=
  th π parameter (hashDomainFields domain) payload

/-! #### The one-time signature -/

/-- `value || LE_16(i)`, the payload of a chain step of chain `i`. -/
def chainPayload (chainIndex : ChainIndex) (value : Digest) : HashInput :=
  littleEndianBytes 16 value ++ littleEndianBytes 16 (BitVec.ofNat 128 chainIndex.val)

/-- Chain `i` of a one-time key; the step leaving position `s` carries step `s`. -/
def chainWalk (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (chainIndex : ChainIndex) : Nat → Nat → Digest → m Digest :=
  walkChain fun step value ↦
    tweakableHash π parameter (.chain layer key step) (chainPayload chainIndex value)

/-- The verifier's half of a chain: walk the remaining `3 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (chainIndex : ChainIndex) (digit : WinternitzDigit) (value : Digest) : m Digest :=
  chainWalk π parameter layer key chainIndex digit.val (chainLength - 1 - digit.val) value

/-- The one-time leaf: the hash of the `v` chain ends (`wots_leaf_hash`). -/
def leafHash (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash π parameter (.leaf layer key) (digestsPayload endpoints)

/-- `D = Th(P, A_msg(l, e), M || rho)` (`message_digest`). -/
def messageDigest (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) (randomizer : Randomizer) : m Digest :=
  tweakableHash π parameter (.message layer key) (message ++ littleEndianBytes 16 randomizer)

/-- `Ots.leaf` (`wots_leaf`): the leaf a claimed one-time signature recovers, or nothing if its
digest is not a codeword. -/
def otsLeaf (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (message : HashInput)
    (randomizer : Randomizer) (values : ChainIndex → Digest) : m (Option Digest) := do
  let digest ← messageDigest π parameter layer key message randomizer
  let some encoding := Codeword.decode digest | return none
  let endpoints ← sequenceFin fun chainIndex =>
    recoverChain π parameter layer key chainIndex (encoding chainIndex) (values chainIndex)
  let value ← leafHash π parameter layer key endpoints
  return some value

/-! #### The trees -/

/-- `Tree.fold`: fold a key's leaf and path into its tree's root. -/
def treeFold (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) : Nat → Digest → m Digest :=
  foldPath (fun level nodeIndex ↦ tweakableHash π parameter (.node layer (level + 1) nodeIndex))
    key.val fun level ↦ if h : level < layerHeight then path ⟨level, h⟩ else 0

/-- The root a layer's signature by key `e` reaches from `message`, or nothing (`layer_root`). -/
def layerRoot (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (message : HashInput)
    (layerSignature : LayerSignature) : m (Option Digest) := do
  let some leaf ← otsLeaf π parameter layer key message layerSignature.randomizer
      layerSignature.chainValues | return none
  let root ← treeFold π parameter layer key layerSignature.authenticationPath layerHeight leaf
  return some root

/-! #### Verification -/

/-- `Ver(pk, m, sigma)`: recover the bottom root from the message, then the top root from the bottom
root, and compare it with the public key. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let leafIndex := signature.leafIndex
  let some bottomRoot ← layerRoot π publicKey.parameter bottomLayer
      (keyIndexOnLayer leafIndex bottomLayer) (littleEndianBytes 32 message)
      (signature.layers bottomLayer) | return false
  let some root ← layerRoot π publicKey.parameter topLayer (keyIndexOnLayer leafIndex topLayer)
      (littleEndianBytes 16 bottomRoot) (signature.layers topLayer) | return false
  return decide (root = publicKey.root)

end Verification

/-- **leanXMSS verification as deployed**: over Keccak-f[1600], the hash Keccak-256. The leaf index
is the signature's. -/
def verifyWithKeccak (publicKey : PublicKey) (message : Message) (signature : Signature) : Bool :=
  Id.run (Verification.verify (m := Id) LeanVM.Semantics.keccakF1600 publicKey message signature)

namespace KeyGenerationAndSigning

open Verification HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- `wots_secrets`: the starts of the `v` chains of a one-time key, from 29 seed derivations.
Chains `2t` and `2t + 1` start at the two halves of derivation `t`. -/
def otsSecrets (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (seed : MasterSeed) :
    m (ChainIndex → Digest) := do
  let outputs ← sequenceFin fun chainPairIndex : ChainPairIndex =>
    thPair π parameter (keygenDomainFields (.oneTimeChainPair layer key chainPairIndex))
      (littleEndianBytes 32 seed)
  return fun chainIndex => hashHalfForChain chainIndex.val (outputs (chainPair chainIndex))

/-- The chain ends of a one-time key. -/
def oneTimePublicKey (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let secrets ← otsSecrets π parameter layer key seed
  sequenceFin fun chainIndex =>
    chainWalk π parameter layer key chainIndex 0 (chainLength - 1) (secrets chainIndex)

/-- The randomizer trials `R0 + c, R0 + c + 1, ...`, stopping at the first codeword. -/
def otsSignFrom (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (seed : MasterSeed)
    (message : HashInput) (randomizerBase : Randomizer) :
    Nat → Nat → m (Option (Randomizer × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomizer := randomizerBase + BitVec.ofNat digestBits trial
      let digest ← messageDigest π parameter layer key message randomizer
      match Codeword.decode digest with
      | some encoding => do
          let secrets ← otsSecrets π parameter layer key seed
          let values ← sequenceFin fun chainIndex =>
            chainWalk π parameter layer key chainIndex 0 (encoding chainIndex).val
              (secrets chainIndex)
          return some (randomizer, values)
      | none => otsSignFrom parameter layer key seed message randomizerBase attempts (trial + 1)

/-- `wots_sign`: derive `R0`, take the least admissible trial, then open the chains. -/
def otsSign (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (seed : MasterSeed)
    (message : HashInput) : m (Option (Randomizer × (ChainIndex → Digest))) := do
  -- `R0`, the randomizer base (`TWEAK_RANDOMIZER = 7`)
  let randomizerBase ← th π parameter (tweakFields 7 0 (layerHi layer 0) key)
    (littleEndianBytes 32 seed ++ message)
  otsSignFrom π parameter layer key seed message randomizerBase randomizerAttemptLimit 0

/-- Node `nodeIndex` at tree level `level` of layer `l`, from the one-time keys below it. On the
bottom layer node indices are global: node `j` at level `level` is in bottom tree
`j / 2^(16 - level)`. -/
def treeNode (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed) : Nat → Nat
    → m Digest :=
  buildTree (fun nodeIndex ↦ do
      let key : KeyIndex := ⟨nodeIndex % lifetime, Nat.mod_lt _ (by decide)⟩
      leafHash π parameter layer key (← oneTimePublicKey π parameter layer key seed))
    fun level nodeIndex ↦ tweakableHash π parameter (.node layer (level + 1) nodeIndex)

/-- The authentication path of key `e`: at level `level`, the sibling of `e / 2^level`. -/
def treePath (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed) (key : KeyIndex) :
    m (Fin layerHeight → Digest) :=
  sequenceFin fun level =>
    treeNode π parameter layer seed level.val (Nat.xor (key.val / 2 ^ level.val) 1)

/-- The public parameter of the scheme seed `S` (`public_param`, `tweak.rs:135-137`). -/
def publicParameterOf (seed : MasterSeed) : m PublicParameter :=
  th π 0 (keygenDomainFields .parameter) (littleEndianBytes 32 seed)

/-- `Gen` (`key_gen_from_seed`, `generate`, `scheme.rs:173-191`): the secret key is the seed `S_0`;
hash it into `S` (`scheme_seed`, `hash.rs:27-29`), derive the public parameter and build the top
tree. -/
def keygenFromSeed (masterSeed : MasterSeed) : m (PublicKey × SecretKey) := do
  let seed ← taggedSeed π seedTag masterSeed
  let parameter ← publicParameterOf π seed
  let root ← treeNode π parameter topLayer seed layerHeight 0
  return (⟨root, parameter⟩, masterSeed)

/-- One layer's signature by key `e` of `message`: the one-time signature and the path. -/
def signLayer (seed : MasterSeed) (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) : m (Option LayerSignature) := do
  let some (randomizer, values) ← otsSign π parameter layer key seed message | return none
  let path ← treePath π parameter layer seed key
  return some ⟨randomizer, values, path⟩

/-- `Sign` at leaf index `idx` with the scheme seed `S` and the public parameter: the bottom key
`idx` signs `m`, and the top key `idx / 2^16` signs the root of bottom tree `idx / 2^16`. -/
def signWithSchemeSeed (seed : MasterSeed) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) : m (Option Signature) := do
  let bottomKey := keyIndexOnLayer leafIndex bottomLayer
  let topKey := keyIndexOnLayer leafIndex topLayer
  let some bottom ← signLayer π seed parameter bottomLayer bottomKey (littleEndianBytes 32 message)
    | return none
  let bottomRoot ← treeNode π parameter bottomLayer seed layerHeight topKey.val
  let some top ← signLayer π seed parameter topLayer topKey (littleEndianBytes 16 bottomRoot)
    | return none
  return some ⟨leafIndex, fun layer => if layer = bottomLayer then bottom else top⟩

/-- `Sign` at leaf index `idx` (`sign`, `sign_over`, `scheme.rs:196-248`): the scheme seed
`S = H(leanXMSS || S_0)` of the key's seed (`scheme_seed`, `hash.rs:27-29`), the public parameter
of `S`, then the two layers' signatures. -/
def sign (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) :
    m (Option Signature) := do
  let seed ← taggedSeed π seedTag secretKey
  let parameter ← publicParameterOf π seed
  signWithSchemeSeed π seed parameter leafIndex message

end KeyGenerationAndSigning

/-! ## Signing requests, forgeries and transcripts -/

/-- A signing request: a leaf index and a 32-byte message. -/
structure SigningRequest where
  /-- The leaf index to sign with. -/
  leafIndex : LeafIndex
  /-- The message. -/
  message : Message
deriving DecidableEq

/-- A claimed forgery: a message and a signature, which carries its leaf index. -/
structure Forgery where
  /-- The message. -/
  message : Message
  /-- Its claimed signature. -/
  signature : Signature
deriving DecidableEq

/-- The signing oracle answers a request with a signature, or `none` if the signer fails. -/
abbrev SigningOracleSpec := SigningRequest →ₒ Option Signature

namespace SigningTranscript

/-- A transcript is valid when no leaf index occurs twice. -/
abbrev NoLeafIndexReused (log : QueryLog SigningOracleSpec) : Prop :=
  (log.map fun entry => entry.1.leafIndex).Nodup

end SigningTranscript

/-! ## Security in the random-permutation model -/

namespace RandomPermutationModel

open Common Common.SufCma

/-- leanXMSS in the generic SUF-CMA game, over `π` (`queryPermutation`): the seed, key generation,
the signer of a request, the verifier, and the winning condition: a valid transcript without the
forgery (`SignerReturnedForgery`). -/
noncomputable def sufCmaScheme :
    Scheme MasterSeed PublicKey SecretKey SigningRequest (Option Signature) Forgery where
  sampleSeed := sampleMasterSeed
  generateKeys := KeyGenerationAndSigning.keygenFromSeed queryPermutation
  sign sk request := KeyGenerationAndSigning.sign queryPermutation sk request.leafIndex
      request.message
  verify pk forgery := Verification.verify queryPermutation pk forgery.message forgery.signature
  winningCondition log forgery :=
    decide (SigningTranscript.NoLeafIndexReused log ∧
      ¬SignerReturnedForgery SigningRequest.message log forgery.message forgery.signature)

/-- **leanXMSS in the random-permutation model**: an adversary whose game makes at most `Q`
permutation calls, `Q ≥ 1`, forges with probability at most `(Q + 1) · 2^-127`
(`StronglyUnforgeable` at 127 bits). `Q` counts every call on the game's worst path, the honest
signer's included (`QueryCostAtMost` is structural): a signing request costs about `2^33` calls
(each layer's `2^32` grinding trials, and the paths and the bottom root rebuilt, about `2^25`), so
`Q ≥ 2^65` once the adversary uses all `2^32` leaves, where the bound is about `2^-62`. -/
abbrev LeanXmssStronglyUnforgeable : Prop :=
  StronglyUnforgeable sufCmaScheme 127

end RandomPermutationModel

end LeanXmss

end
