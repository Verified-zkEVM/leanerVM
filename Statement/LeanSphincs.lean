module

public import Statement.HashSignatures
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# leanSPHINCS

The scheme of `crates/signatures/src/lean_sphincs` (`mod.rs`, `hash.rs`, `wots.rs`, `fors.rs`,
`scheme.rs`; the addresses in `crates/signatures/src/tweak.rs`), specified in `doc/lean_sphincs`,
at leanVM `ed7d2b9c`: FORS without its root hash under a hypertree of WOTS+C keys.

* A message digest of two calls picks an index `idx < 2^26` (a bottom leaf, and so a FORS instance)
  and one leaf in each of the instance's 24 FORS trees of height 10 (§sec:fts). The FORS key is the
  two top nodes of every tree, 48 nodes, not hashed: the bottom one-time key's encoding absorbs
  them.
* The hypertree has 3 layers, of heights 8, 8 and 10 from the bottom (§sec:layer). Index `idx`
  names one one-time key on every layer, `K_l(idx) = (l, τ, e)`. The key of the bottom layer signs
  the FORS key, the key of each layer above the root of the tree below; the top tree's root is the
  public key's.
* A one-time key is WOTS+C (§sec:ots): `v = 64` chains of 4 positions, a codeword of digit sum
  `T = 128`, and the least counter `c < 2^32` whose encoding is a codeword.

Every hash input is `P ‖ A ‖ payload` (§sec:parameters, §sec:tweaks), `P` the 16-byte public
parameter and `A` the 16-byte address, whose layer and tree fields a hash of the hypertree fills.
The secret key is the seed `S0`; every secret derives from `S = H(leanSPHINCS ‖ S0)`. Key
generation builds the top tree. The message digest hashes `m ‖ ρ` (the root is not: `P` binds the
key), the randomizer `S ‖ m`.

**The signer** is the crate's, call for call (`sign`, `sign_with`, `scheme.rs:323-351`): the scheme
seed hashed again from the key's seed, the public parameter, the randomizer, the digest's two
calls, each FORS tree built once for its key and opening, then the layers from the bottom up, each
a one-time signature followed by its tree built once, whose root the layer above signs. So the hash
calls the end statement counts are the crate's.

Then the SUF-CMA game of `Statement/SufCma.lean` with that signer, and the end statement
`Sphincs.LeanSphincsStronglyUnforgeable`, proved by `Sphincs.leanSphincsStronglyUnforgeable`
(`lean_sphincs`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace Sphincs

open HashSig

/-! ### The instance: parameters, types, and hash-input layout -/

/-- The encoding counter's bits, `32` (`COUNTER_LEN`, `mod.rs:42`). -/
def counterBits : Nat := 32
/-- `v`, the chains of a one-time key, `64` (`V`, `mod.rs:50`). -/
def chainCount : Nat := 64
/-- `T`, the digit sum of a codeword, `128` (`TARGET_SUM`, `mod.rs:53`). -/
def targetSum : Nat := 128
/-- Encoding counters tried per one-time signature, `C_max` (`MAX_ENCODING_ATTEMPTS`,
`mod.rs:55`). -/
def encodingAttemptLimit : Nat := 2 ^ 32
/-- `d`, the layers of the hypertree, `3` (`LAYERS`, `mod.rs:59`). -/
def layerCount : Nat := 3
/-- `h`, the bits of an index, `8 + 8 + 10 = 26` (`H`, `mod.rs:63`). -/
def indexBits : Nat := 26
/-- `k`, the trees of a FORS instance, `24` (`FORS_TREES`, `mod.rs:67`). -/
def forsTreeCount : Nat := 24
/-- `a`, the height of a FORS tree, `10` (`FORS_HEIGHT`, `mod.rs:69`). -/
def forsTreeHeight : Nat := 10
/-- `N`, the signatures a key makes at most: the end statement's limit, `1,182,000,000`
(`doc/lean_sphincs` §sec:security; the crate's key is for `2^30`, §sec:sign). -/
def signatureLimit : Nat := 1182000000

/-- `l`, a layer of the hypertree, counted from the bottom. -/
abbrev Layer := Fin layerCount

instance : NeZero layerCount := ⟨by decide⟩

/-- `h_l`, the height of each tree of layer `l`: `8, 8, 10` from the bottom (`LAYER_HEIGHTS`,
`mod.rs:61`). -/
def layerHeight (layer : Layer) : Nat := if layer.val = 2 then 10 else 8

/-- The top layer, `d - 1`, whose single tree's root is the public key's. -/
def topLayer : Layer := ⟨2, by decide⟩

/-- `β_l = h_0 + ... + h_{l-1}`, the index bits below layer `l`. -/
def bitsBelowLayer (layer : Layer) : Nat := 8 * layer.val

/-- `idx`, an index: a bottom leaf, and the FORS instance it carries. -/
abbrev Index := Fin (2 ^ indexBits)
/-- `τ`, a tree of a layer. Layer `l` uses the values below `2^(h - β_l - h_l)`. -/
abbrev TreeIndex := Fin (2 ^ indexBits)
/-- `e`, a leaf of a tree. Layer `l` uses the values below `2^h_l`. -/
abbrev TreeLeafIndex := Fin (2 ^ layerHeight topLayer)
/-- `c`, the WOTS+C encoding counter. -/
abbrev EncodingCounter := BitVec counterBits
/-- `i`, a chain of a one-time key. -/
abbrev ChainIndex := Fin chainCount
/-- A pair of chains `(2t, 2t + 1)` of a one-time key, `t < 32`: one seed derivation. -/
abbrev ChainPairIndex := Fin 32
/-- The `v` digits a codeword assigns to the chains: how far each chain is opened. -/
abbrev Encoding := ChainIndex → WinternitzDigit

/-- `κ`, a tree of a FORS instance. -/
abbrev ForsTreeIndex := Fin forsTreeCount
/-- `s`, a leaf of a FORS tree, or a node index at any of its levels. -/
abbrev ForsLeafIndex := Fin (2 ^ forsTreeHeight)
/-- `p`, a pair of leaves `(2p, 2p + 1)` of a FORS tree: one seed derivation. -/
abbrev ForsLeafPairIndex := Fin (2 ^ (forsTreeHeight - 1))
/-- A hashed level `λ` of a FORS tree, `1 .. a - 1`, as `λ - 1` (`Fin forsTreeHeight` also names
level `a`, the root, which no algorithm hashes). -/
abbrev ForsLevel := Fin forsTreeHeight

/-- `K_l(idx)`'s tree, `⌊idx / 2^(β_l + h_l)⌋` (`OtsKey::of_index`, `wots.rs:25-33`). -/
def treeOfIndex (layer : Layer) (index : Index) : TreeIndex :=
  ⟨index.val / 2 ^ (bitsBelowLayer layer + layerHeight layer),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩

/-- `K_l(idx)`'s leaf, `⌊idx / 2^β_l⌋ mod 2^h_l` (`OtsKey::of_index`, `wots.rs:25-33`). -/
def leafOfIndex (layer : Layer) (index : Index) : TreeLeafIndex :=
  ⟨index.val / 2 ^ bitsBelowLayer layer % 2 ^ layerHeight layer,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (by unfold layerHeight topLayer; split <;> decide))⟩

/-! #### The message digest: two calls, `h + k a = 266` bits -/

/-- The bits of the digest a signature reads: the index, then a leaf per FORS tree (`DIGEST_BITS`,
`mod.rs:73`). -/
def messageDigestBits : Nat := indexBits + forsTreeCount * forsTreeHeight

/-- The Keccak-256 calls that give them, `⌈266 / 256⌉ = 2` (`DIGEST_CALLS`, `mod.rs:75`). -/
def digestCallCount : Nat := 2

/-- A digest call `c`, which its address carries. -/
abbrev DigestCall := Fin digestCallCount

instance : NeZero digestCallCount := ⟨by decide⟩

/-- The `266` bits a signature reads. -/
abbrev MessageDigest := BitVec messageDigestBits

/-- `D_0 ‖ D_1` as one little-endian number, call `0` in the low `256` bits. -/
def digestValue (outputs : DigestCall → HashOutput) : Nat :=
  ∑ call : DigestCall, (outputs call).toNat * 2 ^ (256 * call.val)

/-- The low `266` bits of the concatenated calls. -/
def truncateMessageDigest (outputs : DigestCall → HashOutput) : MessageDigest :=
  BitVec.ofNat messageDigestBits (digestValue outputs)

/-- `idx`, the low `h` bits of the digest (`digest_fields`, `scheme.rs:220-229`). -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 indexBits).toFin

/-- `s_κ`, the `a` bits of the digest from bit `h + a κ` (`digest_fields`, `scheme.rs:220-229`). -/
def digestForsLeaves (digest : MessageDigest) : ForsTreeIndex → ForsLeafIndex := fun tree =>
  (digest.extractLsb' (indexBits + forsTreeHeight * tree.val) forsTreeHeight).toFin

/-! #### Keys and signatures -/

/-- The FORS key of an instance: the two level-`(a - 1)` nodes of every tree, left first
(`ForsKey`, `fors.rs:30`). It is not hashed: the bottom one-time key's encoding absorbs the 48
nodes. -/
abbrev ForsKey := ForsTreeIndex → Digest × Digest

/-- One FORS tree's opening: the selected leaf's secret, and its path from the leaf up, the last
node being the other top node (`ForsTreeOpening`, `fors.rs:16-19`). -/
structure ForsTreeOpening where
  /-- The selected leaf's secret. -/
  secret : Digest
  /-- The siblings from the leaf up, the last the other level-`(a - 1)` node. -/
  path : Fin forsTreeHeight → Digest
deriving DecidableEq

/-- What a signature carries for layer `l`: the one-time signature of what the layer below gives
(`LayerSignature`, `scheme.rs:72-75`), and the key's authentication path in its tree, from the leaf
up (`LeanSphincsSignature::path`, `scheme.rs:112-115`). -/
structure LayerSignature (layer : Layer) where
  /-- The WOTS+C counter `c_l`. -/
  counter : EncodingCounter
  /-- Chain `i` opened to its codeword digit. -/
  chainValues : ChainIndex → Digest
  /-- The siblings from the key's leaf up to its tree's root. -/
  authenticationPath : Fin (layerHeight layer) → Digest
deriving DecidableEq

/-- The randomizer, the FORS opening, and each layer's one-time signature and path, bottom first:
7740 bytes (`LeanSphincsSignature`, `scheme.rs:88-95`; `SIG_SIZE`, `mod.rs:87-91`). -/
structure Signature where
  /-- The randomizer `ρ`. -/
  randomizer : Randomizer
  /-- The FORS opening, one per tree. -/
  forsOpening : ForsTreeIndex → ForsTreeOpening
  /-- Each layer's signature, bottom first. -/
  layers : (layer : Layer) → LayerSignature layer
deriving DecidableEq

/-! #### Addresses -/

/-- `κ + 64 position`, the `hi` field of a FORS call at a position of tree `κ`: a leaf, a pair of
leaves, or `level + 16 node` (`fors_hi`, `hash.rs:21-23`). -/
def forsHi (tree : ForsTreeIndex) (position : Nat) : Nat := tree.val + 64 * position

/-- The verification hash domains; seed derivations use `KeygenDomain`. A `forsNode` at `level` is
the node of FORS tree level `level + 1`: the scheme hashes levels 1 to `a - 1`. -/
inductive HashDomain where
  /-- Step `step` of chain `chainIndex` of the one-time key `(layer, tree, leaf)`. -/
  | chain (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex) (chainIndex : ChainIndex)
      (step : ChainStep)
  /-- The one-time key's leaf, the hash of its chain ends. -/
  | leaf (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
  /-- Node `nodeIndex` at height `level` of tree `tree` of layer `layer`. -/
  | node (layer : Layer) (tree : TreeIndex) (level : Nat) (nodeIndex : Nat)
  /-- The WOTS+C encoding of the one-time key `(layer, tree, leaf)`. -/
  | encoding (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
  /-- Leaf `forsLeaf` of FORS tree `forsTree` of instance `index`, the hash of its secret. -/
  | forsLeaf (index : Index) (forsTree : ForsTreeIndex) (forsLeaf : ForsLeafIndex)
  /-- Node `node` of FORS tree level `level + 1` of tree `forsTree` of instance `index`. -/
  | forsNode (index : Index) (forsTree : ForsTreeIndex) (level : ForsLevel) (node : ForsLeafIndex)
  /-- Digest call `call`. -/
  | message (call : DigestCall)
deriving DecidableEq

/-- The address of a hash domain (§sec:tweaks): `TWEAK_CHAIN = 1`, `TWEAK_LEAF = 2`,
`TWEAK_NODE = 3`, `TWEAK_ENC = 4`, `TWEAK_MSG = 12` (`tweak.rs:22-28`, `hash.rs:9`), the FORS
types `TWEAK_FORS_LEAF = 15` and `TWEAK_FORS_NODE = 17` (`hash.rs:11-12`). A one-time key puts its
layer and tree in their fields and its leaf in `lo` (`OtsKey::tweak`, `wots.rs:36-38`), a chain
step carries the step it leaves (`chain`, `wots.rs:53-57`), a node of the hypertree its height in
`hi` (`node`, `scheme.rs:258-264`); a FORS call has `idx` in `lo` and `forsHi` in `hi`
(`fors_leaf`, `fors_node`, `fors.rs:39-46`); a digest call has its number in `hi`
(`message_digest_bytes`, `scheme.rs:207-216`). -/
def hashDomainFields : HashDomain → TweakFields
  | .chain layer tree leaf chainIndex step =>
      (tweakFields 1 step chainIndex leaf).at layer tree
  | .leaf layer tree leaf => (tweakFields 2 0 0 leaf).at layer tree
  | .node layer tree level nodeIndex => (tweakFields 3 0 level nodeIndex).at layer tree
  | .encoding layer tree leaf => (tweakFields 4 0 0 leaf).at layer tree
  | .forsLeaf index forsTree forsLeaf => tweakFields 15 0 (forsHi forsTree forsLeaf) index
  | .forsNode index forsTree level node =>
      tweakFields 17 0 (forsHi forsTree (level.val + 1 + 16 * node.val)) index
  | .message call => tweakFields 12 0 call 0

/-- The pair of chains a chain of a one-time key belongs to. -/
def chainPair (chain : ChainIndex) : ChainPairIndex :=
  ⟨chain.val / 2, by have h : chain.val < 64 := chain.isLt; omega⟩

/-- The pair of leaves a FORS leaf belongs to. -/
def forsLeafPair (leaf : ForsLeafIndex) : ForsLeafPairIndex :=
  ⟨leaf.val / 2, by have h : leaf.val < 1024 := leaf.isLt; unfold forsTreeHeight; omega⟩

/-- The seed derivations, one hash of `S` each. `oneTimeChainPair` gives the starts of chains `2t`
and `2t + 1` of a one-time key, `forsSecretPair` the secrets of leaves `2p` and `2p + 1` of a FORS
tree: the two 16-byte halves of the hash. The parameter is the first 16 bytes of its hash. -/
inductive KeygenDomain where
  /-- The public parameter `P`. -/
  | parameter
  /-- The starts of chains `2t` and `2t + 1` of the one-time key `(layer, tree, leaf)`,
  `t = pair`. -/
  | oneTimeChainPair (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
      (pair : ChainPairIndex)
  /-- The secrets of leaves `2p` and `2p + 1` of FORS tree `forsTree` of instance `index`. -/
  | forsSecretPair (index : Index) (forsTree : ForsTreeIndex) (pair : ForsLeafPairIndex)
deriving DecidableEq

/-- `TWEAK_PARAMETER = 5` (`public_param`, `tweak.rs:135-137`), `TWEAK_PRF = 0` with the key's
layer, tree and leaf and the pair of chains in `hi` (`wots_secrets`, `wots.rs:43-49`),
`TWEAK_FORS_PRF = 14` with `idx` in `lo` and the tree and the pair of leaves in `hi`
(`secret_pair`, `fors.rs:34-36`). -/
def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0 0
  | .oneTimeChainPair layer tree leaf pair => (tweakFields 0 0 pair leaf).at layer tree
  | .forsSecretPair index forsTree pair => tweakFields 14 0 (forsHi forsTree pair) index

/-- `SEED_TAG`, the 11 ASCII bytes of `leanSPHINCS` (`mod.rs:31`). -/
def seedTag : HashInput := [0x6c, 0x65, 0x61, 0x6e, 0x53, 0x50, 0x48, 0x49, 0x4e, 0x43, 0x53]

/-! #### The target-sum code

`v = 64` chunks of `w = 2` bits covering the 128 digest bits, and the code is the words of digit sum
`T = 128` (`codeword`, `wots.rs:86-90`). -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
abbrev Valid (x : Encoding) : Prop := sum x = targetSum

/-- A digest decodes exactly when its 64 digits (`digestDigits`) reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if Valid (digestDigits digest) then some (digestDigits digest) else none

end TargetSum

/-! ### The algorithms, over a permutation `π` of the Keccak state in any monad -/

namespace Verification

open LeanVM.Semantics (KeccakState)
open HashSig.OverPermutation

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- The tweakable hash at a hash domain's address (`th`). -/
abbrev tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest :=
  th π parameter (hashDomainFields domain) payload

/-! #### The one-time signature -/

/-- A node index at height `0` read as a leaf. -/
def leafOfNat (value : Nat) : TreeLeafIndex :=
  ⟨value % 2 ^ layerHeight topLayer, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Chain `i` of the one-time key `(layer, tree, leaf)`: the step onto position `t + 1` carries
step `t` (`chain`, `wots.rs:53-57`: a step carries the position it leaves). -/
def chainWalk (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (chainIndex : ChainIndex) : Nat → Nat → Digest → m Digest :=
  walkChain fun step value ↦
    tweakableHash π parameter (.chain layer tree leaf chainIndex step) (littleEndianBytes 16 value)

/-- The verifier's half of a chain: walk the remaining `3 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (chainIndex : ChainIndex) (digit : WinternitzDigit) (value : Digest) :
    m Digest :=
  chainWalk π parameter layer tree leaf chainIndex digit.val (chainLength - 1 - digit.val) value

/-- The one-time leaf: the hash of the `v` chain ends (`wots_leaf_hash`, `wots.rs:60-62`). -/
def leafHash (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash π parameter (.leaf layer tree leaf) (digestsPayload endpoints)

/-- `Enc(P, K, M, c)` (`encode`, `wots.rs:80-82`): hash the message `M`, then the counter, under
the key's encoding address, and decode. The counter falls in the last block. -/
def encode (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (message : HashInput) (counter : EncodingCounter) : m (Option Encoding) := do
  let digest ← tweakableHash π parameter (.encoding layer tree leaf)
    (message ++ littleEndianBytes 4 counter)
  return TargetSum.decodeDigest digest

/-- `Ots.leaf` (`wots_leaf`, `wots.rs:106-119`): the leaf a claimed one-time signature of `M`
recovers, or nothing if the counter does not encode `M`. -/
def otsLeaf (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : HashInput) (counter : EncodingCounter)
    (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode π parameter layer tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIndex =>
    recoverChain π parameter layer tree leaf chainIndex (encoding chainIndex) (values chainIndex)
  let value ← leafHash π parameter layer tree leaf endpoints
  return some value

/-! #### The hypertree -/

/-- `Tree.fold` (`tree_fold`, `scheme.rs:355-368`): fold the key's leaf value and a path into its
tree's root. -/
def treeFold (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (path : Nat → Digest) : Nat → Digest → m Digest :=
  foldPath
    (fun level nodeIndex ↦ tweakableHash π parameter (.node layer tree (level + 1) nodeIndex))
    leaf.val path

/-! #### FORS -/

/-- A FORS leaf: the hash of its secret (`fors_leaf`, `fors.rs:39-41`). -/
def forsLeafHash (parameter : PublicParameter) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) (secret : Digest) : m Digest :=
  tweakableHash π parameter (.forsLeaf index forsTree leaf) (littleEndianBytes 16 secret)

/-- A node of a FORS tree: at height `level + 1 < a`, node `node` (`fors_node`, `fors.rs:44-46`;
`0` above). -/
def forsNodeHash (parameter : PublicParameter) (index : Index) (forsTree : ForsTreeIndex)
    (level node : Nat) (payload : HashInput) : m Digest :=
  if h : level < forsTreeHeight then
    tweakableHash π parameter (.forsNode index forsTree ⟨level, h⟩
      ⟨node % 2 ^ forsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) payload
  else pure 0

/-- Fold a FORS leaf and a path over `levels` levels. -/
def forsFold (parameter : PublicParameter) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) (path : Fin forsTreeHeight → Digest) : Nat → Digest → m Digest :=
  foldPath (forsNodeHash π parameter index forsTree) leaf.val
    fun level ↦ if h : level < forsTreeHeight then path ⟨level, h⟩ else 0

/-- The two top nodes of a tree in index order, from the one the fold reached and the last path
element: the reached node is the right one exactly when `bit`, the top bit of the leaf, is set
(`ordered`, `scheme.rs:253-255`). -/
def orderTops (bit : Bool) (current sibling : Digest) : Digest × Digest :=
  if bit then (sibling, current) else (current, sibling)

/-- The last level of a FORS path: the other level-`(a - 1)` node. -/
def forsTopLevel : Fin forsTreeHeight := ⟨forsTreeHeight - 1, by decide⟩

/-- The two top nodes of a FORS tree an opening reaches: the leaf hashed and folded `a - 1`
levels, ordered with the last path element. -/
def forsTreeRecover (parameter : PublicParameter) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) (opening : ForsTreeOpening) : m (Digest × Digest) := do
  let value ← forsLeafHash π parameter index forsTree leaf opening.secret
  let node ← forsFold π parameter index forsTree leaf opening.path (forsTreeHeight - 1) value
  return orderTops (leaf.val.testBit (forsTreeHeight - 1)) node (opening.path forsTopLevel)

/-- `Fts.recover` (`fors_recover`, `fors.rs:80-100`): the FORS key an opening reaches at the
digest's leaves. -/
def forsRecover (parameter : PublicParameter) (index : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    m ForsKey :=
  sequenceFin fun forsTree => forsTreeRecover π parameter index forsTree (leaves forsTree)
    (opening forsTree)

/-- The FORS key's 48 nodes as bytes, `t_0[0] ‖ t_0[1] ‖ ... ‖ t_23[1]`, 768 bytes: the bottom
one-time key's message (`fors_key_bytes`, `scheme.rs:315-317`). -/
def forsKeyPayload (key : ForsKey) : HashInput :=
  (List.ofFn key).flatMap fun pair => nodePayload pair.1 pair.2

/-! #### The message digest -/

/-- `m ‖ ρ`, what a digest call hashes after the parameter and the address: `P ‖ A ‖ m ‖ ρ` is 80
bytes, one block. The root is not hashed (`P` binds the key). -/
def messageDigestPayload (message : Message) (randomizer : Randomizer) : HashInput :=
  littleEndianBytes 32 message ++ littleEndianBytes 16 randomizer

/-- Digest call `c`, `D_c = H(P ‖ A_msg(c) ‖ m ‖ ρ)`, untruncated (`message_digest_bytes`,
`scheme.rs:207-216`). -/
def messageDigestCall (parameter : PublicParameter) (message : Message) (randomizer : Randomizer)
    (call : DigestCall) : m HashOutput :=
  thPair π parameter (hashDomainFields (.message call)) (messageDigestPayload message randomizer)

/-- `Digest(P, m, ρ) = D_0 ‖ D_1`, read to its first 266 bits (`message_digest`,
`scheme.rs:232-234`). -/
def messageDigest (parameter : PublicParameter) (message : Message) (randomizer : Randomizer) :
    m MessageDigest := do
  let outputs ← sequenceFin fun call => messageDigestCall π parameter message randomizer call
  return truncateMessageDigest outputs

/-! #### Verification -/

/-- Layer `l`'s path, read as a function of the level (`0` past its height). -/
def layerPath (signature : Signature) (layer : Layer) (level : Nat) : Digest :=
  if h : level < layerHeight layer then (signature.layers layer).authenticationPath ⟨level, h⟩
  else 0

/-- The walk up the hypertree, `layersLeft + 1` layers from the top: at layer
`l = d - 1 - layersLeft`, whose one-time key `K_l(idx)` signs `message` (the FORS key's bytes at
the bottom, the 16-byte root of the tree below above it), recover the one-time leaf and fold its
path; the top layer's root is the result (the loop of `verify`, `scheme.rs:380-385`). -/
def verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → HashInput → m (Option Digest)
  | 0, _ => pure none
  | layersLeft + 1, message => do
      if hlayer : layersLeft < layerCount then
        let layer : Layer := ⟨layerCount - 1 - layersLeft, by omega⟩
        let tree := treeOfIndex layer index
        let leaf := leafOfIndex layer index
        let some value ← otsLeaf π parameter layer tree leaf message
            (signature.layers layer).counter (signature.layers layer).chainValues
          | return none
        let root ← treeFold π parameter layer tree leaf (layerPath signature layer)
          (layerHeight layer) value
        if layersLeft = 0 then
          return some root
        else
          verifyLayers parameter index signature layersLeft (littleEndianBytes 16 root)
      else
        pure none

/-- `Ver(pk, m, σ)` (`verify`, `scheme.rs:371-391`): compute the digest, recover the FORS key,
walk the layers up (the one-time leaf, the path) and compare with the root. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest π publicKey.parameter message signature.randomizer
  let index := digestIndex digest
  let forsKey ← forsRecover π publicKey.parameter index (digestForsLeaves digest)
    signature.forsOpening
  let some root ← verifyLayers π publicKey.parameter index signature layerCount
      (forsKeyPayload forsKey)
    | return false
  return decide (root = publicKey.root)

end Verification

/-- **leanSPHINCS verification as deployed**: over Keccak-f[1600], the hash Keccak-256. -/
def verifyWithKeccak (publicKey : PublicKey) (message : Message) (signature : Signature) : Bool :=
  Id.run (Verification.verify (m := Id) LeanVM.Semantics.keccakF1600 publicKey message signature)

namespace KeyGenerationAndSigning

open Verification HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-! #### One-time keys and the hypertree -/

/-- `wots_secrets` (`wots.rs:43-49`): the starts of the 64 chains of the one-time key
`(layer, tree, leaf)`, from 32 seed derivations. Chains `2t` and `2t + 1` start at the two halves
of derivation `t`. -/
def otsSecrets (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let outputs ← sequenceFin fun pair : ChainPairIndex =>
    thPair π parameter (keygenDomainFields (.oneTimeChainPair layer tree leaf pair))
      (littleEndianBytes 32 seed)
  return fun chainIndex => hashHalfForChain chainIndex.val (outputs (chainPair chainIndex))

/-- The chain ends of a one-time key. -/
def oneTimePublicKey (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let secrets ← otsSecrets π parameter layer tree leaf seed
  sequenceFin fun chainIndex =>
    chainWalk π parameter layer tree leaf chainIndex 0 (chainLength - 1) (secrets chainIndex)

/-- The encoding counters `counter, counter + 1, ...`, at most `attempts` of them, stopping at the
first that encodes the message. -/
def otsSignFrom (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (seed : MasterSeed) (message : HashInput) :
    Nat → Nat → m (Option (EncodingCounter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode π parameter layer tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let secrets ← otsSecrets π parameter layer tree leaf seed
          let values ← sequenceFin fun chainIndex =>
            chainWalk π parameter layer tree leaf chainIndex 0 (encoding chainIndex).val
              (secrets chainIndex)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter layer tree leaf seed message attempts (counter + 1)

/-- `Ots.sign` (`wots_sign`, `wots.rs:96-102`): the least admissible counter, then the opened
chain values. -/
def otsSign (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (seed : MasterSeed) (message : HashInput) :
    m (Option (EncodingCounter × (ChainIndex → Digest))) :=
  otsSignFrom π parameter layer tree leaf seed message encodingAttemptLimit 0

/-- Node `nodeIndex` at height `level` of tree `tree` of layer `layer`, computed from the one-time
keys below it (`tree_levels`, `scheme.rs:267-280`, `wots_public_leaf`, `wots.rs:123-127`). -/
def treeNode (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex) (seed : MasterSeed) :
    Nat → Nat → m Digest :=
  buildTree (fun nodeIndex ↦ do
      leafHash π parameter layer tree (leafOfNat nodeIndex)
        (← oneTimePublicKey π parameter layer tree (leafOfNat nodeIndex) seed))
    fun level nodeIndex ↦ tweakableHash π parameter (.node layer tree (level + 1) nodeIndex)

/-- Tree `tree` of layer `layer`, built once (`tree_levels`, `scheme.rs:267-280`): node `nodeIndex`
at height `level`, and the siblings of the path of the key at `leaf` below it. The crate builds the
tree level by level and reads the root and the path from its levels (`sign_with`,
`scheme.rs:339-342`); here it is built depth first: the same hash calls, each node once. -/
def treeNodeWithPath (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : TreeLeafIndex) : Nat → Nat → m (Digest × (Nat → Digest)) :=
  buildTreeWithPath (fun nodeIndex ↦ do
      leafHash π parameter layer tree (leafOfNat nodeIndex)
        (← oneTimePublicKey π parameter layer tree (leafOfNat nodeIndex) seed))
    (fun level nodeIndex ↦ tweakableHash π parameter (.node layer tree (level + 1) nodeIndex))
    leaf.val

/-! #### FORS -/

/-- Node `node` at height `height + 1` of FORS tree `forsTree` of instance `index`, built once
(`fors_open`, `fors.rs:50-76`), with the secret of the leaf `leaf` and the siblings of its path
below it (`path l` the sibling at height `l ≤ height`), for a node above `leaf`. A height-1 node
derives its pair of leaves once: the two halves of the hash are their secrets (`secret_pair`,
`fors.rs:34-36`). The crate builds the tree level by level; here it is built depth first, the
same hash calls. -/
def forsSubtree (parameter : PublicParameter) (index : Index) (forsTree : ForsTreeIndex)
    (seed : MasterSeed) (leaf : ForsLeafIndex) : Nat → Nat → m (Digest × Digest × (Nat → Digest))
  | 0, node => do
      let left : ForsLeafIndex := ⟨2 * node % 2 ^ forsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let right : ForsLeafIndex :=
        ⟨(2 * node + 1) % 2 ^ forsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let output ← thPair π parameter (keygenDomainFields (.forsSecretPair index forsTree
        (forsLeafPair left))) (littleEndianBytes 32 seed)
      let leftLeaf ← forsLeafHash π parameter index forsTree left (hashHalfForChain 0 output)
      let rightLeaf ← forsLeafHash π parameter index forsTree right (hashHalfForChain 1 output)
      let value ← tweakableHash π parameter (.forsNode index forsTree ⟨0, by decide⟩
        ⟨node % 2 ^ forsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
        (nodePayload leftLeaf rightLeaf)
      return (value, hashHalfForChain leaf.val output,
        fun _ ↦ if leaf.val.testBit 0 then leftLeaf else rightLeaf)
  | height + 1, node => do
      let left ← forsSubtree parameter index forsTree seed leaf height (2 * node)
      let right ← forsSubtree parameter index forsTree seed leaf height (2 * node + 1)
      let value ← (if hheight : height + 1 < forsTreeHeight then
          tweakableHash π parameter (.forsNode index forsTree ⟨height + 1, hheight⟩
            ⟨node % 2 ^ forsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
            (nodePayload left.1 right.1)
        else pure 0)
      return (value, if leaf.val.testBit (height + 1) then right.2.1 else left.2.1,
        if leaf.val.testBit (height + 1) then Function.update right.2.2 (height + 1) left.1
        else Function.update left.2.2 (height + 1) right.1)

/-- FORS tree `forsTree` of instance `index`, built once: its two level-`(a - 1)` nodes, the FORS
key's pair, and its opening at `leaf`, whose last path element is the other of the two
(`fors_open`, `fors.rs:50-76`). -/
def forsTreeOpen (parameter : PublicParameter) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) (seed : MasterSeed) : m ((Digest × Digest) × ForsTreeOpening) := do
  let left ← forsSubtree π parameter index forsTree seed leaf (forsTreeHeight - 2) 0
  let right ← forsSubtree π parameter index forsTree seed leaf (forsTreeHeight - 2) 1
  let top := forsTreeHeight - 1
  let path := if leaf.val.testBit top then Function.update right.2.2 top left.1
    else Function.update left.2.2 top right.1
  return ((left.1, right.1),
    ⟨if leaf.val.testBit top then right.2.1 else left.2.1, fun level ↦ path level.val⟩)

/-- `Fts.key` and `Fts.sign` together (`fors_open`, `fors.rs:50-76`): every tree of instance
`index` built once, the FORS key and the opening at the digest's leaves. -/
def forsOpen (parameter : PublicParameter) (index : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (seed : MasterSeed) :
    m (ForsKey × (ForsTreeIndex → ForsTreeOpening)) := do
  let trees ← sequenceFin fun forsTree =>
    forsTreeOpen π parameter index forsTree (leaves forsTree) seed
  return (fun forsTree => (trees forsTree).1, fun forsTree => (trees forsTree).2)

/-! #### Key generation and signing -/

/-- The public key of the scheme seed `S` (`public_key_of`, `scheme.rs:290-297`): the public
parameter (`public_param`, `tweak.rs:135-137`) and the root of the top tree. -/
def publicKeyOf (schemeSeed : MasterSeed) : m PublicKey := do
  let parameter ← th π 0 (keygenDomainFields .parameter) (littleEndianBytes 32 schemeSeed)
  let root ← treeNode π parameter topLayer 0 schemeSeed (layerHeight topLayer) 0
  return ⟨root, parameter⟩

/-- `Gen` (`key_gen_from_seed`, `scheme.rs:284-286`): the secret key is the seed `S0`, the public
key that of the scheme seed `S = H(leanSPHINCS ‖ S0)` (`scheme_seed`, `hash.rs:15-17`). -/
def keygenFromSeed (masterSeed : MasterSeed) : m (PublicKey × SecretKey) := do
  let schemeSeed ← taggedSeed π seedTag masterSeed
  let publicKey ← publicKeyOf π schemeSeed
  return (publicKey, masterSeed)

/-- Layer `l`'s one-time signature of `message` with `K_l(idx)` (`wots_sign`), then the key's tree,
built once: the layer's signature with the key's path, and the tree's root, which the layer above
signs (the loop of `sign_with`, `scheme.rs:336-344`). -/
def signLayer (parameter : PublicParameter) (schemeSeed : MasterSeed) (index : Index)
    (layer : Layer) (message : HashInput) : m (Option (LayerSignature layer × Digest)) := do
  let tree := treeOfIndex layer index
  let leaf := leafOfIndex layer index
  let some (counter, values) ← otsSign π parameter layer tree leaf schemeSeed message
    | return none
  let built ← treeNodeWithPath π parameter layer tree schemeSeed leaf (layerHeight layer) 0
  return some (⟨counter, values, fun level ↦ built.2 level.val⟩, built.1)

/-- The three layers' signatures, bottom first. -/
def layerSignatures (bottom : LayerSignature 0) (middle : LayerSignature 1)
    (top : LayerSignature 2) : (layer : Layer) → LayerSignature layer
  | ⟨0, _⟩ => bottom
  | ⟨1, _⟩ => middle
  | ⟨2, _⟩ => top
  | ⟨_ + 3, h⟩ => absurd h (by unfold layerCount; omega)

/-- `sign_with` (`scheme.rs:329-351`), with the scheme seed `S`: the public parameter, the
randomizer `ρ = Th(P, A_rnd, S ‖ m)` (`randomizer`, `scheme.rs:306-312`), the digest's index and
leaves, the FORS instance built once (its key and its opening), then the layers from the bottom up,
each signing what the layer below gives: the FORS key's bytes at the bottom (`fors_key_bytes`), the
root of the tree below above it. -/
def signWithSchemeSeed (schemeSeed : MasterSeed) (message : Message) : m (Option Signature) := do
  let parameter ← th π 0 (keygenDomainFields .parameter) (littleEndianBytes 32 schemeSeed)
  let randomizer ← th π parameter (tweakFields 7 0 0 0)
    (littleEndianBytes 32 schemeSeed ++ littleEndianBytes 32 message)
  let digest ← messageDigest π parameter message randomizer
  let index := digestIndex digest
  let fors ← forsOpen π parameter index (digestForsLeaves digest) schemeSeed
  let some (bottom, bottomRoot) ← signLayer π parameter schemeSeed index 0 (forsKeyPayload fors.1)
    | return none
  let some (middle, middleRoot) ←
      signLayer π parameter schemeSeed index 1 (littleEndianBytes 16 bottomRoot)
    | return none
  let some (top, _) ← signLayer π parameter schemeSeed index 2 (littleEndianBytes 16 middleRoot)
    | return none
  return some ⟨randomizer, fors.2, layerSignatures bottom middle top⟩

/-- `Sign` (`sign`, `scheme.rs:323-325`): the scheme seed `S = H(leanSPHINCS ‖ S0)` of the key's
seed (`scheme_seed`, `hash.rs:15-17`), then `sign_with`. -/
def sign (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  let schemeSeed ← taggedSeed π seedTag secretKey
  signWithSchemeSeed π schemeSeed message

end KeyGenerationAndSigning

/-! ## Forgeries and transcripts -/

/-- A claimed forgery: a message and a signature. -/
structure Forgery where
  /-- The message. -/
  message : Message
  /-- Its claimed signature. -/
  signature : Signature
deriving DecidableEq

/-- The signing oracle answers a message with a signature, or `none` if the signer fails. -/
abbrev SigningOracleSpec := Message →ₒ Option Signature

namespace SigningTranscript

/-- A transcript is valid when it has at most `signatureLimit` requests. -/
abbrev WithinSignatureLimit (log : QueryLog SigningOracleSpec) : Prop :=
  log.length ≤ signatureLimit

end SigningTranscript

/-! ## Security in the random-permutation model -/

namespace RandomPermutationModel

open Common Common.SufCma

/-- leanSPHINCS in the generic SUF-CMA game, over `π` (`queryPermutation`): the seed, key
generation, the deterministic signer, the verifier, and the winning condition: a valid transcript
without the forgery (`SignerReturnedForgery`). -/
noncomputable def sufCmaScheme :
    Scheme MasterSeed PublicKey SecretKey Message (Option Signature) Forgery where
  sampleSeed := sampleMasterSeed
  generateKeys := KeyGenerationAndSigning.keygenFromSeed queryPermutation
  sign sk message := KeyGenerationAndSigning.sign queryPermutation sk message
  verify pk forgery := Verification.verify queryPermutation pk forgery.message forgery.signature
  winningCondition log forgery :=
    decide (SigningTranscript.WithinSignatureLimit log ∧ ¬SignerReturnedForgery id log
        forgery.message forgery.signature)

end RandomPermutationModel

/-! ### The end statement -/

section EndStatement

open Common.SufCma

/-- **leanSPHINCS in the random-permutation model**: up to `N = 1,182,000,000` signatures, an
adversary whose game makes at most `Q` permutation calls, `Q ≥ 1`, forges with probability at most
`(Q + 1) · 2^-127` (`StronglyUnforgeable` at 127 bits). `Q` counts every call on the game's worst
path, the honest signer's included (`QueryCostAtMost` is structural): a signature costs about
`2^19` permutations in expectation, but on the worst path `2^35` (`2^32` encoding counters on each
of three layers, the bottom one's encoding 6 permutations long), so at `N ≈ 2^30.1` signatures
`Q ≥ 2^65` and the bound is about `2^-62`. Proved by `Sphincs.leanSphincsStronglyUnforgeable`. A
key past its signature limit, which the signer does not count, is not covered: keeping within it is
the key holder's duty. -/
abbrev LeanSphincsStronglyUnforgeable : Prop :=
  StronglyUnforgeable RandomPermutationModel.sufCmaScheme 127

end EndStatement

end Sphincs

end
