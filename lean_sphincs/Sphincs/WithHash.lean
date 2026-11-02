module

public import Statement.LeanSphincs
public import Common.WithHash

/-!
# leanSPHINCS with a hash oracle

The statement's leanSPHINCS (`Statement/LeanSphincs.lean`) hashes with Keccak-256 over the
permutation `π`. The proofs reason with the hash a query of its own (`LeanXmss.HashSpec`): these are
its algorithms in that form, each the statement's definition with the hash a query, and the scheme
in the hash-query SUF-CMA game (`Sphincs.RandomPermutationModel.schemeWithHash`).
`Sphincs.WithHashBridge` proves the
statement's these with the hash Keccak-256 over `π`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace Sphincs

export LeanXmss (HashSpec)

namespace Verification

export LeanXmss.Verification (oracleHashWithHash thWithHash thPairWithHash taggedSeedWithHash)

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The tweakable hash at a hash domain's address (`th`). -/
abbrev tweakableHashWithHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    m Digest :=
  thWithHash parameter (hashDomainFields domain) payload

/-- Chain `i` of the one-time key at a leaf: the step onto position `t + 1` carries step `t`
(`chain`, `wots.rs`: a step carries the position it leaves). -/
def chainWalkWithHash (parameter : PublicParameter) (leaf : LeafIndex) (chainIdx : ChainIndex) :
    Nat → Nat → Digest → m Digest :=
  walkChain fun step value ↦
    tweakableHashWithHash parameter (.chain leaf chainIdx step) (littleEndianBytes 16 value)

/-- The verifier's half of a chain: walk the remaining `3 - x_i` steps. -/
def recoverChainWithHash (parameter : PublicParameter) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (digit : WinternitzDigit) (value : Digest) : m Digest :=
  chainWalkWithHash parameter leaf chainIdx digit.val (chainLength - 1 - digit.val) value

/-- The one-time leaf: the hash of the `v` chain ends (`wots_leaf_hash`). -/
def leafHashWithHash (parameter : PublicParameter) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    m Digest :=
  tweakableHashWithHash parameter (.leaf leaf) (leafPayload endpoints)

/-- `Enc(P, e, K, c)`: hash the forest key's sixteen nodes, then the counter, under the leaf's
encoding tweak, and decode. There is no forest-key hash: the counter falls in the last block of this
one (`P || A || K || c`, 292 bytes). -/
def encodeWithHash (parameter : PublicParameter) (leaf : LeafIndex) (message : ForestKey)
    (counter : EncodingCounter) :
    m (Option Encoding) := do
  let digest ← tweakableHashWithHash parameter (.encoding leaf)
    (forestKeyPayload message ++ littleEndianBytes 4 counter)
  return TargetSum.decodeDigest digest

/-- `Ots.leaf` (`wots_leaf`, `wots.rs`): the verifier's leaf, or nothing if the counter does not
encode the message. -/
def otsLeafWithHash (parameter : PublicParameter) (leaf : LeafIndex) (message : ForestKey)
    (counter : EncodingCounter)
    (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encodeWithHash parameter leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChainWithHash parameter leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHashWithHash parameter leaf endpoints
  return some value

/-- `Tree.fold` (`tree_fold`): fold a leaf and a path into the root. -/
def treeFoldWithHash (parameter : PublicParameter) (leaf : LeafIndex) (path : Nat → Digest) :
    Nat → Digest → m Digest :=
  foldPath (fun level nodeIdx ↦ tweakableHashWithHash parameter (.node (level + 1) nodeIdx))
    leaf.val path

/-- Forest chain `i` of a child; the step onto position `t + 1` carries step `t`. -/
def forestWalkWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
    (j : SubtreeIndex)
    (a : ChildIndex) (i : ForestChainIndex) : Nat → Nat → Digest → m Digest :=
  walkChain fun step value ↦
    tweakableHashWithHash parameter (.forestChain index c s j a i step) (littleEndianBytes 16 value)

/-- The verifier's half of a forest chain: from position `4 - d` walk `d` steps. -/
def forestRecoverChainWithHash (parameter : PublicParameter) (index : LeafIndex) (c :
    ForestCoordinate)
    (s : SuperChildIndex) (j : SubtreeIndex)
    (a : ChildIndex) (i : ForestChainIndex) (deficit : ForestChainPosition) (value : Digest) : m Digest :=
  forestWalkWithHash parameter index c s j a i (forestChainTop - deficit.val) deficit.val value

/-- The child leaf: the hash of the 6 chain tops. -/
def childLeafHashWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
    (j : SubtreeIndex)
    (a : ChildIndex) (ends : ForestChainIndex → Digest) : m Digest :=
  tweakableHashWithHash parameter (.childLeaf index c s j a) (childPayload ends)

/-- The child leaf an opening at codeword `word` reaches. -/
def childRecoverWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
    (j : SubtreeIndex)
    (a : ChildIndex) (word : Codeword) (values : ForestChainIndex → Digest) : m Digest := do
  let ends ← sequenceFin fun i =>
    forestRecoverChainWithHash parameter index c s j a i (word i) (values i)
  childLeafHashWithHash parameter index c s j a ends

/-- The node hash of a sub-tree: at level `l + 1 ≤ 3`, node `i < 8` (`0` above). -/
def subNodeHashWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
    (j : SubtreeIndex) (level node : Nat) (payload : HashInput) : m Digest :=
  if h : level < forestSubtreeHeight then
    tweakableHashWithHash parameter (.subtreeNode index c s j ⟨level, h⟩
      ⟨node % 2 ^ forestSubtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) payload
  else pure 0

/-- Fold a child leaf and a sub-tree path into the sub-tree root. -/
def subFoldWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
    (j : SubtreeIndex)
    (a : ChildIndex) (path : Fin forestSubtreeHeight → Digest) : Nat → Digest → m Digest :=
  foldPath (subNodeHashWithHash parameter index c s j) a.val
    fun level ↦ if h : level < forestSubtreeHeight then path ⟨level, h⟩ else 0

/-- The super-child `Th(super(idx, c, s), m_0[0] || m_0[1] || m_1[0] || m_1[1])`: the hash of the
two level-2 nodes of each of its sub-trees. A sub-tree has no root hash. -/
def superHashWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
    (tops : SubtreeIndex → Digest × Digest) : m Digest :=
  tweakableHashWithHash parameter (.superChild index c s) (superChildPayload tops)

/-- The node hash of a coordinate's top tree: at level `l + 1 ≤ 4`, node `i < 16` (`0` above). -/
def topNodeHashWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (level node : Nat)
    (payload : HashInput) : m Digest :=
  if h : level < topTreeHeight then
    tweakableHashWithHash parameter (.topTreeNode index c ⟨level, h⟩
      ⟨node % 2 ^ topTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) payload
  else pure 0

/-- Fold a super-child and a top path into the coordinate root. -/
def topFoldWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
    (path : Fin topTreeHeight → Digest) : Nat → Digest → m Digest :=
  foldPath (topNodeHashWithHash parameter index c) s.val
    fun level ↦ if h : level < topTreeHeight then path ⟨level, h⟩ else 0

/-- The two level-3 nodes of a coordinate's top tree that an opening reaches. In each sub-tree the
child leaf is folded 2 levels and the last path element is the other level-2 node; the four level-2
nodes hash into the super-child, which is folded 3 levels, and the last top path element is the
other level-3 node. -/
def coordRecoverWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate)
    (mark : CoordinateSelection)
    (opening : CoordinateOpening) : m (Digest × Digest) := do
  let tops ← sequenceFin fun j => do
    let leaf ← childRecoverWithHash parameter index c mark.superChild j (mark.child j)
      (lut (mark.codewordIndex j))
      (opening.subtreeOpenings j).values
    let node ← subFoldWithHash parameter index c mark.superChild j (mark.child j)
        (opening.subtreeOpenings j).path
      (forestSubtreeHeight - 1) leaf
    return orderTops ((mark.child j).val.testBit (forestSubtreeHeight - 1)) node
      ((opening.subtreeOpenings j).path subtreePathLastLevel)
  let super ← superHashWithHash parameter index c mark.superChild tops
  let node ← topFoldWithHash parameter index c mark.superChild opening.topTreePath (topTreeHeight -
      1) super
  return orderTops (mark.superChild.val.testBit (topTreeHeight - 1)) node (opening.topTreePath
      topTreePathLastLevel)

/-- `Fts.recover`: the forest key an opening reaches, the sixteen level-3 nodes. A top tree has no
root hash, and the key has no hash: the WOTS+C encoding absorbs it. -/
def forestRecoverWithHash (parameter : PublicParameter) (index : LeafIndex) (marks : ForestCoordinate → CoordinateSelection)
    (opening : ForestCoordinate → CoordinateOpening) : m ForestKey :=
  sequenceFin fun c => coordRecoverWithHash parameter index c (marks c) (opening c)

/-- The single untruncated digest call (`message_digest_bytes`, `scheme.rs`). -/
def messageDigestCallWithHash (parameter : PublicParameter) (message : Message)
    (randomness : Randomizer) : m HashOutput :=
  thPairWithHash parameter (hashDomainFields .message) (messageDigestPayload message randomness)

/-- `Digest(P, m, rho)` (`message_digest`): the single call, truncated to 234 bits. -/
def messageDigestWithHash (parameter : PublicParameter) (message : Message)
    (randomness : Randomizer) : m MessageDigest := do
  let first ← messageDigestCallWithHash parameter message randomness
  return truncateMessageDigest first

/-- `Ver(pk, m, sigma)` (`verify`, `scheme.rs`): recompute the digest, recover the forest key,
recover the one-time leaf at `e = idx`, fold the path and compare with the root. -/
def verifyWithHash (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool :=
  do
  let digest ← messageDigestWithHash publicKey.parameter message signature.randomizer
  let index := digestLeafIndex digest
  let forestKeyWithHash ← forestRecoverWithHash publicKey.parameter index
    (digestCoordinateSelections digest) signature.forestOpening
  let some leaf ← otsLeafWithHash publicKey.parameter index forestKeyWithHash signature.counter
    signature.chainValues | return false
  let root ← treeFoldWithHash publicKey.parameter index
    (fun level ↦ if h : level < treeHeight
        then signature.authenticationPath ⟨level, h⟩ else 0) treeHeight leaf
  return decide (root = publicKey.root)

end Verification

namespace KeyGenerationAndSigning

open Verification

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `wots_secrets`: the starts of the 64 chains of the one-time key at a leaf, from 32 seed
derivations. Chains `2t` and `2t + 1` start at the two halves of derivation `t`. -/
def otsSecretsWithHash (parameter : PublicParameter) (leaf : LeafIndex) (seed : MasterSeed) :
    m (ChainIndex → Digest) := do
  let outputs ← sequenceFin fun pair : ChainPairIndex =>
    thPairWithHash parameter (keygenDomainFields (.oneTimeChainPair leaf pair)) (littleEndianBytes
        32 seed)
  return fun chainIdx => hashHalfForChain chainIdx.val (outputs (chainPair chainIdx))

def oneTimePublicKeyWithHash (parameter : PublicParameter) (leaf : LeafIndex) (seed : MasterSeed) :
    m (ChainIndex → Digest) := do
  let secrets ← otsSecretsWithHash parameter leaf seed
  sequenceFin fun chainIdx =>
    chainWalkWithHash parameter leaf chainIdx 0 (chainLength - 1) (secrets chainIdx)

def otsSignFromWithHash (parameter : PublicParameter) (leaf : LeafIndex) (seed : MasterSeed)
    (message : ForestKey) : Nat → Nat → m (Option (EncodingCounter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encodeWithHash parameter leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let secrets ← otsSecretsWithHash parameter leaf seed
          let values ← sequenceFin fun chainIdx =>
            chainWalkWithHash parameter leaf chainIdx 0 (encoding chainIdx).val (secrets chainIdx)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFromWithHash parameter leaf seed message attempts (counter + 1)

/-- `wots_sign`: the least admissible counter, then the opened chain values. -/
def otsSignWithHash (parameter : PublicParameter) (leaf : LeafIndex) (seed : MasterSeed)
    (message : ForestKey) :
    m (Option (EncodingCounter × (ChainIndex → Digest))) :=
  otsSignFromWithHash parameter leaf seed message encodingAttemptLimit 0

/-- A node of the tree, computed from the one-time keys below it. -/
def treeNodeWithHash (parameter : PublicParameter) (seed : MasterSeed) : Nat → Nat → m Digest :=
  buildTree (fun nodeIdx ↦ do
      leafHashWithHash parameter (leafOfNat nodeIdx)
        (← oneTimePublicKeyWithHash parameter (leafOfNat nodeIdx) seed))
    fun level nodeIdx ↦ tweakableHashWithHash parameter (.node (level + 1) nodeIdx)

/-- The starts `x_{i,0}` of the 6 chains of a child, from 3 seed derivations. Chains `2t` and
`2t + 1` start at the two halves of derivation `t`. -/
def forestSecretsWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
    (j : SubtreeIndex) (a : ChildIndex) (seed : MasterSeed) : m (ForestChainIndex → Digest) := do
  let outputs ← sequenceFin fun pair : ForestChainPairIndex =>
    thPairWithHash parameter (keygenDomainFields (.childChainPair index c s j a pair))
        (littleEndianBytes 32 seed)
  return fun i => hashHalfForChain i.val (outputs (forestChainPair i))

/-- The leaf of a child, from its 6 chain tops. -/
def childLeafWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
    (j : SubtreeIndex)
    (a : ChildIndex) (seed : MasterSeed) : m Digest := do
  let secrets ← forestSecretsWithHash parameter index c s j a seed
  let ends ← sequenceFin fun i =>
    forestWalkWithHash parameter index c s j a i 0 forestChainTop (secrets i)
  childLeafHashWithHash parameter index c s j a ends

/-- A node of a sub-tree at tree level `level`. -/
def subNodeWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
    (j : SubtreeIndex)
    (seed : MasterSeed) : Nat → Nat → m Digest :=
  buildTree (fun node ↦ childLeafWithHash parameter index c s j
      ⟨node % 2 ^ forestSubtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ seed)
    (subNodeHashWithHash parameter index c s j)

/-- A super-child, from the two level-2 nodes of each of its two sub-trees. -/
def superNodeWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
    (seed : MasterSeed) : m Digest := do
  let tops ← sequenceFin fun j => do
    let left ← subNodeWithHash parameter index c s j seed (forestSubtreeHeight - 1) 0
    let right ← subNodeWithHash parameter index c s j seed (forestSubtreeHeight - 1) 1
    return (left, right)
  superHashWithHash parameter index c s tops

/-- A node of a coordinate's top tree at tree level `level`. -/
def topNodeWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (seed : MasterSeed) :
    Nat → Nat → m Digest :=
  buildTree (fun node ↦ superNodeWithHash parameter index c
      ⟨node % 2 ^ topTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ seed)
    (topNodeHashWithHash parameter index c)

/-- The forest key of instance `idx`: the two level-3 nodes of every coordinate (no hash). -/
def forestKeyWithHash (parameter : PublicParameter) (index : LeafIndex) (seed : MasterSeed) :
    m ForestKey :=
  sequenceFin fun c => do
    let left ← topNodeWithHash parameter index c seed (topTreeHeight - 1) 0
    let right ← topNodeWithHash parameter index c seed (topTreeHeight - 1) 1
    return (left, right)

/-- The opening of one coordinate at a mark. The last element of each path (level 2 of a sub-tree,
level 3 of the top tree) is the top node the verifier does not compute. -/
def coordOpenWithHash (parameter : PublicParameter) (index : LeafIndex) (c : ForestCoordinate) (mark : CoordinateSelection)
    (seed : MasterSeed) : m CoordinateOpening := do
  let sub ← sequenceFin fun j => do
    let secrets ← forestSecretsWithHash parameter index c mark.superChild j (mark.child j) seed
    let values ← sequenceFin fun i =>
      forestWalkWithHash parameter index c mark.superChild j (mark.child j) i 0
        (forestChainTop - (lut (mark.codewordIndex j) i).val) (secrets i)
    let path ← sequenceFin fun level : Fin forestSubtreeHeight =>
      subNodeWithHash parameter index c mark.superChild j seed level.val
        (Nat.xor ((mark.child j).val / 2 ^ level.val) 1)
    return (⟨values, path⟩ : SubtreeOpening)
  let top ← sequenceFin fun level : Fin topTreeHeight =>
    topNodeWithHash parameter index c seed level.val (Nat.xor (mark.superChild.val / 2 ^
        level.val) 1)
  return ⟨sub, top⟩

/-- `Fts.sign`: the opening of every coordinate. -/
def forestOpenWithHash (parameter : PublicParameter) (index : LeafIndex) (marks : ForestCoordinate → CoordinateSelection)
    (seed : MasterSeed) : m (ForestCoordinate → CoordinateOpening) :=
  sequenceFin fun c => coordOpenWithHash parameter index c (marks c) seed

variable [KeyShape]

/-- The surrogate sibling at `level >= b`, derived from the seed (`TWEAK_SURROGATE`). Honest calls
have `level < h`. -/
def surrogateWithHash (parameter : PublicParameter) (seed : MasterSeed) (level : Nat) : m Digest :=
  if hlevel :
    level < treeHeight then thWithHash parameter (keygenDomainFields (.surrogate ⟨level, hlevel⟩))
      (littleEndianBytes 32 seed)
  else pure 0

/-- The node at level `b + steps` above the kept subtree: the subtree root folded with the first
`steps` surrogates (the surrogate fold of `key_gen_from_seed`, `scheme.rs`). -/
def spineNodeWithHash (parameter : PublicParameter) (seed : MasterSeed) : Nat → m Digest
  | 0 => treeNodeWithHash parameter seed keptSubtreeHeight (keptSubtreePosition parameter)
  | steps + 1 => do
      let below ← spineNodeWithHash parameter seed steps
      let sibling ← surrogateWithHash parameter seed (keptSubtreeHeight + steps)
      let nodeIdx := keptSubtreePosition parameter / 2 ^ steps
      if nodeIdx.testBit 0 then
        tweakableHashWithHash parameter (.node (keptSubtreeHeight + steps + 1) (nodeIdx / 2))
          (nodePayload sibling below)
      else
        tweakableHashWithHash parameter (.node (keptSubtreeHeight + steps + 1) (nodeIdx / 2))
          (nodePayload below sibling)

/-- The root: the spine's top. -/
def treeRootWithHash (parameter : PublicParameter) (seed : MasterSeed) : m Digest :=
  spineNodeWithHash parameter seed (treeHeight - keptSubtreeHeight)

/-- The authentication path of a kept leaf (`LeanSphincsSecretKey::path`, `scheme.rs`): subtree
nodes below level `b`, surrogates from level `b` on. -/
def treePathWithHash (parameter : PublicParameter) (seed : MasterSeed) (leaf : LeafIndex) :
    m (Fin treeHeight → Digest) :=
  sequenceFin fun level =>
    if level.val < keptSubtreeHeight then
      treeNodeWithHash parameter seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      surrogateWithHash parameter seed level.val

/-- Key generation from the scheme seed `S`: derive the public parameter, which places the kept
subtree, and build the root. -/
def keygenFromMasterWithHash (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let parameter ← thWithHash 0 (keygenDomainFields .parameter) (littleEndianBytes 32 seed)
  let root ← treeRootWithHash parameter seed
  return (⟨root, parameter⟩, ⟨seed, parameter⟩)

/-- `Gen` (`key_gen_from_seed`): hash the key's seed `S0` into the scheme seed `S`, then generate
from `S`. -/
def keygenFromSeedWithHash (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let master ← taggedSeedWithHash seedTag seed
  keygenFromMasterWithHash master

/-- One grinding attempt: the leaf index of the digest call (the `find_map` of `sign`,
`scheme.rs`). -/
def signAttemptWithHash (secretKey : SecretKey) (message : Message) (randomness : Randomizer) :
    m (Option LeafIndex) := do
  let first ← messageDigestCallWithHash secretKey.parameter message randomness
  if LandsInKeptSubtree secretKey.parameter (digestLeafIndex (truncateMessageDigest first)) then
    return some (digestLeafIndex (truncateMessageDigest first))
  else
    return none

/-- Try `randomness, randomness + 1, ...`, stopping at the first that lands in the kept subtree. -/
def signDigestLoopWithHash (secretKey : SecretKey) (message : Message) : Nat → Randomizer →
    m (Option (Randomizer × LeafIndex))
  | 0, _ => pure none
  | attempts + 1, randomness => do
      match ← signAttemptWithHash secretKey message randomness with
      | some index => return some (randomness, index)
      | none => signDigestLoopWithHash secretKey message attempts (randomness + 1)

/-- `Sign` (`sign`, `scheme.rs`): derive the randomizer base `R0` of the message (one hash), scan
`R0, R0 + 1, ...` into the kept subtree, compute the digest, open the forest, sign its key (the
sixteen level-3 nodes) with WOTS+C at `e = idx` and attach the path. -/
def signWithHash (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  -- the randomizer base `S || m` (`TWEAK_RANDOMIZER = 7`)
  let base ← thWithHash secretKey.parameter (tweakFields 7 0 0 0)
    (littleEndianBytes 32 secretKey.schemeSeed ++ littleEndianBytes 32 message)
  let some (randomness, _) ← signDigestLoopWithHash secretKey message digestAttemptLimit base
    | return none
  let digest ← messageDigestWithHash secretKey.parameter message randomness
  let index := digestLeafIndex digest
  let opening ← forestOpenWithHash secretKey.parameter index (digestCoordinateSelections digest)
      secretKey.schemeSeed
  let key ← forestKeyWithHash secretKey.parameter index secretKey.schemeSeed
  let some (counter, values) ← otsSignWithHash secretKey.parameter index secretKey.schemeSeed key
    | return none
  let path ← treePathWithHash secretKey.parameter secretKey.schemeSeed index
  return some ⟨randomness, opening, counter, values, path⟩

end KeyGenerationAndSigning

namespace RandomPermutationModel

open Common Common.SufCma

variable [KeyShape]

/-- leanSPHINCS in the generic SUF-CMA game: the seed, key generation, the deterministic signer,
the verifier, and the winning condition: a valid transcript without the forgery
(`SignerReturnedForgery`). -/
noncomputable def schemeWithHash :
    SchemeWithHash MasterSeed PublicKey KeyGenerationAndSigning.SecretKey Message (Option Signature)
      Forgery where
  sample := sampleMasterSeed
  keygen := KeyGenerationAndSigning.keygenFromSeedWithHash
  sign sk message := KeyGenerationAndSigning.signWithHash (m := OracleComp HashSpec) sk message
  verify pk forgery :=
    Verification.verifyWithHash (m := OracleComp HashSpec) pk forgery.message forgery.signature
  win log forgery :=
    decide (SigningTranscript.WithinSignatureLimit log ∧ ¬SignerReturnedForgery id log
        forgery.message forgery.signature)

end RandomPermutationModel

namespace Lifetimes

open Common.SufCma

/-- **leanSPHINCS in the random-permutation model, at every proved lifetime**: at each subtree
height (`b` = 26, 20, 14, 13, 12, 10, 8, the instances `full`, `pruned20`, …, `pruned8` with
their signature limits), an adversary whose game makes at most `Q` permutation calls,
`Q ≥ 1`, forges with probability at most `(Q + 1) · 2^-127` (`StronglyUnforgeable` at 127 bits).
`Q` counts every call on the game's worst path, the honest signer's included (`QueryCostAtMost` is
structural): a signature costs about `2^35` calls at `b = 26` (`2^32` encoding counters of three
calls, `2^33.6`; `treePath` rebuilding the kept subtree, `2^33.9`; the grinding into the kept
subtree is one call at `b = 26` and up to `2^32` below), so at the largest lifetime, `N ≈ 2^30.4`
signatures, `Q ≥ 2^65` and the bound is about `2^-62`. Proved by
`Sphincs.Lifetimes.requestedSecurityRpm`. -/
abbrev LeanSphincsStronglyUnforgeableWithHash : Prop :=
  ∀ P ∈ [full, pruned20, pruned14, pruned13, pruned12, pruned10, pruned8],
    StronglyUnforgeableWithHash (@RandomPermutationModel.schemeWithHash P) 127

end Lifetimes

end Sphincs

end
