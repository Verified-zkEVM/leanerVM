module

public import Statement.LeanXmss
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# leanSPHINCS

The scheme of `crates/signatures/src/lean_sphincs` (`wots.rs`, `forest.rs`, `scheme.rs`; the
addresses in `crates/signatures/src/tweak.rs`), specified in `doc/lean_sphincs`, for any key
shape (`KeyShape`: the kept subtree's height `b` and the signature limit): one tree of height
`h = 26` of WOTS+C keys (`v = 64` chains of 4 positions, target sum `T = 123`, §sec:ots), pruned
to a kept subtree of height `b` with surrogate siblings (§sec:layer, §sec:pruning), the
randomizer ground into the kept subtree and a counter for the encoding (§sec:sign), and under each
leaf a WOTS forest (§sec:fts):

* 8 trees of height 4 over 16 leaves, hashed up to height 3: the forest key is their sixteen
  height-3 nodes, which no hash folds: the WOTS+C encoding absorbs them with its counter;
* leaf `s` of a tree hashes the four height-2 nodes of its two subtrees of height 3;
* a subtree leaf is a WOTS key of 6 chains of positions `0 … 4`; a codeword is `d ∈ {0..4}^6`
  with `Σ d_i = 5`, named by an 8-bit index into the table `lut` (§sec:codewords);
* one digest call gives `26 + 8 · 26 = 234` bits: the 16 codeword indices (bytes `0 … 15`), then
  from bit 128 the index (26 bits), the 8 tree leaves (4 bits each) and the 16 subtree keys
  (3 bits each, in the order `2c + j`).

Every hash input is `P ‖ A ‖ payload` (§sec:parameters, §sec:tweaks), `P` the 16-byte public
parameter and `A` the 16-byte address. Key generation hashes the seed `S0` into
`S = H(leanSPHINCS ‖ S0)`, from which every secret derives. The message digest hashes `m ‖ ρ` (the
root is not: `P` binds the key), the randomizer base `S ‖ m`.

Then the SUF-CMA game of `Statement/SufCma.lean` with the deterministic signer, the
proved lifetimes (`Lifetimes.full`, `pruned20`, …, `pruned8`), and the end statement
`Sphincs.Lifetimes.LeanSphincsStronglyUnforgeable`, proved by
`Sphincs.Lifetimes.requestedSecurityRpm` (`lean_sphincs`). Its budget `Q` counts the honest signer's
permutation calls too, at their worst case: about `2^35` per signature, so at the largest lifetime
the bound is about `2^-62`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace Sphincs

/-! ### The instance: parameters, types, and hash-input layout -/

export HashSig (digestBits winternitzBits chainLength MasterSeed Digest HashOutput Message
  PublicParameter Randomizer WinternitzDigit ChainStep HashInput truncateHash upperHalfOfHash
  hashHalfForChain PublicKey littleEndianBytes TweakFields addressBytes tweakFields thInput
  sampleMasterSeed)

/-- The encoding counter's bits, `32`. -/
def counterBits : Nat := 32
/-- `v`, the chains of a one-time key, `64`. -/
def chainCount : Nat := 64
/-- `T`, the digit sum of a codeword, `123`. -/
def targetSum : Nat := 123
/-- `h`, the height of the tree. -/
def treeHeight : Nat := 26
/-- Randomizers tried per signature (`ctr` is a `u32`), `A_max`. -/
def digestAttemptLimit : Nat := 2 ^ 32
/-- Encoding counters tried per signature, `C_max`. -/
def encodingAttemptLimit : Nat := 2 ^ 32

/-- The key's shape and lifetime: the kept subtree holds `2^keptSubtreeHeight` leaves
(`keptSubtreeHeight = 26` is the full key), and the key signs at most `signatureLimit` messages. -/
class KeyShape where
  /-- `b`, the kept subtree's height. -/
  keptSubtreeHeight : Nat
  /-- `N`, the most messages the key signs. -/
  signatureLimit : Nat
  keptSubtreeHeight_le_treeHeight : keptSubtreeHeight ≤ treeHeight

export KeyShape (keptSubtreeHeight signatureLimit)

/-- `c`, the WOTS+C encoding counter. -/
abbrev EncodingCounter := BitVec counterBits
/-- `idx = e`, the leaf of the tree and the forest instance a digest selects. -/
abbrev LeafIndex := Fin (2 ^ treeHeight)
/-- `i`, a chain of a one-time key. -/
abbrev ChainIndex := Fin chainCount
/-- A pair of chains `(2t, 2t + 1)` of a one-time key, `t < 32`: one seed derivation. -/
abbrev ChainPairIndex := Fin 32
/-- The `v` digits a codeword assigns to the chains: how far each chain is opened. -/
abbrev Encoding := ChainIndex → WinternitzDigit

/-! #### Forest parameters and types -/

/-- The forest's coordinates: `8` trees under each leaf. -/
def forestCoordinateCount : Nat := 8
/-- Height of a coordinate's top tree (16 super-children). -/
def topTreeHeight : Nat := 4
/-- Height of a sub-tree (8 children). -/
def forestSubtreeHeight : Nat := 3
/-- Chains per child. -/
def forestChainCount : Nat := 6
/-- The top position of a chain: positions `0 .. 4`. -/
def forestChainTop : Nat := 4

/-- `c`, a coordinate: one of the forest's trees. -/
abbrev ForestCoordinate := Fin forestCoordinateCount
/-- `s`, a super-child: a leaf of a coordinate's top tree. -/
abbrev SuperChildIndex := Fin (2 ^ topTreeHeight)
/-- `j`, one of a super-child's two sub-trees. -/
abbrev SubtreeIndex := Fin 2
/-- `a`, a child: a leaf of a sub-tree, a forest WOTS key. -/
abbrev ChildIndex := Fin (2 ^ forestSubtreeHeight)
/-- `i`, a chain of a forest WOTS key. -/
abbrev ForestChainIndex := Fin forestChainCount
/-- A pair of chains `(2t, 2t + 1)` of a forest WOTS key, `t < 3`: one seed derivation. -/
abbrev ForestChainPairIndex := Fin 3
/-- A forest chain position, `0 .. 4`. -/
abbrev ForestChainPosition := Fin (forestChainTop + 1)
/-- A forest chain step, from position `t` to `t + 1`, `t < 4`. -/
abbrev ForestChainStep := Fin forestChainTop
/-- A codeword: the deficit `d_i ∈ {0..4}` of every chain. -/
abbrev Codeword := ForestChainIndex → ForestChainPosition
/-- A codeword index, 8 digest bits. -/
abbrev CodewordIndex := Fin 256

/-! #### The codeword table -/

/-- The 256 entries of the codeword table as base-5 numbers with `d_0` the most significant digit; a
codeword listed twice is chosen by two digest values. The table is `codewordRule`
(`codewordCodes_eq_rule`): the codewords sorted by decreasing `Σ d_i²`, then lexicographically,
entry `t` being codeword number `t mod 214`. By digit pattern: the 30 codewords with digits `{4,1}`
twice each; of the 30 with `{3,2}`, 12 twice and 18 once; the 60 with `{3,1,1}` and the 60 with
`{2,2,1}` once; 34 of the 60 with `{2,1,1,1}` once; none of the 6 with `{1,1,1,1,1}`. Written by
`scripts/forest_table.py`. -/
def codewordTableBase5 : List Nat :=
  [9, 21, 29, 45, 101, 105, 129, 145, 225, 501, 505, 525, 629, 645, 725, 1125,
   2501, 2505, 2525, 2625, 3129, 3145, 3225, 3625, 5625, 12501, 12505, 12525, 12625, 13125, 13, 17,
   53, 65, 77, 85, 253, 265, 325, 377, 385, 425, 1253, 1265, 1325, 1625, 1877, 1885,
   1925, 2125, 6253, 6265, 6325, 6625, 8125, 9377, 9385, 9425, 9625, 10625, 33, 41, 81, 133,
   141, 153, 165, 201, 205, 381, 401, 405, 633, 641, 653, 665, 701, 705, 753, 765,
   825, 1001, 1005, 1025, 1881, 1901, 1905, 2001, 2005, 2025, 3133, 3141, 3153, 3165, 3201, 3205,
   3253, 3265, 3325, 3501, 3505, 3525, 3753, 3765, 3825, 4125, 5001, 5005, 5025, 5125, 9381, 9401,
   9405, 9501, 9505, 9525, 10001, 10005, 10025, 10125, 37, 57, 61, 137, 177, 185, 257, 261,
   277, 285, 301, 305, 637, 677, 685, 877, 885, 925, 1257, 1261, 1277, 1285, 1301, 1305,
   1377, 1385, 1425, 1501, 1505, 1525, 3137, 3177, 3185, 3377, 3385, 3425, 4377, 4385, 4425, 4625,
   6257, 6261, 6277, 6285, 6301, 6305, 6377, 6385, 6425, 6501, 6505, 6525, 6877, 6885, 6925, 7125,
   7501, 7505, 7525, 7625, 157, 161, 181, 281, 657, 661, 681, 757, 761, 777, 785, 801,
   805, 881, 901, 905, 1281, 1381, 1401, 1405, 3157, 3161, 3181, 3257, 3261, 3277, 3285, 3301,
   3305, 3381, 3401, 3405, 3757, 3761, 9, 21, 29, 45, 101, 105, 129, 145, 225, 501,
   505, 525, 629, 645, 725, 1125, 2501, 2505, 2525, 2625, 3129, 3145, 3225, 3625, 5625, 12501,
   12505, 12525, 12625, 13125, 13, 17, 53, 65, 77, 85, 253, 265, 325, 377, 385, 425]

/-- Digit `i` (`i = 0` most significant) of a base-5 code with 6 digits. -/
def base5Digit (code : Nat) (i : ForestChainIndex) : ForestChainPosition :=
  ⟨code / 5 ^ (5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩

/-- `lut t`: entry `t` of the table. -/
def lut (t : CodewordIndex) : Codeword := base5Digit (codewordTableBase5.getD t.val 0)

/-! #### The message digest: one call, 234 bits -/

/-- Digest bits of one coordinate: super-child 4, and child 3 and codeword 8 for each sub-tree. -/
def coordinateBits : Nat := 26

/-- The message digest is `h + 8 · 26 = 234` bits: an index and the fields of 8 coordinates. -/
def messageDigestBits : Nat := treeHeight + forestCoordinateCount * coordinateBits

/-- The message digest's `234` bits. -/
abbrev MessageDigest := BitVec messageDigestBits

/-- The first 234 bits of the single digest call. -/
def truncateMessageDigest (digestCallOutput : HashOutput) : MessageDigest :=
  digestCallOutput.extractLsb' 0 messageDigestBits

/-- What a digest selects in one coordinate: the super-child, and per sub-tree a child and a
codeword index. -/
structure CoordinateSelection where
  /-- The super-child `s`. -/
  superChild : SuperChildIndex
  /-- The child `a` of each sub-tree. -/
  child : SubtreeIndex → ChildIndex
  /-- The codeword index of each sub-tree's child. -/
  codewordIndex : SubtreeIndex → CodewordIndex
deriving DecidableEq

/-- The forest key of an instance: the two level-3 nodes of every tree, `(t_c[0], t_c[1])`. It is
not hashed: the WOTS+C encoding absorbs the sixteen nodes (`Verification.encode`). -/
abbrev ForestKey := ForestCoordinate → Digest × Digest

/-- The opening of one sub-tree: the 6 revealed chain values and the 3 auth nodes. -/
structure SubtreeOpening where
  /-- The child's chains, each opened to position `4 - d_i`. -/
  values : ForestChainIndex → Digest
  /-- The sub-tree's siblings, the last the other level-2 node. -/
  path : Fin forestSubtreeHeight → Digest
deriving DecidableEq

/-- The opening of one coordinate: both sub-trees, then the 4 auth nodes of the top tree. -/
structure CoordinateOpening where
  /-- Each sub-tree's opening. -/
  subtreeOpenings : SubtreeIndex → SubtreeOpening
  /-- The top tree's siblings, the last the other level-3 node. -/
  topTreePath : Fin topTreeHeight → Digest
deriving DecidableEq

/-- The randomizer, the forest opening, the WOTS+C signature (its counter and chain values) and the
authentication path: 4276 bytes (`LeanSphincsSignature`, `scheme.rs`). -/
structure Signature where
  /-- The randomizer `ρ`, which grinds the leaf index into the kept subtree. -/
  randomizer : Randomizer
  /-- The forest's opening, one per coordinate. -/
  forestOpening : ForestCoordinate → CoordinateOpening
  /-- The WOTS+C counter `c` that makes the forest key's encoding a codeword. -/
  counter : EncodingCounter
  /-- Chain `i` opened to its codeword digit. -/
  chainValues : ChainIndex → Digest
  /-- The siblings from the leaf up to the root, surrogates above the kept subtree. -/
  authenticationPath : Fin treeHeight → Digest
deriving DecidableEq

/-! #### Forest addresses -/

/-- `c + 8 s + 128 j`, a sub-tree of the instance (3 + 4 + 1 bits). -/
def subtreeSlot (c : ForestCoordinate) (s : SuperChildIndex) (j : SubtreeIndex) : Nat :=
  c.val + 8 * s.val + 128 * j.val

/-- `c + 8 s + 128 j + 256 a`, a child of the instance (11 bits). -/
def childSlot (c : ForestCoordinate) (s : SuperChildIndex) (j : SubtreeIndex)
    (a : ChildIndex) : Nat :=
  subtreeSlot c s j + 256 * a.val

/-- `c + 8 s + 128 j + 256 a + 2048 i`, a chain of the instance. -/
def chainSlot (c : ForestCoordinate) (s : SuperChildIndex) (j : SubtreeIndex) (a : ChildIndex)
    (i : ForestChainIndex) : Nat :=
  childSlot c s j a + 2048 * i.val

/-- The verification hash domains. Seed derivation uses `KeygenDomain`. Forest levels count from the
leaves: a `subtreeNode` at `level` is the node of sub-tree level `level + 1`, a `topTreeNode` at
`level` the node of top-tree level `level + 1`. The scheme hashes sub-tree levels 1 and 2 and
top-tree levels 1 to 3: the address of a tree's root exists and no algorithm uses it. -/
inductive HashDomain where
  /-- A step of chain `chainIndex` of the one-time key at `leaf`. -/
  | chain (leaf : LeafIndex) (chainIndex : ChainIndex) (step : ChainStep)
  /-- The one-time key's leaf, the hash of its chain ends. -/
  | leaf (leaf : LeafIndex)
  /-- A tree node at `level`, index `nodeIndex`. -/
  | node (level : Nat) (nodeIndex : Nat)
  /-- The WOTS+C encoding of the forest key at `leaf`. -/
  | encoding (leaf : LeafIndex)
  /-- Step `t` of chain `i` of child `(c, s, j, a)` of forest instance `leafIndex`. -/
  | forestChain (leafIndex : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
      (j : SubtreeIndex) (a : ChildIndex) (i : ForestChainIndex) (t : ForestChainStep)
  /-- A child's leaf, the hash of its chain tops. -/
  | childLeaf (leafIndex : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
      (j : SubtreeIndex) (a : ChildIndex)
  /-- A sub-tree's node. -/
  | subtreeNode (leafIndex : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
      (j : SubtreeIndex) (level : Fin forestSubtreeHeight) (node : ChildIndex)
  /-- A super-child, the hash of its sub-trees' level-2 nodes. -/
  | superChild (leafIndex : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
  /-- A top tree's node. -/
  | topTreeNode (leafIndex : LeafIndex) (c : ForestCoordinate) (level : Fin topTreeHeight)
      (node : SuperChildIndex)
  /-- No algorithm's: a label of the proofs. -/
  | roots (leafIndex : LeafIndex)
  /-- The message digest. -/
  | message
deriving DecidableEq

/-- The address of a hash domain: types `TWEAK_CHAIN = 1`, ..., `TWEAK_MSG = 12`, forest types 15 to
19 (`lean_sphincs/hash.rs`); type 20 (`roots`) is not the crate's, a label of the proofs under which
no algorithm hashes. In the tree `lo` is the leaf (or the node index) and `hi` the chain (or the
node level); a chain step carries its step. In a forest instance `lo` is `idx` and `hi` the packed
position; a forest chain step from position `t` carries step `t`. An address has no layer and no
tree field (`Tweak`, `tweak.rs`). -/
def hashDomainFields : HashDomain → TweakFields
  | .chain leaf chainIndex step => tweakFields 1 step chainIndex leaf
  | .leaf leaf => tweakFields 2 0 0 leaf
  | .node level nodeIndex => tweakFields 3 0 level nodeIndex
  | .encoding leaf => tweakFields 4 0 0 leaf
  | .forestChain leafIndex c s j a i t => tweakFields 15 t (chainSlot c s j a i) leafIndex
  | .childLeaf leafIndex c s j a => tweakFields 16 0 (childSlot c s j a) leafIndex
  | .subtreeNode leafIndex c s j level node =>
      tweakFields 17 0 (subtreeSlot c s j + 256 * (level.val + 1) + 1024 * node.val) leafIndex
  | .superChild leafIndex c s => tweakFields 18 0 (c.val + 8 * s.val) leafIndex
  | .topTreeNode leafIndex c level node =>
      tweakFields 19 0 (c.val + 8 * (level.val + 1) + 64 * node.val) leafIndex
  | .roots leafIndex => tweakFields 20 0 0 leafIndex
  | .message => tweakFields 12 0 0 0

/-- The pair of chains a chain of a one-time key belongs to. -/
def chainPair (chain : ChainIndex) : ChainPairIndex :=
  ⟨chain.val / 2, by have h : chain.val < 64 := chain.isLt; omega⟩

/-- The pair of chains a chain of a forest WOTS key belongs to. -/
def forestChainPair (i : ForestChainIndex) : ForestChainPairIndex :=
  ⟨i.val / 2, by have h : i.val < 6 := i.isLt; omega⟩

/-- `c + 8 s + 128 j + 256 a + 2048 t`, a pair of chains of the instance. -/
def chainPairSlot (c : ForestCoordinate) (s : SuperChildIndex) (j : SubtreeIndex) (a : ChildIndex)
    (pair : ForestChainPairIndex) : Nat :=
  childSlot c s j a + 2048 * pair.val

/-- The seed derivations, one hash each. `oneTimeChainPair` gives the starts of chains `2t` and
`2t + 1` of the one-time key at a leaf, `childChainPair` the starts `x_{2t,0}` and `x_{2t+1,0}` of
chains `2t` and `2t + 1` of child `(idx, c, s, j, a)`: the two 16-byte halves of the hash. The
parameter and a surrogate are the first 16 bytes of their hash. -/
inductive KeygenDomain where
  /-- The public parameter `P`. -/
  | parameter
  /-- The starts of chains `2t` and `2t + 1` of the one-time key at `leaf`, `t = pair`. -/
  | oneTimeChainPair (leaf : LeafIndex) (pair : ChainPairIndex)
  /-- The starts of chains `2t` and `2t + 1` of child `(c, s, j, a)`, `t = pair`. -/
  | childChainPair (leafIndex : LeafIndex) (c : ForestCoordinate) (s : SuperChildIndex)
      (j : SubtreeIndex) (a : ChildIndex) (pair : ForestChainPairIndex)
  /-- The surrogate sibling at `level`. -/
  | surrogate (level : Fin treeHeight)
deriving DecidableEq

/-- `TWEAK_PARAMETER = 5`, `TWEAK_PRF = 0` (`hi` the pair of chains, `lo` the leaf),
`TWEAK_FOREST_PRF = 14` (`hi` the packed pair of chains, `lo = idx`), `TWEAK_SURROGATE = 13` (`hi`
the level). -/
def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0 0
  | .oneTimeChainPair leaf pair => tweakFields 0 0 pair leaf
  | .childChainPair leafIndex c s j a pair =>
      tweakFields 14 0 (chainPairSlot c s j a pair) leafIndex
  | .surrogate level => tweakFields 13 0 level 0

/-- `SEED_TAG`, the 11 ASCII bytes of `leanSPHINCS`. -/
def seedTag : HashInput := [0x6c, 0x65, 0x61, 0x6e, 0x53, 0x50, 0x48, 0x49, 0x4e, 0x43, 0x53]

/-! #### The target-sum code

`v = 64` chunks of `w = 2` bits covering the 128 digest bits, and the code is the words of digit sum
`T = 123`. -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- Offset of a two-bit digit. -/
def digitOffset (i : ChainIndex) : Nat := winternitzBits * i.val

/-- `x_i`, the two bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- A digest decodes exactly when its 64 digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if Valid (digestEncoding digest) then some (digestEncoding digest) else none

end TargetSum

/-! ### The algorithms

`Verification` contains the hash and verification routines; `KeyGenerationAndSigning` contains
key generation and signing. Hashing routines work over a permutation `π` of the Keccak state in any
monad, the hash `H` being Keccak-256 over `π` (`keccakHash`). -/

namespace Verification

open LeanVM.Semantics (KeccakState)

export HashSig.OverPermutation (sequenceFin keccakHash walkChain nodePayload foldPath buildTree
    th thPair
  taggedSeed)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- The tweakable hash at a hash domain's address (`th`). -/
abbrev tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest :=
  th π parameter (hashDomainFields domain) payload

/-! #### The one-time signature -/

/-- A node index at level `0` read as a leaf. -/
def leafOfNat (value : Nat) : LeafIndex :=
  ⟨value % 2 ^ treeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Chain `i` of the one-time key at a leaf: the step onto position `t + 1` carries step `t`
(`chain`, `wots.rs`: a step carries the position it leaves). -/
def chainWalk (parameter : PublicParameter) (leaf : LeafIndex) (chainIndex : ChainIndex) :
    Nat → Nat → Digest → m Digest :=
  walkChain fun step value ↦
    tweakableHash π parameter (.chain leaf chainIndex step) (littleEndianBytes 16 value)

/-- The verifier's half of a chain: walk the remaining `3 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (leaf : LeafIndex) (chainIndex : ChainIndex)
    (digit : WinternitzDigit) (value : Digest) : m Digest :=
  chainWalk π parameter leaf chainIndex digit.val (chainLength - 1 - digit.val) value

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (littleEndianBytes 16)

/-- The one-time leaf: the hash of the `v` chain ends (`wots_leaf_hash`). -/
def leafHash (parameter : PublicParameter) (leaf : LeafIndex) (endpoints : ChainIndex → Digest) :
    m Digest :=
  tweakableHash π parameter (.leaf leaf) (leafPayload endpoints)

/-- `t_0[0] || t_0[1] || ... || t_7[0] || t_7[1]`, the forest key as bytes: the level-3 nodes of the
8 top trees. -/
def forestKeyPayload (tops : ForestKey) : HashInput :=
  (List.ofFn tops).flatMap fun pair => nodePayload pair.1 pair.2

/-- `Enc(P, e, K, c)`: hash the forest key's sixteen nodes, then the counter, under the leaf's
encoding tweak, and decode. There is no forest-key hash: the counter falls in the last block of this
one (`P || A || K || c`, 292 bytes). -/
def encode (parameter : PublicParameter) (leaf : LeafIndex) (forestKey : ForestKey)
    (counter : EncodingCounter) : m (Option Encoding) := do
  let digest ← tweakableHash π parameter (.encoding leaf)
    (forestKeyPayload forestKey ++ littleEndianBytes 4 counter)
  return TargetSum.decodeDigest digest

/-- `Ots.leaf` (`wots_leaf`, `wots.rs`): the verifier's leaf, or nothing if the counter does not
encode the message. -/
def otsLeaf (parameter : PublicParameter) (leaf : LeafIndex) (forestKey : ForestKey)
    (counter : EncodingCounter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode π parameter leaf forestKey counter | return none
  let endpoints ← sequenceFin fun chainIndex =>
    recoverChain π parameter leaf chainIndex (encoding chainIndex) (values chainIndex)
  let value ← leafHash π parameter leaf endpoints
  return some value

/-! #### The tree -/

/-- `Tree.fold` (`tree_fold`): fold a leaf and a path into the root. -/
def treeFold (parameter : PublicParameter) (leaf : LeafIndex) (path : Nat → Digest) :
    Nat → Digest → m Digest :=
  foldPath (fun level nodeIndex ↦ tweakableHash π parameter (.node (level + 1) nodeIndex))
    leaf.val path

/-! #### The forest -/

/-- Forest chain `i` of a child; the step onto position `t + 1` carries step `t`. -/
def forestChainWalk (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (s : SuperChildIndex) (j : SubtreeIndex) (a : ChildIndex) (i : ForestChainIndex) : Nat → Nat →
    Digest → m Digest :=
  walkChain fun step value ↦
    tweakableHash π parameter (.forestChain leafIndex c s j a i step) (littleEndianBytes 16 value)

/-- The verifier's half of a forest chain: from position `4 - d` walk `d` steps. -/
def forestRecoverChain (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (s : SuperChildIndex) (j : SubtreeIndex) (a : ChildIndex) (i : ForestChainIndex)
    (deficit : ForestChainPosition) (value : Digest) : m Digest :=
  forestChainWalk π parameter leafIndex c s j a i (forestChainTop - deficit.val) deficit.val value

/-- `x_{0,4} || ... || x_{5,4}`. -/
def childPayload (chainEnds : ForestChainIndex → Digest) : HashInput :=
  (List.ofFn chainEnds).flatMap (littleEndianBytes 16)

/-- The child leaf: the hash of the 6 chain tops. -/
def childLeafHash (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (s : SuperChildIndex) (j : SubtreeIndex) (a : ChildIndex)
    (chainEnds : ForestChainIndex → Digest) : m Digest :=
  tweakableHash π parameter (.childLeaf leafIndex c s j a) (childPayload chainEnds)

/-- The child leaf an opening at codeword `word` reaches. -/
def childLeafRecover (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (s : SuperChildIndex) (j : SubtreeIndex) (a : ChildIndex) (word : Codeword)
    (values : ForestChainIndex → Digest) : m Digest := do
  let chainEnds ← sequenceFin fun i =>
    forestRecoverChain π parameter leafIndex c s j a i (word i) (values i)
  childLeafHash π parameter leafIndex c s j a chainEnds

/-- The node hash of a sub-tree: at level `l + 1 ≤ 3`, node `i < 8` (`0` above). -/
def subtreeNodeHash (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (s : SuperChildIndex) (j : SubtreeIndex) (level node : Nat) (payload : HashInput) : m Digest :=
  if h : level < forestSubtreeHeight then
    tweakableHash π parameter (.subtreeNode leafIndex c s j ⟨level, h⟩
      ⟨node % 2 ^ forestSubtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) payload
  else pure 0

/-- Fold a child leaf and a sub-tree path into the sub-tree root. -/
def subtreeFold (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (s : SuperChildIndex) (j : SubtreeIndex) (a : ChildIndex)
    (path : Fin forestSubtreeHeight → Digest) : Nat → Digest → m Digest :=
  foldPath (subtreeNodeHash π parameter leafIndex c s j) a.val
    fun level ↦ if h : level < forestSubtreeHeight then path ⟨level, h⟩ else 0

/-- The two top nodes of a tree in index order, from the one the fold reached and the last path
element: the reached node is node 1 exactly when `bit`, the top bit of the leaf index, is set. -/
def orderTops (bit : Bool) (current sibling : Digest) : Digest × Digest :=
  if bit then (sibling, current) else (current, sibling)

/-- `m_0[0] || m_0[1] || m_1[0] || m_1[1]`, the level-2 nodes of the two sub-trees. -/
def superChildPayload (tops : SubtreeIndex → Digest × Digest) : HashInput :=
  nodePayload (tops 0).1 (tops 0).2 ++ nodePayload (tops 1).1 (tops 1).2

/-- The super-child `Th(super(idx, c, s), m_0[0] || m_0[1] || m_1[0] || m_1[1])`: the hash of the
two level-2 nodes of each of its sub-trees. A sub-tree has no root hash. -/
def superChildHash (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (s : SuperChildIndex) (tops : SubtreeIndex → Digest × Digest) : m Digest :=
  tweakableHash π parameter (.superChild leafIndex c s) (superChildPayload tops)

/-- The node hash of a coordinate's top tree: at level `l + 1 ≤ 4`, node `i < 16` (`0` above). -/
def topTreeNodeHash (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (level node : Nat) (payload : HashInput) : m Digest :=
  if h : level < topTreeHeight then
    tweakableHash π parameter (.topTreeNode leafIndex c ⟨level, h⟩
      ⟨node % 2 ^ topTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) payload
  else pure 0

/-- Fold a super-child and a top path into the coordinate root. -/
def topTreeFold (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (s : SuperChildIndex) (path : Fin topTreeHeight → Digest) : Nat → Digest → m Digest :=
  foldPath (topTreeNodeHash π parameter leafIndex c) s.val
    fun level ↦ if h : level < topTreeHeight then path ⟨level, h⟩ else 0

/-- The last level of a sub-tree path: the other level-2 node. -/
def subtreePathLastLevel : Fin forestSubtreeHeight := ⟨forestSubtreeHeight - 1, by decide⟩

/-- The last level of a top-tree path: the other level-3 node. -/
def topTreePathLastLevel : Fin topTreeHeight := ⟨topTreeHeight - 1, by decide⟩

/-- The two level-3 nodes of a coordinate's top tree that an opening reaches. In each sub-tree the
child leaf is folded 2 levels and the last path element is the other level-2 node; the four level-2
nodes hash into the super-child, which is folded 3 levels, and the last top path element is the
other level-3 node. -/
def coordinateRecover (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (selection : CoordinateSelection) (opening : CoordinateOpening) : m (Digest × Digest) := do
  let tops ← sequenceFin fun j => do
    let leaf ← childLeafRecover π parameter leafIndex c selection.superChild j (selection.child j)
      (lut (selection.codewordIndex j)) (opening.subtreeOpenings j).values
    let node ← subtreeFold π parameter leafIndex c selection.superChild j (selection.child j)
        (opening.subtreeOpenings j).path
      (forestSubtreeHeight - 1) leaf
    return orderTops ((selection.child j).val.testBit (forestSubtreeHeight - 1)) node
        ((opening.subtreeOpenings j).path subtreePathLastLevel)
  let super ← superChildHash π parameter leafIndex c selection.superChild tops
  let node ← topTreeFold π parameter leafIndex c selection.superChild opening.topTreePath
    (topTreeHeight - 1) super
  return orderTops (selection.superChild.val.testBit (topTreeHeight - 1)) node
    (opening.topTreePath topTreePathLastLevel)

/-- `Fts.recover`: the forest key an opening reaches, the sixteen level-3 nodes. A top tree has no
root hash, and the key has no hash: the WOTS+C encoding absorbs it. -/
def forestRecover (parameter : PublicParameter) (leafIndex : LeafIndex)
    (selections : ForestCoordinate → CoordinateSelection)
    (opening : ForestCoordinate → CoordinateOpening) : m ForestKey :=
  sequenceFin fun c => coordinateRecover π parameter leafIndex c (selections c) (opening c)

/-! #### The message digest -/

/-- `m || rho`, what the message digest hashes after the parameter and the address: the input
`P || A || m || rho` is 80 bytes, one block. The root is not hashed (`P` binds the key). -/
def messageDigestPayload (message : Message) (randomizer : Randomizer) : HashInput :=
  littleEndianBytes 32 message ++ littleEndianBytes 16 randomizer

/-- The single untruncated digest call (`message_digest_bytes`, `scheme.rs`). -/
def messageDigestCall (parameter : PublicParameter) (message : Message) (randomizer : Randomizer) :
    m HashOutput :=
  thPair π parameter (hashDomainFields .message) (messageDigestPayload message randomizer)

/-- Bit offset of the index: the low 26 bits of the last 16 bytes of the digest. -/
def leafIndexOffset : Nat := 128

/-- `idx`, the 26 bits of the digest from bit 128. -/
def digestLeafIndex (digest : MessageDigest) : LeafIndex :=
  (digest.extractLsb' leafIndexOffset treeHeight).toFin

/-- `Digest(P, m, rho)` (`message_digest`): the single call, truncated to 234 bits. -/
def messageDigest (parameter : PublicParameter) (message : Message) (randomizer : Randomizer) : m
    MessageDigest := do
  let digestCallOutput ← messageDigestCall π parameter message randomizer
  return truncateMessageDigest digestCallOutput

/-- Bit offset of the codeword index of sub-tree `j` of coordinate `c`: byte `2c + j` of the digest.
-/
def codewordIndexOffset (c : ForestCoordinate) (j : SubtreeIndex) : Nat := 8 * (2 * c.val + j.val)

/-- Bit offset of coordinate `c`'s super-child (4 bits), after the index. -/
def superChildOffset (c : ForestCoordinate) : Nat := 154 + 4 * c.val

/-- Bit offset of the child of sub-tree `j` of coordinate `c` (3 bits), after the super-children. -/
def childOffset (c : ForestCoordinate) (j : SubtreeIndex) : Nat := 186 + 3 * (2 * c.val + j.val)

/-- The coordinate fields of a digest. -/
def digestCoordinateSelections (digest : MessageDigest) : ForestCoordinate → CoordinateSelection :=
    fun c =>
  { superChild := (digest.extractLsb' (superChildOffset c) topTreeHeight).toFin
    child := fun j => (digest.extractLsb' (childOffset c j) forestSubtreeHeight).toFin
    codewordIndex := fun j => (digest.extractLsb' (codewordIndexOffset c j) 8).toFin }

/-! #### Verification -/

/-- `Ver(pk, m, sigma)` (`verify`, `scheme.rs`): recompute the digest, recover the forest key,
recover the one-time leaf at `e = idx`, fold the path and compare with the root. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest π publicKey.parameter message signature.randomizer
  let leafIndex := digestLeafIndex digest
  let forestKey ← forestRecover π publicKey.parameter leafIndex (digestCoordinateSelections digest)
      signature.forestOpening
  let some leaf ← otsLeaf π publicKey.parameter leafIndex forestKey signature.counter
    signature.chainValues | return false
  let root ← treeFold π publicKey.parameter leafIndex
    (fun level ↦ if h : level < treeHeight
        then signature.authenticationPath ⟨level, h⟩ else 0) treeHeight leaf
  return decide (root = publicKey.root)

end Verification

/-- **leanSPHINCS verification as deployed**: over Keccak-f[1600], the hash Keccak-256. -/
def verifyWithKeccak (publicKey : PublicKey) (message : Message) (signature : Signature) : Bool :=
  Id.run (Verification.verify (m := Id) LeanVM.Semantics.keccakF1600 publicKey message signature)

/-! #### Pruning -/

section Pruning

variable [KeyShape]

/-- `s`, the kept subtree: the low `h - b` bits of `P`, read as a little-endian number (`0` for a
full key). -/
def keptSubtreePosition (parameter : PublicParameter) : Nat :=
  parameter.toNat % 2 ^ (treeHeight - keptSubtreeHeight)

/-- The kept subtree holds leaves `s * 2^b .. (s + 1) * 2^b` (`LeanSphincsSecretKey::keeps`,
`scheme.rs`). -/
abbrev LandsInKeptSubtree (parameter : PublicParameter) (leafIndex : LeafIndex) : Prop :=
  leafIndex.val / 2 ^ keptSubtreeHeight = keptSubtreePosition parameter

end Pruning

namespace KeyGenerationAndSigning

open Verification
open LeanVM.Semantics (KeccakState)

export LeanXmss.KeyGenerationAndSigning (SecretKey)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- `wots_secrets`: the starts of the 64 chains of the one-time key at a leaf, from 32 seed
derivations. Chains `2t` and `2t + 1` start at the two halves of derivation `t`. -/
def otsSecrets (parameter : PublicParameter) (leaf : LeafIndex) (seed : MasterSeed) :
    m (ChainIndex → Digest) := do
  let outputs ← sequenceFin fun pair : ChainPairIndex =>
    thPair π parameter (keygenDomainFields (.oneTimeChainPair leaf pair)) (littleEndianBytes
        32 seed)
  return fun chainIndex => hashHalfForChain chainIndex.val (outputs (chainPair chainIndex))

/-- The chain ends of the one-time key at a leaf. -/
def oneTimePublicKey (parameter : PublicParameter) (leaf : LeafIndex) (seed : MasterSeed) :
    m (ChainIndex → Digest) := do
  let secrets ← otsSecrets π parameter leaf seed
  sequenceFin fun chainIndex =>
    chainWalk π parameter leaf chainIndex 0 (chainLength - 1) (secrets chainIndex)

/-- The encoding counters `counter, counter + 1, ...`, at most `attempts` of them, stopping at the
first that encodes the message. -/
def otsSignFrom (parameter : PublicParameter) (leaf : LeafIndex) (seed : MasterSeed)
    (forestKey : ForestKey) : Nat → Nat → m (Option (EncodingCounter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode π parameter leaf forestKey (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let secrets ← otsSecrets π parameter leaf seed
          let values ← sequenceFin fun chainIndex =>
            chainWalk π parameter leaf chainIndex 0 (encoding chainIndex).val (secrets chainIndex)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter leaf seed forestKey attempts (counter + 1)

/-- `wots_sign`: the least admissible counter, then the opened chain values. -/
def otsSign (parameter : PublicParameter) (leaf : LeafIndex) (seed : MasterSeed)
    (forestKey : ForestKey) : m (Option (EncodingCounter × (ChainIndex → Digest))) :=
  otsSignFrom π parameter leaf seed forestKey encodingAttemptLimit 0

/-- A node of the tree, computed from the one-time keys below it. -/
def treeNode (parameter : PublicParameter) (seed : MasterSeed) : Nat → Nat → m Digest :=
  buildTree (fun nodeIndex ↦ do
      leafHash π parameter (leafOfNat nodeIndex)
        (← oneTimePublicKey π parameter (leafOfNat nodeIndex) seed))
    fun level nodeIndex ↦ tweakableHash π parameter (.node (level + 1) nodeIndex)

/-- The starts `x_{i,0}` of the 6 chains of a child, from 3 seed derivations. Chains `2t` and
`2t + 1` start at the two halves of derivation `t`. -/
def forestSecrets (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (s : SuperChildIndex) (j : SubtreeIndex) (a : ChildIndex) (seed : MasterSeed) :
    m (ForestChainIndex → Digest) := do
  let outputs ← sequenceFin fun pair : ForestChainPairIndex =>
    thPair π parameter (keygenDomainFields (.childChainPair leafIndex c s j a pair))
      (littleEndianBytes 32 seed)
  return fun i => hashHalfForChain i.val (outputs (forestChainPair i))

/-- The leaf of a child, from its 6 chain tops. -/
def childLeaf (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (s : SuperChildIndex) (j : SubtreeIndex) (a : ChildIndex) (seed : MasterSeed) : m Digest := do
  let secrets ← forestSecrets π parameter leafIndex c s j a seed
  let chainEnds ← sequenceFin fun i
      => forestChainWalk π parameter leafIndex c s j a i 0 forestChainTop (secrets i)
  childLeafHash π parameter leafIndex c s j a chainEnds

/-- A node of a sub-tree at tree level `level`. -/
def subtreeNode (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (s : SuperChildIndex) (j : SubtreeIndex) (seed : MasterSeed) : Nat → Nat → m Digest :=
  buildTree (fun node ↦ childLeaf π parameter leafIndex c s j
      ⟨node % 2 ^ forestSubtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ seed)
    (subtreeNodeHash π parameter leafIndex c s j)

/-- A super-child, from the two level-2 nodes of each of its two sub-trees. -/
def superChildNode (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (s : SuperChildIndex) (seed : MasterSeed) : m Digest := do
  let tops ← sequenceFin fun j => do
    let left ← subtreeNode π parameter leafIndex c s j seed (forestSubtreeHeight - 1) 0
    let right ← subtreeNode π parameter leafIndex c s j seed (forestSubtreeHeight - 1) 1
    return (left, right)
  superChildHash π parameter leafIndex c s tops

/-- A node of a coordinate's top tree at tree level `level`. -/
def topTreeNode (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (seed : MasterSeed) : Nat → Nat → m Digest :=
  buildTree (fun node ↦ superChildNode π parameter leafIndex c
      ⟨node % 2 ^ topTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ seed)
    (topTreeNodeHash π parameter leafIndex c)

/-- The forest key of instance `idx`: the two level-3 nodes of every coordinate (no hash). -/
def forestKey (parameter : PublicParameter) (leafIndex : LeafIndex) (seed : MasterSeed) : m
    ForestKey :=
  sequenceFin fun c => do
    let left ← topTreeNode π parameter leafIndex c seed (topTreeHeight - 1) 0
    let right ← topTreeNode π parameter leafIndex c seed (topTreeHeight - 1) 1
    return (left, right)

/-- The opening of one coordinate at a mark. The last element of each path (level 2 of a sub-tree,
level 3 of the top tree) is the top node the verifier does not compute. -/
def coordinateOpen (parameter : PublicParameter) (leafIndex : LeafIndex) (c : ForestCoordinate)
    (selection : CoordinateSelection) (seed : MasterSeed) : m CoordinateOpening := do
  let sub ← sequenceFin fun j => do
    let secrets ←
      forestSecrets π parameter leafIndex c selection.superChild j (selection.child j) seed
    let values ← sequenceFin fun i =>
      forestChainWalk π parameter leafIndex c selection.superChild j (selection.child j) i 0
        (forestChainTop - (lut (selection.codewordIndex j) i).val) (secrets i)
    let path ← sequenceFin fun level : Fin forestSubtreeHeight =>
      subtreeNode π parameter leafIndex c selection.superChild j seed level.val
        (Nat.xor ((selection.child j).val / 2 ^ level.val) 1)
    return (⟨values, path⟩ : SubtreeOpening)
  let top ← sequenceFin fun level : Fin topTreeHeight =>
    topTreeNode π parameter leafIndex c seed level.val
      (Nat.xor (selection.superChild.val / 2 ^ level.val) 1)
  return ⟨sub, top⟩

/-- `Fts.sign`: the opening of every coordinate. -/
def forestOpen (parameter : PublicParameter) (leafIndex : LeafIndex)
    (selections : ForestCoordinate → CoordinateSelection) (seed : MasterSeed) : m
    (ForestCoordinate → CoordinateOpening) :=
  sequenceFin fun c => coordinateOpen π parameter leafIndex c (selections c) seed

variable [KeyShape]

/-- The surrogate sibling at `level >= b`, derived from the seed (`TWEAK_SURROGATE`). Honest calls
have `level < h`. -/
def surrogate (parameter : PublicParameter) (seed : MasterSeed) (level : Nat) : m Digest :=
  if hlevel :
    level < treeHeight then th π parameter (keygenDomainFields (.surrogate ⟨level, hlevel⟩))
      (littleEndianBytes 32 seed)
  else pure 0

/-- The node at level `b + steps` above the kept subtree: the subtree root folded with the first
`steps` surrogates (the surrogate fold of `key_gen_from_seed`, `scheme.rs`). -/
def spineNode (parameter : PublicParameter) (seed : MasterSeed) : Nat → m Digest
  | 0 => treeNode π parameter seed keptSubtreeHeight (keptSubtreePosition parameter)
  | steps + 1 => do
      let below ← spineNode parameter seed steps
      let sibling ← surrogate π parameter seed (keptSubtreeHeight + steps)
      let nodeIndex := keptSubtreePosition parameter / 2 ^ steps
      if nodeIndex.testBit 0 then
        tweakableHash π parameter (.node (keptSubtreeHeight + steps + 1) (nodeIndex / 2))
          (nodePayload sibling below)
      else
        tweakableHash π parameter (.node (keptSubtreeHeight + steps + 1) (nodeIndex / 2))
          (nodePayload below sibling)

/-- The root: the spine's top. -/
def treeRoot (parameter : PublicParameter) (seed : MasterSeed) : m Digest :=
  spineNode π parameter seed (treeHeight - keptSubtreeHeight)

/-- The authentication path of a kept leaf (`LeanSphincsSecretKey::path`, `scheme.rs`): subtree
nodes below level `b`, surrogates from level `b` on. -/
def treePath (parameter : PublicParameter) (seed : MasterSeed) (leaf : LeafIndex) :
    m (Fin treeHeight → Digest) :=
  sequenceFin fun level =>
    if level.val < keptSubtreeHeight then
      treeNode π parameter seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      surrogate π parameter seed level.val

/-- Key generation from the scheme seed `S`: derive the public parameter, which places the kept
subtree, and build the root. -/
def keygenFromSchemeSeed (schemeSeed : MasterSeed) : m (PublicKey × SecretKey) := do
  let parameter ← th π 0 (keygenDomainFields .parameter) (littleEndianBytes 32 schemeSeed)
  let root ← treeRoot π parameter schemeSeed
  return (⟨root, parameter⟩, ⟨schemeSeed, parameter⟩)

/-- `Gen` (`key_gen_from_seed`): hash the key's seed `S0` into the scheme seed `S`, then generate
from `S`. -/
def keygenFromSeed (masterSeed : MasterSeed) : m (PublicKey × SecretKey) := do
  let master ← taggedSeed π seedTag masterSeed
  keygenFromSchemeSeed π master

/-- One grinding attempt: the leaf index of the digest call (the `find_map` of `sign`,
`scheme.rs`). -/
def grindingAttempt (secretKey : SecretKey) (message : Message) (randomizer : Randomizer) :
    m (Option LeafIndex) := do
  let digestCallOutput ← messageDigestCall π secretKey.parameter message randomizer
  if LandsInKeptSubtree secretKey.parameter
      (digestLeafIndex (truncateMessageDigest digestCallOutput)) then
    return some (digestLeafIndex (truncateMessageDigest digestCallOutput))
  else
    return none

/-- Try `randomizer, randomizer + 1, ...`, stopping at the first that lands in the kept subtree. -/
def grindRandomizer (secretKey : SecretKey) (message : Message) : Nat → Randomizer →
    m (Option (Randomizer × LeafIndex))
  | 0, _ => pure none
  | attempts + 1, randomizer => do
      match ← grindingAttempt π secretKey message randomizer with
      | some leafIndex => return some (randomizer, leafIndex)
      | none => grindRandomizer secretKey message attempts (randomizer + 1)

/-- `Sign` (`sign`, `scheme.rs`): derive the randomizer base `R0` of the message (one hash), scan
`R0, R0 + 1, ...` into the kept subtree, compute the digest, open the forest, sign its key (the
sixteen level-3 nodes) with WOTS+C at `e = idx` and attach the path. -/
def sign (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  -- the randomizer base `S || m` (`TWEAK_RANDOMIZER = 7`)
  let base ← th π secretKey.parameter (tweakFields 7 0 0 0)
    (littleEndianBytes 32 secretKey.schemeSeed ++ littleEndianBytes 32 message)
  let some (randomizer, _) ← grindRandomizer π secretKey message digestAttemptLimit base
    | return none
  let digest ← messageDigest π secretKey.parameter message randomizer
  let leafIndex := digestLeafIndex digest
  let opening ← forestOpen π secretKey.parameter leafIndex (digestCoordinateSelections digest)
      secretKey.schemeSeed
  let key ← forestKey π secretKey.parameter leafIndex secretKey.schemeSeed
  let some (counter, values) ← otsSign π secretKey.parameter leafIndex secretKey.schemeSeed
      key | return none
  let path ← treePath π secretKey.parameter secretKey.schemeSeed leafIndex
  return some ⟨randomizer, opening, counter, values, path⟩

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

variable [KeyShape]

/-- A transcript is valid when it has at most `signatureLimit` requests. -/
abbrev WithinSignatureLimit (log : QueryLog SigningOracleSpec) : Prop := log.length ≤ signatureLimit

end SigningTranscript

/-! ## Security in the random-permutation model -/

namespace RandomPermutationModel

open Common Common.SufCma

variable [KeyShape]

/-- leanSPHINCS in the generic SUF-CMA game, over `π` (`queryPermutation`): the seed, key
generation, the deterministic signer, the verifier, and the winning condition: a valid transcript
without the forgery (`SignerReturnedForgery`).
-/
noncomputable def sufCmaScheme : Scheme MasterSeed PublicKey KeyGenerationAndSigning.SecretKey
    Message (Option Signature) Forgery where
  sampleSeed := sampleMasterSeed
  generateKeys := KeyGenerationAndSigning.keygenFromSeed queryPermutation
  sign sk message := KeyGenerationAndSigning.sign queryPermutation sk message
  verify pk forgery := Verification.verify queryPermutation pk forgery.message forgery.signature
  winningCondition log forgery :=
    decide (SigningTranscript.WithinSignatureLimit log ∧ ¬SignerReturnedForgery id log
        forgery.message forgery.signature)

end RandomPermutationModel

/-! ## The proved lifetimes: `⟨b, N, _⟩`, subtree height `b` and `N` signatures -/

namespace Lifetimes

open Common.SufCma

/-- The full key, `b = 26`. -/
abbrev full : KeyShape := ⟨26, 1383000000, by decide⟩
/-- The key pruned to a kept subtree of height `b = 20`. -/
abbrev pruned20 : KeyShape := ⟨20, 26030000, by decide⟩
/-- The key pruned to a kept subtree of height `b = 14`. -/
abbrev pruned14 : KeyShape := ⟨14, 480900, by decide⟩
/-- The key pruned to a kept subtree of height `b = 13`. -/
abbrev pruned13 : KeyShape := ⟨13, 247000, by decide⟩
/-- The key pruned to a kept subtree of height `b = 12`. -/
abbrev pruned12 : KeyShape := ⟨12, 126900, by decide⟩
/-- The key pruned to a kept subtree of height `b = 10`. -/
abbrev pruned10 : KeyShape := ⟨10, 33490, by decide⟩
/-- The key pruned to a kept subtree of height `b = 8`. -/
abbrev pruned8 : KeyShape := ⟨8, 8830, by decide⟩

/-! ### The end statement -/

/-- **leanSPHINCS in the random-permutation model, at every proved lifetime**: at each subtree
height (`b` = 26, 20, 14, 13, 12, 10, 8, the instances `full`, `pruned20`, …, `pruned8` with their
signature limits), an adversary whose game makes at most `Q` permutation calls, `Q ≥ 1`, forges with
probability at most `(Q + 1) · 2^-127` (`StronglyUnforgeable` at 127 bits). `Q` counts every call on
the game's worst path, the honest signer's included (`QueryCostAtMost` is structural): a signature
costs about `2^35` calls at `b = 26` (`2^32` encoding counters of three calls, `2^33.6`; `treePath`
rebuilding the kept subtree, `2^33.9`; the grinding into the kept subtree is one call at `b = 26`
and up to `2^32` below), so at the largest lifetime, `N ≈ 2^30.4` signatures, `Q ≥ 2^65` and the
bound is about `2^-62`. Proved by `Sphincs.Lifetimes.requestedSecurityRpm`. -/
abbrev LeanSphincsStronglyUnforgeable : Prop :=
  ∀ P ∈ [full, pruned20, pruned14, pruned13, pruned12, pruned10, pruned8],
    StronglyUnforgeable (@RandomPermutationModel.sufCmaScheme P) 127

end Lifetimes

end Sphincs

end
