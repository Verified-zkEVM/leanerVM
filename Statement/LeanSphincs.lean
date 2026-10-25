module

public import Statement.LeanXmss
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# leanSPHINCS

The scheme of `crates/signatures/src/lean_sphincs` (`wots.rs`, `forest.rs`, `scheme.rs`; the
addresses in `crates/signatures/src/tweak.rs`), specified in `doc/lean_sphincs`, for any key
shape (`Params`: the kept subtree's height `b` and the signature limit): one tree of height
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

Then the SUF-CMA game of `Statement/RandomPermutation.lean` with the deterministic signer, the
proved lifetimes (`Lifetimes.full`, `pruned20`, …, `pruned8`), and the end statement
`Sphincs.Lifetimes.RequestedSecurityRpm`, proved by `Sphincs.Lifetimes.requestedSecurityRpm`
(`lean_sphincs`). Its budget `Q` counts the honest signer's permutation calls too, at their worst
case: about `2^35` per signature, so at the largest lifetime the bound is about `2^-62`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace Sphincs

/-! ### The instance: parameters, types, and hash-input layout -/

export LeanXmss (digestBits hashOutputBits messageBits publicParameterBits winternitzBits
  chainLength MasterSeed Digest HashOutput Message PublicParameter Randomness Digit ChainStep
  HashInput truncateHash upperHash hashHalf PublicKey bytesLE TweakFields fieldBytes tweakFields
  HashSpec sampleMasterSeed)

def counterBits : Nat := 32
def numChains : Nat := 64
def targetSum : Nat := 123
def numLayers : Nat := 1
def totalHeight : Nat := 26
/-- The height of the only XMSS layer, which bounds its leaf index. -/
def maxLayerHeight : Nat := 26
/-- Randomizers tried per signature (`ctr` is a `u32`), `A_max`. -/
def digestAttemptLimit : Nat := 2 ^ 32
/-- Encoding counters tried per signature, `C_max`. -/
def encodingAttemptLimit : Nat := 2 ^ 32

/-- The key's shape and lifetime: the kept subtree holds `2^subtreeHeight` leaves
(`subtreeHeight = 26` is the full key), and the key signs at most `signatureLimit` messages. -/
class Params where
  subtreeHeight : Nat
  signatureLimit : Nat
  subtreeHeight_le : subtreeHeight ≤ totalHeight

export Params (subtreeHeight signatureLimit)

abbrev Counter := BitVec counterBits
abbrev Layer := Fin numLayers
/-- `idx`, the leaf and the forest instance a digest selects. -/
abbrev Index := Fin (2 ^ totalHeight)
/-- `tau`, always `0`: the scheme has one tree, and a hash address has no tree field. -/
abbrev TreeIndex := Fin 1
/-- `e`, a leaf of the tree. -/
abbrev LeafIndex := Fin (2 ^ maxLayerHeight)
abbrev ChainIndex := Fin numChains
/-- A pair of chains `(2t, 2t + 1)` of a one-time key, `t < 32`: one seed derivation. -/
abbrev ChainPair := Fin 32
abbrev Encoding := ChainIndex → Digit

/-! #### Forest parameters and types -/

/-- Number of coordinates. -/
def forestCoords : Nat := 8
/-- Height of a coordinate's top tree (16 super-children). -/
def topHeight : Nat := 4
/-- Height of a sub-tree (8 children). -/
def subHeight : Nat := 3
/-- Chains per child. -/
def childChains : Nat := 6
/-- The top position of a chain: positions `0 .. 4`. -/
def chainTop : Nat := 4

abbrev Coord := Fin forestCoords
abbrev SuperIdx := Fin (2 ^ topHeight)
abbrev SubIdx := Fin 2
abbrev ChildIdx := Fin (2 ^ subHeight)
abbrev FChain := Fin childChains
/-- A pair of chains `(2t, 2t + 1)` of a forest WOTS key, `t < 3`: one seed derivation. -/
abbrev FPair := Fin 3
/-- A forest chain position, `0 .. 4`. -/
abbrev FPos := Fin (chainTop + 1)
/-- A forest chain step, from position `t` to `t + 1`, `t < 4`. -/
abbrev FStep := Fin chainTop
/-- A codeword: the deficit `d_i ∈ {0..4}` of every chain. -/
abbrev Codeword := FChain → FPos
/-- A codeword index, 8 digest bits. -/
abbrev LutIdx := Fin 256

/-- The layer height, `h = 26`. -/
def layerHeight (_lay : Layer) : Nat := maxLayerHeight

def topLayer : Layer := ⟨0, by decide⟩

/-- `sum_{j < lay} h_j`, the index bits above layer `lay`. -/
def heightAbove (lay : Layer) : Nat := ∑ j : Layer, if j.val < lay.val then layerHeight j else 0

/-- `sum_{j > lay} h_j`, the index bits below layer `lay`. -/
def heightBelow (lay : Layer) : Nat := totalHeight - heightAbove lay - layerHeight lay

/-! #### The codeword table -/

/-- The 256 entries of the codeword table as base-5 numbers with `d_0` the most significant digit; a
codeword listed twice is chosen by two digest values. The table is `codewordRule`
(`codewordCodes_eq_rule`): the codewords sorted by decreasing `Σ d_i²`, then lexicographically, entry
`t` being codeword number `t mod 214`. By digit pattern: the 30 codewords with digits `{4,1}` twice
each; of the 30 with `{3,2}`, 12 twice and 18 once; the 60 with `{3,1,1}` and the 60 with `{2,2,1}`
once; 34 of the 60 with `{2,1,1,1}` once; none of the 6 with `{1,1,1,1,1}`. Written by
`scripts/forest_table.py`. -/
def codewordCodes : List Nat :=
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
def codeDigit (code : Nat) (i : FChain) : FPos :=
  ⟨code / 5 ^ (5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩

/-- `lut t`: entry `t` of the table. -/
def lut (t : LutIdx) : Codeword := codeDigit (codewordCodes.getD t.val 0)

/-! #### The message digest: one call, 234 bits -/

/-- Digest bits of one coordinate: super-child 4, and child 3 and codeword 8 for each sub-tree. -/
def coordBits : Nat := 26

/-- The message digest is `h + 8 · 26 = 234` bits: an index and the fields of 8 coordinates. -/
def messageDigestBits : Nat := totalHeight + forestCoords * coordBits

abbrev MessageDigest := BitVec messageDigestBits

/-- The first 234 bits of the single digest call. -/
def truncateMessageDigest (first : HashOutput) : MessageDigest :=
  first.extractLsb' 0 messageDigestBits

/-- What a digest selects in one coordinate: the super-child, and per sub-tree a child and a codeword
index. -/
structure CoordMark where
  super : SuperIdx
  child : SubIdx → ChildIdx
  word : SubIdx → LutIdx
deriving DecidableEq

/-- The forest key of an instance: the two level-3 nodes of every tree, `(t_c[0], t_c[1])`. It is
not hashed: the WOTS+C encoding absorbs the sixteen nodes (`Concrete.encode`). -/
abbrev ForestKey := Coord → Digest × Digest

/-- The WOTS+C signature and authentication path. -/
structure LayerSignature (lay : Layer) where
  counter : Counter
  chainValues : ChainIndex → Digest
  path : Fin (layerHeight lay) → Digest
deriving DecidableEq

/-- The opening of one sub-tree: the 6 revealed chain values and the 3 auth nodes. -/
structure SubOpening where
  values : FChain → Digest
  path : Fin subHeight → Digest
deriving DecidableEq

/-- The opening of one coordinate: both sub-trees, then the 4 auth nodes of the top tree. -/
structure CoordOpening where
  sub : SubIdx → SubOpening
  top : Fin topHeight → Digest
deriving DecidableEq

/-- The randomizer, the forest opening, and the WOTS+C signature with its path: 4276 bytes. -/
structure Signature where
  randomness : Randomness
  forest : Coord → CoordOpening
  layers : (lay : Layer) → LayerSignature lay
deriving DecidableEq

/-! #### Forest addresses -/

/-- `c + 8 s + 128 j`, a sub-tree of the instance (3 + 4 + 1 bits). -/
def subSlot (c : Coord) (s : SuperIdx) (j : SubIdx) : Nat := c.val + 8 * s.val + 128 * j.val

/-- `c + 8 s + 128 j + 256 a`, a child of the instance (11 bits). -/
def childSlot (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) : Nat :=
  subSlot c s j + 256 * a.val

/-- `c + 8 s + 128 j + 256 a + 2048 i`, a chain of the instance. -/
def chainSlot (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) : Nat :=
  childSlot c s j a + 2048 * i.val

/-- The verification hash domains. Seed derivation uses `KeygenDomain`. Forest levels count from the
leaves: a `subNode` at `level` is the node of sub-tree level `level + 1`, a `topNode` at `level` the
node of top-tree level `level + 1`. The scheme hashes sub-tree levels 1 and 2 and top-tree levels 1
to 3: the address of a tree's root exists and no algorithm uses it. -/
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | fchain (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (t : FStep)
  | childLeaf (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx)
  | subNode (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (level : Fin subHeight) (node : ChildIdx)
  | superChild (index : Index) (c : Coord) (s : SuperIdx)
  | topNode (index : Index) (c : Coord) (level : Fin topHeight) (node : SuperIdx)
  | roots (index : Index)
  | message
deriving DecidableEq

/-- The address of a hash domain: types `TWEAK_CHAIN = 1`, ..., `TWEAK_MSG = 12`, forest types 15 to
20. In the tree `lo` is the leaf (or the node index) and `hi` the chain (or the node level); a chain
step carries its step. In a forest instance `lo` is `idx` and `hi` the packed position; a forest chain
step from position `t` carries step `t`. The layer and the tree, always `0`, are not addressed. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain _ _ leaf chainIdx step => tweakFields 1 step chainIdx leaf
  | .leaf _ _ leaf => tweakFields 2 0 0 leaf
  | .node _ _ level nodeIdx => tweakFields 3 0 level nodeIdx
  | .encoding _ _ leaf => tweakFields 4 0 0 leaf
  | .fchain index c s j a i t => tweakFields 15 t (chainSlot c s j a i) index
  | .childLeaf index c s j a => tweakFields 16 0 (childSlot c s j a) index
  | .subNode index c s j level node =>
      tweakFields 17 0 (subSlot c s j + 256 * (level.val + 1) + 1024 * node.val) index
  | .superChild index c s => tweakFields 18 0 (c.val + 8 * s.val) index
  | .topNode index c level node => tweakFields 19 0 (c.val + 8 * (level.val + 1) + 64 * node.val) index
  | .roots index => tweakFields 20 0 0 index
  | .message => tweakFields 12 0 0 0

/-- The exact 16 address bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The hash input `P || A || payload` of every tweakable hash call and of the message
digest. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ message

/-- `P || A(7, 0, 0) || S || m` (`TWEAK_RANDOMIZER = 7`): the randomizer base of a message. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes ⟨7#5, 0#3, 0#24, 0#32⟩ ++
    bytesLE 32 seed ++ bytesLE 32 message

/-- The pair of chains a chain of a one-time key belongs to. -/
def chainPair (chain : ChainIndex) : ChainPair :=
  ⟨chain.val / 2, by have h : chain.val < 64 := chain.isLt; omega⟩

/-- The pair of chains a chain of a forest WOTS key belongs to. -/
def fchainPair (i : FChain) : FPair :=
  ⟨i.val / 2, by have h : i.val < 6 := i.isLt; omega⟩

/-- `c + 8 s + 128 j + 256 a + 2048 t`, a pair of chains of the instance. -/
def pairSlot (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (pair : FPair) : Nat :=
  childSlot c s j a + 2048 * pair.val

/-- The seed derivations, one hash each. `ots` gives the starts of chains `2t` and `2t + 1` of the
one-time key at a leaf, `forest` the starts `x_{2t,0}` and `x_{2t+1,0}` of chains `2t` and `2t + 1`
of child `(idx, c, s, j, a)`: the two 16-byte halves of the hash. The parameter and a surrogate are
the first 16 bytes of their hash. -/
inductive KeygenDomain where
  | parameter
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (pair : ChainPair)
  | forest (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (pair : FPair)
  | surrogate (level : Fin totalHeight)
deriving DecidableEq

/-- `TWEAK_PARAMETER = 5`, `TWEAK_PRF = 0` (`hi` the pair of chains, `lo` the leaf),
`TWEAK_FOREST_PRF = 14` (`hi` the packed pair of chains, `lo = idx`), `TWEAK_SURROGATE = 13` (`hi`
the level). -/
def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0 0
  | .ots _ _ leaf pair => tweakFields 0 0 pair leaf
  | .forest index c s j a pair => tweakFields 14 0 (pairSlot c s j a pair) index
  | .surrogate level => tweakFields 13 0 level 0

/-- `SEED_TAG`, the 11 ASCII bytes of `leanSPHINCS`. -/
def seedTag : HashInput := [0x6c, 0x65, 0x61, 0x6e, 0x53, 0x50, 0x48, 0x49, 0x4e, 0x43, 0x53]

/-- `leanSPHINCS || S0` (`scheme_seed`), 43 bytes: its hash is the scheme seed `S`, the seed every
other input below derives from. It has no parameter and no address. -/
def schemeSeedInput (seed : MasterSeed) : HashInput :=
  seedTag ++ bytesLE 32 seed

/-- `P || A || S`; parameter derivation uses `P = 0`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (keygenDomainFields domain) ++ bytesLE 32 seed

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

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and
signing. Hashing routines work in any monad with access to `HashSpec`. -/

namespace Concrete

export LeanXmss.Concrete (sequenceFin oracleHash nodePayload)

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `Th(P, tw, M) = Truncate_n(H(P || tw || M))`. -/
def tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

/-! #### The index -/

/-- `tau`, the tree: `0`. -/
def treeIndexAt (_index : Index) (_lay : Layer) : TreeIndex := 0

/-- `e = idx`, the leaf. -/
def leafIndexAt (index : Index) (lay : Layer) : LeafIndex :=
  ⟨index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (le_refl _)⟩

/-! #### The one-time signature -/

/-- A node index at level `0` read as a leaf index. -/
def leafOfNat (value : Nat) : LeafIndex :=
  ⟨value % 2 ^ maxLayerHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- `steps` chain steps from position `start`: the step onto position `start + steps + 1` carries
step `start + steps` (`chain_tweak` with `to = start + steps + 1`). -/
def chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← chainWalk parameter lay tree leaf chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain lay tree leaf chainIdx ⟨start + steps, hstep⟩)
          (bytesLE 16 previous)
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `3 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter lay tree leaf chainIdx digit.val (chainLength - 1 - digit.val) value

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- The one-time leaf: the hash of the `v` chain ends (`wots_leaf_hash`). -/
def leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf lay tree leaf) (leafPayload endpoints)

/-- `t_0[0] || t_0[1] || ... || t_7[0] || t_7[1]`, the forest key as bytes: the level-3 nodes of the 8
top trees. -/
def rootsPayload (tops : ForestKey) : HashInput :=
  (List.ofFn tops).flatMap fun pair => nodePayload pair.1 pair.2

/-- `Enc(P, e, K, c)`: hash the forest key's sixteen nodes, then the counter, under the leaf's encoding
tweak, and decode. There is no forest-key hash: the counter falls in the last block of this one
(`P || A || K || c`, 292 bytes). -/
def encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : ForestKey) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf)
    (rootsPayload message ++ bytesLE 4 counter)
  return TargetSum.decodeDigest digest

/-- `Ots.leaf` (`wots_recover`): the verifier's leaf, or nothing if the counter does not encode the message. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : ForestKey) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value

/-! #### The tree -/

/-- `Tree.fold` (`tree_fold`): fold a leaf and a path into the root. -/
def treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← treeFold parameter lay tree leaf path levels value
      let sibling := path levels
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload current sibling)

/-! #### The forest -/

/-- `steps` forest chain steps from position `start`; the step onto position `start + steps + 1`
carries step `start + steps`. -/
def forestWalk (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (i : FChain) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← forestWalk parameter index c s j a i start steps value
      if hstep : start + steps < chainTop then
        tweakableHash parameter (.fchain index c s j a i ⟨start + steps, hstep⟩) (bytesLE 16 previous)
      else
        pure 0

/-- The verifier's half of a forest chain: from position `4 - d` walk `d` steps. -/
def forestRecoverChain (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (i : FChain) (deficit : FPos) (value : Digest) : m Digest :=
  forestWalk parameter index c s j a i (chainTop - deficit.val) deficit.val value

/-- `x_{0,4} || ... || x_{5,4}`. -/
def childPayload (ends : FChain → Digest) : HashInput :=
  (List.ofFn ends).flatMap (bytesLE 16)

/-- The child leaf: the hash of the 6 chain tops. -/
def childLeafHash (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (ends : FChain → Digest) : m Digest :=
  tweakableHash parameter (.childLeaf index c s j a) (childPayload ends)

/-- The child leaf an opening at codeword `word` reaches. -/
def childRecover (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (word : Codeword) (values : FChain → Digest) : m Digest := do
  let ends ← sequenceFin fun i => forestRecoverChain parameter index c s j a i (word i) (values i)
  childLeafHash parameter index c s j a ends

/-- Fold a child leaf and a sub-tree path into the sub-tree root. -/
def subFold (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (path : Fin subHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← subFold parameter index c s j a path levels value
      if hlevel : levels < subHeight then
        let sibling := path ⟨levels, hlevel⟩
        let node : ChildIdx := ⟨a.val / 2 ^ (levels + 1),
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt⟩
        if a.val.testBit levels then
          tweakableHash parameter (.subNode index c s j ⟨levels, hlevel⟩ node) (nodePayload sibling current)
        else
          tweakableHash parameter (.subNode index c s j ⟨levels, hlevel⟩ node) (nodePayload current sibling)
      else
        pure 0

/-- The two top nodes of a tree in index order, from the one the fold reached and the last path
element: the reached node is node 1 exactly when `bit`, the top bit of the leaf index, is set. -/
def orderTops (bit : Bool) (current sibling : Digest) : Digest × Digest :=
  if bit then (sibling, current) else (current, sibling)

/-- `m_0[0] || m_0[1] || m_1[0] || m_1[1]`, the level-2 nodes of the two sub-trees. -/
def superPayload (tops : SubIdx → Digest × Digest) : HashInput :=
  nodePayload (tops 0).1 (tops 0).2 ++ nodePayload (tops 1).1 (tops 1).2

/-- The super-child `Th(super(idx, c, s), m_0[0] || m_0[1] || m_1[0] || m_1[1])`: the hash of the two
level-2 nodes of each of its sub-trees. A sub-tree has no root hash. -/
def superHash (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (tops : SubIdx → Digest × Digest) : m Digest :=
  tweakableHash parameter (.superChild index c s) (superPayload tops)

/-- Fold a super-child and a top path into the coordinate root. -/
def topFold (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (path : Fin topHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← topFold parameter index c s path levels value
      if hlevel : levels < topHeight then
        let sibling := path ⟨levels, hlevel⟩
        let node : SuperIdx := ⟨s.val / 2 ^ (levels + 1),
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) s.isLt⟩
        if s.val.testBit levels then
          tweakableHash parameter (.topNode index c ⟨levels, hlevel⟩ node) (nodePayload sibling current)
        else
          tweakableHash parameter (.topNode index c ⟨levels, hlevel⟩ node) (nodePayload current sibling)
      else
        pure 0

/-- The last level of a sub-tree path: the other level-2 node. -/
def subTopLevel : Fin subHeight := ⟨subHeight - 1, by decide⟩

/-- The last level of a top-tree path: the other level-3 node. -/
def topTopLevel : Fin topHeight := ⟨topHeight - 1, by decide⟩

/-- The two level-3 nodes of a coordinate's top tree that an opening reaches. In each sub-tree the
child leaf is folded 2 levels and the last path element is the other level-2 node; the four level-2
nodes hash into the super-child, which is folded 3 levels, and the last top path element is the
other level-3 node. -/
def coordRecover (parameter : PublicParameter) (index : Index) (c : Coord) (mark : CoordMark)
    (opening : CoordOpening) : m (Digest × Digest) := do
  let tops ← sequenceFin fun j => do
    let leaf ← childRecover parameter index c mark.super j (mark.child j) (lut (mark.word j))
      (opening.sub j).values
    let node ← subFold parameter index c mark.super j (mark.child j) (opening.sub j).path (subHeight - 1) leaf
    return orderTops ((mark.child j).val.testBit (subHeight - 1)) node ((opening.sub j).path subTopLevel)
  let super ← superHash parameter index c mark.super tops
  let node ← topFold parameter index c mark.super opening.top (topHeight - 1) super
  return orderTops (mark.super.val.testBit (topHeight - 1)) node (opening.top topTopLevel)

/-- `Fts.recover`: the forest key an opening reaches, the sixteen level-3 nodes. A top tree has no
root hash, and the key has no hash: the WOTS+C encoding absorbs it. -/
def forestRecover (parameter : PublicParameter) (index : Index) (marks : Coord → CoordMark)
    (opening : Coord → CoordOpening) : m ForestKey :=
  sequenceFin fun c => coordRecover parameter index c (marks c) (opening c)

/-! #### The message digest -/

/-- `m || rho`, what the message digest hashes after the parameter and the address: the input
`P || A || m || rho` is 80 bytes, one block. The root is not hashed (`P` binds the key); the
argument is kept for the callers. -/
def messageDigestPayload (_root : Digest) (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 32 message ++ bytesLE 16 randomness

/-- The single untruncated digest call (`digest_block`). -/
def messageDigestCall (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m HashOutput :=
  oracleHash (tweakableHashInput parameter .message (messageDigestPayload root message randomness))

/-- Bit offset of the index: the low 26 bits of the last 16 bytes of the digest. -/
def indexOffset : Nat := 128

/-- `idx`, the 26 bits of the digest from bit 128. -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' indexOffset totalHeight).toFin

/-- The leaf index of the digest call (`index_of_block`). -/
def blockIndex (first : HashOutput) : Index :=
  (first.extractLsb' indexOffset totalHeight).toFin

/-- `Digest(P, m, rho)` (`message_digest`): the single call, truncated to 234 bits. The root is not
an input of the hash. -/
def messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let first ← messageDigestCall parameter root message randomness
  return truncateMessageDigest first

/-- Bit offset of the codeword index of sub-tree `j` of coordinate `c`: byte `2c + j` of the digest. -/
def wordOffset (c : Coord) (j : SubIdx) : Nat := 8 * (2 * c.val + j.val)

/-- Bit offset of coordinate `c`'s super-child (4 bits), after the index. -/
def superOffset (c : Coord) : Nat := 154 + 4 * c.val

/-- Bit offset of the child of sub-tree `j` of coordinate `c` (3 bits), after the super-children. -/
def childOffset (c : Coord) (j : SubIdx) : Nat := 186 + 3 * (2 * c.val + j.val)

/-- The coordinate fields of a digest. -/
def digestMarks (digest : MessageDigest) : Coord → CoordMark := fun c =>
  { super := (digest.extractLsb' (superOffset c) topHeight).toFin
    child := fun j => (digest.extractLsb' (childOffset c j) subHeight).toFin
    word := fun j => (digest.extractLsb' (wordOffset c j) 8).toFin }

/-! #### Verification -/

/-- Read a layer's path, returning zero outside its height. -/
def signaturePath (signature : Signature) (lay : Layer) (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then (signature.layers lay).path ⟨level, hlevel⟩ else 0

/-- The tree walk of the one layer: `remaining + 1` enters at layer `remaining`, whose WOTS+C key
signs the forest key; its fold is the value compared against the public root. -/
def verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → ForestKey → m (Option Digest)
  | 0, _ => pure none
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        let part := signature.layers lay
        let some value ← otsLeaf parameter lay tree leaf message part.counter part.chainValues
          | return none
        let root ← treeFold parameter lay tree leaf (signaturePath signature lay) (layerHeight lay) value
        return some root
      else
        pure none

/-- `Ver(pk, m, sigma)`: recompute the digest, recover the forest key, recover the one-time leaf,
fold the path and compare with the root. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  let index := digestIndex digest
  let forestKey ← forestRecover publicKey.parameter index (digestMarks digest) signature.forest
  let some root ← verifyLayers publicKey.parameter index signature numLayers forestKey | return false
  return decide (root = publicKey.root)

/-! #### Signing -/

/-- The scheme has one tree, at index `0`. -/
def rootTree : TreeIndex := 0

/-- Run the layer, stopping on failure. -/
def sequenceLayers {α : Layer → Type}
    (computation : (lay : Layer) → m (Option (α lay))) : m (Option ((lay : Layer) → α lay)) := do
  let some top ← computation topLayer | return none
  return some (Fin.cases top (fun i => Fin.elim0 i))

attribute [irreducible] verify

end Concrete

/-! #### Pruning -/

section Pruning

variable [Params]

/-- `s`, the kept subtree: the low `h - b` bits of `P`, read as a little-endian number (`0` for a
full key). -/
def subtreePosition (parameter : PublicParameter) : Nat :=
  parameter.toNat % 2 ^ (totalHeight - subtreeHeight)

/-- The kept subtree holds leaves `s * 2^b .. (s + 1) * 2^b` (`XmssTree::contains`). -/
def Landed (parameter : PublicParameter) (index : Index) : Prop :=
  index.val / 2 ^ subtreeHeight = subtreePosition parameter

instance (parameter : PublicParameter) (index : Index) : Decidable (Landed parameter index) :=
  inferInstanceAs (Decidable (index.val / 2 ^ subtreeHeight = subtreePosition parameter))

end Pruning

/-- One seed derivation, first 16 bytes: the parameter and the surrogates. -/
def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

/-- One seed derivation, all 32 bytes (`th_pair`): the starts of two chains are its two halves. -/
def deriveOutput {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m HashOutput :=
  Concrete.oracleHash (keygenHashInput parameter domain seed)

def deriveRandomizer {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) : m Randomness := do
  return truncateHash (← Concrete.oracleHash (randomizerHashInput parameter seed message))

/-- `scheme_seed`: the scheme seed `S`, the whole hash of `leanSPHINCS || S0`. -/
def schemeSeed {m : Type → Type} [Monad m] [HasQuery HashSpec m] (seed : MasterSeed) : m MasterSeed :=
  Concrete.oracleHash (schemeSeedInput seed)

namespace Seeded

open Concrete

export LeanXmss.Seeded (SecretKey)

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `wots_secrets`: the starts of the 64 chains of the one-time key at a leaf, from 32 seed
derivations. Chains `2t` and `2t + 1` start at the two halves of derivation `t`. -/
def otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let outputs ← sequenceFin fun pair : ChainPair => deriveOutput parameter (.ots lay tree leaf pair) seed
  return fun chainIdx => hashHalf chainIdx.val (outputs (chainPair chainIdx))

def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let secrets ← otsSecrets parameter lay tree leaf seed
  sequenceFin fun chainIdx =>
    chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secrets chainIdx)

def otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : ForestKey) :
    Nat → Nat → m (Option (Counter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let secrets ← otsSecrets parameter lay tree leaf seed
          let values ← sequenceFin fun chainIdx =>
            chainWalk parameter lay tree leaf chainIdx 0 (encoding chainIdx).val (secrets chainIdx)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter lay tree leaf seed message attempts (counter + 1)

/-- `wots_sign`: the least admissible counter, then the opened chain values. -/
def otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : ForestKey) :
    m (Option (Counter × (ChainIndex → Digest))) :=
  otsSignFrom parameter lay tree leaf seed message encodingAttemptLimit 0

/-- A node of the tree, computed from the one-time keys below it. -/
def treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← oneTimePublicKey parameter lay tree leaf seed
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← treeNode parameter lay tree seed level (2 * nodeIdx)
      let right ← treeNode parameter lay tree seed level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)

/-- The starts `x_{i,0}` of the 6 chains of a child, from 3 seed derivations. Chains `2t` and
`2t + 1` start at the two halves of derivation `t`. -/
def forestSecrets (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (seed : MasterSeed) : m (FChain → Digest) := do
  let outputs ← sequenceFin fun pair : FPair => deriveOutput parameter (.forest index c s j a pair) seed
  return fun i => hashHalf i.val (outputs (fchainPair i))

/-- The leaf of a child, from its 6 chain tops. -/
def childLeaf (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (seed : MasterSeed) : m Digest := do
  let secrets ← forestSecrets parameter index c s j a seed
  let ends ← sequenceFin fun i => forestWalk parameter index c s j a i 0 chainTop (secrets i)
  childLeafHash parameter index c s j a ends

/-- A node of a sub-tree at tree level `level`. -/
def subNode (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (seed : MasterSeed) : Nat → Nat → m Digest
  | 0, node => childLeaf parameter index c s j ⟨node % 2 ^ subHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ seed
  | level + 1, node => do
      let left ← subNode parameter index c s j seed level (2 * node)
      let right ← subNode parameter index c s j seed level (2 * node + 1)
      if hlevel : level < subHeight then
        tweakableHash parameter (.subNode index c s j ⟨level, hlevel⟩
          ⟨node % 2 ^ subHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) (nodePayload left right)
      else
        pure 0

/-- A super-child, from the two level-2 nodes of each of its two sub-trees. -/
def superNode (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (seed : MasterSeed) : m Digest := do
  let tops ← sequenceFin fun j => do
    let left ← subNode parameter index c s j seed (subHeight - 1) 0
    let right ← subNode parameter index c s j seed (subHeight - 1) 1
    return (left, right)
  superHash parameter index c s tops

/-- A node of a coordinate's top tree at tree level `level`. -/
def topNode (parameter : PublicParameter) (index : Index) (c : Coord) (seed : MasterSeed) :
    Nat → Nat → m Digest
  | 0, node => superNode parameter index c ⟨node % 2 ^ topHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ seed
  | level + 1, node => do
      let left ← topNode parameter index c seed level (2 * node)
      let right ← topNode parameter index c seed level (2 * node + 1)
      if hlevel : level < topHeight then
        tweakableHash parameter (.topNode index c ⟨level, hlevel⟩
          ⟨node % 2 ^ topHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) (nodePayload left right)
      else
        pure 0

/-- The forest key of instance `idx`: the two level-3 nodes of every coordinate (no hash). -/
def forestKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed) : m ForestKey :=
  sequenceFin fun c => do
    let left ← topNode parameter index c seed (topHeight - 1) 0
    let right ← topNode parameter index c seed (topHeight - 1) 1
    return (left, right)

/-- The opening of one coordinate at a mark. The last element of each path (level 2 of a sub-tree,
level 3 of the top tree) is the top node the verifier does not compute. -/
def coordOpen (parameter : PublicParameter) (index : Index) (c : Coord) (mark : CoordMark)
    (seed : MasterSeed) : m CoordOpening := do
  let sub ← sequenceFin fun j => do
    let secrets ← forestSecrets parameter index c mark.super j (mark.child j) seed
    let values ← sequenceFin fun i =>
      forestWalk parameter index c mark.super j (mark.child j) i 0
        (chainTop - (lut (mark.word j) i).val) (secrets i)
    let path ← sequenceFin fun level : Fin subHeight =>
      subNode parameter index c mark.super j seed level.val (Nat.xor ((mark.child j).val / 2 ^ level.val) 1)
    return (⟨values, path⟩ : SubOpening)
  let top ← sequenceFin fun level : Fin topHeight =>
    topNode parameter index c seed level.val (Nat.xor (mark.super.val / 2 ^ level.val) 1)
  return ⟨sub, top⟩

/-- `Fts.sign`: the opening of every coordinate. -/
def forestOpen (parameter : PublicParameter) (index : Index) (marks : Coord → CoordMark)
    (seed : MasterSeed) : m (Coord → CoordOpening) :=
  sequenceFin fun c => coordOpen parameter index c (marks c) seed

variable [Params]

/-- The surrogate sibling at `level >= b`, derived from the seed (`TWEAK_SURROGATE`). Honest calls
have `level < h`. -/
def surrogate (parameter : PublicParameter) (seed : MasterSeed) (level : Nat) : m Digest :=
  if hlevel : level < totalHeight then deriveKey parameter (.surrogate ⟨level, hlevel⟩) seed else pure 0

/-- The node at level `b + steps` above the kept subtree: the subtree root folded with the first
`steps` surrogates (`XmssTree::from_leaves`). -/
def spineNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) :
    Nat → m Digest
  | 0 => treeNode parameter lay tree seed subtreeHeight (subtreePosition parameter)
  | steps + 1 => do
      let below ← spineNode parameter lay tree seed steps
      let sibling ← surrogate parameter seed (subtreeHeight + steps)
      let nodeIdx := subtreePosition parameter / 2 ^ steps
      if nodeIdx.testBit 0 then
        tweakableHash parameter (.node lay tree (subtreeHeight + steps + 1) (nodeIdx / 2))
          (nodePayload sibling below)
      else
        tweakableHash parameter (.node lay tree (subtreeHeight + steps + 1) (nodeIdx / 2))
          (nodePayload below sibling)

/-- The root: the spine's top. -/
def treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : m Digest :=
  spineNode parameter lay tree seed (totalHeight - subtreeHeight)

/-- The authentication path of a kept leaf (`XmssTree::path`): subtree nodes below level `b`,
surrogates from level `b` on. -/
def treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) : m (Fin (layerHeight lay) → Digest) :=
  sequenceFin fun level =>
    if level.val < subtreeHeight then
      treeNode parameter lay tree seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      surrogate parameter seed level.val

/-- Key generation from the scheme seed `S`: derive the public parameter, which places the kept
subtree, and build the root. -/
def keygenFromMaster (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let parameter ← deriveKey 0 .parameter seed
  let root ← treeRoot parameter topLayer rootTree seed
  return (⟨root, parameter⟩, ⟨seed, parameter, root⟩)

/-- `Gen` (`key_gen_from_seed`): hash the key's seed `S0` into the scheme seed `S`, then generate
from `S`. -/
def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let master ← schemeSeed seed
  keygenFromMaster master

/-- One grinding attempt: the leaf index of the digest call (`digest_index`). -/
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option Index) := do
  let first ← messageDigestCall secretKey.parameter secretKey.root message randomness
  if Landed secretKey.parameter (blockIndex first) then
    return some (blockIndex first)
  else
    return none

def layerMessage (secretKey : SecretKey) (index : Index) (_lay : Layer) : m ForestKey :=
  forestKey secretKey.parameter index secretKey.seed

def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) : m (Option (LayerSignature lay)) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let message ← layerMessage secretKey index lay
  let some (counter, values) ← otsSign secretKey.parameter lay tree leaf secretKey.seed message
    | return none
  let path ← treePath secretKey.parameter lay tree secretKey.seed leaf
  return some ⟨counter, values, path⟩

/-- Try `randomness, randomness + 1, ...`, stopping at the first that lands in the kept subtree. -/
def signDigestLoop (secretKey : SecretKey) (message : Message) : Nat → Randomness →
    m (Option (Randomness × Index))
  | 0, _ => pure none
  | attempts + 1, randomness => do
      match ← signAttempt secretKey message randomness with
      | some index => return some (randomness, index)
      | none => signDigestLoop secretKey message attempts (randomness + 1)

/-- `Sign`: derive the randomizer base `R0` of the message (one hash), scan `R0, R0 + 1, ...` into
the kept subtree, compute the digest, open the forest, sign its key (the sixteen level-3 nodes) with
WOTS+C and attach the path. -/
def sign (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  let base ← deriveRandomizer secretKey.parameter secretKey.seed message
  let some (randomness, _) ← signDigestLoop secretKey message digestAttemptLimit base
    | return none
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  let index := digestIndex digest
  let opening ← forestOpen secretKey.parameter index (digestMarks digest) secretKey.seed
  let some layers ← sequenceLayers (fun lay => signLayer secretKey index lay) | return none
  return some ⟨randomness, opening, layers⟩

end Seeded

/-! ## Forgeries and transcripts -/

structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq

abbrev SigningSpec := Message →ₒ Option Signature

namespace SigningTranscript

variable [Params]

def Valid (log : QueryLog SigningSpec) : Prop := log.length ≤ signatureLimit

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))

def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))

end SigningTranscript

/-! ## Security in the random-permutation model -/

namespace Rpm

open Common Common.SufCma

variable [Params]

/-- leanSPHINCS in the generic SUF-CMA game: the seed, key generation, the deterministic signer,
the verifier, and the winning condition (`SigningTranscript`, above). -/
noncomputable def scheme :
    Scheme HashOutput MasterSeed PublicKey Seeded.SecretKey Message (Option Signature)
      Forgery where
  sample := sampleMasterSeed
  keygen := Seeded.keygenFromSeed
  sign sk message := Seeded.sign sk message
  verify pk forgery := Concrete.verify pk forgery.message forgery.signature
  win log forgery :=
    decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery)

end Rpm

/-! ## The proved lifetimes: `⟨b, N, _⟩`, subtree height `b` and `N` signatures -/

namespace Lifetimes

open Common.SufCma

abbrev full : Params := ⟨26, 1383000000, by decide⟩
abbrev pruned20 : Params := ⟨20, 26030000, by decide⟩
abbrev pruned14 : Params := ⟨14, 480900, by decide⟩
abbrev pruned13 : Params := ⟨13, 247000, by decide⟩
abbrev pruned12 : Params := ⟨12, 126900, by decide⟩
abbrev pruned10 : Params := ⟨10, 33490, by decide⟩
abbrev pruned8 : Params := ⟨8, 8830, by decide⟩

/-! ### The end statement -/

/-- **leanSPHINCS in the random-permutation model, at every proved lifetime**: at each subtree
height (`b` = 26, 20, 14, 13, 12, 10, 8, the instances `full`, `pruned20`, …, `pruned8` with
their signature limits), an adversary whose game makes at most `Q` permutation calls,
`1 ≤ Q ≤ 2^128`, forges with probability at most `(Q + 1) · 2^-127` (`RpmSecure` at 127 bits).
`Q` counts every call on the game's worst path, the honest signer's included (`IsWeightBound` is
structural): a signature costs about `2^35` calls at `b = 26` (`2^32` grinding attempts of one
call, `2^32` encoding counters of three, and `treePath` rebuilding the kept subtree, about
`2^33.9`), so at the largest lifetime, `N ≈ 2^30.4` signatures, `Q ≥ 2^65` and the bound is about
`2^-62`. Proved by `Sphincs.Lifetimes.requestedSecurityRpm`. -/
abbrev RequestedSecurityRpm : Prop :=
  RpmSecure digestBitVec (@Rpm.scheme full) 127 ∧
  RpmSecure digestBitVec (@Rpm.scheme pruned20) 127 ∧
  RpmSecure digestBitVec (@Rpm.scheme pruned14) 127 ∧
  RpmSecure digestBitVec (@Rpm.scheme pruned13) 127 ∧
  RpmSecure digestBitVec (@Rpm.scheme pruned12) 127 ∧
  RpmSecure digestBitVec (@Rpm.scheme pruned10) 127 ∧
  RpmSecure digestBitVec (@Rpm.scheme pruned8) 127

end Lifetimes

end Sphincs

end
