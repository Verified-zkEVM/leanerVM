module

public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import Statement.LeanSphincs

/-!
# leanSPHINCS with a two-level WOTS forest

The scheme of `SphincsFors.Scheme` (one height-26 tree of WOTS+C keys with 64 chains of length 4,
pruning with surrogate siblings, randomizer grinding, tweakable hash with 16-byte outputs) with the
WOTS+C target sum 123 where it has 120, and the few-time signature under each tree leaf replaced by
a **two-level WOTS forest**:

* 8 independent coordinates; a coordinate is a top Merkle tree of height 4 over 16 super-children,
  hashed up to level 3 only: its two level-3 nodes `t_c[0]`, `t_c[1]` are not hashed into a root. The
  forest key is the sixteen nodes `t_0[0], t_0[1], ..., t_7[0], t_7[1]` themselves, the message WOTS+C
  signs: no hash folds them, and the WOTS+C encoding absorbs them with its counter,
  `Th(enc(e), t_0[0] || t_0[1] || ... || t_7[0] || t_7[1] || ctr)`;
* a sub-tree is a Merkle tree of height 3 over 8 children, hashed up to level 2 only; super-child `s`
  is `Th(super(idx, c, s), m_0[0] || m_0[1] || m_1[0] || m_1[1])` where `m_j[0]`, `m_j[1]` are the two
  level-2 nodes of sub-tree `j`;
* a child is 6 hash chains of length 5: `x_{i,0}` is derived from the seed (one hash of the seed
  gives the two starts `x_{2t,0}` and `x_{2t+1,0}`, its two 16-byte halves), `x_{i,t+1} = Th(x_{i,t})`,
  and the child leaf hashes the 6 chain tops `x_{i,4}`;
* a codeword is a deficit vector `d ∈ {0..4}^6` with `Σ d_i = 5` (246 of them); `lut` is a fixed list
  of 256 of them (`codewordCodes`): the codewords sorted by decreasing `Σ d_i²`, then
  lexicographically, entry `t` being codeword number `t mod 214`;
* one digest call gives `26 + 8 · 26 = 234` bits. The first 16 bytes are the 16 codeword indices
  (byte `2c + j` for sub-tree `j` of coordinate `c`); then, from bit 128, the index (26 bits), the 8
  super-children (4 bits each, from bit 154) and the 16 children (3 bits each, from bit 186, in the
  order `2c + j`). No field lies across two 64-bit words;
* an opening reveals, per coordinate and sub-tree, `x_{i, 4 - d_i}` for the 6 chains and the 3 auth
  nodes of the sub-tree, then the 4 auth nodes of the top tree. The last auth node of a tree is its
  other top node: the verifier folds all levels but the last and hashes the two top nodes, in index
  order, into the hash above.

Everything that is not the forest (parameters, WOTS+C, the tree, pruning, grinding, key generation)
is `SphincsFors.Scheme` verbatim, but for the target sum and the scheme seed: key generation first hashes the key's
seed `S0` into `S = H(leanSPHINCS || S0)`, and everything else derives from `S`. Every other hash
input is `P || A || payload`: the 16-byte public parameter, then the 16-byte address of the call (a
32-bit field `lo`, a 24-bit field `hi`, one byte holding the type and a chain step, then 8 zero
bytes), so the payload starts at byte 32. Forest hashes use types 14 (secret derivation) and 15 to
19, with the instance `idx` in `lo` and the position inside the instance in `hi`; type 20 (`roots`,
the former forest-key hash) is not hashed. The message digest hashes `m || rho` (the root is not
hashed: `P` binds the key), 80 bytes in one block, and the randomizer base `S || m`: the
randomizer, which changes between two grinding attempts, comes last.
-/

open OracleComp OracleSpec ENNReal

namespace Sphincs

@[expose] public section

/-! ## The instance: parameters, types, and hash-input layout -/

export Params (subtreeHeight signatureLimit)

/-! ### Forest parameters and types -/

/-- The deficit sum of a codeword. -/
def codewordSum : Nat := 5

/-! ### The codeword table -/

/-- The table as a rule. The codewords are the base-5 numbers below `5^6` with digit sum 5, in
increasing (that is, lexicographic) order; they are sorted by decreasing sum of squared digits (at
most 17), and entry `t` is codeword number `t mod 214`. -/
def codewordRule : List Nat :=
  let digit (c i : Nat) : Nat := c / 5 ^ i % 5
  let words := (List.range (5 ^ 6)).filter fun c => ((List.range 6).map (digit c)).sum = 5
  let sorted := (List.range 18).reverse.flatMap fun k =>
    words.filter fun c => ((List.range 6).map fun i => digit c i ^ 2).sum = k
  (List.range 256).map fun t => sorted.getD (t % 214) 0

theorem codewordCodes_eq_rule : codewordCodes = codewordRule := by decide +kernel

/-! ### The message digest: one call, 234 bits -/

/-! ### Forest addresses -/

/-! ### The target-sum code

`v = 64` chunks of `w = 2` bits covering the 128 digest bits, and the code is the words of digit sum
`T = 123`. -/

/-! ## The algorithms

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and
signing. Hashing routines work in any monad with access to `HashSpec`. -/

/-- Private uniform sampling and the shared hash oracle. Only hash calls count toward the query budget. -/
abbrev OracleWorld := unifSpec + HashSpec

/-! ### Pruning -/

namespace Seeded

open Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The start of one chain of a one-time key, by its own derivation. The signer calls `otsSecrets`;
this is the value of each of its entries (`Completeness.eval_otsSecrets`). -/
def otsStart (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (seed : MasterSeed) : m Digest := do
  let output ← deriveOutput parameter (.ots lay tree leaf (chainPair chainIdx)) seed
  return hashHalf chainIdx.val output

variable [Params]

end Seeded

namespace Seeded

open Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The start `x_{i,0}` of one chain of a child, by its own derivation. The signer calls
`forestSecrets`; this is the value of each of its entries (`Completeness.eval_forestSecrets`). -/
def forestStart (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (i : FChain) (seed : MasterSeed) : m Digest := do
  let output ← deriveOutput parameter (.forest index c s j a (fchainPair i)) seed
  return hashHalf i.val output

/-- The forest chain value `x_{i,pos}` of a child, by its own derivation. The signer computes the 6
chains of a child from one call of `forestSecrets` (`childLeaf`, `coordOpen`); this is the value of
each of them. -/
def chainValue (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (i : FChain) (seed : MasterSeed) (pos : Nat) : m Digest := do
  let secret ← forestStart parameter index c s j a i seed
  forestWalk parameter index c s j a i 0 pos secret

variable [Params]

end Seeded

end

end Sphincs
