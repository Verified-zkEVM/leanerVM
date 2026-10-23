import LeanVM.Spec.Guest
import LeanVM.Spec.NodeWith
import LeanVMTests.Spec.NodeVectors

/-!
# The deferring verifier and the node's statement: inhabitants, known answers and mutations

* `Evaluations.claimed` answers with the claimed value at the claimed point and rejects
  elsewhere, and the deferring verifier's seed is the deployed verifier's.
* The deferring verifier rejects garbage, and so does the deployed one on the same proof.
* `DeferredClaim.Shaped` rejects a bytecode point one coordinate short, which the digest alone
  cannot tell apart (`statementDigest` carries no lengths: the short claim's odd cell count is
  paired with a zero cell).
* Known answers for the statement's encodings (`xmssListDigest`, `sphincsListDigest`,
  `signersDigest`, `daListDigest`, `statementDigest`), the batching transcript's seed
  (`batchSeed`) and the batching of two children (`batch`): computed by an independent Python
  transcription of `claim_list_digest`, `signers_hash`, `statement_digest`, `FiatShamirState` and
  `aggregate_deferred_claims` (`crates/rec_aggregation/src/aggregation.rs`,
  `crates/fiat_shamir/src/lib.rs` at leanVM `3375f7a137c50b803f3416f6466b5d4e0719708a`) over the
  Python verifier's Keccak and field arithmetic (`python-verifier/verifier.py`). The batching's
  hints are the Python's honest sumcheck messages; Lean's transcript must squeeze the same
  challenges for the claim to close at the Python's point, which is a true claim on the table.
  Mutations: a wrong final value, or a child's false claim, and the batching rejects.
* `batch` on no children is inhabited; `verifyAggregate`'s vector-digest condition rejects a
  digest other than the root's.
* The Rust vectors (`NodeVectors.lean`, written by `scripts/guest-export` from the deployed
  `crates/rec_aggregation/src/aggregation.rs` at the guest's shape, `bytecode_vars = 23`): the
  statement's encodings and the batching of two children's true claims on the guest's stacked
  bytecode are the Spec's, and a batching hint off by one rejects. What is slow in the
  interpreter, `lake exe node-vectors` (`cli/NodeVectors.lean`) checks compiled: that their seed
  is `deployedSeed guest` (the Keccak-256 IV of the guest's `2^23` bytecode words), and the DA
  roots' vector digests.
-/

namespace LeanVMTests.Spec.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash LeanVM.Node

/-- A field element from its limbs. -/
def e (c0 c1 c2 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1) (K.ofBits c2)

/-- The UTF-8 bytes of a string. -/
def utf8 (s : String) : List UInt8 := s.toUTF8.toList

/-! ## The deferring verifier -/

/-- A claim on the fixed polynomial. -/
def c : FixedClaims := ⟨[1, 0], 1⟩

example (words : List K) :
    (Evaluations.claimed c).bytecode words c.bytecodePoint = .ret c.bytecodeValue := by
  simp [Evaluations.claimed, Prog.require]; rfl

-- Mutation: at another point the claimed evaluation rejects.
example (words : List K) : (Evaluations.claimed c).bytecode words [0, 0] = .fail := by
  simp [Evaluations.claimed, Prog.require, c]; rfl

/-- The deferring verifier's seed is the deployed verifier's, from the deployed IV. -/
example (bytecode : List K) (publicInput : Digest) :
    seed bytecode publicInput = keccakF (seedInput (fiatShamirIv bytecode) publicInput) := rfl

/-- A bytecode of 32 words. -/
def bytecode : List K := (List.range 32).map K.ofBits

#guard verifyDeferred bytecode (fiatShamirIv bytecode) default c ⟨[], []⟩ = false
#guard verify bytecode default ⟨[], []⟩ = false

/-! ## The deferred claim's shape -/

/-- A deferred claim of the bytecode's shape, at zero. -/
def zeroClaim : DeferredClaim := ⟨List.replicate 5 0, 0⟩

/-- A deferred claim one coordinate short. -/
def shortClaim : DeferredClaim := ⟨List.replicate 4 0, 0⟩

example : zeroClaim.Shaped bytecode ∧ zeroClaim.AtZero bytecode := by
  simp [DeferredClaim.Shaped, DeferredClaim.AtZero, zeroClaim, bytecode]; decide

/-- No claims. -/
def noClaims : Claims := ⟨[], [], []⟩

-- Mutation: a bytecode point one coordinate short has the same digest (its five cells are paired
-- with a zero cell, the six zero cells of `zeroClaim`), and `Shaped` is what rejects it.
#guard statementDigest default ⟨noClaims, zeroClaim⟩ = statementDigest default ⟨noClaims, shortClaim⟩

example : ¬ shortClaim.Shaped bytecode := by
  simp [DeferredClaim.Shaped, shortClaim, bytecode]; decide

/-- The digest is Keccak-256 of the preimage the collision candidates name. -/
example (seed : Digest) (s : NodeStatement) :
    statementDigest seed s = keccak256 (statementPreimage seed s) := rfl

/-! ## The statement's encodings: known answers -/

/-- The leanXMSS claims. -/
def xmss : List XmssClaim :=
  [(⟨BitVec.ofNat 128 0x0123456789abcdef0011223344556677,
      BitVec.ofNat 128 0x8899aabbccddeeff0f1e2d3c4b5a6978⟩,
    BitVec.ofNat 256 0xdeadbeef00112233445566778899aabbccddeeff102132435465768798a9bacb),
   (⟨BitVec.ofNat 128 0x77665544332211000123456789abcdef,
      BitVec.ofNat 128 0x0f0e0d0c0b0a09080706050403020100⟩, BitVec.ofNat 256 1)]

/-- The leanSPHINCS claims. -/
def sphincs : List SphincsClaim :=
  [(⟨BitVec.ofNat 128 0xfedcba98765432100123456789abcdef, BitVec.ofNat 128 1⟩,
    BitVec.ofNat 256 (2 ^ 256 - 1))]

/-- The DA claims: two roots and vector digests. -/
def da : List DaClaim :=
  [(keccak256 (utf8 "root0"), keccak256 (utf8 "vd0")),
    (keccak256 (utf8 "root1"), keccak256 (utf8 "vd1"))]

/-- A seed. -/
def seed0 : Digest := keccak256 (utf8 "seed")

/-- A deferred claim: five coordinates, one with a top limb, and a value. -/
def defer0 : DeferredClaim :=
  ⟨[e 1 2 3, e 4 5 6, e 7 8 9, e 10 11 12, e 0xffffffffffffffff 0 1], e 13 14 15⟩

#guard xmssListDigest xmss =
  #v[0x414fd0b2c209e3b8, 0x6538b0954fa462a9, 0xe56f9cc0c9d4fdc7, 0xa490bc2e93724856]

#guard sphincsListDigest sphincs =
  #v[0xe8d78086d65bb925, 0x7ace3a6c82dbaf4e, 0xbf24729b60a19887, 0xc1ffa4b8c5dee59e]

#guard signersDigest xmss sphincs =
  #v[0x578e3156cf55ddb9, 0x0752842f4119e935, 0xecc3dd9961739c13, 0x55c151b417effdac]

/- An empty list hashes the empty string. -/
#guard xmssListDigest [] =
  #v[0x3c23f7860146d2c5, 0xc003c7dcb27d7e92, 0x3b2782ca53b600e5, 0x70a4855d04d8fa7b]

#guard daListDigest da =
  #v[0x67506ad9379ddcc3, 0xa767051b758c2b81, 0x474eb5e9359b5a34, 0x2b312eb8ef5489da]

#guard statementDigest seed0 ⟨⟨xmss, sphincs, da⟩, defer0⟩ =
  #v[0xbb11042ec04d4824, 0xf6d5bf5ee4c7123c, 0x0e7010e5449877bc, 0x5815b6affbacaa7e]

/- The same claim one coordinate short: five cells, paired with a zero cell. -/
#guard statementDigest seed0 ⟨⟨xmss, sphincs, da⟩, { defer0 with
    bytecodePoint := defer0.bytecodePoint.take 4 }⟩ =
  #v[0x05e8a745fea55d18, 0x7c4dc87271b326da, 0x83d47fbc1faa0995, 0xfecc538bbfca72bf]

-- Mutation: other lists give another digest.
#guard signersDigest [] [] ≠ signersDigest xmss sphincs

/-! ## The batching: known answers and mutations -/

/- `FiatShamirState::from_label(RECURSION_AGG_LABEL)`'s state, whose lanes `16..25` the guest
bakes as `AGG_SEED_*`. -/
#guard batchSeed = #v[0x870d207a806c795a, 0xb4b4ddd8d965e271, 0xf4d25a66d674ca27,
  0xd58527e821d50d69, 0xe8b3b32bc6b41ca0, 0x1ac6405ae5e1c26c, 0x25100272f63a0add,
  0xddac48119a39ccbb, 0x2f557d8fdc241fb9, 0xb03075526083a5c6, 0x0ae457bd1e0fd49d,
  0xa690dfcc98cbc36e, 0xc8bc6a708f4be81f, 0xaf078f39833eded4, 0xfca5d5aea8d67de1,
  0x160ed37a53dc979a, 0x15afc20f66b0d5b9, 0x6a647807f52d7266, 0xa5800c0973e6ab80,
  0xc99f802c9aef9edd, 0xd2dc01646a279b0e, 0x5d0c9da7c6a96b8d, 0x971016a864ec6d1a,
  0x92ef5eb709b9fa89, 0x02359fac99c1f265]

/-- A table of eight words, the claims' polynomial. -/
def table : List E := (List.range 8).map fun i ↦ ofK (K.ofBits (3 * i + 1))

/-- The table's value at a point. -/
def mle (point : List E) : E := multilinearEval table point

/-- Child `i`: its public input, a true fresh claim and a true carried claim. -/
def child (i : ℕ) : ChildClaims :=
  let p := [e (i + 1) 2 0, e 5 i 7, e 0 0 (i + 9)]
  let q := [e i 1 1, e 2 2 i, e (i + 3) 0 0]
  ⟨keccak256 [i.toUInt8], ⟨p, mle p⟩, ⟨q, mle q⟩⟩

/-- Two children. -/
def children : List ChildClaims := [child 0, child 1]

/- The Python's value of child 0's fresh claim. -/
#guard (child 0).fresh.bytecodeValue = e 0x3b2 0x222 0x7ee

/-- The Python's honest hints. -/
def hints : BatchHints :=
  ⟨[(e 0x8c2d70f60243e79a 0xc604221e4e6170ac 0x4b961ef2ea7dca3b,
      e 0xaab71fc1c2d8c201 0xf2a5da88ee7af659 0xf55524d6fa065909),
    (e 0x9a0cfdfeb1def484 0xfe0a219b5b61f5b8 0x82451ce6ffe24475,
      e 0x89779b56b548eb94 0x4f644d24c57655d2 0x327b5ce4f7f71108),
    (e 0x8249c1015b71778c 0x3c56e312cd234c80 0x9c162cfb9963f7c7,
      e 0x20ed2dfd4e8f49d9 0xd9144a11462fbd34 0x5dfd591542aa9e89)],
    e 0xa251703b3383e44b 0x42efb5fc2363771d 0x2c293884ef51233d⟩

/-- The Python's batched point. -/
def batchedPoint : List E :=
  [e 0xcf8118b32526c5fb 0xdb85e357e0c4b7b0 0x5e5cded60e5d82b,
    e 0xd0a309bc796bbc3e 0xa6d2913a9b2c5b37 0x884658faa61456ab,
    e 0xe7e169cc4ae17a74 0x3b033358521f3357 0x6fc70155944f8469]

#guard (batch children hints).map (·.bytecodePoint) = some batchedPoint
#guard (batch children hints).map (·.bytecodeValue) = some hints.bytecodeValue

/- The batched claim is true of the table. -/
#guard mle batchedPoint = hints.bytecodeValue

/- The batching with Keccak-f as a parameter, from `batchSeed`, is the same. -/
#guard (Id.run (batchWith (m := Id) keccakF batchSeed children hints)).map (·.bytecodePoint) =
  some batchedPoint

-- Mutation: a wrong final value.
#guard (batch children { hints with bytecodeValue := hints.bytecodeValue + 1 }).isNone

-- Mutation: child 1's carried claim false, the same hints.
#guard (batch [child 0, { child 1 with carried := { (child 1).carried with
  bytecodeValue := (child 1).carried.bytecodeValue + 1 } }] hints).isNone

-- Mutation: the children swapped, the same hints.
#guard (batch [child 1, child 0] hints).isNone

/- No children: the empty sumcheck closes on the zero claim. -/
#guard (batch [] ⟨[], 0⟩).isSome

/-! ## The Rust vectors -/

#guard xmssListDigest NodeVectors.xmss = NodeVectors.xmssListDigest
#guard sphincsListDigest NodeVectors.sphincs = NodeVectors.sphincsListDigest
#guard signersDigest NodeVectors.xmss NodeVectors.sphincs = NodeVectors.signersDigest
#guard daListDigest NodeVectors.da = NodeVectors.daListDigest

/-- The statement of the vectors' claims, deferring their claim. -/
def vectorStatement : NodeStatement :=
  ⟨⟨NodeVectors.xmss, NodeVectors.sphincs, NodeVectors.da⟩, NodeVectors.defer⟩

#guard statementDigest NodeVectors.seed vectorStatement = NodeVectors.statementDigest

-- Mutation: another seed, another digest.
#guard statementDigest seed0 vectorStatement ≠ NodeVectors.statementDigest

/- The batching of the two children, with the Rust's hints, defers the Rust's claim. -/
#guard (batch NodeVectors.children NodeVectors.hints).map (·.bytecodePoint) =
  some NodeVectors.batched.bytecodePoint
#guard (batch NodeVectors.children NodeVectors.hints).map (·.bytecodeValue) =
  some NodeVectors.batched.bytecodeValue

-- Mutation: a final value one off.
#guard (batch NodeVectors.children { NodeVectors.hints with
  bytecodeValue := NodeVectors.hints.bytecodeValue + 1 }).isNone

/-! ## The DA claim -/

/-- A root. -/
def root : Digest := keccak256 []

#guard LeanVM.Da.vectorDigestOf root != LeanVM.Da.toBytes root

end LeanVMTests.Spec.Node
