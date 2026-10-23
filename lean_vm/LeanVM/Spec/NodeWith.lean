/-
  LeanVM.Spec.NodeWith

  The aggregation's node relation for any hash and permutation: the digests, the signature
  schemes, the batching and `NodeRel` with the hash and the permutation parameters in any monad,
  the deployed ones recovered at Keccak-256 and Keccak-f[1600].
-/

module

public import LeanVM.Spec.Node
public import LeanVM.Spec.DaWith

/-!
# The node, for any hash and permutation

`Node.lean` states what a node establishes with Keccak-256 and Keccak-f[1600]. The guest's proofs
also need it relative to a hash and a permutation answered by a log: every hash and permutation a
check makes must be answered, and the check must hold for the answers. So every hashing function
of `Node.lean` is given here with the hash `H : Bytes → m Digest` and the permutation
`F : KState → m KState` in any monad (`…With`), as the verifier is (`verifier H F`,
`LeanVM.Spec.Statement`): at `m = Id`, `H = keccak256` and `F = keccakF` it is the deployed one
(`statementDigestWith_id`, `batchWith_id`, `xmssVerifyWith_id`, …), and at `m = Option` with `H`
and `F` a log's lookups it is the computation answered by the log. The digests and the signature
schemes use only `H`; the batching's transcript, a duplex sponge, only `F`, from a parameter
state `s0` (deployed: `batchSeed`, Keccak-f of the label's hash, whose capacity the guest bakes as
`AGG_SEED_*`). `NodeRelWith H F` is `NodeRel` over an `Option`-valued hash and permutation, each
check "answered and true".

The deployed definitions are not changed: this module only adds, so nothing importing `Node.lean`
is affected.
-/

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section With

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KState → m KState)

/-! ## The signature schemes -/

/-- `keccakBits` is `digestBits` of Keccak-256. -/
theorem keccakBits_eq (input : List UInt8) : keccakBits input = digestBits (keccak256 input) :=
  rfl

/-- leanXMSS verification with the hash `H`. -/
def xmssVerifyWith (pk : LeanXmss.PublicKey) (message : LeanXmss.Message)
    (σ : LeanXmss.Signature) : m Bool :=
  letI : HasQuery LeanXmss.HashSpec m := ⟨fun x ↦ digestBits <$> H x⟩
  LeanXmss.Concrete.verify pk message σ

/-- leanSPHINCS verification with the hash `H`. -/
def sphincsVerifyWith (pk : Sphincs.PublicKey) (message : Sphincs.Message)
    (σ : Sphincs.Signature) : m Bool :=
  letI : HasQuery Sphincs.HashSpec m := ⟨fun x ↦ digestBits <$> H x⟩
  Sphincs.Concrete.verify pk message σ

/-! ## The statement's digest -/

/-- `xmssListDigest` with the hash `H`. -/
def xmssListDigestWith (claims : List XmssClaim) : m Digest :=
  H (claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2)

/-- `sphincsListDigest` with the hash `H`. -/
def sphincsListDigestWith (claims : List SphincsClaim) : m Digest :=
  H (claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2)

/-- `signersDigest` with the hash `H`. -/
def signersDigestWith (xmss : List XmssClaim) (sphincs : List SphincsClaim) : m Digest := do
  let x ← xmssListDigestWith H xmss
  let s ← sphincsListDigestWith H sphincs
  H (digestBytes x ++ digestBytes s)

/-- `daListDigest` with the hash `H`. -/
def daListDigestWith (claims : List DaClaim) : m Digest :=
  H (claims.flatMap fun c ↦ digestBytes c.1 ++ digestBytes c.2)

/-- **`statementDigest` with the hash `H`.** -/
def statementDigestWith (seed : Digest) (s : NodeStatement) : m Digest := do
  let sd ← signersDigestWith H s.claims.xmss s.claims.sphincs
  let dd ← daListDigestWith H s.claims.da
  let cells := s.defer.cells ++ if s.defer.cells.length % 2 = 1 then [0] else []
  H (digestBytes seed ++ digestBytes sd ++ digestBytes dd ++ cells.flatMap eBytes)

/-! ## The batching -/

/-- A Fiat-Shamir chain with the permutation `F`. -/
abbrev ChainWith : Type → Type := StateT Sponge m

/-- `observe` with the permutation `F`. -/
def observeWith (x : E) : ChainWith (m := m) Unit := do
  set (← (Compile.absorb F (← get) x dsObserve : m Sponge))

/-- `sample` with the permutation `F`. -/
def sampleWith : ChainWith (m := m) E := do
  let (c, sp) ← (Compile.squeeze F (← get) : m (E × Sponge))
  set sp
  return c

/-- `batchRounds` with the permutation `F`. -/
def batchRoundsWith : E → List (E × E) → ChainWith (m := m) (List E × E)
  | claim, [] => return ([], claim)
  | claim, (g1, gInf) :: rest => do
    observeWith F g1
    observeWith F gInf
    let r ← sampleWith F
    let g0 := claim + g1
    let (rs, final) ← batchRoundsWith ((gInf * r + (g0 + g1 + gInf)) * r + g0) rest
    return (r :: rs, final)

/-- `batchSeed` with the hash `H` and the permutation `F`. -/
def batchSeedWith : m KState := do
  F (seedInput (← H batchLabel) (Vector.replicate 4 0))

/-- **`batch` with the permutation `F`, from the sponge state `s0`** (deployed: `batchSeed`). -/
def batchWith (s0 : KState) (children : List ChildClaims) (h : BatchHints) :
    m (Option DeferredClaim) :=
  go.run' ⟨s0, []⟩
where
  /-- The transcript. -/
  go : ChainWith (m := m) (Option DeferredClaim) := do
    for x in padRate [gpow children.length] do observeWith F x
    for c in children do
      for x in padRate c.words do observeWith F x
    let mut lambdas : List (E × E) := []
    for _ in children do
      let lf ← sampleWith F
      let lc ← sampleWith F
      lambdas := lambdas ++ [(lf, lc)]
    let claim := sumE (List.zipWith (fun c l ↦
      l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) children lambdas)
    let (r, final) ← batchRoundsWith F claim h.bytecodeRounds
    let weight := sumE (List.zipWith (fun c l ↦
      l.1 * eqEval c.fresh.bytecodePoint r + l.2 * eqEval c.carried.bytecodePoint r)
      children lambdas)
    if final = h.bytecodeValue * weight then return some ⟨r, h.bytecodeValue⟩
    else return none

end With

/-! ## The node relation over an answered hash and permutation -/

section Answered

variable (H : Bytes → Option Digest) (F : KState → Option KState)

/-- The leanXMSS claim is held: by a signature verified with every hash answered, or by a child
making it. -/
def XmssHeldWith (children : List Child) (claim : XmssClaim) : Holder LeanXmss.Signature → Prop
  | .direct σ => xmssVerifyWith H claim.1 claim.2 σ = some true
  | .child i => ∃ c, children[i]? = some c ∧ claim ∈ c.statement.claims.xmss

/-- The leanSPHINCS claim is held: by a signature verified with every hash answered, or by a child
making it. -/
def SphincsHeldWith (children : List Child) (claim : SphincsClaim) :
    Holder Sphincs.Signature → Prop
  | .direct σ => sphincsVerifyWith H claim.1 claim.2 σ = some true
  | .child i => ∃ c, children[i]? = some c ∧ claim ∈ c.statement.claims.sphincs

/-- The DA claim is held: by a matrix opening with every hash answered (the padding digests
`pc`, `pr`), or by a child making it. -/
def DaHeldWith (pc pr : LeanDa.Digest) (children : List Child) (claim : DaClaim) :
    Holder Da.Witness → Prop
  | .direct w => w.OpensWith H pc pr claim.1 claim.2
  | .child i => ∃ c, children[i]? = some c ∧ claim ∈ c.statement.claims.da

/-- The children's claims the batching absorbs, their public inputs the answered digests of their
statements. -/
def childClaimsWith (seed : Digest) (children : List Child) : Option (List ChildClaims) :=
  children.mapM fun c ↦ (fun pi ↦ ⟨pi, c.fresh, c.statement.defer⟩) <$>
    statementDigestWith H seed c.statement

/-- **`NodeRel` over an answered hash and permutation**: what the witness `w` establishes of `s`
when every hash and permutation the guest computes is answered by `H` and `F` (a log's lookups) —
every check of `NodeRel` with its hashes and permutations answered and true; the batching from
the sponge state `s0`; the DA padding digests `pc`, `pr`. -/
def NodeRelWith (s0 : KState) (pc pr : LeanDa.Digest) (bytecode : List K) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) : Prop :=
  s.defer.Shaped bytecode ∧
  (∀ c ∈ w.children, c.statement.defer.Shaped bytecode ∧ ∃ pi,
    statementDigestWith H seed c.statement = some pi ∧
    verifyDeferredWith H F bytecode seed pi c.fresh c.proof = some true) ∧
  List.Forall₂ (XmssHeldWith H w.children) s.claims.xmss w.xmss ∧
  List.Forall₂ (SphincsHeldWith H w.children) s.claims.sphincs w.sphincs ∧
  List.Forall₂ (DaHeldWith H pc pr w.children) s.claims.da w.da ∧
  if w.children = [] then s.defer.AtZero bytecode
  else ∃ cs, childClaimsWith H seed w.children = some cs ∧
    batchWith F s0 cs w.hints = some (some s.defer)

end Answered

/-! ## The deployed functions, recovered -/

/-- leanXMSS verification with Keccak-256 is `xmssVerify`. -/
theorem xmssVerifyWith_id (pk : LeanXmss.PublicKey) (message : LeanXmss.Message)
    (σ : LeanXmss.Signature) :
    Id.run (xmssVerifyWith (m := Id) keccak256 pk message σ) = xmssVerify pk message σ :=
  rfl

/-- leanSPHINCS verification with Keccak-256 is `sphincsVerify`. -/
theorem sphincsVerifyWith_id (pk : Sphincs.PublicKey) (message : Sphincs.Message)
    (σ : Sphincs.Signature) :
    Id.run (sphincsVerifyWith (m := Id) keccak256 pk message σ) = sphincsVerify pk message σ :=
  rfl

/-- The statement's digest with Keccak-256 is `statementDigest`. -/
theorem statementDigestWith_id (seed : Digest) (s : NodeStatement) :
    Id.run (statementDigestWith (m := Id) keccak256 seed s) = statementDigest seed s :=
  rfl

/-- Absorbing with Keccak-f is `observe`. -/
theorem observeWith_id (x : E) : observeWith (m := Id) keccakF x = observe x := rfl

/-- Squeezing with Keccak-f is `sample`. -/
theorem sampleWith_id : sampleWith (m := Id) keccakF = sample := rfl

/-- The batching's rounds with Keccak-f are `batchRounds`. -/
theorem batchRoundsWith_id : ∀ (claim : E) (rounds : List (E × E)),
    batchRoundsWith (m := Id) keccakF claim rounds = batchRounds claim rounds
  | _, [] => rfl
  | claim, (g1, gInf) :: rest => by
    simp only [batchRoundsWith, batchRounds, observeWith_id, sampleWith_id, batchRoundsWith_id]

/-- The batching's initial state with Keccak is `batchSeed`. -/
theorem batchSeedWith_id : Id.run (batchSeedWith (m := Id) keccak256 keccakF) = batchSeed := rfl

/-- The batching with Keccak-f, from `batchSeed`, is `batch`. -/
theorem batchWith_id (children : List ChildClaims) (h : BatchHints) :
    Id.run (batchWith (m := Id) keccakF batchSeed children h) = batch children h := by
  simp only [batchWith, batch, batchWith.go, batch.go, observeWith_id, sampleWith_id,
    batchRoundsWith_id]
  rfl

end
end LeanVM.Node
