/-
  LeanVM.Spec.NodeWith

  The aggregation's node relation for any hash: the digests, the signature schemes, the batching
  and `NodeRel` with the hash a parameter in any monad, the deployed ones recovered at BLAKE2s.
-/

module

public import LeanVM.Spec.Node
public import LeanVM.Spec.DaWith

/-!
# The node, for any hash

`Node.lean` states what a node establishes with BLAKE2s. The end-to-end security theorem
(`docs/roadmap/e2e-security.md`) states it relative to a random oracle answered by a log: every
hash a check makes must be answered, and the check must hold for the answers. So every hashing
function of `Node.lean` is given here with the hash `H : Bytes → m Digest` in any monad (`…With`):
at `m = Id` and `H = blake2sBytes` it is the deployed one (`statementDigestWith_id`,
`batchWith_id`, `xmssVerifyWith_id`, …), and at `m = Option` with `H` a log's lookup it is the
computation answered by the log. `NodeRelWith H` is `NodeRel` over an `Option`-valued hash, each
check "answered and true"; the batching starts from a parameter `s0` (deployed: the label's hash,
the guest's baked `AGG_SEED`).

The deployed definitions are not changed: this module only adds, so nothing importing `Node.lean`
is affected.
-/

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section With

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-! ## The signature schemes -/

/-- A digest as the schemes' 256-bit output, its bytes little-endian (`blake2sBits`). -/
def digestBits (d : Digest) : BitVec 256 :=
  BitVec.ofNat 256 ((digestBytes d).foldr (fun b acc ↦ b.toNat + 256 * acc) 0)

theorem blake2sBits_eq (input : List UInt8) : blake2sBits input = digestBits (blake2sBytes input) :=
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
  let bytes := digestBytes seed ++ digestBytes sd ++ digestBytes dd ++ cells.flatMap eBytes
  H (bytes ++ List.replicate ((64 - bytes.length % 64) % 64) 0)

/-! ## The batching -/

/-- A Fiat-Shamir chain with the hash `H`. -/
abbrev ChainWith : Type → Type := StateT Digest m

/-- `observe` with the hash `H`. -/
def observeWith (x : E) : ChainWith (m := m) Unit := do
  let cv ← get
  set (← (H (digestBytes cv ++ blockOf x 1) : m Digest))

/-- `squeeze` with the hash `H`. -/
def squeezeWith : ChainWith (m := m) E := do
  let cv ← get
  let cv' ← (H (digestBytes cv ++ blockOf 0 2) : m Digest)
  set cv'
  return challengeOf cv'

/-- `batchRounds` with the hash `H`. -/
def batchRoundsWith : E → List (E × E) → ChainWith (m := m) (List E × E)
  | claim, [] => return ([], claim)
  | claim, (g1, gInf) :: rest => do
    observeWith H g1
    observeWith H gInf
    let r ← squeezeWith H
    let g0 := claim + g1
    let (rs, final) ← batchRoundsWith ((gInf * r + (g0 + g1 + gInf)) * r + g0) rest
    return (r :: rs, final)

/-- **`batch` with the hash `H`, from the chain state `s0`** (deployed: the label's hash). -/
def batchWith (s0 : Digest) (children : List ChildClaims) (h : BatchHints) :
    m (Option DeferredClaim) :=
  go.run' s0
where
  /-- The transcript. -/
  go : ChainWith (m := m) (Option DeferredClaim) := do
    observeWith H (ofK (gpow children.length))
    for c in children do
      observeWith H (digestScalars c.publicInput).1
      observeWith H (digestScalars c.publicInput).2
      for x in fixedCells c.fresh ++ c.carried.cells do observeWith H x
    let mut bytecodeLambdas : List (E × E) := []
    for _ in children do
      let lf ← squeezeWith H
      let lc ← squeezeWith H
      bytecodeLambdas := bytecodeLambdas ++ [(lf, lc)]
    let bytecodeClaim := sumE (List.zipWith (fun c l ↦
      l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) children bytecodeLambdas)
    let (rBytecode, bytecodeFinal) ← batchRoundsWith H bytecodeClaim h.bytecodeRounds
    let bytecodeWeight := sumE (List.zipWith (fun c l ↦
      l.1 * eqEval c.fresh.bytecodePoint rBytecode +
        l.2 * eqEval c.carried.bytecodePoint rBytecode) children bytecodeLambdas)
    let mut matrixLambdas : List (E × E × E) := []
    for _ in children do
      let lf ← squeezeWith H
      let la ← squeezeWith H
      let lb ← squeezeWith H
      matrixLambdas := matrixLambdas ++ [(lf, la, lb)]
    let matrixClaim := sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.matrixValue +
      l.2.1 * c.carried.matrixA + l.2.2 * c.carried.matrixB) children matrixLambdas)
    let (rMatrix, matrixFinal) ← batchRoundsWith H matrixClaim h.matrixRounds
    let weightA := sumE (List.zipWith (fun c l ↦ l.1 * freshWeight c.fresh rMatrix +
      l.2.1 * eqEval c.carried.matrixPoint rMatrix) children matrixLambdas)
    let weightB := sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.alpha * freshWeight c.fresh rMatrix +
      l.2.2 * eqEval c.carried.matrixPoint rMatrix) children matrixLambdas)
    if bytecodeFinal = h.bytecodeValue * bytecodeWeight ∧
        matrixFinal = h.matrixA * weightA + h.matrixB * weightB then
      return some ⟨rBytecode, h.bytecodeValue, rMatrix, h.matrixA, h.matrixB⟩
    else return none

end With

/-! ## The node relation over an answered hash -/

section Answered

variable (H : Bytes → Option Digest)

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

/-- **`NodeRel` over an answered hash**: what the witness `w` establishes of `s` when every hash
the guest computes is answered by `H` (a log's lookup) — every check of `NodeRel` with its hashes
answered and true; the batching from the chain state `s0`; the DA padding digests `pc`, `pr`. -/
def NodeRelWith (s0 : Digest) (pc pr : LeanDa.Digest) (bytecode : List K) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) : Prop :=
  s.defer.Shaped bytecode ∧
  (∀ c ∈ w.children, c.statement.defer.Shaped bytecode ∧ ∃ pi,
    statementDigestWith H seed c.statement = some pi ∧
    verifyDeferredWith H bytecode seed pi c.fresh c.proof = some true) ∧
  List.Forall₂ (XmssHeldWith H w.children) s.claims.xmss w.xmss ∧
  List.Forall₂ (SphincsHeldWith H w.children) s.claims.sphincs w.sphincs ∧
  List.Forall₂ (DaHeldWith H pc pr w.children) s.claims.da w.da ∧
  if w.children = [] then s.defer.AtZero bytecode
  else ∃ cs, childClaimsWith H seed w.children = some cs ∧
    batchWith H s0 cs w.hints = some (some s.defer)

end Answered

/-! ## The deployed functions, recovered -/

theorem xmssVerifyWith_id (pk : LeanXmss.PublicKey) (message : LeanXmss.Message)
    (σ : LeanXmss.Signature) :
    Id.run (xmssVerifyWith (m := Id) blake2sBytes pk message σ) = xmssVerify pk message σ :=
  rfl

theorem sphincsVerifyWith_id (pk : Sphincs.PublicKey) (message : Sphincs.Message)
    (σ : Sphincs.Signature) :
    Id.run (sphincsVerifyWith (m := Id) blake2sBytes pk message σ) = sphincsVerify pk message σ :=
  rfl

theorem statementDigestWith_id (seed : Digest) (s : NodeStatement) :
    Id.run (statementDigestWith (m := Id) blake2sBytes seed s) = statementDigest seed s :=
  rfl

theorem observeWith_id (x : E) : observeWith (m := Id) blake2sBytes x = observe x := rfl

theorem squeezeWith_id : squeezeWith (m := Id) blake2sBytes = squeeze := rfl

theorem batchRoundsWith_id : ∀ (claim : E) (rounds : List (E × E)),
    batchRoundsWith (m := Id) blake2sBytes claim rounds = batchRounds claim rounds
  | _, [] => rfl
  | claim, (g1, gInf) :: rest => by
    simp only [batchRoundsWith, batchRounds, observeWith_id, squeezeWith_id, batchRoundsWith_id]

theorem batchWith_id (children : List ChildClaims) (h : BatchHints) :
    Id.run (batchWith (m := Id) blake2sBytes (blake2sBytes batchLabel) children h) =
      batch children h := by
  simp only [batchWith, batch, batchWith.go, batch.go, observeWith_id, squeezeWith_id,
    batchRoundsWith_id]
  rfl

end
end LeanVM.Node
