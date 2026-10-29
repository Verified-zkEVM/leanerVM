/-
  LeanVM.Facts.NodeWith

  The node's hashing functions with any hash `H : Bytes → m Digest` and permutation
  `F : KState → m KState` in any monad (`…With`), as the verifier is (`verifier H F`): moved here
  from `Statement/LeanVmGuest.lean`, names kept (no end statement names them), and at `m = Id`,
  Keccak-256 and Keccak-f[1600] the deployed ones: the `*_id` lemmas. The digests and the
  signature schemes use only `H`; the batching's transcript only `F`, from a parameter state `s0`
  (deployed: `batchSeed`).
-/

module

public import Statement.LeanVmGuest
public import LeanVM.Guest.Batch.Def
public import LeanXmss.Scheme
public import Sphincs.Equations
public import Statement.Fast.Schemes
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import LeanVM.Facts.Verifier
public import LeanVM.Facts.DaWith

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section With

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KState → m KState)

/-! ### The signature schemes -/

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

/-! ### The statement's digest -/

/-- `claimListDigest` with the hash `H`. -/
def xmssListDigestWith (claims : List XmssClaim) : m Digest :=
  H (claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2)

/-- `claimListDigest` with the hash `H`. -/
def sphincsListDigestWith (claims : List SphincsClaim) : m Digest :=
  H (claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2)

/-- `daListDigest` with the hash `H`. -/
def daListDigestWith (claims : List DaClaim) : m Digest :=
  H (claims.flatMap fun c ↦ digestBytes c.daRoot ++ digestBytes c.membershipVectorDigest)

/-- **`statementDigest` with the hash `H`.** -/
def statementDigestWith (seed : Digest) (s : NodeStatement) : m Digest := do
  let xd ← xmssListDigestWith H s.claims.xmss
  let sd ← sphincsListDigestWith H s.claims.sphincs
  let dd ← daListDigestWith H s.claims.da
  let cells := s.defer.cells ++ if s.defer.cells.length % 2 = 1 then [0] else []
  H (digestBytes seed ++ digestBytes xd ++ digestBytes sd ++ digestBytes dd ++ cells.flatMap eBytes)

/-! ### The batching -/

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
    let (rs, final) ← batchRoundsWith (Guest.Batch.roundPoly claim (g1, gInf) r) rest
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
    let (r, final) ← batchRoundsWith F (Guest.Batch.claimBOf children lambdas) h.bytecodeRounds
    if final = h.bytecodeValue * Guest.Batch.bytecodeWeight children lambdas r then
      return some ⟨r, h.bytecodeValue⟩
    else return none

/-- `keccakBits` is `digestBits` of Keccak-256. -/
theorem keccakBits_eq (input : List UInt8) : keccakBits input = digestBits (keccak256 input) :=
  rfl

end With

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
