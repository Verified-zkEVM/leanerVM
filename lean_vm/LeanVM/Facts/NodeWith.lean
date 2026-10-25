/-
  LeanVM.Facts.NodeWith

  The node relation with any hash and permutation (`Statement/LeanVmGuest.lean`) at
  Keccak-256 and Keccak-f[1600] is the deployed one: the `*_id` lemmas.
  The definitions are the statement's; these are proofs.
-/

module

public import Statement.LeanVmGuest
public import LeanXmss.Scheme
public import Sphincs.Scheme
public import LeanVM.Fast.Schemes
public import LeanDa.Scheme
public import LeanVM.Fast.Da
public import LeanVM.Fast.Keccak
public import LeanVM.Fast.CubicExt
public import LeanVM.Fast.FieldWords
public import LeanVM.Facts.Verifier
public import LeanVM.Facts.DaWith

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section With

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KState → m KState)

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
