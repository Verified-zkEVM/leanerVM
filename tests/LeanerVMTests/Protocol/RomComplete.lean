/-
  LeanerVMTests.Protocol.RomComplete

  The honest prover's grinds as a proof-of-work search: the parameters the random-oracle
  completeness bound is stated at, and the conditions it rests on.
-/

module

public import LeanerVM.Protocol.Prove.RomComplete
public import LeanerVM.Protocol.Prove.Queries
meta import LeanerVM.Protocol.Prove.Queries
meta import LeanerVM.Protocol.Prove.RomComplete
meta import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Random-oracle completeness: controls

* The zero digest, which answers every query the cache does not hold in the replayed run, clears
  the deployed grind of 17 bits, and a digest whose low bits are not zero fails it.
* `nonceOf` repeats from `2^64` on, so a search of more candidates tries some nonce twice: the
  search counts `min fuel (2^64)` candidates, and the injectivity it needs fails above.
* Every computation on the hash oracle has a query bound (`exists_isTotalQueryBound`), so the
  bound's hypothesis is met by some `N`, for the honest prover too.
* The counts the bound rests on, run with an oracle that counts its queries: a Merkle commitment
  of `2^4` rows asks `2^5 - 1`; a grind of `5` candidates whose answers all fail asks its base and
  the five, and returns none; the WHIR term `130023647` of the count is attained at `μ = 28`,
  rate `4`.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Parameters LeanerVM.Protocol Blake2sHash OracleComp OracleSpec
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- The deployed grind has 17 bits. -/
example : Whir.queryGrindingBits = 17 := rfl

/-- The zero digest clears the deployed grind. -/
example : FsState.lowBitsZero Prove.zeroDigest Whir.queryGrindingBits = true :=
  Prove.lowBitsZero_zeroDigest _

/-- A digest with its lowest bit set fails it. -/
example : FsState.lowBitsZero (Vector.replicate 8 1) Whir.queryGrindingBits = false := by
  decide +kernel

/-- The candidate nonce wraps at `2^64`: a search of more candidates repeats one. -/
example : FsState.nonceOf (2 ^ 64) = FsState.nonceOf 0 := by
  have : K.ofBits (2 ^ 64) = K.ofBits 0 := congrArg BF64.ofBitVec (by decide)
  simp only [FsState.nonceOf, this]

/-- The search's candidates are capped at `2^64`. -/
example (fuel : ℕ) : (Prove.grindSearch fuel 17).F = min fuel (2 ^ 64) := rfl

/-- The honest prover on the hash oracle has a query bound. -/
example (fuel : ℕ) (F : FlockSpec) (prog : LeanerVM.Semantics.Program)
    (input : LeanerVM.Semantics.PublicInput) {κ : ℕ}
    (w : EnsembleWitness (LeanerVM.Arithmetization.leanIsaEnsemble prog κ)) (ρ : ℕ) :
    ∃ N, IsTotalQueryBound (proveWith hashQuery fuel F prog input w ρ) N :=
  exists_isTotalQueryBound _

/-- An oracle that counts its queries and answers the zero digest. -/
def countZero : QueryImpl hashSpec (StateM ℕ) := fun _ ↦ do
  modify (· + 1)
  pure Prove.zeroDigest

/-- An oracle that counts its queries and answers a digest that fails every grind. -/
def countFail : QueryImpl hashSpec (StateM ℕ) := fun _ ↦ do
  modify (· + 1)
  pure (Vector.replicate 8 1)

-- A Merkle commitment of `2^4` rows: sixteen leaves and fifteen nodes.
#guard ((simulateQ countZero (merkleCommitWithM hashQuery 1
  (Vector.replicate (2 ^ 4) ([0] : List K)))).run 0).2 = 2 ^ 5 - 1

-- A grind of `5` candidates that all fail: the base and five candidates, and no nonce.
#guard ((simulateQ countFail (FsState.grind hashQuery 5 ⟨Prove.zeroDigest⟩ 17)).run 0).2 = 6
#guard ((simulateQ countFail (FsState.grind hashQuery 5 ⟨Prove.zeroDigest⟩ 17)).run 0).1.isNone

-- The WHIR term of the count is attained at `μ = 28`, rate `4`.
#guard (Whir.ladder 28 4).map (fun ls ↦ Prove.shapeQueries0 (Verify.levelShapes 28 ls)) =
  some 130023647

end

end LeanerVMTests.Protocol
