/-
  LeanVM.Spec.Ideal.Blind

  The Flock-blind verifier V°: the leanVM verifier with the lincheck's terminal check deleted, so
  that the BLAKE2S rows are bound only to the stack, not to the compression function.
-/

module

public import LeanVM.Spec.Verifier

/-!
# The Flock-blind verifier

The end-to-end security theorem (`docs/roadmap/e2e-security.md` (removed; in git at `6ffa1d1f`) D3) idealizes in-circuit hashing:
a `BLAKE2S` row is bound to the oracle by a check of the whole table outside the circuit, not to
the compression function by Flock. Its verifier V° is the deployed `verifyExecution` with one
check deleted: the lincheck's terminal identity (`verifyFlockLincheck`, the `require` comparing
the matrices' value with the sumcheck's last claim). With it gone, the matrix value is never
compared and Flock's zerocheck and lincheck carry no check; ring switching still adds the slices'
claim to the stacked opening, so the slices remain bound to the committed stack. The bytecode value
is computed, as deployed. One program per statement (`blindProgram`), so the random-oracle theorem
applies to it.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Blake2sHash

@[expose] public section

/-- `verifyFlockLincheck` without its terminal check (and without the matrix value, which only that
check reads): the claim's point and the slices. -/
def verifyFlockLincheckBlind (zc : ZerocheckResult) : Prog (List E × List E) := do
  let alpha ← Prog.sampleE
  let claim := zc.vA + alpha * zc.vB + alpha ^ 2 * zc.vC + alpha ^ 3
  let (roundChallenges, _) ← sumcheck claim 3 (List.replicate flockNumLincheckRounds none)
  let s ← Prog.readN kBits
  return (roundChallenges.reverse ++ zc.chi.drop flockNumLincheckRounds, s)

/-- `verifyFlock` without the terminal check. -/
def verifyFlockBlind (logN : ℕ) : Prog (List E × List E) := do
  let zc ← verifyFlockZerocheck logN
  verifyFlockLincheckBlind zc

/-- **`verifyExecution`, Flock-blind**: the deployed steps, the bytecode value computed, with
`verifyFlockBlind` for step 6. -/
def verifyExecutionBlind (bytecode : List K) (publicInput : Digest) : Prog Unit := do
  let (layout, logInverseRate) ← readSizes bytecode
  commitStack layout.stackLog logInverseRate
  let bus ← verifyBusBalance .computed layout
  let claims ← tablePhase layout bus
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  let (flockPoint, flockS) ←
    verifyFlockBlind (blake2sR1csLogSize + layout.tableLogHeights.getD opBlake2s 0)
  let (ringTarget, ringWeight) ← ringSwitch flockPoint flockS
  verifyStackedOpening layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.onStack layout))

/-- **The Flock-blind verifier program** V°. -/
def blindProgram (bytecode : List K) (publicInput : Digest) : Prog Bool := do
  verifyExecutionBlind bytecode publicInput
  return true

section Hash

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- **V° with the hash `H`**, from the deployed seed. -/
def verifyBlindWith (bytecode : List K) (publicInput : Digest) (π : Proof) : m Bool := do
  let seed ← seedWith H bytecode publicInput
  runProof H (blindProgram bytecode publicInput) seed π

end Hash

end
end LeanVM.Protocol.Verifier
