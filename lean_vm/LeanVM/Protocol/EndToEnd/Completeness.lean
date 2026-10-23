/-
  LeanVM.Protocol.EndToEnd.Completeness

  End-to-end completeness of the deployed leanVM verifier, unconditionally.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Theorem

/-!
# End-to-end completeness

The deployed verifier is `Verifier.verify` (`Verifier.lean`), the compiled reading at Keccak-256
and Keccak-f[1600] of `leanVmProgram`, a transcription of `python-verifier/verifier.py` at leanVM
`3375f7a137c50b803f3416f6466b5d4e0719708a`. The statements here are those of `EndToEnd.Complete`,
which carry no hypothesis.

* `leanVm_interactiveComplete`: from a witness satisfying leanISA's constraint system at
  admissible sizes, for a valid rate, an honest strategy makes the verifier program accept
  against every challenge function, committing well-shaped words.
* `leanVm_complete`: for every hash function and permutation, the compiled honest prover produces
  a proof the compiled verifier accepts, as soon as its proof-of-work searches find nonces below
  the fuel; `leanVm_complete_keccak` is the deployed instance.
* `leanVm_complete_of_execution`: from a valid execution of at most `2^32` steps, a witness
  representing it, accepted as above when its sizes are admissible.

Completeness is perfect: the only way the honest prover fails is a proof-of-work search that finds
no nonce below the fuel, a search over Keccak-f outputs about which nothing is claimed here (the
random-oracle model bounds it, `Complete.Rom`).
-/

namespace LeanVM.Protocol.EndToEnd

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakHash
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- **Interactive perfect completeness of the deployed verifier program.** -/
theorem leanVm_interactiveComplete {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {s : Sizes} {ρ : ℕ}
    (h : SatisfiedBy prog input w) (hsz : Sizes.ofWitness w = some s) (hs : s.Admissible prog)
    (hρ : validRate ρ) :
    ∃ S : Strategy, ∀ chal : List Ev → E,
      runI (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)) S chal = some true ∧
        shapedI (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)) S chal :=
  Complete.leanVm_complete h hsz hs hρ

/-- **Completeness of the compiled verifier, for every hash function and permutation.** -/
theorem leanVm_complete (H : Bytes → Digest) (F : KState → KState) {prog : Program}
    {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)} {s : Sizes} {ρ : ℕ}
    (h : SatisfiedBy prog input w) (hsz : Sizes.ofWitness w = some s) (hs : s.Admissible prog)
    (hρ : validRate ρ) (fuel : ℕ)
    (hg : ∀ hist bits k sp,
      (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)).after hist =
          some (.grind bits k) → findNonce F bits sp fuel ≠ none) :
    ∃ S π, prove H F (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)) S
        (Id.run (seedWith (m := Id) H F (bytecodeWords prog) (Complete.publicDigest input)))
          fuel = some π ∧
      Id.run (verifyWith (m := Id) H F (bytecodeWords prog) (Complete.publicDigest input) π) =
        true :=
  Complete.exists_prove_verifyWith H F h hsz hs hρ fuel hg

/-- **Completeness of the deployed verifier**: the Keccak instance of `leanVm_complete`. -/
theorem leanVm_complete_keccak {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {s : Sizes} {ρ : ℕ}
    (h : SatisfiedBy prog input w) (hsz : Sizes.ofWitness w = some s) (hs : s.Admissible prog)
    (hρ : validRate ρ) (fuel : ℕ)
    (hg : ∀ hist bits k sp,
      (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)).after hist =
          some (.grind bits k) → findNonce keccakF bits sp fuel ≠ none) :
    ∃ S π, prove keccak256 keccakF
        (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)) S
        (seed (bytecodeWords prog) (Complete.publicDigest input)) fuel = some π ∧
      Verifier.verify (bytecodeWords prog) (Complete.publicDigest input) π = true :=
  Complete.exists_prove_verify h hsz hs hρ fuel hg

/-- **Completeness from an execution.** -/
theorem leanVm_complete_of_execution {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hsteps : t.steps ≤ 2 ^ maxLogRows) :
    ∃ w s, SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧ Sizes.ofWitness w = some s ∧
      (s.Admissible prog → ∀ ρ, validRate ρ → ∃ S : Strategy, ∀ chal : List Ev → E,
        runI (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)) S chal =
            some true ∧
          shapedI (leanVmProgram (bytecodeWords prog) (Complete.publicDigest input)) S chal) :=
  Complete.leanVm_complete_of_execution hv hsteps

end
end LeanVM.Protocol.EndToEnd
