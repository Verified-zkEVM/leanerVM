/-
  Probe (boundary-adaptor): the two relations, their universes, and the public input.
  Scratch work for the blueprint review; not part of the repository.
  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/boundary-adaptor/Shapes.lean
-/
import LeanerVM

open LeanerVM LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVM.Protocol
open Air.Flat (Ensemble EnsembleWitness Component)

set_option pp.universes true

/-! ## 1. Universes: the witness of `SatisfiedBy` against the witness of `M3Holds` -/

#check @EnsembleWitness
#check @Air.Flat.Table
#check @Air.Flat.Component
#check @leanIsaEnsemble
#check @SatisfiedBy
#check @M3Holds
#check @M3Rel
#check @Column
#check @Refinement
#check @Refinement.map_option_valid
#check @Extractor.Straightline.map

set_option pp.universes false

/-! ## 2. The statement types as written -/

#print SatisfiedBy
#print Caps
#print PublicInput
#print PublicInput.word0
#print PublicInput.word1
#print PublicIO
#print ValidExecution
#print HasPublicBoundary
#print Program
#print M3Holds
#print M3Instance
#print PublicLine

/-! ## 3. Which `ConstraintsHold` does `w.Constraints` unfold to? -/

#print Air.Flat.EnsembleWitness.Constraints
#print Air.Flat.Table.Constraints
#print Operations.ConstraintsHold
#print Air.Flat.EnsembleWitness.interactions
#print ProverData

/-! ## 4. The top limb of a public word is zero by construction -/

example (p : PublicInput) : p.word0.limb 2 = 0 := by
  simp [PublicInput.word0]

example (p : PublicInput) : p.word1.limb 2 = 0 := by
  simp [PublicInput.word1]

/-- A word of the image whose top limb is nonzero is not a public word, whatever the input: the
fact `word0_eq` needs from the third public line. -/
example (p : PublicInput) (a b c : K) (hc : c ≠ 0) : E.ofLimbs a b c ≠ p.word0 := by
  intro h
  have := congrArg (fun z : E ↦ z.limb 2) h
  simp [PublicInput.word0] at this
  exact hc this

/-- With the top limb zero and the two low limbs those of the statement, the word is the public
word: the three public lines give `word0_eq`. -/
example (p : PublicInput) (a b c : K) (ha : a = p.word0.limb 0) (hb : b = p.word0.limb 1)
    (hc : c = 0) : E.ofLimbs a b c = p.word0 := by
  subst ha hb hc
  simp [PublicInput.word0]

/-! ## 5. Axioms of what the chain will use on the arithmetization side, and of the master
theorems -/

#print axioms assumptions_of_blake2sRowsValid
#print axioms memRowOf_bindings
#print axioms bytecodeRowOf_bindings
#print axioms bytecodeRowOf_decodes
#print axioms verifier_pull_eval
#print axioms verifier_push_eval
#print axioms rowAt_toElements
#print axioms decode_eq_some_iff
#print axioms assignmentRepresents_image
#print axioms xorTable
#print axioms jumpTable
#print axioms blake2sTable
#print axioms memTable
#print axioms bytecodeTable
#print axioms leanIsaVerifier
#print axioms piop_rbrKnowledgeSoundness
#print axioms piop_perfectCompleteness
#print axioms Refinement.map_option_valid
#print axioms bytecodeColumn_eval
#print axioms idxColumn_eval
