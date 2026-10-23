import LeanVM.Protocol.LeanVMSound

/-!
# leanVM's knowledge soundness, locked

Statement locks of `LeanVM/Protocol/LeanVMSound.lean`: the verifier for any hash and permutation,
the deployed verifier, knowledge soundness in the random-oracle model, and the numbers, with the
axioms each depends on.
-/

open LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.LeanIsa LeanVM
open LeanVM.Protocol.KeccakHash

example (prog : Program) (input : PublicInput) (proof : LeanVM.Proof) :
    verify prog input proof = Id.run (verifier (m := Id) keccak256 keccakF prog input proof) :=
  rfl

example {A : Adversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment A}[z.1.2 = true ∧ SentinelSafe z.1.1.1.1 ∧
      ¬ ∃ t, extractor z.1.1.1.1 z.1.1.1.2 z.2.2 z.1.1.2 = some t ∧
        ValidExecution z.1.1.1.1 z.1.1.1.2 t] ≤
      soundnessError Q :=
  knowledgeSoundness hA

/-- The adversary chooses the statement: a fixed statement is the special case of an adversary
that outputs it. -/
example (prog : Program) (input : PublicInput) (P : OracleComp HashSpec LeanVM.Proof) {Q : ℕ}
    (hP : P.IsTotalQueryBound Q) :
    Pr{let z ← experiment ((fun proof ↦ ((prog, input), proof)) <$> P)}[Breaks extractor z] ≤
      soundnessError Q :=
  knowledgeSoundness ((OracleComp.isQueryBound_map_iff P _ Q _ _).mpr hP)

/-- The numbers: `12008` verifier queries, a collision term of `7` per pair of queries. -/
example (Q : ℕ) : soundnessError Q =
    ((Q + 12008 : ℕ) : ENNReal) *
        ((2 : ENNReal)⁻¹ ^ 128 + ((7 * (Q + 12008) : ℕ) : ENNReal) / 2 ^ 256) +
      ((12008 : ℕ) : ENNReal) / 2 ^ 256 := rfl

example {Q : ℕ} (hQ : Q ≤ 2 ^ 64) : soundnessError Q ≤ (2 : ENNReal)⁻¹ ^ 63 :=
  soundnessError_le hQ

/-- The proofs of work have `17` bits. -/
example : LeanVM.Parameters.Whir.queryGrindingBits = 17 := rfl

/-- info: 'LeanVM.knowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knowledgeSoundness

/--
info: 'LeanVM.soundnessError_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms soundnessError_le

/-! ## The statement of `LeanVM/Spec/Statement.lean` -/

example : KnowledgeSoundness := knowledgeSoundness_holds

/--
info: 'LeanVM.knowledgeSoundness_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms knowledgeSoundness_holds
