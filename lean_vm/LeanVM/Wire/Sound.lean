/-
  LeanVM.Wire.Sound

  Knowledge soundness on the wire from knowledge soundness on structured proofs, for any
  straight-line extractor: the adversary on bytes, followed by the decoding of its bytes, is an
  adversary on proofs.
-/

module

public import Statement.LeanVm
public import Common.Prob
public import LeanVM.Wire.Spec

/-!
# Knowledge soundness on the wire

`LeanVM.KnowledgeSoundnessOnBytes E` (`Statement/LeanVm.lean`) follows from
`LeanVM.KnowledgeSoundness E`, for every straight-line extractor `E`, by the reduction "the
adversary decodes its own bytes" (`knowledgeSoundnessOnBytes_of_decodeCost`):

* `decodingAdversary A` runs the adversary on bytes `A`, decodes its bytes
  (`Proof.fromBytes queryPermutation`) and outputs the decoded proof, or `rejectedProof` if the
  bytes encode none. Its transcript, recorded by `Common.loggedOracles`, is exactly the transcript
  of `knowledgeSoundnessExperimentOnBytes A`: both run the same computation `decodeAfter A`
  under the same recording.
* Where the bytes decode to a proof, the two experiments run the same verifier on the same
  statement and proof after the same transcript, and break together. Where they decode to none,
  the experiment on bytes rejects, and does not break. So the break on bytes has probability at most
  the break of `decodingAdversary A` (`prBreaksOnBytes_le`), whatever the verifier does on
  `rejectedProof`.
* `decodingAdversary A` makes at most `Q + D` permutation calls if `A` makes at most `Q` and the
  decoding at most `D` (`decodingAdversary_queryCost`); with `D + 2^14 ≤ 2^17` the bound of
  `KnowledgeSoundness` at `Q + D` is within the bound on bytes at `Q`, and for `Q + D > 2^128`
  (outside `KnowledgeSoundness`'s range) the bound on bytes exceeds `1`.
-/

open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open Common (RandomPermutationOracles OracleQueryLog PermutationEdges queryPermutation
  loggedOracles lazyRandomPermutationOracles runWithRandomPermutation QueryCostAtMost
  permutationCallCost)

/-- A proof the adversary that decodes its own bytes outputs when they encode none: no scalar and
no opening. Nothing depends on the verifier's verdict on it. -/
def rejectedProof : Proof := ⟨[], []⟩

/-- **The adversary on bytes, then the decoding of its bytes**: the computation that
`knowledgeSoundnessExperimentOnBytes` records. -/
noncomputable def decodeAfter (adversary : RandomPermutationAdversaryOnBytes) :
    OracleComp RandomPermutationOracles ((ProgramAndInput × Bytes) × Option Proof) := do
  let (statement, bytes) ← adversary
  let decodedProof ← Proof.fromBytes queryPermutation bytes
  return ((statement, bytes), decodedProof)

/-- **The adversary that decodes its own bytes**: `adversary`, then the decoding of its bytes; it
outputs the statement and the decoded proof, `rejectedProof` if there is none. -/
noncomputable def decodingAdversary (adversary : RandomPermutationAdversaryOnBytes) :
    RandomPermutationAdversary :=
  (fun x ↦ (x.1.1, x.2.getD rejectedProof)) <$> decodeAfter adversary

/-- The adversary that decodes its own bytes makes at most `Q + D` permutation calls when the
adversary makes at most `Q` and every decoding at most `D`. -/
theorem decodingAdversary_queryCost {adversary : RandomPermutationAdversaryOnBytes} {Q D : ℕ}
    (hQ : QueryCostAtMost adversary permutationCallCost Q)
    (hD : ∀ bytes, QueryCostAtMost (Proof.fromBytes queryPermutation bytes) permutationCallCost D) :
    QueryCostAtMost (decodingAdversary adversary) permutationCallCost (Q + D) := by
  have h : QueryCostAtMost (decodeAfter adversary) permutationCallCost (Q + (D + 0)) :=
    Common.QueryCostAtMost.bind hQ fun x ↦ Common.QueryCostAtMost.bind (hD x.2) fun _ ↦ trivial
  have h' := Common.QueryCostAtMost.bind h (b := 0)
    (ob := fun x ↦ pure (x.1.1, x.2.getD rejectedProof)) fun _ ↦ trivial
  simpa [decodingAdversary, map_eq_bind_pure_comp] using h'

/-- A comparison of continuations survives a common prefix, in a game run against the lazily
sampled permutation. -/
theorem prEvent_runWithRandomPermutation_bind_mono {α β γ : Type}
    (game : OracleComp RandomPermutationOracles α) (f : α → OracleComp RandomPermutationOracles β)
    (g : α → OracleComp RandomPermutationOracles γ) (p : β → Prop) (q : γ → Prop)
    (h : ∀ a (edges : PermutationEdges KeccakState),
      Pr{let y ← (simulateQ lazyRandomPermutationOracles (f a)).run' edges}[p y] ≤
        Pr{let y ← (simulateQ lazyRandomPermutationOracles (g a)).run' edges}[q y]) :
    Pr{let y ← runWithRandomPermutation (game >>= f)}[p y] ≤
      Pr{let y ← runWithRandomPermutation (game >>= g)}[q y] := by
  have := prEvent_bind_mono_of_forall_le ((simulateQ lazyRandomPermutationOracles game).run [])
    (fun a ↦ (simulateQ lazyRandomPermutationOracles (f a.1)).run' a.2)
    (fun a ↦ (simulateQ lazyRandomPermutationOracles (g a.1)).run' a.2) p q fun a ↦ h a.1 a.2
  simpa only [runWithRandomPermutation, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    map_bind] using this

/-- A game ending in a pure function of a computation's result, run against the lazily sampled
permutation, is that function after the computation's run. -/
theorem run'_simulateQ_bind_pure {α β : Type} (game : OracleComp RandomPermutationOracles α)
    (k : α → β) (edges : PermutationEdges KeccakState) :
    (simulateQ lazyRandomPermutationOracles (game >>= fun a ↦ pure (k a))).run' edges =
      k <$> (simulateQ lazyRandomPermutationOracles game).run' edges := by
  simp [StateT.run'_eq]

/-- **The break on bytes is at most the break of the adversary that decodes its own bytes.** -/
theorem prBreaksOnBytes_le (extractor : StraightLineExtractor)
    (adversary : RandomPermutationAdversaryOnBytes) :
    Pr{let outcome ← knowledgeSoundnessExperimentOnBytes adversary}[
        BreaksKnowledgeSoundnessOnBytes extractor outcome] ≤
      Pr{let outcome ← knowledgeSoundnessExperiment (decodingAdversary adversary)}[
        BreaksKnowledgeSoundness extractor outcome] := by
  have hrun : (simulateQ loggedOracles (decodingAdversary adversary)).run [] =
      (fun z : ((ProgramAndInput × Bytes) × Option Proof) × OracleQueryLog ↦
          ((z.1.1.1, z.1.2.getD rejectedProof), z.2)) <$>
        (simulateQ loggedOracles (decodeAfter adversary)).run [] := by
    rw [decodingAdversary, simulateQ_map, StateT.run_map]
  have hbytes : knowledgeSoundnessExperimentOnBytes adversary = runWithRandomPermutation
      ((simulateQ loggedOracles (decodeAfter adversary)).run [] >>= fun z ↦ do
        let accepted ← match z.1.2 with
          | none => pure false
          | some proof => leanVmVerifier queryPermutation z.1.1.1.1 z.1.1.1.2 proof
        return ⟨z.1.1.1.1, z.1.1.1.2, z.1.1.2, z.1.2, accepted, z.2⟩) := rfl
  have hproofs : knowledgeSoundnessExperiment (decodingAdversary adversary) =
      runWithRandomPermutation
        ((simulateQ loggedOracles (decodeAfter adversary)).run [] >>= fun z ↦ do
          let accepted ← leanVmVerifier queryPermutation z.1.1.1.1 z.1.1.1.2
            (z.1.2.getD rejectedProof)
          return ⟨z.1.1.1.1, z.1.1.1.2, z.1.2.getD rejectedProof, accepted, z.2⟩) := by
    rw [knowledgeSoundnessExperiment, hrun, bind_map_left]
  rw [hbytes, hproofs]
  refine prEvent_runWithRandomPermutation_bind_mono _ _ _ _ _ fun z edges ↦ ?_
  rcases z with ⟨⟨⟨⟨program, input⟩, bytes⟩, decodedProof⟩, transcript⟩
  rcases decodedProof with _ | proof
  · refine le_of_eq_of_le ?_ zero_le
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun y hy ↦ ?_
    simp only [simulateQ_pure, pure_bind, StateT.run'_eq, StateT.run_pure,
      map_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp [BreaksKnowledgeSoundnessOnBytes]
  · rw [run'_simulateQ_bind_pure, run'_simulateQ_bind_pure, prEvent_map, prEvent_map]
    refine prEvent_mono _ _ _ fun accepted hbreak ↦ ?_
    simpa [BreaksKnowledgeSoundnessOnBytes, BreaksKnowledgeSoundness] using hbreak

/-- `(Q + c) · 2^-128 ≥ 1` once `Q + c ≥ 2^128`. -/
theorem one_le_bound_of_le {x : ℝ≥0∞} (hx : 2 ^ 128 ≤ x) :
    1 ≤ x * (2 : ℝ≥0∞)⁻¹ ^ 128 + 5 * x ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  refine le_add_right ?_
  rw [← ENNReal.inv_pow, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
  exact hx

/-- **Knowledge soundness on the wire, from knowledge soundness on structured proofs**, for every
straight-line extractor, when every decoding makes at most `D` permutation calls and
`D + 2^14 ≤ 2^17`: by the adversary that decodes its own bytes (`decodingAdversary`). -/
theorem knowledgeSoundnessOnBytes_of_decodeCost {extractor : StraightLineExtractor} {D : ℕ}
    (hKS : KnowledgeSoundness extractor)
    (hD : ∀ bytes, QueryCostAtMost (Proof.fromBytes queryPermutation bytes) permutationCallCost D)
    (hD17 : D + 2 ^ 14 ≤ 2 ^ 17) :
    KnowledgeSoundnessOnBytes extractor := by
  intro adversary Q hQ _
  refine (prBreaksOnBytes_le extractor adversary).trans ?_
  have hcast : ((Q + D : ℕ) : ℝ≥0∞) + 2 ^ 14 ≤ (Q : ℝ≥0∞) + 2 ^ 17 := by
    have : (D : ℝ≥0∞) + 2 ^ 14 ≤ 2 ^ 17 := by exact_mod_cast hD17
    rw [Nat.cast_add, add_assoc]
    exact add_le_add le_rfl this
  by_cases hcap : Q + D ≤ 2 ^ 128
  · refine (hKS (decodingAdversary adversary) (Q + D)
      (decodingAdversary_queryCost hQ hD) hcap).trans ?_
    gcongr
  · refine (prEvent_le_one _).trans (one_le_bound_of_le ?_)
    refine le_trans ?_ ((le_add_right le_rfl).trans hcast)
    exact_mod_cast (Nat.lt_of_not_le hcap).le

/-- The decoding's bound with `KnowledgeSoundness`'s `2^14` is within the `2^17` of
`KnowledgeSoundnessOnBytes`: `73728 + 16384 ≤ 131072`. -/
theorem wireDecodePermutationCalls_add_le : wireDecodePermutationCalls + 2 ^ 14 ≤ 2 ^ 17 := by
  simp [wireDecodePermutationCalls, wireMaxPhases, wireMaxQueries, wireMaxHeight]

/-- **Knowledge soundness on the wire, from knowledge soundness on structured proofs**, for every
straight-line extractor, given that every decoding makes at most `wireDecodePermutationCalls`
(`73728`) permutation calls. -/
theorem knowledgeSoundnessOnBytes_of_wireDecodeCost {extractor : StraightLineExtractor}
    (hKS : KnowledgeSoundness extractor)
    (hD : ∀ bytes, QueryCostAtMost (Proof.fromBytes queryPermutation bytes) permutationCallCost
      wireDecodePermutationCalls) :
    KnowledgeSoundnessOnBytes extractor :=
  knowledgeSoundnessOnBytes_of_decodeCost hKS hD wireDecodePermutationCalls_add_le

/-- info: 'LeanVM.Wire.knowledgeSoundnessOnBytes_of_wireDecodeCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms knowledgeSoundnessOnBytes_of_wireDecodeCost

end LeanVM.Wire

end
