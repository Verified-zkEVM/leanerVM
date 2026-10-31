import Sphincs.Scheme
import SphincsBase.Proof.Base.Probability

/-! Uniform bit extraction; adapted from leanVM b7a107256. -/
namespace SphincsLayered
open OracleComp OracleSpec ENNReal
theorem hashOutput_eq_of_extract {width : Nat} (hwidth : width ≤ 256) {x y : HashOutput}
    (hlow : x.extractLsb' 0 width = y.extractLsb' 0 width)
    (hhigh : x.extractLsb' width (256 - width)
      = y.extractLsb' width (256 - width)) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < width
  · have := congrArg (fun b : BitVec width => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hlt] using this
  · have hshift : i - width < 256 - width := by omega
    have := congrArg (fun b : BitVec (256 - width) => b.getLsbD (i - width)) hhigh
    simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
    rwa [show width + (i - width) = i by omega] at this

def splitHashOutput (width : Nat) (output : HashOutput) :
    BitVec width × BitVec (256 - width) :=
  (output.extractLsb' 0 width,
    output.extractLsb' width (256 - width))

theorem splitHashOutput_injective {width : Nat} (hwidth : width ≤ 256) :
    Function.Injective (splitHashOutput width) := by
  intro left right heq
  apply hashOutput_eq_of_extract hwidth
  · exact congrArg Prod.fst heq
  · exact congrArg Prod.snd heq

theorem splitHashOutput_bijective {width : Nat} (hwidth : width ≤ 256) :
    Function.Bijective (splitHashOutput width) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨splitHashOutput_injective hwidth, ?_⟩
  rw [Fintype.card_prod, Fintype.card_bitVec, Fintype.card_bitVec, Fintype.card_bitVec, ← pow_add]
  congr 1
  omega

noncomputable def splitHashOutputEquiv (width : Nat) (hwidth : width ≤ 256) :
    HashOutput ≃ BitVec width × BitVec (256 - width) :=
  Equiv.ofBijective (splitHashOutput width) (splitHashOutput_bijective hwidth)

theorem evalDist_hashOutput_extract_uniform {width : Nat} (hwidth : width ≤ 256) :
    ((fun output : HashOutput => output.extractLsb' 0 width) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ BitVec width : ProbComp (BitVec width)) := by
  let split := splitHashOutput width
  have hmap :
      (fun output : HashOutput => output.extractLsb' 0 width) <$>
          ($ᵗ HashOutput : ProbComp HashOutput) =
        Prod.fst <$> (split <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp [Functor.map_map, split, splitHashOutput]
  rw [hmap]
  have hsplit :
      (split <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ (BitVec width × BitVec (256 - width)) :
          ProbComp (BitVec width × BitVec (256 - width))) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective
      (α := HashOutput) (β := BitVec width × BitVec (256 - width))
      (splitHashOutput_bijective hwidth)
  refine (hsplit.map Prod.fst).trans fun p => ?_
  rw [prEvent_map]
  exact SampleableType.prEvent_uniformSample_fst p

/-- The three parts of a hash output around the `width` bits at `offset`. -/
def splitHashOutputAt (offset width : Nat) (output : HashOutput) :
    BitVec width × (BitVec offset × BitVec (256 - (offset + width))) :=
  (output.extractLsb' offset width,
    (output.extractLsb' 0 offset, output.extractLsb' (offset + width) (256 - (offset + width))))

theorem splitHashOutputAt_bijective {offset width : Nat} (hwidth : offset + width ≤ 256) :
    Function.Bijective (splitHashOutputAt offset width) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨?_, ?_⟩
  · intro x y heq
    have hmid := congrArg Prod.fst heq
    have hlow := congrArg (fun t => t.2.1) heq
    have hhigh := congrArg (fun t => t.2.2) heq
    simp only [splitHashOutputAt] at hmid hlow hhigh
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases hlt : i < offset
    · have := congrArg (fun b : BitVec offset => b.getLsbD i) hlow
      simpa [BitVec.getLsbD_extractLsb', hlt] using this
    · by_cases hlt' : i < offset + width
      · have hshift : i - offset < width := by omega
        have := congrArg (fun b : BitVec width => b.getLsbD (i - offset)) hmid
        simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
        rwa [show offset + (i - offset) = i by omega] at this
      · have hshift : i - (offset + width) < 256 - (offset + width) := by omega
        have := congrArg (fun b : BitVec (256 - (offset + width)) =>
          b.getLsbD (i - (offset + width))) hhigh
        simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
        rwa [show offset + width + (i - (offset + width)) = i by omega] at this
  · rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bitVec, Fintype.card_bitVec, Fintype.card_bitVec, Fintype.card_bitVec,
      ← pow_add, ← pow_add]
    congr 1
    omega

/-- The `width` bits at any offset of a uniform hash output are uniform. -/
theorem evalDist_hashOutput_extractAt_uniform {offset width : Nat}
    (hwidth : offset + width ≤ 256) :
    ((fun output : HashOutput => output.extractLsb' offset width) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ BitVec width : ProbComp (BitVec width)) := by
  let split := splitHashOutputAt offset width
  have hmap :
      (fun output : HashOutput => output.extractLsb' offset width) <$>
          ($ᵗ HashOutput : ProbComp HashOutput) =
        Prod.fst <$> (split <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp [Functor.map_map, split, splitHashOutputAt]
  rw [hmap]
  have hsplit :
      (split <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ (BitVec width × (BitVec offset × BitVec (256 - (offset + width)))) :
          ProbComp (BitVec width × (BitVec offset × BitVec (256 - (offset + width))))) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective
      (α := HashOutput)
      (β := BitVec width × (BitVec offset × BitVec (256 - (offset + width))))
      (splitHashOutputAt_bijective hwidth)
  refine (hsplit.map Prod.fst).trans fun p => ?_
  rw [prEvent_map]
  exact SampleableType.prEvent_uniformSample_fst p

theorem evalDist_truncateHash_uniform :
    (truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ Digest : ProbComp Digest) := by
  exact evalDist_hashOutput_extract_uniform (width := digestBits) (by decide)

theorem probEvent_uniform_truncateHash_mem (targets : Finset Digest) :
    Pr{let output ← ($ᵗ HashOutput : ProbComp HashOutput)}[truncateHash output ∈ targets] =
      (targets.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
  have h := evalDist_truncateHash_uniform.prEvent_eq (· ∈ targets)
  rw [prEvent_map] at h
  rw [h, SampleableType.prEvent_uniformSample]
  rw [Finset.filter_univ_mem]

end SphincsLayered
