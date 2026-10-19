import LeanerVM.Protocol.FlockSpec
import LeanerVM.Protocol.Piop
import LeanerVM.Protocol.Spine.Toy
import CompPoly.Multivariate.MvPolyEquiv.Eval
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Oracle protocol tests

* **The side conditions have inhabitants, with and without a Flock region.** The toy instance
  (no Flock region, so the Flock phase is the pass-through) and `blocky`, one table of `2 ^ 8`
  rows with a push flush and a count column whose whole column is a Flock region with the BLAKE2s
  circuit's R1CS, both meet the bus phase's conditions and the degree bound. At `blocky` the
  Flock slot is the Flock phase itself.
* **The statements, by type.** The two master theorems at both instances, with the relation, the
  seam, the extractor and the error spelled out: a change to their hypotheses or conclusions
  fails here.
-/

namespace LeanerVMTests.Protocol.Piop

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy OracleComp OracleSpec CompPoly
  CPoly

/-! ## The toy, with no Flock region -/

/-- The toy meets the bus phase's conditions. -/
theorem toy_conditions : Bus.Conditions toy where
  one_le_d := by decide
  constrained := by decide
  pull_fits := by decide
  count_fits := by decide

example : toy.d ≤ 2 := by decide

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop (leanVmPhases toy toy_conditions)).perfectCompleteness init impl (M3Rel toy)
      (Seam.done toy) :=
  leanVm_perfectCompleteness toy toy_conditions (by decide) init impl

/-- The verifier at the toy. -/
abbrev toyVerifier := (leanVmVerifier (leanVmPhases toy toy_conditions)).toVerifier

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    toyVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel toy) (Seam.done toy)
      (leanVmSecurity toy toy_conditions (by decide)).extraction.witMid
      (piopExtractor _ (leanVmSecurity toy toy_conditions (by decide)))
      ((leanVmSecurity toy toy_conditions (by decide)).extraction.kSF init impl) (piopError toy) :=
  leanVm_rbrKnowledgeSoundness toy toy_conditions (by decide) init impl

/-! ## An instance with a Flock region -/

/-- One table of height `2 ^ 8` and width one. -/
abbrev blockyShape : Shape := ⟨1, fun _ ↦ 8, fun _ ↦ 1⟩

/-- The stack is the one column. -/
theorem readWith_id (q : Column 8) (c : blockyShape.ColumnId) :
    Layout.readWith (fun (_ : blockyShape.ColumnId) (z : Vector E 8) ↦ z) q c = q := by
  obtain ⟨v⟩ := q
  apply congrArg Column.mk
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn, boolIndex_boolVec]
  rfl

/-- The one flush: `(X₀, 0, …)`, pushed. -/
def flush : Side × Vector (CMvPolynomial 1 K) 16 :=
  (.push, Vector.ofFn fun k ↦ if k.val = 0 then CMvPolynomial.X 0 else 0)

theorem flush_totalDegree (k : Fin 16) : (flush.2.get k).totalDegree ≤ 2 := by
  rw [totalDegree_equiv (S := K)]
  simp only [flush, Vector.get_ofFn]
  split
  · simp [CMvPolynomial.fromCMvPolynomial_X]
  · simp

/-- The instance: the table pushes its rows and counts with its column, which is a Flock region
of `2 ^ 0` blocks with the BLAKE2s circuit's R1CS. -/
abbrev blocky : M3Instance where
  toShape := blockyShape
  Stmt := Unit
  constraints := fun _ ↦ []
  flushes := fun _ ↦ [flush]
  d := 2
  constraints_degree := fun _ _ h ↦ absurd h (List.not_mem_nil)
  flushes_degree := fun _ f h k ↦ by rw [List.mem_singleton.mp h]; exact flush_totalDegree k
  counts := fun _ ↦ [0]
  boundary := []
  μ := 8
  layout := ⟨fun _ z ↦ z, fun q c z ↦ by rw [readWith_id]⟩
  nLines := 0
  publicLines := fun _ ↦ #v[]
  flock := some ⟨⟨0, 0⟩, 0, rfl, Blake2sFlock.blake2sFlockSpec.r1cs⟩

/-- `blocky` meets the bus phase's conditions. -/
theorem blocky_conditions : Bus.Conditions blocky where
  one_le_d := by decide
  constrained := by decide
  pull_fits := by decide
  count_fits := by decide

example : blocky.flock.isSome := rfl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop (leanVmPhases blocky blocky_conditions)).perfectCompleteness init impl
      (M3Rel blocky) (Seam.done blocky) :=
  leanVm_perfectCompleteness blocky blocky_conditions (by decide) init impl

/-- The verifier at `blocky`. -/
abbrev blockyVerifier := (leanVmVerifier (leanVmPhases blocky blocky_conditions)).toVerifier

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    blockyVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel blocky) (Seam.done blocky)
      (leanVmSecurity blocky blocky_conditions (by decide)).extraction.witMid
      (piopExtractor _ (leanVmSecurity blocky blocky_conditions (by decide)))
      ((leanVmSecurity blocky blocky_conditions (by decide)).extraction.kSF init impl)
      (piopError blocky) :=
  leanVm_rbrKnowledgeSoundness blocky blocky_conditions (by decide) init impl

end LeanerVMTests.Protocol.Piop
