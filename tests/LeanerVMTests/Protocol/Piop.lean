import LeanerVM.Protocol.FlockSpec
import LeanerVM.Protocol.Piop
import LeanerVM.Protocol.Spine.Toy
import CompPoly.Multivariate.MvPolyEquiv.Eval
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Oracle protocol tests

* **The side conditions have inhabitants, with and without a Flock region.** The toy instance
  (no Flock region, so the Flock phase is the pass-through) and `blocky`, one table of `2 ^ 8`
  rows that pushes and pulls one tuple per row and whose whole column is a Flock region with the
  BLAKE2s circuit's R1CS, both meet the bus phase's conditions and the degree bound. At `blocky`
  the Flock slot is the Flock phase itself.
* **`blocky`'s relation is inhabited.** The honest column of one BLAKE2s block satisfies
  `M3Holds blocky`; the zero column fails it at the Flock predicate alone.
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

/-- The tuple `(X₀, 0, …)`, flushed on both sides of the bus. -/
def tuple : Vector (CMvPolynomial 1 K) 16 :=
  Vector.ofFn fun k ↦ if k.val = 0 then CMvPolynomial.X 0 else 0

theorem tuple_totalDegree (k : Fin 16) : (tuple.get k).totalDegree ≤ 2 := by
  rw [totalDegree_equiv (S := K)]
  simp only [tuple, Vector.get_ofFn]
  split
  · simp [CMvPolynomial.fromCMvPolynomial_X]
  · simp

/-- The instance: its column pushes and pulls `tuple` on every row and is a Flock region of one
block with the BLAKE2s circuit's R1CS. It has no count column: an honest region has zero cells. -/
abbrev blocky : M3Instance where
  toShape := blockyShape
  Stmt := Unit
  constraints := fun _ ↦ []
  flushes := fun _ ↦ [(.push, tuple), (.pull, tuple)]
  d := 2
  constraints_degree := fun _ _ h ↦ absurd h (List.not_mem_nil)
  flushes_degree := fun _ f h k ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact tuple_totalDegree k
  counts := fun _ ↦ []
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

/-- Every stack balances the bus: the push and pull lists are one list. -/
theorem blocky_balanced (q : Column blocky.μ) : blocky.Balanced q := by
  have h : blocky.tuples q .push = blocky.tuples q .pull := by
    simp [M3Instance.tuples, M3Instance.flushTuples, M3Instance.boundaryTuples, blocky]
  unfold M3Instance.Balanced
  rw [h]

/-- Reading the Flock region reads the entire stack, independently of its values. -/
theorem blocky_flockColumn (q : Column blocky.μ) : blocky.flockColumn
    ⟨⟨0, 0⟩, 0, rfl, Blake2sFlock.blake2sFlockSpec.r1cs⟩ q = q := by
  unfold M3Instance.flockColumn M3Instance.column
  dsimp only [blocky, Layout.read]
  rw [readWith_id]
  simp only [Vector.cast_rfl]

/-- One honest BLAKE2s block, generated from explicit zero input limbs. The generator computes
the output and circuit wires, rather than requiring the supplied output limbs to be correct. -/
def blockyHonest : Column blocky.μ :=
  Blake2sFlock.blake2sFlockSpec.gen (κ := 0) #v[fun _ ↦ 0]

/-- A concrete inhabitant of the full input relation, including the Flock predicate. -/
theorem blocky_honest : M3Holds blocky () blockyHonest := by
  refine ⟨?_, blocky_balanced _, ?_, ?_, ?_⟩
  · intro j C h
    simp [blocky] at h
  · intro j i h
    simp [blocky] at h
  · intro l h
    simp [blocky] at h
  · intro r h
    have hr : ⟨⟨0, 0⟩, 0, rfl, Blake2sFlock.blake2sFlockSpec.r1cs⟩ = r := by
      simpa [blocky] using h
    subst r
    rw [blocky_flockColumn]
    exact Blake2sFlock.blake2sFlockSpec.holds_gen (κ := 0) #v[fun _ ↦ 0]

/-- The zero stack fails the Flock predicate at the circuit's constant position. The other
clauses do not reject it: the bus balances for every stack, and the rest are empty. -/
theorem blocky_zero_rejected : ¬ M3Holds blocky () ⟨Vector.replicate _ 0⟩ := by
  rintro ⟨-, -, -, -, hf⟩
  have h1 := (hf _ rfl 0).2
  rw [blocky_flockColumn, Blake2sFlock.batchBlock_bitTable] at h1
  simp [ProductCircuit.liftBlock, ProductCircuit.ofBool, Blake2sFlock.blockBits, blockCell] at h1

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
