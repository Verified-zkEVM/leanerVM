import LeanerVM.Protocol.FlockSpec
import LeanerVM.Protocol.Piop
import LeanerVM.Protocol.Spine.Toy
import CompPoly.Multivariate.MvPolyEquiv.Eval
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Oracle protocol tests

* **The side conditions have inhabitants, with and without a Flock region.** The toy instance
  (no Flock region, so the Flock phase is the pass-through) and `blocky`, one table of `2 ^ 8`
  rows with matching push and pull flushes whose whole column is a Flock region with the
  BLAKE2s circuit's R1CS, both meet the bus phase's conditions and the degree bound. At `blocky`
  the Flock slot is the Flock phase itself. Its concrete honest stack satisfies the entire
  relation; the zero stack fails the Flock constant-position condition. Count-column behavior
  is exercised by the separate toy and spine tests.
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

/-- The tuple `(X₀, 0, …)` used on both sides of the bus. -/
def flush : Side × Vector (CMvPolynomial 1 K) 16 :=
  (.push, Vector.ofFn fun k ↦ if k.val = 0 then CMvPolynomial.X 0 else 0)

theorem flush_totalDegree (k : Fin 16) : (flush.2.get k).totalDegree ≤ 2 := by
  rw [totalDegree_equiv (S := K)]
  simp only [flush, Vector.get_ofFn]
  split
  · simp [CMvPolynomial.fromCMvPolynomial_X]
  · simp

/-- The instance: matching pushes and pulls of its column, a Flock region of one block with the
BLAKE2s circuit's R1CS. The region includes zero cells, so it is not also a count column. -/
abbrev blocky : M3Instance where
  toShape := blockyShape
  Stmt := Unit
  constraints := fun _ ↦ []
  flushes := fun _ ↦ [flush, (.pull, flush.2)]
  d := 2
  constraints_degree := fun _ _ h ↦ absurd h (List.not_mem_nil)
  flushes_degree := fun _ f h k ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact flush_totalDegree k
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

/-- Every stack balances this fixture's identical push and pull lists. -/
theorem blocky_balanced (q : Column blocky.μ) : blocky.Balanced q := by
  have h : blocky.tuples q .push = blocky.tuples q .pull := by
    simp [M3Instance.tuples, M3Instance.flushTuples, M3Instance.boundaryTuples, blocky, flush]
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

/-- The zero stack preserves bus balance but violates the Flock constant position. -/
theorem blocky_zero_rejected : ¬ M3Holds blocky () ⟨Vector.replicate _ 0⟩ := by
  intro h
  have hf := h.2.2.2.2 ⟨⟨0, 0⟩, 0, rfl, Blake2sFlock.blake2sFlockSpec.r1cs⟩ (by simp [blocky])
  have h1 := (hf 0).2
  rw [Blake2sFlock.batchBlock_bitTable] at h1
  simp [ProductCircuit.liftBlock, ProductCircuit.ofBool, Blake2sFlock.blockBits,
    blockCell, M3Instance.flockColumn, M3Instance.column, blocky, Layout.read,
    readWith_id] at h1

/-- The original fixture, retained only to show why its old completeness example was vacuous. -/
private abbrev unbalancedBlocky : M3Instance :=
  { blocky with
    flushes := fun _ ↦ [flush]
    flushes_degree := fun _ f h k ↦ by
      rw [List.mem_singleton.mp h]
      exact flush_totalDegree k
    counts := fun _ ↦ [0] }

/-- Natural-number multiset lengths rule out every stack for the original fixture. -/
theorem original_blocky_unsatisfiable (q : Column unbalancedBlocky.μ) :
    ¬ M3Holds unbalancedBlocky () q := by
  intro h
  have hl := h.2.1.length_eq
  have hp : (unbalancedBlocky.tuples q .push).length = 256 := by
    simp [M3Instance.tuples, M3Instance.flushTuples, M3Instance.boundaryTuples,
      unbalancedBlocky, blocky, flush, blockyShape, List.length_flatMap, List.length_map]
  have hn : (unbalancedBlocky.tuples q .pull).length = 0 := by
    simp [M3Instance.tuples, M3Instance.flushTuples, M3Instance.boundaryTuples,
      unbalancedBlocky, blocky, flush, blockyShape]
  omega

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
