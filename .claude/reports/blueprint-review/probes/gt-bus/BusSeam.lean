import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose

/-!
Probe for the dossier gt-bus (scratch, not part of the repository).

Three facts about the bus slot of the spine as built on `main` at `b435631`:

1. `countOnly`: an instance with degree bound `d = 0` and one count column. `M3Holds` is
   inhabited, and the count form the bus phase emits (one term, the count column `X₀`) has total
   degree 1, above `d`: a bus statement carrying it is outside `Seam.bus`.
2. `flushless`: an instance whose one table (log-height 2) has a constraint and no flush, no count
   column and no boundary block. `M3Holds` is inhabited and the bus has no tuple at all, so a
   grand-product tree over it has depth 0 and its terminal point has no coordinate, while the
   zerocheck point of the table needs two.
3. On the toy instance, a bus statement with two zerocheck claims of the same table at two
   unrelated points is inside `Seam.bus`: the seam does not tie the points to one `ζ`.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly

namespace Probe

instance {I : M3Instance} (q : Column I.μ) (c : LinearClaim I) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable ((c.terms.map fun t ↦ t.eval q).sum = c.value))

/-- The count column as a polynomial of a row of width one has total degree above zero. -/
theorem x0_degree : ¬ ((CMvPolynomial.X 0 : CMvPolynomial 1 K).totalDegree ≤ 0) := by
  decide +kernel

/-- The Boolean constraint on a row of width one has total degree at most two. -/
theorem bool_degree : (CMvPolynomial.X 0 * CMvPolynomial.X 0 - CMvPolynomial.X 0 :
    CMvPolynomial 1 K).totalDegree ≤ 2 := by
  decide +kernel

/-! ## 1. Degree bound zero with a count column -/

abbrev countOnly : M3Instance where
  toShape := ⟨1, fun _ ↦ 1, fun _ ↦ 1⟩
  Stmt := Unit
  constraints := fun _ ↦ []
  flushes := fun _ ↦ []
  d := 0
  constraints_degree := fun _ _ h ↦ absurd h List.not_mem_nil
  flushes_degree := fun _ _ h ↦ absurd h List.not_mem_nil
  counts := fun _ ↦ [0]
  boundary := []
  μ := 1
  layout := ⟨fun q _ ↦ q, fun _ z ↦ z, fun _ _ _ ↦ rfl⟩
  publicLines := fun _ ↦ []
  aux := fun _ ↦ True
  decAux := fun _ ↦ inferInstance

def ones : Column 1 := ⟨#v[1, 1]⟩

#guard M3Holds countOnly () ones

/-- The count form's one polynomial, the count column itself, is above the bound. -/
example : ¬ ((CMvPolynomial.X 0 : CMvPolynomial 1 K).totalDegree ≤ countOnly.d) := x0_degree

/-- So a bus statement carrying the count form is outside the bus seam. -/
example (w v : E) (p : Vector E 1) (o : ∀ i, TheOracle countOnly i) :
    ((((), (⟨[⟨[⟨w, 0, CMvPolynomial.X 0, p⟩], v⟩], []⟩ : BusOut countOnly)), o), ()) ∉
      Seam.bus countOnly := fun h ↦
  absurd (h.2.1 _ (List.mem_singleton_self _) _ (List.mem_singleton_self _)) x0_degree

/-! ## 2. A constraint on a table that is not on the bus -/

abbrev flushless : M3Instance where
  toShape := ⟨1, fun _ ↦ 2, fun _ ↦ 1⟩
  Stmt := Unit
  constraints := fun _ ↦ [CMvPolynomial.X 0 * CMvPolynomial.X 0 - CMvPolynomial.X 0]
  flushes := fun _ ↦ []
  d := 2
  constraints_degree := fun _ C h ↦ by rw [List.mem_singleton.mp h]; exact bool_degree
  flushes_degree := fun _ _ h ↦ absurd h List.not_mem_nil
  counts := fun _ ↦ []
  boundary := []
  μ := 2
  layout := ⟨fun q _ ↦ q, fun _ z ↦ z, fun _ _ _ ↦ rfl⟩
  publicLines := fun _ ↦ []
  aux := fun _ ↦ True
  decAux := fun _ ↦ inferInstance

def bits : Column 2 := ⟨#v[0, 1, 1, 0]⟩
def notBits : Column 2 := ⟨#v[0, 1, 2, 0]⟩

#guard M3Holds flushless () bits
#guard ¬ M3Holds flushless () notBits
-- No tuple on either side, no count cell: the three trees of the bus are empty.
#guard (flushless.tuples bits .push).length = 0
#guard (flushless.tuples bits .pull).length = 0
#guard (flushless.counts 0).length = 0

/-! ## 3. The bus seam does not tie the points of its claims together -/

def pointA : Vector E 1 := #v[y]
def pointB : Vector E 1 := #v[y + 1]

/-- The toy's zerocheck claim, at `pointA`. -/
def zeroA : LinearClaim toy :=
  ⟨[⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, pointA⟩], 0⟩

/-- The same claim at another point. -/
def zeroB : LinearClaim toy :=
  ⟨[⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, pointB⟩], 0⟩

#guard pointA.toList ≠ pointB.toList
#guard zeroA.Holds honest
#guard zeroB.Holds honest

/-- Both claims, at their two points, are one statement of the bus seam. -/
example (h : toy.PublicLinesHold (1 : K) honest) (hA : zeroA.Holds honest)
    (hB : zeroB.Holds honest) :
    ((((1 : K), (⟨[zeroA, zeroB], []⟩ : BusOut toy)), fun _ ↦ honest), ()) ∈ Seam.bus toy := by
  refine ⟨?_, ?_, ?_, h, trivial⟩
  · intro c hc
    rcases List.mem_pair.mp hc with rfl | rfl
    · exact hA
    · exact hB
  · intro c hc t ht
    rcases List.mem_pair.mp hc with rfl | rfl <;>
      (rw [List.mem_singleton.mp ht]; decide +kernel)
  · intro c hc
    exact absurd hc List.not_mem_nil

#guard toy.PublicLinesHold (1 : K) honest

end Probe
