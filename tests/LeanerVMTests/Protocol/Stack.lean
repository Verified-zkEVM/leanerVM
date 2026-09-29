/-
  LeanerVMTests.Protocol.Stack

  Controls for the stack of columns: the reading law on a column that is not an honest stack, its
  agreement with the toy instance's layout, and the two padding decompositions.
-/

import LeanerVM.Protocol.Stack
import LeanerVM.Protocol.Spine.Toy
import LeanerVMTests.Protocol.Stacking

/-!
# Stack of columns controls

The fixture is the three blocks of heights 4, 2, 1 of `LeanerVMTests.Protocol.Stacking`. The
reading law is checked on a column no honest prover would commit and at a point outside `K`; a
selector with its bits reversed breaks it; a placement with the small block first has no
selector at all. Three blocks of height 2 reproduce the layout of the toy instance. A plain file,
so `#guard` evaluates the compiled definitions.
-/

namespace LeanerVMTests.Protocol.Stack

open LeanerVM.Parameters LeanerVM.Protocol CompPoly CMlPolynomialEval

/-! ## The honest stack -/

-- Blocks at their windows, zero in the one uncovered cell.
#guard (blocks.stack 3).values = #v[1, 2, 3, 4, 5, 6, 7, 0]

-- Reading the honest stack returns each block.
#guard (blocks.readColumn blocks_total_le (blocks.stack 3) (0 : Fin 3)).values.toList = [1, 2, 3, 4]
#guard (blocks.readColumn blocks_total_le (blocks.stack 3) (1 : Fin 3)).values.toList = [5, 6]
#guard (blocks.readColumn blocks_total_le (blocks.stack 3) (2 : Fin 3)).values.toList = [7]

/-! ## The reading law on an arbitrary column -/

/-- A column that is not the stack of the fixture's blocks, with a nonzero uncovered cell. -/
def arbitrary : Column 3 := ⟨#v[9, 8, 7, 6, 5, 4, 3, 2]⟩

/-- A point of `E` outside `K`. -/
def u : E := E.ofLimbs 0 1 0

example : ¬ IsInK u := by decide

-- The blocks read off it are its windows: cells 0 to 3, cells 4 and 5, cell 6.
#guard (blocks.readColumn blocks_total_le arbitrary (0 : Fin 3)).values.toList = [9, 8, 7, 6]
#guard (blocks.readColumn blocks_total_le arbitrary (1 : Fin 3)).values.toList = [5, 4]
#guard (blocks.readColumn blocks_total_le arbitrary (2 : Fin 3)).values.toList = [3]

-- A lifted point is the point followed by the selector bits, low bit first: block 1 sits at
-- selector index 2, bits `(0, 1)`.
#guard blocks.extendPoint blocks_total_le (1 : Fin 3) #v[u] = #v[u, 0, 1]
#guard blocks.extendPoint blocks_total_le (0 : Fin 3) #v[u, u + 1] = #v[u, u + 1, 0]
#guard blocks.extendPoint blocks_total_le (2 : Fin 3) #v[] = #v[0, 1, 1]

-- The law, through the `Layout` an instance carries, for every block.
#guard eval₂Mle ((blocks.layout blocks_total_le).read arbitrary (0 : Fin 3)).values
    (algebraMap K E) #v[u, u + 1] =
  eval₂Mle arbitrary.values (algebraMap K E)
    ((blocks.layout blocks_total_le).extend (0 : Fin 3) #v[u, u + 1])
#guard eval₂Mle ((blocks.layout blocks_total_le).read arbitrary (1 : Fin 3)).values
    (algebraMap K E) #v[u] =
  eval₂Mle arbitrary.values (algebraMap K E)
    ((blocks.layout blocks_total_le).extend (1 : Fin 3) #v[u])
#guard eval₂Mle ((blocks.layout blocks_total_le).read arbitrary (2 : Fin 3)).values
    (algebraMap K E) #v[] =
  eval₂Mle arbitrary.values (algebraMap K E)
    ((blocks.layout blocks_total_le).extend (2 : Fin 3) #v[])

-- Mutation: block 1's selector bits reversed, `(1, 0)`, select cells 2 and 3 instead.
#guard eval₂Mle (blocks.readColumn blocks_total_le arbitrary (1 : Fin 3)).values
    (algebraMap K E) #v[u] ≠
  eval₂Mle arbitrary.values (algebraMap K E) #v[u, 1, 0]

-- The layout is a theorem for every column and point, not only the ones evaluated above.
example (q : Column 3) (b : Fin blocks.n) (z : Vector E (blocks.size b)) :
    eval₂Mle ((blocks.layout blocks_total_le).read q b).values (algebraMap K E) z =
      eval₂Mle q.values (algebraMap K E) ((blocks.layout blocks_total_le).extend b z) :=
  (blocks.layout blocks_total_le).read_eval q b z

/-! ## Alignment needs the largest block first -/

-- Heights 1, 2, 4 in that order are not a `Blocks`.
example : ¬ Antitone (![0, 1, 2] : Fin 3 → ℕ) := fun h ↦
  absurd (h (show (0 : Fin 3) ≤ 1 by decide)) (by decide)

/-- The same cells with the small block first: the block `[5, 6]` sits at offset 1. -/
def smallFirst : CMlPolynomialEval K 3 := #v[7, 5, 6, 1, 2, 3, 4, 0]

-- No selector reads the block `[5, 6]` off that placement: every slice of height 2 differs.
#guard (List.finRange 4).all fun j ↦
  slice (k := 1) (m := 2) smallFirst j ≠ (#v[5, 6] : CMlPolynomialEval K 1)
-- Largest first, the selector of index 2 reads it.
#guard slice (k := 1) (m := 2) (blocks.stack 3).values (2 : Fin 4) =
  (#v[5, 6] : CMlPolynomialEval K 1)

/-! ## The toy instance's layout is an aligned layout -/

/-- Three blocks of height 2, the columns of the toy instance. Only the sizes matter. -/
def toyBlocks : Blocks K where
  n := 3
  size := fun _ ↦ 1
  values := fun _ ↦ #v[0, 0]
  descending := fun _ _ _ ↦ le_refl 1

theorem toyBlocks_total_le : toyBlocks.total ≤ 2 ^ 3 := by decide

-- Same cells read, on the toy's honest stack and on an arbitrary column.
#guard (List.finRange 3).all fun c ↦
  ((toyBlocks.layout toyBlocks_total_le).read Toy.honest c).values.toList =
    (Toy.layout.read Toy.honest ⟨0, c⟩).values.toList
#guard (List.finRange 3).all fun c ↦
  ((toyBlocks.layout toyBlocks_total_le).read arbitrary c).values.toList =
    (Toy.layout.read arbitrary ⟨0, c⟩).values.toList
-- Same lifted points.
#guard (List.finRange 3).all fun c ↦
  (toyBlocks.layout toyBlocks_total_le).extend c #v[u] = Toy.layout.extend ⟨0, c⟩ #v[u]

/-! ## Evaluation at an arbitrary point -/

/-- A point of `E^3` off the cube and outside `K`. -/
def ζ : Vector E 3 := #v[u, u + 1, u * u]

-- The zero-padded stack is the weighted sum of its blocks.
#guard eval₂Mle (blocks.stack 3).values (algebraMap K E) ζ =
  ∑ b : Fin blocks.n, (blocks.map (algebraMap K E)).selectorWeight blocks_total_le b ζ *
    eval₂Mle (blocks.column b).values (algebraMap K E)
      ((blocks.map (algebraMap K E)).lowPoint blocks_total_le b ζ)

/-- The fixture's blocks as tables over `E`, as the leaves of a product tree are. -/
def blocksE : Blocks E := blocks.map (algebraMap K E)

theorem blocksE_total_le : blocksE.total ≤ 2 ^ 3 := blocks_total_le

/-- The weighted sum of the blocks of `blocksE` at `ζ`. -/
def covered : E :=
  ∑ b : Fin blocksE.n, blocksE.selectorWeight blocksE_total_le b ζ *
    evalMle (blocksE.values b) (blocksE.lowPoint blocksE_total_le b ζ)

/-- The total selector weight of `blocksE` at `ζ`. -/
def weight : E := ∑ b : Fin blocksE.n, blocksE.selectorWeight blocksE_total_le b ζ

-- The one-padded stack adds the weight of the uncovered cell.
#guard evalMle (blocksE.stackAt 3 1) ζ = covered + (1 + weight)
-- Mutations: the padding term is neither absent nor the constant `1`.
#guard evalMle (blocksE.stackAt 3 1) ζ ≠ covered
#guard evalMle (blocksE.stackAt 3 1) ζ ≠ covered + 1

example : evalMle (blocksE.stackAt 3 1) ζ = covered + (1 + weight) :=
  blocksE.eval_stackAt_one blocksE_total_le ζ

end LeanerVMTests.Protocol.Stack
