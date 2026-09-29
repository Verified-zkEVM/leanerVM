/-
  LeanerVM.Protocol.Stack

  Aligned stacking on leanVM's columns: `K`-columns stacked into one committed column, read back
  block by block, and evaluated at points of `E`.
-/

module

public import LeanerVM.Protocol.Spine.Instance
public import LeanerVM.Protocol.ToCompPoly.AmbientStacking

/-!
# The stack of columns

The generic stacking of `ToCompPoly/Stacking.lean`, specialised to the two fields of leanVM: the
blocks are columns over `K`, the stack is the one committed column, and every evaluation is at a
point of `E`, the column oracle's answer there (`evalOracle_answer`; specification §4.1).

* `Blocks.stackColumn` is the witness stack: block `b` at its window, zero past the last block.
* `Blocks.readColumn` reads block `b` off *any* column of the stack's height, honest or not.
  `Blocks.readColumn_eval` is the stacking identity `q̃(z, sel_b) = P̃_b(z)`, for every `q`.
* `Blocks.layout` packages the reader, the lift of a point and that identity as a `Layout`, the
  reading law an `M3Instance` carries. A layout is sizes only, so it names no table.
  `Layout.comap` renames its columns, which is how a layout indexed by blocks becomes one
  indexed by the columns of an instance.
* `Blocks.stackColumn_eval_ambient` is the decomposition of the zero-padded stack at an
  arbitrary point, and `Blocks.stack_eval_ambient_one` the one-padded form over `E`, with the
  padding term written as the specification writes it in characteristic two,
  `1 + Σ_b eq(sel_b, ζ_hi)` (§5.4, equation (2)).

Category A: written from the specification; nothing here transcribes Rust. Which columns the
blocks are, and in which order equal sizes come, is the instance's to say, not this module's.

## Wrong readings excluded

* The reading law quantifies over every column `q`, not only over honest stacks: a knowledge
  extractor reads the blocks off whatever the prover committed.
* The padding term of the one-padded stack is the weight of the *uncovered* part of the cube,
  not the constant `1`; it vanishes when the blocks fill the stack.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

/-! ## Renaming the columns of a layout -/

/-- A layout read through a renaming of its columns that keeps their heights. -/
def Layout.comap {μ : ℕ} {ι ι' : Type} {κ : ι → ℕ} {κ' : ι' → ℕ} (L : Layout μ ι κ)
    (f : ι' → ι) (h : ∀ c, κ (f c) = κ' c) : Layout μ ι' κ' where
  read := fun q c ↦ ⟨Vector.cast (congrArg (2 ^ ·) (h c)) (L.read q (f c)).values⟩
  extend := fun c z ↦ L.extend (f c) (Vector.cast (h c).symm z)
  read_eval := fun q c z ↦ by
    have hz : z = Vector.cast (h c) (Vector.cast (h c).symm z) := by simp
    conv_lhs => rw [hz]
    rw [eval₂Mle_cast, L.read_eval]

namespace Blocks

/-! ## Stacking and reading columns -/

section Columns

variable (B : Blocks) {μ : ℕ}

/-- The columns stacked on `μ` variables, zero past the last block: the witness stack (§4.1). -/
def stackColumn (t : B.Tables K) (μ : ℕ) : Column μ := ⟨B.stackAt t μ 0⟩

/-- Read block `b` off a column of height `2 ^ μ`: the cells of the block's window. -/
def readColumn (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n) : Column (B.size b) :=
  ⟨B.unstack hμ q.values b⟩

/-- The stacking identity, for every column `q`: the block read off `q`, evaluated at `z`, is
`q` evaluated at `(z, sel_b)`. -/
theorem readColumn_eval (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n)
    (z : Vector E (B.size b)) :
    eval₂Mle (B.readColumn hμ q b).values (algebraMap K E) z =
      eval₂Mle q.values (algebraMap K E) (B.extendPoint hμ b z) :=
  (B.unstack_eval₂ (algebraMap K E) hμ q.values b z).symm

/-- Reading a block off the honest stack returns the block. -/
@[simp] theorem readColumn_stackColumn (t : B.Tables K) (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) :
    B.readColumn hμ (B.stackColumn t μ) b = ⟨t b⟩ :=
  congrArg Column.mk (B.unstack_stackAt t hμ 0 b)

/-- The honest stack at `(z, sel_b)` is block `b` at `z`. -/
theorem stackColumn_eval (t : B.Tables K) (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (z : Vector E (B.size b)) :
    eval₂Mle (B.stackColumn t μ).values (algebraMap K E) (B.extendPoint hμ b z) =
      eval₂Mle (t b) (algebraMap K E) z :=
  B.stack_eval₂ (algebraMap K E) t hμ 0 b z

/-- The aligned blocks as a reading law on the committed column. -/
def layout (hμ : B.total ≤ 2 ^ μ) : Layout μ (Fin B.n) B.size where
  read := B.readColumn hμ
  extend := B.extendPoint hμ
  read_eval := B.readColumn_eval hμ

/-- The honest stack at an arbitrary point `ζ`: every block at the low coordinates of `ζ`,
weighted by the equality kernel of its selector at the high coordinates. -/
theorem stackColumn_eval_ambient (t : B.Tables K) (hμ : B.total ≤ 2 ^ μ) (ζ : Vector E μ) :
    eval₂Mle (B.stackColumn t μ).values (algebraMap K E) ζ =
      ∑ b : Fin B.n, B.selectorWeight hμ b ζ *
        eval₂Mle (t b) (algebraMap K E) (B.lowPoint hμ b ζ) := by
  have h := B.stack_eval₂_ambient (algebraMap K E) t hμ 0 ζ
  rw [map_zero, zero_mul, add_zero] at h
  exact h

end Columns

/-! ## The one-padded stack in characteristic two -/

/-- The one-padded stack of `E`-tables at an arbitrary point (§5.4, equation (2)): the blocks'
weighted evaluations, plus the weight `1 + Σ_b eq(sel_b, ζ_hi)` of the uncovered cells. -/
theorem stack_eval_ambient_one (B : Blocks) (t : B.Tables E) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (ζ : Vector E μ) :
    evalMle (B.stackAt t μ 1) ζ =
      (∑ b : Fin B.n, B.selectorWeight hμ b ζ * evalMle (t b) (B.lowPoint hμ b ζ)) +
        (1 + ∑ b : Fin B.n, B.selectorWeight hμ b ζ) := by
  rw [B.stack_eval_ambient t hμ 1 ζ, one_mul, CharTwo.sub_eq_add]

end Blocks

end
end LeanerVM.Protocol
