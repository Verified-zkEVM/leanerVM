/-
  LeanerVM.Protocol.Stack

  Aligned stacking on leanVM's columns: `K`-columns stacked into one committed column, read back
  block by block, and evaluated at points of `E`.
-/

module

public import LeanerVM.Protocol.Spine.Instance
public import LeanerVM.Protocol.ToArkLib.AmbientStacking

/-!
# The stack of columns

The generic stacking of `ToArkLib/Stacking.lean`, specialised to the two fields of leanVM: the
blocks are columns over `K`, the stack is the one committed column, and every evaluation is at a
point of `E`, the column oracle's answer there (`evalOracle_answer`; specification §4.1).

* `Blocks.stack` is the witness stack: block `b` at its window, zero past the last block.
* `Blocks.readColumn` reads block `b` off *any* column of the stack's height, honest or not, and
  `Blocks.extendPoint` lifts a point `z` of the block to the point `(z, sel_b)` of the stack.
  `Blocks.readColumn_eval` is the stacking identity `q̃(z, sel_b) = P̃_b(z)`, for every `q`.
* `Blocks.layout` packages the two with that identity as a `Layout`, the reading law an
  `M3Instance` carries. Only the sizes of the blocks enter it, never their values.
* `Blocks.eval_stack` is the decomposition of the zero-padded stack at an arbitrary point, and
  `Blocks.eval_stackAt_one` the one-padded form over `E`, with the padding term written as the
  specification writes it in characteristic two, `1 + Σ_b eq(sel_b, ζ_hi)` (§5.4, equation
  (5.4)).

Written from the specification; nothing here transcribes Rust.

## Wrong readings excluded

* The reading law quantifies over every column `q`, not only over honest stacks: a knowledge
  extractor reads the blocks off whatever the prover committed.
* The padding term of the one-padded stack is the weight of the *uncovered* part of the cube,
  not the constant `1`; it vanishes exactly when the blocks fill the stack.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

namespace Blocks

/-! ## Stacking and reading columns -/

section Columns

variable (B : Blocks K) {μ : ℕ}

/-- The columns stacked on `μ` variables, zero past the last block: the witness stack (§4.1). -/
def stack (μ : ℕ) : Column μ := ⟨B.stackAt μ 0⟩

/-- Block `b` as a column. -/
def column (b : Fin B.n) : Column (B.size b) := ⟨B.values b⟩

/-- Read block `b` off a column of height `2 ^ μ`: the cells of the block's window. -/
def readColumn (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n) : Column (B.size b) :=
  ⟨B.unstack hμ q.values b⟩

/-- Lift a point of block `b` to the stack: the point, then the block's selector bits. -/
def extendPoint (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (z : Vector E (B.size b)) : Vector E μ :=
  Vector.cast (Nat.add_sub_cancel' (B.size_le hμ b))
    (z ++ (boolVec (B.selector hμ b) : Vector E (μ - B.size b)))

/-- The stacking identity, for every column `q`: the block read off `q`, evaluated at `z`, is
`q` evaluated at `(z, sel_b)`. -/
theorem readColumn_eval (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n)
    (z : Vector E (B.size b)) :
    eval₂Mle (B.readColumn hμ q b).values (algebraMap K E) z =
      eval₂Mle q.values (algebraMap K E) (B.extendPoint hμ b z) :=
  (B.unstack_eval₂ (algebraMap K E) hμ q.values b z).symm

/-- Reading a block off the honest stack returns the block. -/
@[simp] theorem readColumn_stack (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) :
    B.readColumn hμ (B.stack μ) b = B.column b :=
  congrArg Column.mk (B.unstack_stackAt hμ 0 b)

/-- The honest stack at `(z, sel_b)` is block `b` at `z`. -/
theorem eval_stack_extendPoint (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n)
    (z : Vector E (B.size b)) :
    eval₂Mle (B.stack μ).values (algebraMap K E) (B.extendPoint hμ b z) =
      eval₂Mle (B.column b).values (algebraMap K E) z := by
  rw [← B.readColumn_eval hμ, readColumn_stack]

/-- The aligned blocks as a reading law on the committed column. -/
def layout (hμ : B.total ≤ 2 ^ μ) : Layout μ (Fin B.n) B.size where
  read := B.readColumn hμ
  extend := B.extendPoint hμ
  read_eval := B.readColumn_eval hμ

/-- The honest stack at an arbitrary point `ζ`: every block at the low coordinates of `ζ`,
weighted by the equality kernel of its selector at the high coordinates. -/
theorem eval_stack (hμ : B.total ≤ 2 ^ μ) (ζ : Vector E μ) :
    eval₂Mle (B.stack μ).values (algebraMap K E) ζ =
      ∑ b : Fin B.n, (B.map (algebraMap K E)).selectorWeight hμ b ζ *
        eval₂Mle (B.column b).values (algebraMap K E)
          ((B.map (algebraMap K E)).lowPoint hμ b ζ) := by
  have h := B.stack_eval₂_ambient (algebraMap K E) hμ 0 ζ
  rw [map_zero, zero_mul, add_zero] at h
  exact h

end Columns

/-! ## The one-padded stack in characteristic two -/

/-- The one-padded stack of `E`-tables at an arbitrary point (§5.4, equation (5.4)): the blocks'
weighted evaluations, plus the weight `1 + Σ_b eq(sel_b, ζ_hi)` of the uncovered cells. -/
theorem eval_stackAt_one (B : Blocks E) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (ζ : Vector E μ) :
    evalMle (B.stackAt μ 1) ζ =
      (∑ b : Fin B.n, B.selectorWeight hμ b ζ * evalMle (B.values b) (B.lowPoint hμ b ζ)) +
        (1 + ∑ b : Fin B.n, B.selectorWeight hμ b ζ) := by
  rw [B.stack_eval_ambient_one hμ ζ, CharTwo.sub_eq_add]

end Blocks

end
end LeanerVM.Protocol
