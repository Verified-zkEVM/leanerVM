/-
  LeanerVM.Protocol.Whir.Word

  The interleaved word WHIR commits to, as an oracle read at sampled positions, and the word of
  a table.
-/

module

public import LeanerVM.Protocol.WhirFold
public import LeanerVM.Protocol.ToArkLib.Oracles

/-!
# The committed word

A level of WHIR commits to the interleaved word of its table: at each position `y` of the code's
domain a *row* of `2 ^ ℓ` symbols, one per lane. `Word ℓ b t` is such a word on `2 ^ b`
positions, read `t` positions at a time: a question is `t` positions and the answer their `t`
rows (the verifier of a level samples its query positions and reads the rows at them together;
the query count is in the oracle's type on purpose, so that the positions are one challenge and
the answer one message).
`wordOf f` is the honest word of the table `f`, the encodings of its lanes (`encode` of
`sliceLow f u`, `LeanerVM.Protocol.WhirFold`), and `foldRow r` folds a row by the fold point `r`:
`foldRow_wordOf` is `fact:fold-decode` in the shape the verifier uses it, the folded row at `y` is
the folded table's encoding at `y`.

The rows are `E`-valued at every level. At level 0 they are `K`-valued (`isInK_encode_ofK`); the
verifier never checks it, since it reads the symbols as `E` elements, and completeness does not
use it.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec

@[expose] public section

namespace Whir

/-- An interleaved word on `2 ^ b` positions with `2 ^ ℓ` lanes, to be read `t` positions at a
time. -/
structure Word (ℓ b t : ℕ) where
  /-- The row at a position. -/
  row : Fin (2 ^ b) → Vector E (2 ^ ℓ)

/-- A question to a word is `t` positions; the answer is their rows. -/
instance (ℓ b t : ℕ) : OracleInterface (Word ℓ b t) where
  Query := Fin t → Fin (2 ^ b)
  toOC :=
    { spec := (Fin t → Fin (2 ^ b)) →ₒ (Fin t → Vector E (2 ^ ℓ))
      impl := fun q ↦ do
        let w ← read
        return fun k ↦ w.row (q k) }

/-- The honest word of a table: at position `y`, the row of the lanes' encodings. -/
def wordOf (ℓ κ R t : ℕ) (f : CMlPolynomialEval E (ℓ + κ)) : Word ℓ (κ + R) t :=
  ⟨fun y ↦ Vector.ofFn fun u ↦ encode (algebraMap K E) κ R (sliceLow f u) y⟩

/-- A row folded by the fold point: `Σ_u eq(r, u) · row[u]`. -/
def foldRow {ℓ : ℕ} (r : Vector E ℓ) (row : Vector E (2 ^ ℓ)) : E :=
  ∑ u : Fin (2 ^ ℓ), (lagrangeBasis r)[u] * row[u]

/-- `fact:fold-decode`: the folded row at a position is the folded table's encoding there. -/
theorem foldRow_wordOf {ℓ κ : ℕ} (R t : ℕ) (f : CMlPolynomialEval E (ℓ + κ))
    (r : Vector E ℓ)
    (y : Fin (2 ^ (κ + R))) :
    foldRow r ((wordOf ℓ κ R t f).row y) = encode (algebraMap K E) κ R (foldTable f r) y := by
  rw [encode_foldTable]
  simp [foldRow, wordOf]

end Whir

end

end LeanerVM.Protocol
