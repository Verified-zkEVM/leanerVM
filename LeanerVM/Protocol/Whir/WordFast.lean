/-
  LeanerVM.Protocol.Whir.WordFast

  The honest level-0 word by the additive transform: its rows computed once and stored, proved
  equal to the encoder's word.
-/

module

public import LeanerVM.Protocol.Whir.Word
public import LeanerVM.Protocol.Whir.Transform

/-!
# The level-0 word by the transform

`kwordOf` gives the level-0 word's row at a position by encoding every lane at that position,
`2 ^ κ` products per symbol. `kwordRows` encodes each lane once on the whole domain by the
transform (`encodeFast`, `κ · 2 ^ (κ - 1)` products per coset) and lays the encodings out as rows;
`kwordOfFast` is the word reading them. On `κ + R ≤ 64` variables it is the encoder's word
(`kwordOfFast_eq`, from `encodeFast_getElem`; `ofRows_kwordRows` for the word read off any
stored copy of the rows).

A word built by a function that returns it is a function in compiled code, and a closure that
returns one is expanded to take the position as one more argument, which rebuilds the word at
every read. A prover that reads a word's every row must therefore keep its rows as data, built
once, and read them through the word (`KWord.ofRows`).

Category A: the encoder `encode` is the specification; nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

namespace Whir

/-- A word reading stored rows. -/
def KWord.ofRows {ℓ b t : ℕ} (rows : Vector (Vector K (2 ^ ℓ)) (2 ^ b)) : KWord ℓ b t :=
  ⟨fun y ↦ rows[y]⟩

/-- The rows of the honest `K` word, each lane encoded once by the transform. -/
def kwordRows (ℓ κ R : ℕ) (q : CMlPolynomialEval K (κ + ℓ)) :
    Vector (Vector K (2 ^ ℓ)) (2 ^ (κ + R)) :=
  let r := relayout (κ := κ) (ℓ := ℓ) q
  let enc : Vector (Vector K (2 ^ (κ + R))) (2 ^ ℓ) :=
    Vector.ofFn fun u ↦ encodeFast (RingHom.id K) κ R (sliceLow r u)
  Vector.ofFn fun y ↦ Vector.ofFn fun u ↦ enc[u][y]

/-- **The honest `K` word by the transform**: `kwordOf`, with one fast encoding per lane and the
rows stored. -/
def kwordOfFast (ℓ κ R t : ℕ) (q : CMlPolynomialEval K (κ + ℓ)) : KWord ℓ (κ + R) t :=
  let rows := kwordRows ℓ κ R q
  KWord.ofRows rows

/-- The word reading the transform's rows is the honest `K` word, on `κ + R ≤ 64` variables. -/
theorem ofRows_kwordRows {ℓ κ R t : ℕ} (hb : κ + R ≤ 64) (q : CMlPolynomialEval K (κ + ℓ)) :
    (KWord.ofRows (kwordRows ℓ κ R q) : KWord ℓ (κ + R) t) = kwordOf ℓ κ R t q := by
  unfold KWord.ofRows kwordRows kwordOf
  dsimp only
  congr 1
  funext y
  apply Vector.ext
  intro u hu
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exact encodeFast_getElem _ hb _ y

/-- The honest `K` word by the transform is the honest `K` word, on `κ + R ≤ 64` variables. -/
theorem kwordOfFast_eq {ℓ κ R t : ℕ} (hb : κ + R ≤ 64) (q : CMlPolynomialEval K (κ + ℓ)) :
    kwordOfFast ℓ κ R t q = kwordOf ℓ κ R t q :=
  ofRows_kwordRows hb q

end Whir

end

end LeanerVM.Protocol
