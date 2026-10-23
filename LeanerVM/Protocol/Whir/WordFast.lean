/-
  LeanerVM.Protocol.Whir.WordFast

  The honest words of WHIR's levels by the additive transform, with their rows stored: proved
  equal to the encoder's words and substituted for them in compiled code.
-/

module

public import LeanerVM.Protocol.Whir.Word
public import LeanerVM.Protocol.Whir.Transform

/-!
# The honest words by the transform

`wordOf` and `kwordOf` give a word's row at a position by encoding every lane at that position,
`2 ^ κ` products per symbol. `wordOfFast` and `kwordOfFast` encode each lane once on the whole
domain by the transform (`encodeFast`, `κ · 2 ^ (κ - 1)` products per coset) and store the rows;
on `κ + R ≤ 64` variables they are the encoder's words (`wordOfFast_eq`, `kwordOfFast_eq`, from
`encodeFast_getElem`). `wordOfImpl` and `kwordOfImpl` take the transform on that window and the
encoder outside it, so they equal `wordOf` and `kwordOf` everywhere, and the `@[csimp]` theorems
`wordOf_eq_wordOfImpl` and `kwordOf_eq_kwordOfImpl` substitute them in code compiled after them:
the honest provers of the levels and of the commitment build each word once. No definition a
theorem states changes.

The stored rows are captured by the word's row function, so the word must be built as a value:
a word returned as a bare function would be eta-expanded by the compiler and rebuilt at every
read, while the one-field structure `Word` is not.

Category A: the encoder `encode` is the specification; nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

namespace Whir

/-! ## The words by the transform -/

/-- **The honest word by the transform**: `wordOf`, with one fast encoding per lane and the rows
stored. -/
def wordOfFast (ℓ κ R t : ℕ) (f : CMlPolynomialEval E (ℓ + κ)) : Word ℓ (κ + R) t :=
  let enc : Vector (Vector E (2 ^ (κ + R))) (2 ^ ℓ) :=
    Vector.ofFn fun u ↦ encodeFast (algebraMap K E) κ R (sliceLow f u)
  let rows : Vector (Vector E (2 ^ ℓ)) (2 ^ (κ + R)) :=
    Vector.ofFn fun y ↦ Vector.ofFn fun u ↦ enc[u][y]
  ⟨fun y ↦ rows[y]⟩

/-- The honest word by the transform is the honest word, on `κ + R ≤ 64` variables. -/
theorem wordOfFast_eq {ℓ κ R t : ℕ} (hb : κ + R ≤ 64) (f : CMlPolynomialEval E (ℓ + κ)) :
    wordOfFast ℓ κ R t f = wordOf ℓ κ R t f := by
  unfold wordOfFast wordOf
  dsimp only
  congr 1
  funext y
  apply Vector.ext
  intro u hu
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exact encodeFast_getElem _ hb _ y

/-- **The honest `K` word by the transform**: `kwordOf`, with one fast encoding per lane and the
rows stored. -/
def kwordOfFast (ℓ κ R t : ℕ) (q : CMlPolynomialEval K (κ + ℓ)) : KWord ℓ (κ + R) t :=
  let r := relayout (κ := κ) (ℓ := ℓ) q
  let enc : Vector (Vector K (2 ^ (κ + R))) (2 ^ ℓ) :=
    Vector.ofFn fun u ↦ encodeFast (RingHom.id K) κ R (sliceLow r u)
  let rows : Vector (Vector K (2 ^ ℓ)) (2 ^ (κ + R)) :=
    Vector.ofFn fun y ↦ Vector.ofFn fun u ↦ enc[u][y]
  ⟨fun y ↦ rows[y]⟩

/-- The honest `K` word by the transform is the honest `K` word, on `κ + R ≤ 64` variables. -/
theorem kwordOfFast_eq {ℓ κ R t : ℕ} (hb : κ + R ≤ 64) (q : CMlPolynomialEval K (κ + ℓ)) :
    kwordOfFast ℓ κ R t q = kwordOf ℓ κ R t q := by
  unfold kwordOfFast kwordOf
  dsimp only
  congr 1
  funext y
  apply Vector.ext
  intro u hu
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exact encodeFast_getElem _ hb _ y

/-! ## The substitution in compiled code -/

/-- `wordOf` by the transform where it applies, by the encoder elsewhere. -/
def wordOfImpl (ℓ κ R t : ℕ) (f : CMlPolynomialEval E (ℓ + κ)) : Word ℓ (κ + R) t :=
  if κ + R ≤ 64 then wordOfFast ℓ κ R t f
  else ⟨fun y ↦ Vector.ofFn fun u ↦ encode (algebraMap K E) κ R (sliceLow f u) y⟩

/-- Compiled code builds an honest word by the transform. -/
@[csimp] theorem wordOf_eq_wordOfImpl : @wordOf = @wordOfImpl := by
  funext ℓ κ R t f
  unfold wordOfImpl
  split
  · exact (wordOfFast_eq ‹_› f).symm
  · rfl

/-- `kwordOf` by the transform where it applies, by the encoder elsewhere. -/
def kwordOfImpl (ℓ κ R t : ℕ) (q : CMlPolynomialEval K (κ + ℓ)) : KWord ℓ (κ + R) t :=
  if κ + R ≤ 64 then kwordOfFast ℓ κ R t q
  else ⟨fun y ↦ Vector.ofFn fun u ↦ encode (RingHom.id K) κ R (sliceLow (relayout q) u) y⟩

/-- Compiled code builds an honest `K` word by the transform. -/
@[csimp] theorem kwordOf_eq_kwordOfImpl : @kwordOf = @kwordOfImpl := by
  funext ℓ κ R t q
  unfold kwordOfImpl
  split
  · exact (kwordOfFast_eq ‹_› q).symm
  · rfl

end Whir

end

end LeanerVM.Protocol
