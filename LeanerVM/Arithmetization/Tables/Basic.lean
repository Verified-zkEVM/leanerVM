/-
  LeanerVM.Arithmetization.Tables.Basic

  The vocabulary shared by the six opcode tables: a row's three-limb words, the limbs of an
  image word read back, and the `Option` lemma that turns a `guard` of `execute` into an
  equation. A plain (non-`module`) file: it imports Clean through the channels of Layer 5.
-/

import LeanerVM.Arithmetization.Channels

/-!
# Shared vocabulary of the tables

leanISA roadmap Layer 6 (`docs/roadmap/leanisa-blueprint.md`). Category A: nothing here is
transcribed; the file names what every table's contract says in the same words.

* `word v` is the `E` word of a row's three-limb column `v`, `E.ofLimbs v[0] v[1] v[2]`, the
  word `MemPull.Guarantees` reads off a memory message (Layer 5).
* `limbsAt L a` reads the word at `a` back into limbs. It is noncomputable, since
  `MemImage.read` is (Layer 2): it is the vocabulary of the row builders, which say which row
  a step admits, not a generator that runs. `word (limbsAt L a) = v` whenever
  `L.read a = some v` (`word_limbsAt`).
* `guard_bind_eq_some_iff` is the one `Option` fact the `*_spec_iff` characterisations need:
  `execute` checks each relation with `guard`, and `guard p >>= f = some b` says `p` and
  `f () = some b`.
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

/-- The `E` word of a row's three-limb column. -/
def word (v : Vector K 3) : E := E.ofLimbs v[0] v[1] v[2]

/-- The three limbs of a word. -/
def limbs (x : E) : Vector K 3 := #v[x.limb 0, x.limb 1, x.limb 2]

/-- A word's limbs form the word. -/
theorem word_limbs (x : E) : word (limbs x) = x := ofLimbs_limb x

/-- The limbs of the image's word at `a`, zero when there is none. Noncomputable: it reads the
image through `MemImage.read`. -/
noncomputable def limbsAt {κ : ℕ} (L : MemImage κ) (a : K) : Vector K 3 :=
  match L.read a with
  | some v => limbs v
  | none => #v[0, 0, 0]

/-- The limbs read back at an address that holds a word form that word. -/
theorem word_limbsAt {κ : ℕ} {L : MemImage κ} {a : K} {v : E} (h : L.read a = some v) :
    word (limbsAt L a) = v := by
  unfold limbsAt
  rw [h]
  exact word_limbs v

/-- The low limb read back at an address that holds a word is the word's. -/
theorem limbsAt_getElem_zero {κ : ℕ} {L : MemImage κ} {a : K} {v : E} (h : L.read a = some v) :
    (limbsAt L a)[0] = v.limb 0 := by
  unfold limbsAt
  rw [h]
  rfl

/-- A word in `K` is its low limb with zeros above. -/
theorem ofLimbs_of_isInK {x : E} (h : IsInK x) : E.ofLimbs (x.limb 0) 0 0 = x :=
  calc E.ofLimbs (x.limb 0) 0 0 = E.ofLimbs (x.limb 0) (x.limb 1) (x.limb 2) := by rw [h.1, h.2]
    _ = x := ofLimbs_limb x

/-- `ofK a` is the word with limbs `(a, 0, 0)`. -/
theorem ofK_eq_ofLimbs (a : K) : ofK a = E.ofLimbs a 0 0 :=
  E.ext fun i ↦ by fin_cases i <;> simp

/-- A word with zero upper limbs lies in `K`. -/
theorem isInK_ofLimbs (c : K) : IsInK (E.ofLimbs c 0 0) := ⟨by simp, by simp⟩

/-- The prover environment of a row of a table without local witnesses: no witness slots
(every slot reads `0`), the data, no hints. -/
def rowEnv (data : ProverData K) : ProverEnvironment K := ⟨⟨fun _ ↦ 0, data⟩, default⟩

/-- A guarded `Option` computation succeeds exactly when the guard holds and the rest does. -/
theorem guard_bind_eq_some_iff {α : Type} (p : Prop) [Decidable p] (f : Unit → Option α)
    (b : α) : Option.bind (guard p) f = some b ↔ p ∧ f () = some b := by
  unfold guard
  split_ifs with h
  · simp [h]
  · simp [h]

/-- A guard that succeeds holds. -/
theorem guard_eq_some {p : Prop} [Decidable p] {u : Unit} (h : (guard p : Option Unit) = some u) :
    p := by
  unfold guard at h
  split_ifs at h with hp
  exact hp

end LeanerVM.Arithmetization
