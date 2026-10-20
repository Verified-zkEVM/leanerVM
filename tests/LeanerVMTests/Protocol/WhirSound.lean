import LeanerVM.Protocol.Whir.OpenSound
import LeanerVM.Protocol.Whir.Exact

/-!
# The soundness of the opening: an instance

`whirOpen_rbrSoundness` takes, per level, the parameters of the level's code: the agreement
threshold, the list bound and the mutual-correlated-agreement bound, with the two interfaces that
the coding theory provides. At exact agreement (`a = 2 ^ (κ + R)`, radius `0`) both interfaces hold
with the constants `1` (`listBound_exact`, `mcaJohnson_exact`), so the theorem applies, from the
encoder alone, to the toy chain of `WhirOpen`: two levels of one lane at rate `2⁻¹`, one query,
a plaintext table of one variable.

* **The parameters are inhabited.** The threshold is the number of positions, the lists have one
  element, the bad folds one: a `Par` for each level.
* **The theorem applies.** `soundOpen` is the security half of `whirOpen` on the toy chain, at the
  errors `openErr`.
* **The errors are the pinned entries.** At the first fold challenge the error is `2 L / |E|` plus
  `2 ^ (ℓ - 1) N / |E|` (`foldErr_eq`), and the query positions' is `(a / 2 ^ (κ + R)) ^ t`, here
  `1`: at exact agreement every position is among those a cheating prover needs, and the bound is
  the trivial one (`positions_err_eq`).
-/

namespace LeanerVMTests.Protocol.WhirSoundToy

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Whir

/-- The first level: one lane, rate `2⁻¹`, one query. -/
def sound0 : Shape := ⟨0, 1, 1⟩

/-- The last level. -/
def sound1 : Shape := ⟨0, 1, 1⟩

/-- The chain. -/
def soundLadder : Ladder sound0 (Kap sound1 (0 + 1)) := .cons sound0 (.last sound1 0)

/-- The first level's parameters: exact agreement. -/
def soundPar0 : Par sound0 (Kap sound1 (0 + 1)) where
  a := 2 ^ (Kap sound1 (0 + 1) + sound0.R)
  L := 1
  N := 1
  hdist := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
  hb := by decide
  hlist := listBound_exact _ (by decide)
  hmca := mcaJohnson_exact

/-- The last level's parameters: exact agreement. -/
def soundPar1 : Par sound1 (0 + 1) where
  a := 2 ^ (0 + 1 + sound1.R)
  L := 1
  N := 1
  hdist := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
  hb := by decide
  hlist := listBound_exact _ (by decide)
  hmca := mcaJohnson_exact

/-- The parameters of the chain. -/
def soundPars : soundLadder.Pars := (soundPar0, soundPar1)

/-- The opening's soundness, applied. -/
noncomputable def soundOpen := whirOpen_rbrSoundness soundLadder soundPars

-- the first fold challenge's error is the pinned entry
example : foldErr soundPar0 0 = (2 * 1 : NNReal) / (Nat.card E : NNReal) +
    2 ^ (sound0.ℓ - 0 - 1) * ((1 : NNReal) / (Nat.card E : NNReal)) := by
  have := foldErr_eq soundPar0 0
  simpa [soundPar0] using this

-- the positions' error is `(a / N) ^ t`
example : ((soundPar0.a ^ sound0.t : ℕ) : NNReal) /
    (Nat.card (Fin sound0.t → Fin (2 ^ (Kap sound1 (0 + 1) + sound0.R))) : NNReal) =
      ((soundPar0.a : NNReal) / (2 ^ (Kap sound1 (0 + 1) + sound0.R) : ℕ)) ^ sound0.t :=
  positions_err_eq _ _ _

end LeanerVMTests.Protocol.WhirSoundToy
