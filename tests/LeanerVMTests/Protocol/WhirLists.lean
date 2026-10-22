import LeanerVM.Protocol.Whir.Stage

/-!
# Lists of codewords and folds: tests

The vocabulary of the soundness of WHIR's opening on a toy code, `κ = 2` message variables at
rate `2⁻¹` (`R = 1`: eight positions, messages of four entries, so a codeword is a polynomial of
degree below four in the novel basis). A plain file, so `#guard` evaluates the compiled
definitions.

* **The minimum distance.** Two distinct messages' codewords agree on fewer than `2 ^ κ = 4`
  positions; messages that differ in the top coefficient only agree where `X_3 = Ŵ_0 Ŵ_1` vanishes,
  on the two positions `0` and `1`.
* **Agreement.** `Cl` counts positions: a word that agrees with a codeword everywhere is within
  every threshold; one position corrupted, within every threshold up to seven and no more. The
  threshold is "at least", not "more than".
* **Folds.** The fold of a lane word at several challenges is the stepwise fold (`foldW_push`),
  and likewise for messages (`foldM_push`); the fold of an interleaved codeword near a word is
  near the fold of the word (the easy half of `lem:fold-list`), and a corrupted position is a
  corrupted position of the fold.
-/

namespace LeanerVMTests.Protocol.WhirListsToy

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Whir CompPoly CMlPolynomialEval

/-- An element of `E`. -/
def eL (a b : ℕ) : E := algebraMap K E (K.ofBits a) + y * algebraMap K E (K.ofBits b)

/-- A message of four entries. -/
def msg (a : ℕ) : CMlPolynomialEval E 2 :=
  Vector.ofFn fun i : Fin 4 ↦ eL (a * (i.val + 1) + 3) (a + i.val)

/-- The same message with its top coefficient changed. -/
def msgTop (a : ℕ) : CMlPolynomialEval E 2 := (msg a).set 3 ((msg a)[3] + 1)

/-- The same message with its second coefficient changed. -/
def msgMid (a : ℕ) : CMlPolynomialEval E 2 := (msg a).set 1 ((msg a)[1] + 1)

/-- The positions where two messages' codewords agree. -/
def agreeCount (m m' : CMlPolynomialEval E 2) : ℕ :=
  (Finset.univ.filter fun v : Fin 8 ↦
    encode (algebraMap K E) 2 1 m v = encode (algebraMap K E) 2 1 m' v).card

/-! ## The minimum distance -/

-- a codeword agrees with itself everywhere
#guard agreeCount (msg 5) (msg 5) = 8
-- distinct messages agree on fewer than four positions
#guard agreeCount (msg 5) (msgTop 5) < 4
#guard agreeCount (msg 5) (msgMid 5) < 4
#guard agreeCount (msg 5) (msg 9) < 4
-- the top coefficient alone: the difference is a multiple of X_3, with roots 0 and 1
#guard agreeCount (msg 5) (msgTop 5) = 2

/-! ## Agreement -/

/-- The honest lane word of a two-lane codeword. -/
def lanesOfMsgs (V : Msgs 1 2) : LW (2 + 1) := fun y u ↦
  if h : u < 2 then encode (algebraMap K E) 2 1 (V ⟨u, by simpa using h⟩) y else 0

/-- Two lanes of messages. -/
def V0 : Msgs 1 2 := fun u ↦ msg (7 + u.val)

/-- The same lane word with the position `3` of lane `0` corrupted. -/
def corrupted : LW (2 + 1) := fun y u ↦
  if y.val = 3 ∧ u = 0 then lanesOfMsgs V0 y u + 1 else lanesOfMsgs V0 y u

-- within every threshold of itself
#guard decide (Cl 2 1 8 1 (lanesOfMsgs V0) V0)
-- one corruption: within seven, not within eight
#guard decide (Cl 2 1 7 1 corrupted V0)
#guard !decide (Cl 2 1 8 1 corrupted V0)

/-! ## Folds -/

def c1 : E := eL 0x1d 0x3
def c2 : E := eL 0x77 0x1
def cs2 : Vector E 2 := #v[c1, c2]

/-- A lane word of four lanes. -/
def F4 : LW (2 + 1) := fun y u ↦
  if u < 4 then encode (algebraMap K E) 2 1 (msg (3 + u)) y else 0

/-- The messages of four lanes. -/
def V4 : Msgs 2 2 := fun u ↦ msg (3 + u.val)

-- the lane word folded at two challenges is the stepwise fold
#guard ∀ y : Fin 8, foldW (cs2) F4 y 0 = fold1W c2 (foldW #v[c1] F4) y 0
#guard ∀ y : Fin 8, foldW (cs2) F4 y 0 = fold1W c2 (fold1W c1 F4) y 0
-- and the messages
#guard foldM 0 cs2 V4 ⟨0, by decide⟩ =
  comb (1 - c2) c2 (foldM 1 #v[c1] V4 ⟨0, by decide⟩) (foldM 1 #v[c1] V4 ⟨1, by decide⟩)
-- folding nothing is the identity on the lane word
#guard ∀ y : Fin 8, ∀ u : Fin 4, foldW (#v[] : Vector E 0) F4 y u = F4 y u
-- the fold of an honest interleaved codeword is near the fold of the word
#guard decide (Cl 2 1 8 1 (fold1W c1 F4) (fold1M c1 V4))
-- a corrupted position is a corrupted position of the fold
#guard !decide (Cl 2 1 8 1 (fold1W c1 (fun y u ↦
  if y.val = 3 ∧ u = 0 then F4 y u + 1 else F4 y u)) (fold1M c1 V4))

end LeanerVMTests.Protocol.WhirListsToy
