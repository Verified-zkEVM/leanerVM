/-
  LeanerVM.Protocol.Verify.Erase

  What the executable verifier's algebra reads of the wire: neither the roots nor the grinding
  nonces, and WHIR's query positions only as reduced below their words' sizes.
-/

module

public import LeanerVM.Protocol.Verify

/-!
# What the algebra reads

The chain walk records everything it reads (`Verify.Wire`), the algebra (`Verify.algebra`) reads
less. The roots are read only by the openings (`walkOpenings`), against the positions; the
grinding nonce only by the walk, which checks it (`ChainOps.checkPow`); WHIR's positions only
through `positionsOf`, reduced below the word's size. `Wire.erase shs w` forgets the roots and
the nonces and reduces the positions, and **`algebra_erase`**: the algebra on a wire is the algebra
on its erasure. Two wires with the same erasure are accepted alike, whatever their roots and
nonces: the nonce a prover grinds and the nonce an oracle transcript carries make no difference to
the algebra.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa CompPoly CMlPolynomialEval

@[expose] public section

namespace Verify

/-- The positions of a word of `2 ^ b` positions, reduced below its size, `t` of them. -/
def reducePositions (t b : ℕ) (ps : List ℕ) : List ℕ :=
  List.ofFn fun q : Fin t ↦ (positionsOf t b ps q).val

/-- Reduced positions index the word as the positions do. -/
private theorem positionsOf_reducePositions (t b : ℕ) (ps : List ℕ) :
    positionsOf t b (reducePositions t b ps) = positionsOf t b ps := by
  funext q
  apply Fin.ext
  simp [positionsOf, reducePositions, List.getD_eq_getElem?_getD, Nat.mod_mod_of_dvd]

/-- A level's wire with what the algebra does not read forgotten: its root and its nonce, and its
positions reduced below its word's size. -/
def WhirLevel.erase (sh : LevelShape) (l : WhirLevel) : WhirLevel :=
  { l with root := none, nonce := 0,
           positions := reducePositions sh.queries (sh.msgLog + sh.rate) l.positions }

/-- The levels' wires erased, each at its shape; levels past the shapes are kept. -/
def eraseLevels : List LevelShape → List WhirLevel → List WhirLevel
  | sh :: shs, l :: ls => l.erase sh :: eraseLevels shs ls
  | _, ls => ls

/-- A wire with what the algebra does not read forgotten: the commitment root, every level's
root and nonce, and the levels' positions reduced. -/
def Wire.erase (shs : List LevelShape) (w : Wire) : Wire :=
  { w with root := default, whir := eraseLevels shs w.whir }

/-- WHIR's algebra does not read the levels' roots and nonces, and reads their positions
reduced. -/
private theorem whirLevels_eraseLevels : ∀ (shs : List LevelShape) (first : Bool) (n : ℕ)
    (W : Weight E n) (claim : E) (quad : Vector E 3) (ls : List WhirLevel)
    (rows : List (List (List K))),
    whirLevels first n W claim quad shs (eraseLevels shs ls) rows =
      whirLevels first n W claim quad shs ls rows
  | [], _, _, _, _, _, ls, _ => by simp only [eraseLevels]
  | _ :: _, _, _, _, _, _, [], _ => by simp only [eraseLevels]
  | _ :: _, _, _, _, _, _, _ :: _, [] => by simp only [eraseLevels, whirLevels]
  | sh :: shs, first, n, W, claim, quad, l :: ls, r :: rs => by
    simp only [eraseLevels, whirLevels, WhirLevel.erase, positionsOf_reducePositions,
      whirLevels_eraseLevels shs]

/-- **The algebra does not read the roots or the nonces**, and reads WHIR's positions reduced:
it accepts a wire exactly when it accepts the wire erased. -/
theorem algebra_erase (prog : Program) (s : Sizes) (input : PublicInput)
    (shs : List LevelShape) (w : Wire) (rows : List (List (List K))) :
    algebra prog s input shs (w.erase shs) rows = algebra prog s input shs w rows := by
  simp only [algebra, Wire.erase, whirCheck, whirLevels_eraseLevels]

end Verify

end
end LeanerVM.Protocol
