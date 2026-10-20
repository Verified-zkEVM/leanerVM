/-
  LeanerVMTests.Protocol.WhirFold

  The fold of the interleaved word at toy sizes, with K and E challenges, and the readings that
  compile and are wrong.
-/

import LeanerVM.Protocol.WhirFold

/-!
# Folding the lanes: tests

A table on `ℓ + κ = 2 + 2` coordinates and rate `2⁻¹` (`R = 1`): lanes are the low two
coordinates. The identities of `LeanerVM.Protocol.WhirFold` are checked on values, over `K` with
`K` challenges and over `E` with `E` challenges on the `K`-valued table lifted (level 0 of the
protocol: a `K` word folded at `E` points), and each is paired with the wrong reading it rules
out: folding the high coordinates, evaluating the stack at the unrotated point, reading a
position's symbol without the folded lanes.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Parameters LeanerVM.Protocol CompPoly CMlPolynomialEval

public section

/-! ## A table and two points -/

/-- A `K`-valued table on four coordinates. -/
def toyTable : CMlPolynomialEval K (2 + 2) :=
  Vector.ofFn fun i : Fin 16 ↦ K.ofBits (0x9e3779b97f4a7c15 * (i.val + 1) + 0x1234567)

/-- Fold challenges in `K`, round order. -/
def toyFold : Vector K 2 := #v[K.ofBits 0x3, K.ofBits 0x1d]

/-- An evaluation point of the folded table. -/
def toyPoint : Vector K 2 := #v[K.ofBits 0x5, K.ofBits 0x77]

/-- The encoder at `κ = 2`, `R = 1`, over `K`, at the position `y < 8`. -/
def encK (m : CMlPolynomialEval K 2) (y : ℕ) : K :=
  encode (RingHom.id K) 2 1 m ⟨y % 2 ^ (2 + 1), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The right side of `fact:fold-decode`: the lanes' encodings folded by `eq(r, .)`. -/
def foldedLanes (t : CMlPolynomialEval K (2 + 2)) (r : Vector K 2) (y : ℕ) : K :=
  ∑ u : Fin (2 ^ 2), (lagrangeBasis r)[u] * encK (sliceLow t u) y

/-! ## Agreement on values -/

/- `fact:fold-decode`: the fold of the encoded lanes is the encoding of the folded table, at
every position of the domain. -/
#guard (List.range 8).all fun y ↦
  encK (foldTable toyTable toyFold) y = foldedLanes toyTable toyFold y

/- The consistency claim: the column weight's pairing with the folded table is that fold. -/
#guard (List.range 8).all fun y ↦
  (columnWeight (RingHom.id K) 2 1 ⟨y % 8, by omega⟩).pair (RingHom.id K)
      (foldTable toyTable toyFold) = foldedLanes toyTable toyFold y

/- Binding the lanes then evaluating is evaluating with the bound coordinates first. -/
#guard evalMle (foldTable toyTable toyFold) toyPoint =
  evalMle toyTable ((toyFold ++ toyPoint : Vector K (2 + 2)))

/- The relayout is the exchange of the low and high blocks. -/
#guard (List.range 4).all fun u ↦ (List.range 4).all fun x ↦
  (relayout (κ := 2) (ℓ := 2) toyTable).toList.getD (u + 4 * x) 0 =
    toyTable.toList.getD (x + 4 * u) 0

/- The terminal point is rotated: the stack evaluated at `z ++ r` is the relayout at `r ++ z`. -/
#guard evalMle (relayout (κ := 2) (ℓ := 2) toyTable) ((toyFold ++ toyPoint : Vector K (2 + 2))) =
  evalMle toyTable ((toyPoint ++ toyFold : Vector K (2 + 2)))

/-! ## Nearby false statements -/

/-- Folding the high coordinates instead of the low ones: a different table, and the fold-decode
identity fails for it. -/
def foldHigh (t : CMlPolynomialEval K (2 + 2)) (r : Vector K 2) : CMlPolynomialEval K 2 :=
  Vector.ofFn fun x : Fin 4 ↦ evalMle (sliceLow t x) r

#guard ¬ (List.range 8).all fun y ↦
  encK (foldHigh toyTable toyFold) y = foldedLanes toyTable toyFold y

/- Evaluating the stack at the unrotated point is another value: the rotation is load-bearing. -/
#guard evalMle (relayout (κ := 2) (ℓ := 2) toyTable)
    ((toyFold ++ toyPoint : Vector K (2 + 2))) ≠
  evalMle toyTable ((toyFold ++ toyPoint : Vector K (2 + 2)))

/- The folded table differs from every single lane: the fold is not a lane selection. -/
#guard (List.range 4).all fun u ↦
  foldTable toyTable toyFold ≠ sliceLow toyTable (Fin.ofNat (2 ^ 2) u)

/- Folding at the other order of the challenges is another table: round `a` binds lane
coordinate `a`. -/
#guard foldTable toyTable toyFold ≠ foldTable toyTable #v[K.ofBits 0x1d, K.ofBits 0x3]

/-! ## The theorems, for a ring and a map of `K` -/

/-- Over `E`, with `E` challenges on the lifted `K` table: level 0 of the protocol. -/
example (t : CMlPolynomialEval E (2 + 2)) (r : Vector E 2) (y : Fin (2 ^ (2 + 3))) :
    encode (algebraMap K E) 2 3 (foldTable t r) y =
      ∑ u : Fin (2 ^ 2), (lagrangeBasis r)[u] * encode (algebraMap K E) 2 3 (sliceLow t u) y :=
  encode_foldTable (algebraMap K E) 3 t r y

end
end LeanerVMTests.Protocol
