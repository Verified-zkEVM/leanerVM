import LeanerVM.Protocol.LeanIsa
import LeanerVM.Protocol.ToCompPoly.WeightedCube
import LeanerVMTests.Protocol.Bus
import LeanerVMTests.Arithmetization.Statement

/-!
# Differential tests of the honest provers' compiled tables

The `@[csimp]` theorems of `LeanerVM.Protocol.ToCompPoly.Doubling`, `…MvEval`, `…Multilinear`,
`…BitProductTable`, `…WeightedCube` and `…Stacking`, of the stack's layouts (`Protocol.Stack`,
`Protocol.LeanIsa`), the rows and virtual tables of an instance (`Spine.Instance`,
`Spine.Seams`), the bus leaves (`Protocol.Bus`) and the grand-product prover
(`ToArkLib.GrandProduct`) are proved; these `#guard`s check the compiled code at small sizes.
The specification side of each guard is the definition's body written out, or the definition the
substitution replaces evaluated through others (`Gkr.roundPolyRaw`, `Bus.Source.leaf`,
`LeanIsa.cellOf`, themselves compiled through the substituted `evalMle`, `lagrangeBasis` and `E`
arithmetic). The independent anchors are CompPoly's own compiled `CMlPolynomialEval.eval` and
`CMvPolynomial.eval₂Horner`, which no `@[csimp]` theorem replaces. Two mutations show what the
doubling and the coefficient recurrence depend on.
-/

namespace LeanerVMTests.Protocol.FastProvers

open LeanerVM.Parameters LeanerVM.Protocol CompPoly CPoly CMlPolynomialEval

/-- A xorshift step. -/
private def xs (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A `K` word from a seed. -/
private def kOf (s : UInt64) : K := BF64.ofBitVec (xs s).toBitVec

/-- An `E` element from a seed. -/
private def eOf (s : UInt64) : E := E.ofLimbs (kOf s) (kOf (s + 1)) (kOf (s + 2))

/-- A point of `E` from a seed. -/
private def pt (n : ℕ) (seed : UInt64) : Vector E n :=
  Vector.ofFn fun i ↦ eOf (seed + 3 * i.val.toUInt64)

/-- A table over `E` from a seed. -/
private def tabE (n : ℕ) (seed : UInt64) : CMlPolynomialEval E n :=
  Vector.ofFn fun i ↦ eOf (seed + 5 * i.val.toUInt64)

/-- A table over `K` from a seed, every third entry zero. -/
private def tabK (n : ℕ) (seed : UInt64) : CMlPolynomialEval K n :=
  Vector.ofFn fun i ↦ if i.val % 3 = 0 then 0 else kOf (seed + i.val.toUInt64)

/-! ## Tables that factor over the bits, and the extension -/

/-- CompPoly's Lagrange basis, written out. -/
private def lagrangeSpec {n : ℕ} (w : Vector E n) : Vector E (2 ^ n) :=
  Vector.ofFn fun i ↦ ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j]

#guard (List.range 6).all fun n ↦ lagrangeBasis (pt n 3) == lagrangeSpec (pt n 3)
#guard lagrangeBasis (pt 0 3) == #v[1]

/-- Factors of a table that factors over the bits. -/
private def factors (n : ℕ) (seed : UInt64) (k : Fin n) (b : Bool) : E :=
  eOf (seed + 2 * k.val.toUInt64 + if b then 1 else 0)

#guard (List.range 5).all fun n ↦ bitProductTable (factors n 7) ==
  Vector.ofFn fun i ↦ ∏ k : Fin n, factors n 7 k (i.val.testBit k)

#guard (List.range 5).all fun n ↦ (List.finRange (2 ^ n)).all fun x ↦
  cubeWeight (fun a : Fin n ↦ (eOf a.val.toUInt64, eOf (a.val.toUInt64 + 9))) x ==
    ∏ a : Fin n, bitWeight (eOf a.val.toUInt64, eOf (a.val.toUInt64 + 9)) (x.val.testBit a)

-- The decoder on the cube, and off it: a coordinate that is not `1` reads as `0`.
#guard (List.range 6).all fun m ↦ (List.finRange (2 ^ m)).all fun x ↦
  boolIndex (boolVec x : Vector E m) == x
#guard (List.range 5).all fun m ↦
  let p : Vector E m := Vector.ofFn fun i ↦ if i.val % 2 = 0 then 1 else eOf i.val.toUInt64
  (boolIndex p).val == ∑ i : Fin m, if p[i] = 1 then 2 ^ i.val else 0

-- The extension against CompPoly's dot product with the Lagrange basis.
#guard (List.range 6).all fun n ↦
  evalMle (tabE n 11) (pt n 13) == CMlPolynomialEval.eval (tabE n 11) (pt n 13)
#guard (List.range 6).all fun n ↦ eval₂Mle (tabK n 17) (algebraMap K E) (pt n 19) ==
  CMlPolynomialEval.eval (CMlPolynomialEval.map (algebraMap K E) (tabK n 17)) (pt n 19)

/-! ## The stack -/

/-- Four blocks of heights `4, 2, 2, 1`. -/
private def B : Blocks := ⟨4, ![2, 1, 1, 0], by unfold Antitone; decide⟩

/-- Tables of the blocks. -/
private def T : B.Tables K := fun b ↦ tabK (B.size b) (100 * b.val.toUInt64)

-- The offsets by recursion against the sum.
#guard (List.range 6).all fun k ↦
  B.offsetNat k == ∑ c ∈ Finset.range k, if h : c < B.n then 2 ^ B.size ⟨c, h⟩ else 0

/-- `stackAt`, written out. -/
private def stackSpec (μ : ℕ) (pad : K) : CMlPolynomialEval K μ :=
  Vector.ofFn fun x ↦
    if B.total ≤ x.val then pad
    else ∑ b : Fin B.n, if B.InWindow b x.val then ((T b)[x.val - B.offset b]?).getD 0 else 0

-- Truncated, exact and padded.
#guard (List.range 6).all fun μ ↦ B.stackAt T μ 1 == stackSpec μ 1

private theorem B_fits : B.total ≤ 2 ^ 4 := by
  simp [B, Blocks.total, Blocks.offsetNat, Finset.sum_range_succ]

-- The lifts through offsets computed once, against `extendPoint`.
#guard (List.finRange B.n).all fun b ↦ (List.finRange (2 ^ B.size b)).all fun x ↦
  (B.layout B_fits).extend b (boolVec x) == B.extendPoint B_fits b (boolVec x)
#guard (List.finRange (2 ^ 1)).all fun c ↦ (List.finRange (2 ^ 1)).all fun x ↦
  (B.stridedLayout B_fits ⟨0, by decide⟩ 1 (κ := fun _ : Fin (2 ^ 1) ↦ 1) (fun c ↦ c)
      fun _ ↦ rfl).extend c (boolVec x) ==
    B.extendPoint B_fits ⟨0, by decide⟩
      (Vector.cast (by rfl) ((boolVec c : Vector E 1) ++ (boolVec x : Vector E 1)))

/-! ## Rows, virtual tables and the bus leaves -/

open LeanerVMTests.Protocol.Bus in
/-- A stack of the bus tests' instance that is not honest. -/
private def wild : Column 2 := ⟨tabK 2 23⟩

open LeanerVMTests.Protocol.Bus in
#guard [honest, wild].all fun q ↦ (List.finRange busToy.ntab).all fun j ↦
  (List.finRange (2 ^ busToy.τ j)).all fun x ↦ (List.finRange (busToy.width j)).all fun i ↦
    busToy.row q j x i == (busToy.column q ⟨j, i⟩).values.get x

-- The cube points and indices over `E` through the constants `oneE`, `zeroE`.
#guard (List.range 6).all fun m ↦ (List.finRange (2 ^ m)).all fun x ↦
  boolVecE x == (boolVec x : Vector E m) && boolIndexE (boolVecE x) == x
#guard (List.range 5).all fun m ↦
  let p : Vector E m := Vector.ofFn fun i ↦ if i.val % 2 = 0 then 1 else eOf i.val.toUInt64
  boolIndexE p == boolIndex p
#guard ([1, 0, y, y + 1, ofK 1, ofK 2] : List E).all fun x ↦ isOneE x == decide (x = 1)

open LeanerVMTests.Protocol.Bus in
-- A column read off the stack, against `readWith` written out over the generic `boolIndex`.
#guard [honest, wild].all fun q ↦ (List.finRange busToy.ntab).all fun j ↦
  (List.finRange (busToy.width j)).all fun i ↦
    (busToy.column q ⟨j, i⟩).values == Vector.ofFn fun x ↦
      q.values.get (boolIndex (busToy.layout.extend ⟨j, i⟩ (boolVec x)))

open LeanerVMTests.Protocol.Bus in
-- The virtual table of the constraint and of the flush's coordinates, against CompPoly's Horner
-- evaluator.
#guard [honest, wild].all fun q ↦ (constraint :: flush.2.toList).all fun P ↦
  busToy.virtualTable q 0 P == Vector.ofFn fun x ↦ ofK (CMvPolynomial.eval₂Horner (RingHom.id K)
    (fun i ↦ (busToy.column q ⟨0, i⟩).values.get x) P)

#guard (List.range 8).all fun s ↦
  let t : Vector K 16 :=
    Vector.ofFn fun i ↦ if i.val % (s + 2) = 0 then 0 else kOf (s + i.val).toUInt64
  let α : Fin 4 → E := fun i ↦ eOf (s.toUInt64 + i.val.toUInt64)
  fingerprintWith (fingerprintWeights α) t == fingerprint α t

open LeanerVMTests.Protocol.Bus in
-- The leaf stacks against the blocks' leaves, read row by row.
#guard [honest, wild].all fun q ↦ (List.finRange 3).all fun k ↦
  Bus.sideLeaves busToy k α β q ==
    (Bus.blocks busToy k).stackAt (fun b ↦ Vector.ofFn ((Bus.sorted busToy k)[b].leaf α β q))
      busToy.μBus 1

/-! ## The grand-product prover -/

/-- Three random trees of `2 ^ μ` leaves. -/
private def gkrLeaves (μ : ℕ) : Unit → (∀ i, NoOracle i) → Fin 3 → CMlPolynomialEval E μ :=
  fun _ _ s ↦ tabE μ (31 * s.val.toUInt64)

/-- A context of a step from layer `m`. -/
private def gkrCtx (m : ℕ) : Gkr.LayerCtx Unit E NoOracle 3 m :=
  (((((), (pt m 41, fun _ ↦ 0)), eOf 43), fun i ↦ i.elim0), ())

/-- The honest message, by `roundPolyRaw`, which no `@[csimp]` theorem replaces. -/
private def roundSpec (μ ρ m j : ℕ) (cv : Vector E j) : SumcheckRound.Message E (2 ^ ρ) :=
  if h : j < m then
    SumcheckRound.ofCPolynomial _ (Gkr.roundPolyRaw 3 μ (gkrLeaves μ) ρ m (gkrCtx m) h cv)
  else SumcheckRound.ofCPolynomial _ 0

-- Every round of a radix-four step at layers `0, 1, 2` and of a binary step at layers `0, 3`,
-- and one round past the last.
#guard [(4, 2, 2), (3, 2, 1), (2, 2, 0), (4, 1, 3), (1, 1, 0)].all fun (μ, ρ, m) ↦
  (List.range (m + 1)).all fun j ↦
    Gkr.roundPoly 3 μ (gkrLeaves μ) ρ m (gkrCtx m) j (pt j 47) == roundSpec μ ρ m j (pt j 47)

-- The descendants' values against the level below at the descendants.
#guard [(4, 2, 2), (4, 1, 3), (2, 2, 0)].all fun (μ, ρ, m) ↦ (List.finRange 3).all fun s ↦
  Gkr.children 3 μ (gkrLeaves μ) ρ m () (fun i ↦ i.elim0) (pt m 53) s ==
    Vector.ofFn fun b ↦
      CMlPolynomialEval.eval (layerTable (gkrLeaves μ () (fun i ↦ i.elim0) s) (m + ρ))
      (childPoint ρ b (pt m 53))

/-! ## The leanISA stack -/

open LeanerVM.Protocol.LeanIsa LeanerVMTests.Arithmetization.Statement in
/-- The hand-built witness's sizes with a memory of `2 ^ 4` words. -/
private def smallSizes : LeanIsa.Sizes :=
  match Sizes.ofWitness (fillW 1 g memCnt) with
  | some s => { s with logMem := 4, logMem_pos := by decide }
  | none => ⟨4, by decide, fun _ ↦ 0⟩

section LeanIsa

open LeanerVM.Arithmetization LeanerVM.Protocol.LeanIsa LeanerVMTests.Arithmetization.Statement

/-- The witness. -/
private abbrev W := fillW 1 g memCnt

/-- The BLAKE2s inhabitant. -/
private abbrev F₀ : FlockSpec := Blake2sFlock.blake2sFlockSpec

-- The columns, read off the witness's rows as arrays, against `cellOf` on the list of rows.
#guard (List.finRange 6).all fun j ↦ (List.finRange (width (opIdx j))).all fun i ↦
  witnessColumn F₀ fillProg smallSizes W ⟨opIdx j, i⟩ ==
    Vector.ofFn (n := 2 ^ kappa fillProg smallSizes ⟨opIdx j, i⟩) fun x ↦
      cellOf (tableAt W ⟨j, by omega⟩) x i
#guard (List.finRange 4).all fun i ↦
  witnessColumn F₀ fillProg smallSizes W (memCol i) ==
    Vector.ofFn (n := 2 ^ kappa fillProg smallSizes (memCol i)) fun x ↦
      cellOf (tableAt W 6) x (memRowCell i)
#guard witnessColumn F₀ fillProg smallSizes W bfcntCol ==
  Vector.ofFn (n := 2 ^ kappa fillProg smallSizes bfcntCol) fun x ↦ cellOf (tableAt W 7) x 1

#guard (blake2sLimbs fillProg smallSizes W).toList.zipIdx.all fun (row, x) ↦
  (List.finRange 18).all fun k ↦ row k == cellOf (tableAt W 5) x (9 + k)

-- The layout's lifts, the stacking order computed once, against `route`'s.
#guard columns.all fun c ↦
  (layout fillProg smallSizes F₀.slot).extend c (boolVec ⟨0, Nat.two_pow_pos _⟩) ==
    ((((blocks fillProg smallSizes).layout (blocks_fits fillProg smallSizes)).piecewise
      ((blocks fillProg smallSizes).stridedLayout (blocks_fits fillProg smallSizes)
        (flockBlock fillProg smallSizes) 8 F₀.slot (κ := fun _ ↦ smallSizes.τ 5)
          fun _ ↦ size_flockBlock fillProg smallSizes)).comap (route fillProg smallSizes)
      (route_kappa fillProg smallSizes)).extend c (boolVec ⟨0, Nat.two_pow_pos _⟩)

end LeanIsa

/-! ## Mutations -/

/-- The Lagrange basis doubled with the halves swapped: the new coordinate's `0` half above. -/
private def lagrangeSwapped {n : ℕ} (w : Vector E n) : (k : ℕ) → k ≤ n → Array E
  | 0, _ => #[1]
  | k + 1, h =>
    let a := lagrangeSwapped w k (Nat.le_of_succ_le h)
    let hi := a.map (· * w[k])
    hi ++ Array.zipWith (· - ·) a hi

#guard (lagrangeSwapped (pt 2 3) 2 le_rfl).toList != (lagrangeBasis (pt 2 3)).toList

-- Without the shift by `X`, the coefficients are of `p·a + p·(b - a)`, not of `p·(a + X·(b - a))`.
#guard (Gkr.mulAffine (d := 2) #v[eOf 1, eOf 2, 0] (eOf 3) (eOf 4)).toList !=
  [eOf 3 * eOf 1 + (eOf 4 - eOf 3) * eOf 1, eOf 3 * eOf 2 + (eOf 4 - eOf 3) * eOf 2, 0]

end LeanerVMTests.Protocol.FastProvers
