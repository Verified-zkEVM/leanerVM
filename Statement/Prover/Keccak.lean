module

public import Statement.Prover.KeccakLayer

/-!
# The Keccak prover

The honest prover of `verifyKeccak` (`verifier.py:1373-1406`) and of the Keccak phase of
`verify_execution` (`keccakPhase`), each table computed once:

* the column's slots at the steps' point `inst`, `Σ_x eq(inst, x)·col(x + 2^h·o)` for the `64`
  slots (`slotWords`), give `committed` (the middle state's lanes, slots `25 .. 49`) and the
  output opening's word;
* the twelve layers (`layersProve`, `KeccakLayer.lean`);
* the openings' sumchecks (`openRound`, `openFold`): sums over the remaining cube of products
  of two folded tables, `Σ_u A(u)·B(u)`, or of several, scaled: the outputs' slot rounds on the
  slot weights and the slot words, the inputs' instance rounds on the instance weights and the
  claim restricted to each instance (`phiTable`), then the slot rounds on the `64` slices' slot
  weights and the slices at `(λ, r_pack)` (`sliceTable`).
-/

@[expose] public section

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier

/-! ## Sums of products over the cube -/

/-- The coefficients of `x ↦ Σ_u A(x, u)·B(x, u)`, both tables affine in the next coordinate. -/
def prodCoeffs (a b : Array E) : List E :=
  sumCoeffs 3 (a.size / 2) fun u ↦
    let al := a.getD (2 * u) 0
    let ad := al + a.getD (2 * u + 1) 0
    let bl := b.getD (2 * u) 0
    let bd := bl + b.getD (2 * u + 1) 0
    [al * bl, al * bd + ad * bl, ad * bd]

/-- An opening's state: a scale and pairs of tables, the sum `scale · Σ_pairs Σ_u A(u)·B(u)`. -/
structure OpenState where
  scale : E
  pairs : List (Array E × Array E)

/-- An opening round's polynomial. -/
def openRound (st : OpenState) : List E :=
  scaleCoeffs st.scale <|
    st.pairs.foldl (fun acc p ↦ addCoeffs acc (prodCoeffs p.1 p.2)) (List.replicate 3 0)

/-- An opening round's fold. -/
def openFold (st : OpenState) (c : E) : OpenState :=
  ⟨st.scale, st.pairs.map fun p ↦ (foldTab c p.1, foldTab c p.2)⟩

/-! ## The column at a point -/

/-- The column's `64` slots at the steps' point `inst`: `Σ_x eq(inst, x)·col(x + 2^h·o)`. -/
def slotWords (col : ℕ → K) (h : ℕ) (inst : List E) : Array E :=
  let eq := eqTable inst
  Array.ofFn (n := 64) fun o ↦ sumRange (2 ^ h) fun x ↦ eq.getD x 0 * ofK (col (x + 2 ^ h * o.val))

/-- The first claim's position weights: `eq(r_lane, ℓ)·x^z` (`verifier.py:1382`). -/
def firstWeightsOf (lanesPt : List E) : List E :=
  let e := eqKernel lanesPt
  (List.range keccakBits).map fun j ↦ e.getD (j / 64) 0 * eOfNat (2 ^ (j % 64))

/-- The first claim (`verifier.py:1383-1385`). -/
def firstClaimOf (inst segment lanesPt output : List E) (committed : E) : KeccakClaim :=
  ⟨committed + (eqKernel segment).getD (keccakSegments - 1) 0 *
      dot ((eqKernel lanesPt).take 25) output,
    eqKernel (inst.take 4), inst.drop 4 ++ segment, firstWeightsOf lanesPt⟩

/-- The weight `_keccak_slot_weights` puts at slot `o`, slice `z`. -/
def slotWeightOf (segments : List E) (w : Array E) (first count o z : ℕ) : E :=
  if 25 * first ≤ o ∧ o < 25 * (first + count) ∧ z < 64 then
    segments.getD (o / 25 - first) 0 * w.getD (64 * (o % 25) + z) 0 else 0

/-! ## The inputs' opening -/

/-- The claim at depth `12` restricted to each instance `i < 16`:
`Σ_z eq(point, z) Σ_j w_j·[bit j of instance i's committed input]`, the words read by byte
tables of the weights. -/
def phiTable (col : ℕ → K) (P : ℕ) (claim : KeccakClaim) : Array E :=
  let eq := eqTable claim.point
  let w := claim.weights.toArray
  let tabs : Array (Array (Array E)) :=
    Array.ofFn (n := 25) fun l ↦ laneTabs (fun j ↦ w.getD j 0) l.val
  Array.ofFn (n := 16) fun i ↦ sumRange (2 ^ (P + 1)) fun z ↦
    eq.getD z 0 * sumRange 25 fun l ↦ wordDot (tabs.getD l #[])
      (col (i.val + 16 * (z % 2 ^ P) + 2 ^ (P + 4) * (25 * (z / 2 ^ P) + l))).toBitVec.toNat

/-- The slices of the column's slots at the steps' point `a`: entry `(o, z)` is
`Σ_x eq(a, x)·[bit z of col(x + 2^h·o)]`. -/
def sliceTable (col : ℕ → K) (h : ℕ) (a : List E) : Array (Array E) :=
  let eq := eqTable a
  Array.ofFn (n := 64) fun o ↦ (List.range (2 ^ h)).foldl (fun acc x ↦
    addBits (eq.getD x 0) (col (x + 2 ^ h * o.val)).toBitVec.toNat 64 acc) (Array.replicate 64 0)

/-- **The inputs' opening**: the instance rounds, the slot rounds, the `64` slices. -/
def inputProve (col : ℕ → K) (P : ℕ) (claim : KeccakClaim) (outs : List ColumnClaim) :
    Script (List ColumnClaim × List E × List E) :=
  let mu : Array E := Array.ofFn (n := 16) fun i ↦ claim.mu.getD i.val 0
  (sumcheckBy openRound openFold (List.replicate 4 none) ⟨1, [(mu, phiTable col P claim)]⟩).bind
    fun y ↦
  let a := y.1 ++ claim.point.take P
  let sl := sliceTable col (P + 4) a
  let segs := eqKernel (claim.point.drop P)
  let w := claim.weights.toArray
  let pairs := (List.range 64).map fun z ↦
    (Array.ofFn (n := 64) fun o ↦ slotWeightOf segs w 0 keccakSegments o.val z,
      Array.ofFn (n := 64) fun o ↦ (sl.getD o.val #[]).getD z 0)
  let muLow := (y.2.pairs.headD (#[], #[])).1.getD 0 0
  (sumcheckBy openRound openFold (List.replicate 6 none) ⟨muLow, pairs⟩).bind fun x ↦
  let slices := x.2.pairs.map fun p ↦ p.2.getD 0 0
  (Script.sendList slices).bind fun _ ↦
  Script.ret (outs, a ++ x.1, slices)

/-! ## The reduction -/

/-- **The honest prover of `verifyKeccak`** on the column `col` (`2^(P + 4)` steps), the output
lanes' claims `output` at `inst`. -/
def keccakProve (col : ℕ → K) (P : ℕ) (inst output : List E) :
    Script (List ColumnClaim × List E × List E) :=
  let V := slotWords col (P + 4) inst
  (Script.sampleN 1).bind fun segment ↦
  (Script.sampleN 5).bind fun lanesPt ↦
  let eS := eqKernel segment
  let eL := eqKernel lanesPt
  let committed := eS.getD 0 0 * sumRange 25 fun l ↦ eL.getD l 0 * V.getD (25 + l) 0
  (Script.sendE committed).bind fun _ ↦
  (layersProve col P (List.range' 0 12)
      (firstClaimOf inst segment lanesPt output committed)).bind fun claim ↦
  let wo : Array E := Array.ofFn (n := 64) fun o ↦
    if 25 ≤ o.val ∧ o.val < 50 then eS.getD 0 0 * eL.getD (o.val - 25) 0 else 0
  (sumcheckBy openRound openFold (List.replicate 6 none) ⟨1, [(wo, V)]⟩).bind fun x ↦
  let word := (x.2.pairs.headD (#[], #[])).2.getD 0 0
  (Script.sendE word).bind fun _ ↦
  inputProve col P claim [⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩]

/-- **The honest prover of the Keccak phase** (`keccakPhase`, `verifier.py:1503-1507`): the
output lanes' claims leave the batch and become the reduction's, on `q_keccak`'s words (the
column `qkeccak` of `cols`), the `KECCAK` table of log-height `τ`. -/
def keccakPhaseProve (τ : ℕ) (cols : Array (Array K)) (claims : List ColumnClaim) :
    Script (List ColumnClaim × List E × List E) :=
  let qk := cols.getD qkeccak #[]
  let lanes := claims.filter fun c ↦ c.column ∈ keccakOutputColumns
  (keccakProve (fun n ↦ qk.getD n 0) (τ - 4) (lanes.headD default).point
      (lanes.map (·.value))).bind fun r ↦
    Script.ret (claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) ++ r.1, r.2.1, r.2.2)

end LeanVM.Prover.KeccakGkr

end
