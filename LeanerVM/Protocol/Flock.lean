/-
  LeanerVM.Protocol.Flock

  The Flock phase of the leanVM protocol: the Flock argument at leanVM's sizes and constants, on
  the instance's Flock region, at the spine's slot, with its completeness and the bound on its
  error.
-/

module

public import LeanerVM.Parameters.Generator
public import LeanerVM.Protocol.Spine.Phase
public import LeanerVM.Protocol.Spine.Errors
public import LeanerVM.Protocol.ToArkLib.Flock.Reduction

/-!
# The Flock phase

The fourth phase after the commitment (Annex C and Annex A, at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`). The instance's Flock region is a column of
`2 ^ (8 + kBatch)` cells of `K`, each packing 64 bits of the BLAKE2s witness, and the phase
proves of it the predicate `FlockRegion.Holds`: every block of `2 ^ 14` bits satisfies the
region's R1CS and holds `1` at position `512`. It is the generic Flock argument
(`Flock.flock`) at `s = 6` skipped and packed coordinates, `m = 8` within-block coordinates,
`κ = kBatch` batch coordinates, the skip nodes `φ_8(0), …, φ_8(127)`, the seven fixed
coordinates of `LeanerVM.Parameters.Flock`, and six ring-switching coefficients with shifts
`32, 16, 8, 4, 2, 1`. Its verifier reads no pooled claim: it hands the column claims on and adds
one weighted claim, `⟨W, q⟩ = T` with `T = Σ_{i < 64} x^i · Φ(s_i)` and `W` the combination of
the equality kernels at the Frobenius powers of the lincheck's point, lifted into the stack by
the instance's layout (`cpu/mod.rs:799-805`, `stack_open.rs:522-527`, `verifier.py:1304-1349`).
With no region, the phase hands the claims on.

* `flockPhase`: the phase, a `Phase.FrontDef` at the slot `flockSpec`.
* `flockComplete`: its completeness from `Seam.pub` to `Seam.flock`.
* `flockError_le`: the slot's error is at most `(4·kBatch + 163) / |E| + 2^32 / |E|`.

The phase rests on two facts about leanVM's constants and fields: the 128 skip nodes are
distinct (`flockNodes_injective`, from the `F_2`-linearity of `φ_8` and a kernel check of its
127 nonzero images), and a cell of `K` is its bits packed by the powers of `x`
(`ofK_eq_sum_cellBit`, through CompPoly's bridge to `GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec

@[expose] public section

/-! ## Packing bits into `K` -/

/-- A cell of `K` is its bits packed by the powers of `x`: `a = Σ_{i < 64} a_i · x^i`. -/
theorem K.eq_sum_bits (a : K) :
    a = ∑ i : Fin 64, if a.toBitVec.getLsbD i then g ^ (i : ℕ) else 0 := by
  apply BF64.toQuot_injective
  have hg : BF64.toQuot g = AdjoinRoot.root BF64.basePoly := by
    rw [BF64.toQuot, BF64.toPolyBF64, g, K.ofBits, BF64.toBitVec_ofBitVec,
      show BitVec.ofNat 64 2 = (1 <<< 1 : BitVec 64) by decide,
      BinaryField.toPoly_one_shiftLeft 1 (by norm_num), pow_one, AdjoinRoot.mk_X]
  have hsum : ∀ (s : Finset (Fin 64)) (f : Fin 64 → K),
      BF64.toQuot (∑ i ∈ s, f i) = ∑ i ∈ s, BF64.toQuot (f i) := fun s f ↦ by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, BF64.toQuot_add, ih]
  rw [hsum]
  conv_lhs => rw [BF64.toQuot, BF64.toPolyBF64, BinaryField.toPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [BitVec.getLsb, BitVec.getLsbD]
  split
  · rw [map_pow, AdjoinRoot.mk_X, BF64.toQuot_npow, hg]
  · rw [map_zero, BF64.toQuot_zero]

/-- The embedding of a cell in `E` is its bits packed by the powers of `x`. -/
theorem ofK_eq_sum_cellBit (a : K) :
    ofK a = ∑ i : Fin (2 ^ Flock.kSkip), ofK (g ^ i.val) * cellBit a i := by
  conv_lhs => rw [K.eq_sum_bits a]
  change algebraMap K E _ = _
  rw [map_sum (algebraMap K E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [cellBit]
  split <;> simp_all

/-- Entry `u` of the table of bit `i` is bit `i` of cell `u`. -/
theorem bitTable_getElem {n : ℕ} (c : Column n) (i : Fin (2 ^ Flock.kSkip)) (u : Fin (2 ^ n)) :
    (bitTable c i)[u] = cellBit c.values[u] i := by
  simp [bitTable, Vector.get_eq_getElem]

/-- A column of `K` is its bit tables packed by the powers of `x`, entry by entry. -/
theorem ofK_eq_sum_bitTable {n : ℕ} (c : Column n) (u : Fin (2 ^ n)) :
    ofK c.values[u] = ∑ i : Fin (2 ^ Flock.kSkip), ofK (g ^ i.val) * (bitTable c i)[u] := by
  simp only [bitTable_getElem]
  exact ofK_eq_sum_cellBit _

/-- The bits of a cell are `0` or `1`. -/
theorem cellBit_isBool (a : K) (i : ℕ) : cellBit a i = 0 ∨ cellBit a i = 1 := by
  unfold cellBit
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The bit tables hold `0`s and `1`s. -/
theorem bitTable_isBool {n : ℕ} (c : Column n) (i : Fin (2 ^ Flock.kSkip)) (u : Fin (2 ^ n)) :
    (bitTable c i)[u] = 0 ∨ (bitTable c i)[u] = 1 := by
  rw [bitTable_getElem]
  exact cellBit_isBool _ _

/-! ## The skip nodes -/

/-- `φ_8` is additive in its byte: it sums the basis images of the set bits. -/
theorem phi8_xor (a b : ℕ) : Flock.phi8 (a ^^^ b) = Flock.phi8 a + Flock.phi8 b := by
  simp only [Flock.phi8, ← Finset.sum_add_distrib, Nat.testBit_xor]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases a.testBit i <;> cases b.testBit i <;> simp [← two_mul, CharTwo.two_eq_zero]

/-- The nonzero bytes below `128` have nonzero images: a kernel check. -/
theorem phi8_ne_zero : ∀ b : Fin 128, b ≠ 0 → Flock.phi8 b ≠ 0 := by decide +kernel

/-- `φ_8` is injective on the bytes below `128`. -/
theorem phi8_injOn {a b : ℕ} (ha : a < 128) (hb : b < 128) (h : Flock.phi8 a = Flock.phi8 b) :
    a = b := by
  have hx : a ^^^ b < 128 := Nat.xor_lt_two_pow (n := 7) ha hb
  by_contra hne
  have hz : Flock.phi8 (a ^^^ b) = 0 := by
    rw [phi8_xor, h, CharTwo.add_self_eq_zero]
  refine phi8_ne_zero ⟨a ^^^ b, hx⟩ (fun h0 ↦ hne ?_) hz
  have h0' : a ^^^ b = 0 := congrArg Fin.val h0
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  have := congrArg (·.testBit i) h0'
  simpa [Nat.testBit_xor] using this

/-- The skip nodes `φ_8(0), …, φ_8(127)`: the skip domain, then its coset. -/
def flockNodes : Vector E (2 ^ Flock.kSkip + 2 ^ Flock.kSkip) :=
  Vector.ofFn fun i ↦ Flock.skipNode ⟨i.val, i.isLt⟩

/-- The skip nodes are distinct. -/
theorem flockNodes_injective :
    Function.Injective fun j : Fin (2 ^ Flock.kSkip + 2 ^ Flock.kSkip) ↦ flockNodes[j] := by
  intro a b h
  simp only [flockNodes, Fin.getElem_fin, Vector.getElem_ofFn, Flock.skipNode] at h
  exact Fin.ext (phi8_injOn a.isLt b.isLt (ofK_injective h))

/-! ## The argument at leanVM's sizes -/

/-- The skip domain: the nodes with their inverse Lagrange denominators, computed once. -/
def flockSkipDomain : Flock.SkipDomain E Flock.kSkip := Flock.SkipDomain.ofPts flockNodes

/-- leanVM's Flock parameters for `2 ^ k` compressions. -/
def flockParams (k : ℕ) : Flock.Params E where
  s := Flock.kSkip
  m := Flock.kIn
  κ := k
  nodes := flockSkipDomain
  nFix := 7
  nRand := k + 1
  fixed := Flock.fixedPoint
  hpoint := by simp only [Flock.kIn]; omega
  cpos := Flock.constPos

namespace FlockPhase

variable {I : M3Instance} (r : FlockRegion I.toShape)

/-- The region's 64 Boolean tables, read off the stack. -/
def bits (o : ∀ i, TheOracle I i) : Fin (2 ^ Flock.kSkip) → CMlPolynomialEval E (8 + r.kBatch) :=
  bitTable (I.flockColumn r (theStack o))

/-- The pooled column claims hold of the stack: what the phase carries along. -/
def side (s : I.Stmt × PubOut I) (o : ∀ i, TheOracle I i) : Prop :=
  ∀ c ∈ s.2.columns.toList, c.Holds (theStack o)

/-- A point of the region, lifted to the stack by the instance's layout. -/
def lift (p : Vector E (8 + r.kBatch)) : Vector E I.μ :=
  I.layout.extend r.col (Vector.cast r.height.symm p)

theorem flockClaims_eq_one (h : I.flock = some r) : I.flockClaims = 1 := by
  simp [M3Instance.flockClaims, h]

/-- The phase's output: the column claims, and the switched weighted claim. -/
def finish (h : I.flock = some r) (s : I.Stmt × PubOut I) (W : Weight E I.μ) (T : E) :
    I.Stmt × FlockOut I :=
  (s.1, ⟨s.2.columns, Vector.cast (flockClaims_eq_one r h).symm #v[⟨W, T⟩]⟩)

/-- The region's column of the stack is read through the lift. -/
theorem eval₂Mle_flockColumn (q : Column I.μ) (p : Vector E (8 + r.kBatch)) :
    eval₂Mle (I.flockColumn r q).values (algebraMap K E) p =
      eval₂Mle q.values (algebraMap K E) (lift r p) := by
  have h := eval₂Mle_cast (algebraMap K E) r.height (I.column q r.col).values
    (Vector.cast r.height.symm p)
  simp only [Vector.cast_cast, Vector.cast_rfl] at h
  rw [M3Instance.flockColumn, h, M3Instance.column, Layout.read_eval]
  rfl

end FlockPhase

variable (I : M3Instance)

/-- The Flock phase on a region. -/
def flockPhaseSome (r : FlockRegion I.toShape) (h : I.flock = some r) :
    Phase.FrontDef I (I.Stmt × PubOut I) (I.Stmt × FlockOut I) (flockSpecOf r.kBatch) where
  toDef := Flock.flock (flockParams r.kBatch) r.r1cs (FlockPhase.bits r) FlockPhase.side 5
    (algebraMap K E) g (FlockPhase.lift r) (FlockPhase.finish r h)
  front := Flock.flockFront (flockParams r.kBatch) r.r1cs (FlockPhase.bits r) FlockPhase.side 5
    (algebraMap K E) g (FlockPhase.lift r) (FlockPhase.finish r h)

/-- The Flock phase on the slot of a region or of none: with no region it hands the claims on. -/
def flockPhaseOpt : (o : Option (FlockRegion I.toShape)) → I.flock = o →
    Phase.FrontDef I (I.Stmt × PubOut I) (I.Stmt × FlockOut I) (flockSpecOpt I o)
  | none, h => ⟨Phase.passThrough I fun s ↦
      (s.1, ⟨s.2.columns, Vector.cast (by simp [M3Instance.flockClaims, h]) #v[]⟩),
    Component.passThroughFront _ _⟩
  | some r, h => flockPhaseSome I r h

/-- **The Flock phase** (Annex C, Annex A): at the slot `flockSpec`, a front phase. -/
def flockPhase : Phase.FrontDef I (I.Stmt × PubOut I) (I.Stmt × FlockOut I) (flockSpec I) :=
  flockPhaseOpt I I.flock rfl

/-- Completeness of the Flock phase on a slot. -/
def flockCompleteOpt : (o : Option (FlockRegion I.toShape)) → (h : I.flock = o) →
    Phase.Complete I (flockPhaseOpt I o h).toDef (Seam.pub I) (Seam.flock I)
  | none, h => Phase.passThroughComplete I _ fun s o hin ↦ ⟨hin.1, by simp⟩
  | some r, h =>
    Flock.flockComplete (flockParams r.kBatch) r.r1cs (FlockPhase.bits r) FlockPhase.side 5
      (algebraMap K E) g (FlockPhase.lift r) (FlockPhase.finish r h)
      (fun o ↦ (I.flockColumn r (theStack o)).values) (fun o ↦ (theStack o).values)
      flockNodes_injective (Seam.pub I) (Seam.flock I)
      (fun s o _ hin ↦ ⟨hin.1, hin.2 r (by rw [h]; rfl)⟩)
      (fun s o _ W T hside hpair ↦ ⟨hside, by
        simp only [FlockPhase.finish, Vector.toList_cast]
        intro c hc
        simp only [Vector.toList_mk, List.mem_singleton] at hc
        subst hc
        exact hpair⟩)
      (fun o u ↦ ofK_eq_sum_bitTable (I.flockColumn r (theStack o)) u)
      (fun o i u ↦ bitTable_isBool (I.flockColumn r (theStack o)) i u)
      (fun o p ↦ FlockPhase.eval₂Mle_flockColumn r (theStack o) p)

/-- **Completeness of the Flock phase**: from the public-input seam to the Flock seam, the honest
prover is accepted with probability one. -/
def flockComplete : Phase.Complete I (flockPhase I).toDef (Seam.pub I) (Seam.flock I) :=
  flockCompleteOpt I I.flock rfl

/-- **The Flock slot's error.** With a region of `2 ^ k` compressions, the errors of the slot sum
to at most `(4k + 163) / |E| + 2^32 / |E|`: the zerocheck and lincheck's `(4k + 163) / |E|`
(Annex C, §C.5) and ring switching's below `2^32 / |E|` (Annex A, §A.4). -/
theorem flockError_le {r : FlockRegion I.toShape} (h : I.flock = some r) :
    ∑ i, flockError I i ≤ overE (4 * r.kBatch + 163) + overE (2 ^ 32) := by
  have key : ∀ o (_ : o = some r), ∑ i, flockErrorOpt I o i ≤
      overE (4 * r.kBatch + 163) + overE (2 ^ 32) := by
    rintro o rfl
    refine (sum_flockErrorOf r.kBatch).trans_le ?_
    rw [← overE_add]
    exact overE_mono (by omega)
  exact key _ h

end
end LeanerVM.Protocol
