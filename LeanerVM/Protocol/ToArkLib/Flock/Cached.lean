/-
  LeanerVM.Protocol.ToArkLib.Flock.Cached

  The Flock argument's honest prover with its tables carried from round to round: the witness
  tables and the products walked once per block, the skip tables built once at `z_skip`, the
  lincheck's tables once at `α`, as a cached prover proved to run as the honest one. Candidate
  for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Flock.Reduction
public import LeanerVM.Protocol.ToArkLib.CachedRounds
public import LeanerVM.Protocol.ToCompPoly.FinLoop

/-!
# The Flock argument with its tables cached

The honest prover of `Flock.flock` computes every message from the oracles and the challenges:
`leftTable` walks a whole block for each entry it reads, the skip tables `â(Y, ·)` read every
product table at every entry, and every round of the two sumchecks rebuilds them, as the lincheck
rebuilds its column weights (a backward walk) and the folded witness. `flockCached` is a cached
prover of it (`Component.Cached`), whose cache holds, in turn:

* the witness tables and the left and right products, every block walked once (`walkedTables`,
  `walkedTables_eq`), read off the oracles once at the skip message;
* after `z_skip`, the three skip tables at it (`skipTableOf`), through the zerocheck's rounds
  (`zcCache`) and its terminal message;
* after `α`, the lincheck's column weights, one backward walk (`mTableOf`), and the folded
  witness (`zTableOf`), through its rounds (`linCache`) and the slices;
* the switched weight with its values combined on the terms' supports (`ringWeightFast`, by
  `eqBatch`), its equality kernels vanishing off the region's block.

The sums over the skip nodes and the batch read tables of `0`s and `1`s in the honest run, so they
add the weights of the entries `1` and skip the entries `0` (`dotSparse`, `dotSparse_eq`). The skip
message combines every table at each of `2 ^ s` coset nodes; on tables of `0`s and `1`s it reads
each entry's bits a byte of tables at a time and adds the weights' subset sums at those bytes
(`combBytes`, `combBytes_eq`), `2 ^ s / 8` additions an entry in place of `2 ^ s`. Every
message read off the cache is the honest one, so the cached prover runs as `flock`'s honest
prover (`Component.Cached.run_eq`). Nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

namespace Flock

open CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec SumcheckRound BlockR1CS

@[expose] public section

section Bytes

/-! ## Combinations of `0`/`1` tables a byte at a time -/

/-- `Σ_{i < k} 2^i · f i`: the number whose bit `i < k` is `f i`. -/
def bitsNat (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * bitsNat (fun i ↦ f (i + 1)) k + if f 0 then 1 else 0

private theorem testBit_bitsNat : ∀ (f : ℕ → Bool) (k i : ℕ),
    (bitsNat f k).testBit i = (decide (i < k) && f i)
  | f, 0, i => by simp [bitsNat]
  | f, k + 1, 0 => by
    rw [bitsNat, Nat.testBit_zero]
    cases f 0 <;> simp
  | f, k + 1, i + 1 => by
    rw [bitsNat, Nat.testBit_succ, show (2 * bitsNat (fun i ↦ f (i + 1)) k +
      (if f 0 then 1 else 0)) / 2 = bitsNat (fun i ↦ f (i + 1)) k by split <;> omega,
      testBit_bitsNat]
    simp

private theorem bitsNat_lt : ∀ (f : ℕ → Bool) (k : ℕ), bitsNat f k < 2 ^ k
  | _, 0 => by simp [bitsNat]
  | f, k + 1 => by
    have := bitsNat_lt (fun i ↦ f (i + 1)) k
    rw [bitsNat, pow_succ]
    split <;> omega

variable {F : Type} [Field F]

/-- The subset sums of `w 0, …, w (k - 1)`: entry `β < 2 ^ k` is the sum of `w i` over the set
bits `i` of `β`. -/
def subsetSums (w : ℕ → F) : ℕ → Array F
  | 0 => #[0]
  | k + 1 =>
    let t := subsetSums (fun i ↦ w (i + 1)) k
    Array.ofFn fun β : Fin (2 * t.size) ↦
      let y := t.getD (β.val / 2) 0
      if β.val % 2 = 1 then y + w 0 else y

private theorem size_subsetSums : ∀ (w : ℕ → F) (k : ℕ), (subsetSums w k).size = 2 ^ k
  | _, 0 => rfl
  | w, k + 1 => by
    simp only [subsetSums, Array.size_ofFn, size_subsetSums _ k, pow_succ]
    ring

private theorem getD_subsetSums : ∀ (w : ℕ → F) (k β : ℕ), β < 2 ^ k →
    (subsetSums w k).getD β 0 = ∑ i ∈ Finset.range k, if β.testBit i then w i else 0
  | _, 0, β, hβ => by
    obtain rfl : β = 0 := by simpa using hβ
    simp [subsetSums]
  | w, k + 1, β, hβ => by
    have hβ' : β < 2 * (subsetSums (fun i ↦ w (i + 1)) k).size := by
      rw [size_subsetSums]; rw [pow_succ] at hβ; omega
    simp only [subsetSums, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hβ', dite_true,
      Option.getD_some]
    rw [← Array.getD_eq_getD_getElem?, getD_subsetSums _ k (β / 2)
      (by rw [pow_succ] at hβ; omega), Finset.sum_range_succ']
    simp only [Nat.testBit_succ, Nat.testBit_zero]
    by_cases h : β % 2 = 1
    · simp [h]
    · simp [h]

variable [DecidableEq F]

/-- Bit `i'` of byte `b` of entry `u` of a family: whether table `8 b + i'` holds `1` at `u`. -/
private def famBit {n N : ℕ} (T : Vector (CMlPolynomialEval F n) N) (u : Fin (2 ^ n)) (i : ℕ) :
    Bool :=
  if h : i < N then decide (T[i][u] = 1) else false

/-- The bytes of entry `u` of a family: byte `b` holds the bits `8 b, …, 8 b + 7`. -/
@[no_expose] def famBytes {n N : ℕ} (T : Vector (CMlPolynomialEval F n) N) (u : Fin (2 ^ n)) :
    Array ℕ :=
  Array.ofFn fun b : Fin (N / 8) ↦ bitsNat (fun i' ↦ famBit T u (8 * b.val + i')) 8

/-- The subset sums of the weights `8 b, …, 8 b + 7`. -/
def byteSums {N : ℕ} (L : Vector F N) (b : ℕ) : Array F :=
  subsetSums (fun i' ↦ L.toArray.getD (8 * b + i') 0) 8

/-- `Σ_i L_i · T_i[u]` for a family of `0`/`1` tables, a byte of indices at a time. -/
def combBytes (S : Array (Array F)) (bytes : Array ℕ) (nb : ℕ) : F :=
  sumFin fun b : Fin nb ↦ (S.getD b #[]).getD (bytes.getD b 0) 0

/-- A sum over `8 · N` indices, a byte at a time. -/
private theorem sum_range_bytes {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ N : ℕ, ∑ i ∈ Finset.range (8 * N), f i = ∑ b ∈ Finset.range N, ∑ i' ∈ Finset.range 8,
      f (8 * b + i')
  | 0 => by simp
  | N + 1 => by
    rw [show 8 * (N + 1) = 8 * N + 8 by ring, Finset.sum_range_add, sum_range_bytes f N,
      Finset.sum_range_succ (fun b ↦ ∑ i' ∈ Finset.range 8, f (8 * b + i')) N]

/-- **The byte-wise combination**: on a family of `0`/`1` tables of `8 · N'` tables, the sum of
the byte subset sums at the entry's bytes is the combination by the weights. -/
theorem combBytes_eq {n N : ℕ} (hN : 8 ∣ N) (L : Vector F N) (T : Vector (CMlPolynomialEval F n) N)
    (hT : ∀ (i : Fin N) (u : Fin (2 ^ n)), T[i][u] = 0 ∨ T[i][u] = 1) (u : Fin (2 ^ n)) :
    combBytes (Array.ofFn fun b : Fin (N / 8) ↦ byteSums L b) (famBytes T u) (N / 8) =
      ∑ i : Fin N, L[i] * T[i][u] := by
  obtain ⟨N', rfl⟩ := hN
  have hdiv : 8 * N' / 8 = N' := by omega
  rw [combBytes, sumFin_eq_sum]
  have hterm : ∀ i : Fin (8 * N'), L[i] * T[i][u] =
      if famBit T u i.val then L.toArray.getD i 0 else 0 := fun i ↦ by
    simp only [famBit, i.isLt, dite_true]
    rcases hT i u with h | h <;> simp only [Fin.getElem_fin] at h <;> simp [h]
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ if famBit T u i then L.toArray.getD i 0 else 0),
    sum_range_bytes, ← Fin.sum_univ_eq_sum_range (fun b ↦ ∑ i' ∈ Finset.range 8,
      if famBit T u (8 * b + i') then L.toArray.getD (8 * b + i') 0 else 0)]
  refine Fintype.sum_equiv (finCongr hdiv) _ _ fun b ↦ ?_
  have hb : b.val < N' := by have := b.isLt; omega
  have h1 : (Array.ofFn fun b : Fin (8 * N' / 8) ↦ byteSums L b).getD b #[] = byteSums L b := by
    simp [Array.getD_eq_getD_getElem?, hb]
  have h2 : (famBytes T u).getD b 0 = bitsNat (fun i' ↦ famBit T u (8 * b.val + i')) 8 := by
    simp [famBytes, Array.getD_eq_getD_getElem?, hb]
  rw [h1, h2, byteSums, getD_subsetSums _ _ _ (bitsNat_lt _ 8)]
  simp only [finCongr_apply, Fin.val_cast]
  refine Finset.sum_congr rfl fun i' hi' ↦ ?_
  rw [testBit_bitsNat]
  simp [Finset.mem_range.mp hi']

/-- Whether every entry of a family is `0` or `1`. -/
def famBool {n N : ℕ} (T : Vector (CMlPolynomialEval F n) N) : Bool :=
  T.all fun t ↦ t.all fun x ↦ decide (x = 0) || decide (x = 1)

private theorem famBool_spec {n N : ℕ} {T : Vector (CMlPolynomialEval F n) N} (h : famBool T = true)
    (i : Fin N) (u : Fin (2 ^ n)) : T[i][u] = 0 ∨ T[i][u] = 1 := by
  have h1 := Vector.all_eq_true.mp h i i.isLt
  have h2 := Vector.all_eq_true.mp h1 u u.isLt
  simpa using h2

end Bytes

/-! ## The tables, computed once -/

section Fast

variable {F : Type} [Field F] [DecidableEq F]

/-- `Σ_i a_i · v_i`, the terms with `v_i = 0` skipped and those with `v_i = 1` added without a
product. -/
def dotSparse {n : ℕ} (a : Vector F n) (v : Fin n → F) : F :=
  Fin.foldl n (fun acc i ↦
    let x := v i
    if x = 0 then acc else if x = 1 then acc + a[i] else acc + a[i] * x) 0

/-- `dotSparse` is the dot product. -/
theorem dotSparse_eq {n : ℕ} (a : Vector F n) (v : Fin n → F) :
    dotSparse a v = ∑ i, a[i] * v i := by
  have h : (fun acc (i : Fin n) ↦
      let x := v i
      if x = 0 then acc else if x = 1 then acc + a[i] else acc + a[i] * x) =
      fun acc i ↦ acc + a[i] * v i := by
    funext acc i
    simp only
    split_ifs with h0 h1
    · rw [h0, mul_zero, add_zero]
    · rw [h1, mul_one]
    · rfl
  rw [dotSparse, h, foldl_add_eq_add_sum, zero_add]

variable {s m κ : ℕ}

/-- The left and the right products laid out like the witness, each block walked once. -/
def walkedTables (C : BlockR1CS F (s + m)) (zt : Vector (CMlPolynomialEval F (m + κ)) (2 ^ s)) :
    Vector (CMlPolynomialEval F (m + κ)) (2 ^ s) × Vector (CMlPolynomialEval F (m + κ)) (2 ^ s) :=
  let ws := Vector.ofFn fun t : Fin (2 ^ κ) ↦ C.rows (batchBlock (fun i ↦ zt[i]) t)
  (Vector.ofFn fun i ↦ Vector.ofFn fun u ↦
      ws[((cubeSplit m κ).symm u).2].1[cubeIndex i ((cubeSplit m κ).symm u).1],
    Vector.ofFn fun i ↦ Vector.ofFn fun u ↦
      ws[((cubeSplit m κ).symm u).2].2[cubeIndex i ((cubeSplit m κ).symm u).1])

omit [DecidableEq F] in
/-- The walked tables are the left and the right products. -/
theorem walkedTables_eq (C : BlockR1CS F (s + m))
    (zt : Vector (CMlPolynomialEval F (m + κ)) (2 ^ s)) :
    walkedTables C zt =
      (Vector.ofFn (leftTable C fun i ↦ zt[i]), Vector.ofFn (rightTable C fun i ↦ zt[i])) := by
  simp only [walkedTables, Prod.mk.injEq]
  constructor <;> refine Vector.ext fun i hi ↦ Vector.ext fun u hu ↦ ?_ <;>
    simp [leftTable, rightTable]

/-- The skip table at `Y` of tables held in a vector: the Lagrange combination entry by entry. -/
def skipTableOf {n : ℕ} (nodes : SkipDomain F s) (T : Vector (CMlPolynomialEval F n) (2 ^ s))
    (Y : F) : CMlPolynomialEval F n :=
  let L := skipWeights nodes Y
  Vector.ofFn fun u ↦ dotSparse L fun i ↦ T[i][u]

private theorem skipTableOf_eq {n : ℕ} (nodes : SkipDomain F s)
    (T : Vector (CMlPolynomialEval F n) (2 ^ s)) (Y : F) :
    skipTableOf nodes T Y = skipTable nodes (fun i ↦ T[i]) Y := by
  simp only [skipTableOf, skipTable, dotSparse_eq]

/-- The skip message from the walked tables: `P` on the coset, each skip table built once per
node. -/
def skipMessageDot (nodes : SkipDomain F s)
    (lt rt zt : Vector (CMlPolynomialEval F (m + κ)) (2 ^ s)) (r : Vector F (m + κ)) :
    Vector F (2 ^ s) :=
  Vector.ofFn fun k ↦
    let Y := nodes.pts[2 ^ s + k.val]
    let A := skipTableOf nodes lt Y
    let B := skipTableOf nodes rt Y
    let Z := skipTableOf nodes zt Y
    evalMle (Vector.ofFn fun u ↦ A[u] * B[u] - Z[u]) r

/-- The skip message from the walked tables is the honest one. -/
private theorem skipMessageDot_eq (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (r : Vector F (m + κ)) :
    skipMessageDot nodes (Vector.ofFn (leftTable C z)) (Vector.ofFn (rightTable C z))
      (Vector.ofFn z) r = skipMessage nodes C z r := by
  simp only [skipMessageDot, skipMessage, pValue, skipTableOf_eq, Fin.getElem_fin,
    Vector.getElem_ofFn, Fin.eta]

/-- The skip message from the walked tables: on tables of `0`s and `1`s, every entry of the skip
tables combined a byte of tables at a time (`combBytes`), from the weights' subset sums. -/
def skipMessageOf (nodes : SkipDomain F s)
    (lt rt zt : Vector (CMlPolynomialEval F (m + κ)) (2 ^ s)) (r : Vector F (m + κ)) :
    Vector F (2 ^ s) :=
  if 2 ^ s % 8 = 0 ∧ famBool lt = true ∧ famBool rt = true ∧ famBool zt = true then
    let bl := Vector.ofFn fun u ↦ famBytes lt u
    let br := Vector.ofFn fun u ↦ famBytes rt u
    let bz := Vector.ofFn fun u ↦ famBytes zt u
    Vector.ofFn fun k ↦
      let S := Array.ofFn fun b : Fin (2 ^ s / 8) ↦
        byteSums (skipWeights nodes nodes.pts[2 ^ s + k.val]) b
      evalMle (Vector.ofFn fun u ↦ combBytes S bl[u] (2 ^ s / 8) * combBytes S br[u] (2 ^ s / 8) -
        combBytes S bz[u] (2 ^ s / 8)) r
  else skipMessageDot nodes lt rt zt r

/-- The skip message a byte of tables at a time is the one by dot products. -/
private theorem skipMessageOf_eq_dot (nodes : SkipDomain F s)
    (lt rt zt : Vector (CMlPolynomialEval F (m + κ)) (2 ^ s)) (r : Vector F (m + κ)) :
    skipMessageOf nodes lt rt zt r = skipMessageDot nodes lt rt zt r := by
  have hc : ∀ (L : Vector F (2 ^ s)) (T : Vector (CMlPolynomialEval F (m + κ)) (2 ^ s)),
      famBool T = true → 8 ∣ 2 ^ s → ∀ u : Fin (2 ^ (m + κ)),
      combBytes (Array.ofFn fun b : Fin (2 ^ s / 8) ↦ byteSums L b) (famBytes T u) (2 ^ s / 8) =
        dotSparse L fun i ↦ T[i][u] := fun L T hT hN u ↦ by
    rw [dotSparse_eq]; exact combBytes_eq hN L T (famBool_spec hT) u
  unfold skipMessageOf
  split
  · next h =>
    have hN : 8 ∣ 2 ^ s := Nat.dvd_of_mod_eq_zero h.1
    refine Vector.ext fun k hk ↦ ?_
    simp only [skipMessageDot, skipTableOf, Vector.getElem_ofFn, Fin.getElem_fin, Fin.eta,
      hc _ _ h.2.1 hN, hc _ _ h.2.2.1 hN, hc _ _ h.2.2.2 hN]
  · rfl

/-- The skip message from the walked tables is the honest one. -/
private theorem skipMessageOf_eq (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (r : Vector F (m + κ)) :
    skipMessageOf nodes (Vector.ofFn (leftTable C z)) (Vector.ofFn (rightTable C z))
      (Vector.ofFn z) r = skipMessage nodes C z r := by
  rw [skipMessageOf_eq_dot, skipMessageDot_eq]

/-- The lincheck's column weights, the backward walk computed once. -/
def mTableOf (C : BlockR1CS F (s + m)) (cpos : Fin (2 ^ (s + m)))
    (e : CMlPolynomialEval F (s + m)) (α : F) : CMlPolynomialEval F (s + m) :=
  let ce := C.cols e
  let a2 := α ^ 2
  let a3 := α ^ 3
  Vector.ofFn fun j ↦ ce.1[j] + α * ce.2[j] + a2 * e[j] + if j = cpos then a3 else 0

omit [DecidableEq F] in
private theorem mTableOf_eq (C : BlockR1CS F (s + m)) (cpos : Fin (2 ^ (s + m)))
    (e : CMlPolynomialEval F (s + m)) (α : F) : mTableOf C cpos e α = mTable C cpos e α := by
  refine Vector.ext fun j hj ↦ ?_
  simp only [mTableOf, mTable, Vector.getElem_ofFn]
  split <;> simp

/-- The folded witness from the witness tables: each entry a combination of the batch's. -/
def zTableOf (zt : Vector (CMlPolynomialEval F (m + κ)) (2 ^ s)) (χout : Vector F κ) :
    CMlPolynomialEval F (s + m) :=
  let L := lagrangeBasis χout
  Vector.ofFn fun j ↦
    dotSparse L fun t ↦ zt[((cubeSplit s m).symm j).1][cubeIndex ((cubeSplit s m).symm j).2 t]

private theorem zTableOf_eq (zt : Vector (CMlPolynomialEval F (m + κ)) (2 ^ s))
    (χout : Vector F κ) :
    zTableOf zt χout = zTable (fun i ↦ zt[i]) χout := by
  rw [zTable_eq_sum]
  simp only [zTableOf, dotSparse_eq, batchBlock, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-- The tables' extensions at a point, with the equality kernel built once. -/
def evalsOf {n : ℕ} (zt : Vector (CMlPolynomialEval F n) (2 ^ s)) (p : Vector F n) :
    Vector F (2 ^ s) :=
  let L := lagrangeBasis p
  Vector.ofFn fun i ↦ dotSparse L fun u ↦ zt[i][u]

private theorem evalsOf_eq {n : ℕ} (zt : Vector (CMlPolynomialEval F n) (2 ^ s)) (p : Vector F n) :
    evalsOf zt p = Vector.ofFn fun i ↦ evalMle zt[i] p := by
  simp only [evalsOf, dotSparse_eq, evalMle_eq_sum, mul_comm]

end Fast

/-! ## The cached prover -/

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] (P : Params F)
  {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] {W : Type}
  (C : BlockR1CS F (P.s + P.m))
  (z : (∀ i, O i) → Fin (2 ^ P.s) → CMlPolynomialEval F (P.m + P.κ))
  {S : Type} (side : S → (∀ i, O i) → Prop)

/-- A table on the zerocheck's coordinates. -/
private abbrev Tab : Type := CMlPolynomialEval F (P.m + P.κ)

/-- The `2 ^ s` tables of a family. -/
private abbrev Tabs : Type := Vector (Tab P) (2 ^ P.s)

/-- The witness tables and the left and right products, from the oracles. -/
private def skipSpec (o : ∀ i, O i) : Tabs P × Tabs P × Tabs P :=
  (Vector.ofFn (z o), Vector.ofFn (leftTable C (z o)), Vector.ofFn (rightTable C (z o)))

/-- The same, every block walked once. -/
private def skipFast (o : ∀ i, O i) : Tabs P × Tabs P × Tabs P :=
  let zt := Vector.ofFn (z o)
  let lr := walkedTables C zt
  (zt, lr.1, lr.2)

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
private theorem skipFast_eq (o : ∀ i, O i) : skipFast P C z o = skipSpec P C z o := by
  simp only [skipFast, skipSpec, walkedTables_eq, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-- The witness tables and the three skip tables at `Y`. -/
private def zcSpec (o : ∀ i, O i) (Y : F) : Tabs P × Tab P × Tab P × Tab P :=
  (Vector.ofFn (z o), zcA P C z o Y, zcB P C z o Y, zcC P z o Y)

/-- The zerocheck's round cache: the witness tables and the skip tables, which no challenge
changes; the round polynomial read off them. -/
private def zcCache (n : ℕ) : RoundCache (zcFamily P C z side (W := W)).poly n where
  C _ := Tabs P × Tab P × Tab P × Tab P
  cache _ ctx _ := zcSpec P C z ctx.1.2 ctx.1.1.2.2
  msg j ctx c T := normRound T.2.1 T.2.2.1 T.2.2.2 ctx.1.1.2.1 j c
  step _ _ _ T _ := T
  msg_eq _ _ _ _ := rfl
  step_eq _ _ _ _ _ := rfl

/-- The column weights, the folded witness and the witness tables of the lincheck. -/
private def linSpec (o : ∀ i, O i) (x : LinX S F (P.m + P.κ)) :
    CMlPolynomialEval F (P.s + P.m) × CMlPolynomialEval F (P.s + P.m) × Tabs P :=
  (linM P C x, linZ P z o x, Vector.ofFn (z o))

/-- The lincheck's round cache: its two tables, which no challenge changes. -/
private def linCache (n : ℕ) : RoundCache (linFamily P C z side (W := W)).poly n where
  C _ := CMlPolynomialEval F (P.s + P.m) × CMlPolynomialEval F (P.s + P.m) × Tabs P
  cache _ ctx _ := linSpec P C z ctx.1.2 ctx.1.1
  msg j _ c T := highRound T.1 T.2.1 j c
  step _ _ _ T _ := T
  msg_eq _ _ _ _ := rfl
  step_eq _ _ _ _ _ := rfl

/-- The skip message, read off the walked tables. -/
private def skipMsgCached : Component.Cached (skipMsg P C z (S := S) (W := W))
    (fun p ↦ skipSpec P C z p.1.2) (fun p ↦ skipSpec P C z p.1.2) :=
  Component.Cached.sendChecked
    (msg := fun p T ↦ skipMessageOf P.nodes T.2.1 T.2.2 T.1 (P.point p.1.1.2))
    (upd := fun _ T _ ↦ T) (honest := skipHonest P C z) (check := fun _ _ ↦ true)
    (out := fun s msg ↦ (s, msg))
    (fun p ↦ by
      simp only [skipSpec, skipHonest]
      exact skipMessageOf_eq P.nodes C (z p.1.2) _) fun _ ↦ rfl

/-- `z_skip`, the skip tables built at it. -/
private def skipDrawCached : Component.Cached (skipDraw P (S := S) (O := O) (W := W))
    (fun p ↦ skipSpec P C z p.1.2) ((zcCache P C z side P.m).at (j := 0)) :=
  Component.Cached.sample
    (upd := fun _ T Y ↦ (T.1, skipTableOf P.nodes T.2.1 Y, skipTableOf P.nodes T.2.2 Y,
      skipTableOf P.nodes T.1 Y))
    fun p Y ↦ by
      simp only [skipSpec, zcCache, RoundCache.at, ctxOf, skipNext, zcSpec, zcA, zcB, zcC,
        skipTableOf_eq, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-- The terminal message, read off the skip tables. -/
private def zcEndCached : Component.Cached (zcEnd P C z (S := S) (W := W))
    ((zcCache P C z side (P.m + P.κ)).at (j := P.m + P.κ)) (fun p ↦ Vector.ofFn (z p.1.2)) :=
  Component.Cached.sendChecked
    (msg := fun p T ↦ #v[evalMle T.2.1 p.1.1.2.1, evalMle T.2.2.1 p.1.1.2.1])
    (upd := fun _ T _ ↦ T.1) (fun _ ↦ rfl) fun _ ↦ rfl

/-- `α`, the lincheck's tables built at it. -/
private def alphaDrawCached : Component.Cached (alphaDraw P (S := S) (O := O) (W := W))
    (fun p ↦ Vector.ofFn (z p.1.2)) ((linCache P C z side P.m).at (j := 0)) :=
  Component.Cached.sample
    (upd := fun p zt α ↦ (mTableOf C P.cpos (eRow P.nodes p.1.1.1.2.2 (lowVec p.1.1.2.1)) α,
      zTableOf zt (highVec p.1.1.2.1), zt))
    fun p α ↦ by
      simp only [linCache, RoundCache.at, ctxOf, alphaNext, linSpec, linM, linZ, mTableOf_eq,
        zTableOf_eq, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-- The slices, read off the witness tables. -/
private def linEndCached : Component.Cached (linEnd P C z (S := S) (W := W))
    ((linCache P C z side P.m).at (j := P.m)) (fun _ ↦ ()) :=
  Component.Cached.sendChecked (msg := fun p T ↦ evalsOf T.2.2 (linPoint P p.1.1))
    (upd := fun _ _ _ ↦ ()) (fun p ↦ by
      simp only [linCache, RoundCache.at, linSpec, evalsOf_eq, linHonest, Fin.getElem_fin,
        Vector.getElem_ofFn, Fin.eta]) fun _ ↦ rfl

variable (s' : ℕ) {K : Type} [CommRing K] (φ : K →+* F) (g : K) {μ : ℕ}
  (lift : Vector F (P.m + P.κ) → Vector F μ) {StmtOut : Type}
  (finish : S → Weight F μ → F → StmtOut)

/-- The switched claim's last coefficient, its weight built by `eqBatch` (`ringWeightFast`). -/
private def ringFinalCached :
    Component.Cached (ringFinal P s' φ g lift finish (O := O) (S := S) (W := W))
    (fun _ ↦ ()) (fun _ ↦ ()) := by
  unfold ringFinal
  exact Component.Cached.sampleOut (upd := fun _ _ _ ↦ ())
    (f' := fun st x ↦ finish st.1.1 (ringWeightFast P s' lift st.1.2.1 (st.2.push x))
      (ringTarget P s' φ g st.1.2.2 (st.2.push x)))
    (fun st x ↦ by rw [ringWeightFast_eq]) fun _ _ ↦ rfl

/-- Ring switching, the switched weight built by `eqBatch`. -/
private def ringSwitchCached :
    Component.Cached (ringSwitch P s' φ g lift finish (O := O) (S := S) (W := W))
    (fun _ ↦ ()) (fun _ ↦ ()) :=
  (Component.Cached.ofDef (Component.drawPushes O F s')).append
    (ringFinalCached P s' φ g lift finish)

/-- **The Flock argument's cached prover**: the witness tables and products walked once, the skip
tables built once at `z_skip`, the lincheck's tables once at `α`, the switched weight's values
built on the terms' supports. -/
@[no_expose] def flockCached :
    Component.Cached (flock P C z side s' φ g lift finish (W := W)) (fun _ ↦ ()) (fun _ ↦ ()) :=
  (Component.Cached.ofDef (Component.drawPushes O F P.nRand)).append
    ((skipMsgCached P C z).adaptIn (fun p _ ↦ skipFast P C z p.1.2)
      fun p ↦ skipFast_eq P C z p.1.2) |>.append
    (skipDrawCached P C z side) |>.append
    (SumcheckRound.cachedRounds (zcCache P C z side P.m) _ P.m 0 (Nat.zero_add _)) |>.append
    (SumcheckRound.cachedRounds (zcCache P C z side (P.m + P.κ)) _ P.κ P.m rfl) |>.append
    (zcEndCached P C z side) |>.append (alphaDrawCached P C z side) |>.append
    (SumcheckRound.cachedRounds (linCache P C z side P.m) _ P.m 0 (Nat.zero_add _)) |>.append
    (linEndCached P C z side) |>.append (ringSwitchCached P s' φ g lift finish)

end

end Flock

end LeanerVM.Protocol
