module

public import Statement.LeanIsa
public import Statement.LeanVmVerifier
public import Statement.Decode.Bf64Trace
public import CompPoly.Bivariate.GuruswamiSudan.Executable
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Completeness
public import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
public import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
public import CompPoly.Univariate.Roots.Shoup
public import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Fast

/-!
# The knowledge extractor

The fixed straight-line extractor of `KnowledgeSoundness` (`Statement/LeanVm.lean`): from the
announced sizes, the stack's Merkle root and the Keccak-256 evaluations it is given, the halting
run of the memory image of a stack in the Johnson list of the committed word. It is an algorithm:
every definition below is computable and deterministic (no coins), and its running time is
polynomial in its input (the cost table below, a reading of its loops rather than a theorem).
-/

section

/-!
## The knowledge extractor

Knowledge soundness (`KnowledgeSoundness`, `Statement/LeanVm.lean`) is stated for the extractor
defined here, `extract`, through `LeanVM.extractorRpm`, which applies it to the program's
bytecode and to the Keccak-256 evaluations of the adversary's transcript of queries to the random
permutation (`transcriptHashes`: the byte strings whose whole sponge path the adversary queried,
with their digests, and the list of those byte strings, `keys`). It is straight-line: it reads the
proof and those evaluations, and nothing else. It neither queries the permutation, nor sees the
verifier's queries, nor runs the adversary again. It does four things.

1. **The announced sizes and the stack's root** (`afterRoot`). It reads them off the proof as the
   verifier's first two steps do, `verify_execution` steps 1 and 2 (`verifier.py:1469-1480`):
   the announced sizes and the layout they build (`readSizes`), then the stack's Merkle root and
   the shape level 0 of the opening commits it at (`commitStack`). These steps read scalars and
   absorb them into the Fiat-Shamir sponge; what they read does not depend on the sponge, so the
   extractor does not compute it (it runs them with every hash and permutation answered by a
   constant, `fun _ ↦ default`).
2. **The committed word** (`committedLeaves`, `leafAt`). It inverts the Merkle tree under the root
   through the evaluations, top down: a node's children are the two digests its unique answered
   64-byte preimage holds, a leaf the words of its unique answered preimage (`preimage`); an
   unanswered node gives zero leaves. Leaf `v` is then the leaf of the opening at position `v`
   that climbs to the root through the evaluations (`openOne`, the check of `Transcript.merkle`,
   `verifier.py:433-445`), if there is one, and the zero row otherwise (proved when no two
   strings have one digest).
3. **The candidates** (`decodeStacks`). Level 0 commits the stack (the committed columns, stacked,
   `2^μ` words of `K`) in `2^6` lanes: lane `u` is the stack's block `u`, its cells
   `j + 2^(μ−6)·u` for `j < 2^(μ−6)`, read as coefficients in the novel polynomial basis `X_j`,
   and column `v` of the word is the leaf holding the values of the `64` lanes at the domain point
   `x_v = K.ofBits v`, in reverse order (`verifier.py:1165-1166`, `tuple(reversed(row))`): the
   binary Reed–Solomon code of Annex B, §B.2 (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`)
   and the encoder of Annex D, `def:enc` (`doc/leanvm/body/d-novel-basis.tex`), `encode` below.
   The candidates (`Candidates`) are the stacks whose encoding agrees with the word on at least
   the Johnson threshold of columns (`johnsonThreshold`): the stacks of the Johnson list of the
   word, at most `2^18` of them at every admissible shape. The extractor lists them: it decodes
   each lane with the Guruswami–Sudan list decoder over `K` (`gsLaneAt`), and extends prefixes of
   lanes one lane at a time, keeping a prefix while its lanes agree with the word on at least the
   threshold of common columns (`pruneUpTo`). Every candidate is listed (proved). A word without
   errors, an honest prover's, is decoded first by interpolation alone (`fastStacks`).
4. **The execution** (`candidateExecutionIn`). For a listed stack, the memory image its memory
   columns hold (`memoryImage`), run from the initial state `(pcInitial, fpInitial)` until it is in
   the final state `(pcFinal, fpFinal)`, for at most as many steps as the announced tables have rows
   (`stepCap`; a halting run never repeats a state and each of its steps takes a row of its own, so
   a valid execution a stack represents halts within the cap, proved). It returns the first listed
   stack's run that halts and has the public input at its boundary, so a valid execution of the
   program on the public input; `none` if there is none.

**Cost**, in operations of `K` and byte comparisons; `N` the number of evaluations given, `n =
2^(κ+R)` the columns (`κ = μ − 6 ≤ 22`, `R ≤ 4`), `L` the list size (at most `2^18` candidates,
`LeanVM.candidates_ncard_le`; the Johnson bound caps the prefixes kept likewise), `m ≤ 4096` the
decoder's multiplicity and `ℓ ≤ 12291` its `Y`-degree (`gsMultiplicityAt`), `M = 2^logMemory`,
`B = 2^logBytecode`:

| Step | Cost |
| --- | --- |
| sizes and root (`afterRoot`) | linear in the proof and the bytecode |
| Merkle inversion (`committedLeaves`) | `N` evaluations, then `2^(height+1)` scans of `N` pairs |
| one lane's list (`gsLaneAt`): interpolation, roots | Lee–O'Sullivan on `n·m(m+1)/2` conditions; Roth–Ruckenstein, `ℓ·2^κ` root findings of degree at most `ℓ`, each `64` squarings and `64` trace splittings |
| novel coefficients (`toNovel`, `novelInv`, `novelFwd`) | `2^κ` evaluations, `κ·2^(κ+R)` butterflies |
| pruning (`pruneUpTo`), 64 lanes | `64·L²·n` comparisons |
| a candidate's execution | `M + B` to index the addresses, at most `stepCap ≤ 2^μ` steps of a fetch and at most 26 reads |

Every loop is a traversal of an explicitly sized list or array, or a recursion on an explicit
natural number (the height, the number of lanes, the cap): there is no unbounded search, and no
classical choice. The list decoder is CompPoly's, whose algorithms are cited below. The whole is
polynomial, dominated by the interpolation, but far too slow to run at deployed sizes except on a
word without errors (`fastStacks`).

Every citation `verifier.py:N` is a line of `python-verifier/verifier.py` at leanVM
`94ee12ff6b2a3d42ba8328e22d09443692e4800b`, the commit `LeanVmVerifier.lean` transcribes; the
Annexes are cited at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`.

**Credits.** The list decoder over `K` is CompPoly's (github.com/Verified-zkEVM/CompPoly at
`572f997390aa4fc131ef30b1186fa1dcf292ca10`, Apache-2.0, "Copyright (c) 2026 CompPoly
Contributors"): by Valerii Huhnin, the executable Guruswami–Sudan decoder and its core and filter
(`Bivariate/GuruswamiSudan/{Executable,Core,Filter,Context}.lean`), its interpolation by the
algorithm of Lee and O'Sullivan (*List decoding of Reed–Solomon codes from a Gröbner basis
perspective*, J. Symbolic Comput. 43, 2008) with the reduction of Mulders and Storjohann (*On
lattice reduction for polynomial matrices*, J. Symbolic Comput. 35, 2003), its bivariate roots by
the algorithm of Roth and Ruckenstein (*Efficient decoding of Reed–Solomon codes beyond half the
minimum distance*, IEEE Trans. Inf. Theory 46, 2000), the roots in a finite field and their
deterministic splitting by Shoup's small-characteristic trace splitter (*A fast deterministic
algorithm for factoring polynomials over finite fields of small characteristic*, ISSAC 1991; at
characteristic two, Berlekamp's trace algorithm), the vanishing polynomial and batch evaluation
(`Univariate/{Vanishing,BatchEval/Context}.lean`), and `SmallPrimeTraceContext`; by Nicolas
Schleicher, `BF64`; and `CPolynomial` (Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond
Coles, Valerii Huhnin, Julian Sutherland). The decoder's parameter check mirrors ArkLib's
certificate (github.com/Verified-zkEVM/ArkLib at `4dae3acff846125521b7b3998010885071746f16`,
Apache-2.0; not imported): `GSParamCert` (`GuruswamiSudan/Executable.lean`, Valerii Huhnin) and
the closed form of `numVars` (`GuruswamiSudan/Basic.lean`, Stefano Rocca). The novel-basis
transforms are the additive NTT of Lin, Chung and Han (FOCS 2014), as in Diamond and Posen,
*Polylogarithmic proofs for multilinears over binary towers* (2024), Algorithm 2, whose forward
stage and point order are CompPoly's `AdditiveNTT` (Chung Thai Nguyen and Quang Dao); no code of
it is copied. The list decoding is Guruswami and Sudan's (*Improved decoding of Reed–Solomon and
algebraic-geometry codes*, IEEE Trans. Inf. Theory 45, 1999).
-/

namespace LeanVM.Extraction

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir LeanVM.Protocol.KeccakHash
open CompPoly CompPoly.GuruswamiSudan CompPoly.CPolynomial.Roots.FiniteField

@[expose] public section

/-! ### 1. The announced sizes and the stack's root -/

/-- `verify_execution`'s steps 1 and 2 (`verifier.py:1469-1480`): read the announced sizes, then
the stack's root; the layout and the WHIR rate exponent. -/
def announceSizesAndRoot (bytecode : List K) : Prog (Layout × ℕ) := do
  let (layout, logInverseRate) ← readSizes bytecode
  commitStack layout.stackLog logInverseRate
  return (layout, logInverseRate)

/-- The verifier's state after its steps 1 and 2 on the proof `π`: the announced layout and rate
exponent, and the state, whose first root is the stack's. The steps only read scalars, so the
sponge is not computed: every hash and every permutation is taken to be `0`. `none` if the steps
reject. -/
def afterRoot (bytecode : List K) (π : Proof) : Option ((Layout × ℕ) × St) :=
  Id.run (run (m := Id) (fun _ ↦ default) (fun _ ↦ default) (announceSizesAndRoot bytecode)
    ⟨⟨default, []⟩, π.stream, π.openings, []⟩)

/-! ### 2. The committed word -/

/-- The little-endian 64-bit word of the first eight bytes (the inverse of `wordBytes`). -/
def bytesWord (b : Bytes) : UInt64 :=
  UInt64.ofNat ((b.take 8).foldr (fun x acc ↦ x.toNat + 256 * acc) 0)

/-- The first `L` little-endian 64-bit words of a byte string. -/
def bytesLanes : ℕ → Bytes → List UInt64
  | 0, _ => []
  | L + 1, b => bytesWord b :: bytesLanes L (b.drop 8)

/-- The digest of the first 32 bytes (the inverse of `digestBytes`). -/
def bytesDigest (b : Bytes) : Digest := Vector.ofFn fun i : Fin 4 ↦ (bytesLanes 4 b).getD i.val 0

/-- The `w` words of `K` of the first `8w` bytes (the inverse of `flatMap kBytes`). -/
def bytesWords (w : ℕ) (b : Bytes) : List K := (bytesLanes w b).map K.ofLane

/-- The two children of a node, from the 64 bytes it hashes. -/
def splitNode (b : Bytes) : Digest × Digest := (bytesDigest b, bytesDigest (b.drop 32))

/-- The answered pairs `(x, answers x)` of the keys, one call of `answers` per key. -/
def answerPairs (answers : Bytes → Option Digest) (keys : List Bytes) : List (Bytes × Digest) :=
  keys.filterMap fun x ↦ (answers x).map (x, ·)

/-- The byte string of length `len` answered by `d`, if exactly one is; `none` otherwise. -/
def preimage (pairs : List (Bytes × Digest)) (d : Digest) (len : ℕ) : Option Bytes :=
  let hit : Bytes × Digest → Bool := fun p ↦
    decide (p.2.toList = d.toList) && decide (p.1.length = len)
  match pairs.find? hit with
  | none => none
  | some p => if pairs.all (fun p' ↦ !hit p' || decide (p'.1 = p.1)) then some p.1 else none

/-- The leaf under a digest: the `w` words of its preimage of `8w` bytes, zeros if there is none. -/
def leafOf (pairs : List (Bytes × Digest)) (w : ℕ) (d : Digest) : List K :=
  match preimage pairs d (8 * w) with
  | some x => bytesWords w x
  | none => List.replicate w 0

/-- The `2^h` leaves under the digest `d` at height `h`, left to right: a node's children are the
halves of its 64-byte preimage; zero leaves under a node without one. -/
def subtreeLeaves (pairs : List (Bytes × Digest)) (w : ℕ) : ℕ → Digest → Array (List K)
  | 0, d => #[leafOf pairs w d]
  | h + 1, d =>
    match preimage pairs d 64 with
    | some x => subtreeLeaves pairs w h (splitNode x).1 ++ subtreeLeaves pairs w h (splitNode x).2
    | none => Array.replicate (2 ^ (h + 1)) (List.replicate w 0)

/-- **The committed leaves**: the `2^height` leaves of `width` words under `root`, read off the
answers to the keys. -/
def committedLeaves (answers : Bytes → Option Digest) (keys : List Bytes) (root : Digest)
    (height width : ℕ) : Array (List K) :=
  subtreeLeaves (answerPairs answers keys) width height root

/-- Position `v` of the committed word: leaf `v mod 2^height` (`width` zeros if absent). -/
def leafAt (leaves : Array (List K)) (height width v : ℕ) : List K :=
  leaves.getD (v % 2 ^ height) (List.replicate width 0)

/-! ### 3. The code and the candidates -/

/-- The subspace polynomial `W_i(a) = ∏_{v < 2^i} (a + x_v)`, `x_v = K.ofBits v`: it vanishes
exactly on `U_i = {x_v | v < 2^i}`. -/
def subspacePoly (i : ℕ) (a : K) : K := ∏ v ∈ Finset.range (2 ^ i), (a + K.ofBits v)

/-- The normalized subspace polynomial `Ŵ_i(a) = W_i(a) / W_i(x_{2^i})`. -/
def normSubspacePoly (i : ℕ) (a : K) : K :=
  subspacePoly i a * (subspacePoly i (K.ofBits (2 ^ i)))⁻¹

/-- The novel basis polynomial `X_j(a) = ∏_{i < 64, bit i of j} Ŵ_i(a)`. -/
def novelBasis (j : ℕ) (a : K) : K :=
  ∏ i ∈ Finset.range 64, if j.testBit i then normSubspacePoly i a else 1

/-- **The encoding of a stack** of `2^μ` words, at lane `u` and column `v`: with `κ = μ − 6`,
lane `u` is the message of the `2^κ` cells `j + 2^κ·u`, `j < 2^κ`, as coefficients of the novel
basis, evaluated at the domain point `x_v`: `Σ_j q[j + 2^κ·u] · X_j(x_v)`. -/
def encode {μ : ℕ} (q : Vector K (2 ^ μ)) (u v : ℕ) : K :=
  ∑ j ∈ Finset.range (2 ^ (μ - initialFold)),
    q.getD (j + 2 ^ (μ - initialFold) * u) 0 * novelBasis j (K.ofBits v)

/-- The columns, among the `2^(μ − 6 + R)` of the code at rate `2^-R`, at which the word `W`
agrees with the encoding of `q` on every lane, a leaf holding lane `u` at word `63 − u`. -/
def agreement {μ : ℕ} (R : ℕ) (W : ℕ → List K) (q : Vector K (2 ^ μ)) : Finset ℕ :=
  (Finset.range (2 ^ (μ - initialFold + R))).filter fun v ↦
    ∀ u : Fin (2 ^ initialFold), (W v).reverse.getD u 0 = encode q u v

/-- **The candidates** of a committed word: the stacks of `2^μ` words whose encoding at rate
`2^-R` agrees with the word on at least `A` columns. The extractor lists every one of them at the
Johnson threshold (`decodeStacks`). -/
def Candidates (μ R A : ℕ) (W : ℕ → List K) : Set (Vector K (2 ^ μ)) :=
  {q | A ≤ (agreement R W q).card}

/-- Level 0's Johnson slacks, `η = e / 2^22`: entry `[R − 1][μ − 15]` for the stack size `μ` and
the rate exponent `R`. The soundness proof certifies the opening's `2^-128` per query at these
slacks (chosen offline to balance the fold and query groups); a larger slack means a smaller list
of candidates. The table is copied from the proof's certificates, and the proof checks the copy
against them for every admissible shape (`certOf_e_eq`, `thrOf_eq_johnsonThreshold` in
`LeanVM.Protocol.EndToEnd.Sound`). -/
def johnsonSlack : List (List ℕ) := [
  [34, 45, 55, 68, 85, 107, 134, 189, 237, 298, 375, 471, 663, 832],
  [34, 52, 65, 81, 102, 128, 161, 203, 255, 321, 404, 508, 639, 802],
  [51, 63, 79, 99, 124, 156, 196, 247, 311, 391, 492, 618, 776, 975],
  [49, 61, 77, 96, 121, 152, 191, 240, 303, 381, 478, 602, 756, 949]]

/-- Level 0's slack `e` (`η = e/2^22`) for a stack of `2^μ` words at rate `2^-R`. -/
def johnsonSlackOf (μ R : ℕ) : ℕ := (johnsonSlack.getD (R - 1) []).getD (μ - minLogStack) 0

/-- `⌈√x⌉` on natural numbers. -/
def ceilSqrt (x : ℕ) : ℕ := if Nat.sqrt x * Nat.sqrt x = x then Nat.sqrt x else Nat.sqrt x + 1

/-- **The Johnson threshold** of level 0 for a stack of `2^μ` words at rate `2^-R`: with
`κ = μ − 6` message variables, `n = 2^(κ+R)` columns and the degree bound `D = 2^κ − 1`, the
agreement `⌈(√(D/n) + η)·n⌉`, the Johnson radius `√(D/n)` plus the slack `η = e/2^22`
(`johnsonSlackOf`), computed exactly in natural numbers: `(√(D/n) + η)·n = (√X + e·n)/2^22` with
`X = 2^44·D·n`, and `⌈(√X + b)/c⌉ = ⌈(⌈√X⌉ + b)/c⌉` (the real form is equal,
`johnsonThreshold_eq_real` in `LeanVM.Extraction`). The table's default `0` is never read: the
extractor reaches the threshold only after `readSizes` accepted the sizes, so `1 ≤ R ≤ 4` and
`15 ≤ μ ≤ 28`, the table's range. -/
def johnsonThreshold (μ R : ℕ) : ℕ :=
  let κ := μ - initialFold
  let n := 2 ^ (κ + R)
  let D := 2 ^ κ - 1
  (ceilSqrt (2 ^ 44 * D * n) + johnsonSlackOf μ R * n + 2 ^ 22 - 1) / 2 ^ 22

/-! ### 4. Novel-basis coefficients and evaluations

The additive NTT in the novel basis `X_j`, on the points `x_v`. Stage `i` pairs the positions `p`
and `p + 2^i` (bit `i` of `p` clear) with the twiddle `t = Ŵ_i(x_{⌊p/2^(i+1)⌋·2^(i+1)})`: the
forward stage maps `(lo, hi)` to `(lo + t·hi, lo + (t + 1)·hi)`, the inverse stage maps it back
(characteristic two). -/

/-- Stage `i`'s twiddles over a buffer of `2^m`: entry `w` is `Ŵ_i(x_{w·2^(i+1)})`. -/
def novelTwiddles (m i : ℕ) : Array K :=
  let nrm := (subspacePoly i (K.ofBits (2 ^ i)))⁻¹
  Array.ofFn fun w : Fin (2 ^ (m - (i + 1))) ↦ subspacePoly i (K.ofBits (w.val * 2 ^ (i + 1))) * nrm

/-- The forward butterfly stage `i` over a buffer of `2^m`. -/
def novelFwdStage (m i : ℕ) (b : Array K) : Array K :=
  let tw := novelTwiddles m i
  Array.ofFn fun p : Fin (2 ^ m) ↦
    let t := tw.getD (p.val / 2 ^ (i + 1)) 0
    if p.val.testBit i then
      b.getD (p.val - 2 ^ i) 0 + (t + 1) * b.getD p.val 0
    else
      b.getD p.val 0 + t * b.getD (p.val + 2 ^ i) 0

/-- The inverse butterfly stage `i` over a buffer of `2^m`. -/
def novelInvStage (m i : ℕ) (b : Array K) : Array K :=
  let tw := novelTwiddles m i
  Array.ofFn fun p : Fin (2 ^ m) ↦
    let t := tw.getD (p.val / 2 ^ (i + 1)) 0
    if p.val.testBit i then
      b.getD (p.val - 2 ^ i) 0 + b.getD p.val 0
    else
      b.getD p.val 0 + t * (b.getD p.val 0 + b.getD (p.val + 2 ^ i) 0)

/-- **The forward transform**: the `2^κ` novel-basis coefficients `c`, tiled `2^R` times, through
stages `κ − 1, …, 0`; entry `v` is `Σ_{j<2^κ} c_j·X_j(x_v)` for `v < 2^(κ+R)`, so the encoding of
a lane. -/
def novelFwd (κ R : ℕ) (c : Array K) : Array K :=
  (List.range κ).foldr (fun i b ↦ novelFwdStage (κ + R) i b)
    (Array.ofFn fun p : Fin (2 ^ (κ + R)) ↦ c.getD (p.val % 2 ^ κ) 0)

/-- **The inverse transform** on `U_κ`: the evaluations `y_v`, `v < 2^κ`, through stages
`0, …, κ − 1`, give the novel-basis coefficients. -/
def novelInv (κ : ℕ) (y : Array K) : Array K :=
  (List.range κ).foldl (fun b i ↦ novelInvStage κ i b) y

/-- **Monomial to novel basis**: the novel-basis coefficients of `p` (of degree `< 2^κ`), from its
evaluations on `U_κ`. -/
def toNovel (κ : ℕ) (p : CPolynomial K) : Array K :=
  novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ p.eval (K.ofBits v.val))

/-! ### 5. The list decoder of one lane

CompPoly's executable Guruswami–Sudan decoder over `K`, deterministic: Lee–O'Sullivan
interpolation, Roth–Ruckenstein roots, and the roots of a univariate polynomial as its `gcd` with
`X^(2^64) − X`, split by Shoup's trace splitter at `p = 2`, `k = 64` over the basis `x^i`, with
the trace `Tr(z) = Σ_{i<64} z^(2^i)`. A context's proof fields are theorems (CompPoly's, and the
two trace facts of `Statement/Decode/Bf64Trace.lean`); only its data is run. -/

/-- Shoup's trace context over `K`: `q = 2^64`, base constants `{0, 1}`, the basis `x^i`,
`i < 64`, and the trace `Σ_{i<64} z^(2^i)`. -/
def traceCtx : SmallPrimeTraceContext K where
  q := 2 ^ 64
  finite := inferInstance
  card_eq := BF64.nat_card_bf64
  frobenius_fixed := Bf64Trace.pow_two_pow_64
  p := 2
  k := 64
  p_prime := Nat.prime_two
  q_eq := rfl
  baseConstants := #[0, 1]
  baseConstants_size := rfl
  basis := Array.ofFn fun i : Fin 64 ↦ K.ofBits (2 ^ i.val)
  basis_size := Array.size_ofFn
  traceValue := tracePowerSum 2 64
  traceValue_eq_powerSum := fun _ ↦ rfl
  traceValue_mem_base := Bf64Trace.tracePowerSum_mem_base
  trace_separates := Bf64Trace.tracePowerSum_separates

/-- Deterministic univariate root finding over `K`. -/
def fieldRootCtx : FieldRootContext K :=
  finiteFieldRootContext K traceCtx.toFiniteFieldContext (shoupLinearFactorProductSplitter traceCtx)
    (fun hp ↦ finiteFieldRootProduct_shoupSplitterInput traceCtx hp)

/-- The list decoder's context: Lee–O'Sullivan interpolation and Roth–Ruckenstein roots. -/
def gsContext : GSFilteredCoreContext K :=
  filteredCoreContextOfInterpRootContexts
    (LeeOSullivan.leeOSullivanInterpContext CPolynomial.VanishingPolynomialContext.direct
      (CPolynomial.BatchEvalContext.horner K)
      (PolynomialMatrix.muldersStorjohannFastReducerContext K))
    (rothRuckensteinRootContext K fieldRootCtx)

/-- The number of unknowns of the interpolation, `#{(i, j) | i + (k−1)·j ≤ W}`, in closed form. -/
def gsNumVars (k W : ℕ) : ℕ := (W / (k - 1) + 1) * (2 * W + 2 - (k - 1) * (W / (k - 1))) / 2

/-- The number of interpolation conditions, `n·m(m+1)/2`. -/
def gsNumConstraints (n m : ℕ) : ℕ := n * (m * (m + 1) / 2)

/-- The parameter check at message length `k`, `n` points and radius `e`: more unknowns than
conditions, and a weighted degree below `m` times the agreement. -/
def gsPass (k n e : ℕ) (params : GSExecParams) : Bool :=
  decide (params.interp.messageDegree = k) && decide (params.radius = e) &&
    decide (0 < params.interp.multiplicity) &&
    decide (gsNumConstraints n params.interp.multiplicity <
      gsNumVars k params.interp.weightedDegreeBound) &&
    decide (params.interp.weightedDegreeBound < params.interp.multiplicity * (n - e))

/-- The parameters at multiplicity `m` for message length `k`, `n` points and agreement `A`:
weighted degree `W = m·A − 1`, radius `n − A`. -/
def gsParamsAt (k n A m : ℕ) : GSExecParams :=
  { interp := { messageDegree := k, multiplicity := m, weightedDegreeBound := m * A - 1 }
    radius := n - A }

/-- A multiplicity that passes the check whenever `A² > (k − 1)·n`:
`⌊((k−1)·n + 1)/(A² − (k−1)·n)⌋ + 1`. -/
def gsMultiplicityBoundAt (k n A : ℕ) : ℕ := ((k - 1) * n + 1) / (A * A - (k - 1) * n) + 1

/-- The least multiplicity, up to `gsMultiplicityBoundAt`, that passes the check. -/
def gsMultiplicityAt (k n A : ℕ) : ℕ :=
  ((List.range' 1 (gsMultiplicityBoundAt k n A)).find?
    fun m ↦ gsPass k n (n - A) (gsParamsAt k n A m)).getD (gsMultiplicityBoundAt k n A)

/-- The decoder's parameters for message length `k`, `n` points and agreement `A`. -/
def gsParamsFor (k n A : ℕ) : GSExecParams := gsParamsAt k n A (gsMultiplicityAt k n A)

/-- The symbol of lane `u` at column `v` of a word: the leaf's word `63 − u`, as `agreement`
reads it. -/
def laneSymbol (W : ℕ → List K) (u v : ℕ) : K := (W v).reverse.getD u 0

/-- The decoder's input for lane `u` on `n` columns: the pairs `(x_v, W_u(v))`, `v < n`. -/
def lanePoints (n : ℕ) (W : ℕ → List K) (u : ℕ) : Array (K × K) :=
  Array.ofFn fun v : Fin n ↦ (K.ofBits v.val, laneSymbol W u v.val)

/-- **The lane decoder**: Guruswami–Sudan over `K` on lane `u` of `W`, for messages of `2^κ`
coefficients on `2^(κ+R)` columns, at agreement `A`: every polynomial of degree `< 2^κ` that
agrees with the lane on at least `A` columns (when `A² > (2^κ − 1)·2^(κ+R)`). -/
def gsLaneAt (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : Array (CPolynomial K) :=
  GuruswamiSudan.decodeWithParams gsContext (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A)
    ⟨lanePoints (2 ^ (κ + R)) W u⟩

/-- The lane decoder's list as novel-basis coefficients, without duplicates. -/
def laneListAt (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : List (Array K) :=
  ((gsLaneAt κ R A W u).toList.map (toNovel κ)).dedup

/-! ### 6. The 64 lanes: prefix pruning -/

/-- One lane: extend every survivor `(cs, S)` (the coefficients of the lanes so far, and the
columns, in increasing order, where all of them agree with the word) by every `(c, e)` of the
lane's list, `e` the encoding of `c`, keeping the columns of `S` at which `e` agrees with the
lane's symbols `sym`; keep the extension if at least `A` columns remain. -/
def pruneStep (A : ℕ) (sym : ℕ → K) (L : List (Array K × Array K))
    (st : List (List (Array K) × List ℕ)) : List (List (Array K) × List ℕ) :=
  st.flatMap fun s ↦ L.filterMap fun ce ↦
    let S' := s.2.filter fun v ↦ decide (ce.2.getD v 0 = sym v)
    if A ≤ S'.length then some (s.1 ++ [ce.1], S') else none

/-- Lane `u`'s list with each element's encoding on the `2^(κ+R)` columns. -/
def laneEncodedAt (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : List (Array K × Array K) :=
  (laneListAt κ R A W u).map fun c ↦ (c, novelFwd κ R c)

/-- The survivors after lanes `0, …, U − 1`; a lane is decoded only while survivors remain. -/
def pruneUpTo (κ R A : ℕ) (W : ℕ → List K) (U : ℕ) : List (List (Array K) × List ℕ) :=
  (List.range U).foldl
    (fun st u ↦
      if st.isEmpty then [] else pruneStep A (laneSymbol W u) (laneEncodedAt κ R A W u) st)
    [([], List.range (2 ^ (κ + R)))]

/-- The stack of `2^μ` words whose lane `u` is `cs[u]`: cell `i` is entry `i mod 2^κ` of lane
`⌊i / 2^κ⌋`, `κ = μ − 6`. -/
def stackOf (μ : ℕ) (cs : List (Array K)) : Vector K (2 ^ μ) :=
  Vector.ofFn fun i ↦
    (cs.getD (i.val / 2 ^ (μ - initialFold)) #[]).getD (i.val % 2 ^ (μ - initialFold)) 0

/-- The decoded stacks at agreement `A`: the survivors of all `2^6` lanes, as stacks. -/
def decodeStacksAt (μ R A : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  (pruneUpTo (μ - initialFold) R A W (2 ^ initialFold)).map fun s ↦ stackOf μ s.1

/-- **The decoded stacks** of a committed word: every candidate at the Johnson threshold. -/
def decodeStacks (μ R : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  decodeStacksAt μ R (johnsonThreshold μ R) W

/-- **The fast path**, for a word without errors: the same pruning, with lane `u`'s list the one
array interpolated from its first `2^κ` columns (`novelInv`). At most one stack, a candidate,
for `2^6` inverse and forward transforms. -/
def fastStacks (μ R : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  let κ := μ - initialFold
  let st := (List.range (2 ^ initialFold)).foldl
    (fun st u ↦
      let c := novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ laneSymbol W u v.val)
      pruneStep (johnsonThreshold μ R) (laneSymbol W u) [(c, novelFwd κ R c)] st)
    [([], List.range (2 ^ (κ + R)))]
  st.map fun s ↦ stackOf μ s.1

/-! ### 7. The execution -/

/-- **The memory image of a stack**: `2^logMemory` words, word `i` the three limbs at cell `i` of
the memory columns `MEMORY_0`, `MEMORY_1`, `MEMORY_2` (`verifier.py:687`), each at its placement's
offset on the stack. -/
def memoryImage (layout : Layout) {μ : ℕ} (q : Vector K (2 ^ μ)) : MemImage layout.logMemory :=
  fun i ↦
    let limb (column : ℕ) : K := q.getD ((layout.placement column).index + i) 0
    E.ofLimbs (limb memory0) (limb memory1) (limb memory2)

/-- Insert `g^i ↦ i` into `m`, keyed by the lane of `g^i`, for the `n` indices `i` from `i₀`,
where `x = g^i₀`: one multiplication and one insertion per index. -/
def powIndexFrom : ℕ → ℕ → K → Std.HashMap UInt64 ℕ → Std.HashMap UInt64 ℕ
  | 0, _, _, m => m
  | n + 1, i, x, m => powIndexFrom n (i + 1) (x * g) (m.insert x.lane i)

/-- **The index of the address space of `2^κ` words**: the lane of `g^i` ↦ `i`, for `i < 2^κ`. -/
def powIndex (κ : ℕ) : Std.HashMap UInt64 ℕ := powIndexFrom (2 ^ κ) 0 1 ∅

/-- The index of address `a` among `2^κ` words, looked up in `idx`: `some i` when `idx` maps the
lane of `a` to `i < 2^κ` (`gLog?`, computed). -/
def gLogIn (idx : Std.HashMap UInt64 ℕ) (κ : ℕ) (a : K) : Option (Fin (2 ^ κ)) :=
  match idx[a.lane]? with
  | some i => if h : i < 2 ^ κ then some ⟨i, h⟩ else none
  | none => none

/-- One step (`step`, computed) with the memory index `memIdx` and the bytecode index `codeIdx`:
fetch the instruction at `pc`, then execute it (`executeWith`), reading the memory through
`memIdx`. -/
def stepIn (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : Program) {κ : ℕ} (L : MemImage κ)
    (r : Regs K) : Option (Regs K) :=
  (gLogIn codeIdx prog.logSize r.pc).map prog.code >>=
    executeWith (fun a ↦ (gLogIn memIdx κ a).map L) r

/-- The halting search from `r`, reached after `n` steps, with at most `fuel` more steps: `some m`
when the run is in the final state after `m` steps in all; `none` if a step fails or the fuel runs
out first. -/
def haltLoop (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : Program) {κ : ℕ}
    (L : MemImage κ) : ℕ → ℕ → Regs K → Option ℕ
  | 0, n, r => if r = Regs.final prog then some n else none
  | fuel + 1, n, r =>
    if r = Regs.final prog then some n
    else
      match stepIn memIdx codeIdx prog L r with
      | none => none
      | some r' => haltLoop memIdx codeIdx prog L fuel (n + 1) r'

/-- The image, run from the initial state `(pcInitial, fpInitial)` for the least number `n ≤ cap`
of steps after which it is in the final state `(pcFinal, fpFinal)`, if any. -/
def haltingRunIn (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : Program) {κ : ℕ}
    (image : MemImage κ) (cap : ℕ) : Option (Trace prog) :=
  (haltLoop memIdx codeIdx prog image cap 0 Regs.initial).map fun n ↦ ⟨κ, image, n⟩

/-- **The step cap of a layout**: the rows its tables hold, `2^τ_j` for each opcode table's
log-height `τ_j`, the `2^logMemory` words of the memory and the `2^logBytecode` slots of the
bytecode. -/
def stepCap (layout : Layout) : ℕ :=
  (layout.tableLogHeights.map (2 ^ ·)).sum + 2 ^ layout.logMemory + 2 ^ layout.logBytecode

/-- **The public boundary** (`HasPublicBoundary`), decided: the memory has between `2^16` and
`2^32` words, and words `0` and `1` (at the addresses `g^0`, `g^1`) hold the public input. -/
def boundaryOK {prog : Program} (input : PublicInput) (t : Trace prog) : Bool :=
  if h : minLogMem ≤ t.κ ∧ t.κ ≤ maxLogMem then
    decide (t.image ⟨0, Nat.two_pow_pos t.κ⟩ = input.word0) &&
      decide (t.image ⟨1, Nat.one_lt_two_pow (by unfold minLogMem at h; omega)⟩ = input.word1)
  else false

/-- **The execution of a stack**: the halting run of its memory image within the layout's step
cap, if it has the public boundary of `input`; `memIdx` and `codeIdx` index the memory's and the
bytecode's addresses. -/
def candidateExecutionIn (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : Program)
    (input : PublicInput) (layout : Layout) {μ : ℕ} (q : Vector K (2 ^ μ)) : Option (Trace prog) :=
  (haltingRunIn memIdx codeIdx prog (memoryImage layout q) (stepCap layout)).filter
    (boundaryOK input)

/-! ### 8. The extractor -/

/-- **The extractor.** From the adversary's answers and the keys they answer (byte strings
`answers` is `none` outside of), and the proof, with the bytecode's words as the verifier reads
them: the announced layout, rate exponent and stack root (`afterRoot`), the word the root commits
to (`committedLeaves`), and the execution of the first decoded stack (the fast path's, then the
list decoder's) that has one; `none` otherwise. The leaves and the two address indices are
computed once, for every stack. -/
def extract (prog : Program) (input : PublicInput) (bytecode : List K)
    (answers : Bytes → Option Digest) (keys : List Bytes) (π : Proof) : Option (Trace prog) := do
  let ((layout, logInverseRate), state) ← afterRoot bytecode π
  let (root, height, width) ← state.roots.head?
  let leaves := committedLeaves answers keys root height width
  let word := leafAt leaves height width
  let memIdx := powIndex layout.logMemory
  let codeIdx := powIndex prog.logSize
  let execution := candidateExecutionIn memIdx codeIdx prog input layout
  (fastStacks layout.stackLog logInverseRate word).findSome? execution <|>
    (decodeStacks layout.stackLog logInverseRate word).findSome? execution

end
end LeanVM.Extraction

end
