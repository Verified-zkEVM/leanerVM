# Dossier `code-layer1`: Layer 1 as built (hypercube tables, stacking, padding, claim weights, the index and bytecode columns)

Object: leanerVM `main` at `b435631` (every Lean line number below is at `b435631`, read with
`git show b435631:<path>`; the upgrade `144c5aa` changed only proof lines and test numerals in
these files, with equal line counts, see section H). Ground truth: leanVM at `a386121f`
(specification tex, Rust, Python verifier). Libraries: CompPoly at the old pin `3468b38c` and at
the new pin `572f9973` (which is also CompPoly `main` today); ArkLib at `dca90385` and `7653a901`.

## Summary

**Examined.** The nine Layer 1 modules (`ToCompPoly/{Multilinear,BitProductTable,Stacking,
AmbientStacking}.lean`, `Stack.lean`, `Padding.lean`, `ClaimWeights.lean`, `BlockClaims.lean`,
`FixedColumns.lean`; 1,628 lines, 143 public declarations), their nine test files (899 lines),
`Arithmetization/Bytecode.lean` (`encodeSlots`), the blueprint's conventions, Layer 1 sketch,
acceptance tests 7, 13, 14, 15 and interface list, the earlier review
`docs/reviews/protocol-layer1.md`; against specification §4.1, §5.4, §5.5, §6.5, §8.1, §8.5, the
Rust (`witness.rs`, `cpu/layout.rs`, `leaf.rs`, `constraints.rs`, `primitives/src/{multilinear.rs,
field/mod.rs}`, `pcs/src/stack_open.rs`, `hash_flock.rs`, `lean_compiler/src/lib.rs`) and the
Python verifier. Six probes: two Python scripts that call the pinned Python verifier's own
functions, four Lean files. All six ran once, with exit 0 (section I says how, given that the
checkout moved during the session).

**Conclusions.**

1. **Faithful where it transcribes.** The cube's bit order, the offsets and selectors, the
   one-padded leaf identity (equation (2) of §5.4), back-loaded padding, the index column and the
   bytecode column agree with leanVM, structurally and numerically. The strongest evidence: on
   the pinned Python verifier's real layout for one admissible announcement (92 committed
   blocks, `stack_log = 22`), `Blocks.offset` on the sorted sizes reproduces all 92 offsets; and
   `bytecodeColumn` of a sixteen-instruction program covering every opcode and every `DEREF`
   mode equals, cell for cell (256 cells), the table a line-by-line transcription of the Rust
   encoder builds, and its extension at `(ζ, α)` equals what `verifier.py:566` computes.
2. **No theorem is false or vacuous.** Every load-bearing and interface statement was read
   against its intended claim; every hypothesis (`B.total ≤ 2 ^ μ`, `Antitone size`) has
   inhabitants in the tests; the seventeen Layer 1 declarations checked with `#print axioms`
   (fourteen theorems, three definitions carrying proofs) depend only on `propext`,
   `Classical.choice`, `Quot.sound`.
3. **What Layer 1 does not carry, although leanVM needs it** (the main results):
   - the **strided reader** for the eighteen BLAKE2S limb columns (low coordinates frozen to a
     slot's bits): absent in every form; its generic selection lemma is twenty lines (probe
     `StridedProbe`, proved); no layer of the blueprint is assigned to write it;
   - the **order of equal-size blocks**: `Blocks` is the sorted sizes and nothing more; the
     tie order lives only in the renaming passed to `Layout.comap`, which no statement, definition
     or test of Layer 1 constrains (probe `OffsetsProbe`: leanVM's order and the "tables first"
     order give the same `Blocks` and different offsets per column);
   - `Layout.comap` accepts a renaming that is not injective, so a layout built with it can
     alias columns (probe `ValuesProbe`, three columns read off one block).
4. **Audit surface.** Today an auditor of the master theorems reads **no** Layer 1
   declaration: the master theorems are over an abstract `M3Instance`. Seventeen definitions
   (61 lines) become trusted when the adaptor is built, and about eight more (22 lines) when the
   executable verifier is. `BlockClaims.lean` (8 public declarations, 40 lines) has no consumer
   and restates `Blocks.unstack_eval₂_eq_sumCube`; `bytecodeColumn_slot` restates its
   definition. Both can go; the generic half can keep most of its 104 declarations `private` or
   in CompPoly.
5. **Blueprint conformance.** The sketch matches the code declaration by declaration. Stale or
   wrong: acceptance test 14 still names `bytecodeColumn_slot` as its witness (the tautology the
   earlier review said was met); acceptance test 15 says `stack_eval` "fails for any other
   placement" (false: sizes 1, 1, 2 in that order are aligned); the interface list omits the two
   evaluators a verifier runs (`idxColumnEval`, `bytecodeColumnEval`), `evalMle_padHigh`, and
   `Blocks.selectorWeight`, `Blocks.lowPoint`, `Blocks.total`, which appear in listed
   statements; Layer 3's `leanIsaInstance_fits` mentions `layout.total`, which `Layout` does not
   have.
6. **The wall and the To-folders.** Two files of `LeanerVM/Protocol` import the arithmetization:
   `FixedColumns.lean` (the documented exception) and the empty placeholder `Basic.lean`, which
   the blueprint does not list and nothing imports; none imports Clean or `LeanerVM.Semantics`
   directly, and no phase imports `FixedColumns`. The four `ToCompPoly` modules are generic;
   CompPoly at both pins has only `eqTilde_eq_prod` (the same as `evalMle_lagrangeBasis`,
   `DuplicatesProbe`) and `eqTilde_append` in common with them; ArkLib at both pins has nothing.
7. **The upgrade to `144c5aa`** changed only proofs in these files; the tests' `K` numerals were
   rewritten as `K.ofBits n`, the same words, so every test keeps its meaning (section H).

**Findings by severity** (section G): no critical. Major: the strided reader is missing and
unassigned (G.1); Layer 3's `leanIsaInstance_fits` cannot be stated as written (a one-line fix,
G.2).
Minor: the tie order is pinned by no statement or test before the compiled verifier (G.3);
acceptance test 14 names a tautology as its witness, and no repository test compares the bytecode
column with leanVM's encoder (G.4); acceptance test 15 overclaims (G.5); the interface list omits
load-bearing names and mislabels three (G.6); `BlockClaims.lean` is dead code (G.7);
`Protocol/Basic.lean` is an unlisted exception of the wall (G.8); acceptance test 7 names the
wrong lemma and an unbuilt witness (G.9). Notes: `Layout.comap` aliasing; the evaluator `idxColumnEval` is efficient
(binary exponentiation in CompPoly's `K`); the witness-stack floor and ceiling live outside
Layer 1; the upgrade preserved the meaning of every Layer 1 test.

## 0. The objects Layer 1 is built on

**CompPoly's hypercube table** (CompPoly is the Verified-zkEVM library of computable
polynomials; revision `3468b38c`, `CompPoly/Multilinear/Basic.lean`). A multilinear polynomial in
`n` variables is stored by its `2^n` values on the Boolean cube, as a vector; index `i` is the cube
point whose coordinate `k` is bit `k` of `i` (low bit first):

```lean
-- CompPoly/Multilinear/Basic.lean:45-47 at 3468b38c
  The indexing is **little-endian** (i.e. the least significant bit is the first bit). -/
@[reducible]
def CMlPolynomialEval (R : Type*) (n : ℕ) := Vector R (2 ^ n) -- coefficient of Lagrange basis
```

`lagrangeBasis w` is the vector of the equality kernel `eq(w, x) = ∏_k (x_k w_k + (1-x_k)(1-w_k))`
over the cube points `x`; `evalMle t x` is the multilinear extension of the table `t` evaluated at
a point `x ∈ R^n` (by folding one variable at a time, low variable first); `eval₂Mle t φ x` first
maps the entries through a ring homomorphism `φ : R →+* S` (for leanVM, the embedding
`algebraMap K E` of `K = GF(2^64)` into `E = GF(2^192)`), then evaluates at `x ∈ S^n`:

```lean
-- CompPoly/Multilinear/Basic.lean:410-411, 499-500, 520-521 at 3468b38c
def lagrangeBasis (w : Vector R n) : Vector R (2 ^ n) :=
  Vector.ofFn (fun i => ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j])
def evalMle (p : CMlPolynomialEval R n) (x : Vector R n) : R :=
  evalMleValues p x
def eval₂Mle (p : CMlPolynomialEval R n) (f : R →+* S) (x : Vector S n) : S :=
  evalMle (map f p) x
```

**The spine's objects Layer 1 plugs into** (`LeanerVM/Protocol/Field.lean`,
`Spine/Instance.lean`, `Spine/Seams.lean` at `b435631`). `Column n` wraps a `K`-table of `n`
variables; its oracle answers a query `r ∈ E^n` with `eval₂Mle q (algebraMap K E) r`
(`Field.lean:102-110`, `evalOracle_answer` is `rfl`). A `Layout μ ι κ` is a *reading law*: how
to read column `c` (height `2^κ c`) off a stack of `2^μ` cells, how to lift a point of the column
to a point of the stack, and the law that the two agree:

```lean
-- LeanerVM/Protocol/Spine/Instance.lean:73-81
structure Layout (μ : ℕ) (ι : Type) (κ : ι → ℕ) where
  /-- Read column `c` off the stack. -/
  read : Column μ → (c : ι) → Column (κ c)
  /-- Lift a point of column `c` to the point of the stack that reads the same value. -/
  extend : (c : ι) → Vector E (κ c) → Vector E μ
  /-- The selector law: reading then extending is extending then reading. -/
  read_eval : ∀ (q : Column μ) (c : ι) (z : Vector E (κ c)),
    CMlPolynomialEval.eval₂Mle (read q c).values (algebraMap K E) z =
      CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) (extend c z)
```

An `M3Instance` carries one such `layout` for all its columns (`Instance.lean:140`), and the
relation `M3Holds` reads every value through it. A `Weight μ` is a weight on the stack given by
its cube values `onCube` and an evaluator `mle` with the proof `mle_eq` that it computes the
extension of `onCube`; `Weight.pair W q = Σ_i W.onCube[i] · q[i]`; a `ColumnClaim` is
(column, point, value) and holds when the column's extension at the point is the value; a
`WeightedClaim` is (weight, value) and holds when the pairing is the value
(`Seams.lean:57-67, 103-124`).

**Mathlib vocabulary.** `Antitone f` means `a ≤ b → f b ≤ f a` (non-increasing). `Vector R n` is
an array of length `n`; `z ++ s` concatenates, so `z` fills the low coordinates. `Fin m` is
`{0, …, m-1}`.

## A. Catalogue

Class legend. **L** load-bearing: a definition the instance `leanIsaInstance` (Layer 3) or the
executable verifier (Layer 12) will unfold, so it becomes trusted surface when they are built
(no master theorem, seam or built instance unfolds any Layer 1 declaration today; see E).
**I** interface: consumed by name by a later phase, the adaptor, or listed in the blueprint's
interface list. **H** helper: a proof step. **T** test fixture (none: fixtures live under
`tests/`). Counts are public declarations (the two `private` lemmas are not counted).

### A.1 `ToCompPoly/Multilinear.lean` (generic: no protocol vocabulary; 43 public)

Load-bearing definitions, copied:

```lean
-- LeanerVM/Protocol/ToCompPoly/Multilinear.lean:144-149
def cubeIndex {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) : Fin (2 ^ (k + m)) :=
  ⟨i.val + 2 ^ k * j.val, by … ⟩            -- (proof of the bound elided here, 4 lines)
-- :170-171
def cubeSplit (k m : ℕ) : Fin (2 ^ k) × Fin (2 ^ m) ≃ Fin (2 ^ (k + m)) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (by rw [pow_add, mul_comm])))
-- :235-236
def boolVec {m : ℕ} (j : Fin (2 ^ m)) : Vector R m :=
  Vector.ofFn fun b ↦ if j.val.testBit b then 1 else 0
-- :307-309
def slice {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (j : Fin (2 ^ m)) :
    CMlPolynomialEval R k :=
  Vector.ofFn fun i ↦ t[cubeIndex i j]
```

In words: `cubeIndex i j` is the index with low bits `i` and high bits `j`; `cubeSplit` is the same
map as an equivalence (`cubeSplit_apply` proves it equals `cubeIndex`); `boolVec j` is the cube
point of index `j` (coordinate `b` is bit `b`); `slice t j` is the subtable of `t` whose high `m`
bits are `j` (an aligned block).

| Line | Declaration | Class | Meaning |
| --- | --- | --- | --- |
| 67 | `sumCube t` | I | `Σ_i t[i]` |
| 70 | `hadamard s t` | I (listed) | pointwise product |
| 73 | `hadamard_getElem` | H | entry of the product |
| 78 | `lagrangeBasis_getElem_nat` | H | `lagrangeBasis_getElem` with a `ℕ` index |
| 85 | `evalMle_eq_sum` | H | `evalMle t x = Σ_i t[i]·(lagrangeBasis x)[i]` |
| 91 | `evalMle_eq_sumCube_hadamard` | I (listed) | same, as `sumCube (hadamard …)` |
| 97, 103 | `evalMle_cast`, `eval₂Mle_cast` | H | evaluation invariant under a cast of `n` (used by `PublicInput`) |
| 125 | `sumCube_lagrangeBasis` | H | partition of unity |
| 131 | `evalMle_replicate` | H | a constant table extends to the constant |
| 144 | `cubeIndex` | L | above |
| 151-164 | `cubeIndex_val`, `cubeIndex_div`, `cubeIndex_mod`, `testBit_cubeIndex` | H | arithmetic of `cubeIndex` |
| 170, 173 | `cubeSplit`, `cubeSplit_apply` | L, H | above |
| 179 | `sum_cube_split` | H | a cube sum is a double sum, high outside |
| 185, 189 | `lowVec`, `highVec` | I | low `k` / high `m` coordinates of a point (inside `lowPoint`, `highPoint`) |
| 193-208 | `lowVec_append`, `highVec_append`, `lowVec_append_highVec` | H | split and join are inverse |
| 220 | `lagrangeBasis_cubeIndex` | H | the basis factors across the index split |
| 235 | `boolVec` | L | above |
| 239 | `onesIndex m` | I | the index `2^m − 1` (used by `padHigh`) |
| 243 | `boolVec_zero` | I | `boolVec 0 = (0,…,0)` (used by `PublicInput`) |
| 250 | `boolVec_onesIndex` | H | `boolVec (2^m−1) = (1,…,1)` |
| 257 | `fin_eq_iff_testBit` | H | indices equal iff low bits equal |
| 269 | `lagrangeBasis_boolVec` | H | basis at a cube point is an indicator |
| 285, 292 | `lagrangeBasis_onesIndex`, `lagrangeBasis_zero_index` | H | basis at the two corners |
| 298 | `evalMle_boolVec` | H | the extension at a cube point reads the entry |
| 307 | `slice` | L | above |
| 312-323 | `slice_getElem`, `cubeIndex_lt`, `slice_getElem_nat` | H | entries of a slice |
| 331 | `evalMle_split` | H | `evalMle t (z ++ s) = Σ_j (lagrangeBasis s)[j]·evalMle (slice t j) z` |
| 342 | `evalMle_append_boolVec` | I (listed; used by `PublicInput`) | a Boolean high part selects a slice |
| 351 | `placeSlice t j` | I (listed) | `t` on the slice `j`, zero elsewhere (`padHigh`, `windowTable`) |
| 357 | `slice_placeSlice` | H | slicing a placed table |
| 371 | `evalMle_placeSlice` | I (listed) | extension of a placed table = `(lagrangeBasis s)[j]·t̃(z)` |
| 381 | `sumCube_placeSlice` | H | placing keeps the cube sum |

### A.2 `ToCompPoly/BitProductTable.lean` (generic; 13 public)

```lean
-- LeanerVM/Protocol/ToCompPoly/BitProductTable.lean:127-128
def powersTable (a : R) (n : ℕ) : CMlPolynomialEval R n :=
  Vector.ofFn fun i ↦ a ^ i.val
```

| Line | Declaration | Class | Meaning |
| --- | --- | --- | --- |
| 44 | `bitProductTable f` | I (listed) | entry `i` is `∏_k f k (bit k of i)` |
| 47, 51 | `bitProductTable_getElem`, `map_bitProductTable` | H | entries; commutes with a ring map |
| 58 | `evalMle_bitProductTable` | I (listed) | extension `= ∏_k ((1 − x_k) f k false + x_k f k true)` |
| 86 | `eval₂Mle_bitProductTable` | H | same at a point of another ring |
| 93 | `lagrangeBasis_eq_bitProductTable` | H | the Lagrange basis is such a table |
| 100 | `pow_eq_prod_testBit` | H | `a^i = ∏_k (a^{2^k})^{bit k of i}` |
| 127 | `powersTable a n` | L (inside `idxColumn`) | entry `i` is `a^i` |
| 130, 137 | `powersTable_eq_bitProductTable`, `map_powersTable` | H | |
| 144 | `evalMle_powersTable` | I (listed) | extension `= ∏_k ((1 − x_k) + x_k a^{2^k})` |
| 149 | `eval₂Mle_powersTable` | H (proof of `idxColumn_eval`) | same at a point of another ring |
| 156 | `evalMle_lagrangeBasis` | I (field `mle_eq` of `eqWeight`) | the extension of `lagrangeBasis w` at `x` is `∏_k ((1−x_k)(1−w_k) + x_k w_k)` |

### A.3 `ToCompPoly/Stacking.lean` (generic; 38 public)

```lean
-- LeanerVM/Protocol/ToCompPoly/Stacking.lean:62-68
structure Blocks where
  /-- The number of blocks. -/
  n : ℕ
  /-- The number of variables of each block; its height is `2 ^ size b`. -/
  size : Fin n → ℕ
  /-- Largest first. -/
  descending : Antitone size
-- :80-87
def offsetNat (k : ℕ) : ℕ :=
  ∑ c ∈ Finset.range k, if h : c < B.n then 2 ^ B.size ⟨c, h⟩ else 0
def offset (b : Fin B.n) : ℕ := B.offsetNat b.val
def total : ℕ := B.offsetNat B.n
-- :159-163
def stackAt (t : B.Tables R) (μ : ℕ) (pad : R) : CMlPolynomialEval R μ :=
  Vector.ofFn fun x ↦
    if B.total ≤ x.val then pad
    else ∑ b : Fin B.n,
      if B.InWindow b x.val then ((t b)[x.val - B.offset b]?).getD 0 else 0
-- :213-214 (bound proof elided, 6 lines)
def selector {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) : Fin (2 ^ (μ - B.size b)) :=
  ⟨B.offset b / 2 ^ B.size b, by … ⟩
-- :227-230
def extendPoint {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (z : Vector R (B.size b)) :
    Vector R μ :=
  Vector.cast (Nat.add_sub_cancel' (B.size_le hμ b))
    (z ++ (boolVec (B.selector hμ b) : Vector R (μ - B.size b)))
-- :264-267
def unstack {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (q : CMlPolynomialEval R μ)
    (b : Fin B.n) : CMlPolynomialEval R (B.size b) :=
  slice (Vector.cast (congrArg (2 ^ ·) (Nat.add_sub_cancel' (B.size_le hμ b)).symm) q)
    (B.selector hμ b)
```

In words: a `Blocks` is a list of sizes, non-increasing; block `b` starts at `offset b`, the sum of
the heights before it; `total` is the sum of all heights; `stackAt` lays given tables end to end and
fills the rest with `pad`; `selector b = offset b / 2^size b`; `extendPoint b z = (z, bits of
selector b)`; `unstack q b` reads block `b`'s window off any table `q`.

| Line | Declaration | Class | Meaning |
| --- | --- | --- | --- |
| 62 | `Blocks` | L | above |
| 75 | `Blocks.Tables R` | I (listed) | one table per block |
| 80, 84, 87 | `offsetNat`, `offset`, `total` | L | above |
| 89, 93 | `offsetNat_succ`, `offsetNat_mono` | H | |
| 97, 103 | `offset_add_pow_le_offset`, `offset_add_pow_le_total` | H | windows disjoint, in order, inside the total |
| 109 | `pow_size_dvd_offset` | I (sketch) | alignment: `2^size b ∣ offset b` |
| 118 | `InWindow b x` | H | `offset b ≤ x < offset b + 2^size b` |
| 121, 129, 147 | `inWindow_unique`, `exists_inWindow`, `inWindow_iff_div` | H | one window per index; no gaps below `total`; window = quotient |
| 159 | `stackAt` | I (listed; the honest prover's stack) | above |
| 165, 176 | `stackAt_getElem_of_inWindow`, `stackAt_getElem_of_total_le` | H | the cells of the stack |
| 182, 197 | `map_stackAt`, `stackAt_eq_of_total_eq` | H | commutes with ring maps; a full stack ignores the pad |
| 206 | `size_le` | H | every block fits in `μ` variables |
| 213, 222 | `selector`, `selector_val` | L, H | above |
| 227 | `extendPoint` | L | above |
| 233, 238 | `lowPoint`, `highPoint` | I | the low `size b` / high `μ − size b` coordinates of a stack point |
| 244-255 | `cast_lowPoint_append_highPoint`, `lowPoint_extendPoint`, `highPoint_extendPoint` | H | |
| 264 | `unstack` | L | above |
| 271 | `unstack_getElem` | I (the cell meaning of the reader) | `(unstack q b)[i] = q[i + offset b]` |
| 280 | `unstack_stackAt` | I | reading the stack returns the table |
| 292, 304 | `unstack_map`, `unstack_eq_of_window_eq` | H | |
| 319 | `unstack_eval` | H | selection identity, one ring |
| 330 | `unstack_eval₂` | I (listed) | `eval₂Mle q φ (extendPoint b z) = eval₂Mle (unstack q b) φ z`, every `q` |
| 339, 345 | `stack_eval`, `stack_eval₂` | I (listed) | the same on the stack, any pad |
| 352 | `unstack_eval₂_eq_sumCube` | H (only `BlockClaims` uses it) | the identity as a cube sum |

### A.4 `ToCompPoly/AmbientStacking.lean` (generic; 10 public)

```lean
-- LeanerVM/Protocol/ToCompPoly/AmbientStacking.lean:69-70
def selectorWeight {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (z : Vector R μ) : R :=
  (lagrangeBasis (B.highPoint hμ b z))[B.selector hμ b]
```

`selectorWeight b z = eq(sel_b, z_hi)`, the weight of block `b` at a stack point.

| Line | Declaration | Class | Meaning |
| --- | --- | --- | --- |
| 69 | `selectorWeight` | I (in `stack_eval_ambient`; L once a verifier computes `eq(sel_b, ζ_hi)` with it) | above |
| 73 | `selectorWeight_extendPoint_self` | H | weight 1 at a lifted point of the block |
| 80, 86, 102 | `windowTable`, `windowTable_getElem`, `evalMle_windowTable` | H | a table placed in one window |
| 111 | `stackAt_decomposition` | H | stack = pad + Σ windows of (block − pad) |
| 134 | `stack_eval_ambient` | I (listed) | the stack at any point (below, B.3) |
| 159 | `stack_eval_ambient_zero` | H | pad 0 |
| 166 | `sum_selectorWeight_of_total_eq` | H | a full layout's weights sum to 1 |
| 178 | `stack_eval₂_ambient` | H (used by `Stack.lean`) | at a point of another ring |

### A.5 `Stack.lean` (leanVM's: specialises to `K`, `E`, the spine's `Column` and `Layout`; 9 public)

```lean
-- LeanerVM/Protocol/Stack.lean:52-59
def Layout.comap {μ : ℕ} {ι ι' : Type} {κ : ι → ℕ} {κ' : ι' → ℕ} (L : Layout μ ι κ)
    (f : ι' → ι) (h : ∀ c, κ (f c) = κ' c) : Layout μ ι' κ' where
  read := fun q c ↦ ⟨Vector.cast (congrArg (2 ^ ·) (h c)) (L.read q (f c)).values⟩
  extend := fun c z ↦ L.extend (f c) (Vector.cast (h c).symm z)
  read_eval := fun q c z ↦ by … (3 lines)
-- :70, :73-74
def stackColumn (t : B.Tables K) (μ : ℕ) : Column μ := ⟨B.stackAt t μ 0⟩
def readColumn (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n) : Column (B.size b) :=
  ⟨B.unstack hμ q.values b⟩
-- :97-100
def layout (hμ : B.total ≤ 2 ^ μ) : Layout μ (Fin B.n) B.size where
  read := B.readColumn hμ
  extend := B.extendPoint hμ
  read_eval := B.readColumn_eval hμ
```

| Line | Declaration | Class | Meaning |
| --- | --- | --- | --- |
| 52 | `Layout.comap L f h` | L | column `c` of the new layout is column `f c` of `L` |
| 70 | `Blocks.stackColumn` | I (listed; `stackOf`) | the witness stack, pad 0 |
| 73 | `Blocks.readColumn` | L | block `b` of a column |
| 78 | `Blocks.readColumn_eval` | I (listed) | the reading law, every `q` |
| 85 | `Blocks.readColumn_stackColumn` | I | reading the honest stack returns the block |
| 90 | `Blocks.stackColumn_eval` | H | the honest stack at a lifted point |
| 97 | `Blocks.layout` | L | the aligned blocks as a `Layout` |
| 104 | `Blocks.stackColumn_eval_ambient` | I (not listed) | the zero-padded stack at any point |
| 118 | `Blocks.stack_eval_ambient_one` | I (listed; the leaf decomposition of Layer 6) | the one-padded stack at any point, char. 2 form |

### A.6 `Padding.lean` (leanVM's: the protocol's choice of slice, over any ring; 6 public)

```lean
-- LeanerVM/Protocol/Padding.lean:43-44, 60-61
def prodVars (m : ℕ) : CMlPolynomialEval R m :=
  Vector.ofFn fun i ↦ if i = onesIndex m then 1 else 0
def padHigh {k : ℕ} (t : CMlPolynomialEval R k) (m : ℕ) : CMlPolynomialEval R (k + m) :=
  placeSlice t (onesIndex m)
```

| Line | Declaration | Class | Meaning |
| --- | --- | --- | --- |
| 43 | `prodVars m` | I (listed) | the table of `x_0 ⋯ x_{m−1}` |
| 47 | `sumCube_prodVars` | I (listed; acceptance test 7) | `Σ_x x_0⋯x_{m−1} = 1` |
| 51 | `evalMle_prodVars` | H | its extension is `∏ s_b` |
| 60 | `padHigh t m` | I (listed) | `t` lifted by the product of `m` new high variables |
| 64 | `sumCube_padHigh` | I (listed) | keeps the cube sum (completeness of the table sumcheck) |
| 70 | `evalMle_padHigh` | I (**not listed**; the verifier's final check needs it) | extension `= t̃(z)·∏_b s_b` |

### A.7 `ClaimWeights.lean` (leanVM's: over an abstract instance; 4 public)

```lean
-- LeanerVM/Protocol/ClaimWeights.lean:45-48
def eqWeight {μ : ℕ} (p : Vector E μ) : Weight μ where
  onCube := lagrangeBasis p
  mle := fun r ↦ ∏ k : Fin μ, ((1 - r[k]) * (1 - p[k]) + r[k] * p[k])
  mle_eq := fun r ↦ (evalMle_lagrangeBasis p r).symm
```

| Line | Declaration | Class | Meaning |
| --- | --- | --- | --- |
| 34 | `Weight.pair_eq_sumCube` | H | the pairing as `sumCube (hadamard …)` |
| 45 | `eqWeight p` | L (the opening phase's weights; the verifier runs `mle`) | the weight `eq(p, ·)` |
| 51 | `eqWeight_pair` | H | pairing `eq(p, ·)` with `q` is `q̃(p)` |
| 58 | `ColumnClaim.holds_iff_weighted` | I (listed; the opening phase) | a column claim is the weighted claim with weight `eq(extend c z, ·)` |

### A.8 `BlockClaims.lean` (generic content, placed in the leanVM half; 8 public; no consumer)

| Line | Declaration | Class | Meaning |
| --- | --- | --- | --- |
| 54 | `BlockClaim B S` | H (unused) | (block, point, value) |
| 69, 73 | `ambientPoint`, `weight` | H (unused) | the lifted point; `lagrangeBasis` of it |
| 78 | `IsValid φ hμ q` | H (unused) | `eval₂Mle (unstack q block) φ point = value` |
| 83, 90 | `pairing_eq`, `isValid_iff_pairing` | H (unused) | `unstack_eval₂_eq_sumCube` restated |
| 101, 113 | `isValid_iff_of_map_window_eq`, `isValid_iff_of_window_eq` | H (unused) | locality: only the window matters |

`git grep -w BlockClaim b435631 -- LeanerVM tests` finds `BlockClaims.lean` and its test only.

### A.9 `FixedColumns.lean` (leanVM's; imports the arithmetization; 12 public)

```lean
-- LeanerVM/Protocol/FixedColumns.lean:48, 56-57
def idxColumn (κ : ℕ) : Column κ := ⟨powersTable g κ⟩
def idxColumnEval {κ : ℕ} (z : Vector E κ) : E :=
  ∏ j : Fin κ, ((1 - z[j]) + z[j] * algebraMap K E (g ^ (2 ^ j.val)))
-- :79-82
def bytecodeColumn (prog : Program) : Column (prog.logSize + 4) :=
  ⟨Vector.ofFn fun i ↦
    let p := (cubeSplit prog.logSize 4).symm i
    (encodeSlots (prog.code p.1))[p.2]⟩
-- :108-111
def bytecodeColumnEval (prog : Program) (z : Vector E prog.logSize) (w : Vector E 4) : E :=
  ∑ s : Fin 16, (lagrangeBasis w)[s] *
    ∑ i : Fin (2 ^ prog.logSize),
      algebraMap K E ((encodeSlots (prog.code i))[s]) * (lagrangeBasis z)[i]
-- LeanerVM/Arithmetization/Bytecode.lean:94-96 (what bytecodeColumn puts in a cell)
def encodeSlots (i : Instr) : Vector K 16 :=
  let e := entry i
  #v[0, 0, 0, e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], 0, 0, 0, 0, 0]
```

| Line | Declaration | Class | Meaning |
| --- | --- | --- | --- |
| 48 | `idxColumn κ` | L (a `Coord.known` column of the instance) | cell `i` holds `g^i` |
| 51 | `idxColumn_get` | H | the cells |
| 56 | `idxColumnEval` | L (the verifier) | `∏_j ((1 − z_j) + z_j g^{2^j})` |
| 60 | `idxColumn_eval` | I (listed) | the oracle's answer is `idxColumnEval` |
| 66 | `idxColumnEval_eq` | I (listed) | the specification's form `∏ (1 + z_k(1 + g^{2^k}))` |
| 75 | `bytecodeSlotColumn prog s` | H | slot `s` of every instruction |
| 79 | `bytecodeColumn prog` | L (a `Coord.known` column; the verifier) | cell `i + 2^κ·s` holds slot `s` of instruction `i` |
| 85 | `bytecodeColumn_slot` | H (restates the definition; section C) | |
| 90 | `slice_bytecodeColumn` | H | slice `s` is `bytecodeSlotColumn s` |
| 97 | `bytecodeColumn_answer_boolVec` | I (listed) | at the cube point `(bits of i, bits of s)` the oracle answers slot `s` of instruction `i` |
| 108 | `bytecodeColumnEval` | L (the verifier) | `Σ_s eq(w, s) Σ_i slot_s(i) eq(z, i)` |
| 114 | `bytecodeColumn_eval` | I (listed) | the oracle's answer at `z ++ w` is `bytecodeColumnEval prog z w` |

**Tally.** 143 public declarations: load-bearing 20 (`cubeIndex`, `cubeSplit`, `boolVec`, `slice`,
`powersTable`, `Blocks`, `offsetNat`, `offset`, `total`, `selector`, `extendPoint`, `unstack`,
`Layout.comap`, `readColumn`, `layout`, `eqWeight`, `idxColumn`, `idxColumnEval`,
`bytecodeColumn`, `bytecodeColumnEval`); interface 41; helper 82 (of which 8 in
`BlockClaims.lean`, unused). Per module (L / I / H): Multilinear 4 / 10 / 29, BitProductTable
1 / 4 / 8, Stacking 7 / 10 / 21, AmbientStacking 0 / 2 / 8, Stack 3 / 5 / 1, Padding 0 / 5 / 1,
ClaimWeights 1 / 1 / 2, BlockClaims 0 / 0 / 8, FixedColumns 4 / 4 / 4. Generic modules: the four under `ToCompPoly/` (104 declarations);
`BlockClaims.lean` is generic in content too (any `Blocks`, any rings) but sits in the leanVM half.

## B. Faithfulness to leanVM at the pin

Citations: `04:`, `05:`, `06:`, `08:` are `doc/leanvm/body/0N-*.tex`; `py:` is
`python-verifier/verifier.py`; Rust paths are under `crates/`. The probes named here are
reproduced in full, with their outputs, in section I.

### B.1 The bit order of the cube and of points: agree

- CompPoly: "The indexing is **little-endian** (i.e. the least significant bit is the first
  bit)" (`Multilinear/Basic.lean:45` at `3468b38c`); `evalMle` folds `x.head` first on the pairs
  `(2i, 2i+1)`.
- Rust: "Truth tables are indexed little-endian (variable `k` is bit `k`)"
  (`primitives/src/multilinear.rs:2-4`); `mle_eval` folds `point[0]` on the pairs
  `table[2 * i], table[2 * i + 1]` (`multilinear.rs:109-114, 271-277`).
- Python: `cur = [cur[2 * i] * (ONE + r) + cur[2 * i + 1] * r …]` for `r in point`
  (`py:240-245`).
- Stack points: Layer 1's `extendPoint b z = z ++ boolVec (selector b)` puts the block's point in
  the low coordinates and the selector's bits, low bit first, in the high ones. Rust:
  `zeta_lo = &zeta[..kappa]`, `sel_bits … ((sel >> k) & 1)` (`lean_vm/src/leaf.rs:405-410`);
  Python `stack_point` and `_selector_point` (`py:295-297, 314-315`); specification
  `q̃(z, sel_i)` (`04:10-12`). The probe `ValuesProbe` checks the lifted point of a claim on block
  1 against `Placement.stack_point`: `#v[E.ofLimbs 3 1 0, 0, 1]` both ways.
- Existing tests that would fail on the opposite order: `Stacking.lean` (tests) `:64-66`
  (`extendPoint … = #v[13, 0, 1]`) and `:79-80` (reversed selector bits give another value);
  `BitProductTable.lean` (tests) `:43-44` (coordinates swapped).

### B.2 Stacking: the offsets agree; the order of equal sizes is supplied by nobody in Layer 1

`Blocks` asks only `Antitone size` (`Stacking.lean:62-68`); alignment is then a theorem
(`pow_size_dvd_offset`, `:109`). leanVM orders the committed columns by size, largest first,
**ties by column index**, with the six shared columns first (`lean_vm/src/witness.rs:63-79`,
`order.sort_by(|&a, &b| kappas[b].unwrap().cmp(&kappas[a].unwrap()).then(a.cmp(&b)))`;
`py:305-311`, `sorted(enumerate(sizes), key=lambda item: (-item[1], item[0]))`;
`lean_vm/src/cpu/layout.rs:13-26`; dossier `gt-bus.md` A.5, G7). The specification orders by
size and gives no rule for ties (`04:6`, "Order them by size, `κ_1 ≥ … ≥ κ_T` variables").

**Who supplies the order.** A `Blocks` is the *sorted* list of sizes; which column sits on which
block is the renaming `f` of `Layout.comap L f h` (`Stack.lean:52`), to be written by the adaptor
(Layer 3). No declaration of Layer 1 computes leanVM's order, and no statement or test pins it:
the tests use distinct sizes (2, 1, 0) or three equal sizes renamed by the identity
(`tests/LeanerVMTests/Protocol/Stack.lean:100-109`). The blueprint states the order as a
convention (`protocol-blueprint.md:322`) and assigns the transcription to Layer 3 (`:865-866`,
"every offset is a `decide`").

**What `OffsetsProbe` shows** (Lean, exit 0; `offsets.py` gives the reference numbers by calling
the pinned `verifier.stack_offsets` and `verifier.build_layout` and a transcription of the Rust
`stack_offsets`, which agree):

- Small configuration, sizes in column-index order `[4, 4, 4, 4, 2, 5, 4, 4]`
  (`mem_0, mem_1, mem_2, cntfin_mem, cntfin_bc, q_flock, table a, table b`): leanVM's offsets per
  column are `[32, 48, 64, 80, 128, 0, 96, 112]`. `Blocks.offset` on the sorted sizes
  `[5, 4, 4, 4, 4, 4, 4, 2]` gives `[0, 32, 48, 64, 80, 96, 112, 128]` and selectors
  `[0, 2, 3, 4, 5, 6, 7, 32]`; mapped back through leanVM's order they are leanVM's offsets.
- The near miss: the order with the tables' columns first sorts to **the same `Blocks`**, and
  through it `mem_0` sits at 64 instead of 32 (`#guard … = [64, 80, 96, 112, 128, 0, 32, 48]`,
  `≠ stackOffsets small`). Every theorem of Layer 1 holds of both.
- The pinned verifier's real layout for `log_memory = 16`, `taus = (3, 16, 0, 5, 16, 3)`,
  `κ_bc = 4`: 110 columns, 92 committed blocks, 18 strided limb columns, `stack_log = 22`. The
  transcribed order equals the Python's column order block by block, and `Blocks.offset` on the
  92 sorted sizes equals the Python's 92 offsets (`#guard offsetsOf realBlocks = pyOffsets`);
  `total = 2165512`, which fits `2^22` and not `2^21`.

So the arithmetic of `Blocks` is leanVM's; the tie order is a deferred obligation of the adaptor,
checked by nothing before the compiled verifier meets a Rust proof (finding G.3).

**Floors.** The Rust floors the witness stack at `MIN_MU = 15` (`witness.rs:97`,
`pcs.rs:49`), the Python at `MIN_STACKED_LOG = 15` and rejects `stack_log > 28`
(`py:890, 907-908, 1379`); the specification has `M = ⌈log₂ N⌉` with no floor (`04:10`). Layer 1
takes `μ` as a parameter with the one hypothesis `B.total ≤ 2 ^ μ`, so it admits the floored `μ`;
the floor is the instance's to choose (blueprint `:322`, `μ_stack ∈ [15, 28]`). Already recorded
as a disagreement in `gt-bus.md` A.5.

### B.3 Padding values and the ambient identity: agree

- Witness stack, pad `0`: `q = P_1 ‖ … ‖ P_T ‖ 0` (`04:8`); the Rust zeroes the tail
  (`witness.rs:122-133`). `Blocks.stackColumn t μ := ⟨B.stackAt t μ 0⟩` (`Stack.lean:70`).
- Leaf stacks, pad `1`: "padding to `2^μ` leaves with `1`s" (`05:103`). Equation (2):

  ```tex
  % doc/leanvm/body/05-arithmetization.tex:106-109
    \widetilde V_0(\zeta)\;=\;\sum_b \eq(\mathsf{sel}_b,\zeta^{b}_{\mathrm{hi}})\Bigl(\beta-\sum_{i}\eq(\alpha,i)\,\widetilde c_{b,i}(\zeta^{b}_{\mathrm{lo}})\Bigr)\;+\;\Bigl(1+\sum_b\eq(\mathsf{sel}_b,\zeta^{b}_{\mathrm{hi}})\Bigr).
  \end{equation}
  That last term is the padding's weight, for the final $\dots 1111$.
  ```

  Lean, for any tables over `E` (the leaves, once formed):

  ```lean
  -- LeanerVM/Protocol/Stack.lean:118-122
  theorem stack_eval_ambient_one (B : Blocks) (t : B.Tables E) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
      (ζ : Vector E μ) :
      evalMle (B.stackAt t μ 1) ζ =
        (∑ b : Fin B.n, B.selectorWeight hμ b ζ * evalMle (t b) (B.lowPoint hμ b ζ)) +
          (1 + ∑ b : Fin B.n, B.selectorWeight hμ b ζ) := by
  ```

  It is the characteristic-two reading of the general `stack_eval_ambient`
  (`AmbientStacking.lean:134-138`, `… + pad * (1 - ∑ b, B.selectorWeight hμ b z)`). Rust:
  `Ok(acc + (F192::ONE + sel_sum))` (`leaf.rs:459-460`); Python:
  `ones_padding = E.sum(framework_selectors + table_selectors) + ONE` (`py:589`).
- `ValuesProbe` (blocks of sizes 2, 1, 0 on three variables; `ζ` off the cube, outside `K`):
  Layer 1's `selectorWeight` equals the Python's `Placement.eq_above` block by block
  (`(3,2,2), (6,8,8), (2,26,30)`); the zero-padded stack at `ζ` is the covered part `(38,3,34)`;
  the one-padded stack is `(32,19,54)` = covered part + `(1 + Σ_b w_b)` = `(6,16,20)`, as the
  Python computes. Near misses: pad `0`, and the padding term read as the constant `1`, both give
  other values. The repository's tests already contain the second near miss
  (`tests/…/Stack.lean:155-156`) and the pad-dropped one (`tests/…/AmbientStacking.lean:90-92`).

What the identity leaves to Layer 6: that a leaf block's extension is
`β − Σ_i eq(α, i)·c̃_{b,i}(ζ_lo)` (linearity of the extension); and the order of the leaf blocks
(`gt-bus.md` G7), which Layer 1 does not carry for the leaf stacks either.

### B.4 Back-loaded padding: agree

Specification (`05:145-155`): table `j` is multiplied by `∏_{k=τ_j}^{τ_max−1} X_k`; "Since
`Σ_{x∈{0,1}^m} x_0⋯x_{m−1} = 1`, the padded variables contribute a factor 1"; "Rounds bind
`X_{τ_max−1}` first".

```lean
-- LeanerVM/Protocol/Padding.lean:60-61, 64-66, 70-72
def padHigh {k : ℕ} (t : CMlPolynomialEval R k) (m : ℕ) : CMlPolynomialEval R (k + m) :=
  placeSlice t (onesIndex m)
theorem sumCube_padHigh {k : ℕ} (t : CMlPolynomialEval R k) (m : ℕ) :
    sumCube (padHigh t m) = sumCube t :=
theorem evalMle_padHigh {k m : ℕ} (t : CMlPolynomialEval R k) (z : Vector R k)
    (s : Vector R m) :
    evalMle (padHigh t m) (z ++ s) = evalMle t z * ∏ b : Fin m, s[b] := by
```

The table sits on the low coordinates and the new variables are the high ones, as in the
specification. The verifier's side is `evalMle_padHigh`: the Rust's final weight multiplies
`eq_k` for a variable the table has and the bare challenge for one it lacks,

```rust
// crates/lean_vm/src/constraints.rs:263-274
    for j in 0..n {
        let m = n - 1 - j;
        …
        chi[m] = rk;
        …
        let eq_k = F192::ONE + zeta[m] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
        }
```

and the Python the same (`py:609-614`, `weights[index] *= equality if height > variable else
challenge`, with `point = list(reversed(challenges))`). Both store the challenges back in natural
coordinate order, which is the order of `z ++ s` in the Lean statement. `ValuesProbe`: the table
`[3, 5]` lifted by two variables is `[0, 0, 0, 0, 0, 0, 3, 5]`, its extension at `(7 | 11, 13)`
is `1935`, as `multilinear_eval` of that table in the Python; the front-loaded placement is
another table.

Two remarks. `prodVars`, `sumCube_prodVars`, `evalMle_prodVars` (`Padding.lean:43-56`) are used
by no proof (`padHigh` is `placeSlice`, and `sumCube_padHigh` is `sumCube_placeSlice`); only the
tests and acceptance test 7's text name them. And `evalMle_padHigh`, the one the verifier's final
check needs, is absent from the blueprint's Layer 1 sketch and interface list (finding G.6).

### B.5 The index column: agree (generator `g = x`, coordinate `k` carries `g^{2^k}`)

Specification (`06:97-100`): the column holds `g^0, …, g^{2^κ−1}`, and
`ĩdx(ζ) = ∏_{k=0}^{κ−1}(1 + ζ_k(1 + g^{2^k}))`.

```lean
-- LeanerVM/Protocol/FixedColumns.lean:48, 56-57, 60-62, 66-67
def idxColumn (κ : ℕ) : Column κ := ⟨powersTable g κ⟩
def idxColumnEval {κ : ℕ} (z : Vector E κ) : E :=
  ∏ j : Fin κ, ((1 - z[j]) + z[j] * algebraMap K E (g ^ (2 ^ j.val)))
theorem idxColumn_eval {κ : ℕ} (z : Vector E κ) :
    OracleInterface.answer (idxColumn κ) z = idxColumnEval z :=
theorem idxColumnEval_eq {κ : ℕ} (z : Vector E κ) :
    idxColumnEval z = ∏ k : Fin κ, (1 + z[k] * (1 + algebraMap K E (g ^ (2 ^ k.val)))) := by
```

- Generator: `g : K := 0x2`, the word `x` (`Parameters/Generator.lean:43`); Rust
  `F64::G = F64(2)` (`primitives/src/field/gf2_64.rs:28`, cited there), Python `GEN = E(2)`
  (`py:182`).
- Exponent order: Rust `index_mle` starts `g2k = G` and squares after each coordinate, `zeta` in
  order (`primitives/src/field/mod.rs:105-113`); Python `index_mle`, "MLE of `[1, g, g^2, ...]` at
  an LSB-first point" (`py:271-278`). Coordinate `k` carries `g^{2^k}` in all three.
- Where it is evaluated: at `ζ_lo`, the first `κ_mem` or `κ_bc` coordinates (`leaf.rs:444`;
  `py:565-566`). Layer 1 states it for every `κ` and every point of `E^κ`.
- `ValuesProbe`: the oracle's answer on `idxColumn 4` at a four-coordinate `ζ`, and
  `idxColumnEval ζ`, both equal the Python's `index_mle(ζ)` `(950617, 874814, 877803)`, which the
  script also obtains as `multilinear_eval([g^0 … g^15], ζ)`; at two coordinates `(109, 29, 108)`;
  the cells are the words `2^i`.
- Cost: `g ^ (2 ^ j)` in CompPoly's `K` is binary exponentiation (`Pow BF64 ℕ := npowBinRec`,
  `Fields/Binary/BF64/Impl.lean:43-44, 169` at `3468b38c`), so the evaluator is `O(κ²)`
  multiplications, usable by an executable verifier.
- Existing near miss: `tests/…/FixedColumns.lean:46-47` (the high-bit-first product differs).

### B.6 The bytecode column: agree, cell for cell

Specification (`08:6-10, 25`): "lay instruction `z` out as 16 slots of `K`: the opcode in slot 3,
the operands and immediate lanes in slots 4, …, 10, and 0 everywhere else"; "read the resulting
`2^κ_bc × 16` table as `P`, the low `κ_bc` variables indexing the instruction and the high four
its slot, bits low first"; "So `P(z,1,1,0,0)` is instruction `z`'s opcode".

- **Layout.** `bytecodeColumn` puts slot `s` of instruction `i` at cell `i + 2^κ·s`
  (`(cubeSplit κ 4).symm`, low part the instruction; `FixedColumns.lean:79-82`). Rust:
  `table[(slot << kbc)..((slot + 1) << kbc)].copy_from_slice(vals)` with `slot =
  BYTECODE_PUBLIC_SLOT + i`, `BYTECODE_PUBLIC_SLOT = 3` (`leaf.rs:579, 596-602`); the claim point
  is `[&point[..kbc], alphas].concat()` (`leaf.rs:630`); Python
  `multilinear_eval(layout.bytecode, (*bytecode_low, *alphas))` (`py:566`).
- **Slots.** `encodeSlots i = [0, 0, 0, e_0, …, e_7, 0, 0, 0, 0, 0]` with `e = entry i`
  (`Arithmetization/Bytecode.lean:83-96`); `encodeSlots_getElem` (`:248-250`) proves the zeros.
  Against the Rust's eight columns `(opcode, o1, o2, o3, fpc, ffp, extra0, extra1)`
  (`lean_vm/src/cpu/layout.rs:229-309`), constructor by constructor: `XOR`, `MUL_NATIVE`, `JUMP`
  `(op, g^a, g^b, g^c, 0, 0, 0, 0)`; `SET_CONSTANT` `(op, g^o, k.c0, k.c1, k.c2, 0, 0, 0)`
  (`:257`, `:270`); `DEREF` `(op, g^o1, g^o2, g^o3, f_pc, f_fp, 0, 0)` with `Pc = (1, 0)`,
  `Fp = (0, 1)` (`cpu/isa.rs:69-74`); `BLAKE2S` `(op, g^ins0, g^ins1, g^ins2, g^ins3, g^cv, g^out,
  g^md)` (`:262`, `:269`, `:275`, `:281`, `:285`). Lean's `entry` has the same eight coordinates
  in the same order for every constructor, and `derefFlags` the same pairs
  (`Bytecode.lean:67-70`). Opcodes `g^0, …, g^5` in the order XOR, MUL, SET, DEREF, JUMP, BLAKE2S
  (`Parameters/Isa.lean:54-60`; `lean_vm/src/tables.rs:95-100`; `06:92`). Operands: Lean stores
  field elements where the Rust stores `g^a` for a `u32` exponent `a`; they agree whenever the
  Lean operand is a power of `g` (`Semantics/Instruction.lean:22-27` records the difference).
- **The last instruction and padding.** The Rust requires a power-of-two program
  (`crate::log2_strict_usize(prog.len())`, `cpu/layout.rs:322`); so does the Python
  (`log2_strict`, `py:857`). The compiler pads to `(total + 1).next_power_of_two()` with
  `Op::Set { o: 0, k: F192::ZERO }`, reserving the last cell for the halt sentinel
  (`lean_compiler/src/lib.rs:121-125, 161-162`), and `bytecode_columns` encodes that padding
  instruction like any other. Lean's `Program` has exactly `2 ^ logSize` instructions
  (`Instruction.lean:87-93`) and `bytecodeColumn` encodes every index, the last one included
  (`FixedColumns.lean:31`, "the column knows no sentinel"). A program whose length is not a power
  of two is not a `Program`; padding it is the compiler's business, outside the proof system.
- **`ValuesProbe`.** A sixteen-instruction program: XOR, MUL, SET with immediate limbs
  `(11, 12, 13)`, DEREF in each of the three modes, JUMP, BLAKE2S, then eight padding
  `SET [g^0] 0` (the last in the sentinel cell). All 256 cells of `bytecodeColumn` equal, as words,
  the table built by `values.py`'s line-by-line transcription of `bytecode_columns` and
  `stacked_bytecode_table`; the oracle's answer and `bytecodeColumnEval` at `(ζ, α)` both equal
  `(1219889995492, 3571792677380, 1279835512890)`, the pinned Python's `multilinear_eval` of that
  table at `(ζ, α)`, the evaluation `py:566` makes; with `α` reversed both sides move to another
  value.
- **Caveat (unverified).** The reference table comes from a transcription of the Rust encoder in
  Python (checked above line by line against `layout.rs:229-309`), not from running the Rust; the
  Python verifier has no encoder (it reads the table from a file). Running `bytecode_table` on the
  same program in the pinned Rust would verify it.
- **The Rust and the Python evaluate the program's share differently** (eight columns one by
  one, weighted by `eq(α, i)`, `leaf.rs:453-455`; the stacked table once at `(ζ, α)`, `py:566`).
  They agree when slots 0-2 and 11-15 are zero (`gt-bus.md` G15), which `encodeSlots_getElem`
  guarantees for Lean's column.

### B.7 A column claim as a weighted claim: agree

Specification: `P̃_i(ζ) = c` is "a weighted sum over `q̃` with weight
`W(w) = eq((ζ, sel_i), w)`" (`04:14-18`); at the opening, "Each pooled claim … via the stacking
selectors … becomes a weighted sum `Σ_w W_j(w) q̃(w) = c_j`" (`08:97`).

```lean
-- LeanerVM/Protocol/ClaimWeights.lean:58-60
theorem ColumnClaim.holds_iff_weighted {I : M3Instance} (q : Column I.μ) (c : ColumnClaim I) :
    c.Holds q ↔
      WeightedClaim.Holds q ⟨eqWeight (I.layout.extend c.col c.point), c.value⟩ := by
```

For the aligned layout `extend c z = (z, sel_c)`, the specification's weight. Python:
`on_stack` returns `(lambda x: eq_eval(point, x), self.value)` with `point` the stacked point
(`py:520-522`), `eq_eval = ∏ (1 + x + y)` (`py:257-261`), the characteristic-two form of
`eqWeight.mle` (`∏ ((1 − r)(1 − p) + r p)`). The theorem holds for every instance's layout, so it
serves the strided limb claims as well, once the layout's `extend` gives them the point
`(slot bits, z, sel_{q_flock})`. `ValuesProbe`: on a stack no honest prover commits, the pairing
of `eqWeight` of block 1's lifted point with the stack is `(6, 1, 0)`, which is block 1 (`[5, 4]`)
at the point and the Python's `dot(stack, eq_kernel(lifted))`; `eqWeight.mle` at a further point
equals the Python's `eq_eval(lifted, r)` `(9, 18, 0)`; the lifted point with its selector bits
reversed weighs other cells.

### B.8 The strided reader: absent

Layer 1 reads only aligned blocks: `slice`, `evalMle_append_boolVec`, `unstack` select on the
**high** index. Its own docstring says so: "`evalMle_append_boolVec` reads the slice at the
*high* index; slicing on the low index is a different, strided selection"
(`ToCompPoly/Multilinear.lean:50-51`).

leanVM reads the eighteen BLAKE2S limb columns as strided slots of `q_flock`:

```rust
// crates/pcs/src/stack_open.rs:84-97
    /// A boolean-selector claim on a packed column: the low `stride_log`
    /// in-block coords are frozen to `slot`'s bits (so the weight is nonzero
    /// only at `offset + slot + j * 2^stride_log`) and `point` is the high
    /// part. Equivalent to a `Point` with `low_point = slot_bits ++ point`,
    …
    Strided {
        offset: usize,
        slot: usize,
        stride_log: usize,
        point: Vec<F192>,
        value: F192,
    },
```

with the Python's `Placement(kappa, offsets[QFLOCK] + limbs[column], QFLOCK_SLOT_BITS)`
(`py:884-894`, `low = 8`), the slot map `SLOTS` (`lean_vm/src/hash_flock.rs:87-115`) and
`gt-flock-ring.md` 2.4 and 5.4. The specification states the routing only (`08:77`).

No form of the low-index selection is in Layer 1 (no `sliceLow`, no lemma for
`evalMle t (boolVec i ++ s)`). `StridedProbe` states and proves the generic identity in twenty
lines from Layer 1's own lemmas:

```lean
theorem evalMle_boolVec_append {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (i : Fin (2 ^ k))
    (s : Vector R m) :
    evalMle t ((boolVec i : Vector R k) ++ s) = evalMle (sliceLow t i) s
```

and checks it on an eight-cell table (slot 1 of four reads cells 1 and 5; the aligned slice at
high index 1 reads cells 2 and 3). A limb column `c` would then be read as
`sliceLow (unstack q b_flock) (slot c)` with `extend c z = extendPoint b_flock (boolVec (slot c)
++ z)`, its `read_eval` following from `evalMle_boolVec_append` and `unstack_eval₂`. Two further
pieces are missing for the instance's single `layout` over all `ColumnId`s: `Layout.comap` cannot
place a limb column (its height `2^τ_B` is no block's, `q_flock`'s block has `τ_B + 8` variables),
so a combinator that takes the aligned reader on some columns and the strided reader on the others
is needed. The blueprint's Layer 3 acknowledges the second reader
(`protocol-blueprint.md:841-848`) but specifies neither the lemma nor the combinator, and assigns
the slot map to Layer 9's `FlockInterface.limbColumns` (the cycle of `gt-flock-ring.md` 8.2).
Finding G.1.

## C. Do the statements say what they claim, and are they non-vacuous?

### C.1 Hypotheses

Layer 1 has two hypotheses in all: `descending : Antitone size` (a field of `Blocks`) and
`hμ : B.total ≤ 2 ^ μ`. Both are inhabited by the intended objects (tests: sizes `2, 1, 0` on three
variables, sizes `1, 0, 0` filling two, three equal sizes, the empty `Blocks`; `OffsetsProbe`: the
92 blocks of a real announcement with `μ = 22`) and refuted by the near misses (sizes `0, 1, 2`,
`tests/…/Stack.lean:84-85`; `¬ blocks.total ≤ 2 ^ 0`, `tests/…/Stacking.lean:121`). Neither
makes a statement trivial. The one total definition with a junk regime is `stackAt`: when
`B.total > 2 ^ μ` it truncates (`Stacking.lean:47-49` says so); every statement that needs the
fit takes `hμ`, and the two that do not (`map_stackAt`, `stackAt_eq_of_total_eq`) are true in the
junk regime too. Inside a window `stackAt` reads `((t b)[x - offset b]?).getD 0`, whose default is
never reached there (`stackAt_getElem_of_inWindow`).

### C.2 Every committed column, or only the honest stack?

The statements the extractor and the verifier need quantify over **every** column `q`:
`Blocks.unstack_eval₂` (`Stacking.lean:330-333`), `Blocks.unstack_getElem` (`:271-275`),
`Blocks.readColumn_eval` (`Stack.lean:78-81`), `ColumnClaim.holds_iff_weighted`
(`ClaimWeights.lean:58-60`, any instance, any `q`). The statements about the honest stack only
are `stack_eval`, `stack_eval₂`, `stackColumn_eval`, `readColumn_stackColumn`,
`stackColumn_eval_ambient`, and `stack_eval_ambient(_one)`. The last is about `stackAt t`
for arbitrary tables `t`; the GKR leaf vector *is* such a stack of tables computed from the
committed columns, so it holds for a dishonest prover's leaves too. `stackColumn_eval_ambient`
(the witness stack at an arbitrary point) is false for a committed `q` with nonzero cells past the
last block; no consumer exists or is planned (it is not in the interface list), and leanVM's
opening never needs it (its weights `eq((z, sel), ·)` vanish on the cube outside the block's
window).

One limit of the reading law, already observed by the earlier review and confirmed here: the
`Layout` law `read_eval` holds for a reader that reads *any* aligned slice `j` together with
`extend c z = (z, bits of j)`. What ties the reader to where the honest prover puts the block is
`readColumn_stackColumn` / `unstack_stackAt` (reading the honest stack returns the table), which
the adaptor's round trip `witnessOf_stackOf` will use. So the layout's faithfulness rests on the
adaptor's round trip plus the offsets, not on `read_eval`.

### C.3 Tautologies and restatements

- **`bytecodeColumn_slot` is still there** (`FixedColumns.lean:84-87`):

  ```lean
  theorem bytecodeColumn_slot (prog : Program) (i : Fin (2 ^ prog.logSize)) (s : Fin 16) :
      (bytecodeColumn prog).values[cubeIndex (m := 4) i s] = (encodeSlots (prog.code i))[s] := by
    simp [bytecodeColumn, ← cubeSplit_apply]
  ```

  It unfolds the definition. Its statement is not empty (through `cubeIndex_val`, a reader can
  see that cell `i + 2^κ·s` holds slot `s` of instruction `i`), but it adds nothing to reading
  `bytecodeColumn` itself, and `ValuesProbe`'s `wrongColumn_slot` shows the same proof script
  proves the analogous statement for the opposite layout. The earlier review's disposition
  ("A3 … Met: `bytecodeColumn_answer_boolVec` …") added the oracle-level theorem and kept this
  one. It is **still cited as the witness of acceptance test 14** (`protocol-blueprint.md:1306-1307`,
  "Witness: `bytecodeColumn_slot` on a two-instruction program") and in the status file's module
  table (`protocol-status.md:51`). The theorem that pins the order independently is
  `bytecodeColumn_answer_boolVec` (`FixedColumns.lean:97-101`), whose proof goes through
  `evalMle_append_boolVec` and `evalMle_boolVec`; the tests that pin it are the oracle `#guard`s
  at `tests/…/FixedColumns.lean:82-93` (slot bits `(1,1,0,0)` answer the opcode; reversed
  `(0,0,1,1)` answer `0`). Finding G.4.
- `BlockClaim.isValid_iff_pairing` and `pairing_eq` (`BlockClaims.lean:83-95`) restate
  `Blocks.unstack_eval₂_eq_sumCube` with the arguments named (the module says so,
  `BlockClaims.lean:31`). Finding G.7.
- Not tautologies, checked: `bytecodeColumn_eval` (its right side is written independently of the
  layout; with the opposite layout and `κ = 4` it is false); `idxColumn_eval` (the binary
  expansion); `ColumnClaim.holds_iff_weighted` (false with another column's selector,
  `tests/…/ClaimWeights.lean:41-43`); `stack_eval_ambient_one` (false with the constant `1` as
  padding term); `evalMle_padHigh` (false with one coordinate as factor).

### C.4 Aliasing through `Layout.comap`

`Layout.comap L f h` (`Stack.lean:52-59`) asks only that `f` keep heights. It does not ask `f` to
be injective. `ValuesProbe` builds `(blocks.layout _).comap (fun _ ↦ 0) _` on three columns, all
reading block 0 of an arbitrary stack. A layout that aliases two columns is a legal field of an
`M3Instance`; the adaptor's `witnessOf_stackOf` and `m3Holds_stackOf` would fail for it (the
honest stack cannot hold two different columns in one block), so completeness catches aliasing.
A bijective `f` that permutes equal-size blocks (the tie order, B.2) passes every Layer 1 and
Layer 3 theorem; only the compiled verifier against a Rust proof catches it.

### C.5 The tests: which would fail on a wrong definition

Near misses present and effective (each compares against an independently written value):
selection with the other high bit (`tests/…/Multilinear.lean:43-44`); placement on the other slot
(`:65-66`); swapped coordinates (`tests/…/BitProductTable.lean:43-44`); offsets and selectors
decided in the kernel (`tests/…/Stacking.lean:49-54`); the stack's cells (`:60-61`); lifted points
(`:64-66`); reversed selector bits (`:79-80`, `tests/…/Stack.lean:77-79`,
`tests/…/BlockClaims.lean:73-75`); small block first, no slice reads it (`tests/…/Stack.lean:91-95`);
the aligned layout against the toy's hand-written one, on the honest and an arbitrary stack
(`:113-120`), and `M3Holds` deciding the same (`:127-129`); padding term absent or constant
(`:155-156`); a full layout's weights against a gapped one (`tests/…/AmbientStacking.lean:61-65`);
pad dropped (`:90-92`); lifting by one coordinate, and the copied table
(`tests/…/Padding.lean:41-49`); another column's weight (`tests/…/ClaimWeights.lean:41-43`); the
index column's reversed exponent order (`tests/…/FixedColumns.lean:46-47`); reversed slot bits
at the oracle (`:85-88`) and in the evaluator (`:100-102`).

Tests that cannot fail independently of the theorem they cite (they instantiate it, so they
compile whenever the library does): the three `example … := bytecodeColumn_slot …`
(`tests/…/FixedColumns.lean:61-74`; the first two do check, by definitional unfolding, that slot 3
of `encodeSlots` is the opcode, which is a property of `encodeSlots`, not of the layout);
`example … := bytecodeColumn_eval …` (`:76-79`, `:115-117`);
`example … := (idxColumn_eval z).trans (idxColumnEval_eq z)` (`:49-51`);
`example … := blocks.stack_eval₂ …` (`tests/…/Stacking.lean:94-97`); the `map_stackAt`
examples (`:84-91`, `:123-125`, `:133-137`); `example … := sum_selectorWeight_of_total_eq …`
(`tests/…/AmbientStacking.lean:56-58`); `example … := c.isValid_iff_pairing …`
(`tests/…/BlockClaims.lean:77-81`). The `#guard`s that evaluate a proved identity on both sides
(`tests/…/Stack.lean:63-74`, `tests/…/ClaimWeights.lean:34-39`) check only that the compiled code
agrees with the kernel; the informative checks next to them are the mutations. No test compares
a definition with itself.

Coverage gap: the repository's bytecode-column tests use programs whose operands are all `1`
(`.xor 1 1 1`, `.mulNative 1 1 1`, `tests/…/FixedColumns.lean:56-59, 105-108`), so a swap of two
operand slots would pass them; the operand layout is covered by `entry`/`encodeSlots` tests on the
arithmetization side (`tests/LeanerVMTests/Arithmetization/Bytecode.lean:62-77`), which are
self-consistency checks against the author's reading. The only comparison with leanVM's own
encoder is `ValuesProbe` (B.6), which is not in the repository. Proposal in G.4.

## D. The wall and the To-folders

### D.1 Imports of the arithmetization, the semantics or Clean from the proof system

`git grep -n -E "^(public |meta )?import" b435631 -- LeanerVM/Protocol` (57 import lines), filtered
for `Arithmetization`, `Semantics`, `Clean`, `Parameters`:

```text
LeanerVM/Protocol/Basic.lean:3:public import LeanerVM.Arithmetization.Basic
LeanerVM/Protocol/Field.lean:10:public import LeanerVM.Parameters.Field
LeanerVM/Protocol/FixedColumns.lean:11:public import LeanerVM.Arithmetization.Bytecode
```

- `FixedColumns.lean` → `Arithmetization.Bytecode` (→ `Semantics.Instruction` →
  `Parameters.Isa`, `Semantics.Memory`): the documented exception of convention *The wall*
  (`protocol-blueprint.md:331`). `Bytecode.lean` imports no Clean. No module of
  `LeanerVM/Protocol` imports `FixedColumns` (`git grep -w bytecodeColumn b435631 -- LeanerVM`
  finds `FixedColumns.lean` only), so the wall holds for every phase.
- `Basic.lean` → `Arithmetization.Basic`: **an exception the blueprint does not list**. The
  module is an empty placeholder ("This layer will assemble upstream proof-system components
  around the verified arithmetization", `Protocol/Basic.lean:5-10`) that only `LeanerVM.lean`
  imports; `Arithmetization/Basic.lean` is itself empty and imports `Semantics.Basic`. It breaks
  nothing, but acceptance test 25's witness (`grep -rn 'import LeanerVM.Arithmetization'
  LeanerVM/Protocol` "lists the exceptions of convention *The wall* only", `:1341-1345`) is false
  as written: the grep lists it. Finding G.8.
- `Field.lean` → `Parameters.Field` (the fields `K`, `E`): below the semantics in the layer DAG,
  allowed.
- No file under `LeanerVM/Protocol` imports Clean or `LeanerVM.Semantics` directly.

### D.2 The `ToCompPoly` modules: generic, and what upstream already has

All four import only CompPoly, Mathlib and each other (`Multilinear.lean:11-12`,
`BitProductTable.lean:10`, `Stacking.lean:11`, `AmbientStacking.lean:19`), are stated over an
arbitrary commutative ring, and contain no protocol vocabulary: `git grep -i
"leanvm\|§\|protocol\|verifier\|prover\|witness\|bus\|algebraMap"` over the folder finds nothing
but the namespace `LeanerVM.Protocol`, which an upstream port renames. `BlockClaims.lean` is as
generic but sits in the leanVM half (and is unused, G.7).

What CompPoly already has (CompPoly's `Multilinear/` folder at the old pin `3468b38c` and at the
new pin `572f9973`, which is CompPoly `main` today; the clone at
`probes/lib-others/upstream/CompPoly-main` is at `572f997`):

| Layer 1 | CompPoly | Relation |
| --- | --- | --- |
| `evalMle_lagrangeBasis` (`BitProductTable.lean:156`) | `eqTilde_eq_prod` (`Multilinear/Basic.lean:600` at `3468b38c`, `:662` at `572f997`): `eqTilde w x = ∏ i, (w[i] * x[i] + (1 - w[i]) * (1 - x[i]))` with `eqTilde w x := eval (lagrangeBasis w) x` | the same statement, factors in another order (`DuplicatesProbe`, three-line proof) |
| `lagrangeBasis_cubeIndex` (`Multilinear.lean:220`) | `eqTilde_append` (`:632` / `:694`): `eqTilde (w₁ ++ w₂) (x₁ ++ x₂) = eqTilde w₁ x₁ * eqTilde w₂ x₂` | the extension-level form of the entry-level factorisation; neither implies the other directly |
| everything else (`sumCube`, `hadamard`, partition of unity, `slice`, `placeSlice`, `boolVec`, `cubeIndex`, bit-product and geometric tables, `Blocks` and stacking) | none | new |

Between the two pins CompPoly's `Multilinear/Basic.lean` gained `eval_add`, `eval_smul`,
`eval_zero`, `map_eval`, `map_monomialBasis`, `evalWithProducts(_eq_eval)`, and the new file
`Multilinear/Bytes.lean` (serialisation); none overlaps Layer 1.

ArkLib (`ArkLib/ToCompPoly/Multilinear/Basic.lean` at `dca90385` and `7653a901`: `eval_zero`,
`eval_eq_MvPolynomial_MLE`; `ArkLib/Data/`) has no stacking, slice or cube-sum lemma for
CompPoly tables; the `stack`/`unstack` of `ArkLib/Commitments/Functional/Hachi/RingSwitch/
Rlin.lean:162-191` (at `7653a901`) concern Hachi's quadratic-evaluation responses, another object.
ArkLib issue #900, which `Stacking.lean:33-34` and `AmbientStacking.lean:33-34` cite as the
request they answer, is open ("feat(data): formalize extension-ring block readout", read with
`gh issue view 900 -R Verified-zkEVM/ArkLib`).

Duplicates inside Layer 1 (`DuplicatesProbe`, each a one- to three-line proof): `unstack_eval` is
`unstack_eval₂` at the identity map; `stack_eval` is `unstack_eval` followed by `unstack_stackAt`;
`stack_eval_ambient_zero` is `stack_eval_ambient` at pad `0`. The probe also records that the
largest-first order is sufficient for alignment and not necessary (sizes `1, 1, 2` sit at offsets
`0, 2, 4`, all aligned, and are no `Blocks`), which bears on acceptance test 15 (G.5).

Mathlib equivalents (for an upstream reviewer, not defects): `sum_cube_split` is
`Fintype.sum_prod_type` through `finProdFinEquiv`; `fin_eq_iff_testBit` is
`Nat.eq_of_testBit_eq` restricted to `Fin (2 ^ m)`.

## E. The audit surface, measured

Method: every `def`, `abbrev`, `structure`, `theorem` outside a `private` modifier in the nine
files at `b435631` (all sit in `@[expose] public section`). "stmt" counts a theorem's lines up to
`:=` and a definition's lines in full (a trusted definition is read whole); "+doc" adds its
docstring. The script (`count2.py`, section I.7) reads the files with `git show b435631:<path>`.
Classes as in section A.

| Module | L n / stmt / +doc | I n / stmt / +doc | H n / stmt / +doc | total n / stmt / +doc |
| --- | --- | --- | --- | --- |
| `ToCompPoly/Multilinear.lean` | 4 / 13 / 18 | 10 / 23 / 35 | 29 / 62 / 84 | 43 / 98 / 137 |
| `ToCompPoly/BitProductTable.lean` | 1 / 2 / 3 | 4 / 9 / 14 | 8 / 19 / 22 | 13 / 30 / 39 |
| `ToCompPoly/Stacking.lean` | 7 / 27 / 38 | 10 / 29 / 41 | 21 / 52 / 68 | 38 / 108 / 147 |
| `ToCompPoly/AmbientStacking.lean` | 0 / 0 / 0 | 2 / 7 / 11 | 8 / 28 / 37 | 10 / 35 / 48 |
| `Stack.lean` | 3 / 14 / 17 | 5 / 16 / 24 | 1 / 4 / 5 | 9 / 34 / 46 |
| `Padding.lean` | 0 / 0 / 0 | 5 / 10 / 17 | 1 / 2 / 3 | 6 / 12 / 20 |
| `ClaimWeights.lean` | 1 / 4 / 6 | 1 / 3 / 5 | 2 / 5 / 7 | 4 / 12 / 18 |
| `BlockClaims.lean` | 0 / 0 / 0 | 0 / 0 / 0 | 8 / 30 / 40 | 8 / 30 / 40 |
| `FixedColumns.lean` | 4 / 11 / 15 | 4 / 10 / 17 | 4 / 8 / 12 | 12 / 29 / 44 |
| **total** | **20 / 71 / 97** | **41 / 107 / 164** | **82 / 210 / 278** | **143 / 388 / 539** |

**What an auditor must read, and when.**

- **Today: nothing.** The master theorems, the seams and the phase interfaces are stated over an
  abstract `I : M3Instance` and import no Layer 1 module (`Spine/Instance.lean` imports `Field`,
  `ToArkLib/Oracles` and CompPoly; `Seams.lean` imports `Instance`). The one built phase that
  touches Layer 1, the public-input phase, imports `ToCompPoly/Multilinear` privately
  (`PublicInput.lean:14`, `import`, not `public import`) and uses `boolVec_zero`,
  `evalMle_append_boolVec`, `eval₂Mle_cast` and `cubeIndex` inside one proof
  (`eval₂Mle_linePoint`, `:71-89`); its definitions unfold none of them. Layer 1 is proved code
  whose statements nobody trusts yet.
- **Once the adaptor is built** (`leanIsaInstance` with `layout := (B.layout hμ).comap f h` and
  the index and bytecode columns as `Coord.known`): seventeen definitions, 61 lines (83 with
  docstrings): `Blocks`, `offsetNat`, `offset`, `total`, `selector`, `extendPoint`, `unstack`,
  `slice`, `cubeIndex`, `boolVec`, `cubeSplit`, `Layout.comap`, `readColumn`, `layout`,
  `powersTable`, `idxColumn`, `bytecodeColumn` (plus `encodeSlots`, `entry`, `derefFlags` and
  `Opcode.code` from the arithmetization and parameters), and the strided reader that does not
  exist yet (B.8).
- **Once the executable verifier is built**: the evaluators it runs, `eqWeight` (its `mle`),
  `idxColumnEval`, `bytecodeColumnEval`, and, if the verifier computes `eq(sel_b, ζ_hi)` with Layer
  1's function rather than its own, `selectorWeight`, `lowPoint`, `highPoint`, `lowVec`,
  `highVec`: eight definitions, 22 lines. The theorems relating them to the oracle
  (`idxColumn_eval`, `bytecodeColumn_eval`, `evalMle_padHigh`, `stack_eval_ambient_one`,
  `ColumnClaim.holds_iff_weighted`) are proved, so they are read for their statements only by
  whoever checks that the phases use them as intended.

**Proposals to reduce it** (each with its saving in public declarations / statement lines):

1. Delete `BlockClaims.lean` and `tests/LeanerVMTests/Protocol/BlockClaims.lean`
   (8 / 30; 122 + 108 file lines). No module uses `BlockClaim`; the opening phase uses
   `ColumnClaim.holds_iff_weighted`, over an abstract instance, which the earlier review
   introduced for that reason; `isValid_iff_pairing` restates `unstack_eval₂_eq_sumCube`; the
   locality lemmas have no consumer. Drop `BlockClaim` from the interface list
   (`protocol-blueprint.md:1404`). If the leanth credit matters, the derived-source notice can move
   with `unstack_eval₂_eq_sumCube`.
2. Delete `bytecodeColumn_slot` (1 / 2) and its three `example`s; point acceptance test 14 at
   `bytecodeColumn_answer_boolVec` and the oracle `#guard`s (G.4). `bytecodeSlotColumn` and
   `slice_bytecodeColumn` (2 / 4) have no consumer either; keep them only if the bus phase takes
   the per-slot form (`ValuesProbe`'s `bytecodeColumn_answer_slots`, which the earlier review
   recorded as open).
3. Remove the in-layer duplicates (`DuplicatesProbe`): `unstack_eval` (a special case of
   `unstack_eval₂`), `stack_eval_ambient_zero`, `stackColumn_eval` (no consumer),
   `stackColumn_eval_ambient` (honest stack only, no consumer): 4 / 14.
4. `prodVars`, `sumCube_prodVars`, `evalMle_prodVars` (3 / 5) prove nothing any other declaration
   uses; `sumCube_padHigh` is the statement the table sumcheck needs. Either delete them and cite
   `sumCube_padHigh` in acceptance test 7, or keep one as the specification's sentence.
5. Replace `evalMle_lagrangeBasis` by CompPoly's `eqTilde_eq_prod` (1 / 2), or upstream the
   reordering; keep `eqWeight.mle` as it is.
6. The 66 helpers of the four `ToCompPoly` files are the upstream pull request's content, not audit
   surface; marking the ones used only inside their own file `private` (for example
   `cubeIndex_div`, `cubeIndex_mod`, `lowVec_append`, `highVec_append`, `slice_placeSlice`,
   `windowTable*`, `stackAt_decomposition`, `offsetNat_succ`, `offsetNat_mono`) would make the
   public list of each file read as its interface.

Together 1 to 5 remove about 20 public declarations and 60 statement lines, and no load-bearing
definition. The load-bearing core (20 definitions, 71 lines) is already small; the one addition
it needs is the strided reader.

## F. Conformance with the blueprint

### F.1 The Layer 1 sketch (`protocol-blueprint.md:665-731`) against the code

Every declaration of the sketch exists with the sketched type:

| Sketch | Code (`b435631`) | Agreement |
| --- | --- | --- |
| `Column` | `Field.lean:67-69` | same (Layer 0) |
| `sumCube`, `hadamard`, `evalMle_eq_sumCube_hadamard`, `sumCube_lagrangeBasis`, `evalMle_replicate`, `slice`, `evalMle_append_boolVec`, `placeSlice`, `evalMle_placeSlice`, `sumCube_placeSlice` | `Multilinear.lean:67, 70, 91, 125, 131, 307, 342, 351, 371, 381` | same |
| `bitProductTable`, `evalMle_bitProductTable`, `powersTable`, `evalMle_powersTable` | `BitProductTable.lean:44, 58, 127, 144` | same |
| `evalMle_lagrangeBasis (w x) : … = ∏ k, (…)` | `BitProductTable.lean:156-157` | the sketch elides the right side (`(…)`) |
| `Blocks`, `Blocks.Tables`, `Blocks.stackAt`, `Blocks.selector`, `Blocks.extendPoint`, `Blocks.pow_size_dvd_offset`, `Blocks.stack_eval`, `Blocks.unstack`, `Blocks.unstack_eval₂` | `Stacking.lean:62, 75, 159, 213, 227, 109, 339, 264, 330` | same |
| `Blocks.stack_eval_ambient` (in mathematical notation) | `AmbientStacking.lean:134-138`, through `selectorWeight` and `lowPoint` | same meaning |
| `Blocks.stackColumn`, `readColumn`, `readColumn_eval`, `layout`, `Layout.comap`, `stack_eval_ambient_one` | `Stack.lean:70, 73, 78, 97, 52, 118` | same (`w_b` of the sketch is `selectorWeight`) |
| `padHigh`, `sumCube_padHigh`, `sumCube_prodVars` | `Padding.lean:60, 64, 47` | same |
| `eqWeight`, `ColumnClaim.holds_iff_weighted` | `ClaimWeights.lean:45, 58` | same |
| `idxColumn`, `idxColumn_eval`, `idxColumnEval_eq`, `bytecodeColumn`, `bytecodeColumn_eval` | `FixedColumns.lean:48, 60, 66, 79, 114` | same |
| `bytecodeColumn_answer_boolVec … = ofK (encodeSlots (prog.code i))[s]` | `FixedColumns.lean:97-101`, `= algebraMap K E (…)` | notation: `ofK := Ext.ofBase` (`Parameters/Field.lean:86`), equal to `algebraMap K E` by `Extension.Ext.algebraMap_eq_ofBase` |

In the code, not in the sketch, and appearing in sketched statements or run by a verifier:
`Blocks.selectorWeight`, `Blocks.lowPoint`, `Blocks.highPoint`, `Blocks.total`, `Blocks.offset`,
`idxColumnEval`, `bytecodeColumnEval`, and `evalMle_padHigh` (the identity the table sumcheck's
final check rests on, B.4). `BlockClaims.lean` is named as a module (`:662`) and sketches nothing.

The prose (`:734-746`) agrees with the code: the aligned reader for a table the prover chose is
`unstack_eval₂`; `stack_eval_ambient` for any pad; back-loaded padding is `placeSlice` at the
all-ones index; the index column is the geometric table; the public-input phase's point
`(r, 0, …, 0)` is handled by `evalMle_append_boolVec` at slice zero (as done in
`PublicInput.lean:71-89`). The tests paragraph (`:748-755`) is met item by item (C.5).

### F.2 Acceptance tests 7, 13, 14, 15

- **7** (`:1284-1286`): "Lifting table `j` by `∏_{k ≥ τ_j} X_k` sums to the table's own sum
  (`sumCube_prodVars`) … Witness: `tableSummand_target` on heights 2 and 1." The statement it
  describes is `sumCube_padHigh`, not `sumCube_prodVars` (which is `Σ x_0⋯x_{m−1} = 1`); and
  `tableSummand_target` does not exist (Layer 7 is not built). The existing witness is
  `tests/…/Padding.lean:44-49` (the copied table sums to 0 in characteristic two).
- **13** (`:1303-1305`): the named witness exists (`tests/…/FixedColumns.lean:37-47`) and fails on
  the reversed order. Met.
- **14** (`:1306-1307`): "Witness: `bytecodeColumn_slot` on a two-instruction program." The theorem
  exists but restates the definition and holds of the opposite layout by the same proof (C.3); the
  witness that pins slot 3 = `(1,1,0,0)` is `bytecodeColumn_answer_boolVec` and the oracle `#guard`s
  at `tests/…/FixedColumns.lean:82-93`. Stale.
- **15** (`:1308-1310`): "Blocks sit at offsets that are multiples of their size, largest first;
  `stack_eval` fails for any other placement. Witness: three blocks of sizes 4, 2, 1 with the
  small one first." Two imprecisions: 4, 2, 1 are the *heights* (the sizes, in the code's sense of
  variables, are 2, 1, 0); and "fails for any other placement" is false: sizes 1, 1, 2 in that
  order sit at offsets 0, 2, 4, all aligned (`DuplicatesProbe`), and any permutation of equal sizes
  is aligned too, which is exactly why the tie order needs its own guard (B.2). The witness exists
  (`tests/…/Stack.lean:87-95`).

### F.3 The interface list (`:1386-1406`)

- Every Layer 1 name listed exists: generic `Column sumCube hadamard slice placeSlice boolVec
  evalMle_eq_sumCube_hadamard evalMle_append_boolVec evalMle_placeSlice bitProductTable
  evalMle_bitProductTable powersTable evalMle_powersTable Blocks Blocks.Tables Blocks.stackAt
  Blocks.selector Blocks.extendPoint Blocks.stack_eval Blocks.stack_eval₂ Blocks.unstack
  Blocks.unstack_eval₂ Blocks.stack_eval_ambient`; leanVM `Blocks.stackColumn Blocks.readColumn
  Blocks.readColumn_eval Blocks.layout Layout.comap Blocks.stack_eval_ambient_one padHigh
  sumCube_padHigh prodVars sumCube_prodVars eqWeight ColumnClaim.holds_iff_weighted BlockClaim
  idxColumn idxColumn_eval idxColumnEval_eq bytecodeColumn bytecodeColumn_answer_boolVec
  bytecodeColumn_eval`.
- Mislabelled: `Column` (over `K`, Layer 0) and `Weight`, `WeightedClaim` (spine objects over `E`,
  `Seams.lean:103-124`, listed a second time under "Spine", `:1370`) are listed under "Protocol
  (generic)" (`:1386`, `:1395`).
- Missing, although "Everything not listed is a proof, a helper, or a test" (`:1419`):
  `idxColumnEval`, `bytecodeColumnEval` (the evaluators the verifier runs; right sides of listed
  theorems), `evalMle_padHigh`, `Blocks.selectorWeight`, `Blocks.lowPoint`, `Blocks.total`,
  `Blocks.offset` (in listed statements).
- Listed and to be removed if proposal E.1 is taken: `BlockClaim`.

### F.4 Elsewhere in the blueprint, touching Layer 1

- Layer 3 (`:808`): `theorem leanIsaInstance_fits : (leanIsaInstance prog s).layout.total ≤ 2 ^
  (leanIsaInstance prog s).μ`. `Layout` (`Spine/Instance.lean:73-81`) has no `total`; `total` is a
  field of `Blocks`. Moreover `Blocks.layout` takes the fit as an argument (`hμ`), so the fit must
  be proved *before* `leanIsaInstance` can be defined, not after it. Finding G.2.
- Layer 3 (`:841-848`): "`Layout` admits both readers; `Blocks` expresses only the first, so
  `leanIsaInstance.layout` combines the two". True of the types, but neither the strided selection
  lemma nor the combinator exists or is sketched in any layer (B.8, G.1).
- Convention *Stacks* (`:322`) states the tie order and `μ_stack ∈ [15, 28]`; both agree with the
  Rust (`witness.rs:67-79`; `pcs.rs:49-51`, `cpu/mod.rs:174`) and the Python (`py:305-311, 890,
  907-908, 1379`). Convention *Hypercube* and *`eq`* (`:312, 314`) agree with B.1 and B.7.
- Convention *The wall* (`:331`) and acceptance test 25 (`:1341-1345`) do not list
  `Protocol/Basic.lean` (D.1, G.8).

## G. Findings

### G.1 The strided reader of the eighteen BLAKE2S limb columns exists nowhere and is assigned to no layer

- **Severity**: major (the blueprint omits something leanVM does, and `leanIsaInstance` cannot be
  built without it).
- **Evidence.** leanVM reads the limb columns as strided slots of `q_flock`
  (`pcs/src/stack_open.rs:84-97`; `py:884-894`, `Placement(…, QFLOCK_SLOT_BITS)` with `low = 8`;
  `lean_vm/src/hash_flock.rs:87-115`; `gt-flock-ring.md` 2.4, 5.4). Layer 1 has only high-index
  selection (`slice`, `evalMle_append_boolVec`, `unstack`), and says so
  (`ToCompPoly/Multilinear.lean:50-51`). `Layout.comap` cannot place a limb column: its height
  `2^τ_B` is no block's (B.8). The blueprint's Layer 3 (`:841-848`) says the instance "combines the
  two" readers but no layer sketches the selection lemma, the strided reader or the combinator;
  the slot map is placed in Layer 9's `FlockInterface.limbColumns` (`gt-flock-ring.md` 8.2).
  `StridedProbe` proves the missing generic lemma in twenty lines from Layer 1's own lemmas.
- **Classification**: an error of the blueprint (omission).
- **Proposed change.** In the Layer 1 sketch, after `evalMle_append_boolVec`, add:

  > ```lean
  > def sliceLow (t : CMlPolynomialEval R (k + m)) (i : Fin (2 ^ k)) : CMlPolynomialEval R m
  > theorem evalMle_boolVec_append (t) (i) (s) : evalMle t (boolVec i ++ s) = evalMle (sliceLow t i) s
  > -- Stack.lean
  > def Blocks.stridedLayout (hμ) (b : Fin B.n) (k : ℕ) (slot : ι → Fin (2 ^ k))
  >     (h : ∀ c, B.size b = k + κ c) : Layout μ ι κ       -- column c = sliceLow of block b at slot c
  > def Layout.piecewise (L₁ : Layout μ ι₁ κ₁) (L₂ : Layout μ ι₂ κ₂) : Layout μ (ι₁ ⊕ ι₂) (Sum.elim κ₁ κ₂)
  > ```

  and in the prose: "leanVM reads the eighteen BLAKE2S limb columns as strided slots of
  `q_flock`: the low eight coordinates of `q_flock`'s block are frozen to the slot's bits
  (`stack_open.rs:84-97`). `evalMle_boolVec_append` is the low-index selection identity;
  `Blocks.stridedLayout` packages it as a `Layout`, and `Layout.piecewise` joins it to the aligned
  layout; Layer 3 transports the sum type to `ColumnId`." Tests: the slot's strided slice against
  the aligned slice of the same index; a limb claim's lifted point against `Placement.stack_point`
  of `py:295-297` on the layout of `offsets.py`. Reason: without it the instance's `layout` cannot
  be written, and the Rust's `Strided` claims have no Lean counterpart.

### G.2 `leanIsaInstance_fits` cannot be stated as written, and is needed before the instance, not after

- **Severity**: major by the scale's letter (a statement that cannot be stated as written); the fix
  is one line.
- **Evidence.** `protocol-blueprint.md:808`: `theorem leanIsaInstance_fits : (leanIsaInstance prog
  s).layout.total ≤ 2 ^ (leanIsaInstance prog s).μ`. `Layout` has the fields `read`, `extend`,
  `read_eval` only (`Spine/Instance.lean:73-81`); `total` belongs to `Blocks`
  (`Stacking.lean:87`), and `Blocks.layout` takes the fit as its argument `hμ` (`Stack.lean:97`),
  so the instance's `layout` field cannot be filled until the fit is proved.
- **Classification**: an error of the blueprint.
- **Proposed change.** As it stands: "`theorem leanIsaInstance_fits : (leanIsaInstance prog
  s).layout.total ≤ 2 ^ (leanIsaInstance prog s).μ`". As proposed: "`def leanIsaBlocks (prog) (s)
  : Blocks` (the sorted sizes of the committed columns); `def leanIsaμ (prog) (s) : ℕ := max 15
  (Nat.clog 2 (leanIsaBlocks prog s).total)` (`witness.rs:97`, `py:890`); `theorem
  leanIsaBlocks_fits : (leanIsaBlocks prog s).total ≤ 2 ^ leanIsaμ prog s`, the `hμ` of
  `leanIsaInstance`'s layout". Reason: the only fit that exists is a `Blocks`'; the order of
  definitions must follow.

### G.3 The order of equal-size blocks is pinned by no statement, definition or test before the compiled verifier

- **Severity**: minor (the blueprint states the order correctly; nothing checks it until Layer 12).
- **Evidence.** `Blocks` is the sorted sizes (`Stacking.lean:62-68`); the column-to-block map is the
  `f` of `Layout.comap` (`Stack.lean:52`), constrained only to keep heights. `OffsetsProbe`:
  leanVM's order and the "tables first" order give the same `Blocks` and different offsets per
  column (`mem_0` at 32 against 64); every Layer 1 theorem holds of both, and so would every
  Layer 3 theorem (a bijective `f` passes the round trip). The earlier review marked the matter
  "Met in the documentation … the instance (I2) supplies it" (`docs/reviews/protocol-layer1.md:34`).
  Layer 3's text promises a transcription and `decide`d offsets (`:865-866`) but no test on a
  configuration where a table height equals `κ_mem`. The leaf stacks have the same gap
  (`gt-bus.md` G7).
- **Classification**: an error of the blueprint (a check deferred with no witness named).
- **Proposed change.** Add to Layer 3's tests (`:866-867`), as it stands "Tests: a witness with one
  row per table stacked and read back …; `Sizes.Admissible` rejects `logMem = 15` and
  `τ_BLAKE2S = 2`", the sentence: "and the offsets of every committed column on the two
  configurations of the Layer 1 review's `OffsetsProbe` (sizes `[4,4,4,4,2,5,4,4]`, and
  `log_memory = 16`, `τ = (3, 16, 0, 5, 16, 3)`, `κ_bc = 4`, whose 92 offsets are the pinned
  Python's `build_layout`), where a table's height equals `κ_mem`, so that the tables-first order
  fails them." Reason: the order decides every selector, and only this guard can catch a wrong
  one before a Rust proof does.

### G.4 Acceptance test 14 names a tautology as its witness; `bytecodeColumn_slot` and its tests prove nothing about the layout

- **Severity**: minor.
- **Evidence.** C.3: `bytecodeColumn_slot` (`FixedColumns.lean:84-87`) unfolds the definition, and
  the same proof proves the opposite layout's analogue (`ValuesProbe`, `wrongColumn_slot`). Still
  cited: `protocol-blueprint.md:1306-1307`, `protocol-status.md:51`. Its three test uses
  (`tests/…/FixedColumns.lean:61-74`) instantiate it. The repository's bytecode-column tests use
  all-`1` operands (`:56-59`), so they cannot see an operand-slot swap; no repository test compares
  `bytecodeColumn` with leanVM's encoder.
- **Classification**: an error of the blueprint (stale witness), and avoidable audit surface.
- **Proposed change.** Acceptance test 14, as it stands: "Witness: `bytecodeColumn_slot` on a
  two-instruction program." As proposed: "Witness: `bytecodeColumn_answer_boolVec`, and the oracle
  `#guard`s of `tests/LeanerVMTests/Protocol/FixedColumns.lean` (slot bits `(1,1,0,0)` answer the
  opcode, `(0,0,1,1)` answer `0`), and a `#guard` of `bytecodeColumn` on a sixteen-instruction
  program with distinct operands against the table of `leaf.rs:585-604`." In the code: delete
  `bytecodeColumn_slot` and its three `example`s; add `ValuesProbe`'s `prog16`/`pyTable` `#guard`
  (rewritten with `K.ofBits` for the new CompPoly pin, H). Reason: the witness must fail on the
  wrong layout, and the operand order needs one independent check.

### G.5 Acceptance test 15 overclaims

- **Severity**: minor.
- **Evidence.** `protocol-blueprint.md:1308-1310`: "`stack_eval` fails for any other placement.
  Witness: three blocks of sizes 4, 2, 1 with the small one first." Sizes `1, 1, 2` in that order
  are aligned (`DuplicatesProbe`); any permutation of equal sizes is aligned; "4, 2, 1" are
  heights, the code's sizes are `2, 1, 0`.
- **Classification**: an error of the blueprint.
- **Proposed change.** As proposed: "**Selector alignment.** Blocks placed largest first sit at
  offsets that are multiples of their heights (`pow_size_dvd_offset`); with the smallest block
  first no selector reads it. Largest first is sufficient, not necessary, and says nothing of the
  order of equal sizes (acceptance test on the tie order, Layer 3). Witness: three blocks of heights
  4, 2, 1 with the small one first (`tests/LeanerVMTests/Protocol/Stack.lean`)." Reason: the
  current wording suggests the descending order pins the placement, which is the reading that hides
  G.3.

### G.6 The interface list omits load-bearing Layer 1 names and mislabels three

- **Severity**: minor.
- **Evidence.** F.3: `idxColumnEval`, `bytecodeColumnEval`, `evalMle_padHigh`,
  `Blocks.selectorWeight`, `Blocks.lowPoint`, `Blocks.total`, `Blocks.offset` are not listed,
  although `:1419` says everything unlisted is a proof, helper or test; `Column`, `Weight`,
  `WeightedClaim` are listed as generic.
- **Classification**: an error of the blueprint.
- **Proposed change.** In "Protocol (generic)" (`:1386-1391`) replace `Column` by nothing (it is
  Layer 0's, listed under "Protocol (leanVM)" with `evalOracle`) and add `Blocks.total
  Blocks.offset Blocks.lowPoint Blocks.selectorWeight` (and `sliceLow evalMle_boolVec_append` if
  G.1 is taken); drop `Weight WeightedClaim` from `:1395`; in "Protocol (leanVM)" (`:1403-1406`)
  add `evalMle_padHigh`, `idxColumnEval`, `bytecodeColumnEval`. In the Layer 1 sketch add
  `evalMle_padHigh` and the two evaluators' definitions. Reason: these are what a verifier runs or
  what listed statements mention.

### G.7 `BlockClaims.lean` has no consumer

- **Severity**: minor (audit surface).
- **Evidence.** A.8, E.1: `git grep -w BlockClaim b435631 -- LeanerVM tests` finds its module and
  its test only; `isValid_iff_pairing` restates `unstack_eval₂_eq_sumCube`
  (`BlockClaims.lean:31`, "this module only names its arguments"); the opening phase uses
  `ColumnClaim.holds_iff_weighted`.
- **Classification**: avoidable audit surface.
- **Proposed change.** Delete `LeanerVM/Protocol/BlockClaims.lean` and its test; remove it from the
  module list of Layer 1 (`:662`, "`BlockClaims.lean` (claims on aligned blocks)") and `BlockClaim`
  from the interface list (`:1404`). Reason: 8 public declarations, 40 lines, no use.

### G.8 `Protocol/Basic.lean` imports the arithmetization and is not a listed exception of the wall

- **Severity**: minor.
- **Evidence.** D.1: `LeanerVM/Protocol/Basic.lean:3`, `public import LeanerVM.Arithmetization.Basic`;
  an empty placeholder imported by `LeanerVM.lean` only. Acceptance test 25 (`:1341-1345`) says
  the grep lists the wall's exceptions only.
- **Classification**: an error of the blueprint (the witness text is false), and dead code.
- **Proposed change.** Delete `LeanerVM/Protocol/Basic.lean` (and its import in `LeanerVM.lean`),
  or drop its import. Reason: acceptance test 25's witness becomes true as written.

### G.9 Acceptance test 7 names the wrong lemma and a witness that does not exist

- **Severity**: minor.
- **Evidence.** F.2: "sums to the table's own sum (`sumCube_prodVars`)" is `sumCube_padHigh`;
  `tableSummand_target` is a Layer 7 name, not built.
- **Classification**: an error of the blueprint.
- **Proposed change.** As proposed: "… sums to the table's own sum (`sumCube_padHigh`); lifting by
  nothing (copying) multiplies it by `2^(τ_max − τ_j)`, which is `0` in characteristic two when
  `τ_j < τ_max`. Witnesses: `tests/LeanerVMTests/Protocol/Padding.lean` (the copied table), and
  `tableSummand_target` on heights 2 and 1 once Layer 7 lands." Reason: the witness must exist.

### G.10 Notes

- **`Layout.comap` accepts a non-injective renaming** (C.4, `ValuesProbe`'s `aliased`). Completeness
  of the adaptor catches aliasing; no change is required. Optional: state `Function.Injective f`
  for `leanIsaInstance`'s map in Layer 3.
- **Unused or duplicated declarations** (`prodVars` and its two lemmas, `unstack_eval`,
  `stack_eval_ambient_zero`, `stackColumn_eval`, `stackColumn_eval_ambient`, `bytecodeSlotColumn`,
  `slice_bytecodeColumn`, `evalMle_lagrangeBasis` against CompPoly's `eqTilde_eq_prod`): E,
  proposals 2 to 5.
- **`idxColumnEval` is efficient** in CompPoly's `K` (binary exponentiation, B.5); no change.
- **Disagreements between leanVM's sources**, recorded, not new: the specification's `M = ⌈log₂ N⌉`
  has no floor or ceiling, the Rust and the Python bound the witness stack to `[15, 28]`
  (B.2; the blueprint follows the Rust and the Python); the specification gives no tie rule, both
  verifiers break ties by column index (B.2; the blueprint follows them); the Rust evaluates the
  program's share per column, the Python as one stacked evaluation (B.6, `gt-bus.md` G15; equal on
  Lean's column).
- **The upgrade to `144c5aa`** leaves every Layer 1 statement and definition unchanged and
  preserves the meaning of every Layer 1 test (H).

## H. What the upgrade to `144c5aa` changed in Layer 1

`git diff b435631 144c5aa` on the nine Layer 1 sources: proof lines only, with equal line counts
(`Padding.lean` 1 line, `AmbientStacking.lean` 2, `BitProductTable.lean` 1, `Multilinear.lean` 4,
`Stacking.lean` 4; for example `if_true` → `ite_true`, `dif_pos hcn` → `dite_eq_left hcn`,
`if_neg …` → `ite_eq_right …`). `Stack.lean`, `ClaimWeights.lean`, `BlockClaims.lean`,
`FixedColumns.lean`, `Arithmetization/Bytecode.lean`, `Parameters/Isa.lean`,
`Semantics/Instruction.lean`, `Spine/Seams.lean` are unchanged; `Protocol/Field.lean` changed its
pin comments and the sampler's equivalence (`BF64.ofBitVec (BitVec.ofFin i)`), not `Column` or
`evalOracle`; `Spine/Instance.lean` changed one import line. Every statement and definition of
section A reads the same at `144c5aa`, at the same line.

**Numerals in `K`.** At the new CompPoly pin `(2 : K) = 0` (a natural-number cast in
characteristic two), and a word is `K.ofBits n` (`Parameters/Field.lean` at `144c5aa`:
"Natural-number casts follow characteristic two: `2 : K = 0`. Wire words use `K.ofBits`"). At the
old pin a numeral `n : K` was the word `n` (`Parameters/Field.lean` at `b435631`: "The numeral
`2 : K` is the `BitVec` literal `x`"). The generator went from `def g : K := 0x2` to
`def g : K := K.ofBits 0x2` (`Parameters/Generator.lean:43`), the same element `x`.

The Layer 1 tests at `b435631` used numerals other than `0` and `1` in `K` throughout:
`Multilinear.lean` (`tbl = #v[1, 2, 3, 4]`, `pt = #v[5, 9]`, …), `BitProductTable.lean` (`factors`
2, 3, 5, 7; `powersTable (3 : K)`), `Stacking.lean` (the tables `[1,2,3,4]`, `[5,6]`, `[7]`, the
points `9, 11, 13`), `AmbientStacking.lean` (pad `5`, points), `Stack.lean` (`arbitrary`,
`smallFirst`, the toy mutation `2`), `Padding.lean` (`short = [3, 5]`, `copied`, points),
`ClaimWeights.lean` (`arbitrary`), `BlockClaims.lean` (`arbitraryTable`, values `5`). The upgrade
rewrote every one of them as `K.ofBits n` (`git diff b435631 144c5aa -- tests/LeanerVMTests/
Protocol`), which is the same word, so every test means at `144c5aa` what it meant at `b435631`.
A scan of the nine test files at `144c5aa` for a remaining `K` numeral other than `0`, `1` finds
none (the matches are dimensions and exponents: `Vector K 3`, `g ^ 2`). `FixedColumns.lean`
(tests) needed no change (operands `1`, points in `E` built from `y`). The copied-table test keeps
its sense: its sum is `4·t = 0` in characteristic two, now with the `K.ofBits` words.

**The probes of this dossier** were written and run at the old pin, where `3 : K` was the word
3. `OffsetsProbe` (lists of `ℕ`) and `DuplicatesProbe` (an arbitrary ring, `ℕ`) do not depend on
this. `ValuesProbe` and `StridedProbe` do: re-run at the new pin, their `K` numerals (`#v[9, 8,
…]`, `E.ofLimbs 3 1 0`, `pyTable` via `toNat`, `packed = #v[10, …, 23]`) must be rewritten with
`K.ofBits`; as they stand their numerals would be casts (`0` or `1`), the immediate limbs
`11, 12, 13` of `prog16` would become `1, 0, 1`, and the `pyTable` guard would not hold (if it
elaborates at all: `K` is now a structure, and `(·.toNat)` may need `toBitVec`). Not run at the
new pin (section J).

## I. Probes

All under `.claude/reports/blueprint-review/probes/code-layer1/`, written by the interrupted
first agent of this task and run once each by this one on 2026-09-30, each output saved next to
its probe (`*.out`). **How they ran**, given that the owner moved the checkout at 09:18 (reflog:
`reset` 09:18:19, `checkout main` 09:18:20, `pull` to `144c5aa` 09:18:26, back to the review branch
09:18:33, `merge main` 09:18:36; the dependency sources under `.lake/packages/` were switched to
the new pins at 09:18:47-09:19:05, their `.olean` files were not rebuilt):

- `offsets.py`, `values.py`: `python3 -B <file>` at 09:16, exit 0. They import the pinned
  Python verifier read-only from `/home/scaraven/Documents/leanEthereum/leanVM/python-verifier`
  (at `a386121f`).
- `OffsetsProbe.lean` (finished 09:17:02) and `ValuesProbe.lean` (finished 09:18:17.99), with the
  brief's command `flock .claude/reports/blueprint-review/logs/lean.lock lake env lean <file>`,
  both before the checkout moved: sources at `b435631`, libraries at the old pins, exit 0.
- `DuplicatesProbe.lean`: the first attempt with `lake env lean` (09:18:22) found the file missing
  (the owner's checkout of `main` had removed the tracked probe files for thirteen seconds) and
  did nothing else. Both it and `StridedProbe.lean` were then run at 09:20 **not through `lake`**
  but with the old pin's Lean binary directly on the `b435631` build artefacts, which the move
  had not touched (no `.olean` under `.lake/` was newer than 2026-09-30 00:00, checked just
  before; `.lake/build` dates from the orchestrator's build of 2026-09-29 17:18, the packages'
  builds from 2026-09-28/29):

  ```sh
  LP="$(pwd)/.lake/build/lib/lean"; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$(pwd)/$d"; done
  LEAN_PATH="$LP" timeout 590 flock .claude/reports/blueprint-review/logs/lean.lock \
    /home/scaraven/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean <probe>.lean
  ```

  Lean loads compiled `.olean` files only and never reads the (switched) library sources, so these
  runs elaborate against `b435631` and the old pins exactly as `lake env lean` did before the
  move; both exit 0. They were made before the coordinator's instruction to stop running Lean
  arrived; no Lean process was started after it. The orchestrator may prefer to treat these two
  as "written, not run through the brief's command"; the conclusions resting on them are marked
  in the text (`DuplicatesProbe`: D.2 and G.5; `StridedProbe`: B.8 and G.1) and each is also a
  short argument a reader can check by hand.

### I.1 `offsets.py`

Command: `python3 -B .claude/reports/blueprint-review/probes/code-layer1/offsets.py`

```python
"""Probe for task code-layer1, deliverable B.2.

Runs the pinned Python verifier's own `stack_offsets` and `build_layout` (imported read-only
from the leanVM checkout at a386121f; no bytecode cache is written) and a line-by-line
transcription of the Rust `stack_offsets` (crates/lean_vm/src/witness.rs:67-79), and prints
the offsets and selectors of two configurations.

Run:  python3 -B .claude/reports/blueprint-review/probes/code-layer1/offsets.py
"""

import sys

sys.dont_write_bytecode = True
sys.path.insert(0, "/home/scaraven/Documents/leanEthereum/leanVM/python-verifier")
import verifier as V  # noqa: E402


def rust_stack_offsets(kappas):
    """witness.rs:67-79, transcribed: `order.sort_by(|a,b| kappas[b].cmp(kappas[a]).then(a.cmp(b)))`."""
    n = len(kappas)
    order = [i for i in range(n) if kappas[i] is not None]
    order.sort(key=lambda i: (-kappas[i], i))
    offsets = [0] * n
    off = 0
    for i in order:
        offsets[i] = off
        off += 1 << kappas[i]
    return offsets, off, order


def report(name, kappas, names=None):
    print(f"== {name}")
    print("sizes in column-index order:", kappas)
    r_off, r_total, order = rust_stack_offsets(kappas)
    p_off, p_log = V.stack_offsets(kappas)
    print("Rust transcription offsets :", r_off, "total", r_total)
    print("Python verifier offsets    :", p_off, "log2_ceil(total)", p_log)
    assert r_off == p_off
    print("stacking order (column indices, first block first):", order)
    print("sorted sizes (the Blocks.size sequence)           :", [kappas[i] for i in order])
    print("offset per block, in stacking order               :", [r_off[i] for i in order])
    print("selector per block (offset >> size)               :", [r_off[i] >> kappas[i] for i in order])
    if names:
        for i in order:
            print(f"   block of column {i:3d} {names[i]:<14s} size {kappas[i]:2d} offset {r_off[i]:8d} selector {r_off[i] >> kappas[i]}")
    print()


# 1. The small configuration of the dossier: six shared columns and two table columns.
names = ["mem_0", "mem_1", "mem_2", "cntfin_mem", "cntfin_bc", "q_flock", "table col a", "table col b"]
report("small configuration", [4, 4, 4, 4, 2, 5, 4, 4], names)

# 2. The pinned verifier's real layout for one admissible announcement:
#    log_memory 16, table log-heights (xor, mul, set, deref, jump, blake2s) = (3, 16, 0, 5, 16, 3),
#    a bytecode of 2^4 instructions (the table has 2^(4+4) words; its content is irrelevant here).
bytecode = [V.K(0)] * (1 << 8)
layout = V.build_layout(bytecode, 16, (3, 16, 0, 5, 16, 3))
cols = []
for column, p in enumerate(layout.placements):
    cols.append((column, p.variables, p.index, p.low))
committed = [(c, k, off) for (c, k, off, low) in cols if low == 0]
virtual = [(c, k, off, low) for (c, k, off, low) in cols if low != 0]
print("== the pinned Python verifier's build_layout(log_memory=16, taus=(3,16,0,5,16,3), kbc=4)")
print("columns:", len(cols), "committed blocks:", len(committed), "strided (BLAKE2S limb) columns:", len(virtual))
print("stack_log:", layout.stack_log)
order = sorted(committed, key=lambda t: t[2])
print("stacking order, as (column index, size, offset):")
print(order)
print("sorted sizes:", [k for (_, k, _) in order])
print("offsets     :", [off for (_, _, off) in order])
print("column index of each block:", [c for (c, _, _) in order])
# the same sizes through the Rust transcription, virtual columns as None
kappas = [None if low != 0 else k for (_, k, _, low) in cols]
r_off, r_total, r_order = rust_stack_offsets(kappas)
assert [r_off[c] for (c, _, _) in committed] == [off for (_, _, off) in committed]
assert r_order == [c for (c, _, _) in order]
print("Rust transcription agrees on every committed column; total", r_total, "log2_ceil", V.log2_ceil(r_total))
print("global column bases of the six tables:", V.GLOBAL_COLUMN_BASES, "widths", V.TABLE_WIDTHS)
```

Output:

```text
== small configuration
sizes in column-index order: [4, 4, 4, 4, 2, 5, 4, 4]
Rust transcription offsets : [32, 48, 64, 80, 128, 0, 96, 112] total 132
Python verifier offsets    : [32, 48, 64, 80, 128, 0, 96, 112] log2_ceil(total) 8
stacking order (column indices, first block first): [5, 0, 1, 2, 3, 6, 7, 4]
sorted sizes (the Blocks.size sequence)           : [5, 4, 4, 4, 4, 4, 4, 2]
offset per block, in stacking order               : [0, 32, 48, 64, 80, 96, 112, 128]
selector per block (offset >> size)               : [0, 2, 3, 4, 5, 6, 7, 32]
   block of column   5 q_flock        size  5 offset        0 selector 0
   block of column   0 mem_0          size  4 offset       32 selector 2
   block of column   1 mem_1          size  4 offset       48 selector 3
   block of column   2 mem_2          size  4 offset       64 selector 4
   block of column   3 cntfin_mem     size  4 offset       80 selector 5
   block of column   6 table col a    size  4 offset       96 selector 6
   block of column   7 table col b    size  4 offset      112 selector 7
   block of column   4 cntfin_bc      size  2 offset      128 selector 32

== the pinned Python verifier's build_layout(log_memory=16, taus=(3,16,0,5,16,3), kbc=4)
columns: 110 committed blocks: 92 strided (BLAKE2S limb) columns: 18
stack_log: 22
stacking order, as (column index, size, offset):
[(0, 16, 0), (1, 16, 65536), (2, 16, 131072), (3, 16, 196608), (21, 16, 262144), (22, 16, 327680), (23, 16, 393216), (24, 16, 458752), (25, 16, 524288), (26, 16, 589824), (27, 16, 655360), (28, 16, 720896), (29, 16, 786432), (30, 16, 851968), (31, 16, 917504), (32, 16, 983040), (33, 16, 1048576), (34, 16, 1114112), (35, 16, 1179648), (59, 16, 1245184), (60, 16, 1310720), (61, 16, 1376256), (62, 16, 1441792), (63, 16, 1507328), (64, 16, 1572864), (65, 16, 1638400), (66, 16, 1703936), (67, 16, 1769472), (68, 16, 1835008), (69, 16, 1900544), (70, 16, 1966080), (71, 16, 2031616), (72, 16, 2097152), (5, 11, 2162688), (44, 5, 2164736), (45, 5, 2164768), (46, 5, 2164800), (47, 5, 2164832), (48, 5, 2164864), (49, 5, 2164896), (50, 5, 2164928), (51, 5, 2164960), (52, 5, 2164992), (53, 5, 2165024), (54, 5, 2165056), (55, 5, 2165088), (56, 5, 2165120), (57, 5, 2165152), (58, 5, 2165184), (4, 4, 2165216), (6, 3, 2165232), (7, 3, 2165240), (8, 3, 2165248), (9, 3, 2165256), (10, 3, 2165264), (11, 3, 2165272), (12, 3, 2165280), (13, 3, 2165288), (14, 3, 2165296), (15, 3, 2165304), (16, 3, 2165312), (17, 3, 2165320), (18, 3, 2165328), (19, 3, 2165336), (20, 3, 2165344), (73, 3, 2165352), (74, 3, 2165360), (75, 3, 2165368), (76, 3, 2165376), (77, 3, 2165384), (78, 3, 2165392), (79, 3, 2165400), (80, 3, 2165408), (81, 3, 2165416), (100, 3, 2165424), (101, 3, 2165432), (102, 3, 2165440), (103, 3, 2165448), (104, 3, 2165456), (105, 3, 2165464), (106, 3, 2165472), (107, 3, 2165480), (108, 3, 2165488), (109, 3, 2165496), (36, 0, 2165504), (37, 0, 2165505), (38, 0, 2165506), (39, 0, 2165507), (40, 0, 2165508), (41, 0, 2165509), (42, 0, 2165510), (43, 0, 2165511)]
sorted sizes: [16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 11, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0]
offsets     : [0, 65536, 131072, 196608, 262144, 327680, 393216, 458752, 524288, 589824, 655360, 720896, 786432, 851968, 917504, 983040, 1048576, 1114112, 1179648, 1245184, 1310720, 1376256, 1441792, 1507328, 1572864, 1638400, 1703936, 1769472, 1835008, 1900544, 1966080, 2031616, 2097152, 2162688, 2164736, 2164768, 2164800, 2164832, 2164864, 2164896, 2164928, 2164960, 2164992, 2165024, 2165056, 2165088, 2165120, 2165152, 2165184, 2165216, 2165232, 2165240, 2165248, 2165256, 2165264, 2165272, 2165280, 2165288, 2165296, 2165304, 2165312, 2165320, 2165328, 2165336, 2165344, 2165352, 2165360, 2165368, 2165376, 2165384, 2165392, 2165400, 2165408, 2165416, 2165424, 2165432, 2165440, 2165448, 2165456, 2165464, 2165472, 2165480, 2165488, 2165496, 2165504, 2165505, 2165506, 2165507, 2165508, 2165509, 2165510, 2165511]
column index of each block: [0, 1, 2, 3, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 5, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 73, 74, 75, 76, 77, 78, 79, 80, 81, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 36, 37, 38, 39, 40, 41, 42, 43]
Rust transcription agrees on every committed column; total 2165512 log2_ceil 22
global column bases of the six tables: (6, 21, 36, 44, 59, 73) widths (15, 15, 8, 15, 14, 37)
```

### I.2 `OffsetsProbe.lean`

Command: `flock .claude/reports/blueprint-review/logs/lean.lock lake env lean .claude/reports/blueprint-review/probes/code-layer1/OffsetsProbe.lean`

```lean
/-
  Probe for task code-layer1, deliverable B.2.

  leanVM's `stack_offsets` (`crates/lean_vm/src/witness.rs:67-79`, `python-verifier/verifier.py:
  305-311`) transcribed as a list function, and Layer 1's `Blocks.offset` / `Blocks.selector`
  fed with the order it produces. The expected numbers are the output of `offsets.py`, which
  runs the pinned Python verifier.

  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/code-layer1/OffsetsProbe.lean
-/
import LeanerVM.Protocol.ToCompPoly.Stacking

open LeanerVM.Protocol

namespace Probe

/-! ## `stack_offsets`, transcribed -/

/-- The stacking order: column indices sorted by size, largest first, ties by index. -/
def stackOrder (kappas : List ℕ) : List ℕ :=
  (List.range kappas.length).mergeSort fun a b ↦
    decide (kappas[b]! < kappas[a]!) || (kappas[a]! == kappas[b]! && decide (a ≤ b))

/-- Prefix sums of the heights along a list of sizes. -/
def prefixOffsets : List ℕ → ℕ → List ℕ
  | [], _ => []
  | k :: ks, off => off :: prefixOffsets ks (off + 2 ^ k)

/-- The offset of every column, in column-index order (`offsets[i] = off` for `i` in order). -/
def stackOffsets (kappas : List ℕ) : List ℕ :=
  let order := stackOrder kappas
  let offs := prefixOffsets (order.map (kappas[·]!)) 0
  (List.range kappas.length).map fun i ↦ (offs[order.idxOf i]?).getD 0

/-- A `Blocks` from a list of sizes that is already largest first. -/
def blocksOfList (l : List ℕ) (h : l.Pairwise (· ≥ ·)) : Blocks where
  n := l.length
  size := fun i ↦ l[i]
  descending := by
    intro a b hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (List.pairwise_iff_getElem.mp h) a.val b.val a.isLt b.isLt hlt

/-- Every offset of a `Blocks`, first block first. -/
def offsetsOf (B : Blocks) : List ℕ := (List.finRange B.n).map B.offset

/-- Every selector of a `Blocks`, first block first. -/
def selectorsOf (B : Blocks) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) : List ℕ :=
  (List.finRange B.n).map fun b ↦ (B.selector hμ b).val

/-! ## The small configuration

Column-index order: `mem_0, mem_1, mem_2, cntfin_mem, cntfin_bc, q_flock, table a, table b`. -/

def small : List ℕ := [4, 4, 4, 4, 2, 5, 4, 4]

-- The transcription gives what the pinned Python verifier and the Rust give (offsets.py).
#guard stackOrder small = [5, 0, 1, 2, 3, 6, 7, 4]
#guard stackOffsets small = [32, 48, 64, 80, 128, 0, 96, 112]

/-- The sorted sizes, as a `Blocks`. -/
def smallBlocks : Blocks := blocksOfList [5, 4, 4, 4, 4, 4, 4, 2] (by decide)

#guard (stackOrder small).map (small[·]!) = [5, 4, 4, 4, 4, 4, 4, 2]

theorem smallBlocks_total_le : smallBlocks.total ≤ 2 ^ 8 := by decide

example : smallBlocks.total = 132 := by decide

-- `Blocks.offset` and `Blocks.selector`, block by block, against the pinned verifiers' values.
#guard offsetsOf smallBlocks = [0, 32, 48, 64, 80, 96, 112, 128]
#guard selectorsOf smallBlocks smallBlocks_total_le = [0, 2, 3, 4, 5, 6, 7, 32]

-- Column `i` sits on block `(stackOrder small).idxOf i`; through that map the offsets are
-- leanVM's, column by column.
#guard (List.range 8).map (fun i ↦ (offsetsOf smallBlocks)[(stackOrder small).idxOf i]!) =
  stackOffsets small

/-- The order the blueprint had before finding F17: ties broken with the tables' columns
first. It sorts to the same sizes, so it is the same `Blocks`. -/
def tablesFirst : List ℕ := [5, 6, 7, 0, 1, 2, 3, 4]

#guard tablesFirst.map (small[·]!) = (stackOrder small).map (small[·]!)

-- Near miss: through that map `mem_0` sits at offset 64, not 32, and nothing about the
-- `Blocks` differs: the order of equal sizes lives in the map from columns to blocks only.
#guard (List.range 8).map (fun i ↦ (offsetsOf smallBlocks)[tablesFirst.idxOf i]!) =
  [64, 80, 96, 112, 128, 0, 32, 48]
#guard (List.range 8).map (fun i ↦ (offsetsOf smallBlocks)[tablesFirst.idxOf i]!) ≠
  stackOffsets small

-- The column-index order itself is not largest first, so it is no `Blocks`.
example : ¬ small.Pairwise (· ≥ ·) := by decide

/-! ## The pinned verifier's layout for one admissible announcement

`build_layout(log_memory = 16, taus = (3, 16, 0, 5, 16, 3), kbc = 4)`: 110 columns, 92 of
them committed. The three lists are copied from the output of `offsets.py`. -/

/-- The sizes of the 92 committed columns, in column-index order (the eighteen BLAKE2S limb
columns, global indices 82 to 99, left out). -/
def committedSizes : List ℕ :=
  [16, 16, 16, 16, 4, 11] ++ List.replicate 15 3 ++ List.replicate 15 16 ++
    List.replicate 8 0 ++ List.replicate 15 5 ++ List.replicate 14 16 ++
    List.replicate 9 3 ++ List.replicate 10 3

/-- The global column index of each committed column, in the same order. -/
def committedIndex : List ℕ := List.range 82 ++ (List.range 10).map (· + 100)

/-- Python: "column index of each block". -/
def pyOrder : List ℕ :=
  [0, 1, 2, 3, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 59, 60, 61, 62, 63,
   64, 65, 66, 67, 68, 69, 70, 71, 72, 5, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56,
   57, 58, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 73, 74, 75, 76, 77, 78,
   79, 80, 81, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 36, 37, 38, 39, 40, 41, 42, 43]

/-- Python: "offsets", first block first. -/
def pyOffsets : List ℕ :=
  [0, 65536, 131072, 196608, 262144, 327680, 393216, 458752, 524288, 589824, 655360, 720896,
   786432, 851968, 917504, 983040, 1048576, 1114112, 1179648, 1245184, 1310720, 1376256,
   1441792, 1507328, 1572864, 1638400, 1703936, 1769472, 1835008, 1900544, 1966080, 2031616,
   2097152, 2162688, 2164736, 2164768, 2164800, 2164832, 2164864, 2164896, 2164928, 2164960,
   2164992, 2165024, 2165056, 2165088, 2165120, 2165152, 2165184, 2165216, 2165232, 2165240,
   2165248, 2165256, 2165264, 2165272, 2165280, 2165288, 2165296, 2165304, 2165312, 2165320,
   2165328, 2165336, 2165344, 2165352, 2165360, 2165368, 2165376, 2165384, 2165392, 2165400,
   2165408, 2165416, 2165424, 2165432, 2165440, 2165448, 2165456, 2165464, 2165472, 2165480,
   2165488, 2165496, 2165504, 2165505, 2165506, 2165507, 2165508, 2165509, 2165510, 2165511]

/-- The sorted sizes. -/
def sortedSizes : List ℕ :=
  List.replicate 33 16 ++ [11] ++ List.replicate 15 5 ++ [4] ++ List.replicate 34 3 ++
    List.replicate 8 0

#guard committedSizes.length = 92
#guard (stackOrder committedSizes).map (committedIndex[·]!) = pyOrder
#guard (stackOrder committedSizes).map (committedSizes[·]!) = sortedSizes

/-- The sorted sizes as a `Blocks`. -/
def realBlocks : Blocks := blocksOfList sortedSizes (by decide +kernel)

#guard offsetsOf realBlocks = pyOffsets
#guard realBlocks.total = 2165512
example : realBlocks.total ≤ 2 ^ 22 := by decide +kernel
example : ¬ realBlocks.total ≤ 2 ^ 21 := by decide +kernel

end Probe
```

Output:

```text
(no output)
exit=0
```

### I.3 `values.py`

Command: `python3 -B .claude/reports/blueprint-review/probes/code-layer1/values.py`

```python
"""Probe for task code-layer1, deliverables B.3, B.5, B.6, B.7 and C.

Reference numbers from the pinned leanVM (a386121f), to be compared with Layer 1's Lean
definitions in `ValuesProbe.lean`. Every evaluation below is made by a function of the pinned
Python verifier (`multilinear_eval`, `index_mle`, `eq_eval`, `stack_offsets`, `Placement`),
imported read-only. The bytecode table is built by a line-by-line transcription of the Rust
`bytecode_columns` (crates/lean_vm/src/cpu/layout.rs:229-309) and `stacked_bytecode_table`
(crates/lean_vm/src/leaf.rs:585-604): the Python verifier takes that table as an input file and
has no encoder of its own.

Run:  python3 -B .claude/reports/blueprint-review/probes/code-layer1/values.py
"""

import sys

sys.dont_write_bytecode = True
sys.path.insert(0, "/home/scaraven/Documents/leanEthereum/leanVM/python-verifier")
import verifier as V  # noqa: E402

K, E = V.K, V.E


def limbs(x):
    return (x.c0.value, x.c1.value, x.c2.value)


def gk(i):
    """g^i in K (primitives/field/mod.rs:82, g_pow)."""
    r = K(1)
    for _ in range(i):
        r = r * K(2)
    return r


# ---- the bytecode table ---------------------------------------------------------------
OP = {"xor": gk(0), "mul": gk(1), "set": gk(2), "deref": gk(3), "jump": gk(4), "blake2s": gk(5)}  # tables.rs:95-100


def bytecode_columns(prog):
    """layout.rs:229-309: (opcode, o1, o2, o3, fpc, ffp, extra0, extra1) per instruction."""
    cols = [[] for _ in range(8)]
    for op in prog:
        kind = op[0]
        z = K(0)
        if kind in ("xor", "mul"):
            _, a, b, c = op
            row = [OP[kind], gk(a), gk(b), gk(c), z, z, z, z]
        elif kind == "set":
            _, o, k = op  # k = (c0, c1, c2)
            row = [OP[kind], gk(o), K(k[0]), K(k[1]), K(k[2]), z, z, z]  # :257, :270
        elif kind == "deref":
            _, o1, o2, o3, mode = op
            f_pc = K(1) if mode == "pc" else z  # isa.rs:69-74
            f_fp = K(1) if mode == "fp" else z
            row = [OP[kind], gk(o1), gk(o2), gk(o3), f_pc, f_fp, z, z]
        elif kind == "jump":
            _, oc, od, of = op
            row = [OP[kind], gk(oc), gk(od), gk(of), z, z, z, z]
        elif kind == "blake2s":
            _, ins, cv, out, md = op
            row = [OP[kind], gk(ins[0]), gk(ins[1]), gk(ins[2]), gk(ins[3]), gk(cv), gk(out), gk(md)]
        for c in range(8):
            cols[c].append(row[c])
    return cols


def stacked_bytecode_table(cols, kbc):
    """leaf.rs:585-604: column i at slot 3 + i, `table[(slot << kbc)..((slot+1) << kbc)]`."""
    table = [K(0)] * (1 << (4 + kbc))
    for i, vals in enumerate(cols):
        slot = 3 + i
        assert len(vals) == 1 << kbc
        table[(slot << kbc):((slot + 1) << kbc)] = vals
    return table


PAD = ("set", 0, (0, 0, 0))  # lean_compiler/src/lib.rs:162
prog = [
    ("xor", 1, 2, 3),
    ("mul", 4, 5, 6),
    ("set", 7, (11, 12, 13)),
    ("deref", 8, 9, 10, "pc"),
    ("deref", 21, 22, 23, "fp"),
    ("deref", 24, 25, 26, "cell"),
    ("jump", 27, 28, 29),
    ("blake2s", (14, 15, 16, 17), 18, 19, 20),
] + [PAD] * 8
kbc = 4
table = stacked_bytecode_table(bytecode_columns(prog), kbc)
print("== bytecode table, 16 instructions, 256 cells (cell i + 16*s holds slot s of instruction i)")
print([w.value for w in table])

zeta = (E(3, 1, 0), E(5, 0, 7), E(2, 2, 2), E(0, 1, 0))
alpha = (E(9, 0, 1), E(0, 4, 0), E(6, 6, 0), E(1, 2, 3))
print("== bytecode multilinear at (zeta, alpha), as verifier.py:566 evaluates it")
print(limbs(V.multilinear_eval(table, (*zeta, *alpha))))
print("== with alpha reversed")
print(limbs(V.multilinear_eval(table, (*zeta, *reversed(alpha)))))

# ---- the index column ----------------------------------------------------------------
print("== index_mle at zeta (4 variables) and at its first 2 coordinates")
print(limbs(V.index_mle(zeta)), limbs(V.index_mle(zeta[:2])))
print("== the MLE of [g^0 .. g^15] at zeta, by multilinear_eval")
print(limbs(V.multilinear_eval([gk(i) for i in range(16)], zeta)))

# ---- stacking: selectors, the zero-padded and the one-padded stack ----------------------
sizes = [2, 1, 0]
tables = [[1, 2, 3, 4], [5, 6], [7]]
offsets, mu = V.stack_offsets(sizes)
print("== blocks of sizes 2, 1, 0: offsets", offsets, "mu", mu)
z3 = zeta[:3]
placements = [V.Placement(k, off) for k, off in zip(sizes, offsets)]
sel = [p.eq_above(z3) for p in placements]
print("eq(sel_b, zeta_hi) per block:", [limbs(s) for s in sel])
blocks_at = [V.multilinear_eval([K(v) for v in t], z3[:k]) for t, k in zip(tables, sizes)]
print("block b at zeta_lo:", [limbs(b) for b in blocks_at])
covered = E.sum(s * b for s, b in zip(sel, blocks_at))
ones_padding = E.sum(sel) + V.ONE  # verifier.py:589
print("covered part:", limbs(covered), " ones padding:", limbs(ones_padding))
stack0 = [K(v) for v in [1, 2, 3, 4, 5, 6, 7, 0]]
stack1 = [K(v) for v in [1, 2, 3, 4, 5, 6, 7, 1]]
print("zero-padded stack at zeta:", limbs(V.multilinear_eval(stack0, z3)))
print("one-padded stack at zeta :", limbs(V.multilinear_eval(stack1, z3)))
assert V.multilinear_eval(stack0, z3) == covered
assert V.multilinear_eval(stack1, z3) == covered + ones_padding

# ---- a column claim as a weight on the stack (verifier.py:520-522) -------------------------
point = (E(3, 1, 0),)  # a claim on block 1 (size 1)
lifted = placements[1].stack_point(point, mu)
print("== claim on block 1 at", [limbs(p) for p in point], "lifts to", [limbs(p) for p in lifted])
kernel = V.eq_kernel(lifted)
print("weight eq(lifted, .) on the cube paired with the arbitrary stack [9,8,7,6,5,4,3,2]:")
arbitrary = [K(v) for v in [9, 8, 7, 6, 5, 4, 3, 2]]
print(limbs(V.dot(arbitrary, kernel)), "  block 1 of it, [5,4], at the point:", limbs(V.multilinear_eval([K(5), K(4)], point)))
r = (E(1, 1, 0), E(0, 2, 0), E(7, 0, 0))
print("the weight's extension at r, eq_eval(lifted, r):", limbs(V.eq_eval(lifted, r)))

# ---- back-loaded padding (verifier.py:609-614) -------------------------------------------
# a table on 1 variable in a sumcheck on 3: the summand's weight at the final point carries
# `challenge` for each variable the table lacks.
print("== back-loaded padding: [3,5] lifted by two variables, at (7 | 11, 13) over K-embedded points")
pt = (E(7), E(11), E(13))
short = V.multilinear_eval([K(3), K(5)], pt[:1])
print("table at 7 times 11*13:", limbs(short * pt[1] * pt[2]))
print("MLE of [0,0,0,0,0,0,3,5] at the point:", limbs(V.multilinear_eval([K(v) for v in [0, 0, 0, 0, 0, 0, 3, 5]], pt)))
```

Output:

```text
== bytecode table, 16 instructions, 256 cells (cell i + 16*s holds slot s of instruction i)
[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 8, 8, 16, 32, 4, 4, 4, 4, 4, 4, 4, 4, 2, 16, 128, 256, 2097152, 16777216, 134217728, 16384, 1, 1, 1, 1, 1, 1, 1, 1, 4, 32, 11, 512, 4194304, 33554432, 268435456, 32768, 0, 0, 0, 0, 0, 0, 0, 0, 8, 64, 12, 1024, 8388608, 67108864, 536870912, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 1, 0, 0, 0, 131072, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 262144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 524288, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1048576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
== bytecode multilinear at (zeta, alpha), as verifier.py:566 evaluates it
(1219889995492, 3571792677380, 1279835512890)
== with alpha reversed
(1332010270628, 4168742050444, 1982034182034)
== index_mle at zeta (4 variables) and at its first 2 coordinates
(950617, 874814, 877803) (109, 29, 108)
== the MLE of [g^0 .. g^15] at zeta, by multilinear_eval
(950617, 874814, 877803)
== blocks of sizes 2, 1, 0: offsets [0, 4, 6] mu 3
eq(sel_b, zeta_hi) per block: [(3, 2, 2), (6, 8, 8), (2, 26, 30)]
block b at zeta_lo: [(46, 11, 42), (0, 3, 0), (7, 0, 0)]
covered part: (38, 3, 34)  ones padding: (6, 16, 20)
zero-padded stack at zeta: (38, 3, 34)
one-padded stack at zeta : (32, 19, 54)
== claim on block 1 at [(3, 1, 0)] lifts to [(3, 1, 0), (0, 0, 0), (1, 0, 0)]
weight eq(lifted, .) on the cube paired with the arbitrary stack [9,8,7,6,5,4,3,2]:
(6, 1, 0)   block 1 of it, [5,4], at the point: (6, 1, 0)
the weight's extension at r, eq_eval(lifted, r): (9, 18, 0)
== back-loaded padding: [3,5] lifted by two variables, at (7 | 11, 13) over K-embedded points
table at 7 times 11*13: (1935, 0, 0)
MLE of [0,0,0,0,0,0,3,5] at the point: (1935, 0, 0)
```

### I.4 `ValuesProbe.lean`

Command: `flock .claude/reports/blueprint-review/logs/lean.lock lake env lean .claude/reports/blueprint-review/probes/code-layer1/ValuesProbe.lean`

```lean
/-
  Probe for task code-layer1, deliverables B.3, B.5, B.6, B.7 and C.

  Layer 1's definitions evaluated against numbers produced by the pinned leanVM: every
  expected value below is copied from the output of `values.py`, which calls the pinned Python
  verifier's own functions (and, for the bytecode table, a transcription of the Rust encoder).

  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/code-layer1/ValuesProbe.lean
-/
import LeanerVM.Protocol.FixedColumns
import LeanerVM.Protocol.Stack
import LeanerVM.Protocol.Padding
import LeanerVM.Protocol.ClaimWeights
import LeanerVM.Protocol.BlockClaims

open LeanerVM.Protocol LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open CompPoly CMlPolynomialEval

namespace Probe

/-- The oracle's answer, as a function `#guard` can evaluate. -/
def answer {n : ℕ} (q : Column n) (z : Vector E n) : E := OracleInterface.answer q z

/-- The point `ζ` of `values.py`. -/
def zeta : Vector E 4 := #v[E.ofLimbs 3 1 0, E.ofLimbs 5 0 7, E.ofLimbs 2 2 2, E.ofLimbs 0 1 0]

/-- The point `α` of `values.py`. -/
def alpha : Vector E 4 := #v[E.ofLimbs 9 0 1, E.ofLimbs 0 4 0, E.ofLimbs 6 6 0, E.ofLimbs 1 2 3]

/-- `α` with its coordinates reversed. -/
def alphaRev : Vector E 4 := #v[E.ofLimbs 1 2 3, E.ofLimbs 6 6 0, E.ofLimbs 0 4 0, E.ofLimbs 9 0 1]

/-! ## B.6 The bytecode column -/

/-- Sixteen instructions: the six opcodes, the three `DEREF` modes, distinct operands, and the
compiler's padding instruction `SET_CONSTANT [g^0] 0` in the last eight cells, the last index
(the halting address) included. Operand `a` of the Rust is the field element `g^a` here. -/
def prog16 : Program where
  logSize := 4
  logSize_le := by decide
  code i := match i.val with
    | 0 => .xor (gpow 1) (gpow 2) (gpow 3)
    | 1 => .mulNative (gpow 4) (gpow 5) (gpow 6)
    | 2 => .setConstant (gpow 7) (E.ofLimbs 11 12 13)
    | 3 => .deref (gpow 8) (gpow 9) (gpow 10) .pc
    | 4 => .deref (gpow 21) (gpow 22) (gpow 23) .fp
    | 5 => .deref (gpow 24) (gpow 25) (gpow 26) .cell
    | 6 => .jump (gpow 27) (gpow 28) (gpow 29)
    | 7 => .blake2s ![gpow 14, gpow 15, gpow 16, gpow 17] (gpow 18) (gpow 19) (gpow 20)
    | _ => .setConstant (gpow 0) 0

/-- The table the transcription of `bytecode_columns` and `stacked_bytecode_table` gives. -/
def pyTable : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 8, 8, 16, 32, 4, 4, 4, 4, 4, 4, 4, 4, 2, 16, 128, 256, 2097152, 16777216, 134217728, 16384, 1, 1, 1, 1, 1, 1, 1, 1, 4, 32, 11, 512, 4194304, 33554432, 268435456, 32768, 0, 0, 0, 0, 0, 0, 0, 0, 8, 64, 12, 1024, 8388608, 67108864, 536870912, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 1, 0, 0, 0, 131072, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 262144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 524288, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1048576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

#guard pyTable.length = 256
-- All 256 cells: the encoding, the opcode values, the slot order and the cell order.
#guard (bytecodeColumn prog16).values.toList.map (·.toNat) = pyTable

/-- The oracle's answer at `(ζ, α)`. -/
def bcAnswer : E := answer (bytecodeColumn prog16) (zeta ++ alpha)

-- The evaluation the pinned verifier makes (`verifier.py:566`), and the native evaluator.
#guard bcAnswer = E.ofLimbs 1219889995492 3571792677380 1279835512890
#guard bytecodeColumnEval prog16 zeta alpha = E.ofLimbs 1219889995492 3571792677380 1279835512890
-- Near miss: with `α` reversed the pinned verifier gets another value, and so does the oracle.
#guard answer (bytecodeColumn prog16) (zeta ++ alphaRev) =
  E.ofLimbs 1332010270628 4168742050444 1982034182034
#guard bcAnswer ≠ E.ofLimbs 1332010270628 4168742050444 1982034182034

/-- The opposite layout: slot bits low, instruction bits high. -/
def wrongColumn (prog : Program) : Column (4 + prog.logSize) :=
  ⟨Vector.ofFn fun i ↦
    let p := (cubeSplit 4 prog.logSize).symm i
    (encodeSlots (prog.code p.2))[p.1]⟩

/-- The analogue of `bytecodeColumn_slot` for the opposite layout, by the same proof script:
the *shape* of that theorem holds of either layout. -/
theorem wrongColumn_slot (prog : Program) (i : Fin (2 ^ prog.logSize)) (s : Fin 16) :
    (wrongColumn prog).values[cubeIndex (k := 4) s i] = (encodeSlots (prog.code i))[s] := by
  simp [wrongColumn, ← cubeSplit_apply]

-- The statement of `bytecodeColumn_slot` itself, word for word, is false of the opposite
-- layout: cell `0 + 16 * 3` is instruction 0's opcode there, and slot 0 of instruction 3 here.
#guard (bytecodeColumn prog16).values.toList[48]! = Opcode.xor.code
#guard (wrongColumn prog16).values.toList[48]! = 0
#guard (wrongColumn prog16).values.toList.map (·.toNat) ≠ pyTable

/-- What the bus phase needs and Layer 1 does not state: the program's share of a bytecode
block is one evaluation of the bytecode column, the slots weighted by `eq(w, ·)`. -/
theorem bytecodeColumn_answer_slots (prog : Program) (z : Vector E prog.logSize)
    (w : Vector E 4) :
    eval₂Mle (bytecodeColumn prog).values (algebraMap K E) (z ++ w) =
      ∑ s : Fin 16, (lagrangeBasis w)[s] *
        eval₂Mle (bytecodeSlotColumn prog s).values (algebraMap K E) z := by
  rw [eval₂Mle, evalMle_split]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  congr 1
  rw [eval₂Mle, ← slice_bytecodeColumn]
  congr 1
  apply Vector.ext
  intro i hi
  simp [slice, CMlPolynomialEval.map]

/-! ## B.5 The index column -/

#guard answer (idxColumn 4) zeta = E.ofLimbs 950617 874814 877803
#guard idxColumnEval zeta = E.ofLimbs 950617 874814 877803
#guard idxColumnEval (#v[E.ofLimbs 3 1 0, E.ofLimbs 5 0 7] : Vector E 2) = E.ofLimbs 109 29 108
#guard (idxColumn 4).values.toList.map (·.toNat) = (List.range 16).map (2 ^ ·)

/-! ## B.2, B.3 Selectors and the two paddings -/

/-- Blocks on 2, 1 and 0 variables. -/
def blocks : Blocks where
  n := 3
  size := ![2, 1, 0]
  descending := by
    show ∀ a b : Fin 3, a ≤ b → ![2, 1, 0] b ≤ ![2, 1, 0] a
    decide

theorem blocks_total_le : blocks.total ≤ 2 ^ 3 := by decide

/-- The tables `[1, 2, 3, 4]`, `[5, 6]`, `[7]`. -/
def tables : blocks.Tables K :=
  show (b : Fin 3) → CMlPolynomialEval K (![2, 1, 0] b) from fun b ↦ match b with
    | 0 => (#v[1, 2, 3, 4] : CMlPolynomialEval K 2)
    | 1 => (#v[5, 6] : CMlPolynomialEval K 1)
    | 2 => (#v[7] : CMlPolynomialEval K 0)

/-- The tables over `E`. -/
def tablesE : blocks.Tables E := fun b ↦ CMlPolynomialEval.map (algebraMap K E) (tables b)

/-- The first three coordinates of `ζ`. -/
def z3 : Vector E 3 := #v[E.ofLimbs 3 1 0, E.ofLimbs 5 0 7, E.ofLimbs 2 2 2]

/-- The selector weights, block by block. -/
def weights : List E := (List.finRange 3).map fun b ↦ blocks.selectorWeight blocks_total_le b z3

/-- The blocks at the low coordinates, block by block. -/
def blocksAt : List E := (List.finRange 3).map fun b ↦
  eval₂Mle (tables b) (algebraMap K E) (blocks.lowPoint blocks_total_le b z3)

-- `eq(sel_b, ζ_hi)` as `Placement.eq_above` computes it (`verifier.py:299-302`).
#guard weights = [E.ofLimbs 3 2 2, E.ofLimbs 6 8 8, E.ofLimbs 2 26 30]
#guard blocksAt = [E.ofLimbs 46 11 42, E.ofLimbs 0 3 0, E.ofLimbs 7 0 0]
-- The witness stack (pad 0) and a leaf stack (pad 1) at `ζ`.
#guard eval₂Mle (blocks.stackColumn tables 3).values (algebraMap K E) z3 = E.ofLimbs 38 3 34
#guard evalMle (blocks.stackAt tablesE 3 1) z3 = E.ofLimbs 32 19 54
-- The padding term of equation (2), `1 + Σ_b eq(sel_b, ζ_hi)` (`verifier.py:589`).
#guard 1 + weights.sum = E.ofLimbs 6 16 20
#guard (List.zipWith (· * ·) weights blocksAt).sum + (1 + weights.sum) = E.ofLimbs 32 19 54
-- Near misses: the wrong pad, and the padding term read as the constant 1.
#guard evalMle (blocks.stackAt tablesE 3 0) z3 ≠ E.ofLimbs 32 19 54
#guard (List.zipWith (· * ·) weights blocksAt).sum + 1 ≠ E.ofLimbs 32 19 54

/-! ## B.7 A column claim as a weight -/

/-- The claim's point on block 1, lifted. -/
def lifted : Vector E 3 := blocks.extendPoint blocks_total_le (1 : Fin 3) #v[E.ofLimbs 3 1 0]

/-- A stack no honest prover commits. -/
def arbitrary : Column 3 := ⟨#v[9, 8, 7, 6, 5, 4, 3, 2]⟩

#guard lifted = #v[E.ofLimbs 3 1 0, 0, 1]
#guard (eqWeight lifted).pair arbitrary = E.ofLimbs 6 1 0
#guard (eqWeight lifted).mle #v[E.ofLimbs 1 1 0, E.ofLimbs 0 2 0, E.ofLimbs 7 0 0] =
  E.ofLimbs 9 18 0
-- Near miss: the selector bits reversed, `(1, 0)`, weigh cells 2 and 3.
#guard (eqWeight (#v[E.ofLimbs 3 1 0, 1, 0] : Vector E 3)).pair arbitrary ≠ E.ofLimbs 6 1 0

/-! ## B.4 Back-loaded padding -/

/-- The table `[3, 5]` on one variable. -/
def short : CMlPolynomialEval K 1 := #v[3, 5]

#guard evalMle (padHigh short 2) ((#v[7] : Vector K 1) ++ (#v[11, 13] : Vector K 2)) = 1935
#guard (padHigh short 2).toList = [0, 0, 0, 0, 0, 0, 3, 5]
-- Near miss: padding on the low variables (front-loaded) is another table.
#guard (padHigh short 2).toList ≠ [0, 0, 0, 3, 0, 0, 0, 5]

/-! ## C A layout need not separate its columns -/

/-- Three columns all read off block 0: `Layout.comap` asks nothing of the renaming. -/
def aliased : Layout 3 (Fin 3) (fun _ ↦ 2) :=
  (blocks.layout blocks_total_le).comap (fun _ ↦ (0 : Fin 3)) (fun _ ↦ rfl)

#guard (List.finRange 3).all fun c ↦ (aliased.read arbitrary c).values.toList = [9, 8, 7, 6]

/-! ## Axioms -/

#print axioms Blocks.unstack_eval₂
#print axioms Blocks.unstack_getElem
#print axioms Blocks.readColumn_eval
#print axioms Blocks.layout
#print axioms Layout.comap
#print axioms Blocks.stack_eval_ambient
#print axioms Blocks.stack_eval_ambient_one
#print axioms Blocks.stackColumn_eval_ambient
#print axioms sumCube_padHigh
#print axioms evalMle_padHigh
#print axioms ColumnClaim.holds_iff_weighted
#print axioms eqWeight
#print axioms idxColumn_eval
#print axioms idxColumnEval_eq
#print axioms bytecodeColumn_answer_boolVec
#print axioms bytecodeColumn_eval
#print axioms BlockClaim.isValid_iff_pairing
#print axioms bytecodeColumn_answer_slots

end Probe
```

Output:

```text
'LeanerVM.Protocol.Blocks.unstack_eval₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Blocks.unstack_getElem' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Blocks.readColumn_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Blocks.layout' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Layout.comap' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Blocks.stack_eval_ambient' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Blocks.stack_eval_ambient_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Blocks.stackColumn_eval_ambient' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.sumCube_padHigh' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.evalMle_padHigh' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.ColumnClaim.holds_iff_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.eqWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.idxColumn_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.idxColumnEval_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.bytecodeColumn_answer_boolVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.bytecodeColumn_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.BlockClaim.isValid_iff_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.bytecodeColumn_answer_slots' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

### I.5 `DuplicatesProbe.lean`

Command: `LEAN_PATH=… flock … leanprover--lean4---v4.33.1/bin/lean .claude/reports/blueprint-review/probes/code-layer1/DuplicatesProbe.lean`

```lean
/-
  Probe for task code-layer1, deliverables D and E: which Layer 1 statements are already in
  CompPoly at the pin (3468b38c), and which are instances of one another.

  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/code-layer1/DuplicatesProbe.lean
-/
import LeanerVM.Protocol.ToCompPoly.BitProductTable
import LeanerVM.Protocol.ToCompPoly.AmbientStacking

open LeanerVM.Protocol CompPoly CMlPolynomialEval

namespace Probe

variable {R : Type*} [CommRing R]

/-- `evalMle_lagrangeBasis` is CompPoly's `eqTilde_eq_prod` (`Multilinear/Basic.lean:600`),
with the factors written in the other order. -/
example {n : ℕ} (w x : Vector R n) :
    evalMle (lagrangeBasis w) x = ∏ k : Fin n, ((1 - x[k]) * (1 - w[k]) + x[k] * w[k]) := by
  have h := eqTilde_eq_prod w x
  rw [eqTilde, ← eval_mle_eq_eval] at h
  rw [h]
  exact Finset.prod_congr rfl fun i _ ↦ by ring

/-- `unstack_eval` is `unstack_eval₂` at the identity map. -/
example (B : Blocks) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (q : CMlPolynomialEval R μ) (b : Fin B.n)
    (z : Vector R (B.size b)) :
    evalMle q (B.extendPoint hμ b z) = evalMle (B.unstack hμ q b) z := by
  have h := B.unstack_eval₂ (RingHom.id R) hμ q b z
  simpa [eval₂Mle, CMlPolynomialEval.map] using h

/-- `stack_eval` is `unstack_eval` on a stack. -/
example (B : Blocks) (t : B.Tables R) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (pad : R) (b : Fin B.n)
    (z : Vector R (B.size b)) :
    evalMle (B.stackAt t μ pad) (B.extendPoint hμ b z) = evalMle (t b) z := by
  rw [B.unstack_eval hμ, B.unstack_stackAt]

/-- `stack_eval_ambient_zero` is `stack_eval_ambient` at pad zero. -/
example (B : Blocks) (t : B.Tables R) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) (z : Vector R μ) :
    evalMle (B.stackAt t μ 0) z =
      ∑ b : Fin B.n, B.selectorWeight hμ b z * evalMle (t b) (B.lowPoint hμ b z) := by
  simpa using B.stack_eval_ambient t hμ 0 z

/-- The largest-first order is sufficient for alignment, not necessary: sizes 1, 1, 2 are
aligned at offsets 0, 2, 4 and are no `Blocks`. -/
example : ¬ Antitone (![1, 1, 2] : Fin 3 → ℕ) := fun h ↦
  absurd (h (show (0 : Fin 3) ≤ 2 by decide)) (by decide)

#guard (2 ^ 1 ∣ 0) ∧ (2 ^ 1 ∣ 2) ∧ (2 ^ 2 ∣ 4)

end Probe
```

Output:

```text
(no output)
exit=0
```

### I.6 `StridedProbe.lean`

Command: `LEAN_PATH=… flock … leanprover--lean4---v4.33.1/bin/lean .claude/reports/blueprint-review/probes/code-layer1/StridedProbe.lean`

```lean
/-
  Probe for task code-layer1, deliverable C and the findings: the selection identity Layer 1
  does not have. leanVM reads the eighteen BLAKE2S limb columns off `q_flock` by freezing the
  LOW coordinates to a slot's bits (`crates/pcs/src/stack_open.rs:84-97`, `StackClaim::Strided`:
  "Equivalent to a `Point` with `low_point = slot_bits ++ point`"). Layer 1 slices on the high
  index only. This file states and proves the mirrored identity, to show what is missing and
  that it is a generic fact of the same size as `evalMle_append_boolVec`.

  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/code-layer1/StridedProbe.lean
-/
import LeanerVM.Protocol.ToCompPoly.Multilinear
import LeanerVM.Parameters.Field

open LeanerVM.Protocol LeanerVM.Parameters CompPoly CMlPolynomialEval

namespace Probe

variable {R : Type*} [CommRing R]

/-- The strided slice of a table at the low index `i`: the entries whose low `k` bits are `i`. -/
def sliceLow {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (i : Fin (2 ^ k)) :
    CMlPolynomialEval R m :=
  Vector.ofFn fun j ↦ t[cubeIndex i j]

/-- A Boolean low coordinate selects the strided slice at that index. -/
theorem evalMle_boolVec_append {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (i : Fin (2 ^ k))
    (s : Vector R m) :
    evalMle t ((boolVec i : Vector R k) ++ s) = evalMle (sliceLow t i) s := by
  rw [evalMle_eq_sum, sum_cube_split, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_eq_single i]
  · rw [lagrangeBasis_cubeIndex, lowVec_append, highVec_append]
    have h := lagrangeBasis_boolVec (R := R) i i
    simp only [if_true] at h
    simp only [Fin.getElem_fin] at h ⊢
    rw [h, one_mul]
    simp [sliceLow]
  · intro i' _ hi
    rw [lagrangeBasis_cubeIndex, lowVec_append, highVec_append]
    have h := lagrangeBasis_boolVec (R := R) i i'
    simp only [if_neg hi] at h
    simp only [Fin.getElem_fin] at h ⊢
    rw [h, zero_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Slot 1 of four (two low bits) of an eight-cell table: cells 1 and 5. -/
def packed : CMlPolynomialEval K 3 := #v[10, 11, 12, 13, 20, 21, 22, 23]

#guard (sliceLow (k := 2) (m := 1) packed (1 : Fin 4)).toList = [11, 21]
-- The point `(slot bits 1, 0 | z)` reads the strided slice at `z`.
#guard evalMle packed (#v[1, 0, 7] : Vector K 3) =
  evalMle (#v[11, 21] : CMlPolynomialEval K 1) #v[7]
-- Near miss: the aligned slice at high index 1 is cells 2 and 3, another column.
#guard (slice (k := 1) (m := 2) packed (1 : Fin 4)).toList = [12, 13]

#print axioms evalMle_boolVec_append

end Probe
```

Output:

```text
'Probe.evalMle_boolVec_append' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

What each Lean probe establishes, in one line: `OffsetsProbe`, that `Blocks.offset` and
`Blocks.selector` on sorted sizes reproduce leanVM's offsets once the columns are mapped by
leanVM's order, and that the tables-first order gives the same `Blocks` and other offsets (B.2);
`ValuesProbe`, that the index column, the bytecode column (256 cells and the `(ζ, α)`
evaluation), the selector weights, both paddings, the column-claim weight and back-loaded padding
agree with the pinned Python's numbers, with their near misses, that `bytecodeColumn_slot`'s
proof also proves the opposite layout's analogue, that `Layout.comap` aliases, and the axioms of
seventeen Layer 1 declarations and of the probe's `bytecodeColumn_answer_slots` (B.3-B.7, C.3,
C.4); `DuplicatesProbe`, that `evalMle_lagrangeBasis` is
CompPoly's `eqTilde_eq_prod`, three in-layer duplicates, and that largest-first is not necessary
for alignment (D.2, G.5); `StridedProbe`, that the low-index selection identity holds and is
twenty lines from Layer 1's lemmas (B.8, G.1).

### I.7 The counting script of section E (`count2.py`, scratch, not a probe)

Command: `python3 -B count2.py`

```python
import re, subprocess, json
files = ["LeanerVM/Protocol/ToCompPoly/Multilinear.lean","LeanerVM/Protocol/ToCompPoly/BitProductTable.lean",
 "LeanerVM/Protocol/ToCompPoly/Stacking.lean","LeanerVM/Protocol/ToCompPoly/AmbientStacking.lean",
 "LeanerVM/Protocol/Stack.lean","LeanerVM/Protocol/Padding.lean","LeanerVM/Protocol/ClaimWeights.lean",
 "LeanerVM/Protocol/BlockClaims.lean","LeanerVM/Protocol/FixedColumns.lean"]
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(private\s+)?(def|theorem|abbrev|structure|lemma)\s+(\S+)')
tot = {}
for f in files:
    src = subprocess.run(["git","show","b435631:"+f],capture_output=True,text=True,cwd="/home/scaraven/Documents/Verified-zkEVM/leanerVM").stdout.split("\n")
    rows=[]
    for i,l in enumerate(src):
        m = decl.match(l)
        if not m or m.group(1): continue
        kind=m.group(2); name=m.group(3)
        j=i; n=0
        if kind in ("def","abbrev","structure"):
            while j < len(src) and src[j].strip()!="":
                n+=1; j+=1
        else:
            while True:
                n+=1
                if ':=' in src[j]: break
                j+=1
        k=i-1; doc=0
        while k>=0 and src[k].startswith('omit'): k-=1
        if k>=0 and src[k].rstrip().endswith('-/'):
            while k>=0:
                doc+=1
                if src[k].lstrip().startswith('/--'): break
                k-=1
        rows.append((i+1,kind,name,n,doc))
    tot[f]=rows
    print(f, len(rows), sum(r[3] for r in rows), sum(r[3]+r[4] for r in rows))
json.dump(tot, open("decls2.json","w"))
```

Output:

```text
LeanerVM/Protocol/ToCompPoly/Multilinear.lean 43 98 137
LeanerVM/Protocol/ToCompPoly/BitProductTable.lean 13 30 39
LeanerVM/Protocol/ToCompPoly/Stacking.lean 38 108 147
LeanerVM/Protocol/ToCompPoly/AmbientStacking.lean 10 35 48
LeanerVM/Protocol/Stack.lean 9 34 46
LeanerVM/Protocol/Padding.lean 6 12 20
LeanerVM/Protocol/ClaimWeights.lean 4 12 18
LeanerVM/Protocol/BlockClaims.lean 8 30 40
LeanerVM/Protocol/FixedColumns.lean 12 29 44
```
(columns: public declarations, statement lines, statement lines with docstrings; the split by class uses the lists of section A.)

## J. Not done, unverified, and contradictions with the brief

- **Unverified: the Rust encoder was not executed.** The bytecode table `ValuesProbe` compares
  against is built by `values.py`'s transcription of `bytecode_columns` and
  `stacked_bytecode_table`, checked by reading against `cpu/layout.rs:229-309` and
  `leaf.rs:585-604` (B.6). Running the pinned Rust `bytecode_table` on the same program and
  comparing would verify it.
- **Unverified: the proposed strided reader and layout combinator** (G.1) are sketched, not built;
  only the selection lemma is proved (`StridedProbe`).
- **Not run at the new pin.** No probe was run against `144c5aa`; `ValuesProbe` and
  `StridedProbe` need their `K` numerals rewritten first (H). The conclusions are about
  `b435631` and the old pins, which is the review's object (brief §8).
- **How two Lean probes ran** (I): `DuplicatesProbe` and `StridedProbe` were run with the old pin's
  Lean binary and `LEAN_PATH` on the untouched `b435631` artefacts, not with `lake env lean`,
  because the checkout had moved; this was before the instruction to stop running Lean reached me.
  If the orchestrator discounts them, D.2's duplicate claims and B.8's lemma stand as short proofs
  on paper (a three-line rewrite with `eqTilde_eq_prod`; the mirror of `evalMle_append_boolVec`).
- **Contradiction with the brief's §2** (not of my making): the leanerVM checkout was moved during
  this task (reflog in I), and `.lake/packages/` switched to the new pins; the coordinator's resume
  message ("nothing else changed") predates it. I moved no checkout, ran no build, and wrote only
  under `.claude/reports/blueprint-review/` (the dossier and the six `*.out` files).
- **Facts of sibling dossiers used, and checked where I read the same lines**: the tie order and
  the six shared columns first (`gt-bus.md` A.5, G7; I read `witness.rs:63-102` and
  `cpu/layout.rs:9-49`); the leaf stacks' pad `1` and no floor (`gt-bus.md` A.5; not re-read); the
  limb columns as strided slots of `q_flock` (`gt-flock-ring.md` 2.4, 5.4; I read
  `stack_open.rs:73-98`, `hash_flock.rs:82-115`, `py:878-895`); the table sumcheck binds the
  highest variable first and pads by the product of the high variables (`gt-table-pub.md`; I read
  `constraints.rs:250-290`, `py:598-626`). All agree with what I read. Nothing in the brief's §7
  is contradicted by this task's sources.
- **Not examined**: the rest of the blueprint's Layer 3 (beyond the lines that touch Layer 1), the
  leaf stacks' block order in code (not built), the pad cells of the committed stack past the last
  lane (`witness.rs:41-60`; no Layer 1 statement concerns them).
