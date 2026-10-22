# Review: the novel basis, the Reed–Solomon encoder and the column weights (PR #103)

Adversarial review of branch `review/whir-103` (the head of pull request #103 by @aryaethn with
`origin/main` `9595721` merged in, merge commit `aeea51a`), run on 2026-10-19 with the three passes
of the `adversarial-review` skill, against the pinned leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`
read first (Annex B `app:ntt`, `def:enc`, `lem:subspace`, `lem:colweight`;
`crates/pcs/src/ntt/additive_ntt_f64.rs:12-69`; `python-verifier/verifier.py:962-989`), then the
Lean, with #67's `Parameters/Whir.lean` beside it for the fit. Every claim below was executed before
it was written down; the probe files are named at the end.

**Disposition**:

| Finding | Disposition | Commit |
| --- | --- | --- |
| 1. the column weight's extension is not evaluable at a deployed size | met: roots in one pass (`rootsFrom`, `subspaceRoots`), the table's factors computed once, the extension `columnWeightMle`; at `κ = 22` it takes 0.7 s in the interpreter. `Weight.onCube` as data is taken up by #110, which makes every weight's table lazy | `0d05112` |
| 2. no vector at a deployed size | met: the roots to stage 30 and the extension at `(22, 1)`, `(9, 1)`, `(16, 4)`, `(6, 19)`, `(2, 16)` against the pinned verifier | `0d05112` |
| 3. the encoder's distance is not stated | met: `encode_eq_of_agree` (needs `κ + R ≤ 64`), `encode_injective` its corollary at the first `2 ^ κ` positions, `encode_eq_eval`; a test shows the distance attained | `0d05112` |
| 4. the generic half duplicates CompPoly | met by the docstring option: the module names each CompPoly counterpart and why it is restated; the port to `ToCompPoly/` with bridge lemmas is put to the maintainer | `0d05112` |
| 5. `encode_columnWeight` is a definition restated | met: its docstring says the identity is definitional and points to `encode_eq_sum`, `eval_novelPoly`, `encode_eq_eval` | `0d05112` |
| 6. stages past the field's dimension are silently zero | met: `subspaceRoot`'s docstring and the guard `subspaceRoot 63 ≠ 0 ∧ subspaceRoot 64 = 0` | `0d05112` |
| 7. documentation and hygiene | met: roadmap references removed, stale sentence fixed (golf `01304b4`); test data wrapped, one classic import; status page on-merge line with the two blueprint edits owed; this review listed in `docs/README.md`; the target named in the pull request body | `01304b4`, `0d05112`, this commit |

## Findings, most severe first

### 1. The column weight's extension is not evaluable at a deployed size (defect, implementation)

`LeanerVM/Protocol/NovelBasis.lean:297-303` with `LeanerVM/Protocol/ToCompPoly/BitProductTable.lean:44-45`.
`columnWeight φ κ R v` is a `Weight` whose `onCube` is
`bitProductTable fun k b ↦ if b then φ (normW k (domainPt v)) else 1`, and `bitProductTable`
is `Vector.ofFn fun i ↦ ∏ k, f k (i.testBit k)`: the closure, hence `normW k (domainPt v)`, is
evaluated once per table entry and per bit, `2^κ · κ` times, each a stage-`k` recursion whose
`subspaceRoot k` rebuilds the layers (quadratic in `k`; the 22 values `normW k (domainPt v)`,
`k < 22`, take 10.2 s in the interpreter). And since a structure is built strictly, reading
`.mle` builds `onCube` first, so the verifier's `O(κ)` evaluation of `lem:colweight` costs the
whole `2^κ` table. Executed, interpreter, on this branch:

- `(columnWeight (algebraMap K E) 22 1 ⟨q, _⟩).mle pt`, the level-0 weight of the largest deployed
  stack (`μ = 28`, `R = 1`, `κ = 22`): killed after 2.5 hours at 3.3 GB resident, no result;
- `(columnWeight (algebraMap K E) 10 1 ⟨5, _⟩).onCube.toList.length`: not finished in 120 s;
- the same extension computed as `∏ k : Fin 22, ((1 - r[k]) + r[k] * algebraMap K E w[k])` with
  `w := (List.range 22).map fun k ↦ normW k (domainPt q)` precomputed: 10.4 s, of which the `E`
  product is negligible (`E(0xdd81a96c…74e2)` at the probe's point);
- the weights at `(κ, R) = (6, 19)` and `(2, 16)` and the encoder at `κ = 4` over all 64
  positions: seconds.

The tests stop at `κ = 8` (`pythonWeights`, `weightAt`), where `2^8 · 8` is cheap, which is why
nothing failed. The theorems are unaffected; the executable is, and `AGENTS.md` treats the Lean
executable as an implementation target: Layer 12's compiled `verify` evaluates `t_i` column
weights per level (223 at level 0) and cannot do so through this definition. Fix, in three parts,
none of which changes a statement:

1. compute the `κ` values once, outside the closure, as the Python does (`verifier.py:983-987`):
   `normWChain (x : K) (κ : ℕ) : Vector K κ` by one pass of `V_{k+1} = V_k (V_k + root_k)` over a
   precomputed `subspaceRoots : Vector K 64` (one pass over the layers), with
   `normWChain_getElem : (normWChain x κ)[k] = normW k x` and `subspaceRoots_getElem`; this also
   removes the quadratic rebuild;
2. a standalone extension `columnWeightMle φ κ R v (r : Vector S κ) : S := ∏ k, ((1 - r[k]) +
   r[k] * φ (chain[k]))`, with `columnWeight`'s field `mle := columnWeightMle φ κ R v`, so a
   consumer that evaluates the extension names `columnWeightMle` and never constructs `onCube`;
   the `mle_eq` field keeps the table and the extension in step;
3. in `tests/LeanerVMTests/Protocol/NovelBasis.lean`, a `#guard` of `columnWeightMle` at
   `(22, 1)`, `(9, 1)` and `(16, 4)` against `_induced_weight`, generated as the existing vectors
   were, so that the cost cannot return.

A fourth option is upstream of this PR: `Weight.onCube : CMlPolynomialEval S n` as data makes
every weight cost `2^n` to construct (`eqWeight` on `main` has the same shape at `n = μ ≤ 28`);
a lazy or functional `onCube` in `ToArkLib/InnerProduct.lean` is a change for the maintainer to
weigh, not this PR. It is now #110: the table is a thunk built on the first sum over the cube, and
once it lands `columnWeight` writes `cube := .mk fun _ ↦ …`.

### 2. No vector at a deployed size (defect in the tests)

`tests/LeanerVMTests/Protocol/NovelBasis.lean:32-82`. The Python vectors are at `κ ∈ {3, 4, 6, 8}`,
`κ + R = 64` in `weightAt`, positions up to `2^64 - 1`; the deployed levels have `κ_0 = μ - 6 ∈
[9, 22]` and `κ_i ∈ [2, 18]` after, with `κ_i + R_i ≤ 26` (#67's `ladder_blocks`, maximum 26 at
level 0 of `(28, 4)`). So no test exercises a level the protocol runs, and finding 1 could not be
seen. Executed by this review against the pinned verifier (`python3 -I`, importing
`verifier.py`): `subspaceRoot k` for `k ≤ 30` against `_subspace_roots(30)`, 31 of 31 equal
(linear cost, 10.7 s for the file); the column weight's extension at random points of `E^κ` at
`(κ, R) ∈ {(6, 19), (2, 16)}` (the last level of `(28, 4)` and a two-variable level), 2 of 2
equal; the full encoder at `κ = 4`, `R = 2` on a random `K` message at all 64 positions,
recomputed in Python from `_induced_weight` at the cube points only
(`Enc(g)[x_v] = Σ_u g(u) · W_{x_v}(u)`), 64 of 64 equal; the `(8, 1)`, `(5, 10)` and
deployed-`κ` weights could not be run (finding 1). Fix: part 3 of finding 1, plus the roots to
stage 26 or more.

### 3. The encoder's distance is not stated (observation, what the opening will need)

`LeanerVM/Protocol/NovelBasis.lean:502-567`, `encode_injective`. Annex B's soundness proof uses
the code's distance, not injectivity: `lem:fold-list` closes with "`|A| ≥ (1 - γ)n > kdim` while
distinct codewords agree on fewer than `kdim` points", and `thm:johnson-general` assumes "two
distinct codewords agree on at most `ρn` coordinates". `encode_injective` says only that distinct
messages differ somewhere, and its proof uses agreement at the *first* `2^κ` positions. The proof
already contains the stronger fact; it should be the statement:

```lean
/-- Two encodings that agree on `2^κ` positions are encodings of one message: the code has
distance `2^(κ+R) - 2^κ + 1` (`thm:johnson-general`'s hypothesis). -/
theorem encode_eq_of_agree {S} [CommRing S] [IsDomain S] (φ : K →+* S) {κ R : ℕ}
    (hκR : κ + R ≤ 64) (hφ : Function.Injective φ) {m m' : CMlPolynomialEval S κ}
    (T : Finset (Fin (2 ^ (κ + R)))) (hT : 2 ^ κ ≤ T.card)
    (h : ∀ v ∈ T, encode φ κ R m v = encode φ κ R m' v) : m = m'
```

with `encode_injective` its corollary at `T = {v | v < 2^κ}`. The hypothesis `κ + R ≤ 64` is where
the two halves of the layer meet: it is what makes every `domainPt v`, `v < 2^(κ+R)`, distinct
(`domainPt_injOn`), and #67's `ladder_blocks` supplies it at every deployed level (since its
second review it states `63`, the Rust's bound, which implies it). Also missing is the plain
identity of `def:enc`, `encode φ κ R m v = (Σ_u C m[u] * (novelPoly κ u).map φ).eval (φ (domainPt
v))`; only its difference form `encode_sub_eq_eval` is stated, and the identity is its `m' = 0`
case once `encode φ κ R 0 v = 0` is noted.

### 4. The generic half duplicates CompPoly (observation, placement)

`LeanerVM/Protocol/NovelBasis.lean:108-176, 385-485`. CompPoly's `Fields/Binary/AdditiveNTT/` at
the pin defines, generically over a binary field `L`, a subfield `𝔽q` and a basis `β`: the span `U
i`, the vanishing polynomial `W i` as the product over `U i` with `degree_W`, `W_monic`,
`Wᵢ_vanishing`, `W₀_eq_X`, `Wᵢ_eval_βᵢ_neq_zero`, `inductive_linear_map_W` (`lem:subspace` (ii))
and `inductive_rec_form_W_comp` (`lem:subspace` (i)) (`NovelPolynomialBasis.lean:75-968`), the
normalization `normalizedW` (`:1143`), the novel basis `Xⱼ` with `degree_Xⱼ` (`:1300-1315`), and
`polynomialFromNovelCoeffs` (`:1550`). The PR re-proves these at `K` and `β = e`:
`subspaceVanish` is `W (ZMod 2) basisElt k`, `subspaceVanish_succ'`/`subspaceVanish_add` are the
two recursion lemmas, `normWPoly` is `normalizedW`, `novelPoly` is `Xⱼ`, `natDegree_novelPoly` is
`degree_Xⱼ`, and the polynomial of `encode_sub_eq_eval` is `polynomialFromNovelCoeffs`. The
instance-specific content is small: `basisElt`, `domainPt`, the executable recursion
`subspaceLayer`/`vanish`/`normW` (Category B, the Python's and the Rust's), the bridge `vanish_eq`,
`basisElt_linearIndependent`, and `columnWeight`.

The brief's question, whether the module should be generic code under `ToCompPoly/` with only the
`K` instantiation here, has a two-part answer. (a) The executable recursion and its bridge are
leanVM's and stay: CompPoly's `W` is noncomputable, and the verifier must run. (b) The polynomial
half, the encoder as evaluation of `polynomialFromNovelCoeffs` on the domain, its linearity, its
injectivity and its distance (finding 3), and the column weight as a tensor (`lem:colweight`), are
generic over CompPoly's `(𝔽q, L, β)` and have a consumer there (the encoder of any additive-NTT
code); they belong in `LeanerVM/Protocol/ToCompPoly/NovelBasisEncoder.lean`, stated against
CompPoly's names, with `NovelBasis.lean` instantiating them through two bridge lemmas,
`normWPoly k = normalizedW (ZMod 2) basisElt ⟨k, _⟩` and `novelPoly κ j = Xⱼ κ _ ⟨j, _⟩`, so that
`natDegree_novelPoly` and `leadingCoeff_novelPoly` are CompPoly's `degree_Xⱼ` and the monicity of
`W` rather than re-proofs. Obstacles to name in the module docstring if (b) is not taken now:
CompPoly's strict `ℓ + R < r` and its `[Fintype L]`, which at `K` is the noncomputable
`Fintype.ofFinite` of `Parameters/Field.lean`. Either way the module docstring should say which of
its declarations CompPoly already has, as the status page's reuse table asks.

### 5. `encode_columnWeight` is a definition restated (observation)

`LeanerVM/Protocol/NovelBasis.lean:305-314`. `encode` is *defined* as `(columnWeight φ κ R
v).pair (RingHom.id S) m`, and `encode_columnWeight` is that definition by `rfl`, docstringed as
"`lem:colweight`, first identity". The content of `lem:colweight` is carried elsewhere:
`encode_eq_sum` with `eval_novelPoly` (the table entry is `X_{⟨u⟩}(x_v)`, so the pairing is
`def:enc`), and `columnWeight`'s `mle_eq` field (the extension's product form). The theorem is
harmless as an API promise, but it is the pattern the brief warns of (an identity that holds by
`rfl` because one side is defined from the other). Fix: either define `encode` as the evaluation
of the novel-basis polynomial (finding 4's generic form) and prove `encode_columnWeight` as the
real identity, or keep the definition and make the docstring say the identity is definitional and
point to `encode_eq_sum`/`eval_novelPoly` for the lemma's content.

### 6. Stages past the field's dimension are silently zero (observation)

`LeanerVM/Protocol/NovelBasis.lean:84-101`. `subspaceLayer k` has 64 entries for every `k`, so
`subspaceRoot 64 = (subspaceLayer 64).getD 64 0 = 0` and `normW 64 x = vanish x 64 / 0 = 0`
(executed: `subspaceRoot 64` prints `0000000000000000`); `columnWeight φ κ R v` at `κ > 64` is a weight
whose factors past stage 63 are the constant `0`/`1` pattern, and `domainPt v` for `v ≥ 2^64` wraps
(`K.ofBits`), so positions alias. No theorem is wrong: each carries `k < 64`, `k ≤ 64` or `κ ≤
64`, and the deployed `κ + R ≤ 26`. But a definition that returns a value where the Annex has none
deserves a sentence in the docstring and a guard, `#guard subspaceRoot 64 = 0`, with the remark
that `encode_injective`'s `κ ≤ 64` is the bound that keeps the stages meaningful.

### 7. Documentation and hygiene

- Roadmap references in Lean comments, which the repository keeps out of source:
  `NovelBasis.lean:23-24` ("Protocol roadmap Layer 11 (`docs/roadmap/protocol-blueprint.md`),
  first slice of the WHIR opening (issue #101)"), `:64-65` ("the blueprint's sketch names this
  basis `novelBasis`"), `:324-325` ("`encode_K` of the blueprint"), `:53-55` (a test file path in
  a production docstring); `tests/…/NovelBasisNtt.lean:193` ("the blueprint's test"). Replace by
  the fact itself (what `basisElt` is, what `encode_map` gives at `ψ = algebraMap K E`).
- `NovelBasis.lean:59-60`: "Not proved here: that `encode` is injective" is stale; the module
  proves it (`:502-567`).
- `tests/…/NovelBasis.lean:34-67`: data lines of 122 to 257 characters; wrap as #67's test tables
  are, one element per line, or move the tables to a `def` per case.
- `tests/…/NovelBasis.lean:10-11`: `public import` plus `meta import` of the same module in a
  test; one line should do (a classic `import`, as the sibling tests use, also lets the kernel
  decide `E` arithmetic).
- `docs/roadmap/protocol-status.md` is untouched; the hole's row and the reuse table's
  `AdditiveNTT` line ("instantiated only at `GF(2^8)`, so Layer 11 supplies the `K` basis") should
  move with this PR. The PR body names Category B and #12 but not the target (T4 through Layer
  12's `verify`, as #67's body does).
- `encodeLinear` is `noncomputable` by necessity (CompPoly's module structure); fine. `#print
  axioms` of every public theorem: `propext, Classical.choice, Quot.sound` (`domainPt_injOn` on
  `propext` alone). `audit-lean.sh`, `check-imports.sh`, `check-layers.sh`, `check-docs.py` green.

## Pass B: fidelity against the pin

**The basis and the roots** (`additive_ntt_f64.rs:12-69`; `verifier.py:962-968`): `e_c = x^c`,
the word `2^c` (`F64(1 << i)`, `E(2**i)`): `basisElt_eq_domainPt`. The layers:
`evals[i][j] = evals[i-1][j+1] · (evals[i-1][j+1] + evals[i-1][0])`, normalised by `evals[i][0]⁻¹`,
is `V_i(e_{i+j})` divided by `V_i(e_i)`; the Python pops the diagonal entry as `roots[k]`. The Lean
keeps all 64 entries per layer (the dropped ones are zero) and reads the diagonal: same values,
checked at `k ≤ 9` by the PR's `pythonRoots` and at `k ≤ 30` by this review (finding 2). The Rust's
`dim ≤ 63` against the Annex's `κ + R ≤ 64` is recorded by the PR; at the deployed maximum 26
nothing depends on it.

**`V_k` and `Ŵ_k`** (`verifier.py:983-987`): `V_0(x) = x`, `V_{k+1}(x) = V_k(x)^2 + V_k(e_k)
V_k(x)`, `Ŵ_k(x) = V_k(x) · V_k(e_k)⁻¹` with `0⁻¹ = 0`: `vanish`, `normW`, the same convention
(the cost of the executable is finding 1). The Annex's definition as the product over `U_k` is `subspaceVanish`, and
`vanish_eq` is the proof that the implementation computes it: this is the right direction, the
transcription proved against the specification.

**Column weight** (`verifier.py:971-989`, `lem:colweight`): `∏_k (1 + r_k (1 + Ŵ_k(x)))` with
coordinate `k` against `Ŵ_k`; the Lean's `(1 - r_k) + r_k Ŵ_k(x)` is the same in characteristic
two and is the ring-generic `eq(0, r) = 1 - r` form, so it is right over any `S`. Coordinate `k` of
the point pairs with bit `k` of the table index (`weightCell` tests; `bitProductTable`): matches
`⟨u⟩ = Σ u_i 2^i`, bit 0 first, of Annex B. The position is `E(query)`, i.e. `x_v = Σ v_c e_c`:
`domainPt`. Random-point vectors at `(6, 19)` and `(2, 16)` (finding 2) agree.

**Encoder** (`def:enc`): the message read directly as novel-basis coefficients, no basis change;
`encode_eq_sum` is `def:enc` expanded. The Lean's `encode` is the specification's object, not the
Rust's NTT; the Rust's output order (position `v` of the codeword is `P(x_v)`) is pinned through the
Python verifier only, and in the kernel at one position for two unit messages against CompPoly's
NTT (`NovelBasisNtt.lean`). The Rust was not executed.

**Fit with #67**: `Level.logInvRate` is `R`, the message log after a level's fold is `κ`,
`blockLogs` is `κ + R`, and `encode φ κ R` indexes positions by `Fin (2^(κ+R))`, the Python's
`block_length`; the names agree. The bound `encode_injective` needs, `κ ≤ 64`, follows from
`ladder_blocks`; the bound the distance needs, `κ + R ≤ 64` (finding 3), is `ladder_blocks`'
first conjunct. The level-0 message is `K`-valued and the later levels `E`-valued; `encode_ofK`
and `isInK_encode_ofK` are the right bridge, taking `φ = algebraMap K E`.

Nothing is from the historical implementation.

## Pass A: specifications

Every theorem was instantiated: `vanish_eq` at `k = 5`, `subspaceRoot_ne_zero` at 63,
`encode_injective` at `K` and `E`, `natDegree_novelPoly` at `(3, 5)`, the linear map's laws over
`E` (the PR's tests), and the vectors of finding 2. `columnWeight` is well defined at every `κ`;
it is its executable that fails at deployed sizes (finding 1). No hypothesis is unsatisfiable: `κ ≤ 64`,
`IsDomain E`, `Function.Injective (algebraMap K E)` all hold at the deployed instance.
`encode_injective` is substantive (its proof would fail for a monomial reading of the message, as
the `x^3` mutation shows). `encode_columnWeight` is not (finding 5). `columnWeight`'s `mle_eq` is
a proof obligation of the structure, so the evaluator cannot drift from the table. The statement
the opening will need is finding 3.

Target classification: the PR says Category B and refs #12 and #101; it should name T4 (finding
7). The definitions are correctly Category B (the Annex and the two implementations are the
authorities) and the proof `vanish_eq` is in the right direction.

## Pass C: hygiene

Findings 4 and 7; the module docstring otherwise carries the pin, the sources and the wrong
readings excluded, which is the right content for it; declaration docstrings are one to three
lines; the module shape and `@[expose] public section` follow the siblings.

## What the review could not do

The column weight at a deployed `κ` could not be evaluated through `columnWeight` (finding 1); the
Rust NTT was not run, so the position order of the codeword rests on the Python verifier and the
two kernel points against CompPoly's NTT. The probes (the axioms, the roots to stage 30 and
`subspaceRoot 64`, the two weights, the encoder at `κ = 4`, the bisection of the `κ = 22` run, the
1024-entry table) were scratch files of the review session and are not kept; the vectors now in
the test file were generated with `python3 -I` against the pinned verifier module.
