# Dossier `obligations`: the hierarchy of proof obligations of the leanVM proof system

Task `obligations` of the blueprint review. Written 2026-09-30. Object: leanerVM `main` at
`b435631` (every Lean citation at that revision, `git show b435631:<path>`); ground truth leanVM
at `a386121f` (read with `git -C /home/scaraven/Documents/leanEthereum/leanVM show a386121f:<path>`;
the checkout has moved, brief §8); libraries at the old pins (ArkLib `dca90385`, CompPoly
`3468b38c`, VCVio `f9dc47d9`, Clean `93c9d1ef`) unless the new pin (`7653a901`, `572f9973`,
`a4232d08`, `42fe4b26`) is named. No Lean was run for this dossier: every status below rests on
the sibling dossiers' recorded probes (named at each node) or on reading the sources.

Inputs, read in the order the task gave: `docs/architecture.md` and
`docs/roadmap/protocol-blueprint.md` at `b435631`; the dossiers `code-spine`, `lib-arklib`,
`gt-bus`, `gt-table-pub`, `gt-flock-ring`, `code-pubinput`, `boundary-adaptor`, `literature`,
`code-layer1`, `gt-opening-compile` (complete when read: its summary is headed "Conclusions" with
five items and its sections A to G are written), `lib-others`, and the `register` staging (its
row identifiers are quoted in parentheses only where they locate a finding); the Lean sources
of `LeanerVM/Protocol/` at `b435631` for every name.

Abbreviations for pointers: `bp:NNN` is a line of the blueprint at `b435631`; `arch:NNN` a line of
`docs/architecture.md` at `b435631`; a dossier is named by its task name and section.

**Status vocabulary** (one tag per node, counted in the summary):

| Tag | Meaning at `b435631` |
| --- | --- |
| `[status: built and proved]` | stated and proved in leanerVM; `#print axioms` gives the kernel's three standard axioms only (as recorded by the named dossier's probe) |
| `[status: built, definition]` | a definition in leanerVM, load-bearing, with no proof obligation of its own (its content is what later theorems prove things about) |
| `[status: library, proved at the old pin]` | proved in ArkLib, VCVio, CompPoly, Clean or Mathlib at the old pin (and, where the dossier checked, at the new one) |
| `[status: library, proved at the new pin only]` | landed upstream between the pins |
| `[status: admitted upstream]` | stated in a library and `sorry` at both pins |
| `[status: specified only]` | stated in the blueprint (a sketch), not built |
| `[status: not specified]` | needed by the composition and stated nowhere in the blueprint |
| `[status: unprovable as written]` | the review found the blueprint's statement cannot be proved (or stated) as it stands |
| `[status: wrong as written]` | the review found the blueprint's description false of leanVM or of the code |
| `[status: trusted, assumed interface]` | a structure whose fields are theorems another roadmap or library owes; every theorem that uses it takes it as an argument |
| `[status: trusted, hypothesis]` | a hypothesis of a theorem on the chain that nothing on the chain discharges |
| `[status: trusted, transcribed data]` | Category B data (layouts, constants, schedules) whose only check is a fixture |

A node marked `[review: …]` is one on which the review found the blueprint's statement wrong,
missing or unprovable; the tag says which.

## 1. Summary

(written last; see the end of the file for the counts and the trusted leaves)

## 2. The tree

How to read it. The root is what the proof system must deliver to the rest of the verification:
the two theorems of the blueprint's Layer 13, which are the proof-system half of target T4
(`arch:261-275`). Each level below is what the level above consumes. A node has: a name (and
the Lean name the blueprint or the code gives it), what it states for a zkVM engineer, which
node(s) it feeds, its status tag, and where the review's dossiers speak about it. The tree is
written for the proof system as the blueprint plans it, with the review's corrections marked in
place; the adaptor (Layer 3) and leanISA's theorems are a separate branch (2.6), and the
hypotheses discharged by verifier checks or by conditions on public data are collected in a
table at the end (2.7).

One convention: "the front" names the oracle protocol's phases before the opening,
`commit ⟫ bus ⟫ table ⟫ pub ⟫ flock`; "the pool" is the list of claims those phases leave for
the opening.

### 2.0 The root: what the proof system delivers (Layer 13, the proof-system half of T4)

- **2.0.1 Base extraction** (`baseVerifier_extractsExecution`, `bp:1247-1248`; `arch:264-269`).
  *States:* an adversary that makes the executable verifier `verify prog input proof` accept
  yields, except with probability `niError`, a stack whose rebuilt witness satisfies leanISA's
  relation, hence an execution of the program on the public input. *Feeds:* T4, T7 through T5
  and T6 (recursion consumes the extracted witness). *Status:* `[status: unprovable as written]`
  `[review: wrong]` — as sketched it has no probability space (its hypothesis is a closed
  Boolean), concludes an existential (soundness, not knowledge), names no adversary or query
  budget, and drops `WellFormedBytecode prog`, which `constraintSoundness` needs; the
  well-formed statement is a bound on the event "`verify^H` accepts and the extracted stack has
  no execution" over a random oracle `H`, for a `Q`-query adversary, under `WellFormedBytecode`.
  *See:* gt-opening-compile E.1; boundary-adaptor findings 3 and 16, E.6; docs-debt (DD1).
  *Consumes:* 2.1.2 (knowledge soundness of `verify`), 2.6.2 (the adaptor's soundness bridge),
  2.6.6 (`constraintSoundness`), 2.1.5 (the random-oracle heuristic, non-formal).
- **2.0.2 Base completeness** (`baseProver_complete`, `bp:1249-1250`; `arch:273-275`). *States:*
  from a valid execution (with fill blocks in the program), the honest Lean prover's proof is
  accepted by `verify`. *Feeds:* T4's completeness half, T8. *Status:* `[status: unprovable as
  written]` `[review: unprovable]` — false without a resource hypothesis (a valid execution with
  `κ_mem = 32` has a stack above `2^28`, which the verifier rejects), and "the witness of `t`"
  needs a witness generator (T2, out of scope) or a classical choice; the honest prover's
  grinding search makes `prove` partial, so the equation must be `prove … = some proof → verify …
  = true`. *See:* boundary-adaptor finding 4, C (rows "resource bound", "constructed witness");
  gt-opening-compile E.5; docs-debt (DD19). *Consumes:* 2.6.7 (`constraintCompleteness`), 2.6.3
  (`m3Holds_stackOf`), 2.2.1 (`piop_perfectCompleteness`), 2.1.4 (completeness through the
  compilation), 2.1.6 (the prover's grind).

### 2.1 The compiled verifier (Layers 11 and 12)

- **2.1.1 Refinement of the executable verifier** (`verify_iff_compiled`, `bp:1218-1221`).
  *States:* `verify prog input proof = true` exactly when, for some admissible sizes `s` read
  from the proof, the Fiat–Shamir compilation of the Merkle-compiled oracle verifier of
  `leanIsaInstance prog s` accepts the decoded messages under the BLAKE2s chain, and every
  grinding check passes. *Feeds:* 2.0.1, 2.0.2 (it is what ties `verify` to every theorem below).
  *Status:* `[status: unprovable as written]` `[review: unprovable]` — the sketch applies ArkLib's
  `Verifier.fiatShamir` to an oracle verifier whose messages are the stack and the codewords in
  the clear, has no `decode`, no Merkle compilation, and no grinding conjunct; statable in the
  corrected form of gt-opening-compile E.4. *See:* gt-opening-compile E.4; lib-arklib G.4.
  Sub-obligations:
  - **2.1.1.1 The Merkle compilation of the IOPP** (`bcsCompile`, no blueprint name). *States:*
    the interactive verifier whose messages are roots, scalars, nonces and openings, obtained
    from the codeword-oracle verifier by replacing each oracle message by a root and each query
    by an opening check. *Status:* `[status: not specified]` `[review: missing]` — ArkLib's
    `BCSTransform` is commented out at both pins. *See:* gt-opening-compile E.4 item 1; lib-arklib D.3.
  - **2.1.1.2 The Fiat–Shamir chain as a challenge oracle** (`FsState.seed/observe/sample/grind`,
    `bp:1200-1205`). *States:* the chain is a function of statement and absorbed messages (in
    the wire encoding: three of four round coefficients, roots as two scalars, openings not
    absorbed), so it is a `QueryImpl` for ArkLib's `fsChallengeOracle`. *Status:* `[status:
    specified only]` (Category B). *See:* gt-opening-compile C.1, E.4 item 2; probe H.2 there.
  - **2.1.1.3 The proof object and its decoding** (`Proof`, `RoundPoly.decode`, `bp:1207-1212`).
    *States:* the stream order of `cpu/mod.rs:711-779`, the dropped coefficient recovered from
    the running claim, the Merkle format (pruned wire form or raw form: unspecified).
    *Status:* `[status: specified only]` `[status: trusted, transcribed data]`. *See:*
    gt-opening-compile C.2, C.3; gt-table-pub finding "the round message".
  - **2.1.1.4 The setup checks** (`Sizes.Admissible` and the canonical-encoding checks). *States:*
    `verify` rejects sizes outside the caps, the stacking window `15 ≤ μ ≤ 28` and the rate
    window `1 ≤ ρ ≤ 4`, non-canonical limbs, an unconsumed stream. *Status:* `[status: unprovable
    as written]` for `Admissible` (it lacks the two windows; `Sizes.ofWitness` cannot produce
    `logInvRate`), `[status: not specified]` for the encoding checks. *See:* gt-bus B, G4, G9;
    gt-opening-compile D.1, D.2; boundary-adaptor finding 5.
  - **2.1.1.5 Native settlement of the fixed columns** (`settleFixedClaims`, `bp:1235-1236`).
    *States:* `verify` evaluates the bytecode multilinear and the Flock matrices itself
    (`idxColumnEval`, `bytecodeColumnEval` of Layer 1; the circuit walk of Flock). *Status:*
    `[status: specified only]`; the Flock walk has no owner. *See:* gt-flock-ring 5.5; code-layer1 A.9.
- **2.1.2 Knowledge soundness of the executable verifier** (`verify_knowledgeSound (fs) (bcs)
  (mca) (flock)`, `bp:1226-1227`). *States:* against a `Q`-query adversary in the random-oracle
  model, `verify^H` accepts a proof whose extracted stack fails `M3Holds` with probability at
  most `niError s Q`. *Feeds:* 2.0.1. *Status:* `[status: unprovable as written]`
  `[review: unprovable]` — its three interfaces cannot be inhabited by any ArkLib theorem at
  either pin, and even inhabited they do not compose to the conclusion: four steps are missing
  (2.1.2.3 to 2.1.2.6). *See:* gt-opening-compile E.2, E.3, G; lib-arklib G.4; literature A.3.
  - **2.1.2.1 Fiat–Shamir security interface** (`FiatShamirSecurity`, `bp:1224`). *States, as
    the blueprint has it:* round-by-round knowledge soundness of the IOPP gives knowledge
    soundness of its Fiat–Shamir compilation in the random-oracle model with error
    `Q · max_i ε_i`. *Status:* `[status: trusted, assumed interface]` `[review: wrong]` — as a
    universal claim over IOPPs it is false (an IOPP's messages are oracles; the compiled error
    carries a hash term; leanVM grinds); to be true and strong enough it must be stated for
    leanVM's construction: a state-restoration-sound interactive argument, the `fs/lib.rs`
    chain with `H` random, named ground rounds with bits `b_i`, error
    `(t + k) · max_i 2^{-b_i} ε_i + 3.5 t²/2^256`; the proof-of-work factor is an assumption no
    published theorem covers. *See:* literature A.3, A.4 (two findings); gt-opening-compile E.2;
    lib-arklib D.3, G.4. Its own leaves:
    - **2.1.2.1.1 Round-by-round to state-restoration knowledge soundness.** *States:* the
      per-round errors bound a state-restoration adversary's success by `(t + k) · max_i ε_i`.
      *Status:* `[status: not specified]` `[review: missing]` — commented out in ArkLib with the
      wrong error (`Implications.lean:230-254`); not in the blueprint's interface list. *See:*
      gt-opening-compile E.2 (last bullets); lib-arklib D.3.
    - **2.1.2.1.2 The hash chain is as good as the ideal per-round challenge oracle.** *States:*
      the ratcheted BLAKE2s chain with its four tags and fixed-width blocks loses at most a
      collision term against the oracle keyed by the whole prefix; the encoding is injective.
      *Status:* `[status: not specified]` `[review: missing]`. *See:* literature E.6 (LT10), G.3
      (transcript-encoding advisories); gt-opening-compile E.2 (c).
    - **2.1.2.1.3 The grinding model.** *States:* a query to `H` at a ground round costs
      `2^{b_i}` queries in expectation, so the effective error of that round is `2^{-b_i} ε_i`.
      *Status:* `[status: not specified]` `[review: missing]`; no theorem in the literature for
      multi-round IOPs. *See:* literature A.3 item 3, G.5 (LT13); gt-opening-compile D.3.
    - **2.1.2.1.4 The hash-collision term.** *States:* `3.5 t²/2^256` (or `3(Q²+1)/2^256`) for
      the chain and the trees. *Status:* `[status: not specified]` `[review: missing]`. *See:*
      literature A.3 item 2 (LT3).
    - **2.1.2.1.5 Program binding through its hash.** *States:* two programs with the same
      `bytecode_hash` share every challenge; the statement binds the program up to a BLAKE2s
      collision, a term of `niError`. *Status:* `[status: not specified]`. *See:* gt-opening-compile E.1.
    - **2.1.2.1.6 The family composition over the prover's sizes.** *States:* `verify`
      dispatches on eight announced sizes; a bound per admissible `s` transfers to the union
      only with an argument on how the adversary's queries split among members, and `niError`
      must be uniform in `s` or take the maximum. *Status:* `[status: not specified]`
      `[review: missing]`. *See:* boundary-adaptor B.3, finding 6; gt-opening-compile E.1.
  - **2.1.2.2 Merkle (BCS) security interface** (`BcsSecurity`, `bp:1225`). *States, as the
    blueprint has it:* "Merkle-compiled oracles: extraction from collision resistance / ROM".
    *Status:* `[status: trusted, assumed interface]` `[review: wrong]` — names a property with
    no error and no object; to be true and strong enough: the Merkle compilation of
    `pcs/merkle.rs`, `fs/merkle.rs` (leaf = BLAKE2s of the row image, node = BLAKE2s of two
    children, height and leaf width fixed from public data) preserves state-restoration
    knowledge soundness in the random-oracle model with the straight-line extractor reading
    every committed leaf off the query log, up to `3(Q²+1)/2^256`. *See:* gt-opening-compile
    E.2, D.4 (checks M1 to M7); lib-arklib G.4. Its leaves:
    - **2.1.2.2.1 Binding of the root to the opened rows** (check M6). *States:* the recomputed
      root equals the committed one, so the opened rows are the committed ones; without it a
      total break. *Status:* `[status: specified only]` (Layer 11's `merkleVerify`). *See:*
      gt-opening-compile D.4.
    - **2.1.2.2.2 Role separation of the one BLAKE2s map** (chain block, Merkle node, Merkle
      leaf, grinding). *States:* no cross-role input is exploitable; replaces domain separation,
      which the trees lack (fixed height and leaf width do the work, check M7). *Status:*
      `[status: not specified]` `[review: missing]`. *See:* literature E.6 (LT10);
      gt-opening-compile D.4 (M7), B.4.
    - **2.1.2.2.3 Straight-line leaf extraction from the query log.** *States:* every leaf the
      prover can open was hashed, so it is in the log except with the collision or preimage
      term. *Status:* `[status: not specified]`. *See:* gt-opening-compile E.1.
    - **2.1.2.2.4 VCVio's Merkle-tree library** (`CryptoFoundations/MerkleTree/`, nineteen
      sorry-free modules at `f9dc47d9`). *States:* a generic Merkle tree with its
      collision-resistance argument. *Status:* `[status: library, proved at the old pin]`; fit
      with leanVM's trees unverified. *See:* docs-debt (DD15).
  - **2.1.2.3 The list-binding compilation** (no blueprint name; "Layer 12 turns list binding
    into extraction of the one `q`", `bp:1190`; acceptance test 11). *States:* let `Front'` be
    the front with the commit message replaced by an interleaved `K`-word `w` (the level-0
    codeword with position queries) and `C := Front' ⟫ whirOpen`; then `C` is worst-case
    round-by-round knowledge sound for `M3Rel` with the extractor "list-decode `w`, return the
    first member satisfying `M3Holds`", with per-challenge errors `L_0 · ε_i` at the front's
    challenges and Theorem B.7's at WHIR's. *Feeds:* 2.1.2; it is where the list-size factor
    enters `niError`. *Status:* `[status: not specified]` `[review: missing]` — the blueprint
    assigns the step to `verify_knowledgeSound`, whose sketched hypotheses cannot prove it.
    *See:* gt-opening-compile E.3, G; literature A.3 item 4 (LT2); gt-flock-ring 8.13. Its leaves:
    - **2.1.2.3.1 Every member of the list is `K`-valued and of the right size.** *States:*
      a codeword of the code over `E` within radius `γ_0 < 1 − √ρ_0` of a `K`-valued word is
      `K`-valued (its `y` and `y²` coordinate projections vanish on more than `2^{κ_0} − 1`
      points), of `μ` variables after the level-0 relayout, with zero rows where `w` has them.
      *Status:* `[status: not specified]` `[review: missing]`; a two-line argument in the dossier,
      not in the specification. *See:* gt-opening-compile G.
    - **2.1.2.3.2 State functions indexed by a finite set compose by a union bound.** *States:*
      a knowledge state function "for every `g ∈ Λ(w)`, the front's state at `(g, τ)` is
      false" escapes with probability at most `|Λ(w)|` times the front's worst-case bound; the
      worst-case form of the spine is what makes this a per-transcript union. *Status:*
      `[status: not specified]`; ArkLib has no such lemma. *See:* gt-opening-compile E.3.
    - **2.1.2.3.3 The front's verifier makes no oracle query.** *States:* every phase before the
      opening reads the stack only through its extractor, never through a query, so `Front'`'s
      verifier is `Front`'s (a cast of `OracleReduction`, ArkLib #383's `Cast.lean`). *Status:*
      `[status: not specified]` `[review: missing]` — true of the two built phases; nothing states
      or enforces it for the others (finding 5.2 of this dossier). *See:* gt-opening-compile E.3.
    - **2.1.2.3.4 The seam step.** *States:* the front's `toFun_full` in the contrapositive:
      state false at the front's last transcript implies some pooled claim is false of `g`,
      which is `∉ R_open`, Theorem B.7's start invariant. *Status:* `[status: not specified]`.
      *See:* gt-opening-compile E.3.
    - **2.1.2.3.5 The compiled extractor computes.** *States:* enumeration of the finite code
      is a definition (Lean has no cost model); efficiency in the literature's sense is
      Guruswami–Sudan, unnamed. *Status:* `[status: specified only]` (acceptance test 24 says
      "computable"). *See:* literature A.4 ("computable is not efficient", LT4), G.2.
  - **2.1.2.4 WHIR's round-by-round soundness** (`whirOpen_rbrSoundness (mca : McaJohnson)`,
    `bp:1175`; Annex B Theorem B.7, `b-polynomial-commitment-scheme.tex:139-152`). *States:* for
    the relation `R_open` ("some codeword within `γ_0` of the committed word satisfies every
    weighted claim"), round-by-round soundness with the per-message errors of Annex B's table;
    soundness for a language, no extractor named. *Feeds:* 2.1.2.3. *Status:* `[status:
    specified only]`; a Lean proof would be the first machine-checked proof of this variant.
    *See:* gt-opening-compile B.5, B.6; literature C.3. Its leaves:
    - **2.1.2.4.1 Mutual correlated agreement up to the Johnson bound** (`McaJohnson`, `bp:1176`;
      ArkLib `rs_mcaError_le_in_johnson_range`, `CapacityBounds.lean:203-219`). *States:*
      [BCHKS25] Theorem 4.6 as printed (with `m = max(⌈√ρ/(1−√ρ−δ)⌉, 3)` and the reduced rate),
      for the affine line, converted to the fold in characteristic two by Annex B's footnote.
      *Status:* `[status: admitted upstream]` `[status: trusted, assumed interface]` — a preprint
      theorem with a sketched proof; the only coding-theoretic input. *See:* literature C.2,
      C.4 (LT7, LT8); gt-opening-compile E.2; lib-arklib B.3.
    - **2.1.2.4.2 The Johnson bound** (Annex B `B:391-414`). *States:* the list within radius
      `γ_i < 1 − √ρ_i − η_i` has at most `L_i = 1/(2η_i√ρ_i)` members. *Status:* `[status:
      specified only]` (proved in the annex, not in Lean). *See:* gt-opening-compile B.5, F.2.
    - **2.1.2.4.3 Folding preserves lists** (Lemma B.10, `B:189-198`, with the `2^{ℓ−1}` row
      union). *States:* the fold of a word close to a list is close to the folded list, except
      with the MCA error times the row union. *Status:* `[status: specified only]`. *See:*
      gt-opening-compile B.5.
    - **2.1.2.4.4 Out-of-domain separation** (Lemma B.11, `B:200-206`; check W2). *States:*
      after the OOD sample the new oracle's list has at most one member consistent with the
      transcript, except with `C(L_i, 2)·μ_i/|E|`; without OOD binding the query phase would pay
      a union over the list. *Status:* `[status: specified only]`. *See:* gt-opening-compile D.5 (W2), F.2.
    - **2.1.2.4.5 Per-level batching** (check W4). *States:* the level's claims (OOD first,
      queries after, running claim at `λ_i^0`) settle in one identity, error `(J_i − 1)L_i/|E|`.
      *Status:* `[status: specified only]`. *See:* gt-opening-compile D.5 (W4).
    - **2.1.2.4.6 The fold rounds.** *States:* each of the `ℓ_i` sumcheck rounds of level `i`
      costs `2L_i/|E| + 2^{ℓ_i−j} ε_i` (the running claim is a cofactor with `c_1` derived, as
      in the table sumcheck). *Status:* `[status: specified only]`; the blueprint's Layer 10
      "2/|E| per round" is the tail's value, wrong for these. *See:* gt-opening-compile B.6.
    - **2.1.2.4.7 The query rounds** (check G1 for the nonce, W3 for row consistency). *States:*
      `t_i` positions sampled after a 17-bit proof of work; error `(1 − γ_i)^{t_i} ≈ 2^{-111}`
      before grinding. *Status:* `[status: specified only]`; the grinding is outside every
      theorem (2.1.2.1.3). *See:* gt-opening-compile D.3, D.5, F.2; literature G.5.
    - **2.1.2.4.8 The terminal check** (W5) and the final plaintext level. *States:* one
      equation `weight · f̃_final(ρ_tail) = t_r` closes the chain; without it nothing is checked
      about `q`. *Status:* `[status: specified only]`. *See:* gt-opening-compile D.5.
    - **2.1.2.4.9 The column weight of the encoder** (`encode_column_weight`, `bp:1170`; Lemma
      B.14). *States:* position `x` of the codeword is an inner product of the message with a
      weight whose extension the verifier computes in closed form. *Status:* `[status:
      specified only]` `[review: wrong]` — as an existential it is true of any linear map and
      says nothing about the novel basis; the needed object is the definition `columnWeight x`
      with its closed-form `mle` and the equation `encode κ R f x = (columnWeight x).pair f`.
      *See:* gt-opening-compile B.6.
    - **2.1.2.4.10 The encoder** (`encode`, `novelBasis`, `bp:1168-1169`; CompPoly's
      `AdditiveNTT`). *States:* Reed–Solomon encoding in the novel polynomial basis on the
      additive domain in `K`, over `K` at level 0 and over `E` at every later level. *Status:*
      `[status: specified only]` `[review: wrong]` — `encode` over `K` alone serves level 0 only.
      *See:* gt-opening-compile B.6; lib-others B (CompPoly's NTT exists, generic over a basis).
    - **2.1.2.4.11 The parameters** (`ladder`, `ladder_queries_eq`, the six constants,
      `bp:1155-1165`). *States:* fold factors, rates, query counts and grinding bits per level
      as `whir_config.rs` derives them; `(ladder 15 1).map (·.queries) = [223, 55]`. *Status:*
      `[status: trusted, transcribed data]`; the Python table is reproduced by a scratch port
      of the Rust's search. *See:* gt-opening-compile F.2, B.3 (`Level` lacks `η`).
  - **2.1.2.5 Perfect completeness of WHIR** (`whirOpen_perfectCompleteness`, `bp:1174`).
    *States:* the honest prover's folds and openings pass every level check. *Feeds:* 2.1.4.
    *Status:* `[status: specified only]`. *See:* gt-opening-compile B.6.
  - **2.1.2.6 Merkle definitions** (`merkleRoot`, `merkleVerify`, `blake2sBytes`, `bp:1179-1182`).
    *States:* BLAKE2s-256 of leaf images and of two-child nodes, the raw path check, the RFC
    7693 byte hasher over leanISA's `compress`. *Status:* `[status: specified only]`
    `[status: trusted, transcribed data]`. *See:* gt-opening-compile B.4, B.6.
  - **2.1.2.7 Plain knowledge soundness from the round-by-round form** (ArkLib
    `rbrKnowledgeSoundness_implies_knowledgeSoundness`, `Implications.lean:223-228`). *States:*
    an interactive prover convinces the verifier without a good first message with
    probability at most `Σ ε_i`. *Feeds:* the blueprint's plain corollary (`bp:261`); not needed
    if 2.1.2.1 consumes the round-by-round form directly. *Status:* `[status: admitted upstream]`;
    its transcript-level half is proved by lib-arklib's probe `PlainReading` in forty lines; its
    conclusion forgets the named extractor. *See:* lib-arklib D.1, D.3, G.3; code-spine C.7.
- **2.1.3 The interactive-oracle form of the compiled protocol** (`leanVmIopp`, `bp:1214-1215`).
  *States:* `commit' ⟫ bus ⟫ table ⟫ pub ⟫ flock ⟫ whirOpen`, where `commit'` sends the level-0
  codeword and `whirOpen`'s level-0 batching is the opening phase's `λ`. *Status:* `[status:
  specified only]` `[review: wrong]` — the blueprint says "WHIR in place of the evaluation
  oracle" after a `μ`-round opening sumcheck; see 2.4.5. *See:* gt-opening-compile A.4, A.5.
- **2.1.4 Completeness survives the compilation** (`bp:1256-1257`: "without any assumption").
  *States:* an honest proof accepted by the interactive verifier on the chain's challenges is
  accepted by `verify` (a statement about two definitions), and the grinding search succeeds.
  *Feeds:* 2.0.2. *Status:* `[status: wrong as written]` `[review: wrong]` — the grind is an
  unbounded search; in the random-oracle model it fails with probability `(1 − 2^{-17})^{2^64}`,
  and with BLAKE2s fixed its success is a conjecture; `prove` must be partial or fuelled.
  *See:* gt-opening-compile E.5.
- **2.1.5 The random-oracle heuristic.** *States:* BLAKE2s's compression function is the random
  oracle `H` of 2.1.2; the theorem about `verify` itself is the instantiation of the
  definitions only. *Status:* `[status: trusted, hypothesis]` — cannot be a Lean hypothesis
  (false for any fixed function) nor an axiom; must be named in Layer 13 and in
  `docs/architecture.md`; classical (no quantum random-oracle model). *See:* gt-opening-compile
  E.1; boundary-adaptor C (row "BLAKE2s as a random oracle"), finding 3; literature B.4 (LT6),
  G.5 (LT14).
- **2.1.6 The honest prover** (`prove`, `leanVmProver`, `bp:1145`, `bp:1250`). *States:* each
  phase's prover is a computable function of the witness, the challenges so far and the layer
  tables; the compiled prover adds encoding, Merkle trees and the grind. *Feeds:* 2.0.2.
  *Status:* `[status: specified only]` (the spine's `leanVmProver` is built as the composed
  prover of whatever bundle is supplied); the phase-level `Def`s bundle a real-number error, so
  on the real protocol neither the verifier nor the extractor compiles (lib-arklib G.5).
  *See:* lib-arklib G.5 (AK5); code-spine D.5.

### 2.2 The master theorems of the oracle protocol (the spine)

Both are one-line proofs of a composed component's own field, stated over an abstract instance
`I : M3Instance` and a bundle `P : Phases I` of five phases with their proofs; they say nothing
about leanVM until an instance and leanVM's phases are supplied (code-spine C.4).

- **2.2.1 Perfect completeness of the oracle protocol** (`piop_perfectCompleteness (P) (C :
  P.Complete)`, `Spine/Compose.lean:162-170`). *States:* for every `(input, q)` with
  `M3Holds I input q`, the honest prover and the composed verifier accept with probability one
  and end in `Seam.done` (which is `True`). *Feeds:* 2.0.2 through 2.1.4. *Status:* `[status:
  built and proved]` (probe `P1Axioms` of code-spine; conditional on `Phases.Complete`).
  *See:* code-spine C.4, C.6; lib-arklib E.
  - **2.2.1.1 ArkLib's completeness composition** (`OracleReduction.append_perfectCompleteness_of_guarded_verifiers`,
    `Composition/Sequential/OracleCompleteness.lean:54-67`). *States:* two perfectly complete
    reductions with guarded verifiers, the second complete from every shared-oracle state,
    compose perfectly; the additive-error form exists too. *Status:* `[status: library, proved
    at the old pin]` (probe `AxiomsArkLibBuilt`). *See:* lib-arklib E.2, E.3.
  - **2.2.1.2 The component-level append** (`Component.Complete.append`, `Component.lean:162-169`).
    *Status:* `[status: built and proved]`. *See:* code-spine A (catalogue).
  - **2.2.1.3 The side conditions `guarded` and `outputPure`** (`Component.Complete`,
    `Component.lean:76-85`). *States:* the verifier is a check followed by a pure verdict; the
    prover's output makes no oracle query. *Status:* `[status: built, definition]`; both
    derivable over the empty shared oracle (ArkLib's `GuardedForm.ofEmpty`,
    `Prover.instOutputIsPureEmpty`), so `outputPure` is redundant. *See:* code-spine finding
    "`outputPure` is redundant" (CS5); lib-arklib G.7.
  - **2.2.1.4 Completeness carries no error** (`Component.Complete.complete` is
    `perfectCompleteness`). *States:* every phase must be perfectly complete; a phase complete
    up to an error has no place. *Status:* `[status: built, definition]` `[review: missing]` —
    ArkLib composes additive completeness errors at both pins; whether Flock needs one is
    settled by gt-flock-ring (it does not, if the Lean prover sends the true coefficients).
    *See:* lib-arklib G.2 (AK2); gt-flock-ring 4, 8.4, 8.12.
- **2.2.2 Round-by-round knowledge soundness of the oracle protocol**
  (`piop_rbrKnowledgeSoundness (P) (S : P.Security)`, `Spine/Compose.lean:172-179`). *States:*
  ArkLib's worst-case round-by-round knowledge soundness of the composed verifier's
  `toVerifier`, from `M3Rel I` to `Seam.done I`, for the named extractor `piopExtractor P S`
  and the composed knowledge state function, at the per-challenge error `piopError P`: for
  every statement, every prefix and every challenge index, the probability over one uniform
  challenge that the state goes from false to true is at most the error of that challenge.
  *Feeds:* 2.1.2.3 (through the list-binding compilation), 2.1.2.7. *Status:* `[status: built
  and proved]` (probes `P1Axioms`, `AxiomsLeanerVM`; conditional on `Phases.Security`).
  *See:* code-spine C.4, D.3; lib-arklib D.1, D.2 (adequacy of the notion).
  - **2.2.2.1 The knowledge-soundness append for a guarded first verifier**
    (`Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`,
    `ToArkLib/KnowledgeAppend.lean:510`; the port of ArkLib #615). *States:* two worst-case
    round-by-round knowledge-sound verifiers, the first guarded, append to one with the
    appended extractor and each challenge keeping its own error. *Status:* `[status: built and
    proved]` (diffed line by line against #615's file). *See:* lib-arklib C.1, C.2; ArkLib's
    own `append_rbrKnowledgeSoundness` is `[status: admitted upstream]` at both pins (ledger
    A2), and #615 is open and in conflict on a framework upstream calls legacy (lib-arklib G.3).
  - **2.2.2.2 The appended knowledge state function** (`Verifier.KnowledgeStateFunction.appendGuarded`,
    `KnowledgeAppend.lean:474`). *States:* the first component's state until its verdict, then
    the second's, with the seam round handled (`backward_right`, `extractMid_seam`). *Status:*
    `[status: built and proved]`. *See:* lib-arklib C.2, G.9.
  - **2.2.2.3 ArkLib's extractor append** (`Extractor.RoundByRound.append`,
    `Append/StateFunction.lean:75`). *Status:* `[status: library, proved at the old pin]`.
    *See:* lib-arklib B.2.
  - **2.2.2.4 The composed extractor** (`piopExtractor P S`, `Compose.lean:153`;
    `commitExtractor`, `Component.sendExtractor`, `SendOracle.lean:134`). *States:* the commit
    phase's extractor reads the stack off the first message; the phases' extractors (all with
    witness `Unit`) are appended through the verdicts; the chain is computable
    (`isNoncomputable = false`). *Status:* `[status: built, definition]` `[review: missing]` — no
    definition "the extracted stack" exists: with a phase that has a round, `extractOut` has
    type `Unit` and the stack is `extractMid` at round 0, so acceptance test 24's `rfl` witness
    is ill-typed (probe `P3cExtractor`). *See:* code-spine D.5, finding "the extracted stack is
    not a definition" (CS4); lib-arklib D.6.
  - **2.2.2.5 A bound on the composed error** (`piopError P := P.toDef.err`, `Compose.lean:149`;
    the blueprint's `piopError_le`, `bp:1130`). *States, as the blueprint has it:* `Σ_i piopError
    s i ≤ 2^40/|E| + flockError` for admissible sizes. *Status:* `[status: unprovable as
    written]` `[review: unprovable]` — the spine's `piopError` takes a bundle `P`, not sizes
    `s`, and nothing bounds it: five phases that draw a challenge, check nothing and declare
    error `1` inhabit `Phases.Security toy` and both master theorems hold of them (probe
    `P4Junk`); the numeric bound is false at the per-log caps (`μ_bus = 38` makes the `(α, β)`
    term alone `2^40/|E|`) and true with the stacking window, with a margin of about `2^8`.
    *See:* code-spine C.5, D.3 (b), finding "the declared error is unconstrained" (CS1);
    gt-bus D.4, G4; gt-opening-compile F.1.
  - **2.2.2.6 The phases' definitions are leanVM's.** *States:* nothing in the oracle protocol's
    theorems pins the phases to leanVM: a zero-round phase whose verifier reads the whole stack
    through the oracle and decides the seam itself fills every slot at error zero. What pins
    them is 2.1.1 with its fixture and review of each `Def`. *Status:* `[status: trusted,
    transcribed data]` (as a fact about the design). *See:* code-spine D.3 (d); gt-table-pub E.4
    item 6 (TP13).
- **2.2.3 The relation and the seams** (built definitions the theorems are about).
  - **2.2.3.1 The relation on the stack** (`M3Holds I input q`, `Spine/Instance.lean:219-220`;
    `M3Rel`). *States:* every constraint polynomial of every table vanishes on that table's rows
    read out of `q`; the pushed and pulled 16-tuples (flush rows and boundary blocks of each
    side) are the same multiset (`List.Perm`, counted in ℕ); every count cell is nonzero; every
    public line's cells 0 and 1 hold the statement's values; the instance's auxiliary predicate
    holds. *Status:* `[status: built, definition]`; says what the specification's accept list
    says, clause by clause, and each clause is refuted alone on the toy (probe `P2Relation`).
    *See:* code-spine C.1, D.1; gt-bus E.5; boundary-adaptor A.2.
  - **2.2.3.2 The abstract instance** (`M3Instance`, `Instance.lean:119-148`; `Layout`,
    `Coord`, `BoundaryBlock`, `PublicLine`). *States:* the tables' widths and log-heights, the
    constraint and flush polynomials with a degree bound `d` and its two proofs, the count
    columns, the boundary blocks, the stack layout with its one reading law, the public lines,
    the auxiliary predicate. *Status:* `[status: built, definition]` `[status: trusted,
    transcribed data]` — an instance is data the theorems trust: a layout may alias columns and
    empty the relation (probe `P2Relation`, `toyAlias`); only the toy's relation is known
    inhabited on `main`. *See:* code-spine C.2, D.4, finding "the instance is data the theorems
    trust" (CS8); code-layer1 G.10.
  - **2.2.3.3 The seams** (`Seam.commit`, `Seam.bus`, `Seam.table`, `Seam.pub`, `Seam.flock`,
    `Seam.done`, `Spine/Seams.lean:171-191`). *States:* the output relation of each phase is the
    input relation of the next by definition: `M3Holds` of the oracle; then the linear and
    column claims hold, every term's degree is within `d`, the public lines and `aux` hold;
    then column claims, lines, `aux`; then column claims and `aux`; then column and weighted
    claims; then `True`. *Status:* `[status: built, definition]`; each seam inhabited and refuted
    per conjunct (probe `P3aSeams`). `[review: wrong]` on `Seam.bus`: it admits statements the
    deployed table sumcheck cannot serve (any number of claims, unrelated points, any table, a
    degree clause on the statement alone), so guards leanVM lacks are forced into the table
    phase (2.3.2.6). *See:* code-spine C.3, D.2, finding "the degree conjunct" (CS2);
    gt-table-pub E.1, finding "the bus seam admits statements" (TP1); gt-bus E.4, G10.
  - **2.2.3.4 The claim types** (`ColumnClaim`, `VirtualTerm`, `LinearClaim`, `Weight`,
    `WeightedClaim`, each with `.Holds`, `Seams.lean:57-124`). *States:* a column claim is an
    evaluation of a column at a point through the layout; a linear claim is a weighted sum of
    extensions of `K`-polynomials of one table's rows; a weighted claim is `Σ_w W(w)·q(w) = c`
    with the weight's cube values and its evaluator agreeing. *Status:* `[status: built,
    definition]`; `Weight.onCube` carries `2^μ` values no deployed verifier builds
    (gt-flock-ring 8.16). *See:* code-spine A; gt-opening-compile A.6.
- **2.2.4 The commit phase** (`commitDef`, `commitComplete`, `commitSecurity`, `Compose.lean:51-71`;
  `Component.sendOracle`, `SendOracle.lean`). *States:* one prover message, the stack itself,
  becomes the oracle; the output relation is `M3Holds` of the oracle; perfectly complete;
  knowledge sound at error zero with the extractor that returns the message. *Feeds:* 2.2.1,
  2.2.2 (first component of the bundle). *Status:* `[status: built and proved]` (probe
  `P3bCommit`). ArkLib's own `SendSingleWitness.oracleReduction_completeness` is admitted; the
  local version is justified by the named form. *See:* code-spine D.6; lib-arklib G.8.
- **2.2.5 Transport of knowledge along the adaptor** (`Refinement`, `Refinement.map_option_valid`,
  `ToArkLib/Refinement.lean:31-57`; `Extractor.Straightline.map`). *States:* validity of one
  extracted witness slot for `M3Rel` gives validity of its image under `witnessOf` for
  `SatisfiedBy` (pointwise). *Feeds:* 2.0.1. *Status:* `[status: built and proved]`; the
  probabilistic transport, which the blueprint calls unproved and consumer-less, is three
  lines in the event form (probe `P6Surface`, `knowledge_transport`) and Layer 13 is its
  consumer; the lemma has the polarity of the good event where the game needs the bad one
  (one line to flip); `Extractor.Straightline.map` cannot serve (its target witness must be in
  `Type`, and `EnsembleWitness` is in `Type 1`). *See:* code-spine C.7, D.7, finding "knowledge
  transport is three lines" (CS9); boundary-adaptor E.6, finding 13.
- **2.2.6 The adequacy of the notion** (ArkLib's `rbrKnowledgeSoundnessWorstCaseWith`,
  `Security/RoundByRound.lean:553-569`; `KnowledgeStateFunction`, `:164-189`). *States:* what
  the definition guarantees (lib-arklib D.1) matches the literature's round-by-round knowledge
  soundness in its worst-case-per-prefix form, with one difference: the extractor may be any
  function, classical choice included, so the existential forms (`rbrKnowledgeSoundness`,
  `rbrKnowledgeSoundnessWorstCase`, hence `piop_rbrKnowledgeSoundness_exists`) prove
  soundness only. *Status:* `[status: library, proved at the old pin]` as a definition;
  `[review: wrong]` for every blueprint interface stated in the existential form (Layer 9's
  `FlockInterface.rbrKnowledgeSoundness`, Layer 10's sketch). *See:* lib-arklib D.2, D.4, D.6,
  G.1 (AK1); literature A.3 (last paragraph).

### 2.3 The phases (the fields of `Phases.Complete` and `Phases.Security`)

Each phase owes three things at its two seams: a definition (`Phase.Def`: schedule, prover,
verifier, per-challenge error), perfect completeness (`Phase.Complete`), and round-by-round
knowledge soundness with a named extractor and state function (`Phase.Security`). Until every
hole is filled, the two bundles are assumed interfaces (`bp:1419-1426`): today
`[status: trusted, assumed interface]` for the bus, table, Flock and opening phases.

#### 2.3.1 The bus phase (Layer 6; `Seam.commit → Seam.bus`)

- **2.3.1.1 Definition** (`busPhase`, `bp:955-963`). *States:* the verifier draws `(α, β) ∈ E^5`;
  the prover sends the two roots `(R, R_c)` (one root for both bus sides); a combiner `λ` after
  the roots and after every layer (the last drawn and never used); the batched radix-4 GKR
  over the three fingerprinted product trees (push, pull, count), odd first layer if `μ_bus`
  is odd, ending at one point `ζ = (u_0, u_1, χ_0, …)` drawn entirely in the last layer; the
  check `R_c ≠ 0`; the five boundary evaluations; the output is `B + 3` linear claims (one per
  constraint at `ζ_{<τ_j}` with value 0; the push, pull and count forms with the derived
  `rem_s`) and five column claims, everything expressible as a `BusOut I`. *Status:*
  `[status: specified only]` `[review: wrong]` — the sketch has `StmtIn := Unit`, a `BusOut`
  with `ζ, rem, pool, α, β` the spine does not have, an undefined `LeafLayout`, one combiner
  per layer, and a degree-5 round message where the deployed GKR sends the degree-4 cofactor
  with `c_0` derived and no round check. *See:* gt-bus A.3, A.4, E.1, G1, G2, G8, G11; register (GB1, GB2, GB11).
- **2.3.1.2 Perfect completeness** (`busPhase_perfectCompleteness`, `bp:971`). *States:* from
  `M3Holds`: the zerocheck claims hold at every point; the two products are one element;
  `R_c ≠ 0` since every count is nonzero; every layer check passes (no inverse of a challenge);
  the bus forms hold with the derived `rem_s` by the leaf decomposition; the degree conjunct of
  `Seam.bus` by `constraints_degree` and `flushes_degree`, provided `1 ≤ d` whenever there is a
  count column. *Status:* `[status: specified only]`; provable on paper. *See:* gt-bus E.2, G10.
- **2.3.1.3 Knowledge soundness** (`busPhase_rbrKnowledgeSoundness … (busError s)`, `bp:972`).
  *States:* one knowledge state function for the whole phase (gt-bus D.3's table): after
  `(α, β)` "the two products of `q`'s leaves are equal and every count is nonzero, the
  constraints vanish, lines and `aux` hold"; after the roots "`R` is both products and `R_c` the
  count product, nonzero"; along the GKR the running claims are the true values; on the last
  layer's challenges the zerocheck restriction `Z(T)` is carried coordinate by coordinate;
  after the boundary evaluations every output claim holds. *Status:* `[status: specified
  only]`; provable on paper, but not as the blueprint plans it (2.3.1.3.6). *See:* gt-bus D.3,
  E.2. Its leaves:
  - **2.3.1.3.1 Balance from the product equality** (`sideProduct_collision`, Theorem 5.1;
    `sideProduct_poly_eq_iff`, Lemma 5.2). *States:* unequal multisets of at most `2^μ`
    16-tuples give unequal polynomials in `K[A_0..A_3, X]` (unique factorization: the factors
    `X − π_A(t)` are monic linear, `t ↦ π_A(t)` injective), so they collide at `(α, β)` with
    probability at most `4·2^μ/|E|` (total degree 4 in `(α, β)`; Schwartz–Zippel). The
    specification leaves Lemma 5.2's proof `TODO`. *Status:* `[status: specified only]`
    (Layer 5, hole G4). *See:* gt-bus D.1, E.2; blueprint acceptance test 1; 2.5.3.
  - **2.3.1.3.2 Nonzero counts from `R_c ≠ 0`** (check B13). *States:* exact, no probability:
    the true count product is nonzero iff every count cell is (padding leaves are `1`).
    *Status:* `[status: specified only]`. *See:* gt-bus B (B13), E.2; acceptance test 3.
  - **2.3.1.3.3 One root, not two** (check B12). *States:* structural: one stream scalar read
    into both slots; with two roots and no comparison any unbalanced stack passes. *Status:*
    `[status: specified only]`. *See:* gt-bus B (B12), G13; acceptance test 4.
  - **2.3.1.3.4 The GKR's errors** (`gkrError`, `bp:941-942`; 2.5.4). *States:* a combiner
    costs `(nside − 1)/|E| = 2/|E|` (a nonzero quadratic in `λ`), the last one `0`; a layer
    sumcheck round `4/|E|` (two distinct polynomials of degree at most 4 agree at 4 points; the
    normalized cofactor is what the verifier holds); a combination pair `2/|E|` (`1/|E|` per
    coordinate), the binary layer's single challenge `1/|E|`; a prover message costs nothing
    given the layer check. *Status:* `[status: specified only]` `[review: wrong]` — the blueprint
    charges `5/|E|` per round (the error of a different verifier that keeps the equality factors),
    omits the last combiner and the binary layer's challenge. *See:* gt-bus D.3, D.4, G1, G2, G12.
  - **2.3.1.3.5 The recycled zerocheck point** (acceptance test 6; row *Seams* `bp:333`;
    `bp:1001-1003`). *States:* with the state a conjunction `G ∧ Z`, the escape "some
    constraint is violated on the cube but every `C̃_{j,i}(ζ_{<τ_j}) = 0`" costs at most `1/|E|`
    per coordinate of `ζ` once for all constraints (a multilinear restriction becomes zero for
    at most one value of the next variable), and the error of a coordinate is the maximum of
    the GKR's and `1/|E|`, that is the GKR's: the recycled point adds nothing to `busError`.
    *Status:* `[status: specified only]` `[review: wrong]` — charged in the blueprint in three
    incompatible ways (per coordinate per constraint; `τ_max/|E|` per constraint to the `(α, β)`
    and GKR challenges, though `(α, β)` precede `ζ`; nothing in `busError`). *See:*
    gt-table-pub D.3; gt-bus D.3, G6 (GB6, TP5).
  - **2.3.1.3.6 The GKR as a separate component cannot be appended** (`bp:930-937`). *States:*
    Layer 5's `gkr` has the leaf tables as its oracles while a phase's one oracle is the stack;
    carrying the stack along needs ArkLib's `liftContext` theorems, admitted at both pins, and
    an appended state function cannot carry the zerocheck clause that changes with the GKR's
    challenges. *Status:* `[status: unprovable as written]` `[review: unprovable]` — restate the
    GKR over a context with leaves and riders, or prove the phase with one state function.
    *See:* gt-bus G3 (GB3); lib-arklib B.3 (ledger A4).
  - **2.3.1.3.7 The leaf decomposition** (`leaf_decomposition`, `bp:969-970`; Layer 1's
    `Blocks.stack_eval_ambient_one`, `Stack.lean:118`). *States:* the extension of a
    one-padded leaf stack at `ζ` is `Σ_b eq(sel_b, ζ_hi)·(β − Σ_i eq(α, i)·c̃_{b,i}(ζ_lo)) +
    (1 + Σ_b eq(sel_b, ζ_hi))`, equation (2) of §5.4 in characteristic two. *Status:* `[status:
    built and proved]` for the Layer 1 identity (probe `ValuesProbe`); the phase-level statement
    over the leaf layout `[status: specified only]`. *See:* code-layer1 B.3, A.5; gt-bus A.5.
  - **2.3.1.3.8 The leaf stacks' layout** (the three unowned blocks first; ties by column
    index). *States:* the order of blocks of equal size decides offsets, selectors and the
    verdict; `M3Instance.tuples` lists flush tuples first, the opposite of the deployed leaf
    order. *Status:* `[status: not specified]` `[review: missing]`. *See:* gt-bus G7 (GB7);
    code-layer1 G.3.
  - **2.3.1.3.9 Two side conditions on the instance** (`1 ≤ d` with a count column; every table
    with a constraint has a flush or count on the bus). *Status:* `[status: not specified]`
    `[review: missing]`; leanVM's instance meets both. *See:* gt-bus G10 (GB10).
  - **2.3.1.3.10 The order of the roots, the boundary evaluations and the linear claims.**
    *Status:* `[status: not specified]` `[review: missing]`. *See:* gt-bus G8 (GB8).

#### 2.3.2 The table sumcheck phase (Layer 7; `Seam.bus → Seam.table`)

- **2.3.2.1 Definition** (`tableSumcheck`, `tableSummand`, `bp:986-990`). *States:* the
  verifier draws `ξ`; constraint `i` of table `t` takes `ξ^{o_t+i}`, the three bus sides
  `ξ^{B+s}` shared by every table; the target `Σ_s ξ^{B+s}·rem_s` is derived, never sent;
  `τ_max` rounds (the maximum over the six opcode tables), highest variable first, each with
  three coefficients `c_0, c_2, c_3` on the wire and `c_1` derived from the running claim;
  table `t` joins at round `τ_max − τ_t` with the weight `∏_{m<τ_t}(1+ζ_m+r_m)·∏_{m≥τ_t} r_m`
  (back-loaded padding); the final message is one value per column of every opcode table (104
  for leanVM, the eighteen BLAKE2S limbs included); the final check reproduces the running
  claim; the claims pooled are the 104 column claims after the five received. *Status:*
  `[status: specified only]` `[review: wrong]` — the sketch's types predate the spine
  (`StmtIn := BusOut` with `rem`, `StmtOut := BusOut × ColumnClaims`); `τ_max` and the final
  message range over every table of the instance, so with Layer 3's column-only tables the
  schedule has at least 16 rounds and 110 values where leanVM has `τ_max` (as few as 3) and
  104; the oracle protocol sends four coefficients and checks the round where the wire carries
  three and no check (a transport lemma is owed and unstated). *See:* gt-table-pub A.1, C.2,
  findings "the table sumcheck's tables are not distinguished" (TP2), "the round message" (TP4),
  "Layer 7's sketch" (TP6); gt-bus G16.
- **2.3.2.2 The target identity** (`tableSummand_target`, `bp:991`). *States:* the cube sum of
  the back-loaded, eq-weighted summand equals `Σ_s ξ^{B+s}·rem_s` (the zerocheck claims
  contribute 0). *Status:* `[status: specified only]`; its two Layer 1 ingredients are built:
  `sumCube_padHigh` (`Padding.lean:64`, the lift by `∏_{k≥τ_j} X_k` keeps the sum) and
  `evalMle_padHigh` (`:70`, the extension the verifier's final weight uses). *See:*
  code-layer1 A.6, B.4, G.9 (acceptance test 7 names the wrong lemma); acceptance tests 7, 9.
- **2.3.2.3 Perfect completeness** (`tableSumcheck_perfectCompleteness`, `bp:993`). *States:*
  on a statement in `Seam.bus` and a stack satisfying it, the honest round polynomials pass and
  the final values are the true column values. *Status:* `[status: unprovable as written]`
  `[review: unprovable]` — against `Seam.bus` as built the deployed sumcheck is not complete
  (terms of one table at unrelated points need one `eq` factor per term; a term on a table
  taller than `τ_max` cannot be folded); provable only for a generalized phase with the guards
  of 2.3.2.6, or after the seam carries the deployed shape. *See:* gt-table-pub E.1 (a) to (d), E.4.
- **2.3.2.4 Knowledge soundness** (`tableSumcheck_rbrKnowledgeSoundness`, `bp:994`; state
  function of gt-table-pub D.2). *States:* before `ξ` every input claim's discrepancy is zero;
  after `ξ` the batching polynomial `Σ_c δ_c X^c` vanishes at `ξ` (error `(k−1)/|E| =
  (B+2)/|E| = 4/|E|`, tight); after each round the running claim is the true partial sum
  (`3/|E|` per round, tight: two cubics agree at three points); after the final message every
  column claim holds (no error on a prover message). Back at the bus seam: a false column
  claim, false lines or `aux` are handed on (error 0). *Status:* `[status: specified only]`;
  the two charged terms are correct, tight and on the right challenges. *See:* gt-table-pub
  D.2, E.3.
- **2.3.2.5 The generic sumcheck it rests on** (2.5.1). *Status:* `[status: specified only]`
  locally; ArkLib's single-round bound `[status: admitted upstream]`.
- **2.3.2.6 The guards the seam forces** (degree of every term at most `I.d`; at most `B + 3`
  claims; one point; the tables the sumcheck opens). *States:* ArkLib's round-by-round notion
  quantifies over every input statement (`toFun_empty` is an `iff`), so a verifier must reject
  a statement outside the seam that its checks would otherwise accept: without the degree
  guard a true cubic claim passes the all-zero run; without the count guard `err ξ ≥
  (k−1)/|E|` for every `k`. *Status:* `[status: not specified]` `[review: missing]` — the
  deployed verifiers have no such checks; smallest fix: the shape in the type (`BusOut` as the
  Rust's `BusVerify`: one point, forms per side and table with the degree in the type, three
  totals) or a subtype for the polynomial. *See:* gt-table-pub E.1, finding TP1; code-spine
  C.3, finding CS2.
- **2.3.2.7 The eighteen limb claims as column claims.** *States:* a limb claim at `z` is the
  claim on `q_flock` at `(slot bits, z, selector)`; it rests on the layout's reading law
  (strided low-index selection), which no built layer supplies. *Status:* `[status: not
  specified]` `[review: missing]` (the strided reader, 2.5.6.3). *See:* gt-table-pub E.2;
  code-layer1 G.1; gt-flock-ring 5.4, 8.2.

