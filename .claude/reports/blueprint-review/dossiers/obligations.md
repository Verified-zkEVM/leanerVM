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

#### 2.3.3 The public-input phase (Layer 8; `Seam.table → Seam.pub`; built)

- **2.3.3.1 Definition** (`publicInputPhase`, `PublicInput.lean:376-381`; `pSpec` `:99`,
  `prover` `:208`, `verifier` `:229`, `check` `:136`, `pooled` `:127`, `expectedValues` `:132`,
  `lineValue` `:119`, `linePoint` `:65`). *States:* one challenge `r ∈ E`; the prover sends, as
  one `List E`, the values at `r` of the lines whose value is sent; the verifier checks the
  message equals the expected values `(1 + r)·cell0 + r·cell1` and rejects otherwise; it pools
  one claim per line, on the line's column at `(r, 0, …, 0)`, with the value it computes, after
  the received claims. *Status:* `[status: built, definition]`; `noncomputable` for its real
  error only. Faithful to §8.2's per-limb check; `[review: wrong]` in one respect: the three
  executable verifiers (Rust, Python, the recursion guest) check one combined equation
  `c_0 + y·c_1 = w_0 + r·(w_0 + w_1)` and pool the scalars sent, and the blueprint assigns their
  soundness to Layer 12, which can neither state nor detect it. *See:* code-pubinput B.1, A,
  G.2 (PI2); gt-table-pub F, finding TP3.
- **2.3.3.2 Perfect completeness** (`complete`, `:300`; `publicInputComplete`, `:384`).
  *States:* from the table seam, for every `r`, the honest values pass the check and the pool
  is in the public seam. *Status:* `[status: built and proved]` (probe `Probe0Baseline`, re-run
  at the new pin: three standard axioms). *See:* code-pubinput F; probes-rerun 1.0.
- **2.3.3.3 Knowledge soundness** (`rbr`, `:350`; `stateFunction`, `:327`; `extractor`, `:317`;
  `publicInputSecurity`, `:391`). *States:* worst-case round-by-round knowledge soundness at
  `1/|E|` on the one challenge: outside the table seam, at most one `r` puts the pool in the
  public seam (`bad_challenge_unique`); the bound is attained (`badLine`). *Status:* `[status:
  built and proved]`. `[review: wrong]` on what it protects: the check on the message is not
  load-bearing for any theorem of the phase, because `pooled` reads the statement, not the
  message; a verifier that ignores the message has the same `Phase.Security` (probe
  `ProbeAnyCheck`, `securityG`). The requirement "a missing check leaves knowledge soundness
  unprovable" fails for this check; pooling the values sent, as §8.2 and the deployed verifiers
  do, restores it. *See:* code-pubinput C.3, C.4, F, G.1 (PI1).
  - **2.3.3.3.1 The line identity** (`eval₂Mle_linePoint`, `:71`). *States:* the extension at
    `(r, 0, …, 0)` is `(1 − r)·q(0) + r·q(1)`; the bit order (coordinate 0 is the low bit) is
    proved, from Layer 1's `evalMle_append_boolVec` at slice zero. *Status:* `[status: built
    and proved]`. *See:* code-pubinput A, negative results.
  - **2.3.3.3.2 Two distinct lines through `K`-cells meet at most once** (`line_challenge_unique`,
    `:152`, private; `bad_challenge_unique`, `:186`). *States:* cells differing by `(a, c) ≠ 0`
    are hit when `(1 + r)·a + r·c = 0`, one `r` at most (`ofK` injective, characteristic two).
    *Status:* `[status: built and proved]`.
  - **2.3.3.3.3 The uniform sampler's law** (`probEvent_uniformSample_le_of_subsingleton`,
    `ToVCVio/UniformSample.lean:44`; `…_of_card_le`, `:35`). *States:* an event with at most
    `k` witnesses has probability at most `k/|α|` under `$ᵗ α`; uniformity is a law of VCVio's
    `SampleableType`, so no instance can be non-uniform. *Status:* `[status: built and proved]`
    (probe `CountingBounds`); redundant with VCVio's `prEvent_uniformSample_le_div_iff` at the
    new pin. *See:* lib-others E.4, G.10; 2.5.7.2.
  - **2.3.3.3.4 The guarded-verdict lemmas** (`Verifier.GuardedForm.of_probEvent_pos`,
    `ToArkLib/GuardedVerdict.lean:40`; `Reduction.mem_support_run_of_guarded`, `:73`). *States:*
    if a guarded verifier can output a statement with a property, its check passed and its
    verdict has it (the last law of a knowledge state function); every outcome of a run is a
    prover run plus the verdict. *Status:* `[status: built and proved]`; restated on VCVio's new
    probability API at `144c5aa` with the same bounds (brief §8). *See:* code-pubinput A.
  - **2.3.3.3.5 The verdict as an ordinary verifier** (`verifier_verify`, `:253`; `guarded`,
    `:273`; `keepOracles`, `materializeOutput_of_keepOracles`, `ToArkLib/KeepOracles.lean`).
    *Status:* `[status: built and proved]`.
- **2.3.3.4 The deployed verifier's phase** (`deployedPhase`, `deployedSecurity`; no blueprint
  name). *States:* the combined check on the two words with the values sent pooled is knowledge
  sound at `1/|E|`: the words' equation with true claims at two distinct challenges forces the
  cells and zero top limbs (`accepts_two_challenges`). *Status:* `[status: not specified]`
  `[review: missing]`; key lemma proved in a probe (`ProbeWordsLemma`), the full `Phase.Security`
  on paper. *See:* code-pubinput C.13, G.2.
- **2.3.3.5 The top limb** (the third public line `mem_2` with cells `(0, 0)`, `sent = false`).
  *States:* the claim on `mem_2` is pooled with value 0 although no scalar is sent; every
  theorem of the phase and the spine holds for an instance with two lines; what a missing third
  line breaks is the adaptor's `satisfiedBy_witnessOf` at `SatisfiedBy.word0_eq`, whose
  right-hand side has a zero top limb by the type of `PublicInput`. *Status:* `[status:
  specified only]` (Layer 3 lists the line; `PublicLine.sent` is pinned by prose only).
  *See:* code-pubinput D, G.3, G.4; boundary-adaptor D; acceptance test 10 (names the wrong witness).

#### 2.3.4 The Flock phase (Layer 9; `Seam.pub → Seam.flock`; nothing built)

Today nothing named `FlockInterface`, `FlockWitnessGen`, `limbColumns` or `flockError` exists
in Lean; the only instance built has `aux := True`, and on it a Flock phase that checks nothing
is knowledge sound at error zero (probe `NoCheckFlock`). Issue #3 records "Flock F0 has not
started". Everything below is `[status: trusted, assumed interface]` for a reader of the master
theorems today (gt-flock-ring 7.1).

- **2.3.4.1 Definition** (the blueprint's `FlockInterface`, `bp:1075-1086`). *States, as
  deployed:* fifteen steps (gt-flock-ring 2.2): seven fixed equality coordinates, `k_batch + 1`
  sampled ones, the univariate skip (64 values on the coset, `z_skip`, the interpolant with 64
  assumed zeros), `n_flock = 8 + k_batch` zerocheck rounds with `c_0` derived, `v_a, v_b` with
  `v_c` derived, `α_lc`, eight lincheck rounds with `c_1` derived, the 64 slice values `s_i`,
  the one check (the lincheck terminal identity with the `α³` constant-position term), six
  ring-switching challenges, the derived target `T = Σ_i x^i Φ(s_i)`; the phase reads no
  claim of the pool and adds one weighted claim on the `q_flock` region. *Status:* `[status:
  specified only]` `[review: wrong]` — Layer 9's interface takes the eighteen limb claims as
  input and emits one claim, which with leanVM's verifier has knowledge-soundness error 1 (the
  limb claims stay in the pool and are opened); the spine's slot (`FlockOut` with `columns` and
  `weighted`) is right. The circuit, wire positions, slot map, `g_0`, `φ_8` and the floor exist
  only in the Rust and Python (Category B, no owner). *See:* gt-flock-ring 2, 5.1, 5.5, 8.1,
  8.7 (FR1, FR7); gt-table-pub finding TP7.
- **2.3.4.2 Perfect completeness** (`FlockInterface.perfectCompleteness`, `bp:1083`). *States:*
  the specification's prover (true coefficients) is accepted at every challenge; no verifier
  inverts a challenge-dependent value. *Status:* `[status: specified only]` `[review: wrong]` on
  its obstacle: acceptance test 20 files a completeness failure under `flockError`, a soundness
  error, and attributes to the protocol the inverse `(1 + r_eq)^{-1}` only the Rust prover
  takes (at `r_eq = 1` that prover emits a proof its verifier rejects: an implementation
  defect, probability at most `(k_batch + 1)/|E|`). *See:* gt-flock-ring 4, 8.4, 8.12 (FR4,
  FR12); lib-arklib G.2 (AK2, the disagreement is settled gt-flock-ring's way).
- **2.3.4.3 Knowledge soundness** (`FlockInterface.rbrKnowledgeSoundness … flockError`,
  `flockError_le`, `bp:1084-1085`). *States:* if `aux q` fails, the weighted claim is false
  except with the error; `Σ flockError ≤ (4·k_batch + 163)/|E| + 2^32/|E|`, right for a fixed
  committed polynomial and term by term the Rust's parameters (gt-flock-ring 5.2). *Status:*
  `[status: specified only]` `[review: wrong]` in form: stated in the existential
  `rbrKnowledgeSoundnessWorstCase` (soundness only, 2.2.6) and bundled with completeness
  (`Security extends Complete`). *See:* gt-flock-ring 5.2, 8.5 (FR5); lib-arklib G.1. Its leaves:
  - **2.3.4.3.1 The partially fixed zerocheck** (Annex C.7; `03:95-100`). *States:* `k_batch + 1`
    sampled coordinates at `1/|E|`; the univariate skip `127/|E|` on `z_skip` (two polynomials
    of degree below 128); `2/|E|` per quadratic round; `1/|E|` more on each of the last
    `k_batch` rounds for the constant position. *Status:* `[status: specified only]`.
  - **2.3.4.3.2 The `F_2`-independence of the 128 fixed equality weights.** *States:* the
    hypothesis of the partially fixed zerocheck holds for the pinned constants. *Status:*
    `[status: trusted, hypothesis]`; verified by a Python probe (rank 128), asserted by a Rust
    unit test, stated nowhere in the blueprint. *See:* gt-flock-ring 5.2, 9.3, 7.1 (row 7).
  - **2.3.4.3.3 The lincheck** (`c-flock:112-133`). *States:* `3/|E|` on `α_lc` (degree three),
    `2/|E|` per round for eight rounds; the terminal identity is the phase's only check, and
    without it any `q_flock` passes. *Status:* `[status: specified only]`. *See:* gt-flock-ring 3.
  - **2.3.4.3.4 The constant position** (`z(512, t) = 1`; the `α³` term). *States:* without it
    the all-zero block satisfies the homogeneous R1CS and "the limb slots compress" is false.
    *Status:* `[status: specified only]` `[review: missing]` — absent from the blueprint's and
    the docstring's wording of `aux`. *See:* gt-flock-ring 5.3, 8.6 (FR6).
  - **2.3.4.3.5 Ring switching** (Annex A; `a-ring:104-128`). *States:* the 64 slice claims at
    one point reduce to one weighted claim on the packed polynomial through a random
    `F_2`-linear map built from six challenges; no message, no check; error below `2^32/|E|`
    (a nonzero polynomial of total degree `2^31 + 2^15 + 2^7 + 2^3 + 2 + 1` in `f_0..f_5`); the
    weight's extension has the closed form `Σ_k c_k ∏_n (1 + r_n^{2^k} + r'_n)`. *Status:*
    `[status: specified only]`; needs "`x` has 64 distinct conjugates" and "the `c_k` are
    distinct monomials" (Annex A, tested in the Rust); ArkLib's `RingSwitching/Packing` is a
    different protocol (Diamond–Posen), admitted at both pins, and no profile turns it into
    leanVM's. *See:* gt-flock-ring 6, 8.9 (FR9); lib-arklib B.3 (ledger A9).
  - **2.3.4.3.6 The auxiliary predicate** (`I.aux`; for leanISA "Flock's R1CS with the constant
    position holds of the bits packed into `q_flock`"). *States:* decidable; well defined only
    from the Rust (the circuit, wire positions and slot map are not in the specification).
    *Status:* `[status: specified only]` `[review: unprovable]` as placed: Layer 9 is over an
    abstract `I` whose `aux` is opaque and names no column, count or relation, so the Flock
    phase cannot be written there (a `FlockRegion I` supplied by Layer 3 is needed). *See:*
    gt-flock-ring 5.3, 8.3 (FR3); code-spine CS8.
- **2.3.4.4 The weighted claim's weight is MLE-friendly** (`Weight.mle_eq` for the
  ring-switched weight). *Status:* `[status: specified only]`, owed by #3. *See:* gt-flock-ring 8.16.
- **2.3.4.5 The limb columns' slot map** (`FlockInterface.limbColumns`, `bp:1077`). *States:*
  eighteen numbers (`hash_flock.rs:87-115`) and a generic low-index selection identity.
  *Status:* `[status: unprovable as written]` `[review: unprovable]` — placed inside an interface
  that takes the instance as parameter while the instance's layout needs it. *See:*
  gt-flock-ring 8.2 (FR2); boundary-adaptor finding 7; code-layer1 G.1.
- **2.3.4.6 The constants** (`φ_8`, `0xf7, 0x53, 0xb5`, `g_0`, `R1CS_DIGEST`, the floor
  `τ_BLAKE2S ≥ 3`). *Status:* `[status: trusted, transcribed data]`; `R1CS_DIGEST` cannot be
  recomputed at the pin and has no owner. *See:* gt-flock-ring 5.5, 8.14 (FR14).

#### 2.3.5 The opening phase (Layer 10; `Seam.flock → Seam.done`)

- **2.3.5.1 Definition** (`openingPhase`, `bp:1112-1113`). *States, as the blueprint has it:*
  the verifier draws `λ`; a `μ`-round sumcheck on `W_λ·q`; a final evaluation query of `q̃`.
  *As deployed:* after `λ` (drawn after the six ring-switching challenges, every claim value
  already bound; the ring-switched claim takes `λ^0`, the pooled claims the next powers in
  pool order; `J = 113`) the next message is WHIR's first round polynomial; the sumcheck rounds
  that reduce the weighted claim are WHIR's own, interleaved with its levels, and the protocol
  ends on one equation, never on an evaluation of `q̃` at a point. *Status:* `[status: wrong as
  written]` `[review: wrong]` — a `verify` built as written has `μ` extra round polynomials, one
  extra challenge and one extra scalar and rejects every Rust proof; `verify_iff_compiled` is
  then false. The fix that keeps the spine's statements: give the stack the inner-product
  oracle interface (a query is a `Weight μ`, the answer `Σ_w W(w)·q(w)`, the idealization of
  Definition 3.13); the opening phase is then "`λ`, then one weighted query", a one-challenge
  component, and WHIR realizes that one query (typechecked against ArkLib at the pin, probe
  `InnerProductOracle`). *See:* gt-opening-compile A.1 to A.5 (recommendation (ii)); brief §7.
- **2.3.5.2 Perfect completeness.** *States:* by linearity of `Weight.pair`, the batched claim
  holds of `q` when every pooled claim does. *Status:* `[status: specified only]`.
- **2.3.5.3 Knowledge soundness** (`openingPhase_rbrKnowledgeSoundness`, `bp:1114`). *States:*
  before `λ` "some pooled claim is false of `q`"; after `λ` "the batched claim is false of
  `q`", error `(J − 1)/|E|` on `λ` (a nonzero polynomial of degree below `J`); the one query
  makes the verdict. *Status:* `[status: specified only]`; the blueprint's "`2/|E|` per round"
  is the tail's value of Theorem B.7 and belongs to no round of this phase. *See:*
  gt-opening-compile A.5 (table, Layer 10 row), B.6.
  - **2.3.5.3.1 A column claim is a weighted claim** (`ColumnClaim.holds_iff_weighted`,
    `ClaimWeights.lean:58`; `eqWeight`, `eqWeight_pair`, `Weight.pair_eq_sumCube`). *States:*
    a claim on column `c` at `z` is the weighted claim with weight `eq(extend c z, ·)`; the
    strided limb claims need the strided extension (2.5.6.3). *Status:* `[status: built and
    proved]` (probe `ValuesProbe`). *See:* code-layer1 A.7, B.7.
  - **2.3.5.3.2 The pool's order and the assignment of the powers of `λ`.** *Status:*
    `[status: specified only]` (convention *Claim pool order*, `bp:324`); agrees with the three
    sources. *See:* gt-opening-compile A.2, A.6; gt-flock-ring negative results.
  - **2.3.5.3.3 The batching component** (2.5.2).
- **2.3.5.4 `Seam.done` is `True`.** *States:* the last phase leaves nothing to check; the
  opening's knowledge soundness therefore says "if the verifier accepts, every pooled claim
  holds of `q` except with the error". *Status:* `[status: built, definition]` (`Seam.done =
  Set.univ`, probe of code-spine E.2).

### 2.5 The generic components and the layers below the phases

#### 2.5.1 Sumcheck for eq-weighted virtual polynomials (Layer 4, holes G1 and G2)

- **2.5.1.1 Definition** (`Virtual`, `sumcheck`, `bp:880-893`). *States:* `n` rounds, each a
  round polynomial of degree `d` sent as `d + 1` coefficients and a challenge, then the claimed
  table values at the point; the output relation says each value is the table's extension at
  the point and the formula reproduces the running claim. *Status:* `[status: specified only]`
  `[review: missing]` — two variants are needed and only the plain one is defined: the
  normalized (Gruen) variant, whose round message is the cofactor of degree `d` with `c_0`
  derived through the equality factor and no equality factor in the final check, is the one
  the GKR runs; the table sumcheck sends three of four coefficients with `c_1` derived. *See:*
  gt-bus G1 (GB1); gt-table-pub A.1 (T5, T6).
- **2.5.1.2 Perfect completeness** (`sumcheck_perfectCompleteness`, `bp:894`). *Status:*
  `[status: specified only]`; ArkLib's `Sumcheck.Spec.SingleRound.reduction_perfectCompleteness`
  is `[status: admitted upstream]` (through the admitted `liftContext_perfectCompleteness`),
  which the blueprint's ledger row A1 omits. *See:* lib-arklib B.3 (row A1).
- **2.5.1.3 Round-by-round knowledge soundness** (`sumcheck_rbrKnowledgeSoundness … (fun _ ↦
  d/|F|)`, `bp:895-896`). *States:* if the running claim is false before a round, the prover's
  message differs from the true round polynomial and the two agree at most at `d` points.
  *Status:* `[status: specified only]`; ArkLib's `Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundness`
  and its lens instances `[status: admitted upstream]` at both pins (ledger A1). *See:*
  lib-arklib B.3, F.1.
  - **2.5.1.3.1 Two distinct polynomials of degree at most `d` agree at most at `d` points**
    (Mathlib `Polynomial.card_roots'`, `Polynomial.eq_of_degree_le_of_eval_finset_eq`).
    *Status:* `[status: library, proved at the old pin]`. *See:* `bp:275-277`.
  - **2.5.1.3.2 The uniform sampler's counting bound** (2.3.3.3.3).
  - **2.5.1.3.3 The round identity as derivation** (the wire drops one coefficient; the
    verifier derives it from the running claim). *States:* the dropped-coefficient encoding is
    inverted by the running claim, so a protocol that sends all coefficients and checks the
    identity accepts the same transcripts as one that derives; Fiat–Shamir absorbs different
    data, so a transport lemma is owed. *Status:* `[status: not specified]` `[review: missing]`.
    *See:* gt-table-pub finding TP4; gt-bus B (B15).
- **2.5.1.4 The eq-weighted, back-loaded variant** (`bp:898-904`). *States:* tables of
  different heights lifted by `∏_{k ≥ τ_j} X_k` (`sumCube_prodVars`, `sumCube_padHigh`), the
  verifier's running weight `∏` of the challenges a table sat out, `eq(ζ_{<τ_j}, ·)` as an
  explicit factor evaluated by the verifier. *Status:* the Layer 1 identities `[status: built
  and proved]` (`Padding.lean:47, 64, 70`); the variant `[status: specified only]`. *See:*
  code-layer1 A.6, B.4.

#### 2.5.2 Batching by the powers of one challenge (Layer 4, hole G3)

- **2.5.2.1 Definition and knowledge soundness** (`batchClaims`, `batchClaims_rbrKnowledgeSoundness
  … (k − 1)/|F|`, `bp:907-911`). *States:* the invariant "some claim is false"; escape needs the
  batching polynomial, of degree below `k`, to vanish at the challenge. *Feeds:* 2.3.2.4 (`ξ`),
  2.3.5.3 (`λ`), the GKR's combiners, WHIR's per-level batching. *Status:* `[status: specified
  only]`; ArkLib #615's `gammaPowers` is a pattern. *See:* gt-table-pub D.2 (the argument, worked).

#### 2.5.3 Fingerprints and the grand product (Layer 5, hole G4)

- **2.5.3.1 The fingerprint and the side product** (`fingerprint`, `sideProduct`, `bp:923-924`).
  *States:* `π_α(t) = Σ_{i<16} eq(α, bits i)·t_i` with `α ∈ E^4`; the product over the multiset
  of `β − π_α(t)`; padding leaves are `1`. *Status:* `[status: specified only]`
  `[status: built, definition]` for the bit order (`bitProductTable`, `lagrangeBasis`).
- **2.5.3.2 The product polynomial determines the multiset** (`sideProduct_poly_eq_iff`,
  Lemma 5.2, `bp:926-928`). *States:* in `K[A_0, …, A_3, X]` the products of the monic linear
  factors `X − π_A(t)` agree iff the multisets do (unique factorization; monic factors are
  equal, not merely associate; `t ↦ π_A(t)` injective). *Status:* `[status: specified only]`;
  Mathlib's `UniqueFactorizationMonoid` on `MvPolynomial` `[status: library, proved at the old
  pin]`; the specification's proof is `TODO`. *See:* gt-bus E.2; `bp:278-279`.
- **2.5.3.3 The collision bound** (`sideProduct_collision`, Theorem 5.1, `bp:929-931`).
  *States:* unequal multisets of size at most `2^μ` collide at `(α, β)` with probability at
  most `4·2^μ/|E|` (total degree `4N`, `N ≤ 2^μ`). *Status:* `[status: specified only]`;
  Schwartz–Zippel `[status: library, proved at the old pin]` (ArkLib
  `schwartz_zippel_counting` in the root namespace, `prob_eval_zero_le_div` a `PMF`
  statement: the blueprint's names are wrong). *See:* lib-arklib G.6 (AK6); acceptance test 1.

#### 2.5.4 The batched radix-4 GKR (Layer 5, holes G5 and G6)

- **2.5.4.1 Definition** (`ProductTree`, `gkr nside μ`, `gkrError`, `bp:933-944`). *States:*
  from the roots to the leaf claims: radix 4 from the root down, one radix-2 layer first if
  `μ` is odd; a combiner after the roots and after every layer (the last unused); per layer
  `k = μ − layer` normalized sumcheck rounds of degree 4, twelve children, the layer check
  `claim = Σ_s λ^s ∏ children[s]` with no equality factor, two combination challenges; the
  three trees share every challenge and end at one `ζ`. *Status:* `[status: specified only]`
  `[review: wrong]` (degree 5, one combiner per layer, no binary-layer error; 2.3.1.3.4).
  *See:* gt-bus A.4, D.4, G1, G2, G12.
- **2.5.4.2 Perfect completeness** (`gkr_perfectCompleteness`, `bp:942`). *Status:*
  `[status: specified only]`; an honest GKR prover written from the specification is accepted
  by the pinned Python verifier (gt-bus probe H.1).
- **2.5.4.3 Round-by-round knowledge soundness** (`gkr_rbrKnowledgeSoundness … (gkrError nside
  μ)`, `bp:943-944`). *States:* per challenge as in 2.3.1.3.4; the layer check turns a false
  running claim into a false child. *Status:* `[status: specified only]`; the specification
  states no error for the GKR (gt-bus G17). Its leaves: the sumcheck of 2.5.1 in its normalized
  variant; the batching of 2.5.2 for the combiners; the bilinear interpolation of the four
  children (`1/|E|` per coordinate).

#### 2.5.5 The ring-switching and WHIR components

Ring switching is 2.3.4.3.5 (inside the Flock phase, #3's); WHIR is 2.1.2.4 (Layer 11, the
compilation). Neither is a phase of the oracle protocol; under recommendation (ii) the opening
phase is the batching component alone.

#### 2.5.6 Layer 1: hypercube tables, stacking, padding, claim weights, the fixed columns (built)

Every theorem below is `[status: built and proved]` (seventeen declarations checked with
`#print axioms` by code-layer1, three standard axioms; the sketch matches the code declaration
by declaration). Today an auditor of the master theorems reads none of them; seventeen
definitions become trusted when the adaptor is built, about eight more with the executable
verifier (code-layer1 E).

- **2.5.6.1 The generic identities** (`ToCompPoly/`; over any commutative ring).
  - `evalMle_eq_sumCube_hadamard`, `sumCube_lagrangeBasis` (partition of unity),
    `evalMle_replicate`, `evalMle_lagrangeBasis` (the eq kernel; duplicates CompPoly's
    `eqTilde_eq_prod`) — `Multilinear.lean:91, 125, 131`, `BitProductTable.lean:156`.
  - `evalMle_append_boolVec` (`Multilinear.lean:342`): the extension at `(z, bits of j)` is
    the extension of slice `j` at `z` (high-index selection; the low-index, strided selection
    is absent: 2.5.6.3). `evalMle_placeSlice`, `sumCube_placeSlice` (`:371, 381`).
  - `evalMle_bitProductTable`, `evalMle_powersTable` (`BitProductTable.lean:58, 144`): a table
    that factors over the index bits evaluates as a product.
  - `Blocks.pow_size_dvd_offset` (alignment from the order), `Blocks.stack_eval` (the one
    selector fact: `q̃(z, sel_b) = P̃_b(z)` for the honest stack), `Blocks.unstack_eval₂` (the
    same for a table the prover chose), `Blocks.stack_eval_ambient` (equation (2) of §5.4 for
    any padding) — `Stacking.lean:109, 339, 330`, `AmbientStacking.lean:134`.
- **2.5.6.2 The leanVM half.** `Blocks.readColumn_eval`, `Blocks.layout` (the aligned blocks as
  the spine's `Layout`), `Layout.comap` (renaming; accepts a non-injective renaming, so a layout
  built with it can alias), `Blocks.stack_eval_ambient_one` (padding `1` over `E`, the leaf
  decomposition), `sumCube_padHigh`, `evalMle_padHigh`, `eqWeight`, `eqWeight_pair`,
  `ColumnClaim.holds_iff_weighted`, `idxColumn_eval`, `idxColumnEval_eq` (the index column
  `g^i`, coordinate `k` carrying `g^{2^k}`, §6.5), `bytecodeColumn_answer_boolVec`,
  `bytecodeColumn_eval` (slot `s` of instruction `z` at `(z, s)`, cell for cell the Rust
  encoder's table on a sixteen-instruction program). *See:* code-layer1 A.5 to A.9, B.1 to B.7.
- **2.5.6.3 The strided reader of the eighteen BLAKE2S limb columns** (`sliceLow`,
  `evalMle_boolVec_append`, `Blocks.stridedLayout`, `Layout.piecewise`; no blueprint name).
  *States:* a limb column is read from `q_flock` at the low eight coordinates frozen to the
  slot's bits; the selection lemma is twenty lines (probe `StridedProbe`, proved). *Status:*
  `[status: not specified]` `[review: missing]` — exists nowhere, assigned to no layer;
  `leanIsaInstance` cannot be built without it. *See:* code-layer1 G.1 (L1-1); gt-flock-ring 8.2.
- **2.5.6.4 The order of equal-size blocks.** *States:* the six shared columns first, then
  every table's columns in table order (`witness.rs:67-79`, `cpu/layout.rs:13-49`); `Blocks` is
  the sorted sizes only, and leanVM's order and "tables first" give different offsets with the
  same `Blocks`. *Status:* `[status: trusted, transcribed data]` `[review: missing]` — pinned by
  no statement or test before the compiled verifier. *See:* code-layer1 G.3 (L1-3), B.2 (the
  92 offsets of the pinned Python layout reproduced by `Blocks.offset`).

#### 2.5.7 Layer 0: the fields, the samplers, the oracle interface (built)

- **2.5.7.1 The fields and their cardinality** (`K`, `E`, `card_E : Fintype.card E = 2^192`,
  `Field.lean:96`; CompPoly's `card_ext3`). *States:* `K = GF(2)[x]/(x^64+x^4+x^3+x+1)` as
  64-bit words, `E = K[y]/(y^3+y+1)` as limb triples, bit for bit leanVM's (probe
  `FieldFidelity`: eleven Rust reference products reproduced). *Status:* `[status: library,
  proved at the old pin]` (irreducibility by a Rabin certificate, no `native_decide`); at the new
  pin `BF64` is a structure and `(2 : K) = 0`. *See:* lib-others B, G.8.
- **2.5.7.2 Uniform challenges** (`instSampleableTypeE`, `Field.lean:93`; VCVio's
  `SampleableType`). *States:* uniformity is a law of the class, so the `E` sampler (three limbs
  through a bijection) is uniform by proof; `Pr[= x | $ᵗ E] = 2^{-192}` (probe `Layer0`); the `K`
  sampler has no consumer. *Status:* `[status: built and proved]`. *See:* lib-others E.1, G.2.
- **2.5.7.3 The evaluation oracle** (`evalOracle`, `evalOracle_answer`, `Field.lean:102-113`).
  *States:* a query is a point of `E^n`, the answer `q̃(r) = Σ_i ofK(q_i)·eq(r, i)` in the
  specification's little-endian order. *Status:* `[status: built and proved]`; `[review: wrong]`
  as the interface of the stack: the compilation needs the inner-product interface (2.3.5.1),
  of which evaluation is the case `W = eq(r, ·)`. *See:* lib-others E.2; gt-opening-compile A.5.
- **2.5.7.4 The scalar oracle interfaces** (`instOracleInterfaceE`, `instOracleInterfaceListE`,
  `Field.lean:115-118`). *States:* a scalar or list message is read whole. *Status:* `[status:
  built, definition]` `[status: trusted, transcribed data]`, unlisted in the blueprint's
  interface list. *See:* lib-others G.4 (LO4).

#### 2.5.8 Layer 2: Clean components as polynomials (hole I1; not built)

- **2.5.8.1 Expressions as polynomials** (`Expression.toMvPolynomial`, `eval_toMvPolynomial`,
  `degreeBound`, `totalDegree_le_degreeBound`, `bp:759-765`). *States:* a Clean expression
  evaluates as the polynomial with `var i ↦ X i`; the syntactic degree bounds the total
  degree. *Status:* `[status: specified only]` `[review: unprovable]` as placed: Layer 2
  produces Mathlib `MvPolynomial`s while the instance holds CompPoly `CMvPolynomial`s and the
  conversion is `noncomputable` at the pin, which would make `M3Holds (leanIsaInstance …)`
  undecidable by evaluation and `verify` noncomputable; a direct translation is twelve
  computable lines (probe `PolyBridge`). *See:* boundary-adaptor E.5, finding 8.
- **2.5.8.2 The polynomial view of a component** (`Component.toM3`, `Ensemble.toM3`,
  `toM3_constraints_iff`, `toM3_flushes_eq`, `vars_lt_width`, `bp:767-780`). *States:* the
  constraints of a row vanish iff Clean's `ConstraintsHold` does; the multiset of evaluated
  flush tuples is the interactions mapped to 16-tuples, with the separator and direction given
  per channel. *Feeds:* 2.6.2 (the constraint and balance clauses). *Status:* `[status:
  specified only]`; Clean has no polynomial, degree, height or padding notion. *See:*
  boundary-adaptor A.4; blueprint `bp:781-786`.
- **2.5.8.3 The count columns' derivation.** *States:* which cells are the pulls' count
  coordinates (`count_columns()` per table, `layout.rs:412-414`), which `Component.toM3` cannot
  derive from the separator and direction alone. *Status:* `[status: not specified]`
  `[review: missing]`. *See:* boundary-adaptor finding 11.

### 2.6 The adaptor and what it needs of leanISA and of Flock (Layer 3, hole I2; not built)

The only place the proof system meets leanISA. Nothing of it exists in Lean at `b435631`
(`M3Holds`, `M3Rel` and `Refinement` are built; `leanIsaInstance`, `stackOf`, `witnessOf` and
the four theorems are not).

- **2.6.1 The leanISA instance** (`leanIsaInstance prog s`, `Sizes`, `Sizes.Admissible`,
  `leanIsaInstance_degree`, `leanIsaInstance_flush_degree`, `leanIsaInstance_fits`,
  `bp:794-808`). *States:* the polynomial view of the eight tables with leanISA's separators and
  directions, `d := 2`, three public lines on `mem_0, mem_1, mem_2`, the six shared columns as
  constraint-free tables, the boundary blocks with the index and bytecode columns as `known`
  coordinates, the stack layout of `witness.rs`, `cpu/layout.rs`, `leaf.rs`, the strided
  limbs, the auxiliary predicate. *Feeds:* everything above through `I`. *Status:* `[status:
  specified only]` `[status: trusted, transcribed data]`; `[review: wrong]` on four points: it
  is not `Ensemble.toM3` of the eight tables (the memory and bytecode seed/finalize blocks and
  the state boundary must be boundary blocks with `known` program data, or the program would be
  committed and no adaptor theorem provable); `leanIsaInstance_fits` mentions a field `Layout`
  does not have (the fit belongs to `Blocks`, before the instance); its layout and `aux` depend
  on a `FlockInterface I` that takes the instance as parameter; it must be reducible for the
  tests' `Decidable` search. *See:* boundary-adaptor A.5, E.4, findings 1, 7, 12; code-layer1
  G.2; gt-flock-ring 8.2, 8.3.
- **2.6.2 The soundness bridge** (`satisfiedBy_witnessOf (hs : s.Admissible prog) (h : M3Holds
  (leanIsaInstance prog s) input q) : SatisfiedBy prog input (witnessOf prog s q)`,
  `bp:815-816`). *States:* the witness rebuilt from a stack satisfying `M3Holds` satisfies
  leanISA's thirteen-conjunct relation; carries knowledge from `M3Holds` to `SatisfiedBy` at the
  same error (pointwise, 2.2.5). *Feeds:* 2.0.1. *Status:* `[status: specified only]`; can work
  as sketched for the reason of 2.6.1. *See:* boundary-adaptor A.4, A.5, E.1. Conjunct by conjunct:
  - **2.6.2.1 Clean's constraints** from `ConstraintsVanish` through `toM3_constraints_iff`
    (2.5.8.2). *Status:* `[status: specified only]`.
  - **2.6.2.2 The three `BalancedPair`s (counted in ℕ)** from `Balanced` (a `List.Perm` of
    16-tuples) through `toM3_flushes_eq` **and a bridge for the boundary blocks** against the
    two Clean blocks and the verifier component. *Status:* `[status: not specified]`
    `[review: missing]` for the boundary bridge; leanISA's `BalancedPair` replaces Clean's
    field-summed balance, unsatisfiable over `K`. *See:* boundary-adaptor finding 2; lib-others C.5.
  - **2.6.2.3 `CountsNonzero`** (both relations quantify over the same cells). *Status:*
    `[status: specified only]`; the count columns' derivation is 2.5.8.3.
  - **2.6.2.4 The public words** (`word0_eq`, `word1_eq`) from `PublicLinesHold` on the three
    lines; the top limb is zero by the type of `PublicInput` and needs the third line (2.3.3.5);
    `κ < 64` for `MemImage.read_gpow` from admissibility. *Status:* `[status: specified only]`.
    *See:* boundary-adaptor D; code-pubinput D.
  - **2.6.2.5 `Blake2sRowsValid`** from `aux` through #3's lemma "the R1CS with the constant
    position holds of `q_flock` ⇒ the eighteen limb slots compress" (the functional
    correctness of a circuit with 14,720 AND gates: the forward walk, two adders, leanISA's
    `compress`). *Status:* `[status: trusted, hypothesis]` `[review: missing]` — nothing carries
    it: the sketched signature has no argument for it, `FlockInterface` has no such field, and
    `aux` needs #3's R1CS to be defined. *See:* boundary-adaptor C (row "the R1CS holds ⇒ the
    limb slots compress"), finding 7; gt-flock-ring 5.3, 7.1 (row 2).
  - **2.6.2.6 `Caps`** from `s.Admissible prog`: a hypothesis, since `M3Holds` leaves the caps
    out and `imageOf` truncates above `maxLogMem`. *Status:* `[status: trusted, hypothesis]`,
    discharged by the verifier's setup check (2.7). `admissible_iff_caps` `[status: unprovable
    as written]` (a free `w`; false in either reading; `Sizes.ofWitness` cannot produce the
    rate). *See:* boundary-adaptor E.3, finding 5; gt-bus G4.
  - **2.6.2.7 The three fixed-column facts and decodability** (from the instance's `known`
    columns and the type of `Program`). *Status:* `[status: specified only]`; "statement
    binding" needs the injectivity of `prog ↦ bytecodeColumn prog`, unstated. *See:*
    boundary-adaptor B.2, F.
- **2.6.3 The completeness bridge** (`m3Holds_stackOf (h : SatisfiedBy prog input w) (hs :
  Sizes.ofWitness w = some s) : M3Holds (leanIsaInstance prog s) input (stackOf gen w hs)`,
  `bp:817-818`). *States:* the stack of a satisfying witness (with the Flock wires generated
  from the limbs) satisfies `M3Holds`; the non-vacuity of the whole protocol for leanISA.
  *Feeds:* 2.0.2. *Status:* `[status: specified only]`; needs `Sizes.ofWitness` (ill-defined
  while `Sizes` holds `logInvRate`) and `FlockWitnessGen` with its lemma "the generated wires
  satisfy the R1CS when the limbs compress" `[status: trusted, assumed interface]` (#3's).
  *See:* boundary-adaptor A.6, C; gt-flock-ring 7.1 (row 3).
- **2.6.4 The round trip** (`witnessOf_stackOf … = w`, `bp:819`). *States:* reading the stack
  back gives the witness on the committed fields. *Status:* `[status: unprovable as written]`
  — not an equality any `EnsembleWitness` satisfies (`ProverData` is a function, `Table.width`
  is free); serves nothing on the chain (a non-vacuity test). *See:* boundary-adaptor E.2,
  finding 10, F.
- **2.6.5 `witnessOf` itself** (`bp:812-814`). *States:* rebuilds the tables from the columns,
  the limbs from their slots, the interactions from the components, the image from the memory
  columns, the program from `prog`; total and computable. *Status:* `[status: specified only]`;
  has no `input` argument. *See:* boundary-adaptor finding 11.
- **2.6.6 leanISA's constraint soundness** (`constraintSoundness (hwf : WellFormedBytecode
  prog) (h : SatisfiedBy prog input w) : ∃ t, AssignmentRepresents w t ∧ ValidExecution prog
  input t`, `leanisa-blueprint.md:1156-1177`; T1-S). *States:* every satisfying assignment of a
  well-formed program represents a valid execution. *Feeds:* 2.0.1. *Status:* `[status:
  specified only]` — a block comment, blocked on Clean's ℕ-counted balance (issue #16, Clean
  #452/#464). *See:* boundary-adaptor C; lib-others C.5 to C.7.
- **2.6.7 leanISA's constraint completeness** (`constraintCompleteness (hwf) (h :
  ValidExecution prog input t) : ∃ w, SatisfiedBy prog input w ∧ AssignmentRepresents w t`;
  T1-C). *Feeds:* 2.0.2. *Status:* `[status: specified only]`; needs a resource hypothesis of its
  own (out of scope). *See:* boundary-adaptor note 18.
- **2.6.8 The witness generator** (T2, `witnessGen_correct`, `arch:230-236`). *States:* the
  executable witness generation produces a satisfying, representing assignment. *Feeds:* 2.0.2
  as `docs/architecture.md` states it. *Status:* `[status: not specified]` in the blueprint (out
  of scope, `bp:147-148`); T4's completeness composes T1-C instead. *See:* boundary-adaptor F;
  docs-debt (DD19).

### 2.7 The hypotheses: what a verifier check or a condition on public data discharges

Every hypothesis on the two chains, with what discharges it (from boundary-adaptor C, extended
by the opening and Flock dossiers). Kinds: a condition on public data (P), a property the
verifier checks (V), a theorem another roadmap or library owes (O), nothing (N).

| Hypothesis | Appears in | Kind | Discharged by | Status |
| --- | --- | --- | --- | --- |
| `s.Admissible prog` (caps, `τ_BLAKE2S ≥ 3`, `15 ≤ μ ≤ 28`, `1 ≤ ρ ≤ 4`) | 2.6.2, 2.1.1 | V | `read_public` (`cpu/mod.rs:130-178`), reproduced by `verify`; supplied by `verify_iff_compiled`'s `∃ s` | consistent once `Admissible` carries the two windows (2.1.1.4) |
| the top limb of each public word is zero | 2.6.2.4 | V in the Rust (`cpu/mod.rs:141-143`); by type in Lean | the parser of `PublicInput`; defence in depth through the third line | consistent; the parsing obligation undocumented (boundary-adaptor finding 15) |
| the bytecode is decodable, of power-of-two length `≤ 2^32` | 2.6.2.7 | V in the Rust; by type in Lean | the loader of `Program` | consistent |
| `WellFormedBytecode prog` (sentinel not a `JUMP`; fill blocks) | 2.6.6, 2.6.7 | P (decidable; no verifier checks it; the compiler emits both) | the guest owner (T3) | **N in the blueprint**: `baseVerifier_extractsExecution` has no such hypothesis, `baseProver_complete` has `HasFillBlocks` only |
| `Sizes.ofWitness w = some s` (power-of-two heights) | 2.6.3 | O (leanISA: `Caps.heights`, `seed_rows`, `bytecode_rows`) | `SatisfiedBy` | provable; ill-defined while `Sizes` holds `logInvRate` |
| a resource bound on the trace (every table `≤ 2^32` rows; the stack `≤ 2^28`) | 2.0.2, 2.6.7 | N | nothing: `ValidExecution` bounds nothing but `κ ≤ 32` | **N**: `baseProver_complete` is false without it |
| a witness constructed from the trace | 2.0.2 | O (T2, out of scope) | `constraintCompleteness` gives `∃ w` only | **N** as written |
| the honest grind succeeds | 2.0.2, 2.1.4 | N (a search) | running the prover | **N**: `prove` must be partial |
| `FlockWitnessGen` and its lemma | 2.6.3 | O (#3) | an explicit argument | assumed interface |
| "the R1CS with the constant position ⇒ the limb slots compress" | 2.6.2.5 | O (#3) | nothing names a carrier | **N** until a carrier is named |
| the `F_2`-independence of the 128 fixed equality weights | 2.3.4.3.2 | P (a rank computation on constants) | a Rust unit test; a Python probe | not in any theorem |
| `Phases.Complete`, `Phases.Security` of `leanIsaInstance prog s` | 2.2.1, 2.2.2 | O (holes P1 to P8; the public-input phase built) | the phases | assumed interface until every hole is filled |
| a bound on `piopError P` | 2.2.2.5 | O (this roadmap) | nothing in the spine | **N** today |
| every front phase's verifier makes no oracle query | 2.1.2.3.3 | O (this roadmap) | nothing; the spine's types allow queries | **N** (finding 5.2) |
| `FiatShamirSecurity`, `BcsSecurity`, `McaJohnson` | 2.1.2 | O (ArkLib; the literature) | explicit arguments | assumed interfaces; the first two as stated are false or empty |
| the list-binding compilation, with `L_0` | 2.1.2.3 | O (this roadmap) | nothing | **N** |
| BLAKE2s's compression function is a random oracle; BLAKE2s-256 is collision resistant | 2.1.5 | N (a heuristic) | nothing | **N**: must be written down as the assumption it is |
| the grinding check at every query round (17 bits) | 2.1.2.1.3, 2.1.2.4.7 | V (`fs/lib.rs:165-174`) | `verify` | no planned theorem or mutation makes it load-bearing (literature LT13) |
| the canonical encodings (upper limbs, root halves) and full consumption of the stream | 2.1.1.4 | V | `verify` | none protects soundness; `verify` without them accepts streams the Rust rejects |
| `R1CS_DIGEST` in the seed | 2.3.4.6 | V (a constant compared) | a Rust-produced proof accepted by `verify` | no theorem; not recomputable at the pin |
| the round-by-round ⇒ plain implication | 2.1.2.7 | O (ArkLib, admitted) | "stated once the implication lands" | consistent; forgets the named extractor |
| the count columns are exactly the pulls' count coordinates | 2.6.2.3 | O (Layer 2/3, Category B) | a transcription of `count_columns()` | unspecified |
| the order of equal-size blocks; the leaf stacks' order | 2.5.6.4, 2.3.1.3.8 | O (Category B) | nothing before the fixture | unspecified |

