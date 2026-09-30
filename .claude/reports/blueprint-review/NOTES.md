# Orchestrator's ledger (blueprint review, session of 2026-09-29)

Running notes of the orchestrating session, kept so that the work survives a context compaction.
Read this file first when resuming. Branch: `docs/protocol-blueprint-review` (from `main` at
`b435631`). The user asked (2026-09-29) for the report to be committed to that branch (not
pushed), and for Opus 5.5 (`model: "opus"`) on simpler sub-agent tasks.

## State of the work

- Wave 1 (12 agents, launched ~17:20): gt-bus, gt-table-pub, gt-flock-ring, gt-opening-compile,
  lib-arklib, lib-others, code-spine, code-layer1, code-pubinput, boundary-adaptor, docs-debt,
  literature. Dossiers land in `dossiers/<name>.md`.
- Report skeleton in `tex/` (LuaLaTeX; `latexmk -lualatex main.tex` or
  `lualatex -output-directory=build main.tex`). Written: `preamble.tex`, `main.tex`,
  `sections/01-scope-method.tex`, `sections/fig-chain.tex`. Others are stubs.
  Do not redirect stdout to `build/<jobname>.out` (hyperref reads that file).
- First commit to the branch: after wave 1 finishes (`git add -f .claude/reports/blueprint-review`).

## Plan after wave 1

1. Read each dossier, record findings below, spot-check the evidence against the sources.
2. Wave 2: (a) independent re-derivation of every major/critical finding (Fable);
   (b) proof-obligation hierarchy (Fable); (c) drift prevention, check-by-check table 6a/6b/6c
   (Fable); (d) catalogue assembly and citation re-checks (Opus); (e) tracker body drafts with
   the technical changes folded in (Opus, from docs-debt + findings).
3. Write the chapters, compile, adversarial read of the report (Fable), fix, commit.

## Dossiers received

### gt-table-pub (received 18:0x; 986 lines; quality high)

Ground truth facts (cited in the dossier):
- Table sumcheck transcript: ξ; τ_max rounds (max over the SIX OPCODE TABLES), each 3 elements
  (coefficients c0, c2, c3; c1 derived from the running claim; NO round check exists in Rust or
  Python: it holds by construction); final message 104 values (15+15+8+15+14+37, incl. the 18
  BLAKE2S limbs); final check; target derived never sent. B = 2 constraints in all (JUMP's two).
- Pool order: ring-switched claim (first power of λ), 5 bus boundary claims, 104 table claims
  (18 strided on q_flock), 3 public-input claims. 112 point claims + 1.
- Public input: spec per-limb; Rust (`cpu/mod.rs:752-755`), Python (`verifier.py:1400`) AND the
  recursion guest (`crates/rec_aggregation/guests/aggregate.py:1683`) check the combined
  equation `c0 + y·c1 = interp(w0, w1, r)`. Pooled values are the scalars SENT, third is 0.
  Rust `read_public` rejects a public word with nonzero top limb (`cpu/mod.rs:141-143`).
  leanISA's `PublicInput` is four lanes of K (`LeanerVM/Semantics/Memory.lean:101-110`), so a
  nonzero top limb is not expressible in Lean.
- ζ = (low, high, x_0, …) from the LAST GKR layer only (`gkr.rs:414-426`); α, β are not
  coordinates of ζ.

Findings (names as in the dossier):
- MAJOR "The bus seam admits statements the deployed table sumcheck cannot serve": `Seam.bus`
  takes any list of linear claims (unbounded number ⇒ error on ξ unbounded over the seam), terms
  of one table at unrelated points, terms on any table, and a degree clause on the statement
  alone (forces a degree check leanVM has not). Probes `probes/gt-table-pub/SeamBus*.lean`
  (exit 0). Proposal: `BusOut` in the shape of the Rust's `BusVerify` (`leaf.rs:849-860`):
  one point, forms per side and table with the degree in the type, three totals, column claims.
- MAJOR "The table sumcheck's tables are not distinguished from the instance's other tables":
  Layer 3 makes the six shared columns tables of the instance; then τ_max and Σ width range over
  them (≥16 rounds, 110 values) unlike leanVM (τ_max ≥ 3, 104). Reading of the text
  (leanIsaInstance not built).
- MAJOR "The public-input phase proves a check no executable verifier runs; the debt is assigned
  to Layer 12, which cannot pay it": needs a phase with the combined check pooling the values
  sent, with its own Phase.Security.
- minor: round message (4 coefficients + check in the oracle protocol vs 3 and none on the wire;
  the transport lemma is not stated; FS absorbs 3).
- minor: zerocheck escape over-charged and stated three ways; it is τ_max/|E| once, carried by
  the last GKR layer's challenges; with a conjunctive state function it adds nothing.
- minor: Layer 7 sketch predates the spine; `tableSumcheck_relOut_implies_constraints` is a
  placeholder. Layer 9 sketch makes the 18 limb claims an input of Flock (Flock takes no claim).
- minor: status finding on the Python verifier omitting caps is WRONG at the pin
  (`verifier.py:857-864` has them); status "four nodes" wording wrong (coefficients).
- note: spec batching error loose by one; spec has no rbr statement for these phases (its only
  round-by-round theorem is Theorem B.2, Annex B, for the opening).
- note: a phase that reads the whole oracle fills the slot (faithfulness is not in the types).

My own first-hand checks so far: Rust `verify` flow `cpu/mod.rs:711-779` read in full (seed,
read_public with caps and top-limb rejection, commitment, bus, ξ, table sumcheck, r_pi + two
scalars + combined check, finish_claims, flock verify_reduction, ring_switch_verify, pcs::verify,
`vs.finish()` = stream fully consumed). `log_inv_rate` IS announced with the sizes.
ArkLib `RoundByRound.lean` read: `KnowledgeStateFunction` deliberately differs from the
literature (docstring cites "ABF26 Definition A.5"); ArkLib itself has a `noncomputable`
extractor by `Classical.choose` (`toRoundByRoundOfRel`), so the notion does not force
computable extractors.

## Interruption (18:05) and restart (20:30)

A usage limit stopped 11 agents ~45 min in. gt-bus and gt-flock-ring had written complete
dossiers (only the hand-back was lost). docs-debt had `probes/docs-debt/dossier-part1.txt`
(A–F + part of G). Restart in two batches. Batch 1 (20:35): resumed on Fable: code-pubinput
(ac9d08c8739049c91), code-spine (a19e52090b4de7aec), lib-arklib (a44f401af73980c7d); fresh on
Opus: docs-debt finish (a5f883689be86186c), literature (a7d298d313359c144).
Batch 2 (pending): resume gt-opening-compile (af3af1b8d3b04f65b), boundary-adaptor
(ac9a0283cf6e56419) on Fable; fresh on Opus: lib-others, code-layer1 (reuse probes on disk).
User constraint (20:30): machine memory-limited (WSL/16 GiB) — NO local builds; expensive builds
go to GitHub CI (needs a push, so ask). Probes few, small, under the lock.

### gt-bus (complete; 1489 lines; quality very high; Python probe drives the pinned verifier's GKR)

Ground truth: setup = seed (iv = BLAKE2s("leanvm"‖len‖R1CS_DIGEST‖bytecode_hash), compress with
public input), 8 announced elements (κ_mem, τ_0..τ_5, ρ=log_inv_rate), checks: upper limbs zero,
public words' third limb zero, caps (program power of two ≤ 2^32; 16 ≤ κ_mem ≤ 32; τ_j ≤ 32;
τ_BLAKE2S ≥ 3; 1 ≤ ρ ≤ 4), stacking window 15 ≤ μ_stack ≤ 28; commitment root = 2 elements with
zero third limbs. Bus: α (4) and β, 5 squeezes; roots message (R, R_c) bus root FIRST; combiner
λ; GKR radix 4 (binary first layer when μ odd); layer sumcheck is NORMALIZED: message = cofactor
of degree 4, 4 elements on the wire, c_0 derived through the eq factor, no round check, final
layer check has NO eq factor; 12 children per radix-4 layer; two combination challenges; a new
combiner after EVERY layer incl. the last (drawn, never used); ζ = (u_0, u_1, χ_0..χ_{μ−3}) all
from the last layer. R_c ≠ 0 checked after the GKR. 5 boundary evaluations (mem_0, mem_1, mem_2,
cntfin_mem at ζ_{<κ_mem}; cntfin_bc at ζ_{<κ_bc}). rem_s derived. 17 checks enumerated (B1–B17)
with attacks. Boundary blocks never depend on the public input; they depend on the program
(final pc g^(2^κ_bc − 1), bytecode columns) and the sizes.
Verdicts: the real bus phase CAN fill the spine's slot (output expressible as BusOut: B+3 linear
claims, 5 column claims; perfect completeness holds; a kSF exists with errors 4·2^μ/|E| on (α,β),
2/|E| per combiner, 4/|E| per round, 1/|E| per combination challenge; zerocheck escape = max not
sum). No theorem/definition of the spine wrong or vacuous concerning the bus.

Findings:
- MAJOR G1 GKR layer sumcheck: blueprint says degree 5 and 5/|E| per round; deployed is the
  normalized cofactor of degree 4 (4 wire elements), error 4/|E|; Layer 4/5 define one variant
  only, leanVM has two (table sumcheck is the plain one).
- MAJOR G2 one combiner more than layers (the last drawn, unused; matters after Fiat–Shamir).
- MAJOR G3 the generic GKR of Layer 5 (oracles = leaf tables) cannot be appended in a phase whose
  one oracle is the stack (needs ArkLib's liftContext, admitted at the pin, which the blueprint's
  ledger says is "not consumed"); and its state function cannot carry the zerocheck clause,
  which changes on the GKR's own challenges. Proposal: GKR over a context with `leaves` and
  `riders`.
- MAJOR G4 admissibility: `admissible_iff_caps` cannot hold with `verify_iff_compiled` and
  `piopError_le`: Rust also rejects μ_stack ∉ [15,28] and ρ ∉ [1,4]; leanISA's `Caps` has
  neither (Statement.lean:79-81); `Sizes.ofWitness` cannot produce logInvRate.
- MAJOR (of the status) G5 = the Python-caps finding is false at the pin. Do NOT report upstream.
- minor G6 zerocheck charge stated four ways; G7 leaf-stack order nowhere stated (boundary
  blocks first), spine's `tuples` lists flush tuples first (immaterial to Perm, a trap for the
  layout); G8 orders left open (roots, boundary evaluations, linear claims, ζ); G9 canonical
  encoding checks and stream-consumption check absent from the blueprint; G10 two side
  conditions (1 ≤ d with a count column; constrained tables must be on the bus); G11 Layer 6
  sketch stale and its named invariant is not one; G12 binary layer's combination challenge has
  no error; G13 status S11 misreads the spec; G14 citation drift (leaf.rs:664-668; Lemma 5.1 vs
  5.2).
- notes G15 seven spec-vs-implementation disagreements (incl. Rust's fingerprint bound 5·2^μ
  `leaf.rs:110` vs spec 4·2^μ); G16 table phase must know its tables; G17 spec has no rbr
  analysis of the bus.
NOTE the tension between gt-table-pub (says the deployed table verifier cannot fill the slot
against Seam.bus as built, because the seam is too general) and gt-bus (says the bus phase can
fill its slot and that "a table phase written over the terms' own points meets it"). Both are
right: the bus side is fine; the table side needs either a generalized verifier with guards or
a narrower seam. To be settled in wave 2 (design decision for the report).

### gt-flock-ring (complete; 1171 lines; quality very high; ArkLib origin/main read at 7653a901, 347 commits past the pin)

Ground truth: Flock commits nothing; all messages in the clear; verifier queries nothing in the
phase; ONE equality check (the lincheck terminal identity, `lincheck.rs:1233-1256`); everything
else is derived. Schedule: k_batch+1 challenges (7 coordinates are FIXED constants); 64 values;
z_skip; n_flock = 8+k_batch rounds of 2 values + challenge; v_a, v_b; α_lc; 8 rounds of 2 values
+ challenge; 64 values s_i; 6 ring-switching challenges; no message/check in ring switching.
Stream: 162 + 2·k_batch scalars. The 18 limb claims are NEVER an input of Flock; they stay in
the pool and are opened as strided evaluation claims on q_flock. Ring switching serves the bit
witness only (F_2 → K); K-columns at E-points need none ("commitment over K, opening over E",
`03:117`). flockError_le numbers check out: (4·k_batch+163)/|E| (Annex C.7) + 2^32/|E| (ring
switching degree). Fixed-coordinate weights independent over F_2 (probe: rank 128).

Findings:
- MAJOR Layer 9's `FlockInterface` (StmtIn := the 18 limb claims, StmtOut := one weighted claim)
  drops the limb claims: with leanVM's verifier it has knowledge error 1. The SPINE's Flock slot
  (PubOut → FlockOut keeping the columns and adding the weighted claim) is right.
- MAJOR the slot map `limbColumns` sits inside the Flock interface, which takes the instance as
  parameter, while the instance's layout needs it: circular. Move 18 numbers to Parameters.
- MAJOR the Flock phase cannot be written over an abstract instance: `aux : Column μ → Prop` is
  opaque. Proposal: `FlockRegion I` (col, kBatch, height, aux_iff) supplied by Layer 3.
- MAJOR acceptance test 20 is a category mistake: completeness failure filed under a soundness
  error; and no verifier takes an inverse. The inverse (1 + r_eq)⁻¹ is taken by the RUST PROVER
  (`zerocheck.rs:116-123`), which at r_eq = 1 silently emits a proof the verifier rejects. The
  spec's protocol is perfectly complete. So the Lean honest prover must be the mathematical one;
  a prover transcribed from the Rust would make Phases.Complete (hence Phases.Security, which
  extends it) uninhabited. Issue #3 plans "exceptional-challenge completeness conditions": wrong.
- minor: `Security extends Complete` couples knowledge soundness to perfect completeness
  (proposal: `Component.Guarded` base); `aux` must include the constant-one position 512 (the
  zero block satisfies the R1CS); Flock's circuit/constants exist only in Rust/Python (Category
  B, not A); acceptance test 23's Flock error omits ring switching's 2^-160; ledger row on ring
  switching misdescribes ArkLib's Packing (a different protocol: Diamond–Posen); hole K3's
  fixture waits on a Flock Def nobody has started (split the Flock hole into Def + Security).
- notes: Rust Flock prover not perfectly complete (report to leanVM); error for a fixed
  polynomial ≠ error after compilation (list size factor, `whir_config.rs:540-541`);
  R1CS_DIGEST cannot be recomputed at the pin; `Weight.onCube` is 2^μ values of E in a statement.
- PROBE `probes/gt-flock-ring/NoCheckFlock.lean`: on the toy (aux := True) a Flock phase with no
  message, no challenge, no check has `Phase.Security`, standard axioms only. I.e. the master
  theorems constrain the Flock verifier exactly as much as the instance's `aux` does.

## PAUSED by the user (about 21:00, 2026-09-29)

The user asked for every sub-agent to be paused until they say to restart. All ten running
agents were stopped with TaskStop; their transcripts are kept, so each is resumed with
SendMessage to its id (a resume continues from the transcript). Nothing else is running.

To restart, send each a short "resume" message (remind: branch `docs/protocol-blueprint-review`,
no build, Lean only under the lock, write the dossier incrementally). Launch in small batches.

| Task | Agent id | Model | State when paused |
| --- | --- | --- | --- |
| code-pubinput | ac9d08c8739049c91 | Fable | resumed once; mutation probes on disk; dossier: see `ls dossiers/` |
| code-spine | a19e52090b4de7aec | Fable | resumed once; probes on disk |
| lib-arklib | a44f401af73980c7d | Fable | resumed once; probes on disk; was about to save a first dossier |
| docs-debt (finish) | a5f883689be86186c | Opus | started from `probes/docs-debt/dossier-part1.txt` |
| literature | a7d298d313359c144 | Opus | just started |
| lib-others | a7d2272ba8e6c4295 | Opus | just started (reusing probes on disk) |
| code-layer1 | ae216ea12b9b64dec | Opus | just started (reusing probes on disk) |
| verify-gt-bus | a8677e8e10ba5195e | Opus | just started |
| verify-gt-table-pub | a7eed15962ee36d90 | Opus | just started |
| verify-gt-flock-ring | a0e2028fc2a0a9921 | Opus | just started |
| gt-opening-compile | af3af1b8d3b04f65b | Fable | NOT resumed since the usage limit; probes on disk, no dossier |
| boundary-adaptor | ac9a0283cf6e56419 | Fable | NOT resumed since the usage limit; probes on disk, no dossier |

Complete dossiers: gt-table-pub, gt-bus, gt-flock-ring.

First-hand checks by the orchestrator (20:55), all confirming the dossiers:
- `gkr.rs:358-430`: roots read as `[shared, shared, root]` (bus root first, then count root);
  `lambda = vs.sample()` before the loop AND at the end of every iteration (so one more combiner
  than layers, the last unused); radix-4 rounds call `next_round_poly(5, claim,
  Some(equality_point))` (5 coefficients, c_0 derived through the eq factor, 4 on the wire);
  layer check `claim != poly_eval(&products, lambda)` has no eq factor;
  `point = [low, high] ++ round_point`.
- `fiat_shamir/src/transcript.rs:289-309`: `fixed = usize::from(eq.is_none())`; with `eq = None`
  the coefficient c_1 is derived as `claim + sum_from(2)`; with `Some(r)` c_0 is derived as
  `claim + r * sum_from(1)`. Only the transmitted coefficients are bound into the chain. No
  round check can fail; no division.
- `flock/src/zerocheck.rs:116-123` (prover `send_round`):
  `let g0 = (claim + r_eq * g1) * (F192::ONE + r_eq).inv();` — the inverse is the PROVER's.

## 2026-09-30 morning: the ground moved, nine dossiers landed, build authorised

- The user merged `main` = `144c5aa` (Lean 4.34.1, pins: ArkLib 7653a901, CompPoly 572f9973,
  Clean 42fe4b26, VCVio a4232d08, Mathlib v4.34.1; leanVM unchanged a386121f) into the review
  branch (`8d3ea7d`). Lean probes impossible until rebuilt ("incompatible header"). BRIEF §8
  written. The user chose "Build once, now": build started ~09:40 in the background
  (`logs/lake-build-144c5aa.log`, `lake exe cache get` then `lake build -j 4`). The lock file
  was removed (recreated by flock on first use).
- The review's object stays `b435631` + a delta assessment for `144c5aa`. Per the docs-debt and
  verify agents: at `144c5aa` the blueprint gained a 4-line paragraph after line 51 and a
  rewritten *Module system* row, so blueprint line numbers cited at `b435631` are 4 higher at
  HEAD; the status did not change (two landings stale).
- At the new CompPoly pin `(2 : K) = 0`; encoded words are `K.ofBits n`; probes with numerals
  ≥ 2 in K need rewriting before a re-run (code-spine flags three; ValuesProbe/StridedProbe).

### Completed dossiers (all under dossiers/)
| dossier | lines | verdict of the citation check |
| lib-arklib | 2633 | — |
| code-pubinput | 1557 | — |
| code-spine | 3388 | — |
| docs-debt | (finished; 3 major, 13 minor, 4 notes; section G has 29 insertion markers) | — |
| lib-others | 2482 | — |
| code-layer1 | (finished) | — |
| verify-gt-table-pub | 301 citations: 294 OK, 2 wrong line, 4 wrong THEOREM NUMBERS (Cor 3.7→3.9, Fact 3.8→3.10, Thm B.2→B.7 = `thm:rbr`), 1 unchecked | dossier substantively right |
| verify-gt-bus | ~400 refs: 300 OK, 3 wrong line, 9 not supported (Lemma 6.2→6.3; `14fbca8f` wrong commit but G5 stands; `appendGuarded` is leanerVM's port not ArkLib's; two arithmetic slips in D.2/D.3; three overstatements) | no finding weakened |
| verify-gt-flock-ring | 381: 375 OK, 1 wrong line, 3 misquoted (abbreviations), 2 not supported; "no verifier takes an inverse" → "no inverse of a challenge-dependent value" | no finding weakened |
Still running: literature. Not resumed yet: gt-opening-compile, boundary-adaptor.

### Headline results to carry into the report
1. (code-pubinput, major) The check on c_0, c_1 is NOT load-bearing in the phase as built
   (`securityG`: any message, any check passing on the honest message → Phase.Security at
   1/|E|); the fix is to pool the values SENT (`pooledFrom`); then mutations 2, 3b are refuted
   and a wrong check breaks completeness. The deployed (combined) check's key lemma is PROVED
   (`ProbeWordsLemma.lean`, `accepts_two_challenges`). Recommend: build the deployed phase in
   Layer 8 with its own Security; keep the spec's as reference; report §8.2 ambiguity upstream.
   The earlier review's claim (five wrong verifiers each break a theorem) is false of merged code.
2. (code-spine, major) `piop_rbrKnowledgeSoundness` has content only with a bound on
   `piopError`; junk phases at error 1 inhabit `Phases.Security I` for every I. Recommend:
   `piopError I` closed form fixed by the spine from the instance's sizes, each phase's `rbr`
   demanded at it; `piopError_le` becomes a spine theorem.
3. (code-spine) the composed extractor's `extractOut` is the stack only for zero-round phases;
   with a real phase the repository's rfl test statement is ILL-TYPED; no definition "the
   extracted stack" exists; headline overstates. Pass-through bus phase has NO Security (P5
   `no_security`). `outputPure` derivable (P6). Probabilistic knowledge transport along a
   refinement is 3 lines (P6 `knowledge_transport`), contradicting the blueprint's "not proved".
   Surface: completeness 70 decls/217 lines; KS named form 100/354 (612 with docstrings).
4. (lib-arklib) plain reading machine-checked at transcript level (`accept_imp_extract_or_bad`);
   existential rbr KS = soundness (classical extractor at error 0 for any relation); the
   named form adequate only with the extractor read; FS/BCS security stated nowhere in ArkLib
   (`Commitment.extractability` body is `False`!); new pin lifts NO relevant admission;
   `OracleReduction` marked "legacy"; typed Interaction framework has no knowledge notion;
   local #615 port still needed; `Component.Def` bundling the real error makes every phase
   with a challenge noncomputable.
5. (lib-others) fields match leanVM bit for bit (11 Rust reference products reproduced);
   samplers uniform by VCVio's class law; Clean's balance over K is UNSATISFIABLE (side
   condition length < 2), not merely unsound; NumeralHazard settled (kernel rejects); new pin:
   `Fintype K` proof-only (eager-Fintype blocker lifted); ArkLib `ToCompPoly/Multilinear/Basic`
   probably clashes with CompPoly at the new pins (`eval_zero` declared twice) — unverified.
6. (code-layer1) Layer 1 matches leanVM where it transcribes (92 offsets reproduced; 16-instr
   program bytecode column 256 cells); MAJOR: nothing reads the 18 limb columns (strided
   reader missing; `Layout.comap` cannot place them; `leanIsaInstance_fits` refers to a
   `layout.total` that does not exist); equal-size block order pinned by nothing before the
   compiled verifier; `Layout.comap` allows aliasing; 143 public decls (20 LB, 41 iface, 82
   helper), auditor reads none today; BlockClaims.lean has no consumer; acceptance tests 7, 14,
   15 wrong; `Protocol/Basic.lean` imports Arithmetization.Basic (wall exception missing).
7. (docs-debt) ≥128 codes, ≥1036 uses, 34 with ≥2 meanings (`C1` five); hole comment: 8 of 13
   sections predate the spine, public-input section says "the prover sends nothing"; T4 sketch
   omits `WellFormedBytecode` (major); status two landings stale; blueprint states old pins in
   five passages.

### literature (complete; ~60 BibTeX entries; sources under probes/literature/src/)
Majors: (1) the non-interactive error as sketched lacks the hash-collision term (~3.5·t²/2^256),
the list-size factor L_0 (list-binding commitment; Flock Remark 11), and any model of grinding;
no published theorem covers FS with proof of work for multi-round IOPs; `FiatShamirSecurity` as
Q·max ε certifies ~111 bits where leanVM claims 128 (query rounds at ~2^-111 before 17 bits of
grinding). (2) ArkLib's transforms (one RO on the transcript prefix / duplex sponge) and the
textbook BCS (separate RO per role) are other constructions than leanVM's one BLAKE2s map for
chain + Merkle nodes (untagged) + grinding: a chain lemma and a role-separation lemma are owed;
"the upstream theorem as witness obligation" cannot discharge the interfaces. (3) proof of work
is the one verifier check no planned theorem or mutation makes load-bearing (also canonical
encodings, Merkle path lengths); propose mutations + reverse tests (spec-rejected transcripts
through Rust/Python). (4, part of 1) list-size factor.
Right: WHIR regime = Johnson with slack citing BCHKS25 Thm 4.6, the provable one (capacity
conjectures refuted: Crites–Stewart 2025, Krachun–Kazanin–Haböck 2026; at the Johnson radius
the bound fails in char 2, BCHKS25 Cor 1.7); Annex B states Thm 4.6 as printed (checked);
caveat: single-version preprint with a sketched proof. KRS25/Fen26 attacks do not reach leanVM
(statement in the seed, trace committed before any challenge, GKR only for grand products); RO
theorems classical (quantum: ~64 bits). The cut (relation on the committed column + adaptor)
is sound practice: every comparable effort stops at a trace relation; SP1's plan asks for the
same exact natural-number balance. ABF26 = Arnon–Boneh–Fenzi ePrint 2026/680 (Def A.5 bounds
extractor time; ArkLib's does not). arXiv 2607.23752 = Kolozyan–Sorger–Hicks–Chaliasos 2026;
T1–T8 refine its six obligations; none covers the deployed verifier's correctness;
architecture.md uses its labels without citing it. Minor: references misattributed (FS paper
authors, Ligerito authors, BCHKS25 title, origin of rbr KNOWLEDGE soundness = CMS19), wrong
Thaler chapter, "computable" ≠ "efficient", RO scope unstated; Rust comment `whir.rs:1210`
stale (level 0 has grinding).

### Build under 4.34.1
`lake build -j`/`--jobs` are not Lake 5 options; packages were already built today (ArkLib
oleans 09:40); `lake env lean` rebuilt the spine cone on demand (probe test exit 0 at 09:50).
Full `lake build LeanerVM LeanerVMTests` started 09:55 in the background
(`logs/lake-build-144c5aa-full.log`). Agents may probe only after it reports exit=0.

### Wave 2 launched 09:52 (Opus): `register` (abab0f7d52443576b) → dossiers/register.md;
`tex-groundtruth` (a187d67d6fb7e3def) → tex/sections/gen/. Resumed (Fable): gt-opening-compile,
boundary-adaptor (reading only until the build is done).

### Wave 2 additions (10:05, Opus): tex-libraries (a766c02d3e91bdda5) → gen/lib-*.tex,
layer0-audit.tex, findings-libraries.tex; tex-catalogue (ad48f4250a49950b2) → gen/catalogue-*.tex,
surface.tex, statements-spine.tex, probes-code.tex, conformance.tex, findings-code.tex;
tex-docs (afad83d0aacd46a63) → gen/docs-*.tex, code-index.tex, findings-docs.tex.
Chapters written by the orchestrator so far: 01 (scope), 02 (map + fig), 05 (phases; the
opening section awaits gt-opening-compile), e (brief review), fig-chain. Report compiles
(`lualatex -output-directory=build main.tex` from tex/).
Pending, in order once inputs land: (a) read register.md; (b) after the build: notify the two
reading agents that Lean runs again under the lock; launch an Opus "probes-rerun" agent for the
probes marked written-not-run / numerals ≥ 2 (code-pubinput 4b, 6, 7a, 8; code-spine's three;
code-layer1 ValuesProbe/StridedProbe with K.ofBits); (c) Fable: proof-obligation hierarchy
(chapter 06) and adversarial re-derivation of the major design findings; (d) orchestrator:
chapters 00, 07 (TCB), 08 (faithfulness: intro + per-phase inputs of gen/), 09 (non-vacuity),
10 (auditability), 11 (options), 12 (documentation), 13 (drift), appendices a–d.

### 10:35 boundary-adaptor landed (~2050 lines, 18 findings); leanVM checkout MOVED
- The leanVM checkout is at `248da071` (crate tree renamed); pin `a386121f` is an ancestor;
  all reading must go through `git show a386121f:<path>`. BRIEF §8 updated. gt-opening-compile
  told. The user has not been asked to restore it (their checkout; they may have moved it for
  the Rust contract tests of #61, "implementation revision 48a90420").
- boundary-adaptor majors: (1) `witnessOf` mixes parts built from `prog` with parts read from
  q; balance carries over ONLY because the boundary blocks are `Coord.known` from the same
  `prog` (decision 8); "Ensemble.toM3 of the eight tables" describes the wrong construction;
  Layer 2 has no bridge lemma for boundary blocks. (2) Both T4 statements unprovable as
  written: `baseVerifier_extractsExecution` omits `WellFormedBytecode` (JUMP-sentinel
  counterexample proved in tests), attaches a probability to a closed Boolean, is a soundness
  statement for the language {∃ t, ValidExecution}; `baseProver_complete` is FALSE: a valid
  execution at κ_mem = 32 needs 2^34 cells, verifier rejects μ > 28; "witness of t" needs T2 or
  classical choice. (3) top limb anchored: without the third line `satisfiedBy_witnessOf`
  unprovable for every `witnessOf` (a `SET_CONSTANT [g^0, y²]` program); ultimate anchor the
  literal 0 in `PublicInput.word0/word1` (`Memory.lean:107-110`). (4) unstatable: `Sizes.
  logInvRate`, `admissible_iff_caps`, `leanIsaInstance` needing `FlockInterface I` (proposed
  instance-free `FlockSpec`), Layer 2's Mathlib polynomials not computably convertible
  (`toCMvPolynomial` noncomputable at both pins; probe PolyBridge gives a direct translation),
  `witnessOf_stackOf … = w` not a Lean statement, `leanIsaInstance` must be an `abbrev` (probe
  DefInstance). (5) `∃ s` sound but the probabilistic composition over prover-announced sizes is
  unspecified (union bound ≈ 2^34 vs Q·max ε needing a family-level FS interface); architecture.md's
  T4 map diverges on T2, resource conditions, hash assumption.

### Disagreement settled by the orchestrator (10:55): the GKR round error
gt-bus: the deployed radix-4 layer round is the NORMALIZED cofactor of degree 4 (read first-hand:
`gkr.rs:399-401` `next_round_poly(5, claim, Some(equality_point))`, five coefficients, c_0
derived through the eq factor; the layer check has no eq factor). If the running claim is
wrong the prover's cofactor differs from the true one, both of degree 4, so the next claim is
right at ≤ 4 challenges: error 4/|E|. gt-table-pub's D.3 used 5/|E| (the blueprint's number)
when arguing that the zerocheck conjunct adds nothing (max, not sum): its argument stands with
4/|E| too. The report states 4/|E| for the deployed protocol and calls the blueprint's 5/|E| a
loose upper bound that also describes a different (non-normalized) protocol.
tex-groundtruth done: 12 fragments + index-gen.tex; the leanVM checkout move confirmed by it.
### 11:00: tex-boundary (aa51a65bb3206779a, Opus) → gen/boundary-*.tex, findings-boundary.tex,
probes-boundary.tex; obligations (ab02c85f4f6a7f994, Fable) → dossiers/obligations.md.
Report at 97 pages (9f5e1f1). Chapters 03, 04, 12 and appendices b, c, d wired to fragments.
### 11:10: verify-majors (a74db140b844df3a5, Fable) → dossiers/verify-majors.md: attacks 11 major findings.
Running now: register, tex-libraries, tex-catalogue, tex-docs, probes-rerun, gt-opening-compile, tex-boundary, obligations, verify-majors.

### 11:25 gt-opening-compile landed (1921 lines)
MAJOR: (1) NO sumcheck between λ and WHIR: after λ the next message is WHIR's own first round
polynomial (`stack_open.rs:452-461` → `whir.rs:1324-1326`; `py:1362, 1012`); the blueprint's
Layer 10 + Layer 11 describe 2μ sumcheck rounds, an extra scalar and a second batching
challenge: `verify_iff_compiled` cannot hold for any Rust proof. Recommend (ii): inner-product
oracle interface (`Query := Weight μ`, answer `W.pair q`; Definition 3.13); the opening phase =
"λ, then one weighted query", error (J−1)/|E|; WHIR replaces the whole opening phase; probe
shows it typechecks at both pins; nothing built breaks. (2) Non-interactive theorems ill-formed
(no probability space; soundness not knowledge; no adversary/query budget); well-formed shape
given (RO H for the compression; Q-query adversary; straight-line extractor: leaves off the log,
list decoding, selection; adversary-chosen sizes; program bound by its hash; ROM heuristic
named). `verify_iff_compiled` as sketched applies `Verifier.fiatShamir` to an oracle verifier
with the stack and codewords as messages in the clear, omits Merkle compilation (ArkLib has
none), grinding, sizes; statable form given. `FiatShamirSecurity` ("rbr ⇒ FS KS, Q·max ε") is
FALSE as a universal (hash term, oracle messages, grinding); nothing at either pin or in
#848/#469 inhabits it; `BcsSecurity` empty; #627 is an issue not a PR. Missing: rbr ⇒
state-restoration (commented out upstream, wrong error), hash-chain instantiation, grinding,
list-binding compilation (stated in E.3 with extractor/state function/errors L_0·ε_i on the
front's challenges; needs "list members are K-valued" lemma, proved in 2 lines). Perfect
completeness does NOT survive compilation: the honest grind is an unbounded search
(`fs/lib.rs:126-155`) → `prove` must be partial/fuelled. (3) Numbers: under the stacking window
(μ_bus ≤ 28) Σ phase errors ≈ 2^-159.7 (ring switching 2^32/|E| dominates), so `piopError_le`
holds; without the window μ_bus = 38 and it is false. Deployed set: 128 bits rbr in the Johnson
regime given BCHKS25 4.6; query rounds 111 bits + 17 grinding per level; fold (MCA) terms
128.2–146 bits; L_0 ≤ 396 (μ=15)…110 (μ=28), up to 2^20 at deep levels; port of
whir_config.rs's search reproduces the Python query table for all 56 (ρ, μ). (4) Hidden
assumption: commitment = Merkle root of a K-valued word (not a codeword) close to ≤ L_0
codewords of the E-code; every such codeword is K-valued (lemma not in spec). Ground truth
B/C/D: four schedule differences vs Protocol B.6 not in the blueprint (per-claim intro
polynomials before λ_i; 17-bit grinding per level; level-0 lane relayout with terminal point
rotated by 6; last round message omitted); RS over E with domain in K, novel basis; Merkle =
BLAKE2s-256 leaves/nodes without domain separation; chain step = BLAKE2s-256(cv‖block) with cv
IN the message (blueprint's "compress with cv as chaining value" wording invites the wrong
function); proof object's Merkle format unspecified; standalone Python accepts nonzero absent
lanes; upper per-log caps implied by the window; `encode_column_weight` near-vacuous; `encode`
K-only; Annex B numbering: Protocol B.6, Theorem B.7, Definition B.4, Lemma B.14.
Caveats: no probe of the list-compile theorem; ArkLib `Commitments/`, `FiatShamir/`,
`Data/CodingTheory/` oleans absent from the build (probes copy definitions).
### 12:10 register done (134 findings: 1 critical, 35 major, 62 minor, 36 notes; 111 negative
results; 58 unverified); probes-rerun done (all agree at the new pins; 4b and 6 never written;
7a/8 rbr fails at the state function as elsewhere; FieldFidelity products agree; LawfulBEq E
now exists; sampler diamond gone). Chapter 11 (options) written. tex-changes launched
(a55116b929f6f43f3). Running: tex-libraries, tex-boundary, obligations, verify-majors,
verify-gt-opening, tex-opening, tex-changes.
### 12:40 obligations done (155 nodes; 66 specified only, 25 not specified, 21 built+proved,
10 unprovable as written; 57 nodes wrong/missing/unprovable; two new majors: 21 obligations with
no owner; the list-binding compilation needs oracle-free front verifiers, nothing enforces it).
tex-obligations launched (ac96c4de5bccaff13); register agent asked to add the new rows.
Still running: tex-boundary, verify-majors, verify-gt-opening, tex-opening, tex-changes,
tex-register, tex-obligations, register (update). Report at 362 pages (d6be851).
Remaining for the orchestrator: wire gen/obligations; read verify-majors + verify-gt-opening
verdicts and adjust 00/05/08 wording; final adversarial read by a fresh agent; final commit
with the PDF (checkpoint.sh adds tex/report.pdf if present: copy build/main.pdf there).
