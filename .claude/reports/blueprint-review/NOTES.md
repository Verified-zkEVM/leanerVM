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
