# Verification of the major findings (task `verify-majors`)

Object: leanerVM `main` at `b435631` (Lean files read with `git show b435631:<path>`); leanVM at
`a386121f` (read with `git -C …/leanVM show a386121f:<path>`; the working tree was never read);
ArkLib at the old pin `dca90385` unless a revision is named (read with
`git -C .lake/packages/Arklib show dca90385:<path>`). Purpose: a hostile second reading of
eleven findings of the other dossiers. Each section records the finding, what was read, a
verdict (`CONFIRMED` / `WEAKENED: …` / `REFUTED: …`) and, where confirmed, the shortest
self-contained argument a reader can check.

No Lean probe was run: the checkout cannot elaborate until it is rebuilt (brief §8). Every
conclusion rests on reading the sources named, on hand computation, and, where cited, on the
probe outputs the other dossiers recorded at the old pins. Nothing under `probes/verify-majors/`
was needed.

## Summary

Eleven findings attacked; none refuted. Nine stand as written. Two are weakened in one clause
each, neither in a way that changes its severity class:

- Finding 5, the GKR layer sumcheck: the blueprint's wire format (five coefficients per round
  where the deployed verifiers read four) and its single sumcheck variant (the deployed layer
  check has no equality factor) are confirmed wrong; but its per-round error `5/|E|` is a loose
  *upper* bound for the deployed verifier, not a wrong one (the tight value is `4/|E|`), and
  the phrase "the round check is on the cofactor (Gruen)" at `:321` is correct. The exact
  round error, settled below: `4/|E|`, tight.
- Finding 10, Layer 1's strided reader: the facts are confirmed (no low-index reader in the
  code, `leanIsaInstance_fits` names a field `Layout` has not), but the blueprint does name
  the strided reader and assigns its combination with the aligned one to Layer 3
  (`:841-848`); what is missing is a sketch and a non-circular owner of the slot map, and the
  generic identity is a twenty-line derivation from Layer 1's own lemmas.

Two points the other dossiers do not make and the report may use:

- Finding 2 and finding 6 together: the *bus phase* can fill its slot and the *table phase*
  cannot serve the seam between them, and there is no tension: `Seam.bus` is a strict superset
  of the bus phase's image, and ArkLib's completeness (`Security/Basic.lean:89-99` at
  `dca90385`) is owed on every element of the input relation, so the surplus burdens the table
  phase only.
- Finding 7: the sentence "the verifiers take no inverse" in `gt-flock-ring.md` is literally
  false (they invert constants); the true statement, re-derived by an inventory of every
  `.inv()` at the pin, is that no verifier inverts a value that depends on a challenge. The
  dossier's finding 8.4 already uses the true form.

| # | Finding | Verdict |
| --- | --- | --- |
| 1 | The knowledge theorem has content only with a bound on `piopError`, and the spine states none | CONFIRMED |
| 2 | `Seam.bus` admits statements the deployed table sumcheck cannot serve; the real bus phase can fill its slot | CONFIRMED (both) |
| 3 | The public-input check is not load-bearing for any theorem | CONFIRMED |
| 4 | Three executable verifiers check one combined equation; the specification checks per limb | CONFIRMED |
| 5 | GKR: cofactor of degree 4, error `4/|E|`, one combiner after every layer including the last | WEAKENED: the blueprint's `5/|E|` is loose, not wrong; the wire and the layer check are wrong as written |
| 6 | The generic GKR cannot be appended without ArkLib's admitted lifting; its state function cannot carry the zerocheck conjunct | CONFIRMED |
| 7 | Flock: interface drops the limb claims (error one); slot map circular; phase not writable over an abstract instance; acceptance test 20 misfiles a prover defect | CONFIRMED (all four) |
| 8 | The two T4 sketches are unprovable as written; the instance is not `Ensemble.toM3` of eight tables | CONFIRMED |
| 9 | `Admissible` cannot equal `Caps`: the deployed verifier also rejects the stacking and rate windows | CONFIRMED |
| 10 | Layer 1 has no reader for the limb columns; `leanIsaInstance_fits` names a missing field | WEAKENED: facts confirmed; the blueprint names the reader and assigns it, and the lemma is cheap |
| 11 | The status file's finding that the Python verifier omits the caps is false | CONFIRMED |

---

## 1. The knowledge theorem has content only with a bound on `piopError`

**The finding** (`code-spine.md`, section D.3 (b) and the finding *the declared error is
unconstrained*; probe `probes/code-spine/P4Junk.lean`). `piopError P := P.toDef.err`; each phase
declares its own error; five phases that draw a challenge and check nothing, each declaring
error `1`, inhabit `Phases.Security toy`, and both master theorems hold of them.

**What I read.**

- `LeanerVM/Protocol/Spine/Compose.lean:149` at `b435631`: `def piopError (P : Phases I) :
  P.toDef.pSpec.ChallengeIdx → ℝ≥0 := P.toDef.err`. The two master theorems `:162-177` and the
  existential form `:179-185` are stated at `(piopError P)`; the docstring `:24-31` says the
  plain reading is ArkLib's `rbrKnowledgeSoundness_implies_knowledgeSoundness`, "admitted at
  the pinned revision" (confirmed: `Implications.lean:223-228` at `dca90385` ends in `sorry`,
  and concludes `knowledgeSoundness … (∑ i, rbrKnowledgeError i)`, again at the declared sum).
- `LeanerVM/Protocol/ToArkLib/Component.lean:66`: `err : pSpec.ChallengeIdx → ℝ≥0`, a bare
  field of `Def` with no law; `:103-106`: `rbr` is `rbrKnowledgeSoundnessWorstCaseWith … D.err`;
  `:148`: `Def.append` keeps each side's declaration (`err := Sum.elim D₁.err D₂.err ∘ …`).
- ArkLib `Security/RoundByRound.lean:553-568` at `dca90385`: the bound is
  `Pr[…] ≤ rbrKnowledgeError i`, an inequality with no constraint on the right-hand side; a
  probability is at most `1`, so `rbrKnowledgeError i = 1` is met by every verifier.
- A search of every `.lean` file under `LeanerVM/` and `tests/` at `b435631` for `piopError`
  and `.err`: the only statements about an error are `(publicInputPhase toy).err i = 1 /
  Fintype.card E := rfl` (`tests/LeanerVMTests/Protocol/PublicInput.lean:225`) and
  `(commitDef toy).err i = 0 := rfl` (`tests/…/Spine.lean:138`). No bound, no sum.
- The blueprint at `b435631`: `:318` ("the closed form is a `def` next to the theorem, and
  the interactive error is its sum"); `:1122` `def piopError (s : Sizes) : (pSpec …).ChallengeIdx
  → ℝ≥0`; `:1129-1130` `piop_rbrKnowledgeSoundness (hs : s.Admissible prog) : … (piopError s)` and
  `piopError_le (hs : s.Admissible prog) : Σ i, piopError s i ≤ 2 ^ 40 / |E| + flockError`;
  `:431-437` item 6 of *What the spine fixes*: "its error `piopError`" is the composition's.
- The probe `P4Junk.lean` (source read in full): `wasted f ε` has one challenge, a verifier
  `wVerifier` that ignores it (`verify := fun s _ ↦ pure (f s)`), and `wState` with
  `toFun := if m.val = 0 then relIn else True`; `w_rbr` closes by `simp` at error `1`;
  `junkSecurity : junkPhases.Security` and `piopError_junk : ∀ i, piopError junkPhases i = 1`.
  Recorded output at the old pins: the three standard axioms. The construction never mentions
  the toy's data.

**Attacks tried.**

1. *A statement on `main` bounding `piopError`.* None (the search above).
2. *A law on `Component.Def.err`.* None; and `Security.rbr` at `D.err` is satisfiable at `1`
   by any verifier, so the field cannot be constrained by its use.
3. *Does the blueprint's `piopError_le` close the gap as written?* No, because it is stated
   about a different object. Layer 10's `piopError (s : Sizes)` is a closed form of the sizes
   and its `piop_rbrKnowledgeSoundness` is stated *at* it (`:1129`), which would give the
   theorem content; but the spine as built states the theorem at `piopError P`, the phases'
   declarations, and no statement relates the two. The blueprint is inconsistent with itself
   on this point (`:318` and `:1122-1130` against `:431-437`), and the dossier's second design
   ("a closed form fixed by the spine") is exactly Layer 10's shape, so the fix is a
   reconciliation, not a new idea. What the blueprint's plan lacks even on its own terms is
   the bridge: each phase's `Security` must be *at* the closed form, or a lemma
   `piopError P = piopError s` must be proved for the leanVM bundle.
4. *Could `piop_rbrKnowledgeSoundness_exists` say more?* No: it is
   `rbrKnowledgeSoundnessWorstCase … (piopError P)` (`RoundByRound.lean:537-551`, the
   existential over `WitMid`, extractor and state function at the same error), one `⟨_, _, _,
   …⟩` away from the `With` form.

**Verdict: CONFIRMED.** Severity as the dossier has it (major: the headline's `piopError I`
and `piopError_le` cannot be stated over what is built). One remark for the report: this is
the expected shape of a composition theorem, and the dossier says so; the defect is that
nothing on `main` or in the blueprint's spine section turns it into a statement about leanVM,
and that the blueprint's Layer 10 already contains the right shape under a different name.

**Shortest argument.** `piop_rbrKnowledgeSoundness P S` proves `Pr[bad transition at
challenge i] ≤ piopError P i` where `piopError P i` is whatever the phase owning `i` wrote in
its `err` field (`Compose.lean:149`, `Component.lean:66, 148`). A phase may write `1`
(`P4Junk.lean`, `w_rbr`), and then the theorem is `Pr[…] ≤ 1`. No statement on `main` says
anything else about `err`.

## 2. The bus seam versus the deployed table sumcheck, and the bus phase's slot

**The findings.** (a) `gt-table-pub.md` section 6 and its first finding: `Seam.bus` admits
statements the deployed table sumcheck cannot serve, so `Phase.Complete` and `Phase.Security`
for a verifier transcribing leanVM's table sumcheck cannot be proved against it; probes
`probes/gt-table-pub/SeamBusShape.lean`, `SeamBusMember.lean`. (b) `gt-bus.md` section E: the
real bus phase's output is expressible as a `BusOut I`, and its completeness and knowledge
soundness against `Seam.commit → Seam.bus` can hold (with the caveat of its G3).

**What I read.**

- ArkLib `Security/Basic.lean:89-99, 103-105` at `dca90385`: `completeness` is `∀ stmtIn witIn,
  (stmtIn, witIn) ∈ relIn → Pr[(stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut | …] ≥ 1 −
  completenessError`; `perfectCompleteness` is the case `0`. Universal over the input relation.
- `Compose.lean:98-107, 117-126` at `b435631`: `Phases.Complete.table : Phase.Complete I
  P.table (Seam.bus I) (Seam.table I)` and `Phases.Security.table` likewise. So the table
  phase's input relation is `Seam.bus I`, whole.
- `Seams.lean:71-79, 91-95, 130-134, 175-178`: `VirtualTerm` (weight, table, `poly :
  CMvPolynomial (I.width j) K`, `point : Vector E (I.τ j)`), `LinearClaim` (a `List` of terms
  and a value), `BusOut` (`linear : List (LinearClaim I)`, `columns`), and `Seam.bus` with its
  five conjuncts, the second being `∀ c ∈ s.2.linear, ∀ t ∈ c.terms, t.poly.totalDegree ≤ I.d`.
- The two probes (sources read in full). `SeamBusMember.lean` decides each clause of
  `Seam.bus` on `twoPoints` (two terms of table 0 at the points `#v[0]` and `#v[1]`, value `0`)
  against `q0`: `#guard twoPoints.Holds q0`, `#guard ∀ t ∈ twoPoints.terms, t.poly.totalDegree
  ≤ toy.d`, `#guard toy.PublicLinesHold (0 : K) q0`; the toy's `aux` is `True`. So
  `twoPoints ∈ Seam.bus toy`. `SeamBusShape.lean`: `cubicClaim` (`X₂³` at `#v[0]`, value `0`)
  has a true sum on `q0` (`#guard cubicSum == cubicClaim.value`) and is outside the seam by the
  degree clause alone (the `example … ∉ Seam.bus toy` closed by `decide +kernel`). Both use
  only the numerals `0` and `1` in `K`, so the change of numerals at the new CompPoly pin does
  not touch them; whether they elaborate at the new pins is unverified (no Lean was run).
- The deployed table sumcheck, `crates/lean_vm/src/constraints.rs:261-291` at `a386121f`: one
  point `zeta`, `n = max τ` rounds, one `next_round_poly(4, claim, None)` per round (`:267`),
  and one equality factor per *table* per round, `eq_k = 1 + zeta[m] + rk`, folded into
  `weights[t]` (`:271-274`); the final check `acc != claim` sums `weights[t] * (air.eval)(w,
  &evals)` over the tables (`:277-289`). It takes no polynomial and no list of claims as input:
  the constraints come from `airs(&l.taus, &bus.forms, form_pows)` and the target from
  `bus.totals` (`cpu/mod.rs:735-741`).
- The Rust's `BusVerify` (`leaf.rs:849-860`): `claims`, `bytecode_claims`, `count_root`,
  `point` ("The GKR point ζ, reused as the table sumcheck's eq point"), `forms[side][table]`,
  `totals[3]`.

**Attacks tried.**

1. *Is completeness of the table phase really owed on every element of `Seam.bus`?* Yes:
   `perfectCompleteness` quantifies over `relIn` (`Basic.lean:89-92`), and the bundle names
   `Seam.bus I` as the table phase's `relIn`. ArkLib's composition of completeness needs the
   second component complete on the whole intermediate relation
   (`Composition/Sequential/OracleCompleteness.lean:63` per `code-spine.md` C.6, `h₂ : ∀ s,
   R₂.perfectCompleteness (pure s) impl rel₂ rel₃`), so the spine could not weaken it to the
   bus phase's image without changing the seam. Which is the dossier's proposal.
2. *Could a table verifier reject the shapes it cannot serve and still be perfectly complete
   on the honest bus output?* No. `twoPoints` is in the seam and is not the honest bus output;
   a verifier that rejects it is not perfectly complete on `Seam.bus`, whatever it does on the
   honest output. `Phase.Complete` has no "honest output" restriction.
3. *Is the "generalized sumcheck with guards" a real way out?* For the theorems, yes: a phase
   whose verifier guards the degree (computable: CompPoly's `totalDegree`), caps the number of
   claims (needed because the error on `ξ` is `(k − 1)/|E|` for `k` claims, and `err` may
   depend on `I` but not on the statement), computes one equality factor per term and ranges
   over every table of `I` serves every element of the seam; its schedule depends on `I` alone,
   so it is a `Phase.Def`. For faithfulness, no: it is a different verifier from
   `constraints.rs`, with four guards the deployed one has not, whose honest transcript equals
   the deployed one only under three further conditions the blueprint does not state (the bus
   phase's emission order, the rounds ranging over the opcode tables only, the guards shown
   dead). The dossier says exactly this.
4. *Does the proposed `BusOut` in the shape of `BusVerify` lose anything the table sumcheck
   needs?* No. `constraints::verify` reads the point (`bus.point`), the forms (through
   `airs`), the totals (through `target`) and the constraints (from the instance); the
   proposal carries `point`, `forms`, `totals`, `columns`, and the zerocheck claims are the
   seam's clause "every constraint's extension is zero at `point_{<τ_j}`". `BusVerify`'s
   `bytecode_claims` and `count_root` are consumed by the recursion harness
   (`VerifySummary`, `cpu/mod.rs:769-777`), not by the base table sumcheck; `count_root ≠ 0` is
   checked inside the bus phase. One caution for the proposal: the forms' coefficients are in
   `E` (`eq(sel_b, ζ_hi)·eq(α, i)`, `eq(sel_b, ζ_hi)·β`), which `Form j := List (E × RowPoly j)`
   covers.
5. *Are (a) and (b) in tension?* No. (b) says the bus phase's image lies inside `Seam.bus`
   and its proofs can be made against it; (a) says `Seam.bus` is strictly larger than that
   image. ArkLib's completeness being universal over `relIn`, the surplus is charged to the
   phase that consumes the seam, not to the one that produces it. `gt-bus.md` E.4 says so in
   one sentence; the two dossiers agree.

I also re-read `gt-bus.md` E.2's completeness argument for the bus phase against
`Seam.bus`'s degree clause: the flush coordinates have degree `≤ d` by `flushes_degree`, the
`β` term's polynomial is the constant `1`, and the count form's polynomial `X_c` has degree
`1`, which needs `1 ≤ d` (its G10). Nothing missing.

**Verdict: CONFIRMED (both).**

**Shortest argument for (a).** *Completeness.* `twoPoints ∈ Seam.bus toy` (every clause decided
by `SeamBusMember.lean`); it has two terms of one table at two different points; the deployed
verifier has one point `ζ` and one equality factor per table (`constraints.rs:271-274`), so it
cannot evaluate the summand `eq(0, x)·C(row x) + eq(1, x)·C(row x)` and either rejects or
checks a different sum; `Phase.Complete` demands acceptance with probability one on every
element of `Seam.bus` (`Basic.lean:89-99`, `Compose.lean:101`). *Knowledge soundness.*
`cubicClaim ∉ Seam.bus toy` by the degree clause alone, with a true sum on `q0`
(`SeamBusShape.lean`); a verifier that does not inspect degrees accepts the honest run with
probability one and outputs true column claims; the state function is false at the start
(`toFun_empty` is an `iff` with `relIn`), true at the end (`toFun_full`), and prover messages
cannot flip it (`toFun_next`), so some challenge flips it, and summing over challenges,
`Σ_i err i ≥ 1`.

## 3. The public-input check is not load-bearing for any theorem

**The finding** (`code-pubinput.md`, section C, probe `ProbeAnyCheck`, theorem `securityG`;
finding G.1). The verifier's pool `pooled` reads the statement and the challenge, never the
prover's message; so for every message function and every check the message passes there is a
`Phase.Security` against the same seams at the same error, the check being any check at all.

**What I read.**

- `LeanerVM/Protocol/PublicInput.lean` at `b435631`: `pooled (s : I.Stmt × TableOut I) (r : E)
  := (s.1, ⟨s.2.columns ++ (I.publicLines s.1).map (lineClaim I r)⟩)` (`:127-128`), with
  `lineClaim I r l := ⟨l.col, linePoint l.pos r, lineValue I r l⟩` (`:123-124`) and `lineValue
  I r l := (1 + r) * ofK l.cell0 + r * ofK l.cell1` (`:119-120`): the pooled value is computed
  from the statement's cells. `check I s r cs := decide (cs = expectedValues I s.1 r)`
  (`:136-137`). The verifier (`:229-234`): `let cs ← liftM queryValues; if check I s (chals
  ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure`; the prover's output
  (`:220`) is `pooled I st.2.1.1 st.1` too. `stateFunction` (`:327-348`) names `check` only in
  its round-2 clause; `rbr` (`:350-366`) closes with `bad_challenge_unique I s o h₁.1 h₁.2
  h₂.2`, a fact about `pooled`, and never mentions `check`.
- The probe's `securityG` (source quoted in the dossier, C.4; recorded output at the old pins,
  exit 0, the three standard axioms): typed `Phase.Security I (phaseG I msg chk) (Seam.table
  I) (Seam.pub I)` with `rbrG` at `(fun _ ↦ error)`, `error = 1 / Fintype.card E` (`:111`).
  The same seams and the same error as `publicInputSecurity` (`:391-397`). Instances:
  `noCheckNoMessage`, `noCheckJunk`, `swappedCheck`, `specification`.
- ArkLib's `completeness` requires `prvStmtOut = stmtOut` (`Security/Basic.lean:85, 99` at
  `dca90385`).

**Attacks tried.**

1. *Is `securityG` about the same seams and the same error?* Yes (its signature; the seams are
   the spine's `Seam.table I` and `Seam.pub I`, the error the module's `error`).
2. *Does ArkLib's completeness rescue the check?* No. The equality `prvStmtOut = stmtOut` is
   between two values of `pooled …`, computed on both sides from the statement and the
   challenge; the message does not enter either. In `proverG` the output is `pooled I
   st.2.1.1 st.1` whatever `msg` is; in `verifierG` the output is `pooled I s (chals ⟨0, rfl⟩)`
   whatever `chk` is. So `completeG` holds whenever `chk` accepts `msg` (`hchk`), and the
   check constrains only the pair (prover, check), not the pool.
3. *Is there a theorem of the phase or of the spine that the unchecked verifier fails?* None:
   `Phase.Complete` and `Phase.Security` are the phase's only theorems, the master theorems
   consume them through `Phases.Security.pub`, and the probe fills that field. The unchecked
   verifier is in fact knowledge sound in the ideal model: the pooled claims are functions of
   public data, and the opening phase later checks them against `q`. What it fails is Layer
   12's `verify_iff_compiled` against a `verify` transcribed from the Rust, which is not built.
4. *Is the phase as merged faithful all the same?* Extensionally, to the specification's
   verifier: on an accepting transcript `cs = expectedValues …`, so pooling the computed values
   and pooling the values sent give the same pool. The finding is not about faithfulness; it is
   about the requirement that a dropped or weakened check leave some theorem unprovable, which
   this design cannot meet for this check.

**Verdict: CONFIRMED.**

**Shortest argument.** `pooled` (`PublicInput.lean:127-128`) does not take the message; the
verifier's output on acceptance is `pooled I s r` (`:233`); `rbr`'s proof (`:350-366`) is about
`pooled` and does not name `check`. Replace `check` by `fun _ _ _ ↦ true`: the verifier's
output on every transcript is still `pooled I s r`, the state function with the check clause
deleted satisfies the three laws, and `rbr`'s proof goes through unchanged (probe
`Probe1NoCheck`, `publicInputSecurity'`, three standard axioms).

## 4. One combined equation in the three executable verifiers, two per-limb equations in the specification

**The finding** (`gt-table-pub.md` section 7; `code-pubinput.md` section B). The specification
checks `c_ℓ = (1 + r)·mem[g⁰]_ℓ + r·mem[g¹]_ℓ` for `ℓ = 0, 1`; the Rust, the Python and the
recursion guest check the single equation `c₀ + y·c₁ = w₀ + r·(w₀ + w₁)` on the two public
words and pool the two scalars sent; the second accepts strictly more.

**What I read** (all at `a386121f`).

- `doc/leanvm/body/08-end-to-end-protocol.tex:29-33`: "`c_ℓ ≟ (1+r_m) mem[g⁰]_ℓ + r_m
  mem[g¹]_ℓ, ℓ ∈ {0,1}`".
- `crates/lean_vm/src/cpu/mod.rs:745-756`: `let want = primitives::multilinear::interp(l.pi[0],
  l.pi[1], r_pi); if pi_limbs[0] + F192::Y * pi_limbs[1] != want { return
  Err(CpuError::PublicInput); }`; `interp(lo, hi, t) = lo + t * (lo + hi)`
  (`crates/primitives/src/multilinear.rs:39-41`); `Y = (0, 1, 0)`
  (`crates/primitives/src/field/gf2_64x3.rs:44`, "root of `y^3 + y + 1`"). The two values then
  go into the pool unchanged: `finish_claims(&l, bus.claims, &table_claims, r_pi, pi_limbs)`
  (`:756`, `:656-667`) and `bind_pi_claim` (`:674-682`, `value: limbs[col - MEM_LO]`).
- `python-verifier/verifier.py:1398-1402`: `require(poly_eval(public_limbs, Y) ==
  multilinear_eval(public_input.halves(), [public_challenge]), …)` with `public_limbs =
  (*transcript.next_scalars(2), ZERO)`, then `claims.extend(ColumnClaim(column, public_point,
  value) for column, value in zip((MEMORY_0, MEMORY_1, MEMORY_2), public_limbs))`.
- `crates/rec_aggregation/guests/aggregate.py:1672-1688`: `mem = pi_0 + rm * (pi_0 + pi_1)`;
  `assert mem == mem_lo + mem_hi * Y_TOWER`; `claim_pool[…] = mem_lo`, `= mem_hi`, `= 0`. The
  comment: "MEM as ONE logical E-column".
- The honest Rust prover, `cpu/mod.rs:611-613`: `interp_k(F64(l.pi[0].c0), F64(l.pi[1].c0),
  r_pi)` and the same on `.c1`: per limb. So an honest proof passes both checks.

**The counterexample, by hand.** Write `w_i = w_{i,0} + y·w_{i,1}` (top limbs zero) and
`L_ℓ(r) = (1 + r)·w_{0,ℓ} + r·w_{1,ℓ} ∈ E`. Then `interp(w_0, w_1, r) = L_0(r) + y·L_1(r)`
(`E` is a `K`-algebra and `y` commutes with everything). The combined check reads `c_0 + y·c_1
= L_0(r) + y·L_1(r)`; for any `δ ∈ E` the pair `(L_0(r) + y·δ, L_1(r) + δ)` satisfies it, so
`|E|` pairs pass per `r`, against one for the per-limb check. No "K-valuedness" saves the
combined check: `c_0, c_1` are elements of `E` sent by the prover, and an evaluation of a
`K`-valued column at a point of `E` is itself in `E`, so nothing forces `δ ∈ K`, let alone
`δ = 0`.

With true evaluations of a committed memory whose cells differ from the words by `a_ℓ` (cell
0) and `c_ℓ` (cell 1), both in `K`: the per-limb check passes iff `(1 + r)·a_ℓ + r·c_ℓ = 0` for
both `ℓ`; the combined check passes iff `(1 + r)·A + r·C = 0` with `A = a_0 + y·a_1`, `C = c_0
+ y·c_1`, that is `A + r·(A + C) = 0`, which has one solution `r = A/(A + C)` when `A + C ≠ 0`
and none when `A + C = 0` unless `A = C = 0`. So both checks have knowledge error `1/|E|`
against a wrong memory. The dossier's instance, `a_0 = 1, c_0 = 0, a_1 = 1, c_1 = 1 + g` with
`g ∉ {0, 1}`: limb 0 needs `1 + r = 0`, limb 1 needs `1 + r·g = 0`, incompatible, so no bad
`r` per limb; `A = 1 + y`, `A + C = 1 + y·g ≠ 0`, so the combined check has the one bad
challenge `r = (1 + y)/(1 + y·g)`. Checked.

**Verdict: CONFIRMED.** The three implementations agree with each other and disagree with the
specification; both checks are sound at `1/|E|`; the per-limb check is strictly stricter; the
Lean phase follows the specification (`PublicInput.lean:136-137`). This is a leanVM finding
(an ambiguity of §8.2 against its implementations) that the blueprint inherits by following
the specification, and the dossiers' further point, that the deployed verifier's theorem is
owed at Layer 8 as a second `Phase.Def` rather than at Layer 12, follows from finding 3's
reading of `verify_iff_compiled`.

## 5. The GKR layer sumcheck: degree, error, and the extra combiner

**The findings** (`gt-bus.md` G1, G2). G1: the deployed layer round message is the normalized
cofactor of degree 4 (four coefficients on the wire, `c_0` derived), the layer's final check
has no equality factor, the per-round error is `4/|E|`; the blueprint says "degree 5",
"`5/|E|`", and Layers 4 and 5 define one sumcheck variant. G2: a combiner is drawn after every
layer, the last included, so there is one more than layers; the blueprint has "a fresh
combiner per layer".

**What I read** (all at `a386121f`).

- `crates/lean_vm/src/gkr.rs:358-427` (`verify_product_triple`): `let mut lambda =
  vs.sample();` before the loop (`:369`); in the binary branch `lambda = vs.sample();`
  (`:391`); in the radix-4 branch the rounds read `vs.next_round_poly(5, claim,
  Some(equality_point))` (`:399-400`), then `claim = poly_eval(&h, challenge)`; twelve children;
  `if claim != poly_eval(&products, lambda) { return Err(GkrError::LayerMismatch …) }`
  (`:410-413`), the products being `tail[0]*tail[1]*tail[2]*tail[3]` with no equality factor;
  `lambda = vs.sample();` (`:423`) at the end of the iteration; `point = vec![low_challenge,
  high_challenge]; point.extend_from_slice(&round_point)` (`:424-425`).
- `crates/fiat_shamir/src/transcript.rs:289-302`: `next_round_poly(n_coeffs, claim, eq)` reads
  `n_coeffs − 1` scalars and derives the fixed one; with `eq = Some(r)`, `fixed = 0` and
  `coeffs[0] = claim + r * sum_from(1)`, the comment "`c0 + r·(c1 + … + cd) = claim`". With
  `n_coeffs = 5`: four read, `c_0` derived, a polynomial of degree 4.
- `python-verifier/verifier.py:406-413`: `sumcheck_round_poly(count, claim, eq_factor)`; with
  an equality factor it reads `count − 1` scalars and returns `[claim + eq_factor * E.sum(tail),
  *tail]`. `:433-457` (`verify_gkr_grand_products`): `combiner = transcript.sample()` at `:435`
  and at `:453` inside the loop; `sumcheck(transcript, claim, 2**step + 1, point)` (`:445`,
  `count = 5` for `step = 2`); `require(claim == poly_eval(products, combiner), …)` (`:449`)
  with no equality factor.
- The table sumcheck for contrast, `constraints.rs:267` `next_round_poly(4, claim, None)`
  (`fixed = 1`, `c_1 = claim + c_2 + c_3`: the textbook `h(0) + h(1) = claim`) and `:271-274`
  where the equality factors are multiplied into the final weights.
- The blueprint at `b435631`: `:315` "A round polynomial travels as its coefficient list, low
  degree first, of length `d + 1`; the oracle protocol sends all of them. Dropping one is the
  *encoding* of Layer 12"; `:321` "A fresh combiner `λ` per layer; … Layer sumcheck messages
  have degree 5 (eq × four multilinears); the round check is on the cofactor (Gruen)";
  `:898-901` (Layer 4) "the eq-weighted variant has `eq(ζ_{<τ_j}, ·)` as an explicit factor
  whose evaluation at `r` the verifier computes itself (so `d` counts the cofactor plus one)";
  `:941-942` "`5/|E|` to each sumcheck round".
- The specification, `05-arithmetization.tex:91` (per `gt-bus.md`, verified by
  `verify-gt-bus.md`): "at every layer a combiner"; `03-proving-primitives.tex:110`: "a
  zerocheck's summand carries `eq(r, ·)`, which the verifier can form itself, so only the
  cofactor travels and it is one degree lower. A zerocheck round on a degree-`d` cofactor
  therefore costs `d` field elements."

**Attacks tried.**

1. *Could "degree 5" be the right description in some sense?* Yes, of the summand: `eq(point,
   x) · Σ_s λ^s ∏_{4} Ṽ^s(…)` has degree 5 in each variable, which is what the parenthetical
   "(eq × four multilinears)" says, and `:321`'s "the round check is on the cofactor (Gruen)"
   correctly names the deployed check. What is wrong is the *message*: under the blueprint's
   own convention `:315` a message "of degree 5" is six coefficients in the oracle protocol and
   five on the wire, where the deployed verifiers read four (`gkr.rs:399-400`,
   `transcript.rs:289-302`, `py:411-413`). A verifier written from `:315` and `:321` together
   misparses every Rust proof. And Layer 4's one variant (`:898-901`, the table sumcheck's:
   the full round polynomial travels, the verifier evaluates the equality factors itself at
   the end, `constraints.rs:271-289`) applied to the GKR gives a layer check with an equality
   factor, which the deployed check has not (`gkr.rs:410-413`). So "wrong degree" is the
   literal reading of `:321` with `:315`, and "no definition" (of the normalized variant) is
   exact.
2. *Is the error "wrong"?* No: it is loose. ArkLib's round-by-round bound is an inequality
   (`RoundByRound.lean:568`), so a `Security` at `5/|E|` per round is provable for the deployed
   verifier, whose tight error is `4/|E|`. For the standard variant with a degree-5 message,
   `5/|E|` is tight; that is where the blueprint's number comes from, and it is the wrong
   verifier. The dossier's proposed correction to `4/|E|` is an improvement in tightness, not a
   repair of a false bound. This clause is **weakened**.
3. *The exact error of one deployed round, settled.* Before round `t` the verifier holds a
   claim `C`; the honest relation is `C = (1 + r_t)·h_t(0) + r_t·h_t(1)` for the true cofactor
   `h_t` (degree `≤ 4`: four multilinear children, the equality factors of the bound
   coordinates and of `r_t` itself never in the message), because `h_{t−1}(χ_{t−1}) = Σ_{b}
   eq(r_t, b)·h_t(b)`. The prover's four coefficients and the derived `c_0` fix a polynomial
   `h'` of degree `≤ 4` that satisfies the identity with `C` by construction
   (`transcript.rs:301`). If `C` is false, `h' ≠ h_t` (else `C` would be the true value); two
   distinct polynomials of degree `≤ 4` agree at most at 4 points of `E`, so the new claim
   `h'(χ_t)` is true for at most 4 challenges: **`4/|E|`**. Tight: for any distinct `ρ_1, …,
   ρ_4` there is `a ≠ 0` with `h' = h_t + a·∏(Y − ρ_i)` satisfying the identity with any `C ≠
   C_true` (one linear condition on `a`, solvable unless `(1 + r_t)∏ρ_i + r_t∏(1 + ρ_i) = 0`,
   avoided by moving one `ρ_i`). If instead the verifier kept the equality factor in the
   running claim (`claim := eq(r_t, χ_t)·h'(χ_t)`), the challenge `χ_t = 1 + r_t` would zero
   both sides and be a fifth bad point: `5/|E|`, the other verifier's error. The deployed
   verifiers never form that product (`gkr.rs:402-404, 410-413`; `py:426, 449`).
4. *G2.* `gkr.rs:369` then `:391`/`:423` at the end of every iteration; `py:435` then `:453`.
   Combiners drawn: one per layer plus one; the last is used by nothing. In the ideal oracle
   model harmless; after Fiat–Shamir a squeeze that moves the state, so a verifier that does
   not draw it desynchronizes from `ξ` onward and rejects every Rust proof. The blueprint's
   "per layer" (`:321`, `:940-941`) follows the specification's wording (`05:91`); the
   implementations draw one more. The blueprint must follow the implementations here (the
   compiled verifier is bound to their chain), or record a deviation. Confirmed as stated;
   the classification "an error of the blueprint" is right for the compiled verifier's sake,
   and the report may add that the specification's count is the blueprint's source.

**Verdict: WEAKENED** in the single clause "the wrong error": `5/|E|` is a valid loose bound;
the wire (four coefficients, not five), the layer check (no equality factor) and the missing
definition of the normalized variant are **confirmed**, and so is the extra combiner. The
severity class (major: a verifier written from the blueprint rejects every Rust proof) is
unchanged.

## 6. The generic GKR of Layer 5 cannot be appended in the bus phase, and its state function cannot carry the zerocheck conjunct

**The finding** (`gt-bus.md` G3).

**What I read.**

- The blueprint's Layer 5 signature (`:930-934` at `b435631`): `def gkr (nside μ : ℕ) :
  OracleReduction []ₒ (StmtIn := Fin nside → E) (OStmtIn := fun _ : Fin nside ↦ ETable μ) Unit
  (StmtOut := (Fin μ → E) × (Fin nside → E)) (OStmtOut := fun _ : Fin nside ↦ ETable μ) Unit …`.
  The holes table (`:606` per the dossier) has the bus phase consume it.
- ArkLib `Composition/Sequential/Append/Basic.lean:709-713` at `dca90385`:
  `def OracleReduction.append (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂
  pSpec₁) (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)`: the second
  component's input oracle family is the first's output family, index type included; likewise
  `OracleVerifier.append` (`:619-621`). The spine's `Def.append` (`Component.lean:143-148`)
  inherits this.
- `Phase.lean:37-38` at `b435631`: `abbrev Def (StmtIn StmtOut : Type) := Component.Def StmtIn
  (TheOracle I) Unit StmtOut (TheOracle I) Unit`, the one oracle the stack.
- ArkLib `LiftContext/Reduction.lean` at `dca90385`: `theorem liftContext_completeness`
  (`:355`, `sorry` at `:365`) and `theorem liftContext_rbr_knowledgeSoundness` (`:542`, `sorry`
  at `:560`). At the new pin `7653a901` the same two theorems are still admitted (`:355`/`:365`
  and `:542`/`:554`), so the upgrade did not retire the workaround.
- `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean:182-194` at `b435631`, the appended state
  function's predicate: `state G K₁ K₂ k s tr w := if k.val ≤ m then K₁ … else G.check s tr₁ =
  true ∧ K₂ (k.val − m) (G.out s tr₁) (right tr …)`; `appendGuarded` (`:474`) packages it. Inside
  the second component the state is `K₂`'s, evaluated on the second component's own transcript.
- The GKR verifier, `gkr.rs:358-427`: it reads messages and challenges only, and queries no
  oracle. The leaf tables enter the deployed protocol only through the input relation (the
  roots are their products) and the output (the leaf claims at `ζ`).

**Attacks tried.**

1. *Make the leaf tables part of the statement.* Typechecks, but the previous phase must then
   output three tables of `2^μ` elements of `E` computed from `q` and `(α, β)`, which an
   oracle verifier cannot do without reading `q` in full; and the composed verifier would hold
   the leaf tables in the clear, which is not the deployed verifier. Not a way out for a
   faithful phase.
2. *A virtual-oracle interface.* The oracle *type* must be the same on both sides of every
   append (`Append/Basic.lean:709-711`), and the whole protocol's oracle is `TheOracle I`
   (`Phase.lean:37-38`). A GKR written over `OStmt := TheOracle I` whose relations mention the
   leaves as a function of the stack needs no lifting, and since the GKR verifier never
   queries its oracle the oracle type is a phantom for it. That is the dossier's proposal
   ("restate Layer 5's component over a context, with riders"), a change of Layer 5's
   signature, not an append of the sketch as written. So the first half is confirmed: as
   written the sketch cannot be appended; carrying it along the map `q ↦ leaves` is ArkLib's
   lifting, admitted at both pins.
3. *The zerocheck conjunct.* `Seam.bus` says the zerocheck claims hold at `ζ` (linear claims
   of value `0` at `ζ_{<τ_j}`, `Seams.lean:175`), and `Seam.commit` says `ConstraintsVanish q`
   (`Instance.lean` via `M3Holds`). Round-by-round knowledge soundness quantifies worst-case
   over the transcript prefix (`RoundByRound.lean:560-568`), so once `ζ` is drawn an adversarial
   prefix may have `C̃(ζ) = 0` for a constraint `C` that does not vanish; if the state function
   still said `ConstraintsVanish q` at that point it would be false at the end of an accepting
   run whose output (true claims at that `ζ`) is in `Seam.bus`, violating `toFun_full`. So the
   clause must flip from `ConstraintsVanish` to "the claims hold at the drawn coordinates"
   *during* the drawing of `ζ`, that is inside the GKR's last layer (`gkr.rs:424-425`: every
   coordinate of `ζ` is a challenge of the last iteration). The appended predicate inside the
   second component is `K₂`'s alone (`KnowledgeAppend.lean:190-194`); a clause that changes
   with the second component's challenges cannot be added around it. Hence a GKR whose
   relations do not mention the constraints cannot supply the bus phase's `Security`; the
   "riders" of the proposal put the constraints into the GKR's relations, which is the only
   place they can go. Confirmed.

**Verdict: CONFIRMED** (both halves). The upgrade to the new pins changes nothing here.

## 7. Flock: the interface drops the limb claims, the slot map is circular, the phase is not writable over an abstract instance, and acceptance test 20 misfiles a prover defect

**The findings** (`gt-flock-ring.md` 8.1 to 8.4; section 4).

**What I read.**

- Blueprint Layer 9 at `b435631` (`:1072-1092`): "`LeanerVM/Protocol/Flock.lean` (module, over
  `I`; hole P6)"; `structure FlockInterface (I : M3Instance)` with `reduction : OracleReduction
  []ₒ (StmtIn := ColumnClaims) (OStmtIn := fun _ : Unit ↦ Column μ) Unit (StmtOut :=
  WeightedClaim) …`, `limbColumns : Column μ → Fin 18 → Column (s.τ 5)`, `relIn : Set _ -- the
  eighteen column claims are true of limbColumns, and aux (Flock's R1CS)`, `relOut : Set _ --
  the weighted claim holds for q`. Layer 3 (`:846-848`): "`leanIsaInstance.layout` combines the
  two, the slot map being #3's `FlockInterface.limbColumns` (Layer 9)". Acceptance test 20
  (`:1323-1325`): "Flock's `(1 + r_eq)⁻¹` at `r_eq = 1` is #3's, inside `flockError`."
- `Instance.lean:143-148` at `b435631`: the instance's only Flock-related field is `aux :
  Column μ → Prop` with `decAux`.
- `cpu/mod.rs` at `a386121f`: `finish_claims` (`:656-667`) builds the pool from the bus claims,
  the table claims and the three public-input claims and maps them through `slot_claims`
  (`:790-814`), which routes a BLAKE2s value column to `pcs::SlotClaim::Strided { offset: …
  QFLOCK …, slot, stride_log, point, value }`; then `verify_reduction(n_blocks, &mut vs)`
  (`:765`) takes no claim; `ring_switch_verify(n_blocks, offset, &replay.claim)` (`:767`) makes
  one weighted claim; `pcs::verify(&mut vs, &slots, &ring, …)` (`:768`) opens the pool and the
  ring-switched claim together. So the eighteen limb claims are opened, and Flock reads none of
  them.
- `crates/flock/src/zerocheck.rs:116-123`: `let g0 = (claim + r_eq * g1) * (F192::ONE +
  r_eq).inv(); ps.add_round_poly(&[g0, g0 + g1 + g_inf, g_inf], true);` with
  `Transmitter::add_round_poly(coeffs, eq)` skipping index `usize::from(!eq) = 0`
  (`transcript.rs:63-71`): `c_0` is not sent. The comment: "`G(0)` never rides the wire: the
  eq split `(1 + r_eq)·G(0) + r_eq·G(1) = claim` fixes it." The inverse contract per the
  dossier (`gf2_64x3.rs:137`): `ZERO.inv() == ZERO`.
- The verifiers' derivation of `c_0`: `transcript.rs:297-302` (`claim + r * sum_from(1)`),
  `py:411-413`. The lincheck prover, `lincheck.rs:1090`: `let mut running =
  inner_product_ext(&comb_vec, &z_vec);`, "The running claim, mirrored from the verifier".
- The specification: `c-flock-protocol.tex:69` "with Gruen's eq-factor optimization" and
  `03-proving-primitives.tex:110` "only the cofactor travels": no inverse anywhere.
- An inventory of every `.inv()` at the pin under `crates/{flock,lean_vm,fiat_shamir,pcs}/src`
  and `crates/primitives/src/multilinear.rs` (`git grep`), plus every `inv(`, `inverse`, `/`
  in `python-verifier/verifier.py`. Rust: `zerocheck.rs:117` (the prover, above); `:703` (a
  test, `bad.stream`); `univariate_skip_optimized.rs:96-99, 114` (`1 + g^{2^k}`, constants);
  `cpu/execute.rs:319, 562, 607` (the VM); `tables.rs:795, 984` (witness generation);
  `pcs/src/ntt.rs:50` (`s_at_root`, a subspace-polynomial value at a domain point);
  `additive_ntt_f64.rs:26` (`row[0]`, a basis constant); `ring_switch.rs:1068` (inside a
  `#[test]`, `assert!(!verify_e2e_dense(&bad))`); `whir_induce.rs:109-114` (`invert_sks`,
  subspace-polynomial values, zero-guarded); `multilinear.rs:185, 237` (constants). Python:
  `:980` `inverses = [value.inv() if value else ZERO for value in roots]` with `roots =
  _subspace_roots(message_log)` (`:962`), constants of the domain; `:1099, 1110` generator
  powers and `PHI`, constants. **No verifier inverts a value that depends on a challenge.**

**Attacks and re-derivations.**

1. *8.1, error one.* The sketch's reduction outputs one `WeightedClaim` and `relOut` is "the
   weighted claim holds". Take a statement whose eighteen limb claims include one false value
   while `aux q` holds; the honest Flock run (which reads no claim) ends with a true weighted
   claim, so the output is in `relOut` with probability one while the input is outside `relIn`;
   the state function is false at the start and true at the end, prover messages cannot flip
   it, so the challenges must, with total probability one: `Σ flockError ≥ 1`. The deployed
   phase avoids this by keeping the eighteen claims in the pool to the opening. Could the
   sketch mean "in addition to the pool passing through"? Its `StmtOut := WeightedClaim` and
   `relOut` say otherwise, and the spine's slot `Phase.Def I (I.Stmt × PubOut I) (I.Stmt ×
   FlockOut I)` with `FlockOut.columns` (`Seams.lean:147-152`) is the shape that passes them.
   Confirmed.
2. *8.2, circular.* `:846-848` makes `leanIsaInstance.layout` depend on
   `FlockInterface.limbColumns`, and `:1077` makes `FlockInterface` take `I : M3Instance`,
   whose `layout` is a field (`Instance.lean:140`). Confirmed; the fix is where the dossier
   puts it (a slot map in `Parameters/`, the generic low-index identity in `ToCompPoly/`).
3. *8.3, not writable over `I`.* The sketch itself reaches for `s.τ 5` and an unbound `μ`,
   leanISA's sizes, while headed "over `I`"; `M3Instance` offers only `aux : Column μ → Prop`
   (`:146`), which names neither the column, nor `k_batch`, nor the R1CS, and the verifier
   cannot apply `decAux` (it has no `q`). The deployed verifier needs `n_blocks` and the
   offset of `q_flock` (`cpu/mod.rs:763-767`). Confirmed; the proposed `FlockRegion I` is the
   minimal extra datum.
4. *8.4, `r_eq = 1`, re-derived.* The true claim at `r_eq = 1` is `(1 + 1)·G(0) + G(1) = G(1)`.
   The prover computes `g0 = (G(1) + 1·G(1))·(1 + 1)⁻¹ = 0·0 = 0` and sends `c_1' = 0 + G(1) +
   G(∞)` and `c_2 = G(∞)` (the true `c_1` is `G(0) + G(1) + G(∞)`). The verifier derives `c_0'
   = claim + 1·(c_1' + c_2) = G(1) + G(1) = 0`. In the basis `G(X) = G(0)(1 + X) + G(1)X +
   G(∞)X(1 + X)`, both parties now hold `G'(X) = G(X) + G(0)(1 + X)`, and the prover's own
   next claim `g0 + χ(g0 + g1 + (1 + χ)g_inf)` equals `G'(χ)`: they agree on a wrong value
   whenever `G(0) ≠ 0` and `χ ≠ 1`. The error rides the zerocheck's remaining rounds into the
   derived `v_c` on both sides (the terminal identity is solved, not checked, `c-flock:69-72`),
   so the zerocheck itself does not reject. The lincheck's verifier target is then built on the
   wrong `v_c`, while the lincheck prover starts its running claim from the true inner product
   (`lincheck.rs:1090`); its first wire message `[e0, e0 + e1 + einf, einf]` with `e0 = running
   + e1` has `c_1` derived by the verifier from *its* claim, so the two parties' polynomials
   differ by a nonzero multiple of `X`, the discrepancy is multiplied by each round's challenge,
   and the terminal identity fails except when a challenge is `0`. So: the Rust prover emits a
   proof the verifier rejects, with probability at most `(k_batch + 1)/|E|` over the sampled
   equality coordinates, and only when `G(0) ≠ 0`. A prover that sends the true `c_1, c_2` is
   accepted at `r_eq = 1`, because the verifier's `c_0 = claim + r(c_1 + c_2)` is then the true
   `G(0)` for every `r`. This is a completeness defect of the implementation's prover, not a
   soundness event, and `flockError` (a per-challenge knowledge error, `Component.lean:65-66`)
   has no slot for it; acceptance test 20's sentence puts it in the wrong theorem. Confirmed
   on paper, as the dossier says (its Python model, probe 9.2, was re-run by
   `verify-gt-flock-ring.md`); not executed in Rust.

One correction of wording, already made by `verify-gt-flock-ring.md` and confirmed here: the
dossier's "The verifiers take no inverse" (section 4.1, first line) should read "no inverse of
a challenge-dependent value"; its proposed text for acceptance test 20 already says the latter.

**Verdict: CONFIRMED** (8.1, 8.2, 8.3, 8.4).

## 8. The two target-theorem sketches, and the instance that is not `Ensemble.toM3`

**The findings** (`boundary-adaptor.md` findings 1 to 4; section A.5; probe `KnownColumn`).

**What I read.**

- Blueprint at `b435631`: `:803-805` "`def leanIsaInstance (prog : Program) (s : Sizes) :
  M3Instance -- Ensemble.toM3 of the eight tables with leanISA's separators and directions`";
  `:1247-1250` the two T4 sketches, `baseVerifier_extractsExecution (fs bcs mca flock) (h :
  verify prog input proof = true) : except with probability niError, ∃ t, ValidExecution prog
  input t` and `baseProver_complete (hfill : HasFillBlocks prog) (h : ValidExecution prog input
  t) : verify prog input (prove prog input (witness of t)) = true`; `:1252-1255` "The first
  composes … `constraintSoundness`; the second composes `constraintCompleteness`, …".
- `docs/roadmap/leanisa-blueprint.md:1163, 1165` at `b435631`: `constraintSoundness (hwf :
  WellFormedBytecode prog) …` and `constraintCompleteness (hwf : WellFormedBytecode prog) …`;
  `:207, 217`: "The constraints let a `JUMP` sentinel execute (acceptance test 20), which
  `WellFormedBytecode` excludes"; `docs/leanvm-target.md:61` records the hypothesis.
- `tests/LeanerVMTests/Semantics/Execution.lean:418-461` at `b435631`: `jumpSentinelProg`,
  `example : ¬ SentinelSafe jumpSentinelProg := by decide`, `jumpSentinel_row1` and
  `jumpSentinel_row2` (two steps chaining `Regs.initial` to `Regs.final`), and the example that
  `run` halts at `(g, g)`, so no step count gives a `ValidExecution`. Proved (the file is in the
  test build; no `sorry` in the region).
- `LeanerVM/Semantics/Execution.lean:108-115`: `HasPublicBoundary input t := minLogMem ≤ t.κ ∧
  t.κ ≤ maxLogMem ∧ …`; `ValidExecution prog input t := HasPublicBoundary input t ∧ run prog
  t.image t.steps Regs.initial = some (Regs.final prog)`. `Arithmetization/Statement.lean:355-358`:
  `AssignmentRepresents` with `κ_eq : (imageOf w.data).1 = t.κ`. `maxLogMem = 32` (the
  Rust `MAX_LOG_MEM = 32`, `cpu/mod.rs:52`; `Caps.le_maxLogMem`).
- The stacking window: `crates/lean_vm/src/pcs.rs:49, 51` `MIN_MU = 15`, `MAX_MU = 28`;
  `cpu/mod.rs:174-176` rejects `mu ∉ [MIN_MU, MAX_MU]`; `verifier.py:907-908, 1379`.
- `Instance.lean:86-89, 167-170, 180-186, 201` at `b435631`: `Coord` (`const`, `known col`,
  `committed c h`), `coordCell` (a `known` coordinate reads its own column, a `committed` one
  reads the stack), `boundaryTuples`, `tuples := flushTuples ++ boundaryTuples`, `Balanced :=
  (tuples q .push).Perm (tuples q .pull)`.
- The deployed framework blocks: `layout.rs:352-395` (per `gt-bus.md` E.3, its table verified
  by `verify-gt-bus.md`): the bytecode blocks' program columns are `Coord::Public`, the index
  columns `Coord::Index`, evaluated by the verifier itself (`leaf.rs:444, 453`).
- The probe `KnownColumn.lean` (source read): `toyOf p` puts the block's column as `.known p`;
  `toyCommitted` puts it as `.committed ⟨0, 1⟩ rfl`; `pushesTwo` has columns `[2, 2]`;
  `#guard M3Holds toyCommitted (1 : K) pushesTwo` and `#guard ¬ (toyOf prog).Balanced
  pushesTwo` (recorded exit 0 at the old pins; at the new pin `2 : K` is `0`, and the dossier's
  `KnownColumnNew.lean` restates it with `K.ofBits 2`).
- The status at `b435631` (per `boundary-adaptor.md`, `protocol-status.md:220-223`), decision
  8: "the fixed columns are `Coord.known` data".

**Attacks tried.**

1. *Is `WellFormedBytecode` implied by something the verifier checks?* No. The Rust verifier's
   checks on the program are the bytecode length (`cpu/mod.rs:158-159`) and its hash in the
   transcript seed; the Python's `build_layout` takes any `Sequence[K]` (`:856`); neither looks
   at the sentinel's opcode or at fill blocks. `constraintSoundness` needs `hwf`
   (`leanisa-blueprint.md:1163`), and the JUMP-sentinel test gives a program with rows that
   balance the state channel and no `ValidExecution`, so the sketch without `hwf` is false. A
   Lean `verify` could add the decidable check and reject more than the Rust, but the sketch
   does not say so and `verify_iff_compiled` would then need the same conjunct on its right.
   Also confirmed: "except with probability" attached to a closed Boolean of a deterministic
   function is not a statement; the probability lives in the random-oracle verifier.
2. *Could `baseProver_complete` carry an implicit resource bound?* No: it quantifies over
   every `t` with `ValidExecution prog input t`, and `HasPublicBoundary` admits `t.κ = 32`
   (`Execution.lean:109`). A run that touches a cell at address `≥ 2^31` needs `κ = 32` by
   `HasPublicBoundary`'s `image.read`; any witness of it has `(imageOf w.data).1 = 32`
   (`Statement.lean:358`), the four memory-height columns alone take `4·2^32 = 2^34` cells,
   the stack has `μ ≥ 34 > 28`, and every deployed verifier rejects the announcement
   (`cpu/mod.rs:174-176`, `pcs.rs:51`, `py:1379`). No `prove` and no `verify` transcribed from
   the Rust can make the conclusion true for that `t`. The other three points (no witness
   generator in scope, `constraintCompleteness` takes `WellFormedBytecode` not
   `HasFillBlocks`, the rate is nobody's) are read straight off the sketch and the leanISA
   blueprint.
3. *Is the "trap of the built parts" real?* Yes, as a property of `Balanced`: a `committed`
   coordinate reads the stack (`coordCell`, `Instance.lean:167-170`), so an instance whose
   bytecode block is a table of `q` makes `Balanced` a statement about whatever the prover
   committed there, and `satisfiedBy_witnessOf`, which must rebuild the block's rows from
   `prog` (`BytecodeRowsAreTheProgram`), has nothing to rebuild them from. The probe shows it
   on the toy in eight lines. But the blueprint already decided against that shape (decision
   8, `Coord.known`; the spine's `boundary` field), and leanVM's blocks are `Public`/`Index`
   coordinates the verifier evaluates. So the substance of finding 1 is that the phrase at
   `:803-805` (and `:21, :77, :1369, :1398`) is stale against decision 8, that `Ensemble.toM3`
   has no signature and could not produce `μ`, `layout`, `publicLines`, `aux`, `Stmt`, and
   that the bridge lemma for the boundary blocks (finding 2) is what the adaptor lacks. Not a
   refutation: the sentence as written specifies the wrong instance, which is the brief's
   definition of major.

**Verdict: CONFIRMED** (findings 1 to 4). For finding 1 the report should say that decision 8
already settles the design and the blueprint's text is what is wrong; the missing boundary
bridge lemma (finding 2) is the real gap.

## 9. `Admissible` cannot equal `Caps`

**The finding** (`gt-bus.md` G4; `boundary-adaptor.md` finding 5).

**What I read.**

- `crates/lean_vm/src/cpu/mod.rs:130-178` (`read_public`) at `a386121f`: after the caps on
  `bytecode_size`, `log_mem`, `taus` and `taus[BLAKE2S_TABLE]`, it rejects
  `::pcs::whir::validate_log_inv_rate(log_inv_rate).is_err()` (`:167`) and, after building the
  layout, `!(pcs::MIN_MU..=pcs::MAX_MU).contains(&l.shape.mu)` (`:174-176`), with the comment
  "The caps bound each announced log on its own; what the PCS is configured for is the stacked
  size they imply, which they do not bound." `pcs.rs:49, 51`: `MIN_MU = 15`, `MAX_MU = 28`.
  The Python: `require(1 <= log_inverse_rate <= 4, …)` (`:1377`), `require(MIN_STACKED_LOG <=
  layout.stack_log <= MAX_STACKED_LOG, …)` (`:1379`, constants `:907-908`).
- `LeanerVM/Arithmetization/Statement.lean:250-263` at `b435631`, `structure Caps`: five
  fields, `minLogMem_le`, `le_maxLogMem`, `heights`, `blake2s_height`, `well_shaped`. Its
  docstring `:245-249` and the module docstring `:79-81`: "(7) the WHIR rate (`:167`) and (8)
  the stacked size `mu ∈ [MIN_MU, MAX_MU]` (`:174-176`) are parameters of the commitment,
  left to the protocol layer". `well_shaped : WellShapedData w.data` is "Not a verifier check".
- Blueprint at `b435631`: `:800` `def Sizes.Admissible (prog : Program) (s : Sizes) : Prop --
  the caps; decidable`; `:801` `theorem admissible_iff_caps : s.Admissible prog ↔ (Caps w ∧
  Sizes.ofWitness w = some s)`; `:1218-1220` `verify_iff_compiled … ↔ ∃ s, s.Admissible prog ∧
  …`; `:1130` `piopError_le (hs : s.Admissible prog) : …`. `:796-798`: `Sizes` has
  `logInvRate`, and `Sizes.ofWitness (w : EnsembleWitness leanIsaEnsemble) : Option Sizes`.

**Attacks tried.** Could the windows be derivable from the caps? No: the caps allow
`κ_mem = 32`, whose four columns alone force `μ ≥ 34`; and no witness determines a rate. Could
`admissible_iff_caps` be read with `Admissible` including the windows? Then its right-hand
side, `Caps w ∧ …`, lacks them, and the `↔` fails from left to right at every witness whose
sizes are cap-admissible and outside a window. Could `verify_iff_compiled` hold with
`Admissible = Caps`? A `verify` transcribed from the Rust rejects an announcement with `μ =
34` (`:174-176`) while the oracle verifier of `leanIsaInstance prog s` has no `μ` window, so
the `↔` fails from right to left. The three statements cannot hold together, as the dossier
says. I did not re-derive the dependence of `piopError_le`'s numeric bound on the window
(`gt-bus.md` D.4: at the caps alone `μ_bus = 38` and the `(α, β)` term is already `2^40/|E|`);
it is not needed for the verdict.

**Verdict: CONFIRMED.**

**Shortest argument.** `Caps` (`Statement.lean:250-263`) has no rate and no stacked-size
window, by its own docstring (`:79-81`); the deployed verifiers reject `log_inv_rate ∉ [1, 4]`
and `μ ∉ [15, 28]` (`cpu/mod.rs:167, 174-176`; `verifier.py:1377, 1379`); the blueprint states
`Admissible` as "the caps" (`:800`), `admissible_iff_caps` (`:801`) and `verify_iff_compiled`
with `∃ s, s.Admissible prog` (`:1218-1220`). With `Admissible = Caps`, `verify_iff_compiled` is
false at `κ_mem = 32`; with the windows added, `admissible_iff_caps` is false.

## 10. Layer 1's strided reader and `leanIsaInstance_fits`

**The finding** (`code-layer1.md` G.1, G.2; section B.8).

**What I read.**

- `LeanerVM/Protocol/Spine/Instance.lean:73-81` at `b435631`: `structure Layout (μ : ℕ) (ι :
  Type) (κ : ι → ℕ)` with exactly the fields `read`, `extend`, `read_eval`. No `total`.
  `ToCompPoly/Stacking.lean:87`: `def total : ℕ := B.offsetNat B.n` on `Blocks`;
  `Stack.lean:97`: `def layout (hμ : B.total ≤ 2 ^ μ) : Layout μ (Fin B.n) B.size`. Blueprint
  `:808`: `theorem leanIsaInstance_fits : (leanIsaInstance prog s).layout.total ≤ 2 ^
  (leanIsaInstance prog s).μ`.
- `ToCompPoly/Multilinear.lean` at `b435631` (outline): `slice` (`:307`), `evalMle_split`
  (`:331`), `evalMle_append_boolVec` (`:342`), `placeSlice` (`:351`); `boolVec` (`:235`);
  nothing that freezes the *low* coordinates. `Stack.lean`: `Layout.comap` (`:52`),
  `readColumn` (`:73`), `layout` (`:97`); all aligned.
- leanVM: `cpu/mod.rs:790-814` (`slot_claims`, `SlotClaim::Strided { offset, slot, stride_log,
  point, value }`, "the point freezing the low 8 coords to the slot's bits and the high coords
  to `r`"); `verifier.py:884-894` and `hash_flock.rs:87-115` per the dossier.
- Blueprint `:841-848`: "The layout has two readers. … The eighteen BLAKE2S value limbs are
  virtual columns …, read as strided slots of `q_flock` … `Layout` admits both readers; `Blocks`
  expresses only the first, so `leanIsaInstance.layout` combines the two, the slot map being
  #3's `FlockInterface.limbColumns` (Layer 9)."
- The dossier's `StridedProbe.lean` (per its section I.6; recorded exit 0 at the old pins):
  `sliceLow` and `evalMle_boolVec_append : evalMle t (boolVec i ++ s) = evalMle (sliceLow t i)
  s` proved from Layer 1's own lemmas, twenty lines.

**Attacks tried.**

1. *`leanIsaInstance_fits`.* `Layout` has no `total`; the fit is a `Blocks` fact and is the
   argument `hμ` of `Blocks.layout`, so it must be proved *before* the instance's `layout`
   field can be filled. Confirmed as a plain type error in the sketch; one line to fix.
2. *Is a strided reader derivable from what is there?* The generic identity is: the probe
   derives it from `evalMle_split`, `lagrangeBasis_boolVec` and `sum_cube_split` (all in
   `Multilinear.lean`). What is not derivable is a `Layout` over all of `ColumnId`: `Layout.comap`
   places columns of a block's own height, and a limb column of height `2^τ_5` sits inside a
   block of `τ_5 + 8` variables, so a second constructor (a strided `Layout` from a block and a
   slot map) and a combinator (piecewise over a sum of index types) are needed. Those are new
   definitions, small, and sketched by nobody.
3. *"Assigned to no layer."* Overstated: `:841-848` assigns the combination to Layer 3's
   `leanIsaInstance.layout` and the slot map to Layer 9. What is unassigned is the lemma, the
   strided `Layout` and the combinator; and the slot map's assignment is the circular one of
   finding 7 (8.2). So the blueprint does not omit that leanVM reads the limbs strided; it
   omits how the instance will do it.

**Verdict: WEAKENED.** Both facts hold (no low-index reader in Layer 1 or anywhere on `main`;
`leanIsaInstance_fits` names a field `Layout` has not, and is needed before the instance). The
clause "assigned to no layer" is overstated, and the missing piece is a twenty-line lemma plus
two small definitions rather than a design. Severity by the brief's letter stays major
(`leanIsaInstance` cannot be built as sketched); by weight it is the smallest of the eleven.

## 11. The status file's finding that the Python verifier omits the caps

**The finding** (three dossiers, `gt-bus.md` G5, `gt-flock-ring.md` 8.10, `gt-table-pub.md`
*Two status findings are wrong at the pin*): status `:316-318` says "F9 the Python verifier
omits the caps `log_mem ∈ [16, 32]`, `τ_j ≤ 32`, the bytecode power-of-two bound and
`τ_BLAKE2S ≥ 3` (`verifier.py:1372-1379` versus `cpu/mod.rs:158-170`)"; `:164` "Finding F9 …
is still to be reported to leanVM."

**What I read** (`python-verifier/verifier.py` at `a386121f`).

- `:1372-1378`: `announced = transcript.next_scalars(2 + len(TABLES))`; `require(all(value.c1
  == value.c2 == 0 …))`; `log_memory`, `table_logs`, `log_inverse_rate` read off; `require(1 <=
  log_inverse_rate <= 4, …)`; `layout = build_layout(bytecode, log_memory, table_logs)`.
- `:856-864`, `build_layout`: `log_bytecode = log2_strict(len(bytecode)) - BUS_BITS;
  require(16 <= log_memory <= 32 and all(0 <= log_height <= 32 for log_height in
  table_log_heights) and table_log_heights[OP_BLAKE2S] >= 3 and 0 <= log_bytecode <= 32,
  "invalid announced table sizes")`.
- `:252-254`, `log2_strict`: `require(value > 0 and not value & (value - 1), "expected a power
  of two")`.
- Units of the bytecode cap: the Rust caps `prog.prog.len()`, a `Vec<Op>` ("bytecode (size B,
  power of two)", `cpu/mod.rs:181-182`), at `2^MAX_LOG_BYTECODE = 2^32` (`:64, :159`); the
  Python caps the word count `len(bytecode)` at `2^(32 + BUS_BITS)` with `BUS_BITS = 4`
  (`:525`), sixteen words per instruction. The same cap.

**Attack.** The status read `:1372-1379` and not the function called at `:1378`. All four caps
named by the status are in `build_layout`, and the power-of-two requirement is in
`log2_strict`. `verify-gt-bus.md` corrected the commit attribution of `gt-bus.md` (the check
was assembled in `8a6e7750`, `348ca455`, `5751a5c7`, all ancestors of the pin); the conclusion
is unaffected.

**Verdict: CONFIRMED.** The status's finding is false at the pin; there is nothing to report
upstream on this point; `:164` and `:316-318` are to be deleted.

---

## Summary table

| # | Finding | Verdict | One line |
| --- | --- | --- | --- |
| 1 | `piopError` unbounded | CONFIRMED | `err` is a bare field met by `1`; nothing on `main` bounds it; the blueprint's Layer 10 closed form is a different object with no bridge stated |
| 2 | `Seam.bus` versus the table sumcheck; the bus phase's slot | CONFIRMED (both) | completeness is universal over `relIn`; `twoPoints` is in the seam and unservable; `cubicClaim` forces `Σ err ≥ 1` on a degree-blind verifier; no tension with the bus phase, whose image is a strict subset |
| 3 | public-input check not load-bearing | CONFIRMED | `pooled` never reads the message; `rbr`'s proof never names `check`; `securityG` at the same seams and error |
| 4 | combined versus per-limb check | CONFIRMED | Rust `:753`, Python `:1400`, guest `:1684` check one equation; `|E|` pairs pass per `r`; the counterexample `r = (1+y)/(1+yg)` checked by hand |
| 5 | GKR degree, error, combiner | WEAKENED | wire (4 not 5), layer check (no `eq`) and missing normalized variant confirmed; `5/|E|` is loose, not wrong; exact round error `4/|E|`, tight; the extra combiner confirmed (`gkr.rs:369, 423`) |
| 6 | generic GKR not appendable; zerocheck conjunct | CONFIRMED | `append` needs equal oracle families; lifting admitted at both pins; the constraint clause must flip inside the last layer, where only `K₂` speaks |
| 7 | Flock 8.1–8.4 | CONFIRMED | Flock reads no claim and the limbs are opened; `limbColumns` circular; `aux` opaque; `r_eq = 1` is the Rust prover's defect, no verifier inverts a challenge-dependent value |
| 8 | T4 sketches; not `Ensemble.toM3` | CONFIRMED | `constraintSoundness` needs `hwf` and the JUMP sentinel is a proved counterexample; `κ = 32` is a valid execution the verifiers reject; the trap is `Balanced` on `committed` coordinates, already avoided by decision 8 but not by the text |
| 9 | `Admissible ≠ Caps` | CONFIRMED | `Caps` has no rate and no `μ` window by its own docstring; the verifiers reject both; the three blueprint statements cannot hold together |
| 10 | Layer 1 reader; `leanIsaInstance_fits` | WEAKENED | facts confirmed; the blueprint names the strided reader and assigns it (circularly); the lemma is twenty lines |
| 11 | status's caps finding | CONFIRMED | `build_layout` (`:856-864`) has all four caps and `log2_strict` the power of two |

## Not verified, and what would verify it

- No Lean was run. The probes relied on (`P4Junk`, `SeamBusShape`, `SeamBusMember`,
  `ProbeAnyCheck`, `Probe1NoCheck`, `KnownColumn`, `StridedProbe`) have recorded outputs at the
  old pins; whether they elaborate at the new pins is unknown. `KnownColumn` needs `K.ofBits 2`
  at the new pin (its `New` variant exists). What would verify: a rebuild and one run each.
- Finding 7 (8.4): the propagation into the lincheck's terminal identity is derived by reading
  `zerocheck.rs:116-123`, `transcript.rs:289-302` and `lincheck.rs:1080-1100`, not executed. A
  unit test calling `send_round` with `r_eq = F192::ONE` and `G(0) ≠ 0` would settle it.
- Finding 9: the numeric claim that `piopError_le` fails at the caps without the window is
  `gt-bus.md` D.4's and was not re-derived here.
- Finding 8: the Rust verifier's acceptance of a proof for the JUMP-sentinel program is the
  earlier faithfulness review's finding (`docs/reviews/leanvm-faithfulness-review.md:74`,
  leanISA F6); I confirmed only that no verifier checks the sentinel and that the Lean test is
  proved.
