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
