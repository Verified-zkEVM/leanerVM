# ArkLib landscape: what upstream implements, what is pending, what stays leanerVM's

Task `arklib-landscape` of the blueprint review. Written 2026-09-30. Sources and pins are named in
every section; the two ArkLib revisions are the OLD pin `dca90385` ("feat(module-system): migrate
to modules (#897)", 2026-09-09) and the NEW pin `7653a901` ("feat(sumcheck): compute honest
messages from CompPoly polynomials (#1243)", 2026-09-26). `origin/main` of `Verified-zkEVM/ArkLib`
was fetched on 2026-09-30 and its head IS the new pin (`git rev-list --count 7653a901..origin/main`
= 0; 347 commits separate the old pin from it). So "landed beyond the new pin" is empty today, and
everything not at the new pin lives in an open pull request or nowhere.

(Sections are appended as they are finished; a section that is missing was not reached.)

## 0. Summary

_(written last)_

## 1. Method and sources

- ArkLib history: the sibling checkout `/home/scaraven/Documents/Verified-zkEVM/ArkLib` after
  `git fetch origin` (2026-09-30). Files at a revision were read with `git show <rev>:<path>`;
  nothing was checked out. The heads of pull requests that live on forks were fetched into
  remote-tracking refs (`git fetch origin refs/pull/<n>/head:refs/remotes/origin/pr/<n>`), which
  moves no working tree.
- Pull requests and issues: `gh pr list/view`, `gh issue list/view`, read-only. Every open
  pull request named below was read in full (description, file list, reviews, last comments);
  every merged pull request since the old pin whose title or files touch a component was read
  (description and file list). Quotations from descriptions are verbatim.
- Proof status: ArkLib's committed allow-list of admitted declarations
  `scripts/axiom_baseline.json` at each pin (291 entries at `dca90385`, 286 at `7653a901`; the
  lib-arklib dossier, section B.3, explains why absence from the list means "no `sorryAx`"),
  cross-checked by `grep -w sorry` on the files. No Lean was run for this task.
- What the blueprint needs: `docs/roadmap/protocol-blueprint.md` at `b435631` (cited as
  `bp:<line>`), `docs/roadmap/protocol-status.md` at `b435631` (`status:<line>`), and the
  sibling dossiers `register.md`, `lib-arklib.md`, `gt-opening-compile.md`, `obligations.md`
  (their section numbers are cited).

Two facts hold throughout and are not repeated per component:

1. **Between the pins no admitted theorem of the composition layer, the implications, context
   lifting, Fiat–Shamir, the classical sumcheck, ring switching, FRI, STIR or Binius was proved.**
   The two baselines differ by exactly six names: five `ArkLib.Lattices.CyclotomicModulus.*`
   entries removed and `LinearTransformations.isMCAGenerator_of_isMDSGenerator` replaced by the
   root-namespace `isMCAGenerator_of_isMDSGenerator` (pull request #902). Every other entry
   the blueprint's ledger names (`Verifier.append_rbrKnowledgeSoundness`,
   `Verifier.seqCompose_rbrKnowledgeSoundness`, `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness`,
   `Verifier.rbrSoundness_implies_soundness`, every `liftContext_*`, `fiatShamir_completeness`,
   `Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundness`,
   `Sumcheck.Spec.reduction_perfectCompleteness`, `CodingTheory.rs_mcaError_le_in_johnson_range`,
   `RingSwitching.*`, `Binius.*`, `Fri.*`, `StirIOP.*`) is in both baselines.
2. **The new files under `ArkLib/Interaction/` (28 files) and `ArkLib/ProofSystem/Sumcheck/Interaction/`
   (22 files) plus `Sumcheck/Impl/{Projection,Representation}.lean` contain no `sorry`** (`git grep -w
   sorry` at `7653a901`: zero files in each tree) and add no baseline entry; `docs/design/00-current-status.md`
   at `7653a901` says the same ("No declaration under `ArkLib/Interaction/` or
   `ArkLib/ProofSystem/Sumcheck/Interaction/` uses `sorry`"), and the merged pull requests
   #1214, #1242, #1243 each report "only `propext`, `Classical.choice`, and `Quot.sound`" for
   their theorems. I did not re-run `#print axioms`; the three sources agree.

## 2. Component 1: the sumcheck

### 2.a At the old pin `dca90385`

`ArkLib/ProofSystem/Sumcheck/` had seven files: `Domain.lean`, `Impl/Basic.lean`,
`Spec/General.lean`, `Spec/SingleRound.lean`, `Structured.lean`, `Structured/Prismalinear.lean`,
`Structured/SingleRound.lean`. `ArkLib/Interaction/` had seven files (the typed core) and no
sumcheck on it.

**The classical specification** (`Spec/`), stated on the legacy `OracleReduction` framework:

- `Sumcheck.Spec.StatementRound R n i` (`Spec/SingleRound.lean:130-133` at both pins): a target
  and the challenges so far. `Sumcheck.Spec.OracleStatement R n deg := fun _ : Unit ↦ R⦃≤ deg⦄[X Fin n]`
  (`:141`), one Mathlib multivariate polynomial of individual degree at most `deg` with the
  evaluation oracle interface. `relationRound` (`:144-147`): the running sum over the domain
  `D : Fin m ↪ R` equals the target.
- The single round `Sumcheck.Spec.SingleRound.Simple.{prover,verifier,oracleVerifier,reduction,oracleReduction}`
  (`:365-448`), the round-`i` versions obtained by context lifting (`:800-830`), and the full
  protocol `Sumcheck.Spec.{pSpec,verifier,oracleVerifier,reduction,oracleReduction}`
  (`Spec/General.lean:129-195`) as `seqCompose` of the rounds.
- Theorems: `Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness` (`:531`, proved in the
  file, no `sorry`), `Simple.verifier_rbrKnowledgeSoundness` and
  `Simple.oracleVerifier_rbrKnowledgeSoundness` (`:570-579`, both `sorry`),
  `Sumcheck.Spec.reduction_perfectCompleteness` (`General.lean:211`, proved from
  `seqCompose_perfectCompleteness_of_guarded_verifiers` and the single-round completeness,
  but its round-`i` leaf `SingleRound.reduction_perfectCompleteness` goes through the admitted
  `Reduction.liftContext_perfectCompleteness`, so the baseline lists it),
  `Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` (`General.lean:223`, from the admitted
  `OracleVerifier.seqCompose_rbrKnowledgeSoundness` and the admitted leaf; in the baseline).

**A defect of the legacy verifier, found upstream after the pin.** The `Simple.verifier`
computes its next target from the *input* polynomial, not the sent one:

`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:391-397` (`7653a901`; identical at `dca90385`):

```lean
def verifier : Verifier oSpec (StmtIn R × (∀ i, OStmtIn R deg i))
    (StmtOut R × (∀ i, OStmtOut R deg i)) (pSpec R deg) where
  verify := fun ⟨target, oStmt⟩ transcript => do
    letI polyLE := transcript 0
    guard (∑ x ∈ (univ.map D), polyLE.val.eval x = target)
    letI chal := transcript 1
    pure ⟨⟨(oStmt ()).val.eval chal, chal⟩, fun _ => oStmt ()⟩
```

and `Simple.oracleVerifier` (`:423-436`) queries `[OStmtIn R deg]ₒ` at the challenge for
`newTarget`. Issue #1, comment of 2026-09-27 (quangvdao, "source inspection at
`c8f2353d3`, independently confirmed"): "`Sumcheck.Spec.SingleRound.Simple.verifier` checks
the prover message's sum but sets `newTarget` to the original input polynomial's evaluation at
the challenge. … Consequently, over F₅, with degree bound zero, domain `{0}`, input polynomial
`p = 0`, claimed sum `s = 1`, and prover message `q = 1`, the input relation is false and the
sum check passes." Since the output statement `(p(r), r)` always satisfies `outputRelation`
(`:354`: `(oStmt ()).1.eval chal = newTarget`), a false input claim is turned into an accepted,
true output claim with probability one, and the admitted
`Simple.verifier_rbrKnowledgeSoundness` at error `deg/|R| = 0` cannot hold (paper reasoning
on my side; the upstream comment and the regression test of #1244,
`ArkLibTest/ProofSystem/Sumcheck/LegacyVerifier.lean`, "the sum check passes, but the output
relation remains false for every challenge", establish the defect). Pull request #1244 (open,
2026-09-27, mergeable, no review) changes the line to `polyLE.val.eval chal` and the oracle
verifier to query `[(pSpec R deg).Message]ₒ`. The round-`i` verifier (`:800`) is
`Simple.verifier` under `liftContext` (#1244's `verifier_eq_unfolded` unfolds exactly that),
so the whole classical protocol inherits the defect at both pins.

**The structured (witness-mode) sumcheck** (`Structured.lean`, `Structured/Prismalinear.lean`,
`Structured/SingleRound.lean`; no `sorry`) is the degree-2 `H = m · t` sumcheck of Binius
Basefold and ring switching, where `t` is a committed multilinear and `m` a context-dependent
multilinear multiplier (`Structured.lean:11-25`). It supplies round-polynomial computation and
degree bookkeeping (`computeRoundPoly`, `projectToNextSumcheckPoly`, `getSumcheckRoundPoly`,
`roundOracleReduction`, `roundKnowledgeError := d/|L|` as a definition) and **no security
theorem** in these files; its docstring says "the two modes carry independent proofs" and the
refinement to the canonical mode "is left for follow-up work".

### 2.b At the new pin `7653a901`

The classical `Spec/` is unchanged except for the `Simple` leaves' proof bodies
(`Spec/SingleRound.lean`: 211 lines changed, no statement changed; 14 lines still contain
`sorry`) and `Domain.lean` (3 lines). What is new is **the typed ("native") sumcheck**, 22
files under `Sumcheck/Interaction/` and two under `Impl/`, built between 2026-09-12 (#872) and
2026-09-27 (#1243). It is stated on the typed `Interaction` framework, not on `OracleReduction`.
The objects, from scratch:

- An `Interaction.Oracle.Protocol` is a typed tree of moves; `.oracleWith M interface rest`
  is "the prover sends a message of type `M` readable only through `interface : OracleInterface M`,
  then `rest`"; `.public .receiver T k` is "the verifier sends a public value of type `T`, then
  `k value`". A `Prover.Strategy` / `Verifier.Strategy` is a monadic program over such a tree.
  `VirtualOracle` (`Interaction/Oracle/Virtual.lean`) implements an oracle by a program over
  earlier oracles; a `ClosedClaim` (`Oracle/Claim.lean`) is a statement plus the *observable
  answers* of its oracles, so relations see answers, never representations.
- The protocol (`Sumcheck/Interaction/Protocol.lean:41-46`): for `count` rounds, the prover
  sends a `Message` (a univariate polynomial of degree at most `deg`, `SingleRound.lean:32`
  `abbrev Message := R⦃≤ deg⦄[X]`, read through evaluation queries), then the verifier sends
  `Option R`: `none` is a public abort, `some r` the challenge.
- The verifier (`Protocol.lean:98-121`): sums the *sent* polynomial over the declared domain
  list, compares with the target, samples `r`, queries the sent polynomial at `r` for the next
  target; at the end it exports the original oracle and the claim `(target, challenges)`. The
  output relation (`:137-138`): `claim.oracles ⟨(), claim.stmt.challenges⟩ = claim.stmt.target`,
  "a relation on the output, not a final verifier query".
- **Soundness** (`ProtocolSoundness.lean:201-215`, quoted in full):

```lean
theorem execute_soundness {m : ℕ} (D : Fin m ↪ F)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (prover : Prover.Strategy unifSpec (protocol F deg count).tree
      (protocol F deg count).roles (fun _ => Unit)) (p : Spec.OracleStatement F n deg ())
    (horiginal : originalOracle.eval impl =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (hfalse : ¬ closedRelation F n deg D ⟨start, by omega⟩ ⟨stmt, originalOracle.eval impl⟩) :
    Pr{let result ← (execute F n deg unifSpec ($ᵗ F) (Finset.univ.map D).toList
      count start finish A originalOracle stmt impl prover)}[
        result.map (outputRelation F n deg) = some True] ≤
      (count : ENNReal) * deg / Fintype.card F := by
```

  In words: for any finite domain `D`, any polynomial `p` of individual degree at most `deg`
  realizing the original oracle, any false running claim, and **any** native prover strategy
  (adaptive, with private memory and effects after each challenge), the probability that the
  run is not rejected and ends in a true evaluation claim is at most `count · deg / |F|`, for
  uniform challenges. This is **plain soundness** (a bound on the whole run), not round-by-round,
  and it is stated for an oracle that *is* a polynomial: the witness is `Unit`, there is no
  extractor and no knowledge notion.
- **Completeness** (`ProtocolCompleteness.lean:36-49, 110-126`): `Native.honestProver` sends the
  projected round polynomial `Spec.SingleRound.projectedRoundPolynomial`;
  `execute_perfectCompleteness` gives probability one for any `ProbComp` challenge program from a
  true claim.
- **The computable layer** (#1242, #1243): `Impl/Representation.lean:25` `Message := {p :
  CompPoly.CPolynomial R // p.degree ≤ deg}` with Horner evaluation (`:28`);
  `Computable.protocol/verifier/execute` are the same `Native.Core` definitions specialized
  (`Computable.lean:34-42`); `Computable.execute_eq_native` (`:54`), `Computable.execute_soundness`
  (`ComputableSoundness.lean:31-47`, same bound, `[BEq F] [LawfulBEq F]` added);
  `Impl/Projection.lean:187` `projectedMessage` computes the honest message from a
  `CMvPolynomial (n+1) R` by CompPoly's variable split and finite sums (`#1243`: "a general
  finite-enumeration prover. It does not claim a linear-time or streaming multilinear
  algorithm"); `Computable.honestProver` and `Computable.execute_perfectCompleteness`
  (`ComputableCompleteness.lean:37, 116`).
- **The bridge to the legacy relations** (`Legacy.lean`, #874): `legacy_input_iff` (`:42`),
  `legacy_output_iff` (`:34`), and `legacy_honest_verifier_correspondence` (`:108`), which is
  "deliberately honest-only. The legacy verifier reads the input polynomial for its next target,
  while the typed verifier reads the actually sent polynomial" (#874's description) — the
  defect above, seen from the typed side.
- Composition (`Composition.lean`, #1235): `execute_eq_appendExported` (`:337`) identifies the
  native execution with "first round, then the remaining rounds" through the typed framework's
  `Verifier.appendExported`, and the soundness proof now goes through the generic
  `executeStrategies_appendExported_soundness_ae` (`Interaction/Oracle/CompositionSoundness.lean:302`).

### 2.c On `origin/main` beyond the new pin

Nothing: `origin/main` is `7653a901`.

### 2.d Open pull requests

| Number | Title, author, state (2026-09-30) | What it supplies | Fit with the spine | Closeness |
| --- | --- | --- | --- | --- |
| #1128 | feat(sumcheck): expose honest round polynomial identities; eliasjudin; open since 2026-09-24, mergeable, no review, 3 files (`Spec/RoundPolynomial.lean` + test) | "The honest projected round polynomial now has a direct polynomial-substitution identity and a degree bound at the selected coordinate … over commutative semirings"; "Extracted from leanth #16" | algebra on the classical `Spec` round polynomial; no protocol shape | small, unreviewed; unknown |
| #1129 | test(sumcheck): cover collision, degree and challenge-order controls; eliasjudin; open since 2026-09-24, mergeable, no review, 1 test file | Boolean-domain controls on the typed one-round executor ("exact repair probability `1/5`… a challenge-first adaptive message that succeeds with probability one") | tests only | small; unknown |
| #1244 | fix(sumcheck): evaluate the sent polynomial in legacy rounds; eliasjudin; open since 2026-09-27, mergeable, no review | the repair of the defect of 2.a, with the F₅ regression | legacy `OracleReduction`; makes the admitted leaf statable | small; requested by the maintainer's own comment; unknown |
| #1241 | docs: refresh project roadmap and Sumcheck priorities; quangvdao; open since 2026-09-27 | "It makes completing native Sumcheck the next priority before FRI migration: CompPoly-backed execution, round-by-round soundness, knowledge soundness, and their combination." | docs | maintainer's; likely |
| #503 | feat(LogUp); jCabala; open since 2026-05-13, CHANGES_REQUESTED, CONFLICTING; touches `Spec/General.lean`, `Spec/SingleRound.lean` | a LogUp reduction on the classical sumcheck with `sorry` security proofs | not the leanVM bus (a product, not a logarithmic derivative) | stalled |

**No open pull request supplies** round-by-round or knowledge soundness of the typed sumcheck,
a virtual (formula-of-tables) summand, an eq-weighted or back-loaded variant, a normalized
(Gruen) round, or a dropped-coefficient encoding. ArkLib's roadmap (`docs/design/05-roadmap.md`
at `7653a901`, "Complete native Sumcheck first", items 3–5) lists as *active*: "Native
round-by-round security. Define the security condition on actual execution prefixes,
instantiate it with Sumcheck's proved per-challenge bound…"; "Knowledge and extraction.
Define native knowledge and round-by-round knowledge games with explicit extractor access and
timing. Current oracle Sumcheck has a `Unit` witness…"; "Efficient implementations and legacy
migration. Optimize the Boolean multilinear case using CompPoly evaluation tables…". No pull
request for any of the three existed on 2026-09-30.

### 2.e What the blueprint plans locally that exists upstream

The blueprint's Layer 4 (`bp:869-904`) plans `Virtual`, `sumcheck : OracleReduction []ₒ …`,
`sumcheck_perfectCompleteness`, `sumcheck_rbrKnowledgeSoundness … (fun _ ↦ d/|F|)`; its
ledger row A1 (`bp:258`) says "Layer 4 proves the single-round bound for its own sumcheck shape
and contributes it as the missing leaf"; hole G1's "Existing work" column names "ArkLib
`main`'s `Sumcheck/Interaction/`" and hole G2 names "`Interaction/Soundness.lean`" (`bp:598-599`).

What exists at the new pin and could be consumed at the pin bump, through an adaptor:

- the one-polynomial sumcheck with **plain** soundness `count·deg/|F|` for every native prover
  (`Native.execute_soundness`, `Computable.execute_soundness`) and perfect completeness with a
  computable honest prover (`Computable.execute_perfectCompleteness`), on any finite domain and
  for any individual degree bound. The blueprint's `sumcheck_perfectCompleteness` for a summand
  that *is* one polynomial is covered; its per-round *knowledge* bound is not (2.f).
- the honest round polynomial as a definition (`Spec.SingleRound.projectedRoundPolynomial`,
  `Impl.Computable.projectedRoundPolynomial`/`projectedMessage`) with proved degree bounds and
  the sum identity — what leanerVM's staged pull request #42 ("connect honest sumcheck
  polynomials to ArkLib", `HonestSumcheckUpstream.lean`, now `CONFLICTING`) re-derives against
  the old pin's `Spec` projection.

The adaptor a consumer would need (not written anywhere): a leanerVM `OracleReduction` whose
verifier *is* a run of `Native.Core.verifier` (or the computable one) with the challenges read
from the `ProtocolSpec` transcript, plus a lemma that the `OracleReduction`'s acceptance
coincides with the native `execute`'s non-rejection — a correspondence of the kind #874 proves
for one honest round (`legacy_honest_verifier_correspondence`) and #1244 sketches
(`verifier_eq_unfolded`). Even with it, the plain bound does not yield the spine's
`rbrKnowledgeSoundnessWorstCaseWith` (component 4): the per-round leaf must still be proved on
the legacy side, or the typed framework must first define round-by-round knowledge (its
roadmap items 3–4).

### 2.f What remains leanerVM's

Nothing upstream, merged or open, covers leanVM's four sumcheck shapes; each is a local
definition with its own proof unless ArkLib's items 3–5 are done *and* generalized:

1. **the virtual summand** (a formula of degree `d` in `m` oracle tables, `bp:880-884`): the
   typed sumcheck takes one polynomial oracle. Its `originalOracle` is a `VirtualOracle`, so a
   formula over table oracles can be *expressed* (the framework's substitution layer, #869);
   but the theorem's `horiginal` requires that virtual oracle to be realized by one polynomial
   `p` of individual degree at most `deg`, and the final relation is `p(r) = target`, not "the
   prover sends the table values at `r` and the verifier evaluates the formula". The last
   message and the `(Fin m → F)` output of `bp:889` are a further reduction, ours.
2. **the eq-weighted, back-loaded variant over tables of different heights** (`bp:898-902`;
   `gt-table-pub` finding on `Seam.bus`, register row *the bus seam admits statements* (`R2`)):
   absent upstream; the structured sumcheck's `H = m·t` is the nearest shape but degree 2 only,
   without security theorems.
3. **the normalized (Gruen) round the GKR runs** (register row *the GKR layer sumcheck is the
   normalized variant* (`R7`): "Each deployed GKR round sends a degree-4 cofactor … the constant
   coefficient derived through the equality factor"): absent upstream; the typed verifier sums
   the sent polynomial over the domain, which is a different verifier.
4. **the round-polynomial encoding** (three of four coefficients sent, `c_1` or `c_0` derived;
   `obligations` node 2.5.1.3.3): absent upstream; #1128 gives only honest identities on the
   full polynomial.

### 2.g Risks

- The classical leaf the ledger targets is **false as stated** at both pins (2.a) until #1244
  merges; a local proof "contributed as the missing leaf" would have to target the repaired
  statement, and the repair is on a framework upstream calls legacy (component 4).
- ArkLib's declared direction is to prove round-by-round and knowledge notions on the *typed*
  framework ("Repair or migrate legacy Sumcheck claims with correspondence and axiom checks;
  do not treat the native result as silently proving those old declarations",
  `05-roadmap.md` item 5). A leanerVM proof on the legacy `Spec` may never be accepted
  upstream; a leanerVM proof on the typed framework cannot feed the spine's master theorems
  until that framework has knowledge soundness (component 9).

