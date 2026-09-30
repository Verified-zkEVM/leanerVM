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

**What was examined.** For nine generic components of the proof system (the sumcheck, batching,
fingerprints/grand product/GKR/stacking, composition and the framework question, oracle
interfaces, Fiat–Shamir and BCS, WHIR/FRI/Basefold and the coding theory, ring switching, the
typed Interaction framework), what ArkLib implements at the old pin `dca90385` and the new pin
`7653a901`, what landed since (nothing: `origin/main` is the new pin), what its open pull
requests would supply, and what leanerVM must build itself. Sources: the two revisions read
with `git show`, both axiom baselines, every relevant open and merged pull request and issue
read with `gh`, the blueprint and status at `b435631`, and four sibling dossiers.

**The three lists.**

*Implemented and usable at the new pin (with the adaptor it needs).*
(1) The typed one-polynomial sumcheck (#872–#892, #1214, #1216, #1235, #1242, #1243): a
computable verifier and honest prover on CompPoly data, perfect completeness, and **plain**
soundness `count·deg/|F|` against every native prover — no round-by-round notion, no extractor,
`Unit` witness, on the typed framework; consumable for the plain case through an
`OracleReduction`-to-native correspondence lemma that nobody has written. (2) The typed
framework's plain composition soundness (#1218, #1231–#1238), not consumable by the spine
(no knowledge notion). (3) Schwartz–Zippel restated on VCVio's sampler
(`prob_eval_zero_le_div`, `prob_eval_zero_univ_le_div`), consumable directly. (4) A **proved**
Johnson-range affine-line mutual-correlated-agreement bound over any finite field
(`ReedSolomon.mcaError_affineLine_johnson_le`, from the completed #907 port), with a constant
different from the admitted [BCHKS25] one Annex B cites; consumable if its constant meets the
parameters (unverified). (5) The pairwise Johnson list bound (#910), interleaving and folding
lemmas (building blocks, fit unverified). (6) In VCVio at `a4232d08`: Merkle trees with proved
completeness and single-opening random-oracle extractability (ArkLib #4 closed, moved to VCVio
#571). (7) The ring-switching packing profile structure with its coordinates repaired (#896);
its protocol's security leaves all admitted.

*Pending upstream, with the pull request.* #1244 repairs the legacy sumcheck verifier
(mergeable, unreviewed); #1245 proves round-by-round ⇒ plain soundness for a stateless shared
oracle and shows it false otherwise (mergeable, unreviewed); #1128/#1129 honest sumcheck
identities and tests (small); #926 lift-context definitions (draft, CI red); #615 the guarded
knowledge append, its n-ary form and `gammaPowers` (conflicting, pre-module, unreviewed since
July); #818 circuit GKR completeness (stalled, wrong shape); #383 binary Basefold security and
#992 multiplicative FRI soundness (conflicting / unreviewed, both on the legacy framework);
#469/#848 duplex-sponge Fiat–Shamir (changes requested, conflicting, not leanVM's chain);
#1251 the next VCVio repin (draft; changes probability notation again). **None supplies
round-by-round knowledge soundness of any sumcheck, a virtual or eq-weighted or normalized
sumcheck, batching as a reduction, a grand product, a product-tree GKR, WHIR, a BCS transform,
or an inner-product oracle.**

*Ours to build.* The four leanVM sumcheck shapes (virtual summand with the final table-value
message; eq-weighted back-loaded over tables of different heights; the normalized Gruen round of
the GKR; the dropped-coefficient encoding) with their round-by-round knowledge leaves; the
batching component (the opening phase under the inner-product interface); the fingerprint,
product lemma and collision bound; the radix-4 GKR with its binary first layer; the
inner-product oracle interface; WHIR over binary Reed–Solomon codes with grinding; the
Merkle/BLAKE2s instantiation over VCVio's trees; the BLAKE2s chain as a challenge oracle, the
grinding checks, the proof object; the three compiled-security interfaces stated for leanVM's
construction and the list-binding compilation; the `GF(2) → K` ring-switching profile and
Annex A's protocol (issue #3); the plain-knowledge corollary in the stateless form.

**The decisions the owner must take.** (1) *Framework*: stay on `OracleReduction` — the only
framework with knowledge soundness — and keep owning the composition; write a ledger row saying
so and naming ArkLib's roadmap items 3–4 as the trigger to revisit. (2) *Sumcheck*: consume the
typed sumcheck only for the plain one-polynomial case through an adaptor, and write the leanVM
variants and every knowledge leaf locally; drop the plan to "contribute the leaf" upstream
(the leaf is false as stated until #1244, and upstream's direction is the typed framework).
(3) *The inner-product oracle*: define it locally; nothing upstream has or plans it.

**Findings by severity.** Major: the classical sumcheck leaf the ledger targets is false as
stated at both pins (12.1); holes G1/G2 name upstream sources of the wrong kind (12.2); ledger
A8 and the status's coding-theory row are stale in both directions — the watched port is
complete without proving the cited theorem, a proved substitute exists, and the capacity
results exclude characteristic two (12.3). Minor: hole K2 cites a closed issue and misses
VCVio's proved Merkle library (12.4); the batching source is a lemma in a pull request that
will not merge as is (12.5); the deletion condition of the port and the plain corollary should
be restated on #1245's evidence (12.6); the status's upstream watch is out of date on eight
rows (12.8). Note: the Schwartz–Zippel citation (12.7). No finding contradicts the brief; the
brief's §7 fact that the generic components are "specified in the blueprint and not built"
stands, with the qualification that a plain one-polynomial sumcheck is now built upstream.

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

## 3. Component 2: batching by the powers of one challenge

### 3.a–b At both pins

Nothing. `git grep BatchingStrategy` at `7653a901` finds no declaration; the only random
linear combination in the library is inside the ring-switching batching phase
(`RingSwitching/Packing/BatchingPhase.lean`, the `κ`-coordinate batching vector of [DP24], whose
security theorem `RingSwitching.BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness` is in
the baseline at both pins) and, as a component, `Component/SendChallenge.lean` (a verifier
sends `Fin ℓ → C`; it carries a `foldBlockStructure : CWSSStructure`, a coordinate-wise
special-soundness structure, and no round-by-round theorem).

### 3.c On `origin/main`

Nothing beyond the pin.

### 3.d Open pull requests

`#615` (feat(ring-switching): add reusable packing proofs and protocol integrations;
alexanderlhicks; open since 2026-07-07, last updated 2026-09-08, `mergeable: CONFLICTING`,
`reviewDecision: REVIEW_REQUIRED`, 100 files, pre-module-system) carries the object the
blueprint's hole G3 names, `BatchingStrategy.gammaPowers`
(`ArkLib/ProofSystem/RingSwitching/Packing/Batching.lean:88-91` at `ca7a2577`):

```lean
structure BatchingStrategy (P : Type) [CommRing P] (W : Type) [Fintype W] where
  Challenge : Type
  [ftC : Fintype Challenge]
  [neC : Nonempty Challenge]
  weight : Challenge → W → P
  error : ℝ≥0
  separates : ∀ s s' : W → P, s ≠ s' →
    Pr_{ let c ←$ᵖ Challenge }[∑ u, weight c u * s u = ∑ u, weight c u * s' u] ≤
      (error : ℝ≥0∞)
```

```lean
def gammaPowers (e : ℕ) : BatchingStrategy P (Fin e) where
  Challenge := P
  weight γ u := γ ^ (u : ℕ)
  error := ((e - 1 : ℕ) : ℝ≥0) / (Fintype.card P : ℝ≥0)
```

It is **not** an `OracleReduction`: it is a separation lemma ("distinct value families coincide
after weighting with probability at most `error`") in the `Pr_{…}` probability notation that
ArkLib retired in #913 (2026-09-21; #615 predates that pull request and the module system),
with `separates_map` (transport along an injective ring hom), `singleton` and
`reindex`. The pull request's own summary of its scope: "Generic pipelines use guarded
composition with explicit extractors, knowledge states and per-prefix bounds. Challenge
errors sum to `batching error + m * (2/|C|)`." Closeness to merging: **remote**. It conflicts
with `main`, predates the module migration (#897, the old pin's own commit) and the probability
migration (#903, #913), has no review, and its last comment is the bot's timing report of
2026-09-08; issue #893 (2026-09-29) lists it as a "reuse candidate" whose "Flock PCS/list/OOD
integration and full FRI-Binius closure remain outside the proved contracts".

### 3.e What the blueprint plans locally that exists upstream

Hole G3 (`bp:600`: "`batchClaims`, `(k − 1)/|F|`", existing work "#43, ArkLib #615's
`gammaPowers`") plans a `batchClaims : OracleReduction …` with `batchClaims_rbrKnowledgeSoundness`
(`bp:907-911`). Nothing at the pin; #615's `gammaPowers` is the scalar separation lemma only.
leanerVM's staged pull request #43 ("pair power-batched weight tables with columns", mergeable,
open since 2026-09-24) says of itself: "[ArkLib #615] contains the scalar strategy but remains
unavailable at leanerVM's pinned revision. This contributes the table pairing and retains the
necessary pinned scalar compatibility; it does not establish batching knowledge soundness."

### 3.f What remains leanerVM's

All of it: the separation lemma (a twenty-line Schwartz–Zippel on a univariate of degree `< k`,
which `gammaPowers.separates` shows), the `OracleReduction` component with its knowledge state
function ("some claim is false" before the challenge, "the batched claim is false" after) and
the worst-case round-by-round theorem. Under the inner-product interface of register row *the
opening phase runs a sumcheck leanVM does not run* (`R18`), this component *is* the opening
phase (gt-opening-compile A.5, alternative (ii)), so it is load-bearing.

### 3.g Risks

Consuming #615 for this would tie the opening phase to a hundred-file pull request that may
never merge, for a lemma of twenty lines. The `To*` rule of the repository (memory:
generic code goes to `ToArkLib/` and is offered upstream) fits: write it, offer it as its own
small pull request, and cite #615 for the idea.

## 4. Component 3: fingerprints, the multiset product, the grand product, GKR, stacking

### 4.a–c At both pins and on `origin/main`

- **Fingerprints, multiset product lemma, grand product**: absent. `git grep -i` for
  `grandProduct`, `fingerprint`, `multiset … prod` at `7653a901` hits only coding-theory
  proofs using Mathlib's `Multiset.prod` (`ListDecodability/Bounds/KKH26.lean`,
  `BCIKS20/ListDecoding/Extraction.lean`) and nothing protocol-level. ArkLib issue #901
  ("feat(data): formalize multiset product injectivity and collision bounds", eliasjudin,
  open since 2026-09-18, last update 2026-09-24) is the request: "symbolic multilinear
  fingerprints; an independent formal product challenge; injectivity of the multiset product
  polynomial over an integral domain, preserving natural multiplicities in every
  characteristic; and a Schwartz-Zippel collision bound when BOTH multisets are fixed before a
  uniform joint challenge. For sixteen-coordinate tuples the joint degree bound is four per
  factor, yielding `4 * cap / |F|`." Its comment (2026-09-24) says the port is staged as
  leanerVM #39 ("symbolic tuple fingerprints", open, mergeable, `LeanerVM/Protocol/Generic/Fingerprint.lean`)
  with a dependent "multiset-product comparison" branch, and "Excluded: GKR, bus-phase assembly
  and conditional freshness for a recycled bus/table challenge." No ArkLib pull request exists.
- **GKR**: absent at both pins (no `ArkLib/ProofSystem/GKR/`).
- **Stacking** (blocks of different sizes read out of one table at extension-field points):
  absent. ArkLib issue #900 ("feat(data): formalize extension-ring block readout", open since
  2026-09-18) scopes "`Blocks.map`, naturality of `stackAt` under arbitrary ring
  homomorphisms …, mixed-ring selection with the fit premise retained, and readout/weighted
  claims for arbitrary columns", says "CompPoly already owns `eval₂Mle` and the underlying
  multilinear table evaluation; this work should reuse that API", and its comment points to
  leanerVM #38, #40, #41 (all merged into leanerVM's Layer 1 on 2026-09-29 per the status). No
  ArkLib pull request exists; leanerVM's own `ToCompPoly/{Stacking,AmbientStacking,…}.lean` are
  the only implementation.
- The building blocks that do exist: `MvPolynomial.MLE`, `eqPolynomial`, `eqTilde`,
  `eqTilde_append`, `MLE_eq_zero_iff` (`Data/MvPolynomial/Multilinear.lean`, proved, both pins;
  lib-arklib B.2), and `schwartz_zippel_counting` (root namespace) with the `PMF`-stated
  `prob_eval_zero_le_div` at the old pin — at the new pin the PMF surface is retired (#913:
  "Coding-theory and protocol events now use VCVio's native measures, `ProbComp`, and
  `Pr{let x ← $ᵗ S}[...]` throughout"; the blueprint's `bp:250` names are stale at both pins,
  lib-arklib G.6).

### 4.d Open pull requests

`#818` (feat(gkr): formalize the GKR protocol with perfect completeness; dolijan; open since
2026-08-31, last update 2026-09-04, `CONFLICTING`, no formal review; head `4dc5142f`, 9 files:
`ProofSystem/GKR/{Circuit,SingleRound,SumcheckAux,OracleLayer,General}.lean`,
`Data/MvPolynomial/LineRestriction.lean`, the baseline). Its description: "Prove the perfect
completeness of GKR. Inherits sorryies from `Reduction.append_completeness`,
`Reduction.liftContext_completeness` and `Prover.append_run` … We follow Thaler's line reduction
for two claim merging step … Soundness is not proven." What it defines (read at `4dc5142f`):
`GKR.Circuit k d` with `addPred`/`mulPred` gates (`Circuit.lean:47, 152, 167`), the wiring
identity `layerMLE_eq_wiringPoly` (`SingleRound.lean:317`), the round polynomial of individual
degree bound (`degreeOf_roundPoly_le`, `:398`), the inner sumcheck as
`innerReduction : … Reduction` built on `Sumcheck.Spec` (`:769`), the per-layer
`Oracle.oracleLayer` and the chain `Oracle.oracleGkr : OracleReduction …` with
`oracleGkr_perfectCompleteness` (`OracleLayer.lean:689, 764, 778`). "Nothing in `ArkLib/ProofSystem/GKR/` contains a `sorry` of its own" (`General.lean:46`), but every composed
theorem inherits `sorryAx` through the legacy composition. Fit with leanVM: **none as a
protocol** — it is Thaler's arithmetic-circuit GKR (add/mul gates, radix 2, one line-reduction
combiner per layer), while leanVM's is a *product tree* of radix 4 with an odd binary first
layer, a fresh combiner after the roots and after every layer, two combination challenges per
layer and the normalized round (`gt-bus` A.4, D.4; register rows `R7`, `R9`). The maintainer's
review comment (2026-09-01) praises the algebra and asks for changes; the author replied on
2026-09-04 ("ready for another look") and nothing happened since. Closeness: **stalled**; and
its shape is classical `OracleReduction` on the admitted composition layer.

### 4.e What the blueprint plans locally that exists upstream

Layer 5 (`bp:918-948`: `fingerprint`, `sideProduct`, `sideProduct_poly_eq_iff`,
`sideProduct_collision`, `ProductTree`, `gkr`, `gkrError`, two theorems) and holes G4, G5, G6
(`bp:601-602`): nothing exists upstream; the status's "GKR: to open (ArkLib #818 is a different
protocol shape)" (`status:180`) is correct. The Layer 1 stacking lemmas are leanerVM's own and
are the *candidates* for #900, not consumers of it.

### 4.f What remains leanerVM's

Everything in this component: the fingerprint and side product with Lemma 5.2 and Theorem 5.1
(leanerVM #39 is the staged fingerprint half; the product-injectivity half is a branch, not a
pull request); the radix-4 batched GKR with its binary first layer and normalized rounds; and
the stacking (built). ArkLib #818 is a *pattern* for stating a layer as an `OracleReduction`
and for the line-restriction algebra (`Data/MvPolynomial/LineRestriction.lean`), which leanVM
does not use (it combines four children by two challenges, not a line).

### 4.g Risks

A GKR written on the legacy composition inherits `sorryAx` unless composed with leanerVM's own
knowledge append (component 4). #818 shows the cost: a 1,300-line single-round file plus a
970-line oracle layer for the *classical* circuit GKR with completeness only.

## 5. Component 4: composition, the implications, context lifting, and which framework

### 5.a At the old pin `dca90385`

- **Completeness composition**: proved. `Reduction.append_completeness_of_guarded_verifiers`
  (`Composition/Sequential/GuardedCompleteness.lean:161`), `OracleReduction.append_perfectCompleteness_of_guarded_verifiers`
  (`OracleCompleteness.lean:54-67`, the theorem the spine uses), the `n`-ary
  `seqCompose_completeness_of_guarded_verifiers` (`GuardedNary.lean:45`, `OracleCompleteness.lean:77`),
  and `Reduction.seqCompose_perfectCompleteness_of_pure` (`Completeness.lean:66`); errors add;
  the suffix must be complete from every deterministic shared-oracle state (lib-arklib E.2).
- **Round-by-round soundness composition** (no knowledge): proved for a pure first verifier,
  `Verifier.append_rbrSoundnessWorstCase_of_pure_first` (`Append/RoundByRound.lean:37`),
  `Verifier.StateFunction.append`, `Extractor.RoundByRound.append` (`Append/StateFunction.lean:292, 75`).
- **Knowledge-soundness composition**: admitted. `Append/Security.lean` holds four `sorry`:
  `Verifier.append_soundness`, `append_knowledgeSoundness`, `append_rbrSoundness`,
  `append_rbrKnowledgeSoundness`; the `OracleVerifier.*` and `seqCompose_*` forms inherit them
  (all in the baseline). The file's umbrella docstring calls them "legacy admitted soundness
  claims and their inherited wrappers" (`Composition/Sequential/Append.lean:34` at `7653a901`).
- **The implications**: `Verifier.rbrKnowledgeSoundness_implies_rbrSoundness`
  (`Security/Implications.lean:87`) proved; `rbrKnowledgeSoundness_implies_knowledgeSoundness`,
  `rbrSoundness_implies_soundness`, `knowledgeSoundness_implies_soundness`, the four `sr*`
  theorems admitted; round-by-round ⇒ state-restoration is commented out
  (`Implications.lean:215-224` at `7653a901`, with error `∑ i, rbrKnowledgeError i`).
- **Context lifting**: `Verifier.liftContext_*`, `OracleVerifier.liftContext_*`,
  `Reduction.liftContext_*`, `OracleReduction.liftContext_*` and the two definitions
  `Verifier.StateFunction.liftContext`, `Extractor.RoundByRound.liftContext` admitted
  (`LiftContext/Reduction.lean`, 10 `sorry`).
- **Guarded verifiers**: `Verifier.GuardedForm` (`CWSS/Guarded.lean:112-118`),
  `Verifier.GuardedForm.ofEmpty` (`NoAmbient.lean:46-55`) proved.

### 5.b At the new pin `7653a901`

Identical on every item above (fact 1 of section 1). The probability notation changed
(`Pr[· | ·]` → `Pr{let x ← ·}[·]`, #903/#913) with the same content (lib-arklib F.3). The
typed framework added *plain* composition soundness with no knowledge notion (component 9).

### 5.c On `origin/main`

Nothing beyond the pin.

### 5.d Open pull requests

- `#615` carries `ArkLib/OracleReduction/Composition/Sequential/Append/Knowledge.lean` (the file
  leanerVM ported as `ToArkLib/KnowledgeAppend.lean`; lib-arklib C.1 verified the port line by
  line against `ca7a2577`) and `KnowledgeNary.lean` (read at `ca7a2577`: `Verifier.KnowledgeSeqCompose.Witness`,
  `extractor`, `state`, `error`, and
  `seqCompose_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_verifiers` (`:128`),
  `seqCompose_rbrKnowledgeSoundnessWith_of_worstCase_of_guarded_verifiers` (`:157`): "Every
  nonempty step uses guarded append; the empty sequence uses the identity extractor and
  knowledge state"). Shape: exactly the spine's (`rbrKnowledgeSoundnessWorstCaseWith`, `GuardedForm`,
  `Extractor.RoundByRound.append`). State: as in 3.d — conflicting, pre-module, unreviewed for
  three months, on the legacy framework. Its `Append/Knowledge.lean` is a plain `import` file;
  the port had to be made a `module` (lib-arklib C.1 item 2).
- `#926` (feat(lift-context): close the structural obligations in `LiftContext/Reduction.lean`;
  Abraxas1010; **draft**, created 2026-09-21, mergeable): closes 4 of the 8 admitted declarations
  (the definitions `Extractor.RoundByRound.liftContext`, `Verifier.StateFunction.liftContext`
  and the two completeness transports), by adding a language-level class
  `Statement.Lens.IsComplete`; "The 4 that remain are exactly the `Verifier.*` soundness
  theorems, which are deliberately out of scope". Its finding: "`Verifier.StateFunction.liftContext`
  was **not provable as typed**"; the author moved it to draft on 2026-09-21 because "CI is red
  at v4.34" with four errors. Closeness: **unknown**, waiting on a maintainer's interface
  decision raised on #676.
- `#1245` (fix(security): qualify `rbrSoundness_implies_soundness` with `[Subsingleton σ]`,
  prove it, and add the counterexample; Calgooon; open since 2026-09-27, mergeable, no
  review): "`Verifier.rbrSoundness_implies_soundness` … has carried `by sorry` in every
  revision since at least January 2025. It is unprovable as stated: `StateFunction.toFun_full`
  quantifies the verifier's run from a fresh draw of `init`, while `Verifier.soundness`'s game
  runs the verifier from the oracle state the prover's queries leave behind." The pull request
  proves `Verifier.rbrSoundnessWith_implies_soundness_of_full` (with a full-transcript clause
  from every state) and `rbrSoundness_implies_soundness_proved` under `[Subsingleton σ]`, and
  exhibits the counterexample on a one-flag oracle. **Relevance to leanerVM**: the spine runs
  over `[]ₒ` with `σ := Unit` (a subsingleton), so the qualified form is exactly what the
  blueprint's "plain corollary" (`bp:261`, ledger A3) needs; the *knowledge* twin
  `rbrKnowledgeSoundness_implies_knowledgeSoundness` is not in this pull request and carries the
  same fresh-`init` defect (the lib-arklib probe `PlainReading` proved the transcript-level half
  locally in forty lines).
- `#383` touches `OracleReduction/Cast.lean` (a cast of reductions between equal statement
  types with `cast_rbrKnowledgeSoundness`, `:373, 492` at the pin, 2 `sorry` in the file at
  `7653a901`) — useful at the seams and for the list-binding compilation (obligations node
  2.1.2.3.3), but the pull request is `CHANGES_REQUESTED` and conflicting (component 8).

### 5.e What the blueprint plans locally that exists upstream

Ledger A2 (`bp:259`): the local port is still the only proved guarded-first knowledge append
(lib-arklib F.4). Ledger A3: the plain corollary — #1245 would supply the *soundness* half in
the stateless form; the knowledge half remains admitted and its statement has the same defect.
Ledger A4 (context lifting, "not consumed"): correct, and register row *Layer 5's generic GKR
cannot be appended in the bus phase* (`R10`) shows a GKR over leaf tables would consume it;
#926 does not touch the soundness theorems.

### 5.f What remains leanerVM's

The knowledge append (built, ported) and the `n`-ary form if ever needed (`KnowledgeNary.lean`
of #615 is the pattern, 170 lines); the plain-knowledge corollary in the stateless form (forty
lines by the lib-arklib probe plus a union bound); any "state functions indexed by a finite
set" union-bound lemma for the list-binding compilation (obligations 2.1.2.3.2).

### 5.g Risks

- **The pull request the blueprint waits for may never merge** (register row `R34`; lib-arklib
  G.3). Issue #676's refresh of 2026-09-29 says: "Keep this issue open until its remaining
  legacy claims are proved with correct assumptions or its consumers migrate with verified
  correspondence. Do not assume an unrestricted stateful composition statement is provable
  merely because its components are secure from the same fresh initialization." #1245's
  counterexample shows that at least one admitted legacy statement (`rbrSoundness_implies_soundness`)
  is false as stated; the same fresh-`init` shape appears in `append_rbrKnowledgeSoundness`
  (its second component is quantified from `init`, lib-arklib C.3). leanerVM's port avoids
  this by requiring both components at the same `init`/`impl` and works over `[]ₒ`, where the
  shared state is trivial.
- The framework question is settled by upstream's words: `AGENTS.md:30` "`ArkLib/OracleReduction/`
  - legacy IOR abstractions and security theory"; `docs/wiki/sequential-composition.md` is
  titled "Legacy sequential composition"; pull request #1240 (merged 2026-09-27) is titled
  "docs: explain legacy oracle reduction interfaces". New security work lands on
  `ArkLib/Interaction/`. But **only the legacy framework has knowledge soundness at all**
  (component 9), so the spine has no alternative today.

## 6. Component 5: the oracle interfaces

### 6.a–b At both pins

`ArkLib/OracleReduction/OracleInterface.lean` (unchanged in content between the pins) defines
the class and these instances (line numbers at `7653a901`): `instFunction` for `α → β`
(`:122`, a query is an argument), tensor and product interfaces (`:142-191`), `instPolynomial`
(`:263`), `instPolynomialDegreeLE : OracleInterface (R⦃≤ d⦄[X])` (`:270-273`, `Query := R`,
answer `eval point`), `instPolynomialDegreeLT` (`:277`), `instMvPolynomial` (`:283`,
`noncomputable`, `Query := σ → R`), `instMvPolynomialDegreeLE : OracleInterface (R⦃≤ d⦄[X σ])`
(`:290-293`, `noncomputable`), `instListVector`, `instVector` (`:311, :317`, index queries).

**Evaluation oracles for multilinears**: the Mathlib-side one is `instMvPolynomialDegreeLE` at
`d = 1`, noncomputable. A *computable* multilinear evaluation interface exists once, local to
Hachi: `Commitments/Functional/Hachi/Commitment.lean:67-72` (`7653a901`)

```lean
instance multilinearEvalOracleInterface {n : ℕ} :
    OracleInterface (CMlPolynomial (Rq 𝓜(q, α)) n) where
  Query := Vector (Rq 𝓜(q, α)) n
  toOC :=
    { spec := Vector (Rq 𝓜(q, α)) n →ₒ Rq 𝓜(q, α)
      impl := fun p => do return CMlPolynomial.eval (← read) p }
```

over the cyclotomic ring `Rq`, not generic. leanerVM's `evalOracle` (`Field.lean:102-113` at
`b435631`; obligations 2.5.7.3) is the same shape over `Column μ` with `eval₂Mle` into `E`.

**An inner-product (weighted-sum) oracle interface**: **none, anywhere upstream** (`git grep -i`
for `innerProduct`, `weightedSum`, `dotProduct … Oracle` at `7653a901` across
`OracleReduction`, `ProofSystem`, `Interaction`, `Data/MvPolynomial` finds no interface; the
only hits are anonymous-constructor tuples in proofs). The functional-commitment interface
`Commitment.Scheme` (`Commitments/Functional/Basic.lean:59-79`) is generic over any
`OracleInterface Data`, so an inner-product interface instantiates it without change
(gt-opening-compile A.5, probe `InnerProductOracle.lean`, exit 0 at both pins per that dossier).

### 6.c–d On `origin/main` and in open pull requests

Nothing. #383 and #615 add `OracleInterface` instances for their own message types only.

### 6.e–f What exists upstream, what remains ours

Upstream has the evaluation interface for Mathlib polynomials (noncomputable) and the generic
class; the inner-product interface the review recommends (register row `R18`; obligations
2.3.5.1, 2.5.7.3) is leanerVM's to define, in Layer 0, with `Weight μ` as the query type and
`Weight.pair` as the answer, and `eqWeight_pair` making evaluation the special case
(`ClaimWeights.lean:51-54` at `b435631`). It is generic ("a weighted-sum oracle on a table")
and belongs under `ToArkLib/` by the repository's rule, with a small upstream pull request as
the destination; nothing upstream plans it.

### 6.g Risk

None specific: the class is stable across the pins and the migration to the typed framework
keeps `OracleInterface` as the message-access primitive (`Interaction/Oracle/Protocol.lean:58`
`oracleWith (Messages : Type u) (interface : OracleInterface.{u, u} Messages)`), so an
interface written today survives a framework change.

## 7. Component 6: Fiat–Shamir, the Merkle/BCS compilation, and compiled security

### 7.a–b At both pins (identical)

- `Verifier.fiatShamir`, `Prover.fiatShamir`, `Reduction.fiatShamir`
  (`FiatShamir/Basic.lean:114-146`): definitions; the challenge oracle is `fsChallengeOracle
  StmtIn pSpec`, keyed by the statement and the messages so far. The one theorem,
  `fiatShamir_completeness` (`:163-173`), is `sorry` and is stated for a constant challenge
  implementation (`challengeImpl := fun ⟨i, _⟩ => (default : pSpec.Challenge i)`); the file
  ends with "`-- TODO: state-restoration (knowledge) soundness implies (knowledge) soundness
  after Fiat-Shamir`" (`:175`).
- State restoration: `Security/StateRestoration.lean` defines the prover types and games
  (`Prover.StateRestoration.{Soundness,KnowledgeSoundness}`, `srSoundnessGame`,
  `srKnowledgeSoundnessGame`, `Verifier.StateRestoration.{soundness,knowledgeSoundness}`,
  `:35-156`, no `sorry` in the file); the bridges from round-by-round are commented out
  (`Implications.lean:215-224`) and the bridges from salted to unsalted are admitted with
  `sorry` *in their statements* (`:229-255`: `Verifier.StateRestoration.soundness sorry sorry …`).
- The duplex-sponge Fiat–Shamir: `FiatShamir/DuplexSponge/{Defs,State}.lean` and
  `Security/{AbortAnalysis,Backtrack,BadEvents,Completeness,KeyLemma,Lookahead,ProverTransform,Soundness,TraceTransform}.lean`;
  every `DuplexSpongeFS.*`, `FSProverState.*`, `FSVerifierState.*`,
  `HashStateWithInstructions.*`, `OracleSpec.QueryLog.BadEventDS.*` name is in the baseline
  (definitions and lemmas admitted). `Security/Soundness.lean` at the pin holds the module
  docstring ("the main theorems that soundness and knowledge soundness of duplex sponge
  Fiat-Shamir reduces to that of basic Fiat-Shamir, following Section 6 in the paper. This
  relies on the key lemma (Lemma 5.1)") and no theorem declaration (`grep` for
  `theorem|lemma|def` after the header: none).
- The BCS transform: `BCS/Basic.lean` (84 lines) defines `ProtocolSpec.renameMessage` and has
  `BCSTransform` commented out twice (`:59-63`, `:79-82`). `Commitment.extractability`
  (`Commitments/Functional/Basic.lean:249-254`) has `False` for its body (lib-arklib B.2).
- Merkle trees: nothing in ArkLib (`git grep -il merkle` at `7653a901`: `Data/Hash/DomainSep.lean`,
  `BCS/Basic.lean`, `Fri/Spec/SingleRound.lean`, all mentions in prose). The implementation and
  its extractability live in **VCVio**: at leanerVM's new VCVio pin `a4232d08`,
  `VCVio/CryptoFoundations/MerkleTree/` (nineteen-plus modules) with, in `Extractability.lean`
  (no `sorry`), the experiment `extractabilityExperiment` (`:315`) and the theorems
  `extractability_rom_bound` (`:591`), `_coarse` (`:679`), `_birthday_dominates` (`:694`),
  `_quadratic` (`:717`): single-opening extractability over "one shared lazy random function"
  `Query →ₒ Y`, with the branch energy `c·k + choose(c,2) + min(T, 2(k+c)+1)·(m-c+depth)` and a
  comparison with Chiesa–Yogev Lemma 18.5.1 in the docstring; `Hashing/Defs.lean` has
  `build`, `verify`, `functional_completeness`, `verifyWithHash_completeness`;
  `BatchExtractability.lean`, `MultiExtractability/{Targets,InitializedBound,OnlineBound}.lean`
  and `Addressed/*` exist. ArkLib issue #4 was closed on 2026-09-27 as "a tracking transfer,
  not a claim that all tasks are complete" to VCVio #571, "including hiding and application
  work". ArkLib's status page lists "Shared-ROM Merkle extraction: available — adapt the
  primitive theorem; do not restate its game in ArkLib".
- BLAKE2s: nothing anywhere upstream (`git grep -il blake2` at `7653a901`: no file).

### 7.c On `origin/main`

Nothing beyond the pin.

### 7.d Open pull requests

- `#469` (feat(dsfs): statements of Section 5; chung-thai-nguyen; open since 2026-04-19,
  updated 2026-09-17, `CHANGES_REQUESTED`, `CONFLICTING`, 21 files): "intentionally provides
  the Section 5 definitions and supporting infrastructure without proving the probabilistic
  hybrid claims, Lemma 5.8, or Lemma 5.1"; "The single-salt Fiat--Shamir completeness theorem
  is stated here, while its proof is also left outside the scope of this PR."
- `#848` (feat(dsfs): prove Theorems 6.1 and 6.2; same author; base `dsfs-section5` (stacked on
  #469), `CHANGES_REQUESTED`, `CONFLICTING`): "Define adaptive, query-bounded NARG soundness and
  straightline knowledge soundness, including the corresponding state-restoration notions …
  Prove the canonical single-salt Fiat--Shamir soundness and straightline knowledge-soundness
  results (Theorems 3.18 and 3.19). Prove DSFS soundness (Theorem 6.1) … (Theorem 6.2)"; "The
  Section 6 reductions take an explicit `KeyLemmaSecurityWitness` … proving that the concrete
  Section 5 transforms produce this witness remains the separate Key Lemma obligation." Its
  `SingleSalt.lean` theorem `single_salt_fiat_shamir_knowledge_soundness` (at head `1c5c5bd7`,
  per gt-opening-compile E.2) takes **state-restoration** knowledge soundness of a plain
  `Verifier` and concludes adaptive NARG knowledge soundness with the same error. Fit with
  leanVM: the transform is the single-salt/duplex-sponge one of [CO25], not leanVM's ratcheted
  BLAKE2s chain with grinding (register row `R22`); the bridge round-by-round ⇒
  state-restoration is nowhere. Closeness: the maintainer requested changes on 2026-09-07 for
  both; the author reports resolving them on 2026-09-09 and 2026-09-04; both are in conflict;
  **unknown**, months.
- `#627` is an issue (design of the BCS transform as a change of `QueryImpl`), refreshed
  2026-09-29: "No BCS stage is marked complete by this source/issue refresh … This dependency
  update supplies no BCS or Flock security theorem." Its author's staging (July 2026) proved
  commit-then-reveal completeness only.
- ArkLib's own plan for compilation is `docs/design/04-oracle-elimination-compiler.md` (four
  passes `RepresentOracles`, `LowerAccesses`, `TransportBoundary`, `FiatShamir`, with
  "`BCS = HashChainFS(iBCS)`" as the conformance target and a Merkle adapter "AR-11" that
  "must adapt VCVio's existing shared-ROM execution and extractability theorem"); the roadmap
  says "Build the compiler only after the ordinary security, runtime, query-trace, and
  extraction results needed by its passes exist." No pull request implements any pass.

### 7.e What the blueprint plans to consume that does not exist

Ledger A5 (`bp:263`: "Named interfaces `FiatShamirSecurity` and `BcsSecurity` with the upstream
theorem as witness obligation; the *definitions* of the compiled verifier are consumed") and
Layer 12 (`bp:1218-1227`): no upstream theorem can be the witness (register rows `R20`,
`R21`, `R22`; lib-arklib G.4; gt-opening-compile E.2). The *definitions* consumable at the
pin are `Verifier.fiatShamir` (which takes a plain `Verifier` and hashes whole messages) and
VCVio's Merkle library; `BCSTransform` does not exist. Hole K2's "ArkLib #4" (`bp:613`) now
points at a closed issue whose work moved to VCVio #571.

### 7.f What remains leanerVM's

The Merkle compilation of the codeword oracles as a leanerVM definition (`bcsCompile`,
obligations 2.1.1.1) over VCVio's trees; the BLAKE2s chain as a `QueryImpl` of
`fsChallengeOracle` (gt-opening-compile probe H.2 shows the mechanism); the grinding checks;
the proof object and its decoding; and the three security interfaces stated for *this*
construction (state-restoration knowledge soundness of the Merkle-compiled argument in the
random-oracle model; the chain lemma; the grinding model) as assumed interfaces whose
obligation is the literature. The list-binding compilation (obligations 2.1.2.3) is ours and
upstream has no lemma for it.

### 7.g Risks

Everything in this component upstream is definitions-plus-admits on the legacy framework, and
the typed framework's compiler is a design document. The blueprint's expectation of "the
upstream theorem as witness obligation" has no date.

## 8. Component 7: WHIR, FRI, Basefold, and the coding theory

### 8.a At the old pin `dca90385`

- **WHIR**: absent (`git grep -il whir` hits only coding-theory files mentioning it in prose;
  no `ProofSystem/Whir/`). Ledger A7 is right.
- **FRI**: `ProofSystem/Fri/Spec/{General,SingleRound}.lean`, `Fri/RoundConsistency.lean`,
  `BatchedFri/*`. Regime (`Fri/Spec/General.lean:22-41`): "`F` a non-binary finite field
  (`[NonBinaryField F]`), `D` the cyclic subgroup of order `2^n` … `SmoothCosetFftDomain`" —
  multiplicative smooth domains, **not** binary fields; every `Fri.*` and `BatchedFri.*`
  relation and theorem is in the baseline (`Fri.fri_soundness`, `fri_query_soundness`, the
  relations themselves are `sorry` definitions).
- **STIR**: `ProofSystem/Stir/*`; `StirIOP.stir_main`, `stir_rbr_soundness`, `STIR.proximity_gap`,
  `Combine.combine_theorem`, `Quotienting.quotienting` admitted (baseline).
- **Binius Basefold and FRI-Binius** (`ProofSystem/Binius/BinaryBasefold/*`,
  `Binius/FRIBinius/*`, 11 files): the binary-field Basefold over CompPoly's additive NTT
  (`BinaryBasefold/Prelude.lean` imports `CompPoly.Fields.Binary.AdditiveNTT.AdditiveNTT`;
  `OracleFunction i := sDomain … → L`, `fold`, `baseFoldMatrix`, `:94, 610, 622`); the
  transcript shapes `pSpecFold`, `pSpecCommit`, `pSpecQuery`, `fullPSpec`
  (`BinaryBasefold/Spec.lean:210-274`); `fullOracleReduction`, `fullOracleReduction_perfectCompleteness`,
  `fullOracleVerifier_rbrKnowledgeSoundness` (`BinaryBasefold/General.lean:69, 110, 150`), all
  in the baseline together with every `Binius.BinaryBasefold.CoreInteraction.*`,
  `QueryPhase.*` and `Binius.FRIBinius.*` name (the whole Binius track is admitted at both
  pins; "definitions with `sorry`" for `fullOracleProof`, `queryOracleReduction`, etc.).
- **Coding theory**: `Data/CodingTheory/` (117 files at the old pin). The theorem the
  blueprint cites as its only coding input, [BCHKS25] Theorem 4.6:
  `CodingTheory.rs_mcaError_le_in_johnson_range` (`ProximityGap/CapacityBounds.lean:203`),
  "`sorry -- ABF26-T4.12; external admit [BCHKS25 Thm 4.6]`", the affine-line MCA error of a
  Reed–Solomon code for `δ < 1 − √ρ` bounded by the printed expression in
  `m = max(⌈√ρ/(1−√ρ−δ)⌉, 3)` (gt-opening-compile E.2 quotes it). The docstring (`:200-202`):
  "This is the only theorem standing under every Johnson-range `McaLowerWitness` constructor …
  until it is proved, every Johnson-range Grand-MCA witness in the tree is admit-backed."

### 8.b At the new pin `7653a901`

- WHIR, FRI, STIR, Binius: unchanged in proof status (the baseline entries are identical). The
  files did change between the pins (`git diff --stat`: `Fri/Spec/SingleRound.lean` 2 lines,
  `BatchedFri/Security.lean` 121, `Binius/BinaryBasefold/Prelude.lean` 234, the FRIBinius and
  Basefold phases a few lines each for #896, `Stir/*` for the perf pass #1094 and the
  probability migration #903/#913); I did not read those diffs beyond their sizes, and the
  identical baselines are the evidence that no theorem's status moved.
- **Coding theory grew from 117 to 369 files** (the #907 port, "port and canonize Reed–Solomon
  beyond-Johnson formalization", closed 2026-09-26: "Every applicable target, R1–R12 … is on
  `main`"; "361 (83,800 lines) were ported"). What matters for Annex B:
  1. `rs_mcaError_le_in_johnson_range` is **still admitted**, unchanged.
  2. A **proved** affine-line MCA bound in the Johnson range now exists, from the [DKT26]
     ("beyond Johnson") argument, `ReedSolomon.mcaError_affineLine_johnson_le`
     (`ReedSolomon/MutualCorrelatedAgreement/Johnson/Probability.lean:41-52`, #1198):

```lean
theorem mcaError_affineLine_johnson_le
    {F : Type} [Field F] [Fintype F] [SampleableType F] {n D : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1) :
    mcaError (AffineLineGenerator F) (code domain (D + 1)) (1 - johnsonAgreement n D eta) ≤
      min 1 (ENNReal.ofReal
        (johnsonExceptionCount n D ⌈johnsonAgreement n D eta * n⌉₊ eta /
          (Fintype.card F : ℝ))) := by
```

     with `johnsonAgreement n D η = √(D/n) + η` (`HiddenDerivative/Parameters/Johnson/FiniteBounds.lean:70`)
     and `johnsonExceptionCount n D A η = (2μ−1)h + θ(h + μ + 4Dμh) + (n−D−1)μ`
     (`:104-108`, with `μ`, `h`, `θ` the Johnson multiplicity, height and slack parameters of
     that file; "the raw exception count of the characteristic-free ordinary-agreement
     argument", closed upper bound `johnsonExceptionCount_lt_closed`). The module docstring:
     "**No characteristic hypothesis is needed.**" Its weighted variant
     `mcaError_affineLine_weightedJohnson_le` (`:72`) and the affine-space transfer
     `mcaError_affineSpace_le_of_exactAgreement` (`LineToAffine.lean:173`) exist. So at the new
     pin **a machine-checked Johnson-range MCA bound for affine lines over any finite field,
     binary included, is available**, with a different (and, by its own docstring, deliberately
     loose) constant from the printed BCHKS25 one that Annex B and the admitted theorem state.
     Whether its constant meets Annex B's per-level error budget at leanVM's parameters is
     **unverified** here (a numeric comparison of `johnsonExceptionCount` against BCHKS25's `a`
     at `ρ ∈ {1/2, …, 1/16}`, `n = 2^{κ+R}` would settle it; gt-opening-compile F.2 has the
     scratch tool).
  3. **MCA up to capacity** (#1208, `MutualCorrelatedAgreement/Capacity.lean`):
     `capacity_lineAgreement` (`:131`), `exists_capacity_mcaError` (`:254`),
     `capacity_powerBatchingAgreement` (`:324`): exact correlated agreement at agreement
     `k + δn` with gap-only constants `C n^(d+1)`. **Regime: every one of them carries the
     hypothesis `(ringChar F = 0 ∨ k - 1 < ringChar F)`** (`HasCapacityLineAgreement`, `:118-121`;
     `exists_capacity_mcaError`, `:254-263`), which **fails for leanVM's binary fields** (`ringChar E = 2`,
     `k − 1 ≥ 2` for any message length above three). The docstring says so: "over any field of
     characteristic zero or larger than `k - 1`"; for lines at gaps `δ ≥ 6/25` the proof uses the
     first-order certificate, below it the rate-partition construction, both with the
     characteristic guard, and only "when the curve characteristic guard fails, the line
     theorem uses the Johnson gap bound". So the beyond-Johnson results do not apply to Annex B
     over `E`; the Johnson-range theorem of item 2 does.
  4. List sizes: the pairwise Johnson list bound for arbitrary codes (#910,
     `JohnsonBound/Pairwise.lean`, `ReedSolomon/ListDecodability/PairwiseJohnson.lean:50`
     `code_isListDecodable_pairwiseJohnson`, `:75`, `:138`), proved — Annex B's Johnson bound
     `L_i = 1/(2η_i√ρ_i)` (obligations 2.1.2.4.2) has a proved upstream source, in the
     "pairwise" integral form `n(A−D)/(A²−nD)`; the exact form used by Annex B is to be derived.
  5. Folding: `ProximityGap/Folding/{FoldingContext,ListDecodability,Multilinear}.lean` exist
     (#825, #845, per #992's review notes: "folding contexts and list-decoding preservation");
     their fit with Annex B's Lemma B.10 (`2^{ℓ−1}` row union over the additive fold) is
     unverified here; `ProximityGenerator/BinaryTensorFoldAgreement.lean`,
     `BinaryTensorFoldProbability.lean` (#937, #938: "shared-level binary tensor fold",
     "tensor-fold probability") are the closest names to WHIR's `k`-ary fold on binary fields.
  6. Interleaving: `ProximityGenerator/Interleaving.lean` (#918 "generalize interleaving MCA
     transfer", #932 "exact agreement transfer for interleaved codes"); issue #893 says "ArkLib
     already provides the relevant interleaving error-transfer theorem; the exact
     list-transport and Flock extraction contracts remain work."
  7. `isMCAGenerator_of_isMDSGenerator` (#902) proved "in its unique-decoding range"; its
     all-radii form still admitted (#992's note).

### 8.c On `origin/main`

Nothing beyond the pin.

### 8.d Open pull requests

- `#992` (feat(fri): prove end-to-end soundness of the computable IOP; alexanderlhicks; open
  since 2026-09-22, mergeable, no review, 40 files): "Prove end-to-end ordinary and
  round-by-round soundness of the **actual computable FRI IOP specification** in
  `Fri.Spec.reduction`, against arbitrary adaptive provers: `Fri.Spec.soundness` …
  `Fri.Spec.rbrSoundness` supplies the existing round-by-round security interface …
  `Fri.Spec.reduction_run` proves the exact correspondence between the composed executable
  verifier and the bounded acceptance event". "The total error is the sum of ArkLib's existing
  powers-generator MCA errors plus `Real.toNNReal (1 - min θ δ) ^ l`." It notes "The general
  round-by-round-to-ordinary implication remains unfinished; this proof uses direct adaptive
  accumulation." Regime: FRI over `NonBinaryField` with smooth multiplicative cosets — **not
  binary, not WHIR**. Fit: a *pattern* for stating an IOPP's round-by-round soundness for a
  list relation on the legacy framework (`Security/Acceptance.lean`, `Accumulation.lean`,
  `BadEvents.lean` are new generic files), which is the shape Layer 11's `whirOpen_rbrSoundness`
  needs. Closeness: forward-ported on 2026-09-22, no review since; **unknown**.
- `#383` (feat: completeness and rbrKnowledgeSoundness of FRI-Binius protocols;
  chung-thai-nguyen; open since 2026-03-03, updated 2026-09-26, `CHANGES_REQUESTED`,
  `CONFLICTING`, 76 files): "Completeness & rbrKnowledgeSoundness for all FRI-Binius
  protocols: Binary Basefold, Ring-switching, FRI-Binius, simple ring-switching construction
  (BBFSmallFieldIOPCS) … All PR-owned files are sorry-free; the top-level composed results
  inherit sorryAx from OracleReduction's composition layer." The author's last update
  (2026-09-24): "DP24's ring-switching and FRI-Binius require laws beyond those in the default
  ring-switching profile, so we use a CoordinateLaws precondition for now." A maintainer
  comment (2026-09-08) says #887 already migrated the FRIBinius/BinaryBasefold *completeness*
  on `main`. Fit with leanVM: Basefold over binary RS codes with the additive NTT is the closest
  upstream object to Annex B's WHIR (same code, `2`-ary fold, no out-of-domain samples, no
  `k`-ary fold, no grinding, no weighted claims); its security proofs would rest on the legacy
  composition and on `rs_mcaError_le_in_johnson_range`. Closeness: seven months open, second
  round of changes requested, conflicting; **remote**.
- `#776` (threshold-form public faces for the proved bound catalog), `#787` (BCIKS20
  separability repairs), `#792` (Grand List-Decoding witness constructors): coding-theory
  polish, none load-bearing for Annex B.

### 8.e What the blueprint plans to consume that changed

Ledger A8 (`bp:265`: "Interface `McaJohnson`, witness obligation [BCHKS25] Theorem 4.6 in
ArkLib") and status `status:181` ("ArkLib's coding-theory track (the #907 slices landing on
`main`)"): the #907 port is **complete**, and it did **not** prove `rs_mcaError_le_in_johnson_range`;
it proved a *different* Johnson-range affine-line bound (8.b item 2) that Annex B could cite
instead, with its own constant. The blueprint's `McaJohnson` structure should be stated so
that either theorem inhabits it (a bound `mcaError (AffineLineGenerator E) (code domain k) δ ≤ a/|E|`
with `a` a parameter), and Annex B's error table re-derived for the proved constant if that is
the one consumed.

### 8.f What remains leanerVM's

WHIR itself (Annex B, Protocol B.1, Theorem B.7 with its per-level table; the `k`-ary fold on
the additive domain over `K` at level 0 and `E` after; out-of-domain samples; the weighted
claims; grinding as a message), the Merkle/BLAKE2s side, the parameters ladder, and the
list-binding compilation. The coding-theory inputs it needs beyond the line MCA bound (folding
preserves lists with the row union, out-of-domain separation, the Johnson list size in Annex
B's form) exist upstream as building blocks in some form (8.b items 4–6) and must be
instantiated and checked against Annex B; nothing upstream states them for WHIR.

### 8.g Risks

Annex B's Theorem B.7 is not machine-checked anywhere, and the two nearest upstream IOPP
soundness proofs (#992 for multiplicative FRI, #383 for binary Basefold) are open and
conflicting on the legacy framework. The capacity-range theorems that made the news are
inapplicable in characteristic two.

## 9. Component 8: ring switching and binary fields

### 9.a At the old pin `dca90385`

`ProofSystem/RingSwitching/` (15 files): the family umbrella `Basic.lean` ("a family of
constructions, not one protocol": **Packing**, small ring → large ring by a basis of rank `2^κ`,
[DP24] Construction 3.1; **Lift**, quotient ring → field, [HMZ25]), `Transport/{Eval,Coeffs}.lean`,
`RoundVerifiers.lean`, `Packing/{Profile,Prelude,Spec,BatchingPhase,SumcheckPhase,General}.lean`,
`Lift/{Presentation,Reduction}.lean`. The packing data layer `RingSwitchingProfile B L κ`
(`Packing/Profile.lean:87`: a basis exhibiting `L` free of rank `2^κ` over `B`, a carrier `A`,
two ring homs `φ₀ φ₁ : L →+* A`, coordinate maps with reconstruction laws) with the one
instance `tensorProductProfile κ K L β` for any `[Field K] [Field L] [Algebra K L]` and a basis
`β : Module.Basis (Fin κ → Fin 2) K L` (`Packing/Prelude.lean:477-487`). The protocol
`RingSwitching.FullRingSwitching.{fullOracleReduction,fullOracleVerifier,fullOracleProof}`
with `fullOracleReduction_perfectCompleteness` and `fullOracleVerifier_rbrKnowledgeSoundness`
(`Packing/General.lean:89, 153, 185`); all `RingSwitching.BatchingPhase.*`,
`SumcheckPhase.*`, `FullRingSwitching.*` security names are in the baseline ("Leaf proofs are
open (`sorry`)", `General.lean:34`; the composed theorem also uses the admitted
`OracleVerifier.append_rbrKnowledgeSoundness` and two `sorry` at `:222, :226`). `Lift/` has
no `sorry` in `Reduction.lean` and `Presentation.lean` (coordinate-wise special soundness at
`k = 2·deg φ`), one in the umbrella.

### 9.b At the new pin `7653a901`

Five files changed (91 insertions, 97 deletions): #894 (CompPoly's explicit tensor-basis API),
#896 ("fix(ring-switching): align packing coordinates with the protocol": "The tensor profile
used row coordinates for the original-claim check and column coordinates for batching. Over
`GF(4)/GF(2)`, honest packing of `t(X₀,X₁) = X₀` at zero consequently rejected the correct claim
`0`. … Generic profile reconstruction remains a data contract; full protocol completeness and
soundness are still open."), and the probability notation. Same baseline. The status's
"packing coordinates repaired after the pin, ArkLib #896" (`status:182`) is correct and now
*at* the pin.

### 9.c On `origin/main`

Nothing beyond the pin.

### 9.d Open pull requests

- `#615` (3.d): "Independent finite bases support different packing/opening algebras and
  ranks. Finite weighted observation is shared by Boolean-table packing and Hachi's
  monomial/ψ representation … The batching head has proved completeness and worst-case
  knowledge security, instantiated with the production codeword commitment's unique-distance
  binding." Its file list adds `Packing/{Batching,BatchingAlgebra,CheckedObservation,Coordinates,ExactCommitment,FiniteObservation,FullFamily/*,Multiplier,Opening,PackedCommitment,Polynomial,ProfileCoordinates,ProfileLayout,Relations,ScalarFamily/*,ScalarHead/*,Tail/*}.lean`
  (forty-odd new files). Its own boundary: "Full FRI-Binius security/completeness, the profile
  sumcheck loop, unrestricted knowledge composition, ordinary-soundness conversion, Flock
  PCS/list/OOD integration, HMZ exceptional-set security, and Hachi scalar-Scheme/recursive
  integration remain outside the proved contracts."
- `#383` (8.d): its `RingSwitching/Packing/{BBFSmallFieldIOPCS,Compatibility,CoordinateLaws,…}.lean`
  add a `CoordinateLaws` precondition and the "simple ring-switching construction".
- Issue `#893` ("roadmap: complete Binius interfaces, rejection semantics and proofs",
  refreshed 2026-09-29): "#615 remains open at `ca7a2577`; its independent-rank packing,
  ordinary/quirky reconstruction and guarded security are reuse candidates, while Flock
  PCS/list/OOD integration and full FRI-Binius closure remain outside the proved contracts.
  #383 remains open." And: "Neither full Binius completion nor a tower replacement is a global
  Flock prerequisite."

### 9.e What the blueprint plans to consume

Ledger A9 (`bp:266`: "`RingSwitching/Packing` leaves are `sorry`, and no `GF(2) → GF(2^64)`
profile … Owned by #3 (F5); consumed through the Flock interface"), hole P6 (`bp:609`: "#3,
ArkLib #383, #893"). At the new pin: the leaves are still `sorry`; the profile constructor
`tensorProductProfile` is generic enough to instantiate `GF(2) → K` given a `Module.Basis (Fin 6 → Fin 2) (ZMod 2) K`
(CompPoly's `BF64` at the new pin is a structure over `BitVec 64`; whether it carries an
`Algebra (ZMod 2) BF64` instance and a bit basis in the shape `Fin 6 → Fin 2` is **unverified**
here; issue #893 says "CompPoly B1/B2 and the selected-tower interface/backend work are
merged"). leanVM's ring switching is not DP24's interactive relocation at an arbitrary large-field
point but the specification's Annex A construction with eighteen strided limb columns
(`gt-flock-ring` §6; the "rectangular" shape of the task statement): the packing sumcheck's
degree-2 `H = m·t` loop of `SumcheckPhase.lean` is the same *kind* of object, but the leanVM
protocol's message schedule, the `Φ(eq(r,u))` weight and its integration into the claim pool
(`stack_open.rs:45-48`) are leanVM-specific.

### 9.f What remains leanerVM's (or Flock's, issue #3)

The `GF(2) → K` profile instance, the Annex A protocol as a `Phase.Def` at the flock seam
(`bp:1083-1090`), its completeness and its round-by-round knowledge soundness with
`flockError`; none of it exists upstream in provable form, and the ArkLib packing security
leaves would need to be proved first if consumed.

### 9.g Risks

Both open pull requests are long-lived, conflicting and unreviewed for weeks; the merged
repair #896 shows the pinned packing protocol was *wrong* on a two-variable example before
2026-09-12, which is evidence that these files are not yet a stable specification.

## 10. Component 9: the typed Interaction framework's security notions, and the cost of migrating the spine

### 10.a–b What the framework proves at the new pin (nothing of it at the old pin)

- **Plain composition soundness** (`Interaction/CompositionSoundness.lean`, #1218, #1231):
  `run_appendFlat_soundness` (`:227`), `_fixed` (`:210`), `_of_support` (`:191`), `_ae` (`:171`),
  `_weighted_ae` (`:122`), `_of_admissible` (`:260`): for a prefix truth-transition bound `ε₁`
  and a suffix bound `ε₂` (and an admissibility error `δ`), the appended interaction's
  success is at most `ε₁ + ε₂` (`ε₁ + δ + ε₂`), for every native prover, under lawful
  distribution semantics; the reachable/almost-everywhere/weighted forms allow branch-dependent
  suffix errors.
- **Oracle composition** (`Interaction/Oracle/{Sequential,SourceRouting,CompositionSoundness}.lean`,
  #1233, #1234, #1235): `executeStrategies_append`, `executeStrategies_appendExported_close`,
  `executeStrategies_appendExported_soundness_ae` (`:302`), `_weighted_ae` (`:208`): a suffix
  reduction written against an *exported* oracle interface composes with the prefix that
  exports it; the uniform bound is `εtruth + εinvalid + εsuffix`.
- **Persistent runtime** (`Oracle/RuntimeSoundness.lean`, #1237) and **access/cost
  certificates** (`Data/OracleComp/QueryBounds.lean`, #1238).
- **Security vocabulary**: soundness only. `git grep -i 'knowledge|extract|rbr|roundbyround'`
  over `ArkLib/Interaction` and `ArkLib/ProofSystem/Sumcheck/Interaction` at `7653a901` finds
  two docstring uses of "extracted" (a handler, a source behavior) and nothing else. There is
  no `KnowledgeStateFunction`, no extractor type, no round-by-round notion, no
  state-restoration notion, no Fiat–Shamir on this framework. The design chapter
  `03-adversarial-oracle-execution.md` §5–7 describes them as *targets*: "State restoration is
  a separate proposed security layer"; "Knowledge soundness requires witness availability, not
  only a bound on true output claims. An offline extractor of a final execution path may learn
  a middle witness too late to supply it to the second protocol. Terminal offline knowledge
  soundness therefore does not compose in general"; "The planned constrained execution tree …
  Round-by-round state is indexed by full concrete prefixes"; "These are target interfaces and
  dependencies, not consequences of the ordinary composition theorem."

### 10.c–d Beyond the pin and in open pull requests

Nothing on `origin/main`; the only open pull request on the framework is the dependency repin
`#1251` (draft, dtumad, 2026-09-29: "Repins VCVio to Verified-zkEVM/VCVio#821 … moves VCVio's
probability semantics onto Mathlib measures and removes the discrete layer"; 59 files, all
mechanical `Pr{x ← e}` → `Pr{let x ← e}` rewrites). When it merges, every probability
statement in leanerVM's bridges (`ToArkLib/GuardedVerdict.lean`, `ToVCVio/UniformSample.lean`)
changes notation again.

### 10.e–f What the blueprint could consume; what migrating would cost

Today nothing: the master theorems are `rbrKnowledgeSoundnessWorstCaseWith` statements, a
notion the typed framework does not have. Migrating the spine would mean:

1. re-expressing every phase as a `Verifier.Strategy`/`Prover.Strategy` on an
   `Interaction.Oracle.Protocol` tree (the commit phase as `.oracleWith (Column μ) evalOracle …`,
   the challenges as `.public .receiver E`), and the relations as predicates on `ClosedClaim`s
   (statement plus observable oracle answers — for the stack, the `2^μ` evaluations the
   relation reads, or the weighted sums under the inner-product interface);
2. waiting for, or writing, the round-by-round knowledge notion and its composition on that
   framework (roadmap items 3–4, no pull request), including the "prefix-available witness
   extraction" the design chapter says composition needs — for the spine this is the commit
   phase's extractor, which reads the stack off the first message and is available to every
   suffix, so the spine is the easy case the design describes;
3. re-proving the two built phases and the port's role (the knowledge append) in the new
   vocabulary, and re-running every probe.

The gain would be the removal of the local port and of the dependence on a framework upstream
calls legacy; the cost is that none of the target notions exists, and that the migration would
have to be redone if the framework's security definitions change while they are being written
(their design is explicitly "fluid internals" behind "normative interfaces",
`04-oracle-elimination-compiler.md:3`).

### 10.g Risk

The typed framework is where all upstream investment goes (the 2026-09-26 train #1214–#1243 is
its work), and the legacy framework's remaining admits are being *characterized as false*
(#1245) rather than proved. A spine that stays legacy must own its composition theorems
(it does) and must not plan on upstream repairs of `Append/Security.lean`.

## 11. A revised upstream ledger for the blueprint

One row per item of the blueprint's ledger (`bp:255-267`) and holes table (`bp:594-617`) that
names generic work. "Exists at `7653a901`" is the declaration and its proof status; "open
pull request" its number and state on 2026-09-30; "action" is the proposal; the last column
lists the register rows the item touches. Statuses: *proved* = not in the axiom baseline;
*admitted* = in it.

| Blueprint item | What the blueprint plans | Exists at `7653a901` | In an open pull request | What remains ours | Proposed action | Register rows |
| --- | --- | --- | --- | --- | --- | --- |
| A1 / G1 sumcheck definition and completeness | `Virtual`, `sumcheck : OracleReduction []ₒ …`, `sumcheck_perfectCompleteness` (`bp:880-894`) | typed one-polynomial sumcheck: `Sumcheck.Interaction.Native.{protocol,verifier,execute}` (`Protocol.lean:333-351`), `Native.execute_perfectCompleteness` (`ProtocolCompleteness.lean:110`), computable prover and verifier (`Computable.*`, `Impl/{Representation,Projection}.lean`), all proved; classical `Sumcheck.Spec.reduction_perfectCompleteness` admitted (through `liftContext_perfectCompleteness`) | #1128 (honest identities, small, mergeable), #1244 (legacy verifier repair) | the virtual summand and its final message; the eq-weighted back-loaded variant; the normalized round; the encoding; an `OracleReduction` adaptor to the native verifier | **write locally** the four variants as `OracleReduction`s; consume the typed honest prover (`projectedMessage`) and CompPoly algebra at the pin bump through an adaptor for the plain case only; drop "contribute the leaf" wording | `R2`, `R7`, 2.5.1.1–2.5.1.4 |
| A1 / G2 sumcheck round-by-round knowledge soundness | `sumcheck_rbrKnowledgeSoundness … (fun _ ↦ d/\|F\|)`; "Layer 4 proves the single-round bound … contributes it as the missing leaf" | `Native.execute_soundness` (`ProtocolSoundness.lean:201`): **plain** soundness `count·deg/\|F\|`, no extractor, `Unit` witness, proved; legacy `Sumcheck.Spec.SingleRound.Simple.verifier_rbrKnowledgeSoundness` **admitted and false as stated** (section 2.a) | #1244 repairs the legacy statement; #1129 tests; upstream roadmap items 3–4 (typed round-by-round and knowledge) have no pull request | the per-round knowledge state function and bound for each leanVM variant, on the legacy notion the spine uses | **write locally**; if offered upstream, target the repaired statement after #1244 or the typed notion once it exists; do not depend on either | `R7`, 2.5.1.3 |
| A2 / C1 knowledge-soundness append | port of #615's `Append/Knowledge.lean`, "deleted at the pin bump" | admitted (`Append/Security.lean`, 4 `sorry`); the port is the only proof | #615 (conflicting, unreviewed, pre-module); n-ary `KnowledgeNary.lean` there too | nothing (built) | **keep the port**; restate the deletion condition as "when a revision of ArkLib proves a guarded-first append for `rbrKnowledgeSoundnessWorstCaseWith`, on whatever framework the spine then uses" | `R34` |
| A3 round-by-round ⇒ plain | "the plain corollary is stated once the implication lands upstream" | `rbrKnowledgeSoundness_implies_knowledgeSoundness`, `rbrSoundness_implies_soundness` admitted | #1245: proves `rbrSoundness_implies_soundness` **under `[Subsingleton σ]`** and exhibits a counterexample without it; the knowledge twin untouched | the knowledge corollary in the stateless form (lib-arklib probe `PlainReading`: forty lines) | **write locally** in the stateless form now (the spine's `σ` is `Unit`); consume #1245's soundness half if it merges | `R34`, 2.1.2.7 |
| A4 context lifting | "not consumed" | all `liftContext_*` security theorems admitted; the two definitions admitted | #926 (draft, CI red) closes the definitions and completeness transports, not the soundness theorems | nothing, provided the GKR is restated over the leaf tables without lifting (`R10`) | **avoid**, as planned; note that `R10` forces the restatement | `R10` |
| A5 / K3 Fiat–Shamir and BCS | `FiatShamirSecurity`, `BcsSecurity` "with the upstream theorem as witness obligation"; consume `Verifier.fiatShamir` | `Verifier.fiatShamir` (definition, hashes whole messages); `fiatShamir_completeness` admitted for a constant oracle; state-restoration definitions proved; round-by-round ⇒ state-restoration commented out; `BCSTransform` commented out; duplex-sponge track all admitted; **no BCS**; Merkle trees in VCVio with `extractability_rom_bound` proved | #469 (definitions, changes requested, conflicting), #848 (Theorems 6.1/6.2 of [CO25] taking a `KeyLemmaSecurityWitness`, stacked, conflicting); #627 is an issue | the chain as a `QueryImpl`, `bcsCompile` over VCVio's trees, grinding, decode, the three interfaces for leanVM's construction, the list-binding compilation | **write locally** the definitions; state the interfaces for leanVM's construction with the literature as obligation; **wait** for nothing | `R20`–`R26`, `R138`, 2.1.1, 2.1.2 |
| A6 / G3 batching | `batchClaims`, `(k − 1)/\|F\|` (`bp:907-911`) | nothing | #615's `BatchingStrategy.gammaPowers` (a separation lemma in retired notation) | all: the lemma, the component, its knowledge state; under `R18` this **is** the opening phase | **write locally** under `ToArkLib/`; offer upstream as its own small pull request | `R18`, 2.5.2 |
| A6 / G4 fingerprints, product lemma, collision | `fingerprint`, `sideProduct`, Lemma 5.2, Theorem 5.1 (`bp:923-931`) | nothing; `schwartz_zippel_counting` and `prob_eval_zero_le_div` proved, the latter **now stated on VCVio's `$ᵗ` sampler** (`SchwartzZippelCounting.lean:114-124`), with `prob_eval_zero_univ_le_div` (`:138`) | none (issue #901 is the request; leanerVM #39 is the staged fingerprint half) | all | **write locally** (finish #39 and the product half); consume `prob_eval_zero_le_div` at the pin bump instead of a local bridge where the bad set is not a subsingleton | 2.5.3 |
| A6 / G5, G6 GKR | radix-4 product-tree GKR, `gkrError` (`bp:933-948`) | nothing | #818: Thaler's circuit GKR, radix 2, completeness only, inherits `sorryAx`, stalled | all | **write locally**; cite #818 as a pattern for a layer as an `OracleReduction` | `R7`, `R9`, `R10`, 2.5.4 |
| A6 / L1 stacking | built in leanerVM (`ToCompPoly/*`) | nothing upstream | none (issue #900 is the request) | nothing (built) | **offer upstream** (CompPoly per the status's finding E16); no consumption | 2.5.6 |
| A7 / K1 WHIR | `encode`, `whirOpen`, `whirOpen_rbrSoundness` (`bp:1166-1177`) | nothing for WHIR; Binius Basefold over binary RS and the additive NTT defined, every theorem admitted; FRI (non-binary) defined, admitted; CompPoly's additive NTT exists | #383 (binary Basefold security, conflicting, changes requested); #992 (multiplicative FRI end-to-end soundness, mergeable, unreviewed) | all of WHIR, over `K` at level 0 and `E` after, with grinding as a message | **write locally**; use #992's `Fri.Spec.rbrSoundness` shape and #383's Basefold as patterns; do not wait | `R19`, `R23`, `R24`, 2.1.2.4 |
| A7 / K2 Merkle, BLAKE2s | `merkleRoot`, `merkleVerify`, `blake2sBytes` (`bp:1179-1182`); "ArkLib #4" | ArkLib: nothing; **VCVio** (`a4232d08`): `MerkleTree/Hashing/Defs.lean` (`build`, `verify`, completeness), `Extractability.lean` (`extractability_rom_bound` and variants, proved), batch and multi-instance extractability modules | none in ArkLib; ArkLib #4 closed 2026-09-27, moved to VCVio #571 (open) | BLAKE2s, the leaf/node encodings, the fit of leanVM's fixed-height trees with VCVio's `NodeQueryModel` | **consume VCVio's trees at the pin bump** for the definitions and the single-opening extraction; write the BLAKE2s instantiation and the fit lemma; replace "ArkLib #4" by VCVio #571 | 2.1.2.2, 2.1.2.6 |
| A8 mutual correlated agreement up to Johnson | `McaJohnson`, obligation [BCHKS25] Theorem 4.6 "in ArkLib" | `rs_mcaError_le_in_johnson_range` still admitted; **`ReedSolomon.mcaError_affineLine_johnson_le` proved** (`Johnson/Probability.lean:41`), any finite field, constant `johnsonExceptionCount`; capacity-range theorems proved but **excluded in characteristic two** | none needed | the numeric comparison of the proved constant with Annex B's table; the fold and list lemmas instantiated for WHIR | **consume the proved theorem at the pin bump** if its constant fits the parameters, else keep the interface with the admitted theorem named as obligation; rewrite ledger A8 and the status's row | 2.1.2.4.1 |
| A9 / P6 ring switching | `FlockInterface` (`bp:1083-1090`), "no `GF(2) → GF(2^64)` profile" | `RingSwitchingProfile`, `tensorProductProfile` (generic constructor, coordinates repaired by #896), protocol defined, every security leaf admitted | #615, #383 (both conflicting) | the profile instance, Annex A's protocol as a phase, its proofs (issue #3) | **write locally** (issue #3); consume the profile *structure* only | 2.3.4 |
| I1 Clean polynomials | Clean #466 | out of ArkLib's scope | — | — | unchanged | 2.5.8 |
| inner-product oracle (not in the ledger; `R18`) | evaluation interface at Layer 0 | `OracleInterface` class; evaluation instances for Mathlib polynomials; no weighted-sum interface anywhere | none | the interface, `Weight` below `Field.lean`, `eqWeight_pair` as the special case | **write locally** under `ToArkLib/`, offer upstream | `R18`, `R138`, 2.5.7.3 |
| the typed framework (not in the ledger; `R34`) | — | plain soundness composition, native sumcheck, runtime and cost certificates, no knowledge notion | #1251 (repin, draft) | — | **add a ledger row**: "the spine stays on `OracleReduction` until the typed framework defines round-by-round knowledge soundness and its composition (ArkLib roadmap items 3–4); revisit at each pin bump" | `R34` |

Two decisions the owner must take before the next pin bump:

1. **Framework.** Stay on `OracleReduction` (the only framework with knowledge soundness) and
   own the composition (done), or migrate now and wait for notions that do not exist. The
   evidence of sections 5 and 10 says stay, and write the ledger row so.
2. **Sumcheck.** Consume the typed sumcheck through an adaptor for the *plain* one-polynomial
   case (honest prover, computable verifier, plain soundness) and write the four leanVM
   variants locally with their round-by-round knowledge leaves; or keep the whole of Layer 4
   local. Either way the leaf proofs are ours; the adaptor buys the computable honest prover
   and the algebra of #1128/#42, and costs a correspondence lemma between an `OracleReduction`
   run and the native `execute`.

The third decision, the inner-product oracle, is not an upstream question: nothing upstream
has it or plans it; the spine should define it (gt-opening-compile A.5 (ii)).

## 12. Findings

### 12.1 The classical sumcheck leaf the ledger targets is false as stated at both pins (major)

*Evidence.* `Sumcheck.Spec.SingleRound.Simple.verifier` (`Spec/SingleRound.lean:391-397` at
`dca90385` and `7653a901`, quoted in 2.a) sets the next target to `(oStmt ()).val.eval chal`,
the input polynomial's value; `Simple.oracleVerifier` (`:423-436`) queries `[OStmtIn R deg]ₒ`
for it; the round-`i` verifier (`:800`) is that verifier under `liftContext` (#1244's
`verifier_eq_unfolded`). ArkLib issue #1, comment of 2026-09-27: the F₅ counterexample, "the
input relation is false and the sum check passes". The admitted
`Simple.verifier_rbrKnowledgeSoundness` (`:570-573`) claims error `deg/|R|` per challenge; at
`deg = 0` the transition from a false input to an accepted true output has probability one
(paper: `outputRelation` is `(oStmt ()).1.eval chal = newTarget`, `:354`, satisfied by
construction). Pull request #1244 (open) repairs the statement.

*Classification.* An error of the blueprint's plan (it names a false statement as the leaf to
prove) caused by an upstream defect; a deviation forced by an upstream library once #1244 is
the reference.

*Proposed change.* Ledger A1 (`bp:258`), as it stands: "Layer 4 proves the single-round bound
for its own sumcheck shape and contributes it as the missing leaf." Proposed: "Layer 4 proves
the single-round knowledge bound for each of its own sumcheck shapes, on the spine's notion.
ArkLib's classical leaf `Sumcheck.Spec.SingleRound.Simple.verifier_rbrKnowledgeSoundness` is
admitted and, until ArkLib #1244 merges, false as stated (the verifier reads the input
polynomial for its next target); the typed sumcheck of `Sumcheck/Interaction/` proves plain
soundness with no knowledge notion. Nothing is contributed upstream until ArkLib has a
knowledge notion for the sumcheck." Reason: the two upstream objects the row could mean are
respectively false and of the wrong kind.

### 12.2 Holes G1 and G2 name upstream sources that do not supply what they are listed for (major)

*Evidence.* Hole G1's "Existing work" (`bp:598`): "#42, ArkLib #1128, ArkLib `main`'s
`Sumcheck/Interaction/`"; hole G2 (`bp:599`): "ArkLib #1129, `Interaction/Soundness.lean`";
status `status:198`: "#42's `HonestSumcheckUpstream.lean` … merged and the pin bumped; the
adapter is deleted then". At `7653a901`: `Sumcheck/Interaction/Soundness.lean` proves one-round
*plain* soundness of a committed message (`executeCommitted_soundness`, `:131`;
`executeRandomCommitment_soundness`, `:167`) on the typed framework; the full protocol's
`Native.execute_soundness` is plain soundness with `Unit` witness (2.b); #1128 is honest
algebra; #1129 is tests. None is an `OracleReduction`, none is round-by-round, none has an
extractor, none has a virtual summand. leanerVM #42 is now `CONFLICTING` and targets the
classical `Spec` projection, whose verifier has the defect of 12.1.

*Classification.* Stale text of the blueprint and status (an error of the plan).

*Proposed change.* Replace the two "Existing work" cells by: G1 — "ArkLib `7653a901`:
`Sumcheck.Interaction.Native` and `Computable` (one-polynomial sumcheck on the typed framework,
computable honest prover `Impl.Computable.projectedMessage`, perfect completeness; consumable
for the plain case through an `OracleReduction` adaptor); #42 for the honest algebra of the
leanVM variants"; G2 — "nothing upstream: `Native.execute_soundness` is plain soundness with no
extractor; ArkLib roadmap items 3–4 (native round-by-round and knowledge) have no pull request
(2026-09-30)". Reason: a reader of the holes table would otherwise start G2 by porting a theorem
of the wrong kind.

### 12.3 Ledger A8 and the status's coding-theory row are stale in both directions (major)

*Evidence.* `bp:265`: "`rs_mcaError_le_in_johnson_range` is an external admit … witness
obligation [BCHKS25] Theorem 4.6 in ArkLib"; `status:181`: "ArkLib's coding-theory track (the
#907 slices landing on `main`)". At `7653a901`: #907 is closed as complete (2026-09-26) and
`rs_mcaError_le_in_johnson_range` is still admitted (baseline; `CapacityBounds.lean:203`),
so the watched track will not prove it; but `ReedSolomon.mcaError_affineLine_johnson_le`
(`Johnson/Probability.lean:41-52`, quoted in 8.b) is a *proved* Johnson-range affine-line MCA
bound over any finite field with the constant `johnsonExceptionCount`; and the capacity-range
theorems (`Capacity.lean:118-121, 254-263`) carry `ringChar F = 0 ∨ k - 1 < ringChar F`, false
over `E`.

*Classification.* An error of the blueprint (it plans to consume a theorem whose proof is not
coming, and misses the one that exists); the constant mismatch with Annex B is a deviation
forced by the upstream library until compared.

*Proposed change.* Ledger A8, as it stands: "Interface `McaJohnson`, witness obligation
[BCHKS25] Theorem 4.6 in ArkLib." Proposed: "Interface `McaJohnson`, a bound
`mcaError (AffineLineGenerator E) (code domain k) δ ≤ a/|E|` with `a` a parameter. Two
inhabitants: ArkLib's admitted `rs_mcaError_le_in_johnson_range` (the printed [BCHKS25]
constant Annex B uses) and ArkLib's proved `ReedSolomon.mcaError_affineLine_johnson_le`
(`7653a901`, the [DKT26] constant `johnsonExceptionCount`, any characteristic); Layer 11 uses
the proved one if its constant meets Annex B's per-level budget at the pinned parameters
(to be computed), else names the admitted one as the obligation. The capacity-range theorems
of the same port exclude characteristic two and are not usable." Reason: consume what is proved;
say what is not.

### 12.4 Hole K2 cites a closed issue; the Merkle library the blueprint needs is VCVio's and is proved (minor)

*Evidence.* `bp:613`: hole K2's issue column "ArkLib #4". ArkLib #4 was closed on 2026-09-27
("Closing this duplicate tracker in favor of VCVio #571 … The Merkle implementation and its
security work are maintained upstream"). VCVio at `a4232d08`:
`CryptoFoundations/MerkleTree/Extractability.lean` with `extractability_rom_bound` (`:591`)
and three variants, no `sorry`; `Hashing/Defs.lean` with `verifyWithHash_completeness`
(`:288`); batch and multi-instance modules. ArkLib's status page: "Shared-ROM Merkle
extraction: available — adapt the primitive theorem; do not restate its game in ArkLib."

*Classification.* Stale text; a missed consumable.

*Proposed change.* Hole K2's issue cell: "VCVio #571 (open); the trees and their single-opening
random-oracle extractability are VCVio's (`MerkleTree/Hashing/Defs.lean`, `Extractability.lean`
at `a4232d08`)". Layer 11's Merkle sketch (`bp:1179-1182`) should say `merkleRoot` and
`merkleVerify` are VCVio's `build`/`verify` instantiated with BLAKE2s, and add the fit lemma
(leanVM's fixed-height, fixed-leaf-width trees as a `NodeQueryModel`). Reason: the blueprint
would otherwise re-implement a proved library.

### 12.5 The batching component's named upstream source is not a reduction and lives in a pull request that will not merge as is (minor)

*Evidence.* Hole G3 (`bp:600`) and status (`status:180, 189`): "ArkLib #615's `gammaPowers`".
`gammaPowers` (`Packing/Batching.lean:88-91` at `ca7a2577`) is a `BatchingStrategy`, a
separation lemma in the `Pr_{…}` notation that #913 retired; #615 is conflicting, pre-module,
unreviewed since July; issue #893 calls it a "reuse candidate".

*Classification.* Stale plan.

*Proposed change.* G3's existing-work cell: "#43 (the table pairing); the separation lemma is
twenty lines (ArkLib #615's `gammaPowers` is the reference, not a dependency)". And the
"Adopt when" of the status's #615 row for G3: "never as a dependency; write and offer
upstream". Reason: the opening phase must not depend on #615.

### 12.6 The deletion condition of the port, and the plain corollary, should be restated on the evidence of #1245 (minor; reinforces register row `R34`)

*Evidence.* #1245 (2026-09-27): `Verifier.rbrSoundness_implies_soundness` "is unprovable as
stated … `toFun_full` quantifies the verifier's run from a fresh draw of `init`, while
`Verifier.soundness`'s game runs the verifier from the oracle state the prover's queries leave
behind", with a kernel-checked counterexample; the pull request proves the implication under
`[Subsingleton σ]`. Issue #676 (2026-09-29): "Do not assume an unrestricted stateful
composition statement is provable merely because its components are secure from the same
fresh initialization."

*Classification.* A deviation forced by the upstream library, to be recorded.

*Proposed change.* Ledger A3, as it stands: "the plain corollary is stated once the
implication lands upstream." Proposed: "the plain corollary is stated locally for the
stateless shared oracle (`σ = Unit`), where ArkLib #1245 shows the implication holds and
outside which it is false; nothing is awaited upstream." Ledger A2's deletion condition as in
section 11. Reason: the awaited theorems are being shown false, not proved.

### 12.7 The blueprint's ArkLib table cites the PMF form of Schwartz–Zippel that the new pin restated (note)

*Evidence.* `bp:250`: "`MvPolynomial.schwartz_zippel_counting`, `prob_eval_zero_le_div`
(`Data/MvPolynomial/SchwartzZippelCounting.lean`) — every per-challenge error bound." At
`7653a901` the first is `schwartz_zippel_counting` in the root namespace (`:29`; lib-arklib G.6
already noted the wrong namespace), and `prob_eval_zero_le_div` (`:114-124`) is now stated as
`Pr{let x ← $ᵗ (∀ i, ↥(S i))}[… = 0] ≤ d/m` with `[SampleableType …]`, plus
`prob_eval_zero_univ_le_div` (`:138`) for full carriers — the VCVio form leanerVM's
`ToVCVio/UniformSample.lean` bridged locally at the old pin.

*Proposed change.* Correct the names and note that the bridge for non-subsingleton bad sets is
now upstream; keep `UniformSample.lean` for its subsingleton specialization or derive it.

### 12.8 The status's upstream-watch table is out of date on eight rows (minor; docs)

*Evidence.* `status:186-206` ("checked 2026-09-24"): #615 "open since 2026-09-08" (opened
2026-07-07); #818 "open since 2026-09-04" (2026-08-31); "#1128, #1129 … merged and the pin
bumped; the adapter is deleted then" (they are unmerged and do not replace the adapter's
role, 12.2); "#900, #901 … when the upstream pull requests open" (none opened; the leanerVM
side merged #38/#40/#41 and staged #39/#43); the "ArkLib `main`" row now describes the pin;
missing rows for #1214/#1242/#1243 (merged, at the pin), #1244, #1245, #1251 (open), VCVio
#571 (Merkle), and #907 (closed, complete). The blueprint's pins table changed at `144c5aa`
("6 lines", brief §8) and nothing else.

*Proposed change.* Rewrite the table from section 11 of this dossier at the next status
rewrite.

## 13. Negative results, and what could not be verified

Checked and found as the blueprint says (no finding):

- Ledger A2, A4, A5 (the admits), A7 ("absent, only coding-theory lemmas" — for WHIR), A9
  (leaves admitted): confirmed at both pins by the baselines and by reading the files.
- The status's "the spine stays on `OracleReduction`, whose security definitions the new
  executor does not yet carry" (`status:201`): confirmed (section 10).
- The status's "GKR: to open (ArkLib #818 is a different protocol shape)" (`status:180`):
  confirmed (4.d).
- The blueprint's `Component.ReduceClaim`, `CheckClaim`, `RandomQuery`, `DoNothing` "all
  proved" (`bp:244`): confirmed at the new pin (no `sorry` in the four files; `SendClaim.lean`
  has one, `SendWitness.lean` six, `NoInteraction.lean` one — none consumed by the spine).
- `Verifier.fiatShamir`, `Commitment.Scheme`, `MLE`/`eqTilde`, `ProtocolSpec`, `OracleInterface`:
  present at the new pin with the shapes the spine uses (also lib-arklib F.2).

Unverified (what would verify it):

- That the typed trees' theorems depend on the three standard axioms only: three consistent
  sources (baseline, `grep`, the pull requests' reports), no probe (a probe `#print axioms
  Sumcheck.Interaction.Native.execute_soundness` under the lock would).
- Whether `johnsonExceptionCount` at leanVM's parameters is within Annex B's error budget (a
  numeric evaluation of `FiniteBounds.lean:66-108` at `ρ ∈ {1/2,…,1/16}`, `n = 2^{κ+R}`,
  `η` as Annex B chooses it; the gt-opening-compile scratch `whir_params.py` gives the
  parameters).
- Whether CompPoly's `BF64` at `572f9973` provides `Algebra (ZMod 2) BF64` and a basis indexed
  by `Fin 6 → Fin 2` for `tensorProductProfile` (read `CompPoly/Fields/Binary/`).
- The closeness-to-merge judgements are inferences from review state, conflict state, dates
  and the maintainers' comments; none is a statement by a maintainer about a date.
- The fit of VCVio's `NodeQueryModel` with leanVM's untagged fixed-height trees (a definition
  to write).

