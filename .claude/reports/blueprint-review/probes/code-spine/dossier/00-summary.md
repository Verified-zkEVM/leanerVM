# Dossier: the spine as built (task `code-spine`)

**Object reviewed:** leanerVM `main` at `b435631` — the five spine modules
`LeanerVM/Protocol/Spine/{Instance,Seams,Phase,Compose,Toy}.lean`, the generic modules
`LeanerVM/Protocol/ToArkLib/{Oracles,Component,PassThrough,SendOracle,Refinement,GuardedVerdict,KeepOracles}.lean`,
the statements of `ToArkLib/KnowledgeAppend.lean`, `Protocol/Field.lean` where the spine
unfolds to it, `Protocol/PublicInput.lean` where a probe needed a real phase, and
`tests/LeanerVMTests/Protocol/Spine.lean`; the blueprint's headline, "For zkVM engineers",
conventions, "The spine" with its sketch, Layers 3 and 6 to 13, acceptance tests 24 to 28 and
the interface list; the earlier review `docs/reviews/protocol-spine.md`; the ArkLib, VCVio and
CompPoly definitions the statements unfold to, at the pins ArkLib `dca90385`, CompPoly
`3468b38c`, VCVio `f9dc47d9`; the specification at leanVM `a386121f` (§3 Definition 3.13, §4,
§5, §6, §8).

**Ground moved during the review** (brief §8): the checkout now holds `main` at `144c5aa`
(Lean 4.34.1, all pins moved). Everything here is about `b435631`; every Lean line number is
`git show b435631:<path>`. All seven probes (`P1` to `P6`, with `P3` in three files) were run
and recorded **before** the move, at `b435631` with the old pins; their outputs are in the
appendix. Three probes (`P2Relation`, `P3aSeams`, `P5PassThrough`) use the numeral `(2 : K)`,
which at the old pin is the polynomial `x` (nonzero, not Boolean) and at the new CompPoly pin
is `0`; they must be re-run with `K.ofBits 2` after a rebuild, and the conclusions they support
are marked accordingly. One probe was planned and not written (the read-everything phase,
D.3 (d)); the sibling dossier reaches the same conclusion on paper.

## 0. Summary

**Conclusions.**

1. **No theorem of the spine is wrong for what it states**, every stated theorem is proved with
   the kernel's three standard axioms (probe P1), and `M3Holds` says what the specification's
   accept list says (C.1, clause by clause against the tex at the pin). The repository's tests
   establish non-vacuity of the four checkable clauses by value changes only; the probes add
   the two multiplicity cases (a tuple pushed twice and pulled once; pushed twice and never
   pulled, where a field-summed balance accepts), the side filter, and the row ranges (D.1).
   No defect found in the relation as a definition.
2. **The master theorems are composition theorems and their hypotheses are cheap to meet.**
   `Phases.Security toy` is inhabited by five phases that draw a challenge, check nothing and
   declare error `1` (probe P4, machine-checked, instance-independent); both master theorems
   hold of that protocol. Nothing in the spine bounds `piopError`, and the blueprint's
   `piopError_le` is stated over an argument the spine's `piopError` does not take. A second
   cheap inhabitant, at error `0`, is the zero-round phase whose verifier reads the whole stack
   through the evaluation oracle and decides the input seam itself (on paper, agreeing with the
   sibling dossier). What pins the phases to leanVM's is outside the oracle protocol: a bound
   on the error, the phases' definitions, and Layer 12's `verify_iff_compiled` with its fixture.
3. **The pass-through bus phase has no `Phase.Security`** — the type is empty (probe P5,
   `no_security`), where the test's docstring only asserts it.
4. **The composed extractor's output is the stack only when every phase has no round.** With
   the repository's own public-input phase in the bundle, `piopExtractor … extractOut` has type
   `Unit` and the `rfl` witness of acceptance test 24 is ill-typed (probe P3c); the stack is
   `extractMid` at round 0. No definition "the extracted stack" exists, so the headline's "the
   extractor's column `q`" names nothing. A classical phase extractor would go unnoticed by
   every check and would not matter, since a phase's witness is `Unit` and the stack comes from
   the commit phase's computable extractor alone (D.5).
5. **A layout may alias columns and empty the relation** (probe P2, `toyAlias`, a `Layout`),
   and the reading law determines `read` from `extend` (C.2, on paper). The spine proves
   nothing about an instance beyond that law; only the toy's relation is known inhabited on
   `main`.
6. **`Seam.bus` as an input relation forces guards into the table phase's verifier** that
   leanVM's has not (the degree conjunct at the least; C.3). This agrees with the sibling
   dossier `gt-table-pub.md`, whose `BusOut` redesign we endorse; the smallest fix is a subtype
   of polynomials within the bound.
7. **The audit surface** (B): 70 declarations and 217 code lines (382 with docstrings) for
   perfect completeness; 76 and 248 (432) for knowledge soundness in its existential form; 100
   and 354 (612) for the named form. Proposals that keep every theorem's meaning: delete
   `outputPure` (derivable for every component over the empty oracle, probe P6), derive
   `Layout.read` from `extend`, drop `Weight.mle` from the seam, put the degree bound in a type;
   and read the existential theorem first.
8. **The blueprint states the same objects two or three times, differently** (E.2, fifteen
   rows): the headline's and Layer 10's theorems, Layer 6's `BusOut`, Layer 7's types, Layer
   9's `FlockInterface`, Layer 10's `Weight`/`WeightedClaim`/`leanVmPiop`/`piopError` are
   pre-spine sketches the code does not implement; the text beside them says the spine's
   version is authoritative, the blocks were not rewritten.
9. Two claims of the blueprint about what is *not* proved are wrong in the other direction:
   the probabilistic transport of knowledge along the adaptor is three lines in the event form
   (probe P6, `knowledge_transport`, no prover conversion needed), and `Refinement`'s two
   witness universes are independent (checked).

**Findings by severity** (section F, each with its evidence and proposed change):

- *major*: the declared error is unconstrained — `piop_rbrKnowledgeSoundness` has content only
  with a bound on `piopError`, and the spine has none (proposal: the closed form fixed by the
  spine as `piopError I`, each phase's security demanded at it; or a bound as a field of
  `Phases.Security`).
- *major*: the degree conjunct of `Seam.bus` is a guard the table phase's verifier must run
  (agreeing with the sibling dossier; type-level fix).
- *minor*: the headline describes theorems that do not exist on `main`.
- *minor*: the extracted stack is not a definition; acceptance test 24's witness covers
  zero-round phases only.
- *minor*: `outputPure` is redundant (ArkLib's `Prover.instOutputIsPureEmpty` at the pin);
  `read` is determined by `extend`; `Protocol/Basic.lean` imports the arithmetization outside
  the wall's exceptions.
- *note*: the instance is data the theorems trust; knowledge transport is three lines; two
  dispositions of the earlier review are met only in part.

**Negative results.** Checked and found in order: the five clauses against
`05-arithmetization.tex:10-16, 101, 111`, `06-bus-interactions.tex:74-78`,
`08-end-to-end-protocol.tex:29-33, 100`; the side filter, row ranges and multiplicity of
`Balanced` (probe P2); each seam inhabited and refuted per conjunct (probe P3a); the commit
phase's state function and extractor as documented (probe P3b); axioms of all load-bearing
declarations and computability of the extractor chain (probe P1); the sketch of the spine
against the code, name by name (E.1: matches, with omissions listed); the wall (E.3);
`Seam.done = Set.univ`.

**Not done.** The read-everything phase probe (D.3 (d)); the formal emptiness of
`toyAlias`'s relation (evidence by exhaustive guard over a small range, argument on paper);
`Layout.read` determined by `extend` (on paper); the always-rejecting verifier's exclusion (a
reading of `Security extends Complete`, not a probe).
