# Dossier `lib-arklib`: ArkLib's framework for interactive oracle reductions at the pin

Task: what ArkLib's oracle-reduction framework defines, proves and admits at the pin, whether
its security notions are an adequate model, and what leanerVM's master theorems mean in
cryptographic terms.

Revisions: leanerVM `main` at `b435631` (the object of the review; the checkout now also holds
`144c5aa`, the Lean 4.34.1 upgrade, section F); ArkLib at the old pin `dca90385` (every
snippet, read in `.lake/packages/Arklib` before the upgrade or with `git show dca90385…:` after
it) and at the new pin `7653a901` (section F; it is the commit this dossier had read as
`origin/main`); pull request #615 at `ca7a2577`; VCVio `f9dc47d9` (old) and `a4232d08` (new).
Every probe (appendix) ran at the old pin; none could be re-run after the upgrade.

## Summary

**What the master theorem means.** `piop_rbrKnowledgeSoundness` says (D.1, with the
transcript-level half proved by probe `PlainReading`): *for every public input and every
transcript, if the verifier accepts then the stack sent as the first message satisfies
`M3Holds`, unless some challenge of the transcript lies in the bad set of its prefix, and every
bad set has probability at most `piopError` of its round.* The probability is over one uniform
challenge at a time, at every prefix (the worst-case form); no prover appears. The step from
this to "an interactive prover convinces the verifier without a good first message with
probability at most `Σ piopError`" is a union bound that ArkLib admits at both pins
(`rbrKnowledgeSoundness_implies_knowledgeSoundness`); the step to Fiat–Shamir security is
stated nowhere in ArkLib. At the oracle-protocol level this is soundness with respect to the
committed oracle; knowledge (extracting the stack from a commitment) belongs to the compiled
protocol, for which ArkLib offers no theorem (`BCSTransform` commented out,
`Commitment.extractability` a placeholder whose body is `False`).

**The definition is adequate with one caveat that matters.** It matches the literature's
round-by-round knowledge soundness (Block et al. 2023, Definition 3.13, quoted in D.2) in its
worst-case-per-prefix form and its per-round errors, with one difference: ArkLib's extractor is
any function, classical choice included. In the existential forms the notion is therefore
soundness only (probe `Extractors`: knowledge soundness at error 0 with an extractor that
computes nothing, for any relation). leanerVM's named form is adequate together with the
reading of the named extractor, which for the spine is "return the first message" and which
compiles (probe `Extractors`). Non-vacuity holds: an accept-everything verifier has no
knowledge state function (no round) and is not knowledge sound at error 0 (one challenge); it is
knowledge sound at error 1, as every verifier is, so the error term is what carries content and
the planned `piopError_le` is the load-bearing companion (probe `NonVacuity`).

**What is proved and admitted.** leanerVM's master theorems, both phases, the composition and
the port depend on the three standard axioms only (probe `AxiomsLeanerVM`). ArkLib admits, at
both pins, the composition of every soundness notion, the round-by-round ⇒ plain implications,
context lifting, Fiat–Shamir completeness (stated, moreover, for a *constant* challenge oracle),
and the sumcheck specification's completeness and knowledge soundness (B.3, F.1). The local
port of #615's guarded-first knowledge append is the pull request's file up to headers, the
module system, docstrings and dropped wrappers (C.1); #615 is open and in conflict; ArkLib now
calls `OracleReduction` legacy and builds a typed framework that has no knowledge notion (F.2).

**Findings** (section G): G.1 *existential round-by-round knowledge soundness has no knowledge
content* (critical as a warning about the definition; leanerVM's named form is safe with the
extractor check); G.2 *the spine's completeness cannot carry an error, and Flock may need one*
(major); G.3 *the blueprint plans on a framework upstream calls legacy and on a pull request
that may not merge* (major); G.4 *no ArkLib statement can serve as the Fiat–Shamir/BCS witness
obligation, and `Verifier.fiatShamir` does not describe the compiled verifier* (major); G.5
*the error bundled in `Component.Def` makes every phase and the composed verifier and extractor
noncomputable* (minor); G.6 *names and line references in the ArkLib table* (minor); G.7, G.8
notes on derivable side conditions and re-implemented components; G.9 negative results.
