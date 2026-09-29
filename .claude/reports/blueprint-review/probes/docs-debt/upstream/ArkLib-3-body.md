This issue hosts all relevant work for the sum-check protocol & the Spartan PIOP.

Currently, we have defined the specification for a single round of the sum-check protocol. The full sum-check protocol will be obtained by composing all the rounds together. This relies on general results about composition of reductions developed in #1.

The following are immediate targets to work on:

- [ ] Prove perfect completeness of a single sum-check round.
- [ ] Define state function for round-by-round (knowledge) soundness (for a single round).
- [ ] Prove round-by-round (knowledge) soundness (for a single round).

Once we finish sum-check, we will start work on formalizing Spartan.