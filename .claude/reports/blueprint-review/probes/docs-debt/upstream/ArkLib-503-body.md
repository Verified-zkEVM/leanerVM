Hi,

I'm interested in implementing LogUp in ArkLib. I have been working on the protocol recently and now have an implementation, together with empty correctness proofs. I would be happy to continue working on this if you think it would be useful.

I'm sharing the current state of the work here in the hope of getting some feedback: whether the overall direction looks reasonable, and what the best next steps would be from the perspective of someone more experienced with the library.

Here is a short overview of the files:

- `Protocol.lean` - defines the prover, verifier, and the full LogUp protocol as an ArkLib reduction.
- `Sumcheck/SumcheckPolynomial.lean` - constructs the polynomial used by the prover in the sumcheck phase and proves that it has sufficiently low degree.
- `Sumcheck/SumcheckBridge.lean` - connects that polynomial to ArkLib's existing sumcheck infrastructure.
- `Security/Completeness.lean` and `Security/Soundness.lean` - state the completeness and soundness theorems. The proofs are currently left as sorry.

There is also one TODO about sampling a challenge, which I am slightly unsure how to handle, but I will try to work it out.

I would be very grateful for any feedback. Even a quick indication of whether this is something the project would currently be interested in would already be very helpful.