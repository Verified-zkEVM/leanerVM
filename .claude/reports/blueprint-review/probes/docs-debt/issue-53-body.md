Tracks #12. Hole **C1**: inhabit the spine's `KnowledgeAppend` interface, ledger A2. Pure ArkLib work; no leanVM object.

**What is owed.** At the pin `dca90385` (and still on ArkLib `main`, 2026-09-24) `Verifier.append_rbrKnowledgeSoundness`, `seqCompose_rbrKnowledgeSoundness` and the append of knowledge state functions are admitted (`Composition/Sequential/Append/Security.lean`, issue ArkLib #676). Round-by-round *soundness* of an append with a pure first verifier is proved (`append_rbrSoundnessWorstCase_of_pure_first`). Every leanVM phase verifier is a pure public-coin check, hence guarded.

**Produces:** either (a) `append_rbrKnowledgeSoundnessWorstCase_of_guarded_first` and its n-ary form under `LeanerVM/Protocol/Generic/KnowledgeAppend.lean`, mirroring the proved soundness version, upstreamed to ArkLib; or (b) a pin bump adopting ArkLib #615, which contains `Append/Knowledge.lean` (`append_rbrKnowledgeSoundnessWorstCase_of_guarded_first`) and `KnowledgeNary.lean` (`seqCompose_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_verifiers`), once it merges. In both cases the deliverable is one term of type `KnowledgeAppend`.

**Consumes:** the spine's `KnowledgeAppend` statement (written in #615's shape so that (b) is a substitution).

**Upstream watch:** ArkLib #615 (open, 2026-09-08, ~100 files; the knowledge-append files are separable), ArkLib #676 (the umbrella), ArkLib #926 (lift-context obligations; not consumed).

**Claim** by assigning yourself.
