## G. What was not verified, and what would verify it

| Claim | Status | What would verify it |
| --- | --- | --- |
| The relation of `toyAlias` is empty for every stack and statement (D.4) | evidence by an exhaustive `#guard` over cells `0, 1` and statements in `{0, 1, 2}` at the old pin; the paper argument is two lines | a theorem `∀ input q, ¬ M3Holds toyAlias input q`, whose proof needs CompPoly's evaluation of `X 0` on a row (no `eval_X` lemma at `3468b38c`; the sibling dossiers may have one) |
| `Layout.read` is determined by `extend` (C.2) | on paper | a lemma `read_eq_of_extend` from CompPoly's `eval_mle_eq_eval` (cited in `Field.lean:50`) |
| An always-rejecting bundle has no `Phases.Security` on an instance with an inhabited relation (D.3 (c)) | a reading of `Security extends Complete` and of `perfectCompleteness` | a probe with a rejecting zero-round verifier and `perfectCompleteness_eq_prob_one` |
| The read-everything phase inhabits `Phases.Security I` at error `0` for every `I` (D.3 (d)) | on paper; agrees with `gt-table-pub.md` section 6 | a probe on an instance with `μ = 0`: one oracle query, `if decide (relIn s ⟨#v[v.limb 0]⟩) then pure (f s) else failure`, with `Verifier.GuardedForm.of_probEvent_pos` for the state function |
| The probes that use `(2 : K)` mean the same at the new CompPoly pin | they do not (`(2 : K) = 0` there, brief §8); their conclusions are about `b435631` with the old pins, where `2 : K` is the polynomial `x` (`tests/…/Spine.lean:30`) | re-run `P2Relation`, `P3aSeams`, `P5PassThrough` with `K.ofBits 2` after the rebuild |
| Line numbers of `Field.lean` and `KnowledgeAppend.lean` | at `b435631` (the working tree had moved by the time the counting script first ran; the script was re-run on `git show b435631:` and the numbers in sections B and C are from that run) | — |
| The earlier review's validation paragraph (`docs/reviews/protocol-spine.md:19-28`) | not re-run (no build allowed); `#print axioms` re-established by probe P1 for the declarations listed there and more | `./scripts/validate.sh` on `b435631` |
