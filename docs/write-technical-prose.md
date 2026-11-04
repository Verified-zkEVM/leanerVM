# Writing workflow

Use this workflow for leanerVM documentation, comments, docstrings, commit messages, PR and issue
text, and review comments. Work within the requested scope. A prose task does not authorize
publication or unrelated source changes.

1. **Read the source before stating a claim.** Read [CONTRIBUTING.md](../CONTRIBUTING.md) for
   contribution requirements. Inspect the relevant definitions, hypotheses, proofs, and test
   evidence. For implementation claims, read the pinned source and the
   [target map](leanvm-target.md). Distinguish a formal theorem from evidence about the Rust
   implementation. State which checks ran and what remains uncertain.
2. **Start with what the reader needs.** State the problem, result, or action first. Develop one
   topic per paragraph. Use the [guide](writing.md) and [vocabulary](writing-vocabulary.md) when
   they help; their advice is not a conformance test. CONTRIBUTING owns titles, PR descriptions,
   docstrings, citations, and proof requirements.
3. **Revise real problems.** Identify a clarity or accuracy problem before changing a passage.
   Keep established terms, hypotheses, quantifiers, conditions, uncertainty, and requirement
   strength. Repository habit alone does not justify unclear wording.
4. **Compare complete passages.** Read the old and new paragraphs side by side in context.
   Compare contribution instructions as carefully as mathematical claims. Keep the meaning,
   conditions, and scope, and explain why the revision is clearer. Check changed links and
   references, then read the final passage.
5. **Leave correct text alone.** The optional checker offers suggestions, not a judgment of
   clarity, accuracy, or STE conformance. Read each suggestion in context. Do not change clear,
   correct text to silence it.

## Optional local suggestions

Run these commands from the repository root, with [uv](development.md#python-tooling):

```sh
uv run --no-project --python 3.12 python scripts/check-writing.py --base origin/main
uv run --no-project --python 3.12 python scripts/check-writing.py docs/writing.md
uv run --no-project --python 3.12 python scripts/check-writing.py --stdin description < /tmp/pr-description.md
git log origin/main..HEAD --format='%s%n%b' > /tmp/leanervm-commits.txt && \
  uv run --no-project --python 3.12 python scripts/check-writing.py --stdin commits < /tmp/leanervm-commits.txt
```

For stacked work, replace `origin/main` with the actual parent branch in both commands. The
commit-message command runs the checker only if `git log` succeeds. Keep drafts and temporary
files outside the contribution.

The checker runs locally, and no CI job or merge check runs it. Suggestions return 0. Input
notices report unsupported encodings or symlinks without failing the run. Usage, Git, and
vocabulary-configuration errors return 2. Counts and source extraction are approximate.

In diff mode, it checks tracked Markdown and Lean prose in paragraphs with added lines. It skips
`docs/reviews/`, which holds historical review records, dependency output under `.lake/`, and
the two import-only aggregate files. It gives no history-word suggestions in `docs/roadmap/`.
An explicit file argument can review an archive when that is the requested task.

The `Licensing` and `Porting and attribution` sections of CONTRIBUTING are excluded from wording
suggestions. The latter combines attribution and licensing duties with engineering guidance;
review the complete section manually to preserve the conditions on ported material. License
files and copyright-notice sections are also excluded. JSON metadata and external dump captures
are not diff-mode prose candidates. Generated values inside maintained Lean files remain code;
the surrounding authored comments can still receive suggestions.

If you change the checker, run its tests:

```sh
uv run --no-project --python 3.12 python -B scripts/test-writing.py
uv run --no-project --python 3.12 python -B -O scripts/test-writing.py
```

If the task includes a commit or handoff, run the validation required by CONTRIBUTING and
[development.md](development.md). This workflow adds no second contribution policy.
