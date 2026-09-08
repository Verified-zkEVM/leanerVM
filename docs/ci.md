# Continuous integration

The CI layout borrows the useful separation of concerns from ArkLib, VCVio, and leanth while
keeping only checks justified by leanerVM's current Lean-only surface.

| Workflow | Responsibility | Branch-protection status |
| --- | --- | --- |
| `CI` | Build with the Actions and Mathlib caches, run the Lake test driver, and elaborate the test root with warnings as errors | Required |
| `Repository policy` | Audit Lean trust markers and repository hygiene, and exercise planted policy violations | Required |
| `Imports and layers` | Keep the aggregate import complete and enforce the architecture DAG | Required |
| `Documentation integrity` | Reject broken or unsafe local Markdown links | Required |
| `Build timing` | Measure clean build, warm build, and test-path wall time | Informational |
| `PR summary` | Post an automated summary using policy from the trusted base revision | Informational |
| `PR review` | Run a member-triggered `/review` pass | Informational |
| `Upstream drift` | Report newer Lean and tracked library releases each week | Informational |

Configure branch protection with the four required checks above after publishing the
repository. Do not make timing a merge gate: hosted-runner timings are noisy and the retained
JSONL and logs are evidence for trends, not deterministic pass/fail thresholds. This initial
workflow reports the current run; exact-base comparisons and PR comments can be enabled once
the new repository has a useful history of successful main-branch timing artifacts.

`PR summary` and `PR review` require an `OPENROUTER_KEY` Actions secret. Summary uses
`pull_request_target` without checking out or executing pull-request code. Review is restricted
to `/review` comments from owners, members, and collaborators; it may inspect pull-request code,
so only trusted members should invoke it on an untrusted fork.

Project releases are milestone-driven. A Lean toolchain update is an ordinary reviewed dependency
change and does not create or move a release tag. Release automation should be introduced only
when the project has a concrete milestone release process to automate.

Workflows have read-only repository contents unless they must post pull-request output.

Native/FFI isolation, CUDA, generated-blueprint, and VM-runtime benchmark jobs are deliberately
absent. Add each only alongside the artifact it protects. Runtime benchmarks should follow the
contract in [../bench/README.md](../bench/README.md).
