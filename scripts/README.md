# Scripts

- `validate.sh`: complete local gate and the command to run before handoff.
- `audit-lean.sh`: first-party lexical policy for trust-sensitive constructs and local
  option overrides.
- `check-repository.sh`: rejects executable Lean sources, case-colliding paths, and
  trailing whitespace.
- `check-imports.sh`: verifies that `LeanerVM.lean` and `tests/LeanerVMTests.lean` list every
  production or test module exactly once and contain no stale imports.
- `check-layers.sh`: enforces the allowed Lean layer dependency direction and rejects unregistered
  production layers.
- `check-docs.py`: validates local Markdown links without third-party Python packages.
- `test-policy-checks.py`: plants isolated violations to exercise the source, aggregate-import,
  and layer gates.
- `build_timing.py`: records timed commands as JSONL and renders a Markdown summary.
- `test-build-timing.py`: exercises successful, failing, and reporting timing paths.
- `check-upstreams.sh`: compares `upstreams.json` with current releases and branch heads;
  requires `gh`, `jq`, and network access.

Keep scripts small and deterministic. Add specialized tooling only with the feature or
artifact it validates.
