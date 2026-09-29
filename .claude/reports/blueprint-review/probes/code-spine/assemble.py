#!/usr/bin/env python3
"""Assemble dossiers/code-spine.md from the fragments in dossier/ and the probe sources."""
import glob, os
here = os.path.dirname(os.path.abspath(__file__))
out = os.path.join(here, '..', '..', 'dossiers', 'code-spine.md')
parts = []
for f in sorted(glob.glob(os.path.join(here, 'dossier', '*.md'))):
    parts.append(open(f).read().rstrip() + '\n')
app = ['## Appendix: the probes, in full\n',
       'Every probe is a plain Lean file under `.claude/reports/blueprint-review/probes/code-spine/`, '
       'run from the repository root (leanerVM `main` at `b435631`, ArkLib `dca90385`) with\n',
       '```sh\nflock .claude/reports/blueprint-review/logs/lean.lock lake env lean '
       '.claude/reports/blueprint-review/probes/code-spine/<File>.lean\n```\n',
       'The output of each run is the file `<File>.out` beside it, reproduced below the source. '
       'An empty output with `exit=0` means every `#guard`, `example` and theorem of the file was accepted.\n']
for f in sorted(glob.glob(os.path.join(here, 'P*.lean'))):
    name = os.path.basename(f)
    app.append(f'### `{name}`\n')
    app.append('```lean\n' + open(f).read().rstrip() + '\n```\n')
    o = f[:-5] + '.out'
    if os.path.exists(o):
        app.append('Output:\n')
        app.append('```text\n' + open(o).read().rstrip() + '\n```\n')
    else:
        app.append('Output: not recorded.\n')
parts.append('\n'.join(app))
open(out, 'w').write('\n'.join(parts))
print('wrote', os.path.normpath(out), sum(len(p) for p in parts), 'bytes')
