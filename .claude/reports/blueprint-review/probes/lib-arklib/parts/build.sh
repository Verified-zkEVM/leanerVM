#!/bin/bash
# Assembles the dossier from its parts and the probe files. Scratch tool of the review.
cd /home/scaraven/Documents/Verified-zkEVM/leanerVM/.claude/reports/blueprint-review || exit 1
P=probes/lib-arklib
{
for f in $P/parts/[0-9]*.md; do cat "$f"; echo; done
echo "## Appendix: the probes"
echo
echo 'Every probe was run from the root of leanerVM (`main` at `b435631`, ArkLib at the pin'
echo '`dca90385`) with'
echo
echo '    flock .claude/reports/blueprint-review/logs/lean.lock lake env lean .claude/reports/blueprint-review/probes/lib-arklib/<File>.lean'
echo
echo 'The output is reproduced after each source. Axioms reported as `[propext, Classical.choice,'
echo 'Quot.sound]` are the three standard axioms of Lean and Mathlib; `sorryAx` marks an admitted proof.'
for f in AxiomsLeanerVM AxiomsArkLibBuilt NonVacuity PlainReading Extractors ExtractorsExpectedFailure; do
echo
echo "### Probe \`$f\`"
echo
echo "Source (\`$P/$f.lean\`):"
echo
echo '```lean'
cat $P/$f.lean
echo '```'
echo
echo "Output:"
echo
echo '```text'
grep -v "^real\|^user\|^sys\|^$" $P/$f.out
echo '```'
done
} > dossiers/lib-arklib.md
wc -l dossiers/lib-arklib.md
