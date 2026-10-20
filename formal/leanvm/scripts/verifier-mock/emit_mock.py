import os, sys, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

overrides, events, reads, samples = pickle.load(open(sys.argv[1], "rb"))
shapes = {}
roots = set()
for ev in events:
    if ev[0] == "q":
        shapes[ev[1]] = (ev[2], ev[3])
    if ev[0] == "c":
        roots.update((ev[2], ev[3]))
trace = []
for ev in events:
    if ev[0] == "r":
        if ev[1] not in roots:
            trace.append("r")
    elif ev[0] == "s":
        trace.append("s")
    elif ev[0] == "g":
        trace.append(f"g{ev[1]};")
    elif ev[0] == "c":
        h, w = shapes[ev[1]]
        trace.append(f"c{h},{w};")
    elif ev[0] == "q":
        trace.append(f"q{ev[1]}:" + ",".join(map(str, ev[4])) + ";")
s = "".join(trace)
chunks = [s[i:i + 88] for i in range(0, len(s), 88)]
name = sys.argv[2]
out = []
out.append(f"/-- The prover messages the mock prover fixed (stream index, value). -/\ndef {name}Overrides : List (ℕ × E) :=\n  " +
           wrap([f"({k}, {le(v)})" for k, v in sorted(overrides.items())], "  "))
out.append(f"/-- The stream indices of the root halves, which are commitments here. -/\ndef {name}Roots : List ℕ := {lnat(sorted(roots))}")
out.append(f"/-- The number of scalars the Python read, root halves included. -/\ndef {name}Reads : ℕ := {reads}")
out.append(f"/-- The number of challenges the Python drew. -/\ndef {name}Samples : ℕ := {samples}")
out.append(f"/-- The Python's run, event by event. -/\ndef {name}Trace : String :=\n  " + " ++\n  ".join(f'"{c}"' for c in chunks))
open(sys.argv[3], "w").write("\n\n".join(out) + "\n")
print(len(s), len(roots), shapes)
