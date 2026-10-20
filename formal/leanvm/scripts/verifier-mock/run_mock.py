import os, sys, time, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mock import *

bytecode = [K(fw(i, 9)) for i in range(32)]
pi = V.Digest(bytes(fw(i, 10) % 256 for i in range(32)))
heights = [2, 1, 1, 2, 2, 3]
overrides = {0: E(16), 7: E(int(sys.argv[2]))}
for t, h in enumerate(heights):
    overrides[1 + t] = E(h)
m = solve(bytecode, pi, overrides)
pickle.dump((overrides, m.events, m.reads, m.samples_n), open(sys.argv[1], "wb"))
print("reads", m.reads, "samples", m.samples_n, "overrides", len(overrides))
