import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

bytecode = [K(fw(i, 9)) for i in range(32)]
pi = V.Digest(bytes(fw(i, 10) % 256 for i in range(32)))
heights = [2, 1, 1, 2, 2, 3]

def stream(rate, n):
    s = [E(16)] + [E(h) for h in heights] + [E(rate)]
    s += [E(fw(8, 0), fw(8, 1)), E(fw(9, 0), fw(9, 1))]   # canonical root halves
    s += [fe(k) for k in range(10, 10 + n)]
    return tuple(s)

iv = V.blake2s_hash(b"leanvm" + V.pack("<Q", len(V.R1CS_DIGEST)) + V.R1CS_DIGEST + V.blake2s_hash(b"".join(w.to_bytes() for w in bytecode)).value)
t = V.Transcript(V.Proof(stream(4, 0), b""), iv, pi)
t.next_scalars(8)
root = V.Digest.from_halves(*t.next_scalars(2))
samples = t.samples(5)
print("#guard (prefixSamples) =\n    " + llist(samples))
st = t.state
print("-- state words", [hex(w) for w in st])
words32 = []
for w in st:
    words32 += [w & 0xFFFFFFFF, w >> 32]
print("#guard (prefixState) =\n    " + wrap([f"0x{w:08x}" for w in words32]))
for rate, n in ((4, 0), (4, 100), (5, 100)):
    try:
        V.verify_execution(bytecode, pi, V.Proof(stream(rate, n), b""))
        print("-- accepted?!")
    except V.VerificationError as exc:
        print(f"-- rate {rate}, {n} extra scalars: {exc}")
