#!/usr/bin/env python3
"""Digest the rows of the Flock BLAKE2s circuit as the pinned Python verifier walks them.

`python-verifier/verifier.py` evaluates the circuit's two matrices only through
`blake2s_row_values`, a forward walk of the circuit against column weights. Run on the weights
`w_j = x^j` of a field of characteristic two represented as bitsets (addition is XOR), the walk
returns, for every row `k`, the bitsets of the positions in row `k` of `A` and of `B`. This
script prints the digest `sum_k (3 (A_k mod P) + 7 (B_k mod P)) (k + 1) mod P`, `P = 2^61 - 1`,
which `tests/LeanerVMTests/Protocol/Blake2sCircuit.lean` compares with the Lean circuit's rows
(`rowsDigest`), and the row statistics.

Usage:
    python3 scripts/dump-flock-circuit-digest.py path/to/leanVM

The leanVM checkout must be at the pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`. The output
at the pin is `digest 2129825626724647737`, `nonzero rows 15873`, `total terms 89305416`.
"""

from __future__ import annotations

import sys


class Bits:
    """An element of a characteristic-two field, as the bitset of its terms."""

    __slots__ = ("m",)

    def __init__(self, m: int) -> None:
        self.m = m

    def __add__(self, other: "Bits") -> "Bits":
        return Bits(self.m ^ other.m)

    __radd__ = __add__


def main() -> None:
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    sys.path.insert(0, f"{sys.argv[1]}/python-verifier")
    import verifier  # noqa: PLC0415

    verifier.ZERO = Bits(0)
    size = 2**verifier.BLAKE2S_R1CS_LOG_SIZE
    left, right = verifier.blake2s_row_values([Bits(1 << j) for j in range(size)])
    p = 2**61 - 1
    digest = 0
    for k in range(size):
        digest = (digest + ((left[k].m % p) * 3 + (right[k].m % p) * 7) * (k + 1)) % p
    print("digest", digest)
    print("nonzero rows", sum(1 for k in range(size) if left[k].m or right[k].m))
    print("total terms", sum(left[k].m.bit_count() + right[k].m.bit_count() for k in range(size)))


if __name__ == "__main__":
    main()
