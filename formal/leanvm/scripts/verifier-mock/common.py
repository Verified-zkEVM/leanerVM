"""Drivers that regenerate the Python-derived vectors of tests/LeanerVMTests/Protocol/Verifier.

Usage: extract the pinned verifier, then run a driver with `python3 -I`:
  git -C <leanVM> show 127510d14c98ade4e8a97646c44fa7f1ff5e752d:python-verifier/verifier.py > DIR/verifier.py
  LEANVM_VERIFIER_DIR=DIR python3 -I scripts/verifier-mock/run_mock.py
"""
import os
import sys
sys.path.insert(0, os.environ["LEANVM_VERIFIER_DIR"])
import verifier as V
from verifier import E, K

M = 2**64

def fw(k, lane):
    """The shared pseudo-random 64-bit word generator (mirrored in Lean as `fw`)."""
    return ((k + 1) * 0x9E3779B97F4A7C15 + lane * 0xD1B54A32D192ED03 + 0x632BE59BD9B4E019) % M

def fe(k):
    return E(fw(k, 0), fw(k, 1), fw(k, 2))

def le(x):
    if isinstance(x, K):
        return f"(k 0x{x.value:x})"
    x = E.lift(x)
    return f"(e 0x{x.c0.value:x} 0x{x.c1.value:x} 0x{x.c2.value:x})"

def wrap(items, indent="    "):
    one = "[" + ", ".join(items) + "]"
    if len(one) <= 90:
        return one
    lines, cur = [], ""
    for it in items:
        if cur and len(cur) + len(it) + 2 > 96 - len(indent):
            lines.append(cur + ",")
            cur = it
        else:
            cur = it if not cur else cur + ", " + it
    lines.append(cur)
    return "[" + ("\n" + indent + " ").join(lines) + "]"

def llist(xs, f=le):
    return wrap([f(x) for x in xs])

def lnat(xs):
    return wrap([str(x) for x in xs])
