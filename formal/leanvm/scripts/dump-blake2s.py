#!/usr/bin/env python3
"""Dump the BLAKE2s constants and compression vectors used by Layer 1 of the leanISA roadmap.

`constants` extracts `blake2s_iv` and `sigma` from the BLAKE2s reference source in RFC 7693
Appendix D and prints them as Lean vectors. `vectors` prints compression-level vectors derived
from `hashlib.blake2s`, which wraps the BLAKE2 authors' reference implementation and supports
the tree-mode `last_node` flag. Both outputs are pasted verbatim into the Lean sources named
in the output header; this script is the record of how they were produced.

Usage:
    python3 scripts/dump-blake2s.py constants [path/to/rfc7693.txt]
    python3 scripts/dump-blake2s.py vectors

Without a path, `constants` downloads https://www.rfc-editor.org/rfc/rfc7693.txt.
"""

from __future__ import annotations

import hashlib
import re
import struct
import sys
import urllib.request

RFC_URL = "https://www.rfc-editor.org/rfc/rfc7693.txt"
RFC_SHA256 = "c943754888364fe29bbd0bb3c71c6658ef392371497eaa4a9d9dde015b0721e5"

# BLAKE2s-256 unkeyed, sequential mode: parameter word 0 is
# digest_length | key_length << 8 | fanout << 16 | depth << 24 = 0x01010020 (RFC 7693 §2.8).
PARAM_WORD0 = 0x01010020
BLOCK_BYTES = 64


def rfc_text(path: str | None) -> str:
    data = open(path, "rb").read() if path else urllib.request.urlopen(RFC_URL).read()
    digest = hashlib.sha256(data).hexdigest()
    if digest != RFC_SHA256:
        sys.exit(f"RFC 7693 text has SHA-256 {digest}, expected {RFC_SHA256}")
    return data.decode("ascii")


def constants(path: str | None) -> None:
    text = rfc_text(path)
    appendix = text[text.index("Appendix D.  BLAKE2s Implementation C Source") :]
    iv_src = re.search(r"blake2s_iv\[8\]\s*=\s*\{([^}]*)\}", appendix).group(1)
    iv = re.findall(r"0x[0-9A-Fa-f]{8}", iv_src)
    sigma_src = re.search(r"sigma\[10\]\[16\]\s*=\s*\{(.*?)\};", appendix, re.S).group(1)
    sigma = [
        [int(n) for n in re.findall(r"\d+", row)] for row in re.findall(r"\{([^}]*)\}", sigma_src)
    ]
    assert len(iv) == 8 and len(sigma) == 10 and all(sorted(r) == list(range(16)) for r in sigma)
    print("-- LeanerVM/Parameters/Blake2s.lean (`scripts/dump-blake2s.py constants`)")
    print("def iv : Vector UInt32 8 := #v[")
    print("  " + ", ".join(w.lower() for w in iv[:4]) + ",")
    print("  " + ", ".join(w.lower() for w in iv[4:]) + "]")
    print()
    print("def sigma : Vector (Vector (Fin 16) 16) 10 := #v[")
    for i, row in enumerate(sigma):
        sep = "," if i < 9 else "]"
        print("  #v[" + ", ".join(f"{n:2d}" for n in row) + "]" + sep)


def words(data: bytes) -> list[int]:
    return list(struct.unpack("<%dI" % (len(data) // 4), data))


def lean_words(ws: list[int]) -> str:
    return "#v[" + ", ".join(f"0x{w:08x}" for w in ws) + "]"


def vectors() -> None:
    print("-- tests/LeanerVMTests/Semantics/Blake2s.lean (`scripts/dump-blake2s.py vectors`)")
    print(f"-- h0 = iv with word 0 xor 0x{PARAM_WORD0:08x}; blocks are zero-padded to 64 bytes.")
    cases = [(b"", "empty"), (b"abc", "abc"), (bytes(range(BLOCK_BYTES + 1)), "twoBlocks")]
    for msg, name in cases:
        blocks = [msg[i : i + BLOCK_BYTES] for i in range(0, max(len(msg), 1), BLOCK_BYTES)]
        for last_node in (False, True):
            digest = hashlib.blake2s(msg, last_node=last_node).digest()
            suffix = "LastNode" if last_node else ""
            print()
            print(f"-- {name}{suffix}: {len(msg)} bytes, {len(blocks)} block(s), "
                  f"last_node={str(last_node).lower()}; digest {digest.hex()}")
            for k, block in enumerate(blocks):
                final = k == len(blocks) - 1
                counter = len(msg) if final else (k + 1) * BLOCK_BYTES
                padded = block + bytes(BLOCK_BYTES - len(block))
                print(f"-- block {k}: t = {counter}, f0 = {str(final).lower()}, "
                      f"f1 = {str(final and last_node).lower()}")
                print(f"--   m = {lean_words(words(padded))}")
            print(f"--   digest words = {lean_words(words(digest))}")


def main(argv: list[str]) -> int:
    if len(argv) >= 2 and argv[1] == "constants":
        constants(argv[2] if len(argv) > 2 else None)
        return 0
    if len(argv) == 2 and argv[1] == "vectors":
        vectors()
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
