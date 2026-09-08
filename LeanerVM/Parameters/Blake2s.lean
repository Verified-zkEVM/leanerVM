/-
  LeanerVM.Parameters.Blake2s

  The BLAKE2s constants: the initialization vector and the message schedule.
-/

module

/-!
# BLAKE2s constants

Category B. Transcribed from RFC 7693, *The BLAKE2 Cryptographic Hash and Message Authentication
Code (MAC)*, §2.6 (initialization vector `IV`) and §2.7 (message schedule `SIGMA`), taking the
numerical values from the BLAKE2s reference source in Appendix D (`blake2s_iv`, `sigma`).
Both tables were dumped mechanically by `scripts/dump-blake2s.py constants` from
https://www.rfc-editor.org/rfc/rfc7693.txt (SHA-256
`c943754888364fe29bbd0bb3c71c6658ef392371497eaa4a9d9dde015b0721e5`) and pasted verbatim.

The pinned leanVM carries the same tables at `crates/primitives/src/hash.rs:19-49`
(`IV`, `SIGMA`, commit `a386121f84292f6fa663aaa3e570c15bc0240ea2`); the RFC is the authority
cited here, and `tests/LeanerVMTests/Parameters/Blake2s.lean` checks `iv` against the RFC's
defining formula and `sigma` for being ten permutations.
-/

namespace LeanerVM.Parameters

@[expose] public section

/-- The BLAKE2s initialization vector, RFC 7693 §2.6: `IV[i] = ⌊2^32 · frac(√pᵢ₊₁)⌋` for the first
eight primes, the SHA-256 IV. -/
def iv : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The BLAKE2s message schedule, RFC 7693 §2.7: `sigma[r]` is the permutation of the sixteen
message words consumed by round `r`. -/
def sigma : Vector (Vector (Fin 16) 16) 10 := #v[
  #v[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
  #v[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
  #v[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
  #v[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
  #v[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
  #v[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
  #v[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
  #v[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
  #v[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
  #v[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]]

end
end LeanerVM.Parameters
