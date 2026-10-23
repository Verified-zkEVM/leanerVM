import LeanVM.Protocol.Verifier

/-!
# The compiled verifier: the Fiat-Shamir sponge against the Python's, and garbage rejected

`verify` is the compiled reading of `leanVmProgram` with Keccak-256 and Keccak-f[1600]. The
honest proofs are the fixtures `tests/fixtures/verifier/*` (accepted by the compiled verifier
`leanvm-verify`, `scripts/fuzz-verifier.py`); this file checks the compiled reading where the
Python can be run without a proof, on the scalar stream `stream rate n`: the eight announced
sizes (memory `2^16`, the row counts `4, 2, 2, 4, 4, 8`, the rate exponent), two canonical root
halves, then `n` scalars `fe(10 + k)`.

* The seed and the sponge: the first two steps of the program (`readSizes`, `commitStack`) and
  five challenges, in the compiled reading, give the challenges and the sponge state the
  Python's `Transcript` gives on the same stream after `next_scalars(8)`,
  `from_halves(next_scalars(2))` and `samples(5)` (`python-verifier/verifier.py` at leanVM
  `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462`, driver `compiled_driver.py` of the port). This binds
  the IV preimage, the seed permutation of the IV and the public input, the duplex absorbs with
  their domain tags, the squeezes, the order of the reads, and the stack root's shape.
* A root half with a nonzero top limb is rejected, as `Digest.from_halves` rejects it.
* Garbage proofs run to a rejection: the empty proof and the stream cut after the root (the
  Python: `proof stream exhausted`), a hundred scalars after it (the Python: `GKR layer 17:
  children do not match the sumcheck`), and a rate exponent of `5` (`invalid PCS inverse rate`).
-/

namespace LeanVMTests.Protocol.Verifier.Compiled

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

/-- The driver's 64-bit word generator. -/
def fw (k lane : ℕ) : ℕ :=
  ((k + 1) * 0x9E3779B97F4A7C15 + lane * 0xD1B54A32D192ED03 + 0x632BE59BD9B4E019) % 2 ^ 64

/-- An `E` element from its three limbs. -/
def e (c0 c1 c2 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1) (K.ofBits c2)

/-- The driver's `fe(k)`. -/
def fe (i : ℕ) : E := e (fw i 0) (fw i 1) (fw i 2)

/-- The bytecode: 32 words. -/
def sampleBytecode : List K := (List.range 32).map fun i ↦ K.ofBits (fw i 9)

/-- The public input: the 32 bytes `fw(i, 10) mod 256`. -/
def samplePublicInput : Digest :=
  digestOfBytes ((List.range 32).map fun i ↦ (fw i 10 % 256).toUInt8)

/-- The sample row counts: `xor, mul, set, deref, jump, keccak`. -/
def sampleRows : List ℕ := [4, 2, 2, 4, 4, 8]

/-- The sizes, the root halves (`top` the root's second half's top limb), then `n` scalars. -/
def stream (rate n : ℕ) (top : ℕ := 0) : List E :=
  [eOfNat 16] ++ sampleRows.map eOfNat ++ [eOfNat rate] ++
    [e (fw 8 0) (fw 8 1) 0, e (fw 9 0) (fw 9 1) top] ++ (List.range n).map fun k ↦ fe (10 + k)

/-- The first two steps of the program, then five challenges. -/
def prefixProgram : Prog (List E) := do
  let (layout, rate) ← readSizes sampleBytecode
  commitStack layout.stackLog rate
  Prog.sampleN 5

/-- The compiled reading of `prefixProgram` on a stream, from the deployed seed. -/
def prefixRun (s : List E) : Option (List E × St) :=
  Id.run (Compile.run keccak256 keccakF prefixProgram
    ⟨⟨seed sampleBytecode samplePublicInput, []⟩, s, [], []⟩)

/-! ## The sponge agrees with the Python's -/

#guard ((prefixRun (stream 4 0)).map (·.1)) =
    some [(e 0xd790895a57ecc448 0x1d3f6a34ba276267 0xd84f736a7ca14a72),
     (e 0xd5e90535f68cfea9 0xbbc49cb20b116769 0x79a750f4c329c3d3),
     (e 0xa77a8da5d12628f3 0x628f9f71648bb439 0xff7344540018cf53),
     (e 0xd8ebb4231e51a997 0x36c7386d30fe9fcd 0x70b54020d618de60),
     (e 0xc4c1773fb367cac6 0xae8c3da5fab70731 0xf44a7f14b39c8cca)]

#guard ((prefixRun (stream 4 0)).map fun r ↦ (r.2.sponge.state.toList, r.2.sponge.pending.length)) =
    some ([0xc4c1773fb367cac6, 0xae8c3da5fab70731, 0xf44a7f14b39c8cca, 0x5e9745ea05eef225,
      0x487a8664795cfe0a, 0x5e4264d9289dfa7d, 0xe32f50eb1f5b7401, 0x5bbca26d605f030e,
      0xa4af9fe4557d02a5, 0x10da4d4b578ef012, 0xecd37a4ba588b299, 0xdf7f4908d22e1734,
      0x81eab84c9c062458, 0x70b4a1d3a309071b, 0xbd14d827401edcb5, 0xf269eb844eefd8af,
      0xb8c5f0d786acf104, 0x54d43adbf6b12746, 0xa9d7ab15287a87d9, 0x5738a45fd96a22be,
      0x4b96cebdc18d3dfc, 0xc3cfdcc776d936f1, 0xf5a34dd2e7f118ac, 0x70aab75027e95e95,
      0x282ee27cc904a7e5], 0)

/- The stack root is commitment `0`, of `2^(19 - 6 + 4)` leaves of `2^6` words. -/
#guard ((prefixRun (stream 4 0)).map fun r ↦ r.2.roots.map fun c ↦ (c.2.1, c.2.2)) =
    some [(17, 64)]

/- A root half with a nonzero top limb. -/
#guard (prefixRun (stream 4 0 1)).isNone

/-! ## Garbage is rejected -/

#guard verify sampleBytecode samplePublicInput ⟨[], []⟩ = false
#guard verify sampleBytecode samplePublicInput ⟨stream 4 0, []⟩ = false
#guard verify sampleBytecode samplePublicInput ⟨stream 4 100, []⟩ = false
#guard verify sampleBytecode samplePublicInput ⟨stream 5 100, []⟩ = false

/-- The deployed verifier is the oracle-parametric one at `Id`, Keccak-256 and Keccak-f. -/
example (π : Proof) :
    Id.run (verifyWith keccak256 keccakF sampleBytecode samplePublicInput π) =
      verify sampleBytecode samplePublicInput π :=
  rfl

end LeanVMTests.Protocol.Verifier.Compiled
