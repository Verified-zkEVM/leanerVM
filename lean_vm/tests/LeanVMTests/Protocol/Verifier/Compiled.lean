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
    some [(e 0x148abcb87ca70219 0x846ba8835e623411 0xc0f612e8b6f385a4),
     (e 0x34005b035dad2d3f 0x8289a20d49fadf57 0x835c9ba69fde4a06),
     (e 0xf6080c476785ceaf 0x12955a6c3e660ffb 0xe3d4885dcf7e2b12),
     (e 0xa6252d945f490912 0x7a6b42738c133b2d 0xd83ec4099168f0e9),
     (e 0x57afc31da54ec6c1 0xa98880d53f79e4d0 0x04dbe9a04ab480bb)]

#guard ((prefixRun (stream 4 0)).map fun r ↦ (r.2.sponge.state.toList, r.2.sponge.pending.length)) =
    some ([0x57afc31da54ec6c1, 0xa98880d53f79e4d0, 0x04dbe9a04ab480bb, 0x521e6822baa11f26,
      0x49b22e1bd231c920, 0xf0b34eadc1f31287, 0x94d7a2d0c0929928, 0x134ae17ac741e0b4,
      0x6b02f8410442b2c5, 0x6ad7f3e54ffe7e98, 0x65dba5a7d5b6f3e1, 0xb983308b08ad19f9,
      0xcf73cd83c8956764, 0x01de8d0e3193f263, 0x178df8c81ea3d0c4, 0x36a5b7e37c9d3525,
      0xb446301617bf2424, 0x0a9ab3ab72a91113, 0x792f3012ec741b67, 0xcb915e1661f1d526,
      0x7bb10017f8d6be50, 0xf9de46766c961d10, 0x4fd52ca162e6f7b7, 0xcdf4f3a074fb8cb4,
      0xaec1f5497894d0d3], 0)

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
