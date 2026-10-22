import LeanerVM.Protocol.Transcript

/-!
# Fiat–Shamir chain tests

Known answers of the pinned Rust chain, printed by `scripts/dump-fs-chain-rust.sh` at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`: the program hash and the seed of a four-instruction
program, the state after seeding with a public input, an observe, two squeezes, the grinding
base, an 8-bit grind with its nonce, and the grinding check at 8 and 0 bits. A word is a
little-endian 64-bit lane, as the Rust prints it.

Then the mutations a wrong reading would pass: the observe tag replaced by the squeeze tag, two
observes swapped, the program and the public input changed, a nonce that does not clear, a
nonzero nonce at 0 bits, and a grind whose fuel stops one short of the Rust's nonce.
-/

namespace LeanerVMTests.Protocol.Transcript

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash

/-- A digest from its four little-endian 64-bit words. -/
def digest64 (a b c d : UInt64) : Digest :=
  #v[a.toUInt32, (a >>> 32).toUInt32, b.toUInt32, (b >>> 32).toUInt32, c.toUInt32,
    (c >>> 32).toUInt32, d.toUInt32, (d >>> 32).toUInt32]

/-- An element of `E` from its three limbs. -/
def e3 (a b c : ℕ) : E := E.ofLimbs (K.ofBits a) (K.ofBits b) (K.ofBits c)

/-- The dump's program: `XOR [g, g², g³]`, `SET_CONSTANT [g⁴; 0x1111 + 0x2222·y + 0x3333·y²]`,
`DEREF [g⁵, g⁶, g⁷; pc]`, `JUMP [g⁸, g⁹, g¹⁰]`. -/
def program : Program where
  logSize := 2
  logSize_le := by decide
  code := ![
    .xor (gpow 1) (gpow 2) (gpow 3),
    .setConstant (gpow 4) (e3 0x1111 0x2222 0x3333),
    .deref (gpow 5) (gpow 6) (gpow 7) .pc,
    .jump (gpow 8) (gpow 9) (gpow 10)]

/-- The dump's public input, the lanes `7, 11, 13, 17`. -/
def input : PublicInput := ⟨![K.ofBits 7, K.ofBits 11, K.ofBits 13, K.ofBits 17]⟩

/-- The observed element of the dump. -/
def x : E := e3 0x0123456789abcdef 0xfedcba9876543210 0x1111222233334444

/-! ## The statement's constants -/

-- The program hash (`bytecode_hash`), over the 64 words of the stacked table.
#guard (bytecodeColumn program).values.toList.length = 64
#guard programHash program =
  digest64 0xe2d63b9bbb48d99c 0x2120b3a19c9ee29d 0xdb2c47087bc9c37c 0xe2d9fc8fe86691fd

-- The seed (`fs_seed`), as its two halves; the preimage is 78 bytes.
#guard (seedPreimage program).length = 78
#guard digestScalars (fsSeed program) =
  (e3 0xe7eb7bdcc35ce043 0xa0beba1e8c375954 0, e3 0x9a6fb9db512a13d5 0x379113ef7769af85 0)

/-! ## The chain -/

/-- The state after seeding. -/
def s0 : FsState := FsState.seed program input

#guard s0.cv = digest64 0xe291a3f3173fff2a 0x5eef874401646aba 0x8821b3201f3eeeb9 0x14bd8e5e2372eb46

/-- After observing `x`. -/
def s1 : FsState := Deployed.observe s0 x

#guard s1.cv = digest64 0xfb638d146c3543ad 0xee957bd34002beb7 0x5539e48061a90335 0xf40d2d5c9a488675

-- The first squeeze: the challenge is the first three words of the new state.
#guard (Deployed.sample s1).1 = e3 0x01e46062e84428be 0x639d7394be8ad7f3 0x5c837b8c41774364
#guard (Deployed.sample s1).2.cv =
  digest64 0x01e46062e84428be 0x639d7394be8ad7f3 0x5c837b8c41774364 0xddfc4ee32027fb3e

/-- After observing `5` and squeezing again. -/
def s2 : E × FsState := Deployed.sample (Deployed.observe (Deployed.sample s1).2 (e3 5 0 0))

#guard s2.1 = e3 0x9a12669cdcdcecf4 0x8309161cfb746173 0xace91f8050fdcc1c
#guard s2.2.cv =
  digest64 0x9a12669cdcdcecf4 0x8309161cfb746173 0xace91f8050fdcc1c 0xef58cf506d73e4a2

/-! ## Grinding -/

#guard Id.run (s2.2.powBase blake2sBytes) =
  digest64 0x9f3128911b813f07 0xf5c82a906a128dc2 0xb8562504749d2baa 0x93a8803347dc2fbc

/-- The state after the Rust's 8-bit grind. -/
def ground : Digest :=
  digest64 0x847949c9d17f50ab 0x6a7452293cb26012 0xe76913ef27cb1fd4 0x02239817db61ee9d

-- The prover's grind finds the Rust's nonce, 262, and absorbs it.
#guard (Deployed.grind 1024 s2.2 8).map (fun p ↦ (p.1, p.2.cv)) =
  some (FsState.nonceOf 262, ground)
-- The verifier's check accepts it and lands in the same state.
#guard (Deployed.checkPow s2.2 8 (FsState.nonceOf 262)).1 = true
#guard (Deployed.checkPow s2.2 8 (FsState.nonceOf 262)).2.cv = ground
-- The next nonce does not clear 8 bits (`verify8_next_ok false`).
#guard (Deployed.checkPow s2.2 8 (FsState.nonceOf 263)).1 = false
-- With fuel for the nonces below 262 only, the search fails.
#guard (Deployed.grind 262 s2.2 8).isNone

-- At 0 bits only the nonce 0 passes, and the nonce is absorbed whatever the outcome.
#guard (Deployed.checkPow s2.2 0 0).1 = true
#guard (Deployed.checkPow s2.2 0 0).2.cv =
  digest64 0x42aa5c2968df6d48 0x7519d5e2be217459 0x72c293c815c188a5 0xc9748a1d79df9508
#guard (Deployed.checkPow s2.2 0 1).1 = false
#guard (Deployed.checkPow s2.2 0 1).2.cv = (Deployed.checkPow s2.2 8 1).2.cv
#guard (Deployed.grind 0 s2.2 0).map (fun p ↦ (p.1, p.2.cv)) =
  some (0, (Deployed.checkPow s2.2 0 0).2.cv)

/-! ## Mutations -/

-- Tags, not labels: observing with the squeeze tag is another chain.
#guard (FsState.mk (blake2sBytes (FsState.stepBytes s0.cv x FsState.squeezeTag))).cv ≠ s1.cv
-- The order of observes is bound.
#guard (Deployed.observe (Deployed.observe s0 x) (e3 5 0 0)).cv ≠
  (Deployed.observe (Deployed.observe s0 (e3 5 0 0)) x).cv
/-- The program with the last operand of its `JUMP` changed. -/
def program' : Program :=
  { program with code := Function.update program.code 3 (.jump (gpow 8) (gpow 9) (gpow 11)) }

-- The seed binds the program and the public input.
#guard (FsState.seed program' input).cv ≠ s0.cv
#guard (FsState.seed program ⟨![K.ofBits 7, K.ofBits 11, K.ofBits 13, K.ofBits 18]⟩).cv ≠ s0.cv

end LeanerVMTests.Protocol.Transcript
