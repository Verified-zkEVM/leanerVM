/-
  LeanerVM.Protocol.Transcript

  leanVM's Fiat–Shamir chain: a BLAKE2s chaining value seeded from the program and the public
  input, the tagged observe and squeeze steps, and the proof-of-work grind and its check.
-/

module

public import LeanerVM.Protocol.Blake2sHash
public import LeanerVM.Protocol.FixedColumns

/-!
# The Fiat–Shamir chain

Category B, transcribed from the pinned leanVM (`a386121f84292f6fa663aaa3e570c15bc0240ea2`):
the chain is `crates/fiat_shamir/src/lib.rs:18-174`, the seed `crates/lean_vm/src/cpu/mod.rs:66-106`
(`fs_seed`, `digest_words`) with the program hash of `Program::assemble` (`:229-245`). The
specification leaves Fiat–Shamir to the code (§8.4 is a `TODO`); the Python verifier computes the
same chain (`python-verifier/verifier.py:335-383, 1366-1369`).

**The step.** Every operation is BLAKE2s-256 of 64 bytes: the 32 bytes of the chaining value,
then a block of four little-endian 64-bit lanes, lanes `0..2` the limbs of an element of `E` and
lane 3 a tag, `1` observe, `2` squeeze, `3` grinding base, `4` grinding nonce (`compress`,
`DS_*`, `lib.rs:18-39`). The chaining value is a `Digest`, eight 32-bit words; the Rust's four
64-bit words (`digest_words`, `:27-29`) are the same 32 bytes, and `digestBytes` is the one byte
encoding used.

* `observe x`: the step on `(x, 1)` is the new state (`:85-87`).
* `sample`: the step on `(0, 2)` is the new state, and its first three 64-bit words are the
  challenge's limbs (`:95-99`).
* `powBase`: the step on `(0, 3)`, the state unchanged (`:108-110`). `powOk base nonce bits`: the
  step from `base` on `(nonce, 4)` has its low `bits` bits zero (`pow_bits_ok`, `:47-51`).
* `grind`: the prover's smallest nonce `n` (as `n + 0·y + 0·y²`) that clears `bits`, `0` when
  `bits = 0`, then the nonce absorbed with tag `4` (`grind_pow`, `:126-155`). `checkPow`: with
  `bits = 0` only the nonce `0` passes, otherwise `powOk`; the nonce is absorbed whatever the
  outcome (`verify_pow_field`, `:165-174`).

**The seed.** `programHash prog` is BLAKE2s-256 of the stacked bytecode table `bytecodeColumn
prog`, its `K` words little-endian (`cpu/mod.rs:237-245`; `layout.rs:317-326`, `leaf.rs:585-604`).
`fsSeed prog` is BLAKE2s-256 of the 78 bytes `"leanvm" ‖ 32 ‖ R1CS_DIGEST ‖ programHash prog`,
the length a little-endian 64-bit word (`fs_seed`, `:82-93`). The chain starts at the BLAKE2s-256
of `fsSeed prog` followed by the four lanes of the public input (`FiatShamirState::new`,
`lib.rs:69-73`; `cpu/mod.rs:556, 712`).

**The hash.** Every chain operation takes the 64-byte map as an argument `H : List UInt8 → m
Digest` in a monad `m`: the deployed chain answers it by `blake2sBytes` in `Id` (`Deployed`), a
random-oracle model by a query. The seed is not a chain operation: `programHash`, `fsSeed` and the
starting state `FsState.seed` are constants of the statement, computed by `blake2sBytes` directly
and never through `H`.

**Differences from the Rust.** None in the values at the grinding bits used (`17` at every WHIR
level, `0` elsewhere). The prover's nonce search takes fuel and returns `none` when it runs out,
where the Rust loops; it runs on one thread, and the Rust's parallel search returns the same,
smallest, nonce. `powOk` equals `pow_bits_ok` for `bits < 64`, the range of the Rust's debug
assertion; at `bits ≥ 64` a release build of the Rust masks the shift to `bits mod 64`, while
`powOk` asks for the whole first word to be zero.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash

@[expose] public section

/-! ## The statement's constants -/

/-- `R1CS_DIGEST`, the 32 bytes naming Flock's BLAKE2s circuit (`crates/flock/src/hash.rs:276-279`;
`python-verifier/verifier.py:629`). -/
def r1csDigest : List UInt8 :=
  [0x53, 0x7a, 0xd2, 0x07, 0x90, 0x30, 0x8f, 0x8e, 0xb8, 0xc0, 0xe8, 0xbd, 0x3e, 0x6c, 0x58, 0xee,
    0x64, 0x57, 0x33, 0x71, 0xe3, 0xd5, 0x3c, 0x30, 0x61, 0x3d, 0xd0, 0x4d, 0x87, 0xc0, 0xb7, 0xea]

/-- The program hash: BLAKE2s-256 of the stacked bytecode table, word by word little-endian
(`Program::assemble`, `bytecode_hash`). -/
def programHash (prog : Program) : Digest := hashWords (bytecodeColumn prog).values.toList

/-- The bytes hashed into the seed: `"leanvm"`, the length of `R1CS_DIGEST` as a little-endian
64-bit word, `R1CS_DIGEST`, and the program hash (`fs_seed`, `cpu/mod.rs:83-89`). -/
def seedPreimage (prog : Program) : List UInt8 :=
  "leanvm".toList.map (·.toNat.toUInt8) ++ kBytes (K.ofBits r1csDigest.length) ++ r1csDigest ++
    digestBytes (programHash prog)

/-- The statement's seed, the chain's starting chaining value (`fs_seed`). -/
def fsSeed (prog : Program) : Digest := blake2sBytes (seedPreimage prog)

/-! ## The chain -/

/-- The chain state: the chaining value, a BLAKE2s-256 digest (`FiatShamirState`). -/
structure FsState where
  /-- The chaining value. -/
  cv : Digest

namespace FsState

/-- The observe tag, `DS_OBSERVE`. -/
def observeTag : K := K.ofBits 1

/-- The squeeze tag, `DS_SQUEEZE`. -/
def squeezeTag : K := K.ofBits 2

/-- The grinding-base tag, `DS_POW_BASE`. -/
def powBaseTag : K := K.ofBits 3

/-- The grinding-nonce tag, `DS_POW_NONCE`. -/
def powNonceTag : K := K.ofBits 4

/-- The 32-byte block of an element and a tag: the three limbs, then the tag, each a
little-endian 64-bit lane. -/
def block (x : E) (tag : K) : List UInt8 :=
  kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2) ++ kBytes tag

/-- The 64 bytes of a step from the chaining value `cv` (`compress`). -/
def stepBytes (cv : Digest) (x : E) (tag : K) : List UInt8 := digestBytes cv ++ block x tag

/-- The element whose limbs are the first three 64-bit words of a digest (`sample`). -/
def challengeOf (d : Digest) : E :=
  E.ofLimbs (ofWords d[0] d[1]) (ofWords d[2] d[3]) (ofWords d[4] d[5])

/-- The low `bits` bits of the first 64-bit word of a digest are zero (`pow_bits_ok`). -/
def lowBitsZero (d : Digest) (bits : ℕ) : Bool :=
  (d[0].toNat + 2 ^ 32 * d[1].toNat) % 2 ^ bits == 0

/-- The nonce `n` as an element, `n + 0·y + 0·y²` (`F192::new(n, 0, 0)`). -/
def nonceOf (n : ℕ) : E := E.ofLimbs (K.ofBits n) 0 0

/-- The state seeded from the digest `iv` and four lanes: BLAKE2s-256 of `iv` followed by the
lanes (`FiatShamirState::new`), computed directly, not through the chain's hash. -/
def new (iv : Digest) (lanes : Vector K 4) : FsState :=
  ⟨blake2sBytes (digestBytes iv ++ lanes.toList.flatMap kBytes)⟩

/-- The state a proof of the program and the public input starts from, a constant of the
statement. -/
def seed (prog : Program) (input : PublicInput) : FsState :=
  new (fsSeed prog) (Vector.ofFn input.lanes)

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- Absorb an element (`observe`). -/
def observe (s : FsState) (x : E) : m FsState :=
  FsState.mk <$> H (stepBytes s.cv x observeTag)

/-- Squeeze a challenge and move to the squeezed digest (`sample`). -/
def sample (s : FsState) : m (E × FsState) := do
  let out ← H (stepBytes s.cv 0 squeezeTag)
  return (challengeOf out, ⟨out⟩)

/-- The grinding base, the state unchanged (`pow_base`). -/
def powBase (s : FsState) : m Digest := H (stepBytes s.cv 0 powBaseTag)

/-- The nonce clears `bits` against the base (`pow_bits_ok`, which it equals for `bits < 64`). -/
def powOk (base : Digest) (nonce : E) (bits : ℕ) : m Bool := do
  return lowBitsZero (← H (stepBytes base nonce powNonceTag)) bits

/-- Absorb a grinding nonce (`absorb_nonce`). -/
def absorbNonce (s : FsState) (nonce : E) : m FsState :=
  FsState.mk <$> H (stepBytes s.cv nonce powNonceTag)

/-- The verifier's grinding check: whether the nonce passes, and the state with the nonce
absorbed whatever the outcome (`verify_pow_field`). -/
def checkPow (s : FsState) (bits : ℕ) (nonce : E) : m (Bool × FsState) := do
  let base ← powBase H s
  let ok ← if bits = 0 then pure (decide (nonce = 0)) else powOk H base nonce bits
  return (ok, ← absorbNonce H s nonce)

/-- The first of `fuel` nonces from `n` on that clears `bits`. -/
def findNonce (base : Digest) (bits : ℕ) : (fuel n : ℕ) → m (Option ℕ)
  | 0, _ => pure none
  | fuel + 1, n => do
    if ← powOk H base (nonceOf n) bits then return some n else findNonce base bits fuel (n + 1)

/-- The prover's grind: the smallest nonce below `fuel` that clears `bits` (`0` when `bits = 0`),
and the state with it absorbed; `none` when no nonce below `fuel` clears (`grind_pow`). -/
def grind (fuel : ℕ) (s : FsState) (bits : ℕ) : m (Option (E × FsState)) := do
  let base ← powBase H s
  let n? ← if bits = 0 then pure (some 0) else findNonce H base bits fuel 0
  match n? with
  | none => return none
  | some n => return some (nonceOf n, ← absorbNonce H s (nonceOf n))

end FsState

/-! ## The deployed chain -/

namespace Deployed

/-- The deployed observe. -/
def observe (s : FsState) (x : E) : FsState := Id.run (s.observe blake2sBytes x)

/-- The deployed squeeze. -/
def sample (s : FsState) : E × FsState := Id.run (s.sample blake2sBytes)

/-- The deployed prover's grind. -/
def grind (fuel : ℕ) (s : FsState) (bits : ℕ) : Option (E × FsState) :=
  Id.run (s.grind blake2sBytes fuel bits)

/-- The deployed grinding check. -/
def checkPow (s : FsState) (bits : ℕ) (nonce : E) : Bool × FsState :=
  Id.run (s.checkPow blake2sBytes bits nonce)

end Deployed

/-! ## The prover's grind passes the verifier's check -/

namespace FsState

variable (H : List UInt8 → Id Digest)

/-- A nonce the search returns clears the grinding check. -/
private theorem powOk_of_findNonce {base : Digest} {bits : ℕ} :
    ∀ {fuel n k : ℕ}, Id.run (findNonce H base bits fuel n) = some k →
      Id.run (powOk H base (nonceOf k) bits) = true
  | 0, _, _, h => nomatch h
  | fuel + 1, n, k, h => by
    simp only [findNonce, Id.run_bind] at h
    split at h
    · cases h; assumption
    · exact powOk_of_findNonce h

/-- The verifier's check accepts the prover's nonce and lands in the prover's state, for every
hash function. -/
theorem checkPow_of_grind {fuel bits : ℕ} {s s' : FsState} {nonce : E}
    (h : Id.run (grind H fuel s bits) = some (nonce, s')) :
    Id.run (checkPow H s bits nonce) = (true, s') := by
  simp only [grind, checkPow] at h ⊢
  split_ifs at h ⊢
  · obtain ⟨rfl, rfl⟩ : nonceOf 0 = nonce ∧ Id.run (absorbNonce H s (nonceOf 0)) = s' := by
      simpa using h
    simp [nonceOf, ofLimbs_eq_zero_iff, show K.ofBits 0 = 0 by decide +kernel]
  · rcases hk : Id.run (findNonce H (Id.run (powBase H s)) bits fuel 0) with _ | k <;>
      simp [hk] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using powOk_of_findNonce H hk

end FsState

end
end LeanerVM.Protocol
