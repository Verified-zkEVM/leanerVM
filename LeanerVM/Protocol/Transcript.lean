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
random-oracle model by a query. The seed is three hashes: of the program's bytes
(`programBytes`), of the 78 bytes `seedPreimageOf` builds from the program hash, and of the 64
bytes `seedInput` builds from the seed and the public input. `programHash`, `fsSeed` and the
starting state `FsState.seed` are the three at `blake2sBytes`, constants of the statement.
`FsState.seedWith H` computes them through `H`, and is `FsState.seed` at BLAKE2s
(`FsState.seedWith_blake2sBytes`); `verifyWith` and `proveWith` start from it, so the statement's
hashes are queries of the hash like the chain's. The preimage's 78 bytes are neither a step nor a
Merkle node; the last input has a step's 64 bytes, and parses as one when the public input's last
lane is a step's tag.

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

/-- The bytes the program hash hashes: the stacked bytecode table, word by word little-endian
(`Program::assemble`, `bytecode_hash`). -/
def programBytes (prog : Program) : List UInt8 := (bytecodeColumn prog).values.toList.flatMap kBytes

/-- The program hash: BLAKE2s-256 of the stacked bytecode table, word by word little-endian
(`Program::assemble`, `bytecode_hash`). -/
def programHash (prog : Program) : Digest := blake2sBytes (programBytes prog)

/-- The 78 bytes hashed into the seed from the program hash `ph`: `"leanvm"`, the length of
`R1CS_DIGEST` as a little-endian 64-bit word, `R1CS_DIGEST`, and `ph` (`fs_seed`,
`cpu/mod.rs:83-89`). -/
def seedPreimageOf (ph : Digest) : List UInt8 :=
  "leanvm".toList.map (·.toNat.toUInt8) ++ kBytes (K.ofBits r1csDigest.length) ++ r1csDigest ++
    digestBytes ph

/-- The bytes hashed into the program's seed. -/
def seedPreimage (prog : Program) : List UInt8 := seedPreimageOf (programHash prog)

/-- The statement's seed, the chain's starting chaining value (`fs_seed`). -/
def fsSeed (prog : Program) : Digest := blake2sBytes (seedPreimage prog)

/-- The 64 bytes hashed into the chain's first state from the seed `iv`: `iv`, then the public
input's four lanes, each a little-endian 64-bit word (`FiatShamirState::new`). -/
def seedInput (iv : Digest) (input : PublicInput) : List UInt8 :=
  digestBytes iv ++ (Vector.ofFn input.lanes).toList.flatMap kBytes

/-! ## The seed's byte layout -/

/-- The seed's preimage is 78 bytes. -/
theorem length_seedPreimageOf (ph : Digest) : (seedPreimageOf ph).length = 78 := by
  simp [seedPreimageOf, length_kBytes, length_digestBytes, r1csDigest]

/-- The first state's input is 64 bytes. -/
theorem length_seedInput (iv : Digest) (input : PublicInput) :
    (seedInput iv input).length = 64 := by
  simp [seedInput, length_digestBytes, length_kBytes]

/-- Words are determined by their bytes. -/
theorem flatMap_kBytes_inj : ∀ {l l' : List K}, l.flatMap kBytes = l'.flatMap kBytes →
    l = l'
  | [], [], _ => rfl
  | [], b :: l', h | b :: l', [], h => by
    have := congrArg List.length h
    simp [length_kBytes] at this <;> omega
  | a :: l, b :: l', h => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [length_kBytes])
    have hk : ∀ c, kOfBytes (kBytes c) = c := fun c ↦ by simpa using kOfBytes_append c []
    have hab : a = b := by simpa [hk] using congrArg kOfBytes h₁
    rw [hab, flatMap_kBytes_inj h₂]

/-- The seed's preimage determines the program hash. -/
theorem seedPreimageOf_injective : Function.Injective seedPreimageOf := fun _ _ h ↦ by
  simpa [digestOfBytes_digestBytes] using congrArg digestOfBytes (List.append_cancel_left h)

/-- The first state's input determines the seed and the public input. -/
theorem seedInput_injective : Function.Injective2 seedInput := fun _ _ input input' h ↦ by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [length_digestBytes])
  refine ⟨by simpa [digestOfBytes_digestBytes] using congrArg digestOfBytes h₁, ?_⟩
  rw [Vector.toList_ofFn, Vector.toList_ofFn] at h₂
  have hl := List.ofFn_injective (flatMap_kBytes_inj h₂)
  cases input
  cases input'
  cases hl
  rfl

/-! ## The program's bytes -/

/-- The program's bytes are eight per word of the bytecode column. -/
theorem length_programBytes (prog : Program) :
    (programBytes prog).length = 2 ^ (prog.logSize + 4) * 8 := by
  simp [programBytes, List.length_flatMap, length_kBytes]

/-- The bytecode column's cell at an instruction and a slot is that slot. -/
private theorem bytecodeColumn_cell (prog : Program) (i : Fin (2 ^ prog.logSize)) (s : Fin 16) :
    (bytecodeColumn prog).values[cubeSplit prog.logSize 4 (i, s)] =
      (LeanerVM.Arithmetization.encodeSlots (prog.code i))[s] := by
  simp [bytecodeColumn]

/-- **The program's bytes determine the program.** -/
theorem programBytes_injective : Function.Injective programBytes := by
  intro p p' h
  have hk : p.logSize = p'.logSize := by
    have hlen := congrArg List.length h
    rw [length_programBytes, length_programBytes] at hlen
    have := Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right (by norm_num) hlen)
    omega
  obtain ⟨k, hk₁, c⟩ := p
  obtain ⟨k', hk₂, c'⟩ := p'
  dsimp only at hk
  subst hk
  have hv : (bytecodeColumn ⟨k, hk₁, c⟩).values = (bytecodeColumn ⟨k, hk₂, c'⟩).values :=
    Vector.toList_inj.mp (flatMap_kBytes_inj h)
  obtain rfl : c = c' := by
    funext i
    refine LeanerVM.Arithmetization.entry_injective (Vector.ext fun j hj ↦ ?_)
    have h₁ := congrArg (·[cubeSplit k 4 (i, (⟨j + 3, by omega⟩ : Fin 16))]) hv
    have h₃ : 3 ≤ j + 3 ∧ j + 3 < 11 := by omega
    rw [bytecodeColumn_cell, bytecodeColumn_cell] at h₁
    simp only [Fin.getElem_fin, LeanerVM.Arithmetization.encodeSlots_getElem _ (j + 3) (by omega), h₃] at h₁
    simpa using h₁
  rfl

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

/-- The state a proof starts from, its three hashes answered by `H`: the program hash, the seed,
then the first state. -/
def seedWith (prog : Program) (input : PublicInput) : m FsState := do
  let ph ← H (programBytes prog)
  let iv ← H (seedPreimageOf ph)
  FsState.mk <$> H (seedInput iv input)

/-- At BLAKE2s, the seed's hashes give the statement's seed. -/
theorem seedWith_blake2sBytes (prog : Program) (input : PublicInput) :
    seedWith (m := Id) blake2sBytes prog input = seed prog input := rfl

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

/-! ## The chain's steps -/

/-- A step of the chain, by the block it absorbs: an observed element (tag `1`), a squeeze (tag
`2`, element `0`), or a grinding nonce (tag `4`). The grinding base (tag `3`) and the grinding
check hash from a state without moving the chain, and are not steps. -/
inductive Block where
  /-- Absorb an element. -/
  | observe (x : E)
  /-- Squeeze a challenge. -/
  | squeeze
  /-- Absorb a grinding nonce. -/
  | nonce (n : E)
  deriving DecidableEq

namespace Block

/-- The element in lanes `0..2`. -/
def elem : Block → E
  | observe x => x
  | squeeze => 0
  | nonce n => n

/-- The tag in lane 3. -/
def tag : Block → K
  | observe _ => FsState.observeTag
  | squeeze => FsState.squeezeTag
  | nonce _ => FsState.powNonceTag

/-- The 64 bytes the step absorbing `b` from the chaining value `cv` hashes. -/
def input (cv : Digest) (b : Block) : List UInt8 := FsState.stepBytes cv b.elem b.tag

/-- The step a 64-byte input hashes, if it is one: the chaining value in the first 32 bytes, then
the three limbs and a tag `1`, `2` with the element `0`, or `4`. -/
def parse? (q : List UInt8) : Option (Digest × Block) :=
  if q.length = 64 then
    let x := E.ofLimbs (kOfBytes (q.drop 32)) (kOfBytes (q.drop 40)) (kOfBytes (q.drop 48))
    let t := kOfBytes (q.drop 56)
    if t = FsState.observeTag then some (digestOfBytes q, observe x)
    else if t = FsState.squeezeTag ∧ x = 0 then some (digestOfBytes q, squeeze)
    else if t = FsState.powNonceTag then some (digestOfBytes q, nonce x)
    else none
  else none

private theorem squeezeTag_ne_observeTag : FsState.squeezeTag ≠ FsState.observeTag := by
  decide +kernel

private theorem powNonceTag_ne_observeTag : FsState.powNonceTag ≠ FsState.observeTag := by
  decide +kernel

private theorem powNonceTag_ne_squeezeTag : FsState.powNonceTag ≠ FsState.squeezeTag := by
  decide +kernel

/-- A step's input is 64 bytes. -/
theorem length_input (cv : Digest) (b : Block) : (input cv b).length = 64 := by
  simp [input, FsState.stepBytes, FsState.block, length_digestBytes, length_kBytes]

/-- The input of a step parses back to the step. -/
theorem parse?_input (cv : Digest) (b : Block) : parse? (input cv b) = some (cv, b) := by
  have ht : kOfBytes (kBytes b.tag) = b.tag := by simpa using kOfBytes_append b.tag []
  have hk : ∀ a n, 8 ≤ n → (kBytes a).drop n = [] := fun _ _ h ↦ List.drop_eq_nil_of_le h
  simp only [parse?, length_input, ↓reduceIte]
  simp only [input, FsState.stepBytes, FsState.block, List.append_assoc, List.drop_append,
    length_digestBytes, length_kBytes, List.drop_eq_nil_of_le, Nat.reduceLeDiff, Nat.reduceSub,
    List.drop_zero, List.nil_append, hk, kOfBytes_append, ht, digestOfBytes_append, ofLimbs_limb]
  cases b with
  | observe x => simp [tag, elem]
  | squeeze => simp [tag, elem, squeezeTag_ne_observeTag]
  | nonce n => simp [tag, elem, powNonceTag_ne_observeTag, powNonceTag_ne_squeezeTag]

end Block

namespace FsState

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- One step of the chain: the new chaining value is the hash of the old one and the block. -/
def step (s : FsState) (b : Block) : m FsState := FsState.mk <$> H (Block.input s.cv b)

/-- An observe is the step on `observe x`. -/
theorem observe_eq_step (s : FsState) (x : E) : observe H s x = step H s (.observe x) := rfl

/-- A nonce absorption is the step on `nonce n`. -/
theorem absorbNonce_eq_step (s : FsState) (n : E) : absorbNonce H s n = step H s (.nonce n) :=
  rfl

/-- A squeeze is the step on `squeeze`, with the challenge read off the new state. -/
theorem sample_eq_step [LawfulMonad m] (s : FsState) :
    sample H s = (fun s' ↦ (challengeOf s'.cv, s')) <$> step H s .squeeze := by
  simp only [sample, step, Block.input, Block.elem, Block.tag, Functor.map_map]
  rw [map_eq_bind_pure_comp]
  rfl

end FsState

end
end LeanerVM.Protocol
