/-
  LeanerVM.Protocol.RandomOracle

  BLAKE2s-256 on byte strings as one oracle, answered by BLAKE2s or lazily at random; the
  distribution of a challenge and of a grinding check on a uniform digest; and the Fiat–Shamir
  chain read back off a log of the oracle's queries.
-/

module

public import LeanerVM.Protocol.Field
public import LeanerVM.Protocol.Transcript
public import LeanerVM.Protocol.ToVCVio.HashChain
public import LeanerVM.Protocol.ToVCVio.UniformSample
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# The hash oracle

Every hash of the proof system, the chain's steps, the Merkle leaves and nodes, is BLAKE2s-256 of
a byte string. As an oracle it is VCVio's `hashSpec := List UInt8 →ₒ Digest`, queried by
`hashQuery`. A computation over it runs in one of two ways:

* `runBlake2s`: every query answered by `blake2sBytes`, the deployed hash; one value.
* `runRandom`: VCVio's lazy random oracle from the empty cache, a fresh query answered by a
  uniform digest and a repeated one from the cache; the run returns the final cache.

A uniform digest is eight independent uniform words, VCVio's vector sampler over Mathlib's
enumeration of `UInt32`; `card_digest` counts `2^256` digests.

**Challenges and grinding.** A squeeze's challenge is the element whose limbs are the first three
64-bit words of the new state (`FsState.challengeOf`). Each element is the challenge of `2^64`
digests, so the challenge of a uniform digest is uniform on `E` (`prEvent_challengeOf`). The
grinding check asks for `bits` low zero bits in the first 64-bit word (`FsState.lowBitsZero`), which
a uniform digest has with probability `2^-bits` for `bits ≤ 64` (`prEvent_lowBitsZero`).

**Tuples and positions.** The challenges of `m` fresh uniform digests are a uniform tuple in
`Fin m → E` (`prEvent_challengeOf_tuple`). WHIR's query positions of `b` bits are chunks of the
challenges' 192 bits (`challengeBits`), `⌊192/b⌋` to a squeeze, low bits first
(`challengePositions`); with `t ≤ m⌊192/b⌋`, the `t` positions of `m` fresh squeezes are a uniform
tuple in `Fin t → Fin (2^b)` (`prEvent_positions_uniform`).

**The chain read off a log.** `chainHistory log seed s` is the chain `HashChain.history` reads back
from the state `s` to `seed`: at each state, the unique logged query answered by it that parses as
a step (`Block.parse?`), with the state each block leads to. A Merkle node is also a 64-byte input
of the same oracle and may parse as a step; it is one more entry of the log. The digests in play
after a log (`inPlay`) are a fixed list of roots, the two halves of every logged 64-byte input
(`halves`: the chaining value and the block of a step, the two children of a node), and the Merkle
roots the log's chains absorb as two consecutive observes (`rebuiltRoots`, one per observe step).

* `chainHistory_of_noCollision_noSeed`: a chain whose every step is logged is its history, when the
  log has no collision and no answer is the seed.
* `chainHistory_take_of_noCollision_noHit`: in a consistent log with no collision and no hit on the
  digests in play, the history is already in the log before a query from the chain's last state
  that is none of its steps: the next step (`chainHistory_take_of_step`), the grinding base or the
  grinding check.
* `chainHistory_take_of_mem_inPlay`: under the same hypotheses, a history whose last state is in
  play after `m` entries is already in them.
* `chainHistory_determined`: without a collision, a history once in the log does not change.
* `chainHistory_append`: a query answered by a digest not in play leaves every other state's
  history unchanged.
* `chainHistory_dedupKeys`, `inPlay_dedupKeys`: in a consistent log, histories and the digests in
  play are those of the log with each query at its first occurrence only (`QueryLog.dedupKeys`),
  the fresh log of a lazy random oracle.
* `length_inPlay_le`: at most the roots, two halves and one absorbed root per entry are in play.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/-! ## The digests -/

/-- `|Digest| = 2^256`. -/
theorem card_digest : Fintype.card Digest = 2 ^ 256 := by
  rw [Fintype.card_congr (arrayVectorEquivFin UInt32 8), Fintype.card_fun, Fintype.card_fin,
    ← FinEnum.card_eq_fintypeCard]
  rfl

/-! ## The oracle -/

/-- The one hash oracle: BLAKE2s-256 on byte strings. -/
abbrev hashSpec : OracleSpec (List UInt8) := List UInt8 →ₒ Digest

/-- A query of the hash on the bytes `t`. -/
def hashQuery (t : List UInt8) : OracleComp hashSpec Digest := liftM (hashSpec.query t)

/-- A computation with every query answered by BLAKE2s-256. -/
def runBlake2s {α : Type} (oa : OracleComp hashSpec α) : ProbComp α :=
  simulateQ (fun t ↦ pure (blake2sBytes t) : QueryImpl hashSpec ProbComp) oa

/-- A computation with its queries answered by the lazy random oracle from the empty cache: a
fresh query by a uniform digest, a repeated one from the cache. The run returns the final
cache. -/
def runRandom {α : Type} (oa : OracleComp hashSpec α) : ProbComp (α × hashSpec.QueryCache) :=
  (simulateQ hashSpec.randomOracle oa).run ∅

/-! ## Challenges and grinding checks of a uniform digest -/

/-- A digest is its challenge and its last two words. -/
private theorem challengeOf_bijective :
    Function.Bijective fun d : Digest ↦ (FsState.challengeOf d, (d[6], d[7])) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨Function.LeftInverse.injective (g := fun p : E × UInt32 × UInt32 ↦
    #v[lowWord (p.1.limb 0), highWord (p.1.limb 0), lowWord (p.1.limb 1), highWord (p.1.limb 1),
      lowWord (p.1.limb 2), highWord (p.1.limb 2), p.2.1, p.2.2]) fun d ↦ ?_, ?_⟩
  · ext i hi
    simp only [FsState.challengeOf, limb_ofLimbs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, lowWord_ofWords, highWord_ofWords]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | rfl | omega
  · rw [card_digest, Fintype.card_prod, Fintype.card_prod, card_E, ← FinEnum.card_eq_fintypeCard]
    rfl

/-- **The challenge of a uniform digest is uniform.** Every event of the challenge of a uniform
digest has its probability under a uniform element of `E`: each element is the challenge of `2^64`
digests. -/
theorem prEvent_challengeOf (p : E → Prop) :
    Pr{let d ← $ᵗ Digest}[p (FsState.challengeOf d)] = Pr{let x ← $ᵗ E}[p x] :=
  prEvent_uniformSample_fst_of_bijective challengeOf_bijective p

/-- The challenge of a uniform digest is any given element with probability `1/|E|`. -/
theorem prEvent_challengeOf_eq (e : E) :
    Pr{let d ← $ᵗ Digest}[FsState.challengeOf d = e] = 1 / (Fintype.card E : ℝ≥0∞) := by
  rw [prEvent_challengeOf (· = e), SampleableType.prEvent_uniformSample_eq_singleton, one_div]

/-- The first 64-bit word of a digest. -/
private def firstWord (d : Digest) : ℕ := d[0].toNat + 2 ^ 32 * d[1].toNat

/-- The 64-bit word of two 32-bit words is below `2^64` and determines them. -/
private theorem wordPair_lt_and_inj (a b : UInt32) : a.toNat + 2 ^ 32 * b.toNat < 2 ^ 64 ∧
    ∀ {a' b' : UInt32}, a.toNat + 2 ^ 32 * b.toNat = a'.toNat + 2 ^ 32 * b'.toNat →
      a = a' ∧ b = b' := by
  have := a.toNat_lt
  have := b.toNat_lt
  refine ⟨by omega, fun {a' b'} h ↦ ?_⟩
  have := a'.toNat_lt
  have := b'.toNat_lt
  exact ⟨UInt32.toNat_inj.mp (by omega), UInt32.toNat_inj.mp (by omega)⟩

/-- A digest is the low `bits` bits and the rest of its first 64-bit word, and its last six
words. -/
private theorem lowBits_bijective {bits : ℕ} (hb : bits ≤ 64) :
    Function.Bijective fun d : Digest ↦
      ((⟨firstWord d % 2 ^ bits, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ bits)),
        ((⟨firstWord d / 2 ^ bits, by
            rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hb]
            exact (wordPair_lt_and_inj _ _).1⟩ : Fin (2 ^ (64 - bits))),
          #v[d[2], d[3], d[4], d[5], d[6], d[7]])) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun d d' h ↦ ?_, ?_⟩
  · simp only [Prod.mk.injEq, Fin.mk.injEq, Vector.mk_eq, Array.mk.injEq, List.cons.injEq,
      and_true] at h
    obtain ⟨hlo, hhi, h2, h3, h4, h5, h6, h7⟩ := h
    have hw := Nat.div_add_mod (firstWord d) (2 ^ bits)
    rw [hlo, hhi, Nat.div_add_mod] at hw
    obtain ⟨h0, h1⟩ := (wordPair_lt_and_inj _ _).2 hw.symm
    ext i hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | assumption | omega
  · rw [card_digest, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_congr (arrayVectorEquivFin UInt32 6), Fintype.card_fun, Fintype.card_fin,
      ← FinEnum.card_eq_fintypeCard, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hb]
    rfl

/-- **The grinding check of a uniform digest.** A uniform digest has `bits ≤ 64` low zero bits
in its first 64-bit word with probability `2^-bits`. -/
theorem prEvent_lowBitsZero {bits : ℕ} (hb : bits ≤ 64) :
    Pr{let d ← $ᵗ Digest}[FsState.lowBitsZero d bits = true] = (2 ^ bits : ℝ≥0∞)⁻¹ := by
  have h := prEvent_uniformSample_fst_of_bijective (lowBits_bijective hb)
    (· = ⟨0, by positivity⟩)
  simp only [Fin.mk.injEq] at h
  simp only [FsState.lowBitsZero, beq_iff_eq, ← firstWord.eq_def, h,
    SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat]

/-! ## Tuples of challenges and query positions -/

/-- **The challenges of fresh digests are a uniform tuple.** The challenges of `m` independent
uniform digests, the answers to `m` fresh squeezes, are `m` independent uniform elements of
`E`. -/
theorem prEvent_challengeOf_tuple (m : ℕ) (p : (Fin m → E) → Prop) :
    Pr{let d ← $ᵗ (Fin m → Digest)}[p fun i ↦ FsState.challengeOf (d i)] =
      Pr{let x ← $ᵗ (Fin m → E)}[p x] :=
  prEvent_uniformSample_pi_of_bijective challengeOf_bijective m p

/-- The integer of a challenge's 192 bits, limb `0` lowest: the bits `sample_queries_ordered`
chunks into query positions. -/
def challengeBits (x : E) : ℕ :=
  (x.limb 0).toBitVec.toNat + 2 ^ 64 * (x.limb 1).toBitVec.toNat +
    2 ^ 128 * (x.limb 2).toBitVec.toNat

/-- The `t` query positions of `b` bits that the challenges `xs` of successive squeezes give
(`sample_queries_ordered`, `crates/pcs/src/whir.rs:1175-1193` at
`a386121f84292f6fa663aaa3e570c15bc0240ea2`): `⌊192/b⌋` to a challenge, low bits first, so position
`q` is bits `[c·b, c·b + b)` of the 192 bits of challenge `q / ⌊192/b⌋`, `c = q % ⌊192/b⌋`. The
Rust reads a chunk off at most two limbs into a `u64` and masks it with `2^b - 1`, which is these
bits for `1 ≤ b < 64` (`b = 0` divides by zero, `b = 64` overflows the mask); the deployed `b`, a
level's `κ + R`, is in that range. A position past the challenges given reads `0`. -/
def challengePositions (b t : ℕ) (xs : List E) : Fin t → Fin (2 ^ b) := fun q ↦
  ⟨challengeBits (xs.getD (q / (192 / b)) 0) / 2 ^ (q % (192 / b) * b) % 2 ^ b,
    Nat.mod_lt _ (Nat.two_pow_pos b)⟩

/-- A challenge's bits are below `2^192`. -/
private theorem challengeBits_lt (x : E) : challengeBits x < 2 ^ 192 := by
  have := (x.limb 0).toBitVec.isLt
  have := (x.limb 1).toBitVec.isLt
  have := (x.limb 2).toBitVec.isLt
  simp only [challengeBits]
  omega

/-- A challenge is its 192 bits. -/
private theorem challengeBits_bijective :
    Function.Bijective fun x : E ↦ (⟨challengeBits x, challengeBits_lt x⟩ : Fin (2 ^ 192)) := by
  rw [Fintype.bijective_iff_injective_and_card, card_E, Fintype.card_fin]
  refine ⟨fun x y h ↦ ?_, rfl⟩
  simp only [Fin.mk.injEq, challengeBits] at h
  have := (x.limb 0).toBitVec.isLt
  have := (x.limb 1).toBitVec.isLt
  have := (x.limb 2).toBitVec.isLt
  have := (y.limb 0).toBitVec.isLt
  have := (y.limb 1).toBitVec.isLt
  have := (y.limb 2).toBitVec.isLt
  have h0 : (x.limb 0).toBitVec.toNat = (y.limb 0).toBitVec.toNat := by omega
  have h1 : (x.limb 1).toBitVec.toNat = (y.limb 1).toBitVec.toNat := by omega
  have h2 : (x.limb 2).toBitVec.toNat = (y.limb 2).toBitVec.toNat := by omega
  refine E.ext fun i ↦ BF64.toBitVec_injective (BitVec.toNat_inj.mp ?_)
  fin_cases i
  exacts [h0, h1, h2]

/-- **Query positions are uniform.** Let `m` fresh squeezes give `m` independent uniform digests,
enough for `t` positions of `b` bits: `t ≤ m * ⌊192/b⌋`. The `t` positions their challenges give
are `t` independent uniform elements of `Fin (2^b)`: every event of them has its probability
under a uniform `Fin t → Fin (2^b)`. The top `192 - b⌊192/b⌋` bits of each challenge and the
chunks of the last squeeze past position `t` are not read. -/
theorem prEvent_positions_uniform {b t m : ℕ} (ht : t ≤ m * (192 / b))
    (p : (Fin t → Fin (2 ^ b)) → Prop) :
    Pr{let d ← $ᵗ (Fin m → Digest)}[
      p (challengePositions b t (List.ofFn fun i ↦ FsState.challengeOf (d i)))] =
      Pr{let y ← $ᵗ (Fin t → Fin (2 ^ b))}[p y] := by
  have hdvd : (2 ^ b) ^ (192 / b) ∣ 2 ^ 192 := by
    rw [← pow_mul]
    exact pow_dvd_pow 2 (Nat.mul_div_le 192 b)
  refine (prEvent_challengeOf_tuple m fun x ↦ p (challengePositions b t (List.ofFn x))).trans
    (Eq.trans ?_ (prEvent_uniformSample_digitChunks hdvd ht p))
  rw [← SampleableType.prEvent_uniformSample_equiv
    (Equiv.arrowCongr (Equiv.refl (Fin m)) (Equiv.ofBijective _ challengeBits_bijective))]
  congr! with x q
  simp only [challengePositions, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply,
    Equiv.refl_symm, id_eq, Equiv.ofBijective_apply, Fin.coe_modNat, Fin.val_castLE, ← pow_mul,
    mul_comm b, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    Nat.div_lt_of_lt_mul (q.2.trans_le (ht.trans_eq (mul_comm _ _))), dite_true,
    Option.getD_some]
  rfl

/-! ## The chain read off a log -/

/-- The two 32-byte halves of a 64-byte input, read as digests: the chaining value and the block
of a chain step, the two children of a Merkle node. Other inputs carry none. -/
def halves (q : List UInt8) : List Digest :=
  if q.length = 64 then [digestOfBytes q, digestOfBytes (q.drop 32)] else []

/-- The chaining value a 64-byte hash of the chain starts from is a half of its input: a step,
the grinding base, the grinding check. -/
theorem mem_halves_stepBytes (cv : Digest) (x : E) (tag : K) :
    cv ∈ halves (FsState.stepBytes cv x tag) := by
  simp [halves, FsState.stepBytes, FsState.block, length_digestBytes, length_kBytes,
    digestOfBytes_append]

/-- The state an input observes from and the element it absorbs, if it is an observe step. -/
def observed? (q : List UInt8) : Option (Digest × E) :=
  match Block.parse? q with
  | some (cv, .observe x) => some (cv, x)
  | _ => none

/-- The element of the first observe step of a log answered by `cv`. -/
def observedInto (log : hashSpec.QueryLog) (cv : Digest) : Option E :=
  log.findSome? fun e ↦ if e.2 = cv then (observed? e.1).map (·.2) else none

/-- The Merkle roots a log's chains absorb: a root travels as two consecutive observes, so every
observe step from a state that an observe step answers rebuilds the digest the two elements
encode. -/
def rebuiltRoots (log : hashSpec.QueryLog) : List Digest :=
  log.filterMap fun e ↦ (observed? e.1).bind fun p ↦
    (observedInto log p.1).bind fun x₁ ↦ digestOfScalars (x₁, p.2)

/-- The digests in play after a log: `roots` (the seed among them), the halves of every logged
input, and the roots the log's chains absorb. -/
def inPlay (roots : List Digest) (log : hashSpec.QueryLog) : List Digest :=
  roots ++ log.flatMap (fun e ↦ halves e.1) ++ rebuiltRoots log

/-- The digests in play only grow along a log. -/
theorem inPlay_mono (roots : List Digest) :
    ∀ l₁ l₂ : hashSpec.QueryLog, l₁ <+: l₂ → ∀ d ∈ inPlay roots l₁, d ∈ inPlay roots l₂ := by
  rintro l₁ _ ⟨t, rfl⟩ d hd
  simp only [inPlay, List.flatMap_append, List.mem_append] at hd ⊢
  rcases hd with (hd | hd) | hd
  · exact .inl (.inl hd)
  · exact .inl (.inr (.inl hd))
  obtain ⟨e, he, hr⟩ := List.mem_filterMap.mp hd
  simp only [Option.bind_eq_some_iff] at hr
  obtain ⟨p, hp, x₁, hx, hr⟩ := hr
  refine .inr (List.mem_filterMap.mpr ⟨e, List.mem_append_left _ he, ?_⟩)
  simp only [observedInto, List.findSome?_append] at hx ⊢
  simp [hp, hx, hr]

/-- The halves of a logged input are in play once it is asked. -/
theorem halves_mem_inPlay (roots : List Digest) :
    ∀ (l : hashSpec.QueryLog) (e : (_ : List UInt8) × Digest), ∀ d ∈ halves e.1,
      d ∈ inPlay roots (l ++ [e]) :=
  fun _ e _ hd ↦ by simp [inPlay, hd]

/-- The chain's history in a log: from the state `s` back to `seed`, at each state the unique
logged query answered by it that parses as a step, each block with the state it leads to; `none`
when a step is missing or ambiguous. -/
def chainHistory (log : hashSpec.QueryLog) (seed s : FsState) :
    Option (List (Block × Digest)) :=
  HashChain.history Block.parse? log seed.cv s.cv

/-- **The history of a logged chain.** If every step of a chain from `seed` is in the log, the
log has no collision, and no answer is the seed, then the history of the chain's last state is the
chain. -/
theorem chainHistory_of_noCollision_noSeed {log : hashSpec.QueryLog} {seed : FsState}
    (hcoll : ¬ QueryLog.HasCollision log) (hseed : ∀ e ∈ log, e.2 ≠ seed.cv)
    (steps : List (Block × Digest))
    (hchain : ∀ e ∈ HashChain.queries Block.input seed.cv steps, e ∈ log) :
    chainHistory log seed ⟨HashChain.last seed.cv steps⟩ = some steps :=
  HashChain.history_of_noCollision_noSeed Block.parse?_input hcoll hseed steps hchain

/-- **The history before a query.** If every step of a chain from `seed` is in a consistent log
with no collision and no hit on the digests in play (`roots`, which hold the seed, the halves of
earlier inputs, the roots earlier chains absorb), then at a position whose query has the chain's
last state as a half and is none of the chain's own queries (the next step, the grinding base or
check), the history of the chain's last state in the entries before it is the chain. -/
theorem chainHistory_take_of_noCollision_noHit {log : hashSpec.QueryLog} {seed : FsState}
    {roots : List Digest} (hcons : QueryLog.Consistent log) (hcoll : ¬ QueryLog.HasCollision log)
    (hhit : ¬ QueryLog.HasHit (inPlay roots) log) (hseed : seed.cv ∈ roots)
    (steps : List (Block × Digest))
    (hchain : ∀ e ∈ HashChain.queries Block.input seed.cv steps, e ∈ log) {m : ℕ}
    (hm : m < log.length) (hq : HashChain.last seed.cv steps ∈ halves log[m].1)
    (hnew : ∀ e ∈ HashChain.queries Block.input seed.cv steps, e.1 ≠ log[m].1) :
    chainHistory (log.take m) seed ⟨HashChain.last seed.cv steps⟩ = some steps :=
  HashChain.history_take_of_noCollision_noHit Block.parse?_input
    (fun cv b ↦ mem_halves_stepBytes cv b.elem b.tag) (halves_mem_inPlay roots)
    (inPlay_mono roots) (by simp [inPlay, hseed]) hcons hcoll hhit steps hchain hm hq hnew

/-- **The history before the next step.** Under the hypotheses of
`chainHistory_take_of_noCollision_noHit`, at a position where the chain's next step is asked, the
history of the chain's last state in the entries before it is the chain. -/
theorem chainHistory_take_of_step {log : hashSpec.QueryLog} {seed : FsState}
    {roots : List Digest} (hcons : QueryLog.Consistent log) (hcoll : ¬ QueryLog.HasCollision log)
    (hhit : ¬ QueryLog.HasHit (inPlay roots) log) (hseed : seed.cv ∈ roots)
    (steps : List (Block × Digest))
    (hchain : ∀ e ∈ HashChain.queries Block.input seed.cv steps, e ∈ log) {m : ℕ}
    (hm : m < log.length) {b : Block}
    (hq : log[m].1 = Block.input (HashChain.last seed.cv steps) b) :
    chainHistory (log.take m) seed ⟨HashChain.last seed.cv steps⟩ = some steps :=
  HashChain.history_take_of_step Block.parse?_input
    (fun cv b ↦ mem_halves_stepBytes cv b.elem b.tag) (halves_mem_inPlay roots)
    (inPlay_mono roots) (by simp [inPlay, hseed]) hcons hcoll hhit steps hchain hm hq

/-- **Histories are determined.** Without a collision in the log, a history found in the log's
first `k` entries is the history in the whole log. -/
theorem chainHistory_determined {log : hashSpec.QueryLog} {seed s : FsState} {k : ℕ}
    {hs : List (Block × Digest)} (hcoll : ¬ QueryLog.HasCollision log)
    (h : chainHistory (log.take k) seed s = some hs) : chainHistory log seed s = some hs :=
  HashChain.history_determined hcoll h

/-- **The history before a state is in play.** Under the hypotheses of
`chainHistory_take_of_noCollision_noHit`, if the chain's last state is in play after the first
`m` entries, its history in those entries is the chain. -/
theorem chainHistory_take_of_mem_inPlay {log : hashSpec.QueryLog} {seed : FsState}
    {roots : List Digest} (hcons : QueryLog.Consistent log) (hcoll : ¬ QueryLog.HasCollision log)
    (hhit : ¬ QueryLog.HasHit (inPlay roots) log) (hseed : seed.cv ∈ roots)
    (steps : List (Block × Digest))
    (hchain : ∀ e ∈ HashChain.queries Block.input seed.cv steps, e ∈ log) {m : ℕ}
    (hq : HashChain.last seed.cv steps ∈ inPlay roots (log.take m)) :
    chainHistory (log.take m) seed ⟨HashChain.last seed.cv steps⟩ = some steps :=
  HashChain.history_take_of_mem_inPlay Block.parse?_input
    (fun cv b ↦ mem_halves_stepBytes cv b.elem b.tag) (halves_mem_inPlay roots)
    (inPlay_mono roots) (by simp [inPlay, hseed]) hcons hcoll hhit steps hchain hq

/-- The state a step parses from is a half of its input. -/
theorem mem_halves_of_parse? {q : List UInt8} {x : Digest} {b : Block}
    (h : Block.parse? q = some (x, b)) : x ∈ halves q := by
  unfold Block.parse? at h
  split at h
  · rename_i hlen
    have hx : x = digestOfBytes q := by
      dsimp only at h
      split at h
      · cases h; rfl
      · split at h
        · cases h; rfl
        · split at h
          · cases h; rfl
          · cases h
    simp [halves, hlen, hx]
  · cases h

/-- **One more query.** An answer not in play before its query leaves the history of every other
state unchanged. -/
theorem chainHistory_append {log : hashSpec.QueryLog} {roots : List Digest}
    {e : (_ : List UInt8) × Digest} (hu : e.2 ∉ inPlay roots log) (seed : FsState) {s : FsState}
    (hs : s.cv ≠ e.2) : chainHistory (log ++ [e]) seed s = chainHistory log seed s := by
  refine HashChain.history_append_of_not_start (fun e' he p hp hpu ↦ hu ?_) hs
  obtain ⟨x, b⟩ := p
  simp only at hpu
  subst hpu
  simp only [inPlay, List.mem_append, List.mem_flatMap]
  exact .inl (.inr ⟨e', he, mem_halves_of_parse? hp⟩)

/-- **Deduplication.** In a consistent log, a history is that of the log with each input at its
first occurrence only. -/
theorem chainHistory_dedupKeys {log : hashSpec.QueryLog} (hcons : QueryLog.Consistent log)
    (seed s : FsState) : chainHistory (QueryLog.dedupKeys log) seed s = chainHistory log seed s :=
  HashChain.history_dedupKeys hcons s.cv

/-- In a consistent log, the observe step into a state is the one found after deduplication. -/
theorem observedInto_dedupKeys {log : hashSpec.QueryLog} (hcons : QueryLog.Consistent log)
    (cv : Digest) : observedInto (QueryLog.dedupKeys log) cv = observedInto log cv :=
  QueryLog.findSome?_dedupKeys hcons _

/-- In a consistent log, the digests in play are those of the log with each input at its first
occurrence only. -/
theorem inPlay_dedupKeys (roots : List Digest) {log : hashSpec.QueryLog}
    (hcons : QueryLog.Consistent log) (d : Digest) :
    d ∈ inPlay roots (QueryLog.dedupKeys log) ↔ d ∈ inPlay roots log := by
  simp only [inPlay, rebuiltRoots, observedInto_dedupKeys hcons, List.mem_append,
    List.mem_flatMap, List.mem_filterMap, QueryLog.mem_dedupKeys_iff hcons]

/-- A query has at most two halves. -/
theorem length_halves_le (q : List UInt8) : (halves q).length ≤ 2 := by
  unfold halves
  split <;> simp

/-- At most the roots, two halves per entry and one absorbed root per entry are in play. -/
theorem length_inPlay_le (roots : List Digest) (log : hashSpec.QueryLog) :
    (inPlay roots log).length ≤ roots.length + 3 * log.length := by
  have h1 : (log.flatMap fun e ↦ halves e.1).length ≤ 2 * log.length := by
    induction log with
    | nil => simp
    | cons e log ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have := length_halves_le e.1
      omega
  have h2 : (rebuiltRoots log).length ≤ log.length := List.length_filterMap_le _ _
  simp only [inPlay, List.length_append]
  omega

end
end LeanerVM.Protocol
