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
* `chainHistory_determined`: without a collision, a history once in the log does not change.
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

/-- The first half of a bijection pushes a uniform sample to a uniform sample. -/
private theorem prEvent_uniformSample_fst_of_bijective {α β γ : Type} [SampleableType α]
    [SampleableType β] [SampleableType γ] {f : α → β} {g : α → γ}
    (h : Function.Bijective fun x ↦ (f x, g x)) (p : β → Prop) :
    Pr{let x ← $ᵗ α}[p (f x)] = Pr{let y ← $ᵗ β}[p y] :=
  (SampleableType.prEvent_uniformSample_comp_of_bijective h fun z ↦ p z.1).trans
    (SampleableType.prEvent_uniformSample_fst p)

/-- Two digests with the same eight words are equal. -/
private theorem digest_ext {d d' : Digest} (h0 : d[0] = d'[0]) (h1 : d[1] = d'[1])
    (h2 : d[2] = d'[2]) (h3 : d[3] = d'[3]) (h4 : d[4] = d'[4]) (h5 : d[5] = d'[5])
    (h6 : d[6] = d'[6]) (h7 : d[7] = d'[7]) : d = d' := by
  refine Vector.ext fun i hi ↦ ?_
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7
  | _ + 8, hi => omega

/-- A digest is its challenge and its last two words. -/
private theorem challengeOf_bijective :
    Function.Bijective fun d : Digest ↦ (FsState.challengeOf d, (d[6], d[7])) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun d d' h ↦ ?_, ?_⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨hc, h6, h7⟩ := h
    have hl : ∀ i, (FsState.challengeOf d).limb i = (FsState.challengeOf d').limb i :=
      fun i ↦ congrArg (·.limb i) hc
    have l0 := hl 0
    have l1 := hl 1
    have l2 := hl 2
    simp only [FsState.challengeOf, limb_ofLimbs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] at l0 l1 l2
    exact digest_ext (by simpa [lowWord_ofWords] using congrArg lowWord l0)
      (by simpa [highWord_ofWords] using congrArg highWord l0)
      (by simpa [lowWord_ofWords] using congrArg lowWord l1)
      (by simpa [highWord_ofWords] using congrArg highWord l1)
      (by simpa [lowWord_ofWords] using congrArg lowWord l2)
      (by simpa [highWord_ofWords] using congrArg highWord l2) h6 h7
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

private theorem firstWord_lt (d : Digest) : firstWord d < 2 ^ 64 := by
  have := d[0].toNat_lt
  have := d[1].toNat_lt
  unfold firstWord
  omega

/-- A digest is the low `bits` bits and the rest of its first 64-bit word, and its last six
words. -/
private theorem lowBits_bijective {bits : ℕ} (hb : bits ≤ 64) :
    Function.Bijective fun d : Digest ↦
      ((⟨firstWord d % 2 ^ bits, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ bits)),
        ((⟨firstWord d / 2 ^ bits, by
            rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hb]
            exact firstWord_lt d⟩ : Fin (2 ^ (64 - bits))),
          #v[d[2], d[3], d[4], d[5], d[6], d[7]])) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun d d' h ↦ ?_, ?_⟩
  · simp only [Prod.mk.injEq, Fin.mk.injEq, Vector.mk_eq, Array.mk.injEq, List.cons.injEq,
      and_true] at h
    obtain ⟨hlo, hhi, h2, h3, h4, h5, h6, h7⟩ := h
    have hw : firstWord d = firstWord d' := by
      rw [← Nat.div_add_mod (firstWord d) (2 ^ bits), ← Nat.div_add_mod (firstWord d') (2 ^ bits),
        hlo, hhi]
    have := d[0].toNat_lt
    have := d[1].toNat_lt
    have := d'[0].toNat_lt
    have := d'[1].toNat_lt
    unfold firstWord at hw
    exact digest_ext (UInt32.toNat_inj.mp (by omega)) (UInt32.toNat_inj.mp (by omega))
      h2 h3 h4 h5 h6 h7
  · rw [card_digest, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_congr (arrayVectorEquivFin UInt32 6), Fintype.card_fun, Fintype.card_fin,
      ← FinEnum.card_eq_fintypeCard, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hb]
    rfl

/-- **The grinding check of a uniform digest.** A uniform digest has `bits ≤ 64` low zero bits
in its first 64-bit word with probability `2^-bits`. -/
theorem prEvent_lowBitsZero {bits : ℕ} (hb : bits ≤ 64) :
    Pr{let d ← $ᵗ Digest}[FsState.lowBitsZero d bits = true] = (2 ^ bits : ℝ≥0∞)⁻¹ := by
  have hpos : 0 < 2 ^ bits := by positivity
  have h := prEvent_uniformSample_fst_of_bijective (lowBits_bijective hb)
    (fun y ↦ y = ⟨0, hpos⟩)
  simp only [Fin.mk.injEq] at h
  have hev : ∀ d : Digest, (FsState.lowBitsZero d bits = true) = (firstWord d % 2 ^ bits = 0) :=
    fun d ↦ by simp [FsState.lowBitsZero, firstWord]
  simp only [hev]
  rw [h, SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat]

/-! ## The chain read off a log -/

/-- The two 32-byte halves of a 64-byte input, read as digests: the chaining value and the block
of a chain step, the two children of a Merkle node. Other inputs carry none. -/
def halves (q : List UInt8) : List Digest :=
  if q.length = 64 then [digestOfBytes q, digestOfBytes (q.drop 32)] else []

/-- The chaining value a 64-byte hash of the chain starts from is a half of its input: a step,
the grinding base, the grinding check. -/
theorem mem_halves_stepBytes (cv : Digest) (x : E) (tag : K) :
    cv ∈ halves (FsState.stepBytes cv x tag) := by
  have hlen : (FsState.stepBytes cv x tag).length = 64 := by
    simp [FsState.stepBytes, FsState.block, length_digestBytes, length_kBytes]
  simp only [halves, hlen, ↓reduceIte]
  simp [FsState.stepBytes, digestOfBytes_append]

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
private theorem inPlay_mono (roots : List Digest) :
    ∀ l₁ l₂ : hashSpec.QueryLog, l₁ <+: l₂ → ∀ d ∈ inPlay roots l₁, d ∈ inPlay roots l₂ := by
  intro l₁ l₂ hpre d hd
  obtain ⟨t, rfl⟩ := hpre
  simp only [inPlay, List.mem_append, List.mem_flatMap] at hd ⊢
  rcases hd with (hd | ⟨e, he, hd⟩) | hd
  · exact Or.inl (Or.inl hd)
  · exact Or.inl (Or.inr ⟨e, Or.inl he, hd⟩)
  · right
    obtain ⟨e, he, hr⟩ := List.mem_filterMap.mp hd
    refine List.mem_filterMap.mpr ⟨e, List.mem_append_left _ he, ?_⟩
    rcases ho : observed? e.1 with _ | p
    · simp [ho] at hr
    · simp only [ho, Option.bind_some] at hr ⊢
      rcases hx : observedInto l₁ p.1 with _ | x₁
      · simp [hx] at hr
      · have : observedInto (l₁ ++ t) p.1 = some x₁ := by
          rw [observedInto, List.findSome?_append, ← observedInto, hx, Option.some_or]
        rw [this]
        simpa [hx] using hr

/-- The halves of a logged input are in play once it is asked. -/
private theorem halves_mem_inPlay (roots : List Digest) :
    ∀ (l : hashSpec.QueryLog) (e : (_ : List UInt8) × Digest), ∀ d ∈ halves e.1,
      d ∈ inPlay roots (l ++ [e]) := by
  intro l e d hd
  simp only [inPlay, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨e, Or.inr (List.mem_singleton_self e), hd⟩)

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

end
end LeanerVM.Protocol
