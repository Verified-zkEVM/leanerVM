/-
  LeanVM.E2E.Reduction.World

  The schemes' world for the reductions of T5: the game's queries as queries of the signature
  schemes' oracle world (a digest as 256 bits), and the transport of the game's run to that
  world's lazy random oracle.
-/

module

public import LeanVM.E2E.Bridge
public import LeanVM.E2E.Runs
public import LeanXmss.MultiUserStatement

/-!
# The schemes' world

The signature schemes' security games (`LeanXmss.MultiUser`, `Sphincs.Security.Multi`) run in
`OracleWorld = unifSpec + (List UInt8 →ₒ BitVec 256)` against VCVio's lazy random oracle on a
cache (`randomOracle`), the coins forwarded. The game (`game`) runs in `GameSpec`, a hash answered
by a digest, against the logged oracle (`Rom.loggedRO`). This module relates the two.

**Digests as bits** (`digestBits_bijective`). `digestBits`, a digest's 32 bytes little-endian, is
a bijection `Digest ≃ BitVec 256` (`digestEquiv`); `bitsDigest` is its inverse.

**The game's queries in the schemes' world** (`toW`): a coin query forwarded, a hash query the
schemes' query read back as a digest.

**The transport** (`evalDistEq_run_toW`). The run of a game computation against the logged
oracle from a log `ℓ`, its final log read as the cache of its answers' bits (`bitsCache`), has
the distribution of the run of its translation by `toW` against the schemes' lazy random oracle
(`owImpl`) from the cache of `ℓ`'s answers: the two oracles agree on cached points, and a fresh
uniform digest read as bits is a fresh uniform 256-bit answer.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-! ## Digests as bits -/

/-- The little-endian value of a byte list. -/
theorem foldr_bytes_lt : ∀ l : List UInt8,
    l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 < 256 ^ l.length
  | [] => by simp
  | b :: l => by
    have h := foldr_bytes_lt l
    have hb := b.toNat_lt
    simp only [List.foldr_cons, List.length_cons, pow_succ]
    omega

/-- The little-endian value of byte lists of one length is injective. -/
theorem foldr_bytes_inj : ∀ {l l' : List UInt8}, l.length = l'.length →
    l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 = l'.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 →
      l = l'
  | [], [], _, _ => rfl
  | b :: l, b' :: l', hlen, h => by
    simp only [List.foldr_cons] at h
    have hb := b.toNat_lt
    have hb' := b'.toNat_lt
    have h1 : b.toNat = b'.toNat := by omega
    have h2 : l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 =
        l'.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 := by omega
    rw [UInt8.toNat_inj.mp h1, foldr_bytes_inj (by simpa using hlen) h2]

/-- **`digestBits` is injective.** -/
theorem digestBits_injective : Function.Injective digestBits := by
  intro d d' h
  unfold digestBits at h
  have hl := Guest.Binding.length_digestBytes d
  have hl' := Guest.Binding.length_digestBytes d'
  have hv := foldr_bytes_lt (digestBytes d)
  have hv' := foldr_bytes_lt (digestBytes d')
  rw [hl] at hv
  rw [hl'] at hv'
  have h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using hv),
    Nat.mod_eq_of_lt (by simpa using hv')] at h'
  exact Guest.Binding.digestBytes_inj (foldr_bytes_inj (hl.trans hl'.symm) h')

/-- **`digestBits` is a bijection** `Digest ≃ BitVec 256`. -/
theorem digestBits_bijective : Function.Bijective digestBits := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨digestBits_injective, by rw [card_digest]; simp⟩

/-- Digests as bits. -/
noncomputable def digestEquiv : Digest ≃ BitVec 256 := Equiv.ofBijective _ digestBits_bijective

/-- The digest of 256 bits (`digestBits`'s inverse). -/
noncomputable def bitsDigest (v : BitVec 256) : Digest := digestEquiv.symm v

/-- A digest's bits read back. -/
@[simp] theorem bitsDigest_digestBits (d : Digest) : bitsDigest (digestBits d) = d :=
  digestEquiv.symm_apply_apply d

/-- Bits read as a digest and back. -/
@[simp] theorem digestBits_bitsDigest (v : BitVec 256) : digestBits (bitsDigest v) = v :=
  digestEquiv.apply_symm_apply v

/-! ## The schemes' world -/

/-- The schemes' oracle world: coins and a hash with 256-bit answers (`LeanXmss.OracleWorld`). -/
abbrev OW : OracleSpec (ℕ ⊕ List UInt8) := LeanXmss.OracleWorld

/-- A digest as the schemes' hash output. -/
def hBits (d : Digest) : LeanXmss.HashOutput := digestBits d

/-- The schemes' hash output as a digest. -/
noncomputable def bitsD (v : LeanXmss.HashOutput) : Digest := bitsDigest v

/-- A digest's output read back. -/
@[simp] theorem bitsD_hBits (d : Digest) : bitsD (hBits d) = d := bitsDigest_digestBits d

/-- An output read as a digest and back. -/
@[simp] theorem hBits_bitsD (v : LeanXmss.HashOutput) : hBits (bitsD v) = v :=
  digestBits_bitsDigest v

/-- **The game's queries in the schemes' world**: a coin query forwarded, a hash query the
schemes' query read as a digest. -/
noncomputable def toW : QueryImpl GameSpec (OracleComp OW)
  | .inl n => (liftM (OW.query (.inl n)) : OracleComp OW (Fin (n + 1)))
  | .inr x => bitsD <$> (liftM (OW.query (.inr x)) : OracleComp OW LeanXmss.HashOutput)

/-- The schemes' lazy random oracle, the coins forwarded (the schemes' `countedOracle` without
the count). -/
noncomputable abbrev owImpl :
    QueryImpl OW (StateT (QueryCache LeanXmss.HashSpec) ProbComp) :=
  unifFwdImpl LeanXmss.HashSpec +
    (randomOracle : QueryImpl LeanXmss.HashSpec (StateT (QueryCache LeanXmss.HashSpec) ProbComp))

/-- The cache of a log: its answers as outputs. -/
def logCache (ℓ : Log) : QueryCache LeanXmss.HashSpec :=
  QueryCache.ofFn fun x ↦ hBits <$> look ℓ x

/-- The cache of a log answers its answers as outputs. -/
theorem logCache_apply (ℓ : Log) (x : List UInt8) : logCache ℓ x = hBits <$> look ℓ x := rfl

/-- The cache of the empty log is empty. -/
theorem logCache_nil : logCache [] = ∅ := by
  refine QueryCache.ext fun x ↦ ?_
  rfl

/-- A fresh entry of a log is cached. -/
theorem logCache_append_fresh {ℓ : Log} {x : Bytes} (h : look ℓ x = none) (u : Digest) :
    logCache (ℓ ++ [(x, u)]) = (logCache ℓ).cacheQuery x (hBits u) := by
  refine QueryCache.ext fun y ↦ ?_
  rw [logCache_apply]
  by_cases hy : y = x
  · subst hy
    rw [QueryCache.cacheQuery_self]
    change hBits <$> logLookup (ℓ ++ [(y, u)]) y = _
    rw [logLookup_append_singleton ℓ y y u h]
    simp
  · rw [QueryCache.cacheQuery_of_ne _ _ hy, logCache_apply]
    change hBits <$> logLookup (ℓ ++ [(x, u)]) y = _
    rw [logLookup_append_singleton ℓ x y u h]
    simp [hy]

/-- A uniform digest read as an output is uniform. -/
theorem hBits_uniform (x : List UInt8) [SampleableType (LeanXmss.HashSpec.Range x)] :
    (hBits <$> ($ᵗ Digest : ProbComp Digest)) =ᵈ
      ($ᵗ LeanXmss.HashSpec.Range x : ProbComp LeanXmss.HashOutput) := by
  rw [evalDistEq_iff_forall_prEvent_eq_output]
  intro v
  rw [prEvent_map]
  have h : (fun d : Digest ↦ hBits d = v) = (fun d ↦ d = bitsD v) := by
    funext d
    exact propext ⟨fun h ↦ h ▸ (bitsD_hBits d).symm, fun h ↦ h ▸ hBits_bitsD v⟩
  rw [h, SampleableType.prEvent_uniformSample_eq_singleton,
    SampleableType.prEvent_uniformSample_eq_singleton, card_digest]
  simp [LeanXmss.hashOutputBits]

/-- **The state projection in distribution**: if every step of `impl₁`, its state mapped by
`proj`, has the distribution of `impl₂`'s step from the mapped state, so has every run. -/
theorem evalDistEq_map_run_simulateQ {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ₁ σ₂ α : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂)
    (h : ∀ t s, Prod.map id proj <$> (impl₁ t).run s =ᵈ (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s =ᵈ (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun p ↦ ih p.1 p.2) ?_
    rw [show ((impl₁ t).run s >>= fun p ↦ (simulateQ impl₂ (k p.1)).run (proj p.2)) =
      (Prod.map id proj <$> (impl₁ t).run s) >>= fun p ↦ (simulateQ impl₂ (k p.1)).run p.2 by
        rw [bind_map_left]; rfl]
    exact (h t s).bind fun _ ↦ .rfl

/-- One step of the transport: the game's oracle against the schemes' through `toW`. -/
theorem evalDistEq_step_toW (t : GameSpec.Domain) (ℓ : Log) :
    Prod.map id logCache <$> (gameImpl t).run ℓ =ᵈ ((owImpl ∘ₛ toW) t).run (logCache ℓ) := by
  rcases t with n | x
  · change Prod.map id logCache <$> (coinImpl n).run ℓ =ᵈ
      (simulateQ owImpl (liftM (OW.query (.inl n)) : OracleComp OW _)).run (logCache ℓ)
    simp only [coinImpl, simulateQ_spec_query, QueryImpl.liftTarget_apply, QueryImpl.add_apply_inl,
      unifFwdImpl]
    simp [Prod.map]
  · change Prod.map id logCache <$> (Rom.loggedRO x).run ℓ =ᵈ
      (simulateQ owImpl (bitsD <$> (liftM (OW.query (.inr x)) : OracleComp OW _))).run
        (logCache ℓ)
    have hro := loggedRO_isLazySampler (D := Bytes) (R := Digest) x ℓ
    rw [hro, simulateQ_map, StateT.run_map, simulateQ_spec_query,
      show owImpl (.inr x) = randomOracle x from rfl, randomOracle.run_eq]
    rcases h : look ℓ x with _ | d
    · change logLookup ℓ x = none at h
      have hc : logCache ℓ x = none := by
        rw [logCache_apply]; change hBits <$> logLookup ℓ x = _; rw [h]; rfl
      simp only [h, hc]
      rw [map_bind, map_bind]
      simp only [map_pure, Prod.map, id, logCache_append_fresh h]
      refine EvalDistEq.trans ?_ ((hBits_uniform x).bind (g := fun u ↦
        (pure (bitsD u, (logCache ℓ).cacheQuery x u) : ProbComp _)) fun _ ↦ .rfl)
      rw [bind_map_left]
      simp
    · change logLookup ℓ x = some d at h
      have hc : logCache ℓ x = some (hBits d) := by
        rw [logCache_apply]; change hBits <$> logLookup ℓ x = _; rw [h]; rfl
      simp only [h, hc]
      simp [Prod.map]

/-- **The transport.** The run of a game computation against the logged oracle from `ℓ`, its
final log read as a cache, has the distribution of the run of its translation by `toW` against
the schemes' lazy random oracle from `ℓ`'s cache. -/
theorem evalDistEq_run_toW {α : Type} (oa : OracleComp GameSpec α) (ℓ : Log) :
    Prod.map id logCache <$> (simulateQ gameImpl oa).run ℓ =ᵈ
      (simulateQ owImpl (simulateQ toW oa)).run (logCache ℓ) := by
  rw [← QueryImpl.simulateQ_compose]
  exact evalDistEq_map_run_simulateQ _ _ _ evalDistEq_step_toW oa ℓ

/-- **The transport from the empty log**, to the empty cache. -/
theorem evalDistEq_run_toW_nil {α : Type} (oa : OracleComp GameSpec α) :
    Prod.map id logCache <$> (simulateQ gameImpl oa).run [] =ᵈ
      (simulateQ owImpl (simulateQ toW oa)).run ∅ := by
  rw [← logCache_nil]
  exact evalDistEq_run_toW oa []

end
end LeanVM.E2E
