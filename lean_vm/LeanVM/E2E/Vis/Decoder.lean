/-
  LeanVM.E2E.Vis.Decoder

  W-vis, P3a: on a log without the format event, the decoders of T1 and W6 decode no hidden
  prefix, so a fresh hidden query starts no record. Their potentials then rise at a hidden query
  only through failure, and are at most the failure indicator on the key-generation log.
-/

module

public import LeanVM.E2E.Vis.Shape
public import LeanVM.E2E.Batch
public import LeanVM.Protocol.EndToEnd.Sound.Statements

/-!
# The decoder invariant (W-vis, P3a)

The random-oracle theorem's decoder (`LeanVM.Protocol.Compile.Rom.Decode`) reads a record only
at a chain step `cv ‖ (x, tag)` from a decoded state `cv`, or at a seeding's last input
`d ‖ s` (`s` 32 bytes), `d` the answer to the seeding's penultimate input. A hidden input
(`Hid keys`) whose first 32 bytes are a digest `c`, followed by 32 bytes, has `c` a hidden
prefix (`inPfx_of_hid_digest_append`). So it suffices that

* every non-hidden entry has an answer that is no hidden prefix (`NotHidOut`). This follows from
  `¬ FormatI keys k0 ℓ` when the first `k0` entries are hidden (`notHidOut_of_not_formatI`);
* the seeding's penultimate input is never hidden (`SeedsNotHid`): for leanVM it is
  `ivPrefix ‖ d`, and for the batching it is the label (`seedsNotHid_leanVmSeeds`,
  `seedsNotHid_batchSeedsAll`).

Then, by induction on the log, every decoded digest comes from a non-hidden entry, so it is no
hidden prefix (`decode_info_not_inPfx`), and a hidden entry is read as nothing
(`step_of_hid`).

## The potentials

* `pot_step_hid`: a fresh hidden query raises T1's potential by at most the failure term
  `(4 + k)(|ℓ| + 1)/|Digest|`. Old records are supermartingales (`term_step_old`) and the new
  record is `none`.
* `potStop_step_hid`: the same for the stopped potential `pot · 1[¬ FormatI]`
  (`sum_stop_le_of_step`).
* `pot_le_of_allHid`, `termSum_eq_zero_of_allHid`: on a log of hidden entries only (key
  generation) every record is `none`.
* The batching's potential `batchPot` (W6) reads the log from its constant start `s0`
  (`startLog`). With `s0` no hidden prefix, the same holds there (`batchPotStop_step_hid`,
  `batchPot_le_of_allHid`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom LeanVM.Node LeanVM.Guest.Batch
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## The stopped step -/

section Stop

variable {nx ns : ℕ} [Sphincs.Params]

/-- The format event persists. -/
theorem FormatI.append {keys : Keys nx ns} {k0 : ℕ} {ℓ : Log} (h : FormatI keys k0 ℓ)
    (ℓ' : Log) : FormatI keys k0 (ℓ ++ ℓ') := by
  obtain ⟨i, hi, hk, hd, hp⟩ := h
  refine ⟨i, by rw [List.length_append]; omega, hk, ?_, ?_⟩
  · rwa [List.getElem_append_left hi]
  · rwa [List.getElem_append_left hi]

/-- **The stopped step.** A step bound for `Φ`, needed only before the format event, is one for
the stopped potential `Φ · 1[¬ FormatI]`. -/
theorem sum_stop_le_of_step (keys : Keys nx ns) (k0 : ℕ) {Φ : Log → ℝ≥0∞} {δ : ℝ≥0∞} {ℓ : Log}
    {t : Bytes}
    (h : ¬ FormatI keys k0 ℓ → (∑ u, Φ (ℓ ++ [(t, u)])) / Fintype.card Digest ≤ Φ ℓ + δ) :
    (∑ u, Φ (ℓ ++ [(t, u)]) * ind (¬ FormatI keys k0 (ℓ ++ [(t, u)]))) /
        Fintype.card Digest ≤ Φ ℓ * ind (¬ FormatI keys k0 ℓ) + δ := by
  by_cases hF : FormatI keys k0 ℓ
  · have h0 : ∀ u, Φ (ℓ ++ [(t, u)]) * ind (¬ FormatI keys k0 (ℓ ++ [(t, u)])) = 0 := fun u ↦ by
      rw [ind_of_not (not_not.mpr (hF.append _)), mul_zero]
    simp only [h0, Finset.sum_const_zero, ENNReal.zero_div]
    exact bot_le
  · rw [ind_of hF, mul_one]
    refine le_trans (ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ ?_) _) (h hF)
    calc Φ (ℓ ++ [(t, u)]) * ind (¬ FormatI keys k0 (ℓ ++ [(t, u)]))
        ≤ Φ (ℓ ++ [(t, u)]) * 1 := by gcongr; exact ind_le_one _
      _ = Φ (ℓ ++ [(t, u)]) := mul_one _

end Stop

/-! ## Hidden inputs that start with a digest -/

section Shape

variable {nx ns : ℕ} [Sphincs.Params]

/-- An honest key's parameter has 16 bytes. -/
theorem keyParam_length_of_mem {keys : Keys nx ns} {p : Bytes} (hp : p ∈ keyParams keys) :
    p.length = 16 := by
  unfold keyParams at hp
  rcases List.mem_append.mp hp with h | h <;>
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h <;> simp [LeanXmss.bytesLE, Sphincs.bytesLE]

omit [Sphincs.Params] in
/-- The parameter derivation's prefix has 32 bytes. -/
theorem paramPrefix_length : paramPrefix.length = 32 := by decide

/-- **A hidden input that starts with a digest**, followed by neither 8 nor 11 bytes (the seed
derivations' tails), has that digest as a hidden prefix. -/
theorem inPfx_of_hid_digest_append {keys : Keys nx ns} {c : Digest} {b : Bytes}
    (hb8 : b.length ≠ 8) (hb11 : b.length ≠ 11) (h : Hid keys (digestBytes c ++ b)) :
    InPfx keys c := by
  have hl : (digestBytes c ++ b).length = 32 + b.length := by
    simp [digestBytes_length]
  rcases h with ⟨p, hp, a, ha, r, hr⟩ | h
  · have hp16 := keyParam_length_of_mem hp
    refine Or.inl ⟨p, hp, a, ha, ?_⟩
    have hpa : (p ++ a).length = 32 := by simp [hp16, ha.1]
    have := congrArg (List.take 32) hr
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.take_append_of_le_length (by rw [digestBytes_length]),
      List.take_of_length_le (by rw [digestBytes_length])] at this
    exact this.symm
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, r, hr⟩
    · omega
    · omega
    · refine Or.inr ?_
      have := congrArg (List.take 32) hr
      rw [List.take_append_of_le_length (by rw [paramPrefix_length]),
        List.take_of_length_le (by rw [paramPrefix_length]),
        List.take_append_of_le_length (by rw [digestBytes_length]),
        List.take_of_length_le (by rw [digestBytes_length])] at this
      exact this.symm

/-- A chain input whose state is no hidden prefix is not hidden. -/
theorem not_hid_chain_of_not_inPfx {keys : Keys nx ns} {c : Digest} (hc : ¬ InPfx keys c)
    (x : E) (tag : ℕ) : ¬ Hid keys (digestBytes c ++ blockOf x tag) := fun h ↦
  hc (inPfx_of_hid_digest_append (by rw [blockOf_length]; decide)
    (by rw [blockOf_length]; decide) h)

end Shape

/-! ## Non-hidden entries answer no hidden prefix -/

section Out

variable {nx ns : ℕ} [Sphincs.Params]

/-- **Every non-hidden entry of the log answers no hidden prefix.** -/
def NotHidOut (keys : Keys nx ns) (ℓ : Log) : Prop :=
  ∀ e ∈ ℓ, ¬ Hid keys e.1 → ¬ InPfx keys e.2

/-- A log whose entries are among another's inherits the property. -/
theorem NotHidOut.of_subset {keys : Keys nx ns} {ℓ ℓ' : Log} (h : NotHidOut keys ℓ')
    (hs : ∀ e ∈ ℓ, e ∈ ℓ') : NotHidOut keys ℓ := fun e he ↦ h e (hs e he)

/-- A prefix of the log inherits the property. -/
theorem NotHidOut.of_append {keys : Keys nx ns} {ℓ ℓ' : Log} (h : NotHidOut keys (ℓ ++ ℓ')) :
    NotHidOut keys ℓ := h.of_subset fun _ he ↦ List.mem_append_left _ he

/-- A log of hidden entries has the property. -/
theorem notHidOut_of_allHid {keys : Keys nx ns} {ℓ : Log} (hall : ∀ e ∈ ℓ, Hid keys e.1) :
    NotHidOut keys ℓ := fun e he hn ↦ absurd (hall e he) hn

/-- **Without the format event**, and with the first `k0` entries hidden, every non-hidden
entry answers no hidden prefix. -/
theorem notHidOut_of_not_formatI {keys : Keys nx ns} {ℓ : Log} {k0 : ℕ}
    (hkg : ∀ (i : ℕ) (hi : i < ℓ.length), i < k0 → Hid keys ℓ[i].1)
    (hF : ¬ FormatI keys k0 ℓ) : NotHidOut keys ℓ := by
  intro e he hn hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  refine hF ⟨i, hi, ?_, fun hd ↦ hn (Or.inr hd), hp⟩
  by_contra hlt
  exact hn (hkg i hi (by omega))

omit [Sphincs.Params] in
/-- A log's answer is an entry of the log. -/
theorem mem_of_look_eq_some {ℓ : Log} {x : Bytes} {v : Digest} (h : look ℓ x = some v) :
    (x, v) ∈ ℓ := by
  obtain ⟨i, hi, he, -⟩ := (look_eq_some_iff ℓ x v).mp h
  exact he ▸ List.getElem_mem hi

end Out

/-! ## The seedings -/

section Seeds

variable {nx ns : ℕ} [Sphincs.Params]

/-- **The seeding's penultimate input is not hidden**: the first input when there is one step,
and every step but the last otherwise. -/
def SeedsNotHid (keys : Keys nx ns) {X : Type} (σ : Seeds X) : Prop :=
  ∀ x, ((σ.seed x).steps.length = 1 → ¬ Hid keys (σ.seed x).first) ∧
    ∀ a ∈ (σ.seed x).steps.dropLast, ∀ d, ¬ Hid keys (Seed.input a d)

omit [Sphincs.Params] in
/-- The last pending input of seeding steps: the last step's, at the answer to the first step
(the start `d`, for one step) or to a step before it. -/
theorem goPend_last_true (H : Bytes → Option Digest) :
    ∀ (as : List (Bytes × Bytes)) (d : Digest) (t : Bytes), goPend H as d = some (t, true) →
      ∃ a d', as.getLast? = some a ∧ t = Seed.input a d' ∧
        ((d' = d ∧ as.length = 1) ∨ ∃ a' ∈ as.dropLast, ∃ d'', H (Seed.input a' d'') = some d')
  | [], _, _, h => by simp [goPend] at h
  | a :: rest, d, t, h => by
    simp only [goPend] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq, List.isEmpty_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨a, d, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · rename_i d₁ hd₁
      obtain ⟨al, d', hl, rfl, hc⟩ := goPend_last_true H rest d₁ t h
      have hne : rest ≠ [] := by rintro rfl; simp at hl
      refine ⟨al, d', ?_, rfl, Or.inr ?_⟩
      · rw [List.getLast?_cons, hl]; rfl
      · obtain ⟨b, rest', rfl⟩ := List.exists_cons_of_ne_nil hne
        rcases hc with ⟨rfl, -⟩ | ⟨a', ha', d'', hd''⟩
        · exact ⟨a, by simp, d, hd₁⟩
        · refine ⟨a', ?_, d'', hd''⟩
          rw [List.dropLast_cons_of_ne_nil (by simp)]
          exact List.mem_cons_of_mem _ ha'

omit [Sphincs.Params] in
/-- **The last pending input of a seeding** with steps: the last step's input at the answer to
the penultimate input, which is the first input (one step) or a step's. -/
theorem pend_last_true {H : Bytes → Option Digest} {S : Seed} (hne : S.steps ≠ []) {t : Bytes}
    (h : pend H S = some (t, true)) :
    ∃ a d' t', S.steps.getLast? = some a ∧ t = Seed.input a d' ∧ H t' = some d' ∧
      ((t' = S.first ∧ S.steps.length = 1) ∨
        ∃ a' ∈ S.steps.dropLast, ∃ d'', t' = Seed.input a' d'') := by
  unfold pend at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq, List.isEmpty_iff] at h
    exact absurd h.2 hne
  · rename_i d hd
    obtain ⟨a, d', hl, rfl, hc⟩ := goPend_last_true H S.steps d t h
    rcases hc with ⟨rfl, hlen⟩ | ⟨a', ha', d'', hd''⟩
    · exact ⟨a, d', S.first, hl, rfl, hd, Or.inl ⟨rfl, hlen⟩⟩
    · exact ⟨a, d', Seed.input a' d'', hl, rfl, hd'', Or.inr ⟨a', ha', d'', rfl⟩⟩

/-- **A seeding's last input is not hidden**, when its penultimate input is not and the
non-hidden entries answer no hidden prefix. -/
theorem not_hid_of_pend {keys : Keys nx ns} {X : Type} {σ : Seeds X} (hσ : SeedsNotHid keys σ)
    {ℓ : Log} (hN : NotHidOut keys ℓ) {x : X} {t : Bytes}
    (h : pend (look ℓ) (σ.seed x) = some (t, true)) : ¬ Hid keys t := by
  obtain ⟨s, hs, hlast⟩ := σ.last x
  have hne : (σ.seed x).steps ≠ [] := by
    intro he; rw [he] at hlast; simp at hlast
  obtain ⟨a, d', t', ha, rfl, hl, hc⟩ := pend_last_true hne h
  rw [hlast, Option.some.injEq] at ha
  subst ha
  have hnt : ¬ Hid keys t' := by
    rcases hc with ⟨rfl, hlen⟩ | ⟨a', ha', d'', rfl⟩
    · exact (hσ x).1 hlen
    · exact (hσ x).2 a' ha' d''
  have hd := hN _ (mem_of_look_eq_some hl) hnt
  intro hh
  rw [Seed.input, List.nil_append] at hh
  exact hd (inPfx_of_hid_digest_append (by rw [hs]; decide) (by rw [hs]; decide) hh)

/-- leanVM's seedings: the penultimate input is `ivPrefix ‖ d`. -/
theorem seedsNotHid_leanVmSeeds (keys : Keys nx ns) :
    SeedsNotHid keys EndToEnd.Sound.leanVmSeeds := by
  intro x
  refine ⟨fun h ↦ ?_, fun a ha d ↦ ?_⟩
  · simp [EndToEnd.Sound.leanVmSeeds, EndToEnd.Sound.leanVmSeed_steps] at h
  · simp only [EndToEnd.Sound.leanVmSeeds, EndToEnd.Sound.leanVmSeed_steps,
      List.dropLast_cons_cons, List.dropLast_singleton, List.mem_singleton] at ha
    subst ha
    rw [Seed.input, List.append_nil]
    exact not_hid_ivPrefix_append keys d

/-- The batching's seedings: the penultimate input is the label. -/
theorem seedsNotHid_batchSeedsAll (keys : Keys nx ns) : SeedsNotHid keys batchSeedsAll := by
  intro x
  refine ⟨fun _ ↦ ?_, fun a ha d ↦ ?_⟩
  · exact not_hid_batchLabel keys
  · simp [batchSeedsAll, batchSeeds] at ha

end Seeds

/-! ## The decoder -/

section Decoder

variable {nx ns : ℕ} [Sphincs.Params] {keys : Keys nx ns} {X : Type} {σ : Seeds X}
  {P : Prog Bool}

omit [Sphincs.Params] in
/-- The statement whose seeding an input completes has that input as its last pending one. -/
theorem pend_of_rootAt {ℓ : Log} {t : Bytes} {x : X} (h : rootAt σ ℓ t = some x) :
    pend (look ℓ) (σ.seed x) = some (t, true) := by
  unfold rootAt at h
  split at h
  · rename_i hex
    cases h
    exact hex.choose_spec
  · cases h

/-- **A hidden entry is read as nothing**: no record, and no decoding of its answer, when the
decoded digests are no hidden prefixes. -/
theorem step_of_hid (hσ : SeedsNotHid keys σ) {ℓ : Log} (hN : NotHidOut keys ℓ)
    (hδ : ∀ c, (decode σ P ℓ).info c ≠ none → ¬ InPfx keys c) {t : Bytes} (ht : Hid keys t) :
    (Rom.step σ P ℓ (decode σ P ℓ) t).1 = .none ∧
      ∀ u, (Rom.step σ P ℓ (decode σ P ℓ) t).2 u = none := by
  unfold Rom.step
  split
  · rename_i x hx
    exact absurd ht (not_hid_of_pend hσ hN (pend_of_rootAt hx))
  · split
    · rename_i cv x tag hp
      obtain ⟨-, rfl⟩ := parse_eq_some hp
      rcases hi : (decode σ P ℓ).info cv with _ | i
      · exact ⟨rfl, fun _ ↦ rfl⟩
      · exact absurd ht (not_hid_chain_of_not_inPfx (hδ cv (by rw [hi]; simp)) x tag)
    · exact ⟨rfl, fun _ ↦ rfl⟩

/-- **The invariant**, from non-hidden entries: every decoded digest is no hidden prefix. -/
theorem decode_info_not_inPfx_of (hσ : SeedsNotHid keys σ) :
    ∀ {ℓ : Log}, NotHidOut keys ℓ → ∀ c, (decode σ P ℓ).info c ≠ none → ¬ InPfx keys c := by
  intro ℓ
  induction ℓ using List.reverseRecOn with
  | nil => intro _ c hc; exact absurd rfl hc
  | append_singleton ℓ e ih =>
    obtain ⟨t, u⟩ := e
    intro hN c hc
    have hN' : NotHidOut keys ℓ := hN.of_append
    have ih' := ih hN'
    rw [info_decode_append] at hc
    generalize ho : (Rom.step σ P ℓ (decode σ P ℓ) t).2 u = o at hc
    rcases o with _ | i
    · exact ih' c hc
    · have hnt : ¬ Hid keys t := fun ht ↦ by
        rw [(step_of_hid hσ hN' ih' ht).2 u] at ho
        cases ho
      have hu : ¬ InPfx keys u :=
        hN _ (List.mem_append_right _ (List.mem_singleton_self _)) hnt
      simp only [setInfo, Function.update_apply] at hc
      split at hc
      · rename_i hcu
        rw [hcu]
        exact hu
      · exact ih' c hc

/-- **The invariant** (P3a): without the format event, and with the first `k0` entries hidden,
every decoded digest is no hidden prefix. -/
theorem decode_info_not_inPfx (σ : Seeds X) (P : Prog Bool) (hσ : SeedsNotHid keys σ)
    {ℓ : Log} {k0 : ℕ} (hkg : ∀ (i : ℕ) (hi : i < ℓ.length), i < k0 → Hid keys ℓ[i].1)
    (hF : ¬ FormatI keys k0 ℓ) : ∀ c, (decode σ P ℓ).info c ≠ none → ¬ InPfx keys c :=
  decode_info_not_inPfx_of hσ (notHidOut_of_not_formatI hkg hF)

/-- A hidden entry adds a `none` record. -/
theorem kinds_decode_append_hid (hσ : SeedsNotHid keys σ) {ℓ : Log} (hN : NotHidOut keys ℓ)
    {t : Bytes} (ht : Hid keys t) (u : Digest) :
    (decode σ P (ℓ ++ [(t, u)])).kinds = (decode σ P ℓ).kinds ++ [(.none, u)] := by
  rw [kinds_decode_append, (step_of_hid hσ hN (decode_info_not_inPfx_of hσ hN) ht).1]

/-- **On hidden entries, every record is `none`**: after a log whose records are `none`, the
hidden entries add `none` records. -/
theorem kinds_none_append_allHid (hσ : SeedsNotHid keys σ) (L : Log)
    (hL : ∀ κ ∈ (decode σ P L).kinds, κ.1 = .none) :
    ∀ {ℓ : Log}, NotHidOut keys (L ++ ℓ) → (∀ e ∈ ℓ, Hid keys e.1) →
      ∀ κ ∈ (decode σ P (L ++ ℓ)).kinds, κ.1 = .none := by
  intro ℓ
  induction ℓ using List.reverseRecOn with
  | nil => intro _ _; simpa using hL
  | append_singleton ℓ e ih =>
    obtain ⟨t, u⟩ := e
    intro hN hall κ hκ
    rw [← List.append_assoc] at hN hκ
    rw [kinds_decode_append_hid hσ hN.of_append (hall (t, u) (by simp)) u] at hκ
    rcases List.mem_append.mp hκ with hκ | hκ
    · exact ih hN.of_append (fun e he ↦ hall e (List.mem_append_left _ he)) κ hκ
    · rw [List.mem_singleton] at hκ
      rw [hκ]

/-- On a log of hidden entries, every record is `none`. -/
theorem kinds_none_of_allHid (hσ : SeedsNotHid keys σ) {ℓ : Log}
    (hall : ∀ e ∈ ℓ, Hid keys e.1) : ∀ κ ∈ (decode σ P ℓ).kinds, κ.1 = .none := by
  have h := kinds_none_append_allHid (P := P) hσ [] (by simp [Dec.init])
    (by simpa using notHidOut_of_allHid hall) hall
  simpa using h

end Decoder

/-! ## T1's potential -/

section Pot

variable {nx ns : ℕ} [Sphincs.Params] {keys : Keys nx ns} {X : Type} {σ : Seeds X}
  {P : Prog Bool}

omit [Sphincs.Params] in
/-- Records that are all `none` sum to zero. -/
theorem termSum_eq_zero_of_kinds (D : List Ev → Prop) {ℓ : Log}
    (h : ∀ κ ∈ (decode σ P ℓ).kinds, κ.1 = .none) : termSum D σ P ℓ = 0 := by
  unfold termSum
  refine List.sum_eq_zero fun x hx ↦ ?_
  obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hx
  obtain ⟨s, d⟩ := κ
  obtain rfl : s = .none := h _ hκ
  rfl

omit [Sphincs.Params] in
/-- With no record, the potential is the failure indicator. -/
theorem pot_le_of_kinds (D : List Ev → Prop) {ℓ : Log}
    (h : ∀ κ ∈ (decode σ P ℓ).kinds, κ.1 = .none) : pot D σ P ℓ ≤ ind (Fail σ ℓ) := by
  unfold pot
  split
  · rename_i hf; rw [ind_of hf]
  · rw [termSum_eq_zero_of_kinds D h, min_eq_right (zero_le_one' ℝ≥0∞)]; exact bot_le

/-- **On the key-generation log, no term**: a log of hidden entries has `termSum = 0`. -/
theorem termSum_eq_zero_of_allHid (D : List Ev → Prop) (hσ : SeedsNotHid keys σ) {ℓ : Log}
    (hall : ∀ e ∈ ℓ, Hid keys e.1) : termSum D σ P ℓ = 0 :=
  termSum_eq_zero_of_kinds D (kinds_none_of_allHid hσ hall)

/-- **On the key-generation log, only failure**: T1's potential of a log of hidden entries is at
most its failure indicator. -/
theorem pot_le_of_allHid (D : List Ev → Prop) (hσ : SeedsNotHid keys σ) {ℓ : Log}
    (hall : ∀ e ∈ ℓ, Hid keys e.1) : pot D σ P ℓ ≤ ind (Fail σ ℓ) :=
  pot_le_of_kinds D (kinds_none_of_allHid hσ hall)

/-- **A hidden fresh query and T1's terms**: averaged over the answers that keep the log free of
predictions, the terms after a fresh hidden entry sum to at most the terms before. -/
theorem termSum_step_hid (D : List Ev → Prop) (hσ : SeedsNotHid keys σ) {ℓ : Log}
    (hN : NotHidOut keys ℓ) {t : Bytes} (ht : Hid keys t) (hfresh : look ℓ t = none) :
    (∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) * termSum D σ P (ℓ ++ [(t, u)])) /
        Fintype.card Digest ≤ termSum D σ P ℓ := by
  have hsplit : ∀ u, ind (Fresh (ℓ ++ [(t, u)]) u) * termSum D σ P (ℓ ++ [(t, u)]) =
      ((decode σ P ℓ).kinds.map fun κ ↦
        ind (Fresh (ℓ ++ [(t, u)]) u) * term D (ℓ ++ [(t, u)]) κ).sum := by
    intro u
    simp only [termSum, kinds_decode_append_hid hσ hN ht u, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton, List.sum_map_mul_left]
    simp [term]
  simp only [hsplit]
  rw [sum_list_sum_comm, list_sum_div]
  exact List.sum_le_sum fun κ _ ↦ term_step_old D hfresh κ

/-- **The hidden step of T1's potential**: a fresh hidden query raises it, in expectation, by at
most the failure term `(4 + k)(|ℓ| + 1)/|Digest|`. -/
theorem pot_step_hid (D : List Ev → Prop) (hσ : SeedsNotHid keys σ) {ℓ : Log}
    (hN : NotHidOut keys ℓ) {t : Bytes} (ht : Hid keys t) (hfresh : t ∉ ℓ.map Prod.fst) :
    (∑ u, pot D σ P (ℓ ++ [(t, u)])) / Fintype.card Digest ≤
      pot D σ P ℓ + ((4 + σ.steps.length) * (ℓ.length + 1) : ℕ) / Fintype.card Digest := by
  have ht' : look ℓ t = none := (logLookup_eq_none_iff ℓ t).mpr hfresh
  by_cases hf : Fail σ ℓ
  · have h1 : pot D σ P ℓ = 1 := by simp only [pot, hf, ↓reduceIte]
    rw [h1]
    exact (avg_le_of_le fun u ↦ pot_le_one D σ P _).trans le_self_add
  have hpot : pot D σ P ℓ = min 1 (termSum D σ P ℓ) := by simp only [pot, hf, ↓reduceIte]
  have hpt : ∀ u, pot D σ P (ℓ ++ [(t, u)]) ≤
      ind (BadEntry σ ℓ t u) +
        ind (Fresh (ℓ ++ [(t, u)]) u) * min 1 (termSum D σ P (ℓ ++ [(t, u)])) := by
    intro u
    by_cases hb : BadEntry σ ℓ t u
    · rw [ind_of hb]; exact (pot_le_one D σ P _).trans le_self_add
    · have hnf : ¬ Fail σ (ℓ ++ [(t, u)]) := by rw [fail_append]; tauto
      rw [ind_of_not hb, zero_add, ind_of (fresh_of_not_bad hb), one_mul]
      simp only [pot, hnf, ↓reduceIte, le_refl]
  have hfresh' : (∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) *
      min 1 (termSum D σ P (ℓ ++ [(t, u)]))) / Fintype.card Digest ≤
        min 1 (termSum D σ P ℓ) := by
    refine le_min ?_ ?_
    · exact avg_le_of_le fun u ↦
        (mul_le_mul_left (ind_le_one _) _).trans ((one_mul _).le.trans (min_le_left _ _))
    · refine le_trans (ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ ?_) _)
        (termSum_step_hid D hσ hN ht ht')
      exact mul_le_mul_right (min_le_right _ _) _
  calc (∑ u, pot D σ P (ℓ ++ [(t, u)])) / Fintype.card Digest
      ≤ (∑ u, (ind (BadEntry σ ℓ t u) +
          ind (Fresh (ℓ ++ [(t, u)]) u) * min 1 (termSum D σ P (ℓ ++ [(t, u)])))) /
          Fintype.card Digest :=
        ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hpt u) _
    _ = (∑ u, ind (BadEntry σ ℓ t u)) / Fintype.card Digest +
          (∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) * min 1 (termSum D σ P (ℓ ++ [(t, u)]))) /
            Fintype.card Digest := by
        rw [Finset.sum_add_distrib, ENNReal.add_div]
    _ ≤ ((4 + σ.steps.length) * (ℓ.length + 1) : ℕ) / Fintype.card Digest +
          min 1 (termSum D σ P ℓ) :=
        add_le_add (ENNReal.div_le_div_right (sum_badEntry_le σ ℓ t) _) hfresh'
    _ = _ := by rw [hpot, add_comm]

omit [Sphincs.Params] in
/-- The failure term at a log of length `n`. -/
theorem failTerm_eq_failBound (σ : Seeds X) (n : ℕ) :
    (((4 + σ.steps.length) * (n + 1) : ℕ) : ℝ≥0∞) / Fintype.card Digest =
      failBound σ (n + 1) := by
  rw [failBound, card_digest, Nat.cast_pow, Nat.cast_ofNat]

/-- **The hidden step of T1's potential, stopped at the format event** (P3a). -/
theorem potStop_step_hid (D : List Ev → Prop) (σ : Seeds X) (P : Prog Bool)
    (hσ : SeedsNotHid keys σ) {ℓ : Log} {k0 : ℕ}
    (hkg : ∀ (i : ℕ) (hi : i < ℓ.length), i < k0 → Hid keys ℓ[i].1) {t : Bytes}
    (ht : Hid keys t) (hfresh : t ∉ ℓ.map Prod.fst) :
    (∑ u, pot D σ P (ℓ ++ [(t, u)]) * ind (¬ FormatI keys k0 (ℓ ++ [(t, u)]))) /
        Fintype.card Digest ≤
      pot D σ P ℓ * ind (¬ FormatI keys k0 ℓ) + failBound σ (ℓ.length + 1) := by
  refine sum_stop_le_of_step keys k0 fun hF ↦ ?_
  rw [← failTerm_eq_failBound]
  exact pot_step_hid D hσ (notHidOut_of_not_formatI hkg hF) ht hfresh

end Pot

/-! ## W6's potential -/

section BatchPot

variable {nx ns : ℕ} [Sphincs.Params] {keys : Keys nx ns}

/-- The log read from a start that is no hidden prefix keeps the property. -/
theorem notHidOut_startLog {s0 : Digest} (hs0 : ¬ InPfx keys s0) {ℓ : Log}
    (h : NotHidOut keys ℓ) : NotHidOut keys (startLog s0 ℓ) := by
  intro e he hn
  simp only [E2E.startLog, List.mem_cons] at he
  rcases he with rfl | he
  · exact hs0
  · exact h e (List.mem_filter.mp he).1 hn

omit [Sphincs.Params] in
/-- The label's entry alone starts nothing. -/
theorem kinds_decode_label (bytecode : List K) (s0 : Digest) :
    ∀ κ ∈ (decode batchSeedsAll (bytecodeAny bytecode) [(batchLabel, s0)]).kinds,
      κ.1 = .none := by
  have hroot : rootAt batchSeedsAll [] batchLabel = none := by
    unfold rootAt
    split
    · rename_i hex
      obtain ⟨x, hx⟩ := hex
      simp [pend, look, logLookup, batchSeedsAll, batchSeeds] at hx
    · rfl
  have hstep : (Rom.step batchSeedsAll (bytecodeAny bytecode) [] Dec.init batchLabel).1 =
      Shape.none := by
    simp only [Rom.step, hroot, parse_label]
  rw [show [(batchLabel, s0)] = ([] : Log) ++ [(batchLabel, s0)] from rfl, kinds_decode_append,
    decode_nil, hstep]
  simp [Dec.init]

/-- **The hidden step of the batching's potential, stopped at the format event** (P3a): a fresh
hidden query raises it, in expectation, by at most `4 (|ℓ| + 2)/|Digest|`, for a start `s0`
that is no hidden prefix. -/
theorem batchPotStop_step_hid (s0 : Digest) (hs0 : ¬ InPfx keys s0) (bytecode : List K)
    {ℓ : Log} {k0 : ℕ} (hkg : ∀ (i : ℕ) (hi : i < ℓ.length), i < k0 → Hid keys ℓ[i].1)
    {t : Bytes} (ht : Hid keys t) (hfresh : t ∉ ℓ.map Prod.fst) :
    (∑ u, batchPot s0 bytecode (ℓ ++ [(t, u)]) * ind (¬ FormatI keys k0 (ℓ ++ [(t, u)]))) /
        Fintype.card Digest ≤
      batchPot s0 bytecode ℓ * ind (¬ FormatI keys k0 ℓ) +
        ((4 * (ℓ.length + 2) : ℕ) : ℝ≥0∞) / Fintype.card Digest := by
  refine sum_stop_le_of_step keys k0 fun hF ↦ ?_
  have hl : t ≠ batchLabel := fun h ↦ not_hid_batchLabel keys (h ▸ ht)
  unfold batchPot
  split_ifs with hb
  · simp only [startLog_append_of_ne s0 ℓ hl]
    refine (pot_step_hid _ (seedsNotHid_batchSeedsAll keys)
      (notHidOut_startLog hs0 (notHidOut_of_not_formatI hkg hF)) ht
      (not_mem_startLog hfresh hl)).trans
      (add_le_add le_rfl (ENNReal.div_le_div_right ?_ _))
    have hlen := length_startLog_le s0 ℓ
    have hsteps : (batchSeedsAll.steps).length = 0 := rfl
    rw [hsteps]
    exact_mod_cast Nat.mul_le_mul_left 4 (by omega)
  · simp

/-- **On the key-generation log, only failure**: the batching's potential of a log of hidden
entries, from a start that is no hidden prefix, is at most the failure indicator of the log read
from the start. -/
theorem batchPot_le_of_allHid {s0 : Digest} (hs0 : ¬ InPfx keys s0) (bytecode : List K)
    {ℓ : Log} (hall : ∀ e ∈ ℓ, Hid keys e.1) :
    batchPot s0 bytecode ℓ ≤ ind (Fail batchSeedsAll (startLog s0 ℓ)) := by
  unfold batchPot
  split_ifs with hb
  · refine pot_le_of_kinds _ ?_
    have hfil : ∀ e ∈ ℓ.filter (fun e ↦ decide (e.1 ≠ batchLabel)), Hid keys e.1 :=
      fun e he ↦ hall e (List.mem_filter.mp he).1
    exact kinds_none_append_allHid (seedsNotHid_batchSeedsAll keys) [(batchLabel, s0)]
      (kinds_decode_label bytecode s0) (notHidOut_startLog hs0 (notHidOut_of_allHid hall)) hfil
  · exact bot_le

end BatchPot

end
end LeanVM.E2E
