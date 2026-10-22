/-
  LeanVM.E2E.Vis.Bound

  W-vis, P6a: the chain's bad events with the visible accounting. On the game with V_I's trace,
  T1's, W6's, E5's and T3's bad events and the format event have probability at most `visError`:
  the leanVM rates per visible query, the failure rates per query.
-/

module

public import LeanVM.E2E.Vis.Count
public import LeanVM.E2E.Vis.Pred
public import LeanVM.E2E.Vis.Decoder
public import LeanVM.E2E.Vis.DaDecoder
public import LeanVM.E2E.Vis.Knowledge
public import LeanVM.E2E.Vis.WalkSphincs

/-!
# The bound on the bad events, visible accounting (W-vis, P6a)

The plan is `docs/roadmap/w-vis.md` §3 P6. The bad events (`AggBadV`) are T4's at the trace
(`AggBadT`: T1, W6, E5), T3 restricted to non-hidden entries (`PredS`) and the statement's format
event (`FormatT`). With `Q_v = qH + budget` visible and `Q` hash queries in all
(`prEvent_gameRec_aggBadV_le`):

  `Pr[AggBadV] ≤ visError Q_v Q (n_x + n_s)`.

**The split** (`prEvent_gameRec_le_of_phase`, P1). The game is key generation, then the rest.
Key generation logs only hidden inputs (`keygenPhase_hid`, with the scheme walks of P2b/P2c), at
most `n_x · c_xk + n_s · c_sk` of them (`length_le_of_mem_support_runGame`).

**The rest** (`prEvent_runGame_le_budgeted`, `prEvent_runGame_le_lin`). The two-budget engine
(`lintegral_run_le_of_budgetedPQ`, P1) on the game's oracle, from the key-generation log `ℓ₀`,
with `p` the visible queries (at most `Q_v`, `isQueryBoundP_restRec_vis`) and `q` the hash queries
(at most the rest's count, `isQueryBoundP_restRec`). The step bounds are needed only on logs that
extend a hidden log of length `k0 = |ℓ₀|` (`KgPre`) and are shorter than `Q`. A visible fresh query
is charged `δp + δq`, a hidden one `δq`. One potential per leg:

* T1 (`prEvent_runGame_t1_le`): `pot · 1[¬ FormatI]`; `δp = εLean` (`step_ineq`), `δq` T1's failure
  rate (`potStop_step_hid`). At `ℓ₀` it is at most the failure indicator (`pot_le_of_allHid`).
* W6 (`prEvent_runGame_w6_le`): `batchPot · 1[¬ FormatI]`; `δp = 2/|E|` (`batchPot_step`), `δq` the
  batching's failure rate (`batchPotStop_step_hid`, the baked start no hidden prefix).
* E5 (`prEvent_runGame_e5_le`): `daPot · 1[¬ FormatI]`, at E5's full rate on every hash query
  (`daPotStop_step`, decision fix B).
* T3 (`prEvent_runGame_t3_le`): `predPotS` with the visible budget (P4); `Q_v (Q_v + 1)/2^193`.
* The format event (`prEvent_runGame_fmt_le`): `1[FormatI]`, raised by a fresh answer that is a
  hidden prefix, `(n · 2^64 + 1)/2^256` per hash query (`sum_ind_inPfx_le`). `FormatT` is
  `FormatI` on a log with a hidden prefix of length `k0` (`FormatT.formatI`).

**Key generation** (`lintegral_keygenPhase_le`). The legs' potentials at `ℓ₀` are at most
keys-free potentials: T1's and W6's failure indicators (`ind (Fail …)`) and E5's `daPot`, whose
expectation after key generation the one-budget engine bounds by their rates per key-generation
query (the failure rates for T1 and W6, E5's full rate). T3's and the format event's are
constants there (`predPotS_of_allHid`, `not_formatI_self`).

**The constants.** `visError` is the plan's; the proof gives `visErrorTight`, with the failure
rates at `Q` rather than `Q + 1` (§0's `sec0Error` forms), and `visErrorTight ≤ visError`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.EndToEnd.Blind LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Rom LeanVM.Node
open LeanVM.Guest.Batch
open OracleSpec OracleComp MeasureTheory
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## Averages, failure and the format event -/

section Steps

variable {nx ns : ℕ} [Sphincs.Params]

omit [Sphincs.Params] in
/-- The average of a function plus a constant. -/
theorem avgDigest_add_const (g : Digest → ℝ≥0∞) (c : ℝ≥0∞) :
    (∑ u, (g u + c)) / Fintype.card Digest = (∑ u, g u) / Fintype.card Digest + c := by
  simp only [add_comm _ c]
  rw [avg_const_add, add_comm]

omit [Sphincs.Params] in
/-- The failure term grows with the log's length. -/
theorem failBound_le_of_le {X : Type} (σ : Seeds X) {m n : ℕ} (h : m ≤ n) :
    failBound σ m ≤ failBound σ n := by
  unfold failBound
  exact ENNReal.div_le_div_right (by exact_mod_cast Nat.mul_le_mul_left _ h) _

omit [Sphincs.Params] in
/-- **A fresh answer makes the log fail** with probability at most the failure term. -/
theorem avg_ind_fail_le {X : Type} (σ : Seeds X) (ℓ : Log) (t : Bytes) :
    (∑ u, ind (Fail σ (ℓ ++ [(t, u)]))) / Fintype.card Digest ≤
      ind (Fail σ ℓ) + failBound σ (ℓ.length + 1) := by
  calc (∑ u, ind (Fail σ (ℓ ++ [(t, u)]))) / Fintype.card Digest
      ≤ (∑ u, (ind (Fail σ ℓ) + ind (BadEntry σ ℓ t u))) / Fintype.card Digest :=
        ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦
          (ind_mono (fail_append σ ℓ t u).mp).trans (ind_or_le _ _)) _
    _ = ind (Fail σ ℓ) + (∑ u, ind (BadEntry σ ℓ t u)) / Fintype.card Digest := avg_const_add _ _
    _ ≤ ind (Fail σ ℓ) +
          (((4 + σ.steps.length) * (ℓ.length + 1) : ℕ) : ℝ≥0∞) / Fintype.card Digest :=
        add_le_add le_rfl (ENNReal.div_le_div_right (sum_badEntry_le σ ℓ t) _)
    _ = _ := by rw [failTerm_eq_failBound]

omit [Sphincs.Params] in
/-- Bytes `16..24` of a digest are its words `4` and `5`. -/
theorem digestBytes_drop16_take8 (d : Digest) :
    ((digestBytes d).drop 16).take 8 = wordBytes d[4] ++ wordBytes d[5] := by
  obtain ⟨⟨l⟩, hl⟩ := d
  simp only [List.size_toArray] at hl
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ |
    ⟨a8, l⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at hl
  rfl

omit [Sphincs.Params] in
/-- **The digests whose bytes are `p ‖ a`**, `p` of 16 bytes and `a` an address: at most `2^64`,
one per value of the address's free half. -/
theorem sum_ind_addrPfx_le (p : Bytes) (hp : p.length = 16) :
    ∑ u : Digest, ind (∃ a, AddrOK a ∧ digestBytes u = p ++ a) ≤ 2 ^ 64 := by
  classical
  have hsum : ∑ u : Digest, ind (∃ a, AddrOK a ∧ digestBytes u = p ++ a) =
      ((Finset.univ.filter fun u : Digest ↦ ∃ a, AddrOK a ∧ digestBytes u = p ++ a).card :
        ℝ≥0∞) := by
    simp only [ind]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- such a digest is fixed by its words `4` and `5`
  have hform : ∀ (w : Digest) (a : Bytes), AddrOK a → digestBytes w = p ++ a →
      digestBytes w = p ++ ((wordBytes w[4] ++ wordBytes w[5]) ++ List.replicate 8 0) := by
    intro w a ha hw
    have h1 : a.take 8 = wordBytes w[4] ++ wordBytes w[5] := by
      rw [← digestBytes_drop16_take8, hw, List.drop_left' hp]
    rw [hw, ← h1, ← ha.2, List.take_append_drop]
  have hinj : Set.InjOn (fun u : Digest ↦ (u[4], u[5]))
      ↑(Finset.univ.filter fun u : Digest ↦ ∃ a, AddrOK a ∧ digestBytes u = p ++ a) := by
    intro u hu v hv huv
    obtain ⟨a, ha, hua⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
    obtain ⟨b, hb, hvb⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
    simp only [Prod.mk.injEq] at huv
    refine digestBytes_injective ?_
    rw [hform u a ha hua, hform v b hb hvb, huv.1, huv.2]
  have hcard : (Finset.univ.filter fun u : Digest ↦ ∃ a, AddrOK a ∧ digestBytes u = p ++ a).card ≤
      2 ^ 64 := by
    rw [← Finset.card_image_of_injOn hinj]
    refine (Finset.card_le_univ _).trans (le_of_eq ?_)
    rw [Fintype.card_prod, card_uint32]
    norm_num
  rw [hsum]
  exact_mod_cast hcard

/-- **The hidden prefixes**: at most `n · 2^64 + 1` digests, `n = n_x + n_s` the keys. -/
theorem sum_ind_inPfx_le (keys : Keys nx ns) :
    ∑ u : Digest, ind (InPfx keys u) ≤ (((nx + ns) * 2 ^ 64 + 1 : ℕ) : ℝ≥0∞) := by
  have hpt : ∀ u : Digest, ind (InPfx keys u) ≤
      ((keyParams keys).map fun p ↦ ind (∃ a, AddrOK a ∧ digestBytes u = p ++ a)).sum +
        ind (digestBytes u = paramPrefix) := fun u ↦
    (ind_or_le _ _).trans (add_le_add (ind_exists_le _ _) le_rfl)
  have hlen : (keyParams keys).length = nx + ns := by simp [keyParams]
  calc ∑ u : Digest, ind (InPfx keys u)
      ≤ ∑ u : Digest, (((keyParams keys).map fun p ↦
          ind (∃ a, AddrOK a ∧ digestBytes u = p ++ a)).sum + ind (digestBytes u = paramPrefix)) :=
        Finset.sum_le_sum fun u _ ↦ hpt u
    _ = ((keyParams keys).map fun p ↦
          ∑ u : Digest, ind (∃ a, AddrOK a ∧ digestBytes u = p ++ a)).sum +
          ∑ u : Digest, ind (digestBytes u = paramPrefix) := by
        rw [Finset.sum_add_distrib, sum_list_sum_comm]
    _ ≤ (keyParams keys).length * 2 ^ 64 + 1 :=
        add_le_add (list_sum_le _ _ _ fun p hp ↦
          sum_ind_addrPfx_le p (length_of_mem_keyParams hp))
          (sum_ind_le_one fun u v hu hv ↦ digestBytes_injective (hu.trans hv.symm))
    _ = _ := by rw [hlen]; push_cast; ring

/-- A format event on a log one entry longer is one on the log, or the new answer is a hidden
prefix. -/
theorem formatI_append_cases {keys : Keys nx ns} {k0 : ℕ} {ℓ : Log} {x : Bytes} {u : Digest}
    (h : FormatI keys k0 (ℓ ++ [(x, u)])) : FormatI keys k0 ℓ ∨ InPfx keys u := by
  obtain ⟨i, hi, hk, hd, hp⟩ := h
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
  · refine Or.inl ⟨i, hi', hk, ?_, ?_⟩
    · rwa [List.getElem_append_left hi'] at hd
    · rwa [List.getElem_append_left hi'] at hp
  · rw [List.getElem_append_right (le_refl _)] at hp
    simp only [Nat.sub_self, List.getElem_singleton] at hp
    exact Or.inr hp

/-- **A fresh answer starts the format event** with probability at most
`(n · 2^64 + 1)/2^256`. -/
theorem avg_ind_formatI_le (keys : Keys nx ns) (k0 : ℕ) (ℓ : Log) (x : Bytes) :
    (∑ u, ind (FormatI keys k0 (ℓ ++ [(x, u)]))) / Fintype.card Digest ≤
      ind (FormatI keys k0 ℓ) + (((nx + ns) * 2 ^ 64 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  calc (∑ u, ind (FormatI keys k0 (ℓ ++ [(x, u)]))) / Fintype.card Digest
      ≤ (∑ u, (ind (FormatI keys k0 ℓ) + ind (InPfx keys u))) / Fintype.card Digest :=
        ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦
          (ind_mono formatI_append_cases).trans (ind_or_le _ _)) _
    _ = ind (FormatI keys k0 ℓ) + (∑ u, ind (InPfx keys u)) / Fintype.card Digest :=
        avg_const_add _ _
    _ ≤ _ := by
        rw [card_digest, Nat.cast_pow, Nat.cast_ofNat]
        exact add_le_add le_rfl (ENNReal.div_le_div_right (sum_ind_inPfx_le keys) _)

end Steps

/-! ## The engine on the game's oracle -/

section Engine

variable {nx ns : ℕ} [Sphincs.Params]

omit [Sphincs.Params] in
/-- **The game's log grows by at most one entry per hash query.** -/
theorem length_le_of_mem_support_runGame {α : Type} (oa : OracleComp GameSpec α) (b : ℕ)
    (hb : IsQueryBoundP oa IsHash b) (ℓ₀ : Log) {z : α × Log}
    (hz : z ∈ support ((simulateQ gameImpl oa).run ℓ₀)) : z.2.length ≤ ℓ₀.length + b := by
  induction oa using OracleComp.inductionOn generalizing b ℓ₀ with
  | pure x =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Nat.le_add_right _ _
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    obtain ⟨hpos, hrest⟩ := hb
    rw [simulateQ_query_bind, StateT.run_bind] at hz
    simp only [OracleQuery.input_query, monadLift_self] at hz
    change z ∈ support ((gameImpl t).run ℓ₀ >>= fun p ↦ (simulateQ gameImpl (mx p.1)).run p.2)
      at hz
    rw [gameImpl_isLazySampler t ℓ₀] at hz
    rcases hs : gameLookup ℓ₀ t with _ | u
    · simp only [hs, bind_assoc, pure_bind] at hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨u, -, hz⟩ := hz
      have h := ih u _ (hrest u) _ hz
      rcases t with k | x
      · split_ifs at h with hh
        · exact absurd hh id
        · simpa only [gameRecord] using h
      · split_ifs at h with hh
        · have := hpos.resolve_left (not_not.mpr hh)
          simp only [gameRecord, List.length_append, List.length_singleton] at h
          omega
        · exact absurd trivial hh
    · simp only [hs, pure_bind] at hz
      have h := ih u _ (hrest u) _ hz
      split_ifs at h <;> omega

/-- **The engine on the rest of the game, two budgets.** On the game's oracle from `ℓ₀`, with at
most `a` visible and `b` hash queries: a visible fresh query lowers both budgets, a hidden one the
second; the steps are needed only on logs with the invariant `I` (kept by every fresh entry)
shorter than `N`, `|ℓ₀| + b ≤ N`. -/
theorem prEvent_runGame_le_budgeted (keys : Keys nx ns) (I : Log → Prop)
    (hI : ∀ (ℓ : Log) (x : Bytes) (u : Digest), I ℓ → I (ℓ ++ [(x, u)])) (N : ℕ)
    {Φ : ℕ → ℕ → Log → ℝ≥0∞}
    (hP : ∀ (m n : ℕ) (ℓ : Log) (x : Bytes), I ℓ → ℓ.length + (n + 1) ≤ N → ¬ Hid keys x →
      x ∉ ℓ.map Prod.fst →
      (∑ u, Φ m n (ℓ ++ [(x, u)])) / Fintype.card Digest ≤ Φ (m + 1) (n + 1) ℓ)
    (hQ : ∀ (m n : ℕ) (ℓ : Log) (x : Bytes), I ℓ → ℓ.length + (n + 1) ≤ N → Hid keys x →
      x ∉ ℓ.map Prod.fst →
      (∑ u, Φ m n (ℓ ++ [(x, u)])) / Fintype.card Digest ≤ Φ m (n + 1) ℓ)
    (hmono : ∀ (m n : ℕ) (ℓ : Log), Φ m n ℓ ≤ Φ (m + 1) n ℓ ∧ Φ m n ℓ ≤ Φ m (n + 1) ℓ)
    {α : Type} (oa : OracleComp GameSpec α) (a b : ℕ) (ha : IsQueryBoundP oa (VisQ keys) a)
    (hb : IsQueryBoundP oa IsHash b) (ℓ₀ : Log) (hI₀ : I ℓ₀) (hN : ℓ₀.length + b ≤ N)
    (ev : α × Log → Prop)
    (hev : ∀ z ∈ support ((simulateQ gameImpl oa).run ℓ₀), ev z → I z.2 → 1 ≤ Φ 0 0 z.2) :
    Pr{let z ← (simulateQ gameImpl oa).run ℓ₀}[ev z] ≤ Φ a b ℓ₀ := by
  classical
  let _ : MeasurableSpace (α × Log) := ⊤
  rw [prEvent_eq_evalDist_of_discrete _ ev, ← lintegral_indicator_one MeasurableSet.of_discrete]
  -- The potential, infinite off the invariant and past the size cap.
  let Ψ : ℕ → ℕ → Log → ℝ≥0∞ := fun m n ℓ ↦ if I ℓ ∧ ℓ.length + n ≤ N then Φ m n ℓ else ⊤
  have hstep : ∀ (m n : ℕ) (ℓ : Log) (x : Bytes) (m' : ℕ),
      (I ℓ → ℓ.length + (n + 1) ≤ N →
        (∑ u, Φ m n (ℓ ++ [(x, u)])) / Fintype.card Digest ≤ Φ m' (n + 1) ℓ) →
      (∑ u, Ψ m n (ℓ ++ [(x, u)])) / Fintype.card Digest ≤ Ψ m' (n + 1) ℓ := by
    intro m n ℓ x m' h
    by_cases hc : I ℓ ∧ ℓ.length + (n + 1) ≤ N
    · have he : ∀ u, Ψ m n (ℓ ++ [(x, u)]) = Φ m n (ℓ ++ [(x, u)]) := fun u ↦ by
        refine ite_eq_left ⟨hI ℓ x u hc.1, ?_⟩
        rw [List.length_append, List.length_singleton]
        omega
      simp only [he]
      refine (h hc.1 hc.2).trans (le_of_eq ?_)
      exact (ite_eq_left hc).symm
    · exact le_top.trans_eq (ite_eq_right hc).symm
  have key := lintegral_run_le_of_budgetedPQ (Φ := Ψ) gameImpl_isLazySampler (VisQ keys) IsHash
    (visQ_isHash keys) ?_ ?_ ?_ ?_ oa a b ha hb ℓ₀ (Set.indicator {z | ev z} 1) ?_
  · exact key.trans (le_of_eq (ite_eq_left ⟨hI₀, hN⟩))
  · rintro m n ℓ (k | x) hp hs
    · exact absurd hp id
    · exact hstep m n ℓ x (m + 1) fun h1 h2 ↦
        hP m n ℓ x h1 h2 hp ((logLookup_eq_none_iff ℓ x).mp hs)
  · rintro m n ℓ (k | x) hq hp hs
    · exact absurd hq id
    · exact hstep m n ℓ x m fun h1 h2 ↦
        hQ m n ℓ x h1 h2 (not_not.mp hp) ((logLookup_eq_none_iff ℓ x).mp hs)
  · rintro m n ℓ (k | x) hq _
    · exact (sum_gameRecord_coin (Ψ m n) ℓ k).le
    · exact absurd trivial hq
  · intro m n ℓ
    refine ⟨?_, ?_⟩
    · by_cases hc : I ℓ ∧ ℓ.length + n ≤ N
      · simp only [Ψ, ite_eq_left hc]
        exact (hmono m n ℓ).1
      · simp only [Ψ, ite_eq_right hc, le_refl]
    · by_cases hc : I ℓ ∧ ℓ.length + (n + 1) ≤ N
      · have hc' : I ℓ ∧ ℓ.length + n ≤ N := ⟨hc.1, by omega⟩
        simp only [Ψ, ite_eq_left hc, ite_eq_left hc']
        exact (hmono m n ℓ).2
      · simp only [Ψ, ite_eq_right hc]
        exact le_top
  · intro z hz
    by_cases hc : I z.2 ∧ z.2.length + 0 ≤ N
    · simp only [Ψ, ite_eq_left hc]
      by_cases hz' : ev z
      · rw [Set.indicator_of_mem (show z ∈ {z | ev z} from hz')]
        exact hev z hz hz' hc.1
      · rw [Set.indicator_of_notMem (show z ∉ {z | ev z} from hz')]
        exact bot_le
    · simp only [Ψ, ite_eq_right hc]
      exact le_top

/-- **The engine on the rest of the game, two rates.** A visible fresh query raises `Φ` by at most
`δp + δq`, a hidden one by `δq`, on logs with the invariant shorter than `N`. -/
theorem prEvent_runGame_le_lin (keys : Keys nx ns) (I : Log → Prop)
    (hI : ∀ (ℓ : Log) (x : Bytes) (u : Digest), I ℓ → I (ℓ ++ [(x, u)])) (N : ℕ)
    {Φ : Log → ℝ≥0∞} {δp δq : ℝ≥0∞}
    (hvis : ∀ (ℓ : Log) (x : Bytes), I ℓ → ℓ.length < N → ¬ Hid keys x → x ∉ ℓ.map Prod.fst →
      (∑ u, Φ (ℓ ++ [(x, u)])) / Fintype.card Digest ≤ Φ ℓ + (δp + δq))
    (hhid : ∀ (ℓ : Log) (x : Bytes), I ℓ → ℓ.length < N → Hid keys x → x ∉ ℓ.map Prod.fst →
      (∑ u, Φ (ℓ ++ [(x, u)])) / Fintype.card Digest ≤ Φ ℓ + δq)
    {α : Type} (oa : OracleComp GameSpec α) (a b : ℕ) (ha : IsQueryBoundP oa (VisQ keys) a)
    (hb : IsQueryBoundP oa IsHash b) (ℓ₀ : Log) (hI₀ : I ℓ₀) (hN : ℓ₀.length + b ≤ N)
    (ev : α × Log → Prop)
    (hev : ∀ z ∈ support ((simulateQ gameImpl oa).run ℓ₀), ev z → I z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ gameImpl oa).run ℓ₀}[ev z] ≤ Φ ℓ₀ + (a * δp + b * δq) := by
  refine prEvent_runGame_le_budgeted (Φ := fun m n ℓ ↦ Φ ℓ + (m * δp + n * δq)) keys I hI N
    ?_ ?_ ?_ oa a b ha hb ℓ₀ hI₀ hN ev ?_
  · intro m n ℓ x hI' hlen hx hf
    rw [avgDigest_add_const]
    calc (∑ u, Φ (ℓ ++ [(x, u)])) / Fintype.card Digest + (m * δp + n * δq)
        ≤ Φ ℓ + (δp + δq) + (m * δp + n * δq) :=
          add_le_add (hvis ℓ x hI' (by omega) hx hf) le_rfl
      _ = Φ ℓ + (((m + 1 : ℕ) : ℝ≥0∞) * δp + ((n + 1 : ℕ) : ℝ≥0∞) * δq) := by
          push_cast; ring
  · intro m n ℓ x hI' hlen hx hf
    rw [avgDigest_add_const]
    calc (∑ u, Φ (ℓ ++ [(x, u)])) / Fintype.card Digest + (m * δp + n * δq)
        ≤ Φ ℓ + δq + (m * δp + n * δq) :=
          add_le_add (hhid ℓ x hI' (by omega) hx hf) le_rfl
      _ = Φ ℓ + ((m : ℝ≥0∞) * δp + ((n + 1 : ℕ) : ℝ≥0∞) * δq) := by
          push_cast; ring
  · intro m n ℓ
    refine ⟨?_, ?_⟩ <;> gcongr <;> exact_mod_cast Nat.le_succ _
  · intro z hz h hI'
    simpa using hev z hz h hI'

/-- **The keys-free potential after key generation**: a potential on logs rising by at most `δ`
per fresh hash query, at logs shorter than `N`, has expectation at most `f [] + Q_k · δ` after
key generation, `Q_k` a bound on its hash queries. -/
theorem lintegral_keygenPhase_le [MeasurableSpace ((Keys nx ns × SignState nx ns) × Log)]
    [DiscreteMeasurableSpace ((Keys nx ns × SignState nx ns) × Log)]
    {f : Log → ℝ≥0∞} {δ : ℝ≥0∞} (N : ℕ)
    (hf : ∀ (ℓ : Log) (x : Bytes), ℓ.length < N → x ∉ ℓ.map Prod.fst →
      (∑ u, f (ℓ ++ [(x, u)])) / Fintype.card Digest ≤ f ℓ + δ)
    {Qk : ℕ} (hQk : IsQueryBoundP ((keygen : GameM nx ns (Keys nx ns)).run (SignState.init nx ns))
      IsHash Qk) (hN : Qk ≤ N) :
    ∫⁻ k, f k.2 ∂𝒟[keygenPhase (nx := nx) (ns := ns)] ≤ f [] + Qk * δ := by
  let Ψ : ℕ → Log → ℝ≥0∞ := fun n ℓ ↦ if ℓ.length + n ≤ N then f ℓ + n * δ else ⊤
  have hstep : ∀ (n : ℕ) (ℓ : Log) (x : Bytes), x ∉ ℓ.map Prod.fst →
      (∑ u, Ψ n (ℓ ++ [(x, u)])) / Fintype.card Digest ≤ Ψ (n + 1) ℓ := by
    intro n ℓ x hx
    by_cases hc : ℓ.length + (n + 1) ≤ N
    · have he : ∀ u, Ψ n (ℓ ++ [(x, u)]) = f (ℓ ++ [(x, u)]) + n * δ := fun u ↦ by
        refine ite_eq_left ?_
        rw [List.length_append, List.length_singleton]
        omega
      simp only [he]
      rw [avgDigest_add_const]
      simp only [Ψ, ite_eq_left hc]
      calc (∑ u, f (ℓ ++ [(x, u)])) / Fintype.card Digest + n * δ
          ≤ f ℓ + δ + n * δ := add_le_add (hf ℓ x (by omega) hx) le_rfl
        _ = f ℓ + ((n + 1 : ℕ) : ℝ≥0∞) * δ := by push_cast; ring
    · simp only [Ψ, ite_eq_right hc]
      exact le_top
  have h := lintegral_run_le_of_budgetedP (Φ := Ψ) gameImpl_isLazySampler IsHash ?_ ?_ ?_
    ((keygen : GameM nx ns (Keys nx ns)).run (SignState.init nx ns)) Qk hQk [] (fun k ↦ f k.2) ?_
  · refine h.trans (le_of_eq ?_)
    simp only [Ψ, List.length_nil, Nat.zero_add, ite_eq_left hN]
  · rintro n ℓ (k | x) hp hs
    · exact absurd hp id
    · exact hstep n ℓ x ((logLookup_eq_none_iff ℓ x).mp hs)
  · rintro n ℓ (k | x) hp _
    · exact (sum_gameRecord_coin (Ψ n) ℓ k).le
    · exact absurd trivial hp
  · intro n ℓ
    by_cases hc : ℓ.length + (n + 1) ≤ N
    · simp only [Ψ, ite_eq_left hc, ite_eq_left (show ℓ.length + n ≤ N by omega)]
      gcongr
      exact_mod_cast Nat.le_succ n
    · simp only [Ψ, ite_eq_right hc]
      exact le_top
  · intro z _
    by_cases hc : z.2.length + 0 ≤ N
    · simp only [Ψ, ite_eq_left hc, Nat.cast_zero, zero_mul, add_zero, le_refl]
    · simp only [Ψ, ite_eq_right hc]
      exact le_top

end Engine

/-! ## The legs on the rest of the game -/

section Legs

variable {nx ns : ℕ} [Sphincs.Params]

/-- **A hidden prefix of length `k0`**: the log has at least `k0` entries, the first `k0` hidden
(the key-generation log and its extensions). -/
def KgPre (keys : Keys nx ns) (k0 : ℕ) (ℓ : Log) : Prop :=
  k0 ≤ ℓ.length ∧ ∀ (i : ℕ) (hi : i < ℓ.length), i < k0 → Hid keys ℓ[i].1

/-- A fresh entry keeps the hidden prefix. -/
theorem KgPre.append {keys : Keys nx ns} {k0 : ℕ} {ℓ : Log} (h : KgPre keys k0 ℓ) (x : Bytes)
    (u : Digest) : KgPre keys k0 (ℓ ++ [(x, u)]) := by
  have h1 := h.1
  refine ⟨by rw [List.length_append]; exact h1.trans (Nat.le_add_right _ _), fun i hi hk ↦ ?_⟩
  have hi' : i < ℓ.length := by omega
  rw [List.getElem_append_left hi']
  exact h.2 i hi' hk

/-- A log of hidden entries is its own hidden prefix. -/
theorem kgPre_of_allHid {keys : Keys nx ns} {ℓ : Log} (hall : ∀ e ∈ ℓ, Hid keys e.1) :
    KgPre keys ℓ.length ℓ :=
  ⟨le_rfl, fun _ hi _ ↦ hall _ (List.getElem_mem hi)⟩

/-- No format event within the hidden prefix. -/
theorem not_formatI_self (keys : Keys nx ns) (ℓ : Log) : ¬ FormatI keys ℓ.length ℓ :=
  fun ⟨_, hi, hk, _⟩ ↦ by omega

variable (keys : Keys nx ns) {ℓ₀ : Log} (hall : ∀ e ∈ ℓ₀, Hid keys e.1) {α : Type}
  (oa : OracleComp GameSpec α) {a b : ℕ} (ha : IsQueryBoundP oa (VisQ keys) a)
  (hb : IsQueryBoundP oa IsHash b) {N : ℕ} (hN : ℓ₀.length + b ≤ N)
include hall ha hb hN

/-- **T1's leg**: V°'s certificate's potential at least one, or a failure, before the format
event. -/
theorem prEvent_runGame_t1_le :
    Pr{let z ← (simulateQ gameImpl oa).run ℓ₀}[(1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind
        z.2 ∨ Fail leanVmSeeds z.2) ∧ ¬ FormatI keys ℓ₀.length z.2] ≤
      ind (Fail leanVmSeeds ℓ₀) + (a * εLean + b * failBound leanVmSeeds N) := by
  refine (prEvent_runGame_le_lin keys (KgPre keys ℓ₀.length) (fun ℓ x u h ↦ h.append x u) N
    (Φ := fun ℓ ↦ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ *
      ind (¬ FormatI keys ℓ₀.length ℓ)) ?_ ?_ oa a b ha hb ℓ₀ (kgPre_of_allHid hall) hN _ ?_).trans
    (add_le_add ?_ le_rfl)
  · intro ℓ x _ hlt _ hf
    refine le_trans (sum_stop_le_of_step (Φ := pot anyCertBlind.D leanVmSeeds anyProgramBlind)
      keys _ fun _ ↦ step_ineq (σ := leanVmSeeds) anyCertBlind anyCertBlind_bound ℓ x hf)
      (add_le_add le_rfl (add_le_add le_rfl ?_))
    rw [failTerm_eq_failBound]
    exact failBound_le_of_le _ (by omega)
  · intro ℓ x hI hlt hx hf
    exact (potStop_step_hid anyCertBlind.D leanVmSeeds anyProgramBlind
      (seedsNotHid_leanVmSeeds keys) hI.2 hx hf).trans
      (add_le_add le_rfl (failBound_le_of_le _ (by omega)))
  · rintro z _ ⟨h1, hF⟩ _
    rw [ind_of hF, mul_one]
    rcases h1 with h | h
    · exact h
    · simp only [pot, h, ↓reduceIte, le_refl]
  · calc pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ₀ * ind (¬ FormatI keys ℓ₀.length ℓ₀)
        ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ₀ * 1 := by gcongr; exact ind_le_one _
      _ ≤ _ := by rw [mul_one]; exact pot_le_of_allHid _ (seedsNotHid_leanVmSeeds keys) hall

/-- **W6's leg**: the batching's bad event from the baked start, before the format event. -/
theorem prEvent_runGame_w6_le :
    Pr{let z ← (simulateQ gameImpl oa).run ℓ₀}[BatchBad Guest.B1.Main.aggSeedD
        (bytecodeWords Guest.guest) z.2 ∧ ¬ FormatI keys ℓ₀.length z.2] ≤
      ind (Fail batchSeedsAll (startLog Guest.B1.Main.aggSeedD ℓ₀)) +
        (a * batchε + b * (((4 * (N + 1) : ℕ) : ℝ≥0∞) / Fintype.card Digest)) := by
  have hcap : ∀ ℓ : Log, ℓ.length < N →
      (((4 * (ℓ.length + 2) : ℕ) : ℝ≥0∞) / Fintype.card Digest) ≤
        ((4 * (N + 1) : ℕ) : ℝ≥0∞) / Fintype.card Digest := fun ℓ hlt ↦
    ENNReal.div_le_div_right (by exact_mod_cast Nat.mul_le_mul_left 4 (by omega)) _
  refine (prEvent_runGame_le_lin keys (KgPre keys ℓ₀.length) (fun ℓ x u h ↦ h.append x u) N
    (Φ := fun ℓ ↦ batchPot Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) ℓ *
      ind (¬ FormatI keys ℓ₀.length ℓ)) ?_ ?_ oa a b ha hb ℓ₀ (kgPre_of_allHid hall) hN _ ?_).trans
    (add_le_add ?_ le_rfl)
  · intro ℓ x _ hlt _ hf
    exact le_trans (sum_stop_le_of_step
      (Φ := batchPot Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest)) keys _ fun _ ↦
        batchPot_step _ _ ℓ x hf) (add_le_add le_rfl (add_le_add le_rfl (hcap ℓ hlt)))
  · intro ℓ x hI hlt hx hf
    exact (batchPotStop_step_hid _ (not_inPfx_aggSeedD keys) _ hI.2 hx hf).trans
      (add_le_add le_rfl (hcap ℓ hlt))
  · rintro z _ ⟨h1, hF⟩ _
    rw [ind_of hF, mul_one]
    exact h1
  · calc batchPot Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) ℓ₀ *
          ind (¬ FormatI keys ℓ₀.length ℓ₀)
        ≤ batchPot Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) ℓ₀ * 1 := by
          gcongr; exact ind_le_one _
      _ ≤ _ := by rw [mul_one]; exact batchPot_le_of_allHid (not_inPfx_aggSeedD keys) _ hall

/-- **E5's leg**: the DA bad event at the deployed padding, before the format event, at E5's full
rate on every hash query. -/
theorem prEvent_runGame_e5_le :
    Pr{let z ← (simulateQ gameImpl oa).run ℓ₀}[DaBad deployedPads.1 z.2 ∧
        ¬ FormatI keys ℓ₀.length z.2] ≤
      daPot deployedPads.1 ℓ₀ + b * (14 * (Fintype.card E : ℝ≥0∞)⁻¹ +
        ((4 * N : ℕ) : ℝ≥0∞) / Fintype.card Digest) := by
  have hcap : ∀ (ℓ : Log) (x : Bytes), ℓ.length < N →
      (∑ u, daPot deployedPads.1 (ℓ ++ [(x, u)]) * ind (¬ FormatI keys ℓ₀.length (ℓ ++ [(x, u)])))
          / Fintype.card Digest ≤
        daPot deployedPads.1 ℓ * ind (¬ FormatI keys ℓ₀.length ℓ) +
          (14 * (Fintype.card E : ℝ≥0∞)⁻¹ + ((4 * N : ℕ) : ℝ≥0∞) / Fintype.card Digest) :=
    fun ℓ x hlt ↦ (daPotStop_step keys _ _ ℓ x).trans (add_le_add le_rfl (add_le_add le_rfl
      (ENNReal.div_le_div_right (by exact_mod_cast Nat.mul_le_mul_left 4 (by omega)) _)))
  refine (prEvent_runGame_le_lin keys (KgPre keys ℓ₀.length) (fun ℓ x u h ↦ h.append x u) N
    (δp := 0) (δq := 14 * (Fintype.card E : ℝ≥0∞)⁻¹ + ((4 * N : ℕ) : ℝ≥0∞) / Fintype.card Digest)
    (Φ := fun ℓ ↦ daPot deployedPads.1 ℓ * ind (¬ FormatI keys ℓ₀.length ℓ)) ?_ ?_ oa a b ha hb
    ℓ₀ (kgPre_of_allHid hall) hN _ ?_).trans ?_
  · intro ℓ x _ hlt _ _
    rw [zero_add]
    exact hcap ℓ x hlt
  · intro ℓ x _ hlt _ _
    exact hcap ℓ x hlt
  · rintro z _ ⟨h1, hF⟩ _
    rw [ind_of hF, mul_one]
    exact one_le_daPot_of_daBad h1
  · rw [mul_zero, zero_add]
    refine add_le_add ?_ le_rfl
    calc daPot deployedPads.1 ℓ₀ * ind (¬ FormatI keys ℓ₀.length ℓ₀)
        ≤ daPot deployedPads.1 ℓ₀ * 1 := by gcongr; exact ind_le_one _
      _ = _ := mul_one _

/-- **The format event's leg**: the statement's format event, or the analysis's from the end of
the hidden prefix. -/
theorem prEvent_runGame_fmt_le :
    Pr{let z ← (simulateQ gameImpl oa).run ℓ₀}[FormatT keys z.2 ∨ FormatI keys ℓ₀.length z.2] ≤
      b * ((((nx + ns) * 2 ^ 64 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  have hstep : ∀ (ℓ : Log) (x : Bytes),
      (∑ u, ind (FormatI keys ℓ₀.length (ℓ ++ [(x, u)]))) / Fintype.card Digest ≤
        ind (FormatI keys ℓ₀.length ℓ) + (((nx + ns) * 2 ^ 64 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
    fun ℓ x ↦ avg_ind_formatI_le keys _ ℓ x
  refine (prEvent_runGame_le_lin keys (KgPre keys ℓ₀.length) (fun ℓ x u h ↦ h.append x u) N
    (δp := 0) (δq := (((nx + ns) * 2 ^ 64 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256)
    (Φ := fun ℓ ↦ ind (FormatI keys ℓ₀.length ℓ)) ?_ ?_ oa a b ha hb
    ℓ₀ (kgPre_of_allHid hall) hN _ ?_).trans (le_of_eq ?_)
  · intro ℓ x _ _ _ _
    rw [zero_add]
    exact hstep ℓ x
  · intro ℓ x _ _ _ _
    exact hstep ℓ x
  · rintro z _ h hI
    rw [ind_of (h.elim (FormatT.formatI hI.2) id)]
  · rw [ind_of_not (not_formatI_self keys ℓ₀), mul_zero, zero_add, zero_add]

/-- **T3's leg**: a restricted prediction at offset `o`, charged per visible query only. -/
theorem prEvent_runGame_t3_le (o : ℕ) :
    Pr{let z ← (simulateQ gameImpl oa).run ℓ₀}[PredS keys o z.2] ≤ a * (a + 1) / 2 ^ 193 := by
  refine (prEvent_runGame_le_budgeted keys (fun _ ↦ True) (fun _ _ _ _ ↦ trivial) N
    (Φ := fun m _ ℓ ↦ predPotS keys o m ℓ) ?_ ?_ ?_ oa a b ha hb ℓ₀ trivial hN _ ?_).trans
    (le_of_eq (predPotS_of_allHid hall a))
  · intro m n ℓ x _ _ hx _
    exact predPotS_step_vis hx m
  · intro m n ℓ x _ _ hx _
    exact predPotS_step_hid hx m
  · intro m n ℓ
    exact ⟨predPotS_mono m, le_rfl⟩
  · intro z _ h _
    rw [predPotS, ind_of h]
    exact le_self_add

end Legs

/-! ## The bound -/

section Bound

variable {nx ns : ℕ} [Sphincs.Params]

/-- The chain's bad events with the visible accounting (`AggBadT`: P5's four non-rank events). -/
def AggBadV (keys : Keys nx ns) (ℓ : Log) : Prop :=
  AggBadT ℓ ∨ PredS keys (predOffset (bytecodeWords Guest.guest)) ℓ ∨ FormatT keys ℓ

/-- The chain's error: `Qv` visible (non-hidden) and `Q` total hash queries, `n` keys. -/
noncomputable def visError (Qv Q n : ℕ) : ℝ≥0∞ :=
  Qv * (εLean + 2 / 2 ^ 192) + Q * (14 / 2 ^ 192) + Qv * (Qv + 1) / 2 ^ 193 +
    Q * (failBound leanVmSeeds (Q + 1) + 4 * (Q + 2) / 2 ^ 256 + 4 * (Q + 1) / 2 ^ 256 +
      (n * 2 ^ 64 + 1) / 2 ^ 256)

/-- **The chain's error as the proof gives it**: `visError` with the failure rates at `Q`
(§0's `sec0Error` forms). -/
noncomputable def visErrorTight (Qv Q n : ℕ) : ℝ≥0∞ :=
  Qv * (εLean + 2 / 2 ^ 192) + Q * (14 / 2 ^ 192) + Qv * (Qv + 1) / 2 ^ 193 +
    Q * (failBound leanVmSeeds Q + 4 * (Q + 1) / 2 ^ 256 + 4 * Q / 2 ^ 256 +
      (n * 2 ^ 64 + 1) / 2 ^ 256)

omit [Sphincs.Params] in
/-- The tight error is at most the plan's. -/
theorem visErrorTight_le_visError (Qv Q n : ℕ) : visErrorTight Qv Q n ≤ visError Qv Q n := by
  have h1 : failBound leanVmSeeds Q ≤ failBound leanVmSeeds (Q + 1) :=
    failBound_le_of_le _ (Nat.le_succ Q)
  have h2 : (4 * (Q + 1) / 2 ^ 256 : ℝ≥0∞) ≤ 4 * (Q + 2) / 2 ^ 256 := by
    gcongr
    norm_num
  have h3 : (4 * Q / 2 ^ 256 : ℝ≥0∞) ≤ 4 * (Q + 1) / 2 ^ 256 := by
    gcongr
    exact le_self_add
  unfold visErrorTight visError
  exact add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add (add_le_add (add_le_add h1 h2) h3)
    le_rfl))

open Classical in
/-- **The bad events with the visible accounting, tight constants.** In the game with V_I's
trace, with at most `Q_v = qH + budget` visible and
`Q = n_x · c_xk + n_s · c_sk + (qH + s_X · c_xs + s_S · c_ss) + budget` hash queries, the chain's
bad events have probability at most `visErrorTight Q_v Q (n_x + n_s)`. -/
theorem prEvent_gameRec_aggBadV_le_tight {cxk csk cxs css : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[AggBadV p.1.1.keys p.2] ≤
      visErrorTight (qH + budget) (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget)
        (nx + ns) := by
  let _ : MeasurableSpace ((Keys nx ns × SignState nx ns) × Log) := ⊤
  set N := nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget with hNdef
  set Qv := qH + budget with hQv
  set Qk := nx * cxk + ns * csk with hQk
  set Qr := (qH + sX * cxs + sS * css) + budget with hQr
  have hNk : Qk + Qr = N := by rw [hQk, hQr, hNdef]; omega
  -- The scheme walks (P2b, P2c) in the form of the counts (P2d).
  have hxw : ∀ sk i msg, IsQueryBoundP (LeanXmss.Seeded.sign sk i msg :
      OracleComp LeanXmss.HashSpec _)
      (fun x ↦ ¬ ∃ a, AddrOK a ∧ LeanXmss.bytesLE 16 sk.parameter ++ a <+: x) 0 :=
    fun sk i msg ↦ by
      refine IsQueryBoundP.of_imp ?_ (xmss_sign_queries sk i msg)
      exact fun _ hx h ↦ hx h.1
  have hsw : ∀ sk msg, IsQueryBoundP (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _)
      (fun x ↦ ¬ ∃ a, AddrOK a ∧ Sphincs.bytesLE 16 sk.parameter ++ a <+: x) 0 :=
    fun sk msg ↦ by
      refine IsQueryBoundP.of_imp ?_ (sphincs_sign_queries sk msg)
      exact fun _ hx h ↦ hx h.1
  have hkg := keygenPhase_hid (nx := nx) (ns := ns)
    (fun seed z hz x hx ↦ (xmss_keygen_queries seed z hz x hx).imp_right (·.1))
    (fun seed z hz x hx ↦ (sphincs_keygen_queries seed z hz x hx).imp_right (·.1))
  have hKQ : IsQueryBoundP ((keygen : GameM nx ns (Keys nx ns)).run (SignState.init nx ns))
      IsHash Qk := costs_keygen hxk hsk _
  -- The rates.
  set fbL := failBound leanVmSeeds N with hfbL
  set bq := ((4 * (N + 1) : ℕ) : ℝ≥0∞) / Fintype.card Digest with hbq
  set dq := 14 * (Fintype.card E : ℝ≥0∞)⁻¹ + ((4 * N : ℕ) : ℝ≥0∞) / Fintype.card Digest with hdq
  set r := (((nx + ns) * 2 ^ 64 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 with hr
  set T3 := (Qv : ℝ≥0∞) * (Qv + 1) / 2 ^ 193 with hT3
  set C := Qr * r + ((Qv * εLean + Qr * fbL) + ((Qv * batchε + Qr * bq) + (Qr * dq + T3)))
    with hC
  -- The bound at a reachable outcome of key generation.
  have hrest : ∀ k ∈ support (keygenPhase (nx := nx) (ns := ns)),
      Pr{let z ← (simulateQ gameImpl (restRec Guest.guest fuel budget A k.1.1 k.1.2)).run k.2}[
        AggBadV z.1.1.keys z.2] ≤
      ind (Fail leanVmSeeds k.2) + ind (Fail batchSeedsAll (startLog Guest.B1.Main.aggSeedD k.2)) +
        daPot deployedPads.1 k.2 + C := by
    intro k hk
    have hall := hkg k hk
    have ha : IsQueryBoundP (restRec Guest.guest fuel budget A k.1.1 k.1.2) (VisQ k.1.1) Qv :=
      isQueryBoundP_restRec_vis hxw hsw k.1.1 k.1.2 hH
    have hb : IsQueryBoundP (restRec Guest.guest fuel budget A k.1.1 k.1.2) IsHash Qr :=
      isQueryBoundP_restRec hxs hss Guest.guest fuel budget A hH hX hS k.1.1 k.1.2
    have hN : k.2.length + Qr ≤ N := by
      have := length_le_of_mem_support_runGame _ Qk hKQ [] hk
      simp only [List.length_nil, Nat.zero_add] at this
      omega
    have hinc : ∀ z ∈ support ((simulateQ gameImpl
          (restRec Guest.guest fuel budget A k.1.1 k.1.2)).run k.2),
        AggBadV z.1.1.keys z.2 →
        (FormatT k.1.1 z.2 ∨ FormatI k.1.1 k.2.length z.2) ∨
          (((1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind z.2 ∨ Fail leanVmSeeds z.2) ∧
              ¬ FormatI k.1.1 k.2.length z.2) ∨
            ((BatchBad Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) z.2 ∧
                ¬ FormatI k.1.1 k.2.length z.2) ∨
              ((DaBad deployedPads.1 z.2 ∧ ¬ FormatI k.1.1 k.2.length z.2) ∨
                PredS k.1.1 (predOffset (bytecodeWords Guest.guest)) z.2))) := by
      intro z hz h
      have hz1 : z.1 ∈ support (restRec Guest.guest fuel budget A k.1.1 k.1.2) :=
        support_simulateQ_run'_subset gameImpl
          (restRec Guest.guest fuel budget A k.1.1 k.1.2) k.2
          (by rw [StateT.run'_eq, support_map]; exact ⟨z, hz, rfl⟩)
      rw [restRec_keys hz1] at h
      by_cases hF : FormatI k.1.1 k.2.length z.2
      · exact Or.inl (Or.inr hF)
      rcases h with (h | h | h | h) | h | h
      · exact Or.inr (Or.inl ⟨Or.inl h, hF⟩)
      · exact Or.inr (Or.inl ⟨Or.inr h, hF⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h, hF⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hF⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inl (Or.inl h)
    refine (prEvent_mono_of_support _ _ _ hinc).trans ?_
    refine ((prEvent_or_le _ _ _).trans (add_le_add le_rfl ((prEvent_or_le _ _ _).trans
      (add_le_add le_rfl ((prEvent_or_le _ _ _).trans (add_le_add le_rfl
        (prEvent_or_le _ _ _))))))).trans ?_
    refine (add_le_add (prEvent_runGame_fmt_le k.1.1 hall _ ha hb hN)
      (add_le_add (prEvent_runGame_t1_le k.1.1 hall _ ha hb hN)
        (add_le_add (prEvent_runGame_w6_le k.1.1 hall _ ha hb hN)
          (add_le_add (prEvent_runGame_e5_le k.1.1 hall _ ha hb hN)
            (prEvent_runGame_t3_le k.1.1 hall _ ha hb hN _))))).trans (le_of_eq ?_)
    rw [hC, hT3, hr, hbq, hdq, hfbL]
    ring
  refine (prEvent_gameRec_le_of_phase (fun p ↦ AggBadV p.1.1.keys p.2)
    (fun k ↦ ind (Fail leanVmSeeds k.2) +
      ind (Fail batchSeedsAll (startLog Guest.B1.Main.aggSeedD k.2)) +
        daPot deployedPads.1 k.2 + C) hrest).trans ?_
  -- Key generation: the failure potentials.
  have hT1 : ∫⁻ k, ind (Fail leanVmSeeds k.2) ∂𝒟[keygenPhase (nx := nx) (ns := ns)] ≤
      Qk * fbL := by
    refine (lintegral_keygenPhase_le (f := fun ℓ ↦ ind (Fail leanVmSeeds ℓ)) (δ := fbL) N
      (fun ℓ x hlt _ ↦ (avg_ind_fail_le _ ℓ x).trans
      (add_le_add le_rfl (failBound_le_of_le _ (by omega)))) hKQ (by omega)).trans (le_of_eq ?_)
    rw [ind_of_not (not_fail_nil _), zero_add]
  have hW6 : ∫⁻ k, ind (Fail batchSeedsAll (startLog Guest.B1.Main.aggSeedD k.2))
      ∂𝒟[keygenPhase (nx := nx) (ns := ns)] ≤ Qk * bq := by
    refine (lintegral_keygenPhase_le
      (f := fun ℓ ↦ ind (Fail batchSeedsAll (startLog Guest.B1.Main.aggSeedD ℓ))) (δ := bq) N
      (fun ℓ x hlt _ ↦ ?_) hKQ (by omega)).trans (le_of_eq ?_)
    · by_cases hl : x = batchLabel
      · subst hl
        simp only [startLog_append_label]
        exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
      · simp only [startLog_append_of_ne _ ℓ hl]
        refine (avg_ind_fail_le _ _ x).trans (add_le_add le_rfl ?_)
        have hlen := length_startLog_le Guest.B1.Main.aggSeedD ℓ
        have hsteps : (batchSeedsAll.steps).length = 0 := rfl
        rw [failBound, hsteps, hbq, card_digest, Nat.cast_pow, Nat.cast_ofNat]
        have h4 : (4 + 0) * ((startLog Guest.B1.Main.aggSeedD ℓ).length + 1) ≤ 4 * (N + 1) := by
          omega
        exact ENNReal.div_le_div_right (by exact_mod_cast h4) _
    · rw [ind_of_not (not_fail_startLog_nil _), zero_add]
  have hE5 : ∫⁻ k, daPot deployedPads.1 k.2 ∂𝒟[keygenPhase (nx := nx) (ns := ns)] ≤
      Qk * dq := by
    refine (lintegral_keygenPhase_le (f := daPot deployedPads.1) (δ := dq) N
      (fun ℓ x hlt _ ↦ ?_) hKQ (by omega)).trans (le_of_eq ?_)
    · refine daPot_step.trans ?_
      rw [hdq]
      have h4 : ((4 * (ℓ.length + 1) : ℕ) : ℝ≥0∞) ≤ ((4 * N : ℕ) : ℝ≥0∞) := by
        exact_mod_cast Nat.mul_le_mul_left 4 (by omega)
      exact add_le_add le_rfl (add_le_add le_rfl (ENNReal.div_le_div_right h4 _))
    · rw [daPot_nil, zero_add]
  -- The integral of the per-outcome bound.
  have hint : ∫⁻ k, (ind (Fail leanVmSeeds k.2) +
      ind (Fail batchSeedsAll (startLog Guest.B1.Main.aggSeedD k.2)) +
        daPot deployedPads.1 k.2 + C) ∂𝒟[keygenPhase (nx := nx) (ns := ns)] ≤
      Qk * fbL + Qk * bq + Qk * dq + C := by
    rw [lintegral_add_right _ measurable_const, lintegral_add_left Measurable.of_discrete,
      lintegral_add_left Measurable.of_discrete, lintegral_const]
    exact add_le_add (add_le_add (add_le_add hT1 hW6) hE5)
      (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _))
  refine hint.trans ?_
  -- The constants.
  have hE : ∀ i : Fintype E, @Fintype.card E i = 2 ^ 192 := fun i ↦ by convert card_E
  have hbe : batchε = 2 / 2 ^ 192 := by rw [batchε, hE]; norm_cast
  have hdq' : dq = 14 / 2 ^ 192 + 4 * N / 2 ^ 256 := by
    rw [hdq, hE, card_digest, div_eq_mul_inv (14 : ℝ≥0∞)]
    norm_cast
  have hbq' : bq = 4 * (N + 1) / 2 ^ 256 := by
    rw [hbq, card_digest]
    norm_cast
  have hr' : r = ((nx + ns : ℕ) * 2 ^ 64 + 1) / 2 ^ 256 := by
    rw [hr]
    norm_cast
  have hNc : (N : ℝ≥0∞) = Qk + Qr := by rw [← hNk]; norm_cast
  calc Qk * fbL + Qk * bq + Qk * dq + C ≤ Qk * fbL + Qk * bq + Qk * dq + C + Qk * r :=
        le_self_add
    _ = visErrorTight Qv N (nx + ns) := by
        rw [visErrorTight, hC, hT3, hdq', hbq', hr', hbe, ← hfbL, hNc]
        ring

/-- **The bad events with the visible accounting.** In the game with V_I's trace, with at most
`Q_v = qH + budget` visible and `Q = n_x · c_xk + n_s · c_sk + (qH + s_X · c_xs + s_S · c_ss) +
budget` hash queries, the chain's bad events have probability at most
`visError Q_v Q (n_x + n_s)`. -/
theorem prEvent_gameRec_aggBadV_le {cxk csk cxs css : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[AggBadV p.1.1.keys p.2] ≤
      visError (qH + budget) (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget)
        (nx + ns) :=
  (prEvent_gameRec_aggBadV_le_tight hxk hsk hxs hss fuel budget A hH hX hS).trans
    (visErrorTight_le_visError _ _ _)

/-- **No bad event, T3's conclusion**: on a log without `AggBadV`, the guest's rank holds. -/
theorem rankOK_of_not_aggBadV {keys : Keys nx ns} {ℓ : Log} (h : ¬ AggBadV keys ℓ) : RankOK ℓ :=
  rankOK_of_vis (fun hf ↦ h (Or.inl (Or.inr (Or.inl hf)))) (fun hF ↦ h (Or.inr (Or.inr hF)))
    (fun hP ↦ h (Or.inr (Or.inl hP)))

/-- **No bad event, T4's events at the trace.** -/
theorem not_aggBadT_of_not_aggBadV {keys : Keys nx ns} {ℓ : Log} (h : ¬ AggBadV keys ℓ) :
    ¬ AggBadT ℓ :=
  fun h' ↦ h (Or.inl h')

end Bound

end
end LeanVM.E2E
