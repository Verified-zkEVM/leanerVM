/-
  LeanerVM.Protocol.RandomOracleBound

  The potential of the random-oracle bound: the sum, over the open groups of Fiat–Shamir queries,
  of their probabilities of closing on a bad challenge, and `1` once the hash has misbehaved. At a
  fresh query it grows in expectation by at most a charge: the chance the answer is a digest it
  must avoid, and the probabilities of the groups the query opens.
-/

module

public import LeanerVM.Protocol.ChainGroups
public import LeanerVM.Protocol.ToVCVio.ChargedInvariant
public import LeanerVM.Protocol.ToVCVio.UniformCondition

/-!
# The potential of the random-oracle bound

The lazy random oracle's state, `QueryHistory.freshLog`'s, is its cache and the log of its fresh
queries (`OracleState`). A log is `Clean` when it has no collision, no hit on the digests in play
from `seedRoots`, no query answered by one of its own halves, no flip (`SlotReader.FlipAt`), and
no query after the first `k₀` answered by one of `proofRoots`. Every theorem holds for every
reader of histories (`SlotReader`); the flips bounded are those of the reader the bound is stated
with, so a reader with no bad challenge makes the bound one on collisions and hits alone, and the
bound means what the extraction needs only when both are stated with the one reader of the
deployed protocol.

* `Φ`: on a state whose log is its cache's (`QueryHistory.IsFreshLog`) and clean, the sum over the
  open groups of their probabilities `π` of closing on a bad challenge; `1` on any other state.
* `charge s t`: on such a state, the probability `|B| / 2^256` that the answer to `t` is one of the
  digests `B` it must avoid (`badDigests`: an answer of the log, a digest in play, a half of `t`,
  and a root of `proofRoots` past the first `k₀` queries), plus the probabilities of the groups
  `t` opens.
* `potential_step`: at every fresh query, the expected potential after the uniform answer is at
  most the potential before plus the charge, the step of
  `QueryHistory.potential_le_expected_charge`.
  An answer to avoid makes the potential `1`; any other answer keeps the log clean but for a flip,
  which is a group open before or opened by the query reaching probability `1`, and moves only the
  groups the query touches, each a step of a martingale (`lintegral_π_le`): the probability of a
  group is the expectation, over the next answer, of its probability after it.
* `π_le_of_not_asked`: a group with no logged query closes on a bad challenge with probability at
  most `ε`, when every challenge is bad with probability at most `ε` (a marked one after a uniform
  check passes, `Density`); `sum_openedBy_le`: the groups one query opens are worth `ε` together,
  when the reader's starts are safe (`StartsSafe`: every start is one of `seedRoots`, or announces
  nothing at the empty history, so that a grinding base's answer that is a start fixes no
  challenge); `charge_le`: within `L` queries the charge is at most
  `(4L + |seedRoots| + |proofRoots|) / 2^256 + ε`. `startsSafe_of_seed`: a reader of one fixed
  seed among the roots has safe starts.
* `Φ_empty`: the potential starts at `0`; `Φ_start`: with the roots past a whole log it is the
  potential with no roots; `one_le_Φ`: it is at least `1` off a clean state.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash OracleComp OracleSpec ProtocolSpec
  MeasureTheory
open MerkleTree (logAnswer)
open scoped ENNReal

@[expose] public section

/-- The state of the lazy random oracle that records its fresh queries: the cache and the log of
fresh queries, in order. -/
abbrev OracleState : Type := hashSpec.QueryCache × hashSpec.QueryLog

/-- The digests the answer to a fresh query `t` must avoid: the log's answers, the digests in play,
the halves of `t`, and, once the first `k₀` queries are asked, the roots `proofRoots`. -/
def badDigests (seedRoots proofRoots : List Digest) (k₀ : ℕ) (l : hashSpec.QueryLog)
    (t : List UInt8) : List Digest :=
  l.map (·.2) ++ inPlay seedRoots l ++ halves t ++ if k₀ ≤ l.length then proofRoots else []

namespace SlotReader

variable (R : SlotReader) (seedRoots proofRoots : List Digest) (k₀ : ℕ)

/-- **A clean log**: no collision, no hit, no query answered by one of its halves, no flip, and no
query after the first `k₀` answered by a root of `proofRoots`. -/
def Clean (l : hashSpec.QueryLog) : Prop :=
  CleanLog seedRoots l ∧ (∀ e ∈ l, e.2 ∉ halves e.1) ∧ ¬ R.FlipAt l ∧
    ∀ e ∈ l.drop k₀, e.2 ∉ proofRoots

open Classical in
/-- **The potential**: on a state whose log is its cache's and clean, the sum over the open groups
of their probabilities of closing on a bad challenge; `1` on any other state. -/
noncomputable def Φ (s : OracleState) : ℝ≥0∞ :=
  if QueryHistory.IsFreshLog s ∧ R.Clean seedRoots proofRoots k₀ s.2 then
    ∑ G ∈ R.openGroups s.2, R.π s.2 G
  else 1

open Classical in
/-- **The charge of a fresh query**: on a state whose log is its cache's and clean, the chance that
its answer is a digest to avoid, and the probabilities of the groups it opens. -/
noncomputable def charge (s : OracleState) (t : List UInt8) : ℝ≥0∞ :=
  if QueryHistory.IsFreshLog s ∧ R.Clean seedRoots proofRoots k₀ s.2 then
    ((badDigests seedRoots proofRoots k₀ s.2 t).length : ℝ≥0∞) / 2 ^ 256 +
      ∑ G ∈ R.openedBy s.2 t, R.π s.2 G
  else 0

/-- **The density of bad challenges** is at most `ε`: at every challenge, a uniform challenge is
bad with probability at most `ε`, counted once a uniform check passes when a proof of work
precedes the challenge. -/
def Density (ε : ℝ≥0∞) : Prop :=
  ∀ a i tr, (if R.mark a i then Pr{let d ← $ᵗ Digest}[
    FsState.lowBitsZero d R.powBits = true] else 1) *
      Pr{let c ← $ᵗ ((R.spec a).Challenge i)}[c ∈ R.Bad a i tr] ≤ ε

/-- **The starts are safe** with the roots `roots`: every digest that opens a statement in a log is
one of the roots, or its statement announces nothing at the empty history. A start that is a root
answers no query of a clean log; one that is not may be a fresh answer, the grinding base's say,
and then its own history fixes no challenge. -/
def StartsSafe : Prop :=
  ∀ l σ st, R.stmtAt l σ = some st → σ ∈ seedRoots ∨ R.announcementOf st [] = none

/-- **Starts among the roots are safe.** -/
theorem startsSafe_of_roots (h : ∀ l d, R.isStart l d = true → d ∈ seedRoots) :
    R.StartsSafe seedRoots :=
  fun l σ _ hσ ↦ .inl (h l σ (by simp [ChainStarts.isStart, hσ]))

/-- **One fixed start among the roots is safe.** -/
theorem startsSafe_of_seed {seed : Digest} (hR : R.toChainStarts = ChainStarts.startAt seed)
    (hseed : seed ∈ seedRoots) : R.StartsSafe seedRoots :=
  R.startsSafe_of_roots seedRoots fun l d hd ↦ by
    have : (ChainStarts.startAt seed).isStart l d = true := hR ▸ hd
    simp only [ChainStarts.isStart_startAt, HashChain.isSeed_eq_true] at this
    exact this ▸ hseed

end SlotReader

/-! ## Clean logs and answers to avoid -/

variable {R : SlotReader} {seedRoots proofRoots : List Digest} {k₀ : ℕ} {l : hashSpec.QueryLog}
  {t : List UInt8} {u : Digest}

/-- A fresh query answered by a digest it need not avoid is a clean step. -/
private theorem cleanStep_of_not_mem (hfr : QueryLog.Fresh l t)
    (hu : u ∉ badDigests seedRoots proofRoots k₀ l t) : CleanStep seedRoots l t u := by
  simp only [badDigests, List.mem_append, not_or] at hu
  exact ⟨hfr, fun e he h ↦ hu.1.1.1 (h ▸ List.mem_map_of_mem he), hu.1.1.2, hu.1.2⟩

/-- A query of a log whose cache is its log is fresh when the cache does not hold it. -/
private theorem fresh_of_isFreshLog {s : OracleState} (hs : QueryHistory.IsFreshLog s)
    (ht : s.1 t = none) : QueryLog.Fresh s.2 t := fun ⟨t', u'⟩ he het ↦ by
  have := hs.1 _ he
  simp only at het this
  subst het
  simp [ht] at this

/-- An entry past the first `k` of a log with one more query. -/
private theorem mem_drop_concat {α : Type} {l : List α} {x e : α} {k : ℕ} :
    e ∈ (l ++ [x]).drop k ↔ e ∈ l.drop k ∨ (k ≤ l.length ∧ e = x) := by
  rw [List.drop_append, List.mem_append]
  by_cases hk : k ≤ l.length
  · simp [Nat.sub_eq_zero_of_le hk, hk]
  · simp [List.drop_eq_nil_of_le (show [x].length ≤ k - l.length by simp; omega), hk]

/-- A log clean after one more query is clean before it. -/
private theorem SlotReader.Clean.of_append (h : R.Clean seedRoots proofRoots k₀ (l ++ [⟨t, u⟩])) :
    R.Clean seedRoots proofRoots k₀ l := by
  obtain ⟨hl, hh, hf, hr⟩ := h
  refine ⟨hl.of_append, fun e he ↦ hh e (List.mem_append_left _ he),
    fun h ↦ hf (R.flipAt_append_of_flipAt hl h), fun e he ↦ hr e (mem_drop_concat.mpr (.inl he))⟩

/-- One more query answered by a digest it need not avoid keeps a clean log clean, unless it makes
a flip. -/
private theorem SlotReader.Clean.append (h : R.Clean seedRoots proofRoots k₀ l)
    (hfr : QueryLog.Fresh l t) (hu : u ∉ badDigests seedRoots proofRoots k₀ l t)
    (hf : ¬ R.FlipAt (l ++ [⟨t, u⟩])) :
    R.Clean seedRoots proofRoots k₀ (l ++ [⟨t, u⟩]) := by
  obtain ⟨hl, hh, -, hr⟩ := h
  have hs := cleanStep_of_not_mem hfr hu
  refine ⟨hl.append hs, fun e he ↦ ?_, hf, fun e he ↦ ?_⟩
  · rcases List.mem_append.mp he with he | he
    · exact hh e he
    · obtain rfl := List.mem_singleton.mp he
      exact hs.notHalf
  · rcases mem_drop_concat.mp he with he | ⟨hk, rfl⟩
    · exact hr e he
    · simp only [badDigests, hk, ↓reduceIte, List.mem_append, not_or] at hu
      exact hu.2

/-- An answer to avoid leaves no clean log. -/
private theorem SlotReader.not_clean_of_mem (hfr : QueryLog.Fresh l t)
    (hu : u ∈ badDigests seedRoots proofRoots k₀ l t) :
    ¬ R.Clean seedRoots proofRoots k₀ (l ++ [⟨t, u⟩]) := by
  rintro ⟨hl', hh, -, hr⟩
  simp only [badDigests, List.mem_append] at hu
  rcases hu with ((hu | hu) | hu) | hu
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hu
    refine hl'.noCollision ⟨e, List.mem_append_left _ he, ⟨t, e.2⟩, by simp, ?_, rfl⟩
    exact fun h ↦ hfr e he h
  · exact hl'.notInPlay_of_append hu
  · exact hh ⟨t, u⟩ (by simp) hu
  · split at hu
    · exact hr ⟨t, u⟩ (mem_drop_concat.mpr (.inr ⟨‹_›, rfl⟩)) hu
    · simp at hu

/-! ## A group's probability is a martingale -/

/-- One more fresh squeeze, conditioned on: the probability over the unasked squeezes after the
squeezes `r` is the expectation, over the next one, of the probability over the rest. -/
private theorem prEvent_squeezes_succ (Q : Digest → List Digest → Prop) (r : List Digest) (k : ℕ) :
    Pr{let z ← $ᵗ (Digest × (Fin (k + 1) → Digest))}[Q z.1 (r ++ List.ofFn z.2)] =
      ∫⁻ p, p ∂𝒟[(fun x ↦ Pr{let z ← $ᵗ (Digest × (Fin k → Digest))}[
        Q z.1 (r ++ [x] ++ List.ofFn z.2)]) <$> ($ᵗ Digest)] := by
  rw [prEvent_uniformSample_prod_finCons_eq_lintegral (fun z ↦ Q z.1 (r ++ List.ofFn z.2))]
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.append_assoc,
    List.singleton_append]

/-- A squeeze is no grinding check. -/
private theorem squeezeInput_ne_checkInput (x b : Digest) (n : E) :
    squeezeInput x ≠ checkInput b n :=
  fun h ↦ by simpa using (input_inj (h.trans (checkInput_eq b n))).2

/-- A squeeze is no nonce step. -/
private theorem squeezeInput_ne_absorbInput (x cv : Digest) (n : E) :
    squeezeInput x ≠ absorbInput cv n :=
  fun h ↦ by simpa using (input_inj h).2

/-- A group's probability, at the challenge it fixes. -/
private theorem SlotReader.π_eq_of_groupSlot {l' : hashSpec.QueryLog} {G : Group} {a : R.Ann}
    {i : (R.spec a).ChallengeIdx} {tr : (R.spec a).Transcript i.1.castSucc}
    (h : R.groupSlot l' G = some ⟨a, i, tr⟩) :
    R.π l' G = Pr{let z ← $ᵗ (Digest × (Fin ((R.slot a i).m -
      (G.run l' (R.slot a i).m).length) → Digest))}[(G.nonce.isSome = true →
        FsState.lowBitsZero ((G.check? l').getD z.1) R.powBits = true) ∧
      (R.slot a i).assemble (fun j ↦ (G.run l' (R.slot a i).m ++ List.ofFn z.2).getD j
        default) ∈ R.Bad a i tr] := by
  simp only [SlotReader.π, h]

/-- The martingale step at the group's next squeeze: the probability is the expectation, over
the squeeze's answer, of the probability with the answer logged. -/
private theorem SlotReader.lintegral_π_le_of_squeeze (hfr : QueryLog.Fresh l t) {G : Group}
    {a : R.Ann} {i : (R.spec a).ChallengeIdx} {tr : (R.spec a).Transcript i.1.castSucc}
    (hg : R.groupSlot l G = some ⟨a, i, tr⟩)
    (hg' : ∀ u, u ∉ badDigests seedRoots proofRoots k₀ l t →
      R.groupSlot (l ++ [⟨t, u⟩]) G = some ⟨a, i, tr⟩)
    {s₀ : Digest} (hs₀ : G.start? l = some s₀)
    (hlen : (squeezeRun l s₀ (R.slot a i).m).length < (R.slot a i).m)
    (ht : t = squeezeInput ((squeezeRun l s₀ (R.slot a i).m).getLastD s₀)) :
    ∫⁻ p, p ∂𝒟[(fun u ↦ if u ∈ badDigests seedRoots proofRoots k₀ l t then 0
      else R.π (l ++ [⟨t, u⟩]) G) <$> ($ᵗ Digest)] ≤ R.π l G := by
  have hrun : G.run l (R.slot a i).m = squeezeRun l s₀ (R.slot a i).m := by
    simp [Group.run, hs₀]
  have hk : (R.slot a i).m - (G.run l (R.slot a i).m).length =
      ((R.slot a i).m - ((G.run l (R.slot a i).m).length + 1)) + 1 := by
    rw [hrun]; omega
  rw [R.π_eq_of_groupSlot hg, hk]
  refine le_of_le_of_eq ?_ (prEvent_squeezes_succ (fun c ds ↦ (G.nonce.isSome = true →
    FsState.lowBitsZero ((G.check? l).getD c) R.powBits = true) ∧
      (R.slot a i).assemble (fun j ↦ ds.getD j default) ∈ R.Bad a i tr)
        (G.run l (R.slot a i).m) ((R.slot a i).m - ((G.run l (R.slot a i).m).length + 1))).symm
  refine lintegral_id_evalDist_map_mono _ fun u ↦ ?_
  split_ifs with hu
  · exact zero_le
  have hs := cleanStep_of_not_mem hfr hu
  have hc : G.check? (l ++ [⟨t, u⟩]) = G.check? l :=
    Group.check?_append hs fun n b _ _ h ↦ squeezeInput_ne_checkInput _ b n (ht.symm.trans h)
  have hst : G.start? (l ++ [⟨t, u⟩]) = G.start? l :=
    Group.start?_append fun n _ h ↦ squeezeInput_ne_absorbInput _ G.cv n (ht.symm.trans h)
  have hr : G.run (l ++ [⟨t, u⟩]) (R.slot a i).m = G.run l (R.slot a i).m ++ [u] := by
    simp only [Group.run, hst, hs₀]
    rw [squeezeRun_append hs.logAnswer_squeezeInput hfr]
    simp [hlen, ht]
  rw [R.π_eq_of_groupSlot (hg' u hu), hc, hr, List.length_append, List.length_singleton]

/-- The martingale step at the group's check: the probability is the expectation, over the
check's answer, of the probability with the answer logged. -/
private theorem SlotReader.lintegral_π_le_of_check (hfr : QueryLog.Fresh l t) {G : Group}
    {a : R.Ann} {i : (R.spec a).ChallengeIdx} {tr : (R.spec a).Transcript i.1.castSucc}
    (hg : R.groupSlot l G = some ⟨a, i, tr⟩)
    (hg' : ∀ u, u ∉ badDigests seedRoots proofRoots k₀ l t →
      R.groupSlot (l ++ [⟨t, u⟩]) G = some ⟨a, i, tr⟩)
    {n : E} {b : Digest} (hn : G.nonce = some n) (hb : logAnswer l (baseInput G.cv) = some b)
    (ht : t = checkInput b n) :
    ∫⁻ p, p ∂𝒟[(fun u ↦ if u ∈ badDigests seedRoots proofRoots k₀ l t then 0
      else R.π (l ++ [⟨t, u⟩]) G) <$> ($ᵗ Digest)] ≤ R.π l G := by
  have hc₀ : G.check? l = none := by
    simp [Group.check?, hn, hb, ← ht, logAnswer_eq_none_iff.mpr hfr]
  rw [R.π_eq_of_groupSlot hg, hc₀]
  simp only [Option.getD_none]
  rw [prEvent_uniformSample_prod_eq_lintegral]
  refine lintegral_id_evalDist_map_mono _ fun u ↦ ?_
  split_ifs with hu
  · exact zero_le
  have hc : G.check? (l ++ [⟨t, u⟩]) = some u := by
    simp [Group.check?, hn, logAnswer_append_of_eq_some hb, ← ht, logAnswer_append_self hfr]
  have hr : G.run (l ++ [⟨t, u⟩]) (R.slot a i).m = G.run l (R.slot a i).m :=
    Group.run_append (cleanStep_of_not_mem hfr hu) fun _ _ _ h ↦
      squeezeInput_ne_checkInput _ b n (h.symm.trans ht)
  rw [R.π_eq_of_groupSlot (hg' u hu), hc, hr]
  simp only [Option.getD_some]
  exact (prEvent_uniformSample_snd (α := Digest)
    (fun w : Fin ((R.slot a i).m - (G.run l (R.slot a i).m).length) → Digest ↦
      (G.nonce.isSome = true → FsState.lowBitsZero u R.powBits = true) ∧
        (R.slot a i).assemble (fun j ↦ (G.run l (R.slot a i).m ++ List.ofFn w).getD j default) ∈
          R.Bad a i tr)).le

/-- **A group's probability is a martingale**: over a fresh answer to `t`, the expected probability
that a group closes on a bad challenge after the answer, counting nothing on an answer to avoid, is
at most its probability before. The answer is one of the group's unasked queries (its next
squeeze, its check) or leaves the group as it was. -/
private theorem SlotReader.lintegral_π_le (hl : CleanLog seedRoots l) (hfr : QueryLog.Fresh l t)
    {G : Group} (hG : ∀ u, u ∉ badDigests seedRoots proofRoots k₀ l t → G.cv ≠ u) :
    ∫⁻ p, p ∂𝒟[(fun u ↦ if u ∈ badDigests seedRoots proofRoots k₀ l t then 0
      else R.π (l ++ [⟨t, u⟩]) G) <$> ($ᵗ Digest)] ≤ R.π l G := by
  classical
  have hslot : ∀ u, u ∉ badDigests seedRoots proofRoots k₀ l t →
      R.groupSlot (l ++ [⟨t, u⟩]) G = R.groupSlot l G :=
    fun u hu ↦ R.groupSlot_append (hl.append (cleanStep_of_not_mem hfr hu)) (hG u hu)
  cases hg : R.groupSlot l G with
  | none =>
    refine lintegral_id_evalDist_map_le_of_le _ fun u ↦ ?_
    split_ifs with hu
    · exact zero_le
    · simp [SlotReader.π, hslot u hu, hg]
  | some x =>
    obtain ⟨a, i, tr⟩ := x
    have hg' : ∀ u, u ∉ badDigests seedRoots proofRoots k₀ l t →
        R.groupSlot (l ++ [⟨t, u⟩]) G = some ⟨a, i, tr⟩ := fun u hu ↦ (hslot u hu).trans hg
    by_cases hA : ∃ s₀, G.start? l = some s₀ ∧
        (squeezeRun l s₀ (R.slot a i).m).length < (R.slot a i).m ∧
          t = squeezeInput ((squeezeRun l s₀ (R.slot a i).m).getLastD s₀)
    · obtain ⟨s₀, hs₀, hlen, ht⟩ := hA
      exact R.lintegral_π_le_of_squeeze hfr hg hg' hs₀ hlen ht
    by_cases hB : ∃ n b, G.nonce = some n ∧ logAnswer l (baseInput G.cv) = some b ∧
        t = checkInput b n
    · obtain ⟨n, b, hn, hb, ht⟩ := hB
      exact R.lintegral_π_le_of_check hfr hg hg' hn hb ht
    -- any other query leaves the group's check and squeezes as they were
    refine lintegral_id_evalDist_map_le_of_le _ fun u ↦ ?_
    split_ifs with hu
    · exact zero_le
    have hs := cleanStep_of_not_mem hfr hu
    rw [R.π_eq_of_groupSlot (hg' u hu), R.π_eq_of_groupSlot hg,
      Group.check?_append hs fun n b hn hb h ↦ hB ⟨n, b, hn, hb, h⟩,
      Group.run_append hs fun s hs hlen h ↦ hA ⟨s, hs, hlen, h⟩]

/-! ## The step of the potential -/

/-- A uniform digest is one of `B` with probability at most `|B| / 2^256`. -/
private theorem prEvent_mem_le (B : List Digest) :
    Pr{let u ← $ᵗ Digest}[u ∈ B] ≤ (B.length : ℝ≥0∞) / 2 ^ 256 := by
  have h := (SampleableType.prEvent_uniformSample_le_div_iff (· ∈ B) (c := B.length)).mpr
    ((congrArg Finset.card (Finset.ext fun _ ↦ by simp)).trans_le B.toFinset_card_le)
  rwa [card_digest, Nat.cast_pow, Nat.cast_ofNat] at h

/-- A group open in a log starts from a digest in play. -/
private theorem SlotReader.cv_mem_inPlay_of_mem_openGroups {G : Group} (h : G ∈ R.openGroups l) :
    G.cv ∈ inPlay seedRoots l := by
  rw [R.mem_openGroups_iff] at h
  simp only [SlotReader.isOpen, Bool.and_eq_true] at h
  obtain ⟨q, d, hq, hcv⟩ := Group.exists_query_of_asked h.1.2
  exact mem_inPlay_of_logAnswer hq hcv

/-- **The step of the potential**: at a fresh query, the expected potential after the uniform
answer is at most the potential before plus the query's charge. -/
theorem SlotReader.potential_step (s : OracleState) (t : List UInt8) (ht : s.1 t = none) :
    ∫⁻ p, p ∂𝒟[(fun u ↦ R.Φ seedRoots proofRoots k₀ (QueryHistory.freshLog.record s t u)) <$>
      ($ᵗ Digest)] ≤ R.Φ seedRoots proofRoots k₀ s + R.charge seedRoots proofRoots k₀ s t := by
  classical
  by_cases hgood : QueryHistory.IsFreshLog s ∧ R.Clean seedRoots proofRoots k₀ s.2
  · obtain ⟨hinv, hcl⟩ := hgood
    have hfr := fresh_of_isFreshLog hinv ht
    have hrec : ∀ u, (QueryHistory.freshLog.record s t u).2 = s.2 ++ [⟨t, u⟩] := fun _ ↦ rfl
    rw [SlotReader.Φ, ite_eq_left_of_eq_true _ _ (eq_true ⟨hinv, hcl⟩), SlotReader.charge,
      ite_eq_left_of_eq_true _ _ (eq_true ⟨hinv, hcl⟩)]
    set B := badDigests seedRoots proofRoots k₀ s.2 t with hB
    have hpt : ∀ u, R.Φ seedRoots proofRoots k₀ (QueryHistory.freshLog.record s t u) ≤
        ((if u ∈ B then 1 else 0) + ∑ G ∈ R.openGroups s.2,
          (if u ∈ B then 0 else R.π (s.2 ++ [⟨t, u⟩]) G)) +
        ∑ G ∈ R.openedBy s.2 t, (if u ∈ B then 0 else R.π (s.2 ++ [⟨t, u⟩]) G) := by
      intro u
      by_cases hu : u ∈ B
      · rw [SlotReader.Φ, ite_eq_right_of_eq_false _ _
          (eq_false fun h ↦ R.not_clean_of_mem hfr hu (hrec u ▸ h.2))]
        simp [hu]
      · simp only [hu, ↓reduceIte, zero_add]
        have hs := cleanStep_of_not_mem hfr hu
        refine le_trans ?_ (le_self_add.trans_eq Finset.sum_union_inter)
        by_cases hf : R.FlipAt (s.2 ++ [⟨t, u⟩])
        · rw [SlotReader.Φ, ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ (hrec u ▸ h.2).2.2.1 hf)]
          obtain ⟨G, hG, -, hπ⟩ := R.flipAt_append hcl.1 hs hcl.2.2.1 hf
          exact hπ ▸ Finset.single_le_sum (f := fun G ↦ R.π (s.2 ++ [⟨t, u⟩]) G)
            (fun _ _ ↦ zero_le) hG
        · rw [SlotReader.Φ, ite_eq_left_of_eq_true _ _
            (eq_true ⟨hinv.record ht u, hrec u ▸ hcl.append hfr hu hf⟩), hrec u]
          exact Finset.sum_le_sum_of_subset (R.openGroups_append_subset hcl.1 hs)
    refine (lintegral_id_evalDist_map_mono _ hpt).trans ?_
    rw [lintegral_id_evalDist_map_add, lintegral_id_evalDist_map_add,
      lintegral_id_evalDist_map_finset_sum, lintegral_id_evalDist_map_finset_sum,
      ← prEvent_eq_lintegral_id_evalDist_map_ite]
    -- every group summed over starts from a digest to avoid
    have hcv : ∀ G : Group, G.cv ∈ halves t ∨ G.cv ∈ inPlay seedRoots s.2 →
        ∀ u, u ∉ badDigests seedRoots proofRoots k₀ s.2 t → G.cv ≠ u := fun G hG u hu h ↦ hu (by
      simp only [badDigests, List.mem_append]
      exact hG.elim (fun hc ↦ .inl (.inr (h ▸ hc))) fun hc ↦ .inl (.inl (.inr (h ▸ hc))))
    calc _ ≤ (B.length : ℝ≥0∞) / 2 ^ 256 + ∑ G ∈ R.openGroups s.2, R.π s.2 G +
          ∑ G ∈ R.openedBy s.2 t, R.π s.2 G :=
        add_le_add (add_le_add (prEvent_mem_le B) (Finset.sum_le_sum fun G hG ↦
          R.lintegral_π_le hcl.1 hfr (hcv G (.inr (R.cv_mem_inPlay_of_mem_openGroups hG)))))
          (Finset.sum_le_sum fun G hG ↦ R.lintegral_π_le hcl.1 hfr
            (hcv G (R.cv_mem_of_mem_touched (R.mem_openedBy_iff.mp hG).1)))
      _ = _ := by ring
  · rw [SlotReader.Φ, ite_eq_right_of_eq_false _ _ (eq_false hgood), SlotReader.charge,
      ite_eq_right_of_eq_false _ _ (eq_false hgood), add_zero]
    refine lintegral_id_evalDist_map_le_of_le _ fun u ↦ ?_
    rw [SlotReader.Φ, ite_eq_right_of_eq_false _ _
      (eq_false fun h ↦ hgood ⟨h.1.of_record ht, h.2.of_append⟩)]

/-! ## The charge's bound -/

/-- A group keeps a challenge marked exactly when it has a nonce. -/
private theorem SlotReader.mark_eq_of_groupSlot {G : Group} {a : R.Ann}
    {i : (R.spec a).ChallengeIdx} {tr : (R.spec a).Transcript i.1.castSucc}
    (h : R.groupSlot l G = some ⟨a, i, tr⟩) :
    R.mark a i = G.nonce.isSome := by
  unfold SlotReader.groupSlot at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨hs, -, st, -, a', -, p, -, ⟨i', tr'⟩, -, h⟩ := h
  split_ifs at h with hm
  cases h
  exact hm

/-- **The opening bound**: a group with no logged query closes on a bad challenge with
probability at most `ε`, when the bad challenges have density at most `ε`. -/
theorem SlotReader.π_le_of_not_asked {ε : ℝ≥0∞} (hbad : R.Density ε) {G : Group}
    (h : G.asked l (R.size l G) = false) : R.π l G ≤ ε := by
  cases hg : R.groupSlot l G with
  | none => simp [SlotReader.π, hg]
  | some x =>
    obtain ⟨a, i, tr⟩ := x
    have hm : R.size l G = (R.slot a i).m := by simp [SlotReader.size, hg]
    rw [hm] at h
    simp only [Group.asked, Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_false',
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, List.isEmpty_iff] at h
    obtain ⟨⟨hc, -⟩, hr⟩ := h
    rw [R.π_eq_of_groupSlot hg, hc, hr]
    simp only [List.length_nil, Nat.sub_zero, Option.getD_none, List.nil_append]
    have hz : ∀ z : Fin (R.slot a i).m → Digest,
        (fun j : Fin (R.slot a i).m ↦ (List.ofFn z).getD j default) = z := fun z ↦
      funext fun j ↦ by simp [List.getD_eq_getElem?_getD]
    simp only [hz]
    have hb := hbad a i tr
    rw [R.mark_eq_of_groupSlot hg] at hb
    rcases hn : G.nonce with _ | n <;> simp only [hn, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte, one_mul, false_implies, true_and, forall_const] at hb ⊢
    · rwa [prEvent_uniformSample_snd (α := Digest)
        (fun w ↦ (R.slot a i).assemble w ∈ R.Bad a i tr), (R.slot a i).uniform]
    · rwa [SampleableType.prEvent_uniformSample_prod,
        prEvent_bind_bind_and ($ᵗ Digest) ($ᵗ (Fin (R.slot a i).m → Digest))
          (fun d ↦ FsState.lowBitsZero d R.powBits = true)
          (fun w ↦ (R.slot a i).assemble w ∈ R.Bad a i tr), (R.slot a i).uniform]

/-- A sum over a finite set whose terms are nonzero at one member at most, each at most `ε`, is
at most `ε`. -/
private theorem sum_le_of_unique {α : Type} {S : Finset α} {f : α → ℝ≥0∞} {ε : ℝ≥0∞}
    (h : ∀ x ∈ S, ∀ y ∈ S, f x ≠ 0 → f y ≠ 0 → x = y) (hε : ∀ x ∈ S, f x ≤ ε) :
    ∑ x ∈ S, f x ≤ ε := by
  by_cases hx : ∃ x ∈ S, f x ≠ 0
  · obtain ⟨x, hx, hfx⟩ := hx
    rw [Finset.sum_eq_single x (fun y hy hyx ↦ by_contra fun hfy ↦ hyx (h y hy x hx hfy hfx))
      (fun hx' ↦ absurd hx hx')]
    exact hε x hx
  · rw [Finset.sum_eq_zero fun x hxS ↦ by_contra fun h ↦ hx ⟨x, hxS, h⟩]
    exact zero_le

/-- On a log with no collision, the states whose grinding base it answers by `y` are one at
most. -/
private theorem baseStates_unique (hcoll : ¬ QueryLog.HasCollision l) {y cv cv' : Digest}
    (h : cv ∈ baseStates l y) (h' : cv' ∈ baseStates l y) : cv = cv' := by
  simp only [baseStates, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq] at h h'
  obtain ⟨e, he, ⟨hy, -⟩, rfl⟩ := h
  obtain ⟨e', he', ⟨hy', -⟩, rfl⟩ := h'
  by_contra hne
  exact hcoll ⟨e, he, e', he', fun hq ↦ hne (by rw [hq]), hy.trans hy'.symm⟩

/-- On a clean log, a base answer is no state's: a nonce step from it fixes no challenge, when the
reader's starts are safe. -/
private theorem SlotReader.groupSlot_of_mem_baseStates (hl : CleanLog seedRoots l)
    (hsafe : R.StartsSafe seedRoots) {y cv : Digest} (h : cv ∈ baseStates l y) (n : Option E) :
    R.groupSlot l ⟨y, n⟩ = none := by
  simp only [baseStates, List.mem_filterMap, Option.ite_none_right_eq_some] at h
  obtain ⟨e, he, ⟨hey, hb⟩, -⟩ := h
  have hroot : y ∉ seedRoots := fun hy ↦ by
    obtain ⟨p, hp, hfresh, hpe⟩ := QueryLog.first_occurrence hl.consistent he
    refine hl.noHit ⟨⟨p, hp⟩, by simpa [hpe] using hfresh, ?_⟩
    simp only [Fin.getElem_fin, hpe, hey]
    exact mem_inPlay_of_mem_roots hy
  cases hst : R.stmtAt l y with
  | some st =>
    -- a start: its empty history announces nothing
    have hann := (hsafe l y st hst).resolve_left hroot
    have hch : chainHistory l (R.isStart l) ⟨y⟩ = some (y, []) := by
      have : R.isStart l y = true := by simp [ChainStarts.isStart, hst]
      unfold chainHistory HashChain.history
      cases l.length <;> simp [HashChain.walk, this]
    simp [SlotReader.groupSlot, hch, hst, hann]
  | none =>
    -- no start, and the log shows no step into it
    have hpre : HashChain.preimages Block.parse? l y = [] := by
      refine List.filterMap_eq_nil_iff.mpr fun e' he' ↦ ?_
      split
      · rename_i he'y
        have : e'.1 = e.1 :=
          by_contra fun hne ↦ hl.noCollision ⟨e', he', e, he, hne, he'y.trans hey.symm⟩
        rw [this, hb, parse?_baseInput]
      · rfl
    have : chainHistory l (R.isStart l) ⟨y⟩ = none :=
      HashChain.history_eq_none (by simp [ChainStarts.isStart, hst]) hpre
    simp [SlotReader.groupSlot, this]

/-- **The groups a query opens** have probabilities summing to at most `ε` on a clean log: a
squeeze opens the plain group at its state alone, and a nonce step the group it absorbs and the
group it checks, of which the first fixes no challenge when the second exists. -/
private theorem SlotReader.sum_openedBy_le (hl : CleanLog seedRoots l)
    (hsafe : R.StartsSafe seedRoots)
    {ε : ℝ≥0∞} (hε : ∀ G, G.asked l (R.size l G) = false → R.π l G ≤ ε) :
    ∑ G ∈ R.openedBy l t, R.π l G ≤ ε := by
  refine sum_le_of_unique (fun G hG G' hG' hπ hπ' ↦ ?_)
    fun G hG ↦ hε G (R.mem_openedBy_iff.mp hG).2
  rw [R.mem_openedBy_iff] at hG hG'
  obtain ⟨hG, ha⟩ := hG
  obtain ⟨hG', ha'⟩ := hG'
  unfold SlotReader.touched at hG hG'
  split at hG
  · rename_i x hx
    rw [hx] at hG'
    simp only [List.mem_filter] at hG hG'
    -- an unasked group awaiting the squeeze from `x` is the plain group at `x`
    have key : ∀ H : Group, H.asked l (R.size l H) = false → R.awaits l H x = true →
        H = ⟨x, none⟩ := by
      intro H hna haw
      unfold SlotReader.awaits at haw
      split at haw
      · cases haw
      · rename_i s hs
        simp only [Group.asked, hs, Option.isSome_some, Bool.and_true, Bool.or_eq_false_iff,
          Bool.not_eq_false', List.isEmpty_iff] at hna
        obtain ⟨⟨-, hnn⟩, hr⟩ := hna
        simp only [hr, List.length_nil, List.getLastD_nil, Bool.and_eq_true,
          decide_eq_true_eq] at haw
        obtain ⟨cv, nonce⟩ := H
        rcases nonce with _ | n
        · simp only [Group.start?, Option.some.injEq] at hs
          rw [hs, haw.2]
        · simp at hnn
    rw [key G ha hG.2, key G' ha' hG'.2]
  · rename_i y n hy
    rw [hy] at hG'
    simp only [List.mem_cons, List.mem_map] at hG hG'
    have hzero : ∀ cv, cv ∈ baseStates l y → R.π l ⟨y, some n⟩ = 0 := fun cv hcv ↦ by
      simp [SlotReader.π, R.groupSlot_of_mem_baseStates hl hsafe hcv]
    rcases hG with rfl | ⟨cv, hcv, rfl⟩ <;> rcases hG' with rfl | ⟨cv', hcv', rfl⟩
    · rfl
    · exact absurd (hzero cv' hcv') hπ
    · exact absurd (hzero cv hcv) hπ'
    · rw [baseStates_unique hl.noCollision hcv hcv']
  · simp at hG

/-- **The charge is bounded** at a state reached within `L` fresh queries: at most
`(4L + |seedRoots| + |proofRoots|) / 2^256` for the answer, and `ε` for the groups the query
opens when the bad challenges have density at most `ε` and the reader's starts are safe. -/
theorem SlotReader.charge_le (hsafe : R.StartsSafe seedRoots) {ε : ℝ≥0∞} (hbad : R.Density ε)
    {s : OracleState} {L : ℕ} (hL : s.1.enncard + 1 ≤ L) (t : List UInt8) :
    R.charge seedRoots proofRoots k₀ s t ≤
      ((4 * L + seedRoots.length + proofRoots.length : ℕ) : ℝ≥0∞) / 2 ^ 256 + ε := by
  classical
  unfold SlotReader.charge
  split_ifs with hgood
  · obtain ⟨hinv, hcl⟩ := hgood
    refine add_le_add (ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _)
      (R.sum_openedBy_le hcl.1 hsafe fun G hG ↦ R.π_le_of_not_asked hbad hG)
    have hl : s.2.length + 1 ≤ L := by
      rw [hinv.enncard_eq] at hL
      exact_mod_cast hL
    have hp := length_inPlay_le seedRoots s.2
    have hh := length_halves_le t
    have hr : (if k₀ ≤ s.2.length then proofRoots else []).length ≤ proofRoots.length := by
      split_ifs <;> simp
    simp only [badDigests, List.length_append, List.length_map]
    omega
  · exact zero_le

/-! ## The potential at the start -/

/-- No root is asked after all of a log's queries: the potential with the roots past the whole
log is the potential with none. -/
theorem SlotReader.Φ_start (s : OracleState) :
    R.Φ seedRoots proofRoots s.2.length s = R.Φ seedRoots [] 0 s := by
  have : R.Clean seedRoots proofRoots s.2.length s.2 ↔ R.Clean seedRoots [] 0 s.2 := by
    simp [SlotReader.Clean]
  classical
  exact if_congr (and_congr_right fun _ ↦ this) rfl rfl

/-- The empty log has no flip. -/
private theorem SlotReader.not_flipAt_nil : ¬ R.FlipAt [] := fun ⟨G, hG⟩ ↦ by
  obtain ⟨-, -, ha⟩ := R.complete_of_flips hG
  obtain ⟨q, d, hq, -⟩ := Group.exists_query_of_asked ha
  simp [logAnswer] at hq

/-- **The potential at the start** is `0`: the empty log is clean and has no open group. -/
theorem SlotReader.Φ_empty : R.Φ seedRoots proofRoots k₀ ((∅ : hashSpec.QueryCache), []) = 0 := by
  have hclean : R.Clean seedRoots proofRoots k₀ [] :=
    ⟨⟨by simp, fun ⟨_, h, _⟩ ↦ by simp at h, fun ⟨⟨_, h⟩, _⟩ ↦ by simp at h⟩, by simp,
      R.not_flipAt_nil, by simp⟩
  rw [SlotReader.Φ, ite_eq_left_of_eq_true _ _ (eq_true ⟨QueryHistory.isFreshLog_empty, hclean⟩)]
  simp [SlotReader.openGroups, candidates, nonceGroups, checkGroups]

/-- The potential is at least `1` off a clean state. -/
theorem SlotReader.one_le_Φ {s : OracleState}
    (h : ¬ (QueryHistory.IsFreshLog s ∧ R.Clean seedRoots proofRoots k₀ s.2)) :
    1 ≤ R.Φ seedRoots proofRoots k₀ s := by
  rw [SlotReader.Φ, ite_eq_right_of_eq_false _ _ (eq_false h)]

end
end LeanerVM.Protocol
