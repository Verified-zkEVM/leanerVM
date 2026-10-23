/-
  LeanerVM.Protocol.ToVCVio.QueryLog

  What a finite log of queries to one function shows: whether it is the trace of a function,
  whether it has a collision, which queries are fresh, and whether a fresh answer hits a value
  already in play. Candidate for VCVio.
-/

module

public import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Induction

/-!
# Facts read off a query log

A log is the list of a run's queries with their answers, in the order asked:
`List ((_ : Q) × D)`, to which VCVio's `(Q →ₒ D).QueryLog` and `MerkleTreeExtractor.QueryLog Q D`
both unfold. Every predicate here is decidable.

* `Consistent`: no input appears with two answers; the log is the trace of a function.
* `HasCollision`: two different inputs have one answer.
* `Fresh log q`: the log never asks `q`.
* `HasHit inPlay log`: some entry, at its input's first occurrence, is answered by a value in play
  before it, `inPlay` giving the values in play after each prefix of the log.

`mem_take_of_inPlay` is what a hit buys: when `inPlay` only grows along the log, a consistent log
with no hit asks every query whose answer is in play after `n` entries within those `n` entries;
a value cannot be used before the query that produces it. `answer_not_mem_inPlay_nil`: no answer
is in play before the first query.

`dedupKeys log` keeps each input of a log at its first occurrence only: the fresh queries of a run
against a lazy random oracle, in order. It is defined for logs of a dependent function, as VCVio's
`QueryLog spec` is. Appending an entry keeps it exactly when its input is new (`dedupKeys_concat`),
the deduplicated prefix of a log is a prefix of the deduplicated log (`take_dedupKeys`), and on a
consistent log it has the log's entries (`mem_dedupKeys_iff`), finds what the log finds
(`findSome?_dedupKeys`), and keeps its collisions (`hasCollision_dedupKeys`). A hit, being at a
first occurrence, survives deduplication when the values in play do (`hasHit_dedupKeys`).
-/

namespace LeanerVM.Protocol.QueryLog

@[expose] public section

variable {Q D : Type}

/-- No input appears in the log with two answers: the log is the trace of a function. -/
def Consistent (log : List ((_ : Q) × D)) : Prop :=
  ∀ e₁ ∈ log, ∀ e₂ ∈ log, e₁.1 = e₂.1 → e₁.2 = e₂.2

/-- A collision: two different inputs of the log with one answer. -/
def HasCollision (log : List ((_ : Q) × D)) : Prop :=
  ∃ e₁ ∈ log, ∃ e₂ ∈ log, e₁.1 ≠ e₂.1 ∧ e₁.2 = e₂.2

/-- A query is fresh with respect to a log when the log never asks it. -/
def Fresh (log : List ((_ : Q) × D)) (q : Q) : Prop := ∀ e ∈ log, e.1 ≠ q

/-- A hit: an entry, at its input's first occurrence, answered by a value in play after the
entries before it. -/
def HasHit (inPlay : List ((_ : Q) × D) → List D) (log : List ((_ : Q) × D)) : Prop :=
  ∃ i : Fin log.length, Fresh (log.take i) log[i].1 ∧ log[i].2 ∈ inPlay (log.take i)

section Decidable

variable [DecidableEq Q] [DecidableEq D]

instance (log : List ((_ : Q) × D)) : Decidable (Consistent log) := by
  unfold Consistent; infer_instance

instance (log : List ((_ : Q) × D)) : Decidable (HasCollision log) := by
  unfold HasCollision; infer_instance

instance (log : List ((_ : Q) × D)) (q : Q) : Decidable (Fresh log q) := by
  unfold Fresh; infer_instance

instance (inPlay : List ((_ : Q) × D) → List D) (log : List ((_ : Q) × D)) :
    Decidable (HasHit inPlay log) := by
  unfold HasHit; infer_instance

end Decidable

/-! ## Consequences -/

/-- A collision in part of a log is one in the log. -/
theorem HasCollision.mono {log log' : List ((_ : Q) × D)} (h : HasCollision log')
    (hsub : ∀ e ∈ log', e ∈ log) : HasCollision log :=
  let ⟨e₁, h₁, e₂, h₂, h⟩ := h
  ⟨e₁, hsub e₁ h₁, e₂, hsub e₂ h₂, h⟩

variable [DecidableEq Q] {inPlay : List ((_ : Q) × D) → List D} {log : List ((_ : Q) × D)}

/-- The first occurrence of a logged input: a position before which the log never asks it, and
at which it is answered as everywhere else in a consistent log. -/
theorem first_occurrence (hcons : Consistent log) {e : (_ : Q) × D} (he : e ∈ log) :
    ∃ (p : ℕ) (hp : p < log.length), Fresh (log.take p) e.1 ∧ log[p] = e := by
  have hp := List.findIdx_lt_length_of_exists (p := fun x ↦ x.1 = e.1) ⟨e, he, by simp⟩
  have hq := of_decide_eq_true (List.findIdx_getElem (w := hp))
  refine ⟨_, hp, fun x hx ↦ ?_, Sigma.ext hq (heq_of_eq (hcons _ (List.getElem_mem _) e he hq))⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
  simpa using List.not_of_lt_findIdx (Nat.lt_min.mp hj).1

/-- In a consistent log with no hit, a logged query whose answer is in play after `n` entries is
asked within them, when `inPlay` grows along the log. -/
theorem mem_take_of_inPlay (hmono : ∀ l₁ l₂, l₁ <+: l₂ → ∀ d ∈ inPlay l₁, d ∈ inPlay l₂)
    (hcons : Consistent log) (hhit : ¬ HasHit inPlay log) {e : (_ : Q) × D} (he : e ∈ log)
    {n : ℕ} (hn : e.2 ∈ inPlay (log.take n)) : e ∈ log.take n := by
  obtain ⟨p, hp, hfresh, rfl⟩ := first_occurrence hcons he
  by_cases hpn : p < n
  · exact List.mem_take_iff_getElem.mpr ⟨p, Nat.lt_min.mpr ⟨hpn, hp⟩, rfl⟩
  · exact absurd ⟨⟨p, hp⟩, hfresh,
      hmono _ _ (List.take_prefix_take_left (Nat.not_lt.mp hpn)) _ hn⟩ hhit

/-- In a consistent log with no hit, no answer is in play before the first query. -/
theorem answer_not_mem_inPlay_nil (hmono : ∀ l₁ l₂, l₁ <+: l₂ → ∀ d ∈ inPlay l₁, d ∈ inPlay l₂)
    (hcons : Consistent log) (hhit : ¬ HasHit inPlay log) {e : (_ : Q) × D} (he : e ∈ log) :
    e.2 ∉ inPlay [] := fun h ↦
  List.not_mem_nil (mem_take_of_inPlay hmono hcons hhit he (n := 0) h)

omit [DecidableEq Q] in
/-- A query is fresh exactly when it is not among the log's inputs. -/
theorem fresh_iff_not_mem_keys {log : List ((_ : Q) × D)} {q : Q} :
    Fresh log q ↔ q ∉ log.map (·.1) := by
  simp [Fresh]

/-! ## Each input at its first occurrence -/

section Dedup

variable {β : Q → Type}

/-- The log with each input kept at its first occurrence only, in order. -/
def dedupKeys (l : List ((q : Q) × β q)) : List ((q : Q) × β q) :=
  l.foldl (fun acc e ↦ if acc.any (fun x ↦ decide (x.1 = e.1)) then acc else acc ++ [e]) []

@[simp]
theorem dedupKeys_nil : dedupKeys ([] : List ((q : Q) × β q)) = [] := rfl

@[simp]
theorem dedupKeys_singleton (e : (q : Q) × β q) : dedupKeys [e] = [e] := rfl

private theorem dedupKeys_concat_any (l : List ((q : Q) × β q)) (e : (q : Q) × β q) :
    dedupKeys (l ++ [e]) =
      if (dedupKeys l).any (fun x ↦ decide (x.1 = e.1)) then dedupKeys l
      else dedupKeys l ++ [e] := by
  unfold dedupKeys
  rw [List.foldl_append]
  rfl

/-- The deduplicated log has the log's inputs. -/
theorem mem_keys_dedupKeys (l : List ((q : Q) × β q)) (q : Q) :
    q ∈ (dedupKeys l).map (·.1) ↔ q ∈ l.map (·.1) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l e ih =>
    rw [dedupKeys_concat_any]
    split
    · rename_i h
      obtain ⟨x, hx, hxe⟩ := by simpa only [List.any_eq_true, decide_eq_true_eq] using h
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton]
      refine ⟨fun hq ↦ .inl (ih.mp hq), ?_⟩
      rintro (hq | rfl)
      · exact ih.mpr hq
      · exact hxe ▸ List.mem_map_of_mem hx
    · simp [ih]

/-- **Appending an entry** keeps it exactly when its input is new. -/
theorem dedupKeys_concat (l : List ((q : Q) × β q)) (e : (q : Q) × β q) :
    dedupKeys (l ++ [e]) = if e.1 ∈ l.map (·.1) then dedupKeys l else dedupKeys l ++ [e] := by
  rw [dedupKeys_concat_any]
  have h : (dedupKeys l).any (fun x ↦ decide (x.1 = e.1)) = decide (e.1 ∈ l.map (·.1)) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq, ← mem_keys_dedupKeys]
    simp only [decide_eq_true_eq, List.mem_map]
  by_cases he : e.1 ∈ l.map (·.1) <;> simp [h, he]

/-- The deduplicated log is a sublist of the log. -/
theorem dedupKeys_sublist (l : List ((q : Q) × β q)) : (dedupKeys l).Sublist l := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l e ih =>
    rw [dedupKeys_concat]
    split
    · exact ih.trans (List.sublist_append_left l [e])
    · exact ih.append (List.Sublist.refl [e])

/-- Each input appears once in the deduplicated log. -/
theorem nodup_keys_dedupKeys (l : List ((q : Q) × β q)) : ((dedupKeys l).map (·.1)).Nodup := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l e ih =>
    rw [dedupKeys_concat]
    split
    · exact ih
    · rename_i h
      rw [List.map_append, List.nodup_append]
      refine ⟨ih, by simp, fun a ha b hb hab ↦ ?_⟩
      obtain rfl : b = e.1 := by simpa using hb
      exact h ((mem_keys_dedupKeys l _).mp (hab ▸ ha))

/-- **Deduplicating an appended log**: the deduplicated first part, then the second part's first
occurrences of inputs the first part does not ask. -/
theorem dedupKeys_append (l₁ l₂ : List ((q : Q) × β q)) :
    dedupKeys (l₁ ++ l₂) =
      dedupKeys l₁ ++ (dedupKeys l₂).filter fun e ↦ decide (e.1 ∉ l₁.map (·.1)) := by
  induction l₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton l₂ e ih =>
    rw [← List.append_assoc, dedupKeys_concat, dedupKeys_concat, ih]
    by_cases h₁ : e.1 ∈ l₁.map (·.1) <;> by_cases h₂ : e.1 ∈ l₂.map (·.1) <;>
      simp [h₁, h₂, List.filter_append]
    · exact List.mem_map.mp h₁
    · have h : ∀ x ∈ l₁, ¬ x.1 = e.1 := fun x hx hx' ↦ h₁ (hx' ▸ List.mem_map_of_mem hx)
      rw [List.filter_cons_of_pos (by simpa using h)]
      rfl

/-- Deduplicating a log with an entry in front. -/
theorem dedupKeys_cons (e : (q : Q) × β q) (l : List ((q : Q) × β q)) :
    dedupKeys (e :: l) = e :: (dedupKeys l).filter fun x ↦ decide (x.1 ≠ e.1) := by
  simpa using dedupKeys_append [e] l

/-- The deduplicated part of a log up to a point is a prefix of the deduplicated log. -/
theorem dedupKeys_take_prefix (l : List ((q : Q) × β q)) (i : ℕ) :
    dedupKeys (l.take i) <+: dedupKeys l := by
  have h := dedupKeys_append (l.take i) (l.drop i)
  rw [List.take_append_drop] at h
  rw [h]
  exact List.prefix_append _ _

/-- The deduplicated part of a log up to a point is the deduplicated log cut at its length. -/
theorem take_dedupKeys (l : List ((q : Q) × β q)) (i : ℕ) :
    (dedupKeys l).take (dedupKeys (l.take i)).length = dedupKeys (l.take i) :=
  (List.prefix_iff_eq_take.mp (dedupKeys_take_prefix l i)).symm

end Dedup

section DedupConsistent

variable {log : List ((_ : Q) × D)}

omit [DecidableEq Q] in
/-- An entry of a consistent log is the entry at its input's first logged occurrence. -/
private theorem eq_of_consistent (hcons : Consistent log) {e x : (_ : Q) × D} (he : e ∈ log)
    (hx : x ∈ log) (h : x.1 = e.1) : x = e :=
  Sigma.ext h (heq_of_eq (hcons x hx e he h))

/-- In a consistent log, every entry is kept by deduplication. -/
theorem mem_dedupKeys_of_mem (hcons : Consistent log) {e : (_ : Q) × D} (he : e ∈ log) :
    e ∈ dedupKeys log := by
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp
    ((mem_keys_dedupKeys log e.1).mpr (List.mem_map_of_mem (f := (·.1)) he))
  rwa [eq_of_consistent hcons he ((dedupKeys_sublist log).subset hx) hxe] at hx

/-- A consistent log and its deduplication have the same entries. -/
theorem mem_dedupKeys_iff (hcons : Consistent log) {e : (_ : Q) × D} :
    e ∈ dedupKeys log ↔ e ∈ log :=
  ⟨fun h ↦ (dedupKeys_sublist log).subset h, mem_dedupKeys_of_mem hcons⟩

omit [DecidableEq Q] in
/-- A consistent log's prefix is consistent. -/
theorem Consistent.of_prefix {log' : List ((_ : Q) × D)} (hcons : Consistent log)
    (h : log' <+: log) : Consistent log' :=
  fun e₁ h₁ e₂ h₂ ↦ hcons e₁ (h.subset h₁) e₂ (h.subset h₂)

/-- A search along a consistent log finds what it finds along the deduplicated log. -/
theorem findSome?_dedupKeys {γ : Type} (hcons : Consistent log)
    (f : (_ : Q) × D → Option γ) : (dedupKeys log).findSome? f = log.findSome? f := by
  induction log using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    have hl := hcons.of_prefix (List.prefix_append l [e])
    rw [dedupKeys_concat]
    split
    · rename_i h
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
      obtain rfl := eq_of_consistent hcons (List.mem_append_right l (List.mem_singleton_self e))
        (List.mem_append_left _ hx) hxe
      rw [ih hl, List.findSome?_append]
      rcases hf : l.findSome? f with _ | y
      · simp [List.findSome?_eq_none_iff.mp hf x hx]
      · rfl
    · rw [List.findSome?_append, List.findSome?_append, ih hl]

/-- A collision of a consistent log is one of its deduplication. -/
theorem hasCollision_dedupKeys (hcons : Consistent log) (h : HasCollision log) :
    HasCollision (dedupKeys log) :=
  let ⟨e₁, h₁, e₂, h₂, h⟩ := h
  ⟨e₁, mem_dedupKeys_of_mem hcons h₁, e₂, mem_dedupKeys_of_mem hcons h₂, h⟩

/-- **A hit survives deduplication**: a hit is at a first occurrence, which deduplication keeps,
and its prefix deduplicates to the prefix of the deduplicated log; so the hit is one of the
deduplicated log when the values in play after each prefix are in play after its deduplication. -/
theorem hasHit_dedupKeys {inPlay : List ((_ : Q) × D) → List D}
    (hplay : ∀ i, ∀ d ∈ inPlay (log.take i), d ∈ inPlay (dedupKeys (log.take i)))
    (h : HasHit inPlay log) : HasHit inPlay (dedupKeys log) := by
  obtain ⟨⟨i, hi⟩, hfresh, hin⟩ := h
  simp only [Fin.getElem_fin] at hfresh hin
  have hcat : dedupKeys (log.take (i + 1)) = dedupKeys (log.take i) ++ [log[i]] := by
    rw [List.take_succ_eq_append_getElem hi, dedupKeys_concat]
    simp only [fresh_iff_not_mem_keys.mp hfresh, ↓reduceIte]
  have hpre := hcat ▸ dedupKeys_take_prefix log (i + 1)
  have hj : (dedupKeys (log.take i)).length < (dedupKeys log).length := by
    have := hpre.length_le
    simp only [List.length_append, List.length_singleton] at this
    omega
  have hget : (dedupKeys log)[(dedupKeys (log.take i)).length] = log[i] := by
    rw [← hpre.getElem (by simp)]
    simp
  refine ⟨⟨_, hj⟩, ?_, ?_⟩
  · simp only [Fin.getElem_fin, take_dedupKeys, hget]
    exact fun e he ↦ hfresh e ((dedupKeys_sublist _).subset he)
  · simp only [Fin.getElem_fin, take_dedupKeys, hget]
    exact hplay i _ hin

end DedupConsistent

end
end LeanerVM.Protocol.QueryLog
