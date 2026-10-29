/-
  LeanerVM.Protocol.ToVCVio.QueryLog

  What a finite log of queries to one function shows: whether it is the trace of a function,
  whether it has a collision, which queries are fresh, and whether a fresh answer hits a value
  already in play. Candidate for VCVio.
-/

module

public import Mathlib.Data.Nat.Notation

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
private theorem first_occurrence (hcons : Consistent log) {e : (_ : Q) × D} (he : e ∈ log) :
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

end
end LeanerVM.Protocol.QueryLog
