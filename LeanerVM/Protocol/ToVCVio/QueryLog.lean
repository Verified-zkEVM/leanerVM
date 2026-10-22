/-
  LeanerVM.Protocol.ToVCVio.QueryLog

  What a finite log of queries to one function shows: whether it is the trace of a function,
  whether it has a collision, which queries are fresh, which digests are in play, and whether a
  fresh answer hits one of them. Candidate for VCVio.
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
* `Known chunks roots log d`: `d` is one of `roots`, or a chunk of a logged input, where `chunks q`
  lists the digests an input carries (the children of a Merkle node, the chaining value of a
  chain step).
* `HasHit chunks roots log`: some entry, at its input's first occurrence, is answered by a digest
  known from the entries before it.

`mem_take_of_chunk` is what the last two buy: in a consistent log with no hit, a query whose answer
is a chunk of the input at position `r` was asked before `r`, unless it is that input. A digest
cannot be used before the query that produces it. `answer_not_mem_roots`: no answer is a root.
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

/-- A digest is known from a log when it is one of `roots` or a chunk of a logged input. -/
def Known (chunks : Q → List D) (roots : List D) (log : List ((_ : Q) × D)) (d : D) : Prop :=
  d ∈ roots ∨ ∃ e ∈ log, d ∈ chunks e.1

/-- A hit: an entry, at its input's first occurrence, answered by a digest known from the entries
before it. -/
def HasHit (chunks : Q → List D) (roots : List D) (log : List ((_ : Q) × D)) : Prop :=
  ∃ i : Fin log.length, Fresh (log.take i) log[i].1 ∧ Known chunks roots (log.take i) log[i].2

section Decidable

variable [DecidableEq Q] [DecidableEq D]

instance (log : List ((_ : Q) × D)) : Decidable (Consistent log) := by
  unfold Consistent; infer_instance

instance (log : List ((_ : Q) × D)) : Decidable (HasCollision log) := by
  unfold HasCollision; infer_instance

instance (log : List ((_ : Q) × D)) (q : Q) : Decidable (Fresh log q) := by
  unfold Fresh; infer_instance

instance (chunks : Q → List D) (roots : List D) (log : List ((_ : Q) × D)) (d : D) :
    Decidable (Known chunks roots log d) := by
  unfold Known; infer_instance

instance (chunks : Q → List D) (roots : List D) (log : List ((_ : Q) × D)) :
    Decidable (HasHit chunks roots log) := by
  unfold HasHit; infer_instance

end Decidable

/-! ## Consequences -/

/-- A collision in part of a log is one in the log. -/
theorem HasCollision.mono {log log' : List ((_ : Q) × D)} (h : HasCollision log')
    (hsub : ∀ e ∈ log', e ∈ log) : HasCollision log := by
  obtain ⟨e₁, h₁, e₂, h₂, hne, heq⟩ := h
  exact ⟨e₁, hsub e₁ h₁, e₂, hsub e₂ h₂, hne, heq⟩

/-- The first occurrence of a logged input: a position before which the log never asks it, and
at which it is answered as everywhere else in a consistent log. -/
private theorem first_occurrence [DecidableEq Q] {log : List ((_ : Q) × D)}
    (hcons : Consistent log) {e : (_ : Q) × D} (he : e ∈ log) :
    ∃ (p : ℕ) (hp : p < log.length), Fresh (log.take p) e.1 ∧ log[p] = e := by
  have hex : ∃ x ∈ log, decide (x.1 = e.1) = true := ⟨e, he, by simp⟩
  refine ⟨log.findIdx (fun x ↦ decide (x.1 = e.1)), List.findIdx_lt_length_of_exists hex,
    ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    rw [List.length_take] at hj
    rw [List.getElem_take]
    have := List.not_of_lt_findIdx (Nat.lt_min.mp hj).1
    simpa using this
  · have hp := List.findIdx_getElem (w := List.findIdx_lt_length_of_exists hex)
    simp only [decide_eq_true_eq] at hp
    exact Sigma.ext hp (heq_of_eq (hcons _ (List.getElem_mem _) e he hp))

/-- An entry at a position before `r` is in the log's first `r` entries. -/
private theorem getElem_mem_take {log : List ((_ : Q) × D)} {p r : ℕ} (hp : p < log.length)
    (hpr : p < r) : log[p] ∈ log.take r :=
  List.mem_iff_getElem.mpr ⟨p, by rw [List.length_take]; exact Nat.lt_min.mpr ⟨hpr, hp⟩,
    by simp⟩

variable [DecidableEq Q] {chunks : Q → List D} {roots : List D} {log : List ((_ : Q) × D)}

/-- In a consistent log with no hit, no answer is one of the roots. -/
theorem answer_not_mem_roots (hcons : Consistent log) (hhit : ¬ HasHit chunks roots log)
    {e : (_ : Q) × D} (he : e ∈ log) : e.2 ∉ roots := by
  intro hr
  obtain ⟨p, hp, hfresh, he'⟩ := first_occurrence hcons he
  exact hhit ⟨⟨p, hp⟩, by simp only [Fin.getElem_fin, he']; exact hfresh,
    by simp only [Fin.getElem_fin, he']; exact Or.inl hr⟩

/-- In a consistent log with no hit, a query answered by a chunk of the input at position `r` is
asked before `r`, unless it is that input. -/
theorem mem_take_of_chunk (hcons : Consistent log) (hhit : ¬ HasHit chunks roots log)
    {e : (_ : Q) × D} (he : e ∈ log) {r : ℕ} (hr : r < log.length) (hne : log[r].1 ≠ e.1)
    (hk : e.2 ∈ chunks log[r].1) : e ∈ log.take r := by
  obtain ⟨p, hp, hfresh, he'⟩ := first_occurrence hcons he
  have hpr : p ≠ r := fun h ↦ hne (by subst h; rw [he'])
  rcases Nat.lt_or_gt_of_ne hpr with hlt | hgt
  · rw [← he']
    exact getElem_mem_take hp hlt
  · refine absurd ⟨⟨p, hp⟩, by simp only [Fin.getElem_fin, he']; exact hfresh,
      Or.inr ⟨log[r], getElem_mem_take hr hgt, by simp only [Fin.getElem_fin, he']; exact hk⟩⟩ hhit

end
end LeanerVM.Protocol.QueryLog
