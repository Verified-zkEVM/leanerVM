/-
  LeanerVM.Protocol.ToVCVio.HashChain

  A hash chain read back off a query log: from a state, the unique logged step into it, back to
  the seed. Without a collision the history of an honest chain is its steps, and without a hit it
  is already in the log when the chain's next query is first asked. Candidate for VCVio.
-/

module

public import LeanerVM.Protocol.ToVCVio.QueryLog
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm

/-!
# Hash chains read off a query log

A hash chain has states `D` and blocks `B`: from the state `cv`, absorbing `b` is the query
`enc cv b`, whose answer is the next state. A chain from `seed` is a list of steps, each block with
the state it leads to; `queries enc seed steps` are its log entries and `last seed steps` the state
it ends in. `step?` parses a query back into a state and a block, and only
`step? (enc d b) = some (d, b)` is asked of it: other queries of the same length (a Merkle node,
say) may parse too, and are only more entries of the log.

`history step? log seed cv` walks back from `cv`: at a state other than `seed`, the parses of the
logged queries answered by it must agree, and the walk moves to the parsed state; it stops at
`seed` with the steps it passed, and returns `none` when a step is missing or ambiguous, or after
as many steps as the log has entries.

* `history_of_noCollision_noHit`: if every step of a chain is logged, the log has no collision, and
  no answer is `seed`, the history of the chain's last state is the chain.
* `history_take_of_noCollision_noHit`: if the log is also consistent and has no hit (an answer equal
  to a root or to a chunk of an earlier input, with `seed` a root and every state a chunk of the
  queries it starts), then the history is already in the log before the chain's next query is
  first asked.
* `history_determined`: without a collision, a history found in part of a log is the history in the
  whole log.

What each hypothesis excludes: a collision makes a step ambiguous; an answer equal to `seed` cuts
the history short; a state produced after a query that uses it puts the history after that
query.
-/

namespace LeanerVM.Protocol.HashChain

open QueryLog

@[expose] public section

variable {Q D B : Type}

/-! ## Chains -/

/-- The log entries of a chain from `cv`: each step's query `enc cv b`, answered by the state it
leads to. -/
def queries (enc : D → B → Q) : D → List (B × D) → List ((_ : Q) × D)
  | _, [] => []
  | cv, (b, cv') :: steps => ⟨enc cv b, cv'⟩ :: queries enc cv' steps

/-- The state a chain from `cv` ends in. -/
def last : D → List (B × D) → D
  | cv, [] => cv
  | _, (_, cv') :: steps => last cv' steps

/-- The element of a list all of whose elements are equal; `none` for the empty list and for a
list with two different elements. -/
def unique? {α : Type} [DecidableEq α] : List α → Option α
  | [] => none
  | x :: rest => if rest.all (· = x) then some x else none

/-- The steps the log shows into `cv`: the parses of the logged queries answered by `cv`. -/
def preimages [DecidableEq D] (step? : Q → Option (D × B)) (log : List ((_ : Q) × D)) (cv : D) :
    List (D × B) :=
  log.filterMap fun e ↦ if e.2 = cv then step? e.1 else none

variable [DecidableEq D] [DecidableEq B]

/-- The walk back from `cv` to `seed` in at most `fuel` steps, each the unique step the log shows
into the current state; the steps passed, in chain order. -/
def walk (step? : Q → Option (D × B)) (log : List ((_ : Q) × D)) (seed : D) :
    ℕ → D → Option (List (B × D))
  | 0, cv => if cv = seed then some [] else none
  | fuel + 1, cv =>
    if cv = seed then some [] else
      match unique? (preimages step? log cv) with
      | some (cv', b) => (walk step? log seed fuel cv').map (· ++ [(b, cv)])
      | none => none

/-- The history of `cv` in a log: the chain from `seed` the log shows into `cv`, each block with
the state it leads to; `none` when a step on the way is missing or ambiguous, or the walk is longer
than the log. -/
def history (step? : Q → Option (D × B)) (log : List ((_ : Q) × D)) (seed cv : D) :
    Option (List (B × D)) :=
  walk step? log seed log.length cv

/-! ## Chain bookkeeping -/

section Bookkeeping

omit [DecidableEq D] [DecidableEq B]

private theorem queries_append (enc : D → B → Q) (b : B) (cv' : D) :
    ∀ (cv : D) (init : List (B × D)),
      queries enc cv (init ++ [(b, cv')]) = queries enc cv init ++ [⟨enc (last cv init) b, cv'⟩]
  | _, [] => rfl
  | _, (_, c) :: init => by
    simp only [List.cons_append, queries, last, queries_append enc b cv' c init]

private theorem last_append (b : B) (cv' : D) :
    ∀ (cv : D) (init : List (B × D)), last cv (init ++ [(b, cv')]) = cv'
  | _, [] => rfl
  | _, (_, c) :: init => last_append b cv' c init

private theorem queries_take (enc : D → B → Q) :
    ∀ (cv : D) (steps : List (B × D)) (j : ℕ),
      queries enc cv (steps.take j) = (queries enc cv steps).take j
  | _, [], _ => by simp [queries]
  | _, _ :: _, 0 => rfl
  | _, (_, c) :: steps, j + 1 => by
    simp only [List.take_succ_cons, queries, queries_take enc c steps j]

private theorem map_snd_queries (enc : D → B → Q) :
    ∀ (cv : D) (steps : List (B × D)),
      (queries enc cv steps).map (·.2) = steps.map (·.2)
  | _, [] => rfl
  | _, (_, c) :: steps => by
    simp only [queries, List.map_cons, map_snd_queries enc c steps]

/-- Every state a chain passes through, the start included, is the last state of a prefix. -/
private theorem exists_take_of_mem :
    ∀ (cv : D) (steps : List (B × D)) (x : D), x ∈ cv :: steps.map (·.2) →
      ∃ j ≤ steps.length, last cv (steps.take j) = x
  | cv, [], x, hx => ⟨0, Nat.le_refl _, by simpa [last] using (List.mem_singleton.mp hx).symm⟩
  | cv, (b, c) :: steps, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨0, Nat.zero_le _, rfl⟩
    · obtain ⟨j, hj, hlast⟩ := exists_take_of_mem c steps x hx
      exact ⟨j + 1, by simp [hj], by simpa [last] using hlast⟩

/-- The last state of a chain is one of its states. -/
private theorem last_mem : ∀ (cv : D) (steps : List (B × D)), last cv steps ∈ cv :: steps.map (·.2)
  | _, [] => List.mem_singleton_self _
  | _, (_, c) :: steps => List.mem_cons_of_mem _ (last_mem c steps)

private theorem unique?_eq_some_iff {α : Type} [DecidableEq α] {l : List α} {x : α} :
    unique? l = some x ↔ x ∈ l ∧ ∀ y ∈ l, y = x := by
  cases l with
  | nil => simp [unique?]
  | cons a rest =>
    simp only [unique?]
    split
    · rename_i h
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      simp only [Option.some.injEq, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro rfl
        exact ⟨Or.inl rfl, rfl, h⟩
      · rintro ⟨-, rfl, -⟩
        rfl
    · rename_i h
      simp only [List.all_eq_true, decide_eq_true_eq, not_forall] at h
      obtain ⟨y, hy, hne⟩ := h
      simp only [reduceCtorEq, false_iff, not_and, List.mem_cons, forall_eq_or_imp]
      rintro - rfl hall
      exact hne (hall y hy)

end Bookkeeping

/-! ## The history of a chain -/

variable {enc : D → B → Q} {step? : Q → Option (D × B)} {log : List ((_ : Q) × D)} {seed : D}

/-- The walk recovers a logged chain with enough fuel, when the log has no collision and no
answer is `seed`. -/
private theorem walk_last (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hcoll : ¬ HasCollision log) (hseed : ∀ e ∈ log, e.2 ≠ seed) (steps : List (B × D)) :
    (∀ e ∈ queries enc seed steps, e ∈ log) → ∀ fuel, steps.length ≤ fuel →
      walk step? log seed fuel (last seed steps) = some steps := by
  induction steps using List.reverseRecOn with
  | nil =>
    intro _ fuel _
    cases fuel <;> simp [walk, last]
  | append_singleton init x ih =>
    obtain ⟨b, cv⟩ := x
    intro hchain fuel hlen
    rw [queries_append] at hchain
    rw [last_append]
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    have hmem : (⟨enc (last seed init) b, cv⟩ : (_ : Q) × D) ∈ log := hchain _ (by simp)
    have hpre : unique? (preimages step? log cv) = some (last seed init, b) := by
      rw [unique?_eq_some_iff]
      refine ⟨List.mem_filterMap.mpr ⟨_, hmem, by simp [henc]⟩, fun y hy ↦ ?_⟩
      obtain ⟨e, he, hy⟩ := List.mem_filterMap.mp hy
      by_cases hcv : e.2 = cv
      · have hq : e.1 = enc (last seed init) b := by
          by_contra hne
          exact hcoll ⟨e, he, _, hmem, hne, hcv⟩
        simp only [hcv, ↓reduceIte, hq, henc, Option.some.injEq] at hy
        exact hy.symm
      · simp [hcv] at hy
    simp only [walk, hseed _ hmem, ↓reduceIte, hpre]
    rw [ih (fun e he ↦ hchain e (List.mem_append_left _ he)) f (by simp at hlen; omega)]
    rfl

/-- The states of a logged chain are distinct, when the log has no collision and no answer is
`seed`. -/
private theorem nodup_states (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hcoll : ¬ HasCollision log) (hseed : ∀ e ∈ log, e.2 ≠ seed) (steps : List (B × D))
    (hchain : ∀ e ∈ queries enc seed steps, e ∈ log) : (seed :: steps.map (·.2)).Nodup := by
  induction steps using List.reverseRecOn with
  | nil => exact List.nodup_singleton _
  | append_singleton init x ih =>
    obtain ⟨b, cv⟩ := x
    have hinit : ∀ e ∈ queries enc seed init, e ∈ log := fun e he ↦
      hchain e (by rw [queries_append]; exact List.mem_append_left _ he)
    rw [List.map_append, ← List.cons_append, List.nodup_append]
    refine ⟨ih hinit, List.nodup_singleton _, fun x hx y hy hxy ↦ ?_⟩
    obtain rfl : cv = y := (List.mem_singleton.mp hy).symm
    obtain ⟨j, hj, hlast⟩ := exists_take_of_mem seed init x hx
    have h1 := walk_last henc hcoll hseed (init.take j)
      (fun e he ↦ hinit e (by rw [queries_take] at he; exact List.mem_of_mem_take he))
      (init.length + 1) (by rw [List.length_take]; omega)
    have h2 := walk_last henc hcoll hseed (init ++ [(b, cv)]) hchain (init.length + 1) (by simp)
    rw [last_append, ← hxy, ← hlast, h1, Option.some.injEq] at h2
    have := congrArg List.length h2
    simp at this
    omega

/-- **The history of a logged chain.** If every step of a chain from `seed` is in the log, the log
has no collision, and no answer is `seed`, then the history of the chain's last state is the
chain. -/
theorem history_of_noCollision_noHit (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hcoll : ¬ HasCollision log) (hseed : ∀ e ∈ log, e.2 ≠ seed) (steps : List (B × D))
    (hchain : ∀ e ∈ queries enc seed steps, e ∈ log) :
    history step? log seed (last seed steps) = some steps := by
  refine walk_last henc hcoll hseed steps hchain _ ?_
  have hnd := (nodup_states henc hcoll hseed steps hchain).of_cons
  have hsub : steps.map (·.2) ⊆ log.map (·.2) := by
    intro x hx
    rw [← map_snd_queries enc seed steps] at hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map_of_mem (hchain e he)
  simpa using (List.Nodup.subperm hnd hsub).length_le

variable [DecidableEq Q] {chunks : Q → List D} {roots : List D}

/-- **The history before the next query.** If every step of a chain from `seed` is in a
consistent log with no collision and no hit, with `seed` a root and every state a chunk of the
queries that start from it, then at a position where the chain's next query is asked, the history
of the chain's last state in the entries before it is the chain. -/
theorem history_take_of_noCollision_noHit (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hchunk : ∀ d b, d ∈ chunks (enc d b)) (hcons : Consistent log)
    (hcoll : ¬ HasCollision log) (hhit : ¬ HasHit chunks roots log) (hseed : seed ∈ roots)
    (steps : List (B × D)) (hchain : ∀ e ∈ queries enc seed steps, e ∈ log) {m : ℕ}
    (hm : m < log.length) {b : B} (hq : log[m].1 = enc (last seed steps) b) :
    history step? (log.take m) seed (last seed steps) = some steps := by
  have hns : ∀ e ∈ log, e.2 ≠ seed := fun e he h ↦
    answer_not_mem_roots hcons hhit he (h ▸ hseed)
  have hin : ∀ (steps : List (B × D)), (∀ e ∈ queries enc seed steps, e ∈ log) →
      ∀ (r : ℕ) (hr : r < log.length) (b : B), log[r].1 = enc (last seed steps) b →
        ∀ e ∈ queries enc seed steps, e ∈ log.take r := by
    intro steps
    induction steps using List.reverseRecOn with
    | nil => intro _ _ _ _ _ e he; simp [queries] at he
    | append_singleton init x ih =>
      obtain ⟨b', cv⟩ := x
      intro hchain r hr b hq e he
      have hnd := nodup_states henc hcoll hns _ hchain
      rw [queries_append] at hchain he
      rw [last_append] at hq
      have hmem : (⟨enc (last seed init) b', cv⟩ : (_ : Q) × D) ∈ log := hchain _ (by simp)
      have hne : log[r].1 ≠ enc (last seed init) b' := by
        intro h
        rw [hq] at h
        have h' := congrArg step? h
        simp only [henc, Option.some.injEq, Prod.mk.injEq] at h'
        rw [List.map_append, ← List.cons_append, List.nodup_append] at hnd
        exact hnd.2.2 _ (h'.1 ▸ last_mem seed init) cv (by simp) rfl
      have hlast := mem_take_of_chunk hcons hhit hmem hr hne (by rw [hq]; exact hchunk cv b)
      obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp hlast
      rw [List.length_take] at hp
      have hpr : p < r := (Nat.lt_min.mp hp).1
      have hpl : p < log.length := (Nat.lt_min.mp hp).2
      rw [List.getElem_take] at hpe
      rcases List.mem_append.mp he with he | he
      · have := ih (fun e he ↦ hchain e (List.mem_append_left _ he)) p hpl b'
          (by rw [hpe]) e he
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp this
        rw [List.length_take] at hi
        rw [List.getElem_take]
        exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
      · obtain rfl := List.mem_singleton.mp he
        exact hlast
  refine history_of_noCollision_noHit henc
    (fun h ↦ hcoll (h.mono fun e he ↦ List.mem_of_mem_take he))
    (fun e he ↦ hns e (List.mem_of_mem_take he)) steps (hin steps hchain m hm b hq)

/-- A walk found in part of a log is found in the whole log with more fuel, when the whole log has
no collision. -/
private theorem walk_mono {log' : List ((_ : Q) × D)} (hcoll : ¬ HasCollision log)
    (hsub : ∀ e ∈ log', e ∈ log) :
    ∀ (fuel fuel' : ℕ) (cv : D) (hs : List (B × D)), fuel ≤ fuel' →
      walk step? log' seed fuel cv = some hs → walk step? log seed fuel' cv = some hs
  | 0, fuel', cv, hs, _, h => by
    by_cases hcv : cv = seed
    · cases fuel' <;> simp_all [walk]
    · simp [walk, hcv] at h
  | fuel + 1, fuel', cv, hs, hle, h => by
    obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
    by_cases hcv : cv = seed
    · simp_all [walk]
    simp only [walk, hcv, ↓reduceIte] at h ⊢
    split at h
    · rename_i cv' b hu
      obtain ⟨hs', hw, rfl⟩ := Option.map_eq_some_iff.mp h
      have hu' : unique? (preimages step? log cv) = some (cv', b) := by
        obtain ⟨hmem, -⟩ := unique?_eq_some_iff.mp hu
        obtain ⟨e₀, he₀, hp₀⟩ := List.mem_filterMap.mp hmem
        have hcv₀ : e₀.2 = cv := by by_contra hne; simp [hne] at hp₀
        simp only [hcv₀, ↓reduceIte] at hp₀
        refine unique?_eq_some_iff.mpr
          ⟨List.mem_filterMap.mpr ⟨e₀, hsub e₀ he₀, by simp [hcv₀, hp₀]⟩, fun y hy ↦ ?_⟩
        obtain ⟨e, he, hy⟩ := List.mem_filterMap.mp hy
        by_cases hecv : e.2 = cv
        · have hq : e.1 = e₀.1 := by
            by_contra hne
            exact hcoll ⟨e, he, e₀, hsub e₀ he₀, hne, hecv.trans hcv₀.symm⟩
          simp only [hecv, ↓reduceIte, hq, hp₀, Option.some.injEq] at hy
          exact hy.symm
        · simp [hecv] at hy
      simp only [hu', walk_mono hcoll hsub fuel f' cv' hs' (by omega) hw, Option.map_some]
    · cases h

/-- **Histories are determined.** Without a collision in the log, a history found in the log's
first `k` entries is the history in the whole log. -/
theorem history_determined (hcoll : ¬ HasCollision log) {k : ℕ} {cv : D} {hs : List (B × D)}
    (h : history step? (log.take k) seed cv = some hs) : history step? log seed cv = some hs :=
  walk_mono hcoll (fun _ he ↦ List.mem_of_mem_take he) _ _ cv hs
    (by rw [List.length_take]; exact Nat.min_le_right _ _) h

end
end LeanerVM.Protocol.HashChain
