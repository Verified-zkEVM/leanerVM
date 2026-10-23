/-
  LeanerVM.Protocol.ToVCVio.HashChain

  A hash chain read back off a query log: from a state, the unique logged step into it, back to
  the seed. Without a collision the history of an honest chain is its steps, and without a hit it
  is already in the log when a query using the chain's last state is first asked. Candidate for
  VCVio.
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

* `history_of_noCollision_noSeed`: if every step of a chain is logged, the log has no collision, and
  no answer is `seed`, the history of the chain's last state is the chain.
* `history_take_of_noCollision_noHit`: if the log is also consistent and has no hit, the history is
  already in the log before any query that has the chain's last state as a chunk and is not one
  of the chain's own queries; `history_take_of_step` is the case of the chain's next step. A hit
  is read off `inPlay`, the values in play after each prefix of the log, which must grow along the
  log, hold `seed` from the start, and take in the chunks `chunks q` of each query, every state
  being a chunk of the steps from it. The chunks of a query are the values it carries: the
  chaining value of a step, the children of a Merkle node.
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
  | cv, [], x, hx => ⟨0, Nat.le_refl _, (List.mem_singleton.mp hx).symm⟩
  | cv, (b, c) :: steps, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨0, Nat.zero_le _, rfl⟩
    · obtain ⟨j, hj, hlast⟩ := exists_take_of_mem c steps x hx
      exact ⟨j + 1, Nat.succ_le_succ hj, hlast⟩

private theorem unique?_eq_some_iff {α : Type} [DecidableEq α] {l : List α} {x : α} :
    unique? l = some x ↔ x ∈ l ∧ ∀ y ∈ l, y = x := by
  cases l with
  | nil => simp [unique?]
  | cons a rest =>
    simp only [unique?, List.all_eq_true, decide_eq_true_eq, List.mem_cons, forall_eq_or_imp]
    split_ifs with h
    · exact ⟨by rintro ⟨⟩; exact ⟨.inl rfl, rfl, h⟩, fun ⟨_, hax, _⟩ ↦ hax ▸ rfl⟩
    · exact ⟨nofun, fun ⟨_, hax, hall⟩ ↦ (h fun y hy ↦ (hall y hy).trans hax.symm).elim⟩

/-- Every query of a chain starts from the last state of a shorter prefix. -/
private theorem mem_queries (enc : D → B → Q) :
    ∀ (cv : D) (steps : List (B × D)) (e : (_ : Q) × D), e ∈ queries enc cv steps →
      ∃ j < steps.length, ∃ b, e.1 = enc (last cv (steps.take j)) b
  | _, [], _, he => nomatch he
  | cv, (b, c) :: steps, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨0, Nat.zero_lt_succ _, b, rfl⟩
    · obtain ⟨j, hj, b', hb'⟩ := mem_queries enc c steps e he
      exact ⟨j + 1, Nat.succ_lt_succ hj, b', hb'⟩

end Bookkeeping

/-! ## The history of a chain -/

variable {enc : D → B → Q} {step? : Q → Option (D × B)} {log : List ((_ : Q) × D)} {seed : D}

/-- Without a collision, the step a logged query into `cv` parses as is the one step the log
shows into `cv`. -/
private theorem unique?_preimages (hcoll : ¬ HasCollision log) {e : (_ : Q) × D} (he : e ∈ log)
    {cv : D} (hcv : e.2 = cv) {p : D × B} (hp : step? e.1 = some p) :
    unique? (preimages step? log cv) = some p := by
  refine unique?_eq_some_iff.mpr ⟨List.mem_filterMap.mpr ⟨e, he, by simp [hcv, hp]⟩, fun y hy ↦ ?_⟩
  obtain ⟨e', he', hy⟩ := List.mem_filterMap.mp hy
  split_ifs at hy with h
  obtain hq : e'.1 = e.1 := by_contra fun hne ↦ hcoll ⟨e', he', e, he, hne, h.trans hcv.symm⟩
  rw [hq, hp] at hy
  exact (Option.some.inj hy).symm

/-- The walk recovers a logged chain with enough fuel, when the log has no collision and no
answer is `seed`. -/
private theorem walk_last (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hcoll : ¬ HasCollision log) (hseed : ∀ e ∈ log, e.2 ≠ seed) (steps : List (B × D)) :
    (∀ e ∈ queries enc seed steps, e ∈ log) → ∀ fuel, steps.length ≤ fuel →
      walk step? log seed fuel (last seed steps) = some steps := by
  induction steps using List.reverseRecOn with
  | nil => rintro - (_ | _) - <;> simp [walk, last]
  | append_singleton init x ih =>
    obtain ⟨b, cv⟩ := x
    rintro hchain (_ | f) hlen
    · simp at hlen
    rw [queries_append] at hchain
    have hmem := hchain ⟨enc (last seed init) b, cv⟩ (by simp)
    simp only [walk, last_append, hseed _ hmem, ↓reduceIte,
      unique?_preimages hcoll hmem rfl (henc _ _),
      ih (fun e he ↦ hchain e (List.mem_append_left _ he)) f (by simpa using hlen), Option.map_some]

/-- Two prefixes of a logged chain that end in one state have one length, when the log has no
collision and no answer is `seed`. -/
private theorem min_eq_of_last_take_eq (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hcoll : ¬ HasCollision log) (hseed : ∀ e ∈ log, e.2 ≠ seed) (steps : List (B × D))
    (hchain : ∀ e ∈ queries enc seed steps, e ∈ log) {j k : ℕ}
    (h : last seed (steps.take j) = last seed (steps.take k)) :
    min j steps.length = min k steps.length := by
  have hw i := walk_last henc hcoll hseed (steps.take i)
    (fun e he ↦ hchain e (List.mem_of_mem_take (queries_take enc seed steps i ▸ he)))
    steps.length (List.length_take_le' _ _)
  have hj := hw j
  rw [h, hw k, Option.some.injEq] at hj
  simpa using congrArg List.length hj.symm

/-- The states of a logged chain are distinct, when the log has no collision and no answer is
`seed`. -/
private theorem nodup_states (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hcoll : ¬ HasCollision log) (hseed : ∀ e ∈ log, e.2 ≠ seed) (steps : List (B × D))
    (hchain : ∀ e ∈ queries enc seed steps, e ∈ log) : (seed :: steps.map (·.2)).Nodup := by
  induction steps using List.reverseRecOn with
  | nil => exact List.nodup_singleton _
  | append_singleton init x ih =>
    obtain ⟨b, cv⟩ := x
    rw [List.map_append, ← List.cons_append, List.nodup_append]
    refine ⟨ih fun e he ↦ hchain e (by rw [queries_append]; exact List.mem_append_left _ he),
      List.nodup_singleton _, fun x hx y hy hxy ↦ ?_⟩
    obtain rfl := List.mem_singleton.mp hy
    obtain ⟨j, hj, rfl⟩ := exists_take_of_mem seed init x hx
    have := min_eq_of_last_take_eq henc hcoll hseed _ hchain (k := (init ++ [(b, y)]).length)
      (by rwa [List.take_append_of_le_length hj, List.take_length, last_append])
    simp at this
    omega

/-- **The history of a logged chain.** If every step of a chain from `seed` is in the log, the log
has no collision, and no answer is `seed`, then the history of the chain's last state is the
chain. -/
theorem history_of_noCollision_noSeed (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hcoll : ¬ HasCollision log) (hseed : ∀ e ∈ log, e.2 ≠ seed) (steps : List (B × D))
    (hchain : ∀ e ∈ queries enc seed steps, e ∈ log) :
    history step? log seed (last seed steps) = some steps := by
  refine walk_last henc hcoll hseed steps hchain _ ?_
  have hsub : steps.map (·.2) ⊆ log.map (·.2) :=
    map_snd_queries enc seed steps ▸ List.map_subset _ hchain
  simpa using ((nodup_states henc hcoll hseed steps hchain).of_cons.subperm hsub).length_le

variable [DecidableEq Q] {chunks : Q → List D} {inPlay : List ((_ : Q) × D) → List D}

omit [DecidableEq D] [DecidableEq B] in
/-- With no hit, every query of a logged chain whose last state is in play after `n` entries is
asked within them. -/
private theorem queries_mem_take (hchunk : ∀ d b, d ∈ chunks (enc d b))
    (hplay : ∀ l e, ∀ d ∈ chunks e.1, d ∈ inPlay (l ++ [e]))
    (hmono : ∀ l₁ l₂, l₁ <+: l₂ → ∀ d ∈ inPlay l₁, d ∈ inPlay l₂) (hcons : Consistent log)
    (hhit : ¬ HasHit inPlay log) (steps : List (B × D)) :
    (∀ e ∈ queries enc seed steps, e ∈ log) → ∀ n, last seed steps ∈ inPlay (log.take n) →
      ∀ e ∈ queries enc seed steps, e ∈ log.take n := by
  induction steps using List.reverseRecOn with
  | nil => simp [queries]
  | append_singleton init x ih =>
    obtain ⟨b, cv⟩ := x
    intro hchain n hn e he
    rw [queries_append] at hchain he
    rw [last_append] at hn
    have hlast :=
      mem_take_of_inPlay hmono hcons hhit (hchain ⟨enc (last seed init) b, cv⟩ (by simp)) hn
    obtain ⟨p, hp, hpe⟩ := List.mem_take_iff_getElem.mp hlast
    have hinit : last seed init ∈ inPlay (log.take (p + 1)) := by
      rw [List.take_succ_eq_append_getElem (Nat.lt_min.mp hp).2]
      exact hplay _ _ _ (hpe ▸ hchunk _ _)
    rcases List.mem_append.mp he with he | he
    · obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.mp
        (ih (fun e he ↦ hchain e (List.mem_append_left _ he)) (p + 1) hinit e he)
      exact List.mem_take_iff_getElem.mpr ⟨i, by omega, rfl⟩
    · rwa [List.mem_singleton.mp he]

/-- **The history before a query.** Let a log be consistent, with no collision and no hit, where
the values in play grow along the log, start with `seed`, and take in the chunks of each query,
every state being a chunk of the steps from it. If every step of a chain from `seed` is in the
log, then at a position whose query has the chain's last state as a chunk and is none of the
chain's own queries, the history of the last state in the entries before it is the chain. -/
theorem history_take_of_noCollision_noHit (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hchunk : ∀ d b, d ∈ chunks (enc d b))
    (hplay : ∀ l e, ∀ d ∈ chunks e.1, d ∈ inPlay (l ++ [e]))
    (hmono : ∀ l₁ l₂, l₁ <+: l₂ → ∀ d ∈ inPlay l₁, d ∈ inPlay l₂) (hseed : seed ∈ inPlay [])
    (hcons : Consistent log) (hcoll : ¬ HasCollision log) (hhit : ¬ HasHit inPlay log)
    (steps : List (B × D)) (hchain : ∀ e ∈ queries enc seed steps, e ∈ log) {m : ℕ}
    (hm : m < log.length) (hq : last seed steps ∈ chunks log[m].1)
    (hnew : ∀ e ∈ queries enc seed steps, e.1 ≠ log[m].1) :
    history step? (log.take m) seed (last seed steps) = some steps := by
  have htake := List.take_succ_eq_append_getElem hm
  have hin := queries_mem_take hchunk hplay hmono hcons hhit steps hchain (m + 1)
    (htake ▸ hplay _ _ _ hq)
  refine history_of_noCollision_noSeed henc
    (fun h ↦ hcoll (h.mono fun e he ↦ List.mem_of_mem_take he))
    (fun e he h ↦ answer_not_mem_inPlay_nil hmono hcons hhit (List.mem_of_mem_take he)
      (h ▸ hseed)) steps fun e he ↦ ?_
  rcases List.mem_append.mp (htake ▸ hin e he) with h | h
  · exact h
  · exact absurd (by rw [List.mem_singleton.mp h]) (hnew e he)

/-- **The history before the next step.** Under the hypotheses of
`history_take_of_noCollision_noHit`, at a position where the chain's next step is asked, the
history of the chain's last state in the entries before it is the chain. -/
theorem history_take_of_step (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hchunk : ∀ d b, d ∈ chunks (enc d b))
    (hplay : ∀ l e, ∀ d ∈ chunks e.1, d ∈ inPlay (l ++ [e]))
    (hmono : ∀ l₁ l₂, l₁ <+: l₂ → ∀ d ∈ inPlay l₁, d ∈ inPlay l₂) (hseed : seed ∈ inPlay [])
    (hcons : Consistent log) (hcoll : ¬ HasCollision log) (hhit : ¬ HasHit inPlay log)
    (steps : List (B × D)) (hchain : ∀ e ∈ queries enc seed steps, e ∈ log) {m : ℕ}
    (hm : m < log.length) {b : B} (hq : log[m].1 = enc (last seed steps) b) :
    history step? (log.take m) seed (last seed steps) = some steps := by
  refine history_take_of_noCollision_noHit henc hchunk hplay hmono hseed hcons hcoll hhit steps
    hchain hm (hq ▸ hchunk _ _) fun e he heq ↦ ?_
  -- the query would start from the last state of a shorter prefix
  obtain ⟨j, hj, b', hde⟩ := mem_queries enc seed steps e he
  have h' := congrArg step? (hde.symm.trans (heq.trans hq))
  simp only [henc, Option.some.injEq, Prod.mk.injEq] at h'
  have := min_eq_of_last_take_eq henc hcoll
    (fun e he h ↦ answer_not_mem_inPlay_nil hmono hcons hhit he (h ▸ hseed)) steps hchain
    (j := j) (k := steps.length) (by rw [List.take_length]; exact h'.1)
  simp at this
  omega

omit [DecidableEq Q] in
/-- A walk found in part of a log is found in the whole log with more fuel, when the whole log has
no collision. -/
private theorem walk_mono {log' : List ((_ : Q) × D)} (hcoll : ¬ HasCollision log)
    (hsub : ∀ e ∈ log', e ∈ log) :
    ∀ (fuel fuel' : ℕ) (cv : D) (hs : List (B × D)), fuel ≤ fuel' →
      walk step? log' seed fuel cv = some hs → walk step? log seed fuel' cv = some hs
  | 0, fuel', cv, hs, _, h => by cases fuel' <;> by_cases cv = seed <;> simp_all [walk]
  | _ + 1, 0, _, _, hle, _ => absurd hle (by omega)
  | fuel + 1, fuel' + 1, cv, hs, hle, h => by
    unfold walk at h ⊢
    split_ifs at h ⊢ with hcv
    · exact h
    rcases hu : unique? (preimages step? log' cv) with _ | ⟨cv', b⟩ <;> rw [hu] at h
    · cases h
    obtain ⟨hs', hw, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨e, he, hp⟩ := List.mem_filterMap.mp (unique?_eq_some_iff.mp hu).1
    split_ifs at hp with hecv
    simp only [unique?_preimages hcoll (hsub e he) hecv hp,
      walk_mono hcoll hsub fuel fuel' cv' hs' (by omega) hw, Option.map_some]

omit [DecidableEq Q] in
/-- **Histories are determined.** Without a collision in the log, a history found in the log's
first `k` entries is the history in the whole log. -/
theorem history_determined (hcoll : ¬ HasCollision log) {k : ℕ} {cv : D} {hs : List (B × D)}
    (h : history step? (log.take k) seed cv = some hs) : history step? log seed cv = some hs :=
  walk_mono hcoll (fun _ he ↦ List.mem_of_mem_take he) _ _ cv hs
    (by rw [List.length_take]; exact Nat.min_le_right _ _) h

end
end LeanerVM.Protocol.HashChain
