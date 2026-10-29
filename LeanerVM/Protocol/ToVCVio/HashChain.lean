/-
  LeanerVM.Protocol.ToVCVio.HashChain

  A hash chain read back off a query log: from a state, the unique logged step into it, back to a
  start. Without a collision the history of an honest chain is its steps, and without a hit it is
  already in the log when a query using the chain's last state is first asked. Candidate for
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
`enc cv b`, whose answer is the next state. A chain from `start` is a list of steps, each block
with the state it leads to; `queries enc start steps` are its log entries and `last start steps`
the state it ends in. `step?` parses a query back into a state and a block, and only
`step? (enc d b) = some (d, b)` is asked of it: other queries of the same length (a Merkle node,
say) may parse too, and are only more entries of the log.

`history step? log isStart cv` walks back from `cv`: at a state `isStart` holds of it stops, with
that start and the steps it passed; at any other state the parses of the logged queries answered
by it must agree, and the walk moves to the parsed state. It returns `none` when a step is missing
or ambiguous, or after as many steps as the log has entries. The start test comes first: a start
whose own query parses as a step is still where the walk stops. A chain from one fixed `seed` is
read with `isSeed seed`.

* `history_of_noCollision`: if every step of a chain from a start is logged, the log has no
  collision, and no later state of the chain is a start, the history of the chain's last state is
  the chain; `history_of_noCollision_noSeed` is the case of one seed that answers no query.
* `history_take_of_noCollision_noHit`: if the log is also consistent and has no hit, the history is
  already in the log before any query that has the chain's last state as a chunk and is not one
  of the chain's own queries; `history_take_of_step` is the case of the chain's next step. A hit
  is read off `inPlay`, the values in play after each prefix of the log, which must grow along the
  log and take in the chunks `chunks q` of each query, every state being a chunk of the steps from
  it. The chunks of a query are the values it carries: the chaining value of a step, the children
  of a Merkle node.
* `history_take_of_mem_inPlay`: under the same hypotheses, the history of a chain whose last state
  is in play after `m` entries is already in those `m` entries.
* `history_determined`: without a collision, a history found in part of a log is the history in the
  whole log.
* `start_of_history`, `step_of_history`: a history starts at a start and ends in the state it was
  read from, and every step of it is a logged entry, answered by the step's state, whose query
  parses as the step from the state before. `history_eq_none`: a state that is no start and that
  no logged step leads to has no history.
* `history_append_of_not_start`: a new entry whose answer no logged step starts from leaves the
  history of every other state unchanged, under start tests that agree off that answer.
* `history_dedupKeys`: in a consistent log, a history is that of the log with each input at its
  first occurrence only.

What each hypothesis excludes: a collision makes a step ambiguous; a later state that is a start
cuts the history short; a state produced after a query that uses it puts the history after that
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

/-- The start test of the one start `seed`. -/
def isSeed (seed : D) (d : D) : Bool := decide (d = seed)

/-- The walk back from `cv` in at most `fuel` steps: it stops at a start, tested first, and from
any other state moves to the unique step the log shows into it; the start and the steps passed, in
chain order. -/
def walk (step? : Q → Option (D × B)) (log : List ((_ : Q) × D)) (isStart : D → Bool) :
    ℕ → D → Option (D × List (B × D))
  | 0, cv => if isStart cv then some (cv, []) else none
  | fuel + 1, cv =>
    if isStart cv then some (cv, []) else
      match unique? (preimages step? log cv) with
      | some (cv', b) => (walk step? log isStart fuel cv').map fun p ↦ (p.1, p.2 ++ [(b, cv)])
      | none => none

/-- The history of `cv` in a log: the start and the chain from it the log shows into `cv`, each
block with the state it leads to; `none` when a step on the way is missing or ambiguous, or the
walk is longer than the log. -/
def history (step? : Q → Option (D × B)) (log : List ((_ : Q) × D)) (isStart : D → Bool) (cv : D) :
    Option (D × List (B × D)) :=
  walk step? log isStart log.length cv

/-! ## Chain bookkeeping -/

section Bookkeeping

omit [DecidableEq D] [DecidableEq B]

/-- The queries of two chains in sequence: the first's, then the second's from its last state. -/
theorem queries_append (enc : D → B → Q) :
    ∀ (cv : D) (s₁ s₂ : List (B × D)),
      queries enc cv (s₁ ++ s₂) = queries enc cv s₁ ++ queries enc (last cv s₁) s₂
  | _, [], _ => rfl
  | _, (_, c) :: s₁, s₂ => by
    simp only [List.cons_append, queries, last, queries_append enc c s₁ s₂]

/-- The last state of two chains in sequence: the second's, from the first's. -/
theorem last_append : ∀ (cv : D) (s₁ s₂ : List (B × D)), last cv (s₁ ++ s₂) = last (last cv s₁) s₂
  | _, [], _ => rfl
  | _, (_, c) :: s₁, s₂ => last_append c s₁ s₂

private theorem queries_take (enc : D → B → Q) :
    ∀ (cv : D) (steps : List (B × D)) (j : ℕ),
      queries enc cv (steps.take j) = (queries enc cv steps).take j
  | _, [], _ => by simp [queries]
  | _, _ :: _, 0 => rfl
  | _, (_, c) :: steps, j + 1 => by
    simp only [List.take_succ_cons, queries, queries_take enc c steps j]

/-- The answers of a chain's queries are the states it leads to. -/
theorem map_snd_queries (enc : D → B → Q) :
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

/-- Every state a logged chain leads to is a logged answer. -/
theorem answer_of_mem_states {enc : D → B → Q} {log : List ((_ : Q) × D)} {cv : D}
    {steps : List (B × D)} (hchain : ∀ e ∈ queries enc cv steps, e ∈ log) {x : D}
    (hx : x ∈ steps.map (·.2)) : ∃ e ∈ log, e.2 = x := by
  rw [← map_snd_queries enc cv steps] at hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact ⟨e, hchain e he, rfl⟩

end Bookkeeping

/-! ## The history of a chain -/

variable {enc : D → B → Q} {step? : Q → Option (D × B)} {log : List ((_ : Q) × D)}
  {isStart : D → Bool}

/-- The one start of `isSeed seed` is `seed`. -/
@[simp] theorem isSeed_eq_true {seed d : D} : isSeed seed d = true ↔ d = seed := by
  simp [isSeed]

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

/-- The walk recovers a logged chain from a start with enough fuel, when the log has no collision
and no later state of the chain is a start. -/
private theorem walk_last (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hcoll : ¬ HasCollision log) {start : D} (hstart : isStart start = true)
    (steps : List (B × D)) :
    (∀ x ∈ steps.map (·.2), isStart x = false) → (∀ e ∈ queries enc start steps, e ∈ log) →
      ∀ fuel, steps.length ≤ fuel →
        walk step? log isStart fuel (last start steps) = some (start, steps) := by
  induction steps using List.reverseRecOn with
  | nil => rintro - - (_ | _) - <;> simp [walk, last, hstart]
  | append_singleton init x ih =>
    obtain ⟨b, cv⟩ := x
    rintro hlater hchain (_ | f) hlen
    · simp at hlen
    rw [queries_append] at hchain
    have hmem := hchain ⟨enc (last start init) b, cv⟩ (by simp [queries])
    have hcv : isStart cv = false := hlater cv (by simp)
    simp only [walk, last_append, last, hcv, Bool.false_eq_true, ↓reduceIte,
      unique?_preimages hcoll hmem rfl (henc _ _),
      ih (fun y hy ↦ hlater y (by simp only [List.map_append, List.mem_append]; exact .inl hy))
        (fun e he ↦ hchain e (List.mem_append_left _ he)) f (by simpa using hlen), Option.map_some]

/-- Two prefixes of a logged chain that end in one state have one length, when the log has no
collision and no later state of the chain is a start. -/
private theorem min_eq_of_last_take_eq (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hcoll : ¬ HasCollision log) {start : D} (hstart : isStart start = true)
    (steps : List (B × D)) (hlater : ∀ x ∈ steps.map (·.2), isStart x = false)
    (hchain : ∀ e ∈ queries enc start steps, e ∈ log) {j k : ℕ}
    (h : last start (steps.take j) = last start (steps.take k)) :
    min j steps.length = min k steps.length := by
  have hw i := walk_last henc hcoll hstart (steps.take i)
    (fun x hx ↦ hlater x (List.map_subset _ (List.take_subset _ _) hx))
    (fun e he ↦ hchain e (List.mem_of_mem_take (queries_take enc start steps i ▸ he)))
    steps.length (List.length_take_le' _ _)
  have hj := hw j
  rw [h, hw k, Option.some.injEq] at hj
  simpa using congrArg (fun p ↦ p.2.length) hj.symm

/-- The states of a logged chain are distinct, when the log has no collision and no later state of
the chain is a start. -/
private theorem nodup_states (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hcoll : ¬ HasCollision log) {start : D} (hstart : isStart start = true)
    (steps : List (B × D)) (hlater : ∀ x ∈ steps.map (·.2), isStart x = false)
    (hchain : ∀ e ∈ queries enc start steps, e ∈ log) : (start :: steps.map (·.2)).Nodup := by
  induction steps using List.reverseRecOn with
  | nil => exact List.nodup_singleton _
  | append_singleton init x ih =>
    obtain ⟨b, cv⟩ := x
    rw [List.map_append, ← List.cons_append, List.nodup_append]
    refine ⟨ih
      (fun y hy ↦ hlater y (by simp only [List.map_append, List.mem_append]; exact .inl hy))
      fun e he ↦ hchain e (by rw [queries_append]; exact List.mem_append_left _ he),
      List.nodup_singleton _, fun x hx y hy hxy ↦ ?_⟩
    obtain rfl := List.mem_singleton.mp hy
    obtain ⟨j, hj, rfl⟩ := exists_take_of_mem start init x hx
    have := min_eq_of_last_take_eq henc hcoll hstart _ hlater hchain
      (k := (init ++ [(b, y)]).length)
      (by rw [List.take_append_of_le_length hj, List.take_length, last_append]; simpa only [last])
    simp at this
    omega

/-- **The history of a logged chain.** If every step of a chain from a start is in the log, the
log has no collision, and no later state of the chain is a start, then the history of the chain's
last state is the chain, from that start. -/
theorem history_of_noCollision (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hcoll : ¬ HasCollision log) {start : D} (hstart : isStart start = true)
    (steps : List (B × D)) (hlater : ∀ x ∈ steps.map (·.2), isStart x = false)
    (hchain : ∀ e ∈ queries enc start steps, e ∈ log) :
    history step? log isStart (last start steps) = some (start, steps) := by
  refine walk_last henc hcoll hstart steps hlater hchain _ ?_
  have hsub : steps.map (·.2) ⊆ log.map (·.2) :=
    map_snd_queries enc start steps ▸ List.map_subset _ hchain
  simpa using
    ((nodup_states henc hcoll hstart steps hlater hchain).of_cons.subperm hsub).length_le

/-- **The history of a logged chain from a seed.** If every step of a chain from `seed` is in the
log, the log has no collision, and no answer is `seed`, then the history of the chain's last state
is the chain. -/
theorem history_of_noCollision_noSeed (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hcoll : ¬ HasCollision log) {seed : D} (hseed : ∀ e ∈ log, e.2 ≠ seed)
    (steps : List (B × D)) (hchain : ∀ e ∈ queries enc seed steps, e ∈ log) :
    history step? log (isSeed seed) (last seed steps) = some (seed, steps) :=
  history_of_noCollision henc hcoll (by simp) steps (fun x hx ↦ by
    obtain ⟨e, he, rfl⟩ := answer_of_mem_states hchain hx
    simpa [isSeed] using hseed e he) hchain

variable [DecidableEq Q] {chunks : Q → List D} {inPlay : List ((_ : Q) × D) → List D}

omit [DecidableEq D] [DecidableEq B] in
/-- With no hit, every query of a logged chain whose last state is in play after `n` entries is
asked within them. -/
private theorem queries_mem_take (hchunk : ∀ d b, d ∈ chunks (enc d b))
    (hplay : ∀ l e, ∀ d ∈ chunks e.1, d ∈ inPlay (l ++ [e]))
    (hmono : ∀ l₁ l₂, l₁ <+: l₂ → ∀ d ∈ inPlay l₁, d ∈ inPlay l₂) (hcons : Consistent log)
    (hhit : ¬ HasHit inPlay log) {start : D} (steps : List (B × D)) :
    (∀ e ∈ queries enc start steps, e ∈ log) → ∀ n, last start steps ∈ inPlay (log.take n) →
      ∀ e ∈ queries enc start steps, e ∈ log.take n := by
  induction steps using List.reverseRecOn with
  | nil => simp [queries]
  | append_singleton init x ih =>
    obtain ⟨b, cv⟩ := x
    intro hchain n hn e he
    rw [queries_append] at hchain he
    simp only [last_append, last] at hn
    have hlast :=
      mem_take_of_inPlay hmono hcons hhit (hchain ⟨enc (last start init) b, cv⟩ (by simp [queries]))
        hn
    obtain ⟨p, hp, hpe⟩ := List.mem_take_iff_getElem.mp hlast
    have hinit : last start init ∈ inPlay (log.take (p + 1)) := by
      rw [List.take_succ_eq_append_getElem (Nat.lt_min.mp hp).2]
      exact hplay _ _ _ (hpe ▸ hchunk _ _)
    rcases List.mem_append.mp he with he | he
    · obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.mp
        (ih (fun e he ↦ hchain e (List.mem_append_left _ he)) (p + 1) hinit e he)
      exact List.mem_take_iff_getElem.mpr ⟨i, by omega, rfl⟩
    · rwa [List.mem_singleton.mp he]

/-- **The history before a query.** Let a log be consistent, with no collision and no hit, where
the values in play grow along the log and take in the chunks of each query, every state being a
chunk of the steps from it. If every step of a chain from a start is in the log and no later state
of the chain is a start, then at a position whose query has the chain's last state as a chunk and
is none of the chain's own queries, the history of the last state in the entries before it is the
chain. -/
theorem history_take_of_noCollision_noHit (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hchunk : ∀ d b, d ∈ chunks (enc d b))
    (hplay : ∀ l e, ∀ d ∈ chunks e.1, d ∈ inPlay (l ++ [e]))
    (hmono : ∀ l₁ l₂, l₁ <+: l₂ → ∀ d ∈ inPlay l₁, d ∈ inPlay l₂)
    (hcons : Consistent log) (hcoll : ¬ HasCollision log) (hhit : ¬ HasHit inPlay log)
    {start : D} (hstart : isStart start = true) (steps : List (B × D))
    (hlater : ∀ x ∈ steps.map (·.2), isStart x = false)
    (hchain : ∀ e ∈ queries enc start steps, e ∈ log) {m : ℕ}
    (hm : m < log.length) (hq : last start steps ∈ chunks log[m].1)
    (hnew : ∀ e ∈ queries enc start steps, e.1 ≠ log[m].1) :
    history step? (log.take m) isStart (last start steps) = some (start, steps) := by
  have htake := List.take_succ_eq_append_getElem hm
  have hin := queries_mem_take hchunk hplay hmono hcons hhit steps hchain (m + 1)
    (htake ▸ hplay _ _ _ hq)
  refine history_of_noCollision henc
    (fun h ↦ hcoll (h.mono fun e he ↦ List.mem_of_mem_take he)) hstart steps hlater fun e he ↦ ?_
  rcases List.mem_append.mp (htake ▸ hin e he) with h | h
  · exact h
  · exact absurd (by rw [List.mem_singleton.mp h]) (hnew e he)

/-- **The history before the next step.** Under the hypotheses of
`history_take_of_noCollision_noHit`, at a position where the chain's next step is asked, the
history of the chain's last state in the entries before it is the chain. -/
theorem history_take_of_step (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hchunk : ∀ d b, d ∈ chunks (enc d b))
    (hplay : ∀ l e, ∀ d ∈ chunks e.1, d ∈ inPlay (l ++ [e]))
    (hmono : ∀ l₁ l₂, l₁ <+: l₂ → ∀ d ∈ inPlay l₁, d ∈ inPlay l₂)
    (hcons : Consistent log) (hcoll : ¬ HasCollision log) (hhit : ¬ HasHit inPlay log)
    {start : D} (hstart : isStart start = true) (steps : List (B × D))
    (hlater : ∀ x ∈ steps.map (·.2), isStart x = false)
    (hchain : ∀ e ∈ queries enc start steps, e ∈ log) {m : ℕ}
    (hm : m < log.length) {b : B} (hq : log[m].1 = enc (last start steps) b) :
    history step? (log.take m) isStart (last start steps) = some (start, steps) := by
  refine history_take_of_noCollision_noHit henc hchunk hplay hmono hcons hcoll hhit hstart steps
    hlater hchain hm (hq ▸ hchunk _ _) fun e he heq ↦ ?_
  -- the query would start from the last state of a shorter prefix
  obtain ⟨j, hj, b', hde⟩ := mem_queries enc start steps e he
  have h' := congrArg step? (hde.symm.trans (heq.trans hq))
  simp only [henc, Option.some.injEq, Prod.mk.injEq] at h'
  have := min_eq_of_last_take_eq henc hcoll hstart steps hlater hchain
    (j := j) (k := steps.length) (by rw [List.take_length]; exact h'.1)
  simp at this
  omega

/-- **The history before a state is in play.** Under the hypotheses of
`history_take_of_noCollision_noHit`, if the chain's last state is in play after the first `m`
entries, its history in those entries is the chain. -/
theorem history_take_of_mem_inPlay (henc : ∀ d b, step? (enc d b) = some (d, b))
    (hchunk : ∀ d b, d ∈ chunks (enc d b))
    (hplay : ∀ l e, ∀ d ∈ chunks e.1, d ∈ inPlay (l ++ [e]))
    (hmono : ∀ l₁ l₂, l₁ <+: l₂ → ∀ d ∈ inPlay l₁, d ∈ inPlay l₂)
    (hcons : Consistent log) (hcoll : ¬ HasCollision log) (hhit : ¬ HasHit inPlay log)
    {start : D} (hstart : isStart start = true) (steps : List (B × D))
    (hlater : ∀ x ∈ steps.map (·.2), isStart x = false)
    (hchain : ∀ e ∈ queries enc start steps, e ∈ log) {m : ℕ}
    (hq : last start steps ∈ inPlay (log.take m)) :
    history step? (log.take m) isStart (last start steps) = some (start, steps) :=
  history_of_noCollision henc (fun h ↦ hcoll (h.mono fun _ he ↦ List.mem_of_mem_take he)) hstart
    steps hlater (queries_mem_take hchunk hplay hmono hcons hhit steps hchain m hq)

omit [DecidableEq Q] in
/-- A walk found in part of a log is found in the whole log with more fuel, when the whole log has
no collision. -/
private theorem walk_mono {log' : List ((_ : Q) × D)} (hcoll : ¬ HasCollision log)
    (hsub : ∀ e ∈ log', e ∈ log) :
    ∀ (fuel fuel' : ℕ) (cv : D) (hs : D × List (B × D)), fuel ≤ fuel' →
      walk step? log' isStart fuel cv = some hs → walk step? log isStart fuel' cv = some hs
  | 0, fuel', cv, hs, _, h => by cases fuel' <;> by_cases isStart cv <;> simp_all [walk]
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
theorem history_determined (hcoll : ¬ HasCollision log) {k : ℕ} {cv : D}
    {hs : D × List (B × D)} (h : history step? (log.take k) isStart cv = some hs) :
    history step? log isStart cv = some hs :=
  walk_mono hcoll (fun _ he ↦ List.mem_of_mem_take he) _ _ cv hs
    (by rw [List.length_take]; exact Nat.min_le_right _ _) h

/-! ## Walks with any fuel -/

section Fuel

omit [DecidableEq Q]

/-- A successful walk stops at a start, or steps back from another state to the unique step the
log shows into it. -/
private theorem walk_eq_some {f : ℕ} {cv σ : D} {hs : List (B × D)}
    (h : walk step? log isStart f cv = some (σ, hs)) :
    (isStart cv = true ∧ σ = cv ∧ hs = []) ∨ ∃ g cv' b hs', f = g + 1 ∧ isStart cv = false ∧
      unique? (preimages step? log cv) = some (cv', b) ∧
      walk step? log isStart g cv' = some (σ, hs') ∧ hs = hs' ++ [(b, cv)] := by
  cases f <;> unfold walk at h <;> split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
    exact .inl ⟨‹_›, rfl, rfl⟩
  · cases h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
    exact .inl ⟨‹_›, rfl, rfl⟩
  · split at h
    · obtain ⟨⟨σ', hs'⟩, hw, hp⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      exact .inr ⟨_, _, _, hs', rfl, Bool.eq_false_iff.mpr ‹_›, ‹_›, hw, rfl⟩
    · cases h

/-- A successful walk stops at a start. -/
private theorem start_of_walk {f : ℕ} {cv σ : D} {hs : List (B × D)}
    (h : walk step? log isStart f cv = some (σ, hs)) : isStart σ = true := by
  rcases walk_eq_some h with ⟨hcv, rfl, -⟩ | ⟨_, _, _, _, -, -, -, hw, -⟩
  · exact hcv
  · exact start_of_walk hw
termination_by f

/-- The state a successful walk ends in is the state it started from. -/
private theorem last_of_walk {f : ℕ} {cv σ : D} {hs : List (B × D)}
    (h : walk step? log isStart f cv = some (σ, hs)) : last σ hs = cv := by
  rcases walk_eq_some h with ⟨-, rfl, rfl⟩ | ⟨_, _, _, _, -, -, -, -, rfl⟩
  · rfl
  · rw [last_append]
    rfl

/-- A successful walk passes at most as many steps as its fuel. -/
private theorem length_le_of_walk {f : ℕ} {cv σ : D} {hs : List (B × D)}
    (h : walk step? log isStart f cv = some (σ, hs)) : hs.length ≤ f := by
  rcases walk_eq_some h with ⟨-, -, rfl⟩ | ⟨g, _, _, _, rfl, -, -, hw, rfl⟩
  · simp
  · simpa using length_le_of_walk hw
termination_by f

/-- A successful walk succeeds, with the same steps, with any fuel at least its length. -/
private theorem walk_of_length_le {f f' : ℕ} {cv σ : D} {hs : List (B × D)}
    (h : walk step? log isStart f cv = some (σ, hs)) (hle : hs.length ≤ f') :
    walk step? log isStart f' cv = some (σ, hs) := by
  rcases walk_eq_some h with ⟨hcv, rfl, rfl⟩ | ⟨g, cv', b, hs', rfl, hcv, hu, hw, rfl⟩
  · cases f' <;> simp [walk, hcv]
  · cases f' with
    | zero => simp at hle
    | succ f' =>
      simp only [List.length_append, List.length_singleton, Nat.add_le_add_iff_right] at hle
      simp only [walk, hcv, Bool.false_eq_true, ↓reduceIte, hu, walk_of_length_le hw hle,
        Option.map_some]
termination_by f

/-- The walk from a state a successful walk passes is the walk's prefix up to it. -/
private theorem walk_take {f : ℕ} {cv σ : D} {hs : List (B × D)}
    (h : walk step? log isStart f cv = some (σ, hs)) (j : ℕ) (hj : j ≤ hs.length) :
    walk step? log isStart f (last σ (hs.take j)) = some (σ, hs.take j) := by
  rcases walk_eq_some h with ⟨hcv, rfl, rfl⟩ | ⟨g, _, _, hs', rfl, -, -, hw, rfl⟩
  · obtain rfl : j = 0 := by simpa using hj
    cases f <;> simp [walk, last, hcv]
  · by_cases hjs : j ≤ hs'.length
    · rw [List.take_append_of_le_length hjs]
      exact walk_of_length_le (walk_take hw j hjs)
        (Nat.le_trans (List.length_take_le _ _) (by have := length_le_of_walk hw; omega))
    · rw [List.take_of_length_le (by simp at hj ⊢; omega), last_of_walk h]
      exact h
termination_by f

/-- The states a successful walk passes are distinct. -/
private theorem nodup_of_walk {f : ℕ} {cv σ : D} {hs : List (B × D)}
    (h : walk step? log isStart f cv = some (σ, hs)) : (σ :: hs.map (·.2)).Nodup := by
  rcases walk_eq_some h with ⟨-, -, rfl⟩ | ⟨g, _, _, hs', rfl, -, -, hw, rfl⟩
  · simp
  · rw [List.map_append, ← List.cons_append, List.nodup_append]
    refine ⟨nodup_of_walk hw, by simp, fun x hx y hy hxy ↦ ?_⟩
    obtain rfl : y = cv := by simpa using hy
    subst hxy
    obtain ⟨j, hj, hlast⟩ := exists_take_of_mem σ hs' x hx
    have := walk_of_length_le (hlast ▸ walk_take hw j hj) (f' := g + 1)
      (Nat.le_trans (List.length_take_le _ _) (by have := length_le_of_walk hw; omega))
    rw [h] at this
    have := congrArg (fun p ↦ p.2.length) (Option.some.inj this)
    simp at this
    omega
termination_by f

/-- Every state but the start that a successful walk passes is a logged answer. -/
private theorem answered_of_walk {f : ℕ} {cv σ : D} {hs : List (B × D)}
    (h : walk step? log isStart f cv = some (σ, hs)) :
    ∀ x ∈ hs.map (·.2), ∃ e ∈ log, e.2 = x := by
  rcases walk_eq_some h with ⟨-, -, rfl⟩ | ⟨g, _, _, hs', rfl, -, hu, hw, rfl⟩
  · simp
  · intro x hx
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact answered_of_walk hw x hx
    · obtain ⟨e, he, hp⟩ := List.mem_filterMap.mp (unique?_eq_some_iff.mp hu).1
      split at hp
      · exact ⟨e, he, by assumption⟩
      · cases hp
termination_by f

/-- A successful walk passes at most as many steps as the log has entries. -/
private theorem length_le_length_of_walk {f : ℕ} {cv σ : D} {hs : List (B × D)}
    (h : walk step? log isStart f cv = some (σ, hs)) : hs.length ≤ log.length := by
  have hsub : hs.map (·.2) ⊆ log.map (·.2) := fun x hx ↦ by
    obtain ⟨e, he, rfl⟩ := answered_of_walk h x hx
    exact List.mem_map_of_mem he
  simpa using ((nodup_of_walk h).of_cons.subperm hsub).length_le

/-- A successful walk, with any fuel, is the history. -/
private theorem history_of_walk {f : ℕ} {cv σ : D} {hs : List (B × D)}
    (h : walk step? log isStart f cv = some (σ, hs)) :
    history step? log isStart cv = some (σ, hs) :=
  walk_of_length_le h (length_le_length_of_walk h)

/-- Every step a successful walk passes is a logged entry answered by the step's state, whose
query parses as the step from the state before. -/
private theorem step_of_walk {f : ℕ} {cv σ : D} {hs : List (B × D)}
    (h : walk step? log isStart f cv = some (σ, hs)) (j : ℕ) (hj : j < hs.length) :
    ∃ e ∈ log, e.2 = hs[j].2 ∧ step? e.1 = some (last σ (hs.take j), hs[j].1) := by
  rcases walk_eq_some h with ⟨-, -, rfl⟩ | ⟨g, _, _, hs', rfl, -, hu, hw, rfl⟩
  · simp at hj
  · by_cases hjs : j < hs'.length
    · obtain ⟨e, he, h₁, h₂⟩ := step_of_walk hw j hjs
      refine ⟨e, he, ?_, ?_⟩
      · rw [h₁, List.getElem_append_left hjs]
      · rw [h₂, List.take_append_of_le_length (Nat.le_of_lt hjs), List.getElem_append_left hjs]
    · obtain rfl : j = hs'.length := by simp at hj; omega
      obtain ⟨e, he, hp⟩ := List.mem_filterMap.mp (unique?_eq_some_iff.mp hu).1
      split at hp
      · rename_i hecv
        refine ⟨e, he, by simpa using hecv, ?_⟩
        simp only [List.take_left', List.getElem_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem_cons_zero, last_of_walk hw]
        exact hp
      · cases hp
termination_by f

/-- **A history runs from a start to its state**: it starts at a start, and the chain from that
start ends in the state it was read from. -/
theorem start_of_history {cv σ : D} {hs : List (B × D)}
    (h : history step? log isStart cv = some (σ, hs)) : isStart σ = true ∧ last σ hs = cv :=
  ⟨start_of_walk h, last_of_walk h⟩

/-- **The steps of a history are logged**: step `j` of a history is a logged entry answered by
its state, whose query parses as the step from the state before it. -/
theorem step_of_history {cv σ : D} {hs : List (B × D)}
    (h : history step? log isStart cv = some (σ, hs)) (j : ℕ) (hj : j < hs.length) :
    ∃ e ∈ log, e.2 = hs[j].2 ∧ step? e.1 = some (last σ (hs.take j), hs[j].1) :=
  step_of_walk h j hj

/-- **No start, no step, no history**: a state that is no start and that no logged step leads to
has no history. -/
theorem history_eq_none {cv : D} (hcv : isStart cv = false)
    (hpre : preimages step? log cv = []) : history step? log isStart cv = none := by
  unfold history
  cases log.length <;> simp [walk, hcv, hpre, unique?]

/-- Lists with the same elements have the same unique element. -/
private theorem unique?_congr {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : unique? l₁ = unique? l₂ :=
  Option.ext fun x ↦ by simp only [unique?_eq_some_iff, h]

/-- Walks on two logs, with two start tests, agree when the logs show the same steps into every
state but `avoid`, the tests agree off `avoid`, and no step shown into another state starts from
`avoid`. -/
private theorem walk_congr {log' : List ((_ : Q) × D)} {isStart' : D → Bool} (avoid : D)
    (hpre : ∀ x, x ≠ avoid → ∀ p, p ∈ preimages step? log x ↔ p ∈ preimages step? log' x)
    (hfrom : ∀ x, x ≠ avoid → ∀ p ∈ preimages step? log x, p.1 ≠ avoid)
    (hst : ∀ x, x ≠ avoid → isStart x = isStart' x) :
    ∀ (f : ℕ) (cv : D), cv ≠ avoid →
      walk step? log isStart f cv = walk step? log' isStart' f cv
  | 0, cv, hcv => by simp only [walk, hst cv hcv]
  | f + 1, cv, hcv => by
    simp only [walk, hst cv hcv]
    split
    · rfl
    · rw [← unique?_congr (hpre cv hcv)]
      rcases hu : unique? (preimages step? log cv) with _ | ⟨cv', b⟩
      · rfl
      · simp only
        rw [walk_congr avoid hpre hfrom hst f cv'
          (hfrom cv hcv (cv', b) (unique?_eq_some_iff.mp hu).1)]

/-- Logs and start tests on which every walk from `cv` agrees give `cv` one history. -/
private theorem history_congr {log' : List ((_ : Q) × D)} {isStart' : D → Bool} {cv : D}
    (hw : ∀ f, walk step? log isStart f cv = walk step? log' isStart' f cv) :
    history step? log isStart cv = history step? log' isStart' cv := by
  cases h : history step? log isStart cv with
  | some hs => exact (history_of_walk ((hw _).symm.trans h)).symm
  | none =>
    cases h' : history step? log' isStart' cv with
    | none => rfl
    | some hs => cases h.symm.trans (history_of_walk ((hw _).trans h'))

end Fuel

/-! ## The history after one more entry, and after deduplication -/

omit [DecidableEq Q] in
/-- **One more entry.** If no logged step starts from the new entry's answer, and the start tests
before and after the entry agree off that answer, the history of every other state is unchanged by
the entry. -/
theorem history_append_of_not_start {e : (_ : Q) × D} {isStart' : D → Bool}
    (hfrom : ∀ e' ∈ log, ∀ p, step? e'.1 = some p → p.1 ≠ e.2)
    (hst : ∀ x, x ≠ e.2 → isStart' x = isStart x) {cv : D} (hcv : cv ≠ e.2) :
    history step? (log ++ [e]) isStart' cv = history step? log isStart cv := by
  have hpre : ∀ x, x ≠ e.2 → ∀ p,
      p ∈ preimages step? log x ↔ p ∈ preimages step? (log ++ [e]) x := fun x hx p ↦ by
    simp [preimages, List.filterMap_append, Ne.symm hx]
  have hfr : ∀ x, x ≠ e.2 → ∀ p ∈ preimages step? log x, p.1 ≠ e.2 := fun x _ p hp ↦ by
    obtain ⟨e', he', hp⟩ := List.mem_filterMap.mp hp
    split at hp
    · exact hfrom e' he' p hp
    · cases hp
  exact history_congr fun f ↦
    (walk_congr e.2 hpre hfr (fun x hx ↦ (hst x hx).symm) f cv hcv).symm

/-- **Deduplication.** In a consistent log, every history is that of the log with each input at
its first occurrence only. -/
theorem history_dedupKeys (hcons : Consistent log) (cv : D) :
    history step? (List.dedupKeys log) isStart cv = history step? log isStart cv := by
  have hpre : ∀ x p, p ∈ preimages step? (List.dedupKeys log) x ↔ p ∈ preimages step? log x :=
    fun x p ↦ by simp only [preimages, List.mem_filterMap, mem_dedupKeys_iff hcons]
  refine history_congr fun f ↦ ?_
  induction f generalizing cv with
  | zero => rfl
  | succ f ih => simp only [walk, ih, unique?_congr (hpre cv)]

end
end LeanerVM.Protocol.HashChain
