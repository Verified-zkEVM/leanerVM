/-
  LeanerVM.Semantics.Walk

  A balanced multiset of transitions of a partial function contains a walk from the start to
  the end: the Euler-walk argument of a functional graph.
-/

module

public import Mathlib.Data.List.Perm.Basic

@[expose] public section

/-!
# Walks in a balanced functional graph

The combinatorial core of specification Proposition 6.1 (`doc/leanvm/body/06-bus-interactions.tex:9`
at leanVM pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`), for a deterministic transition: the
edges of the graph are `v → f v` for the states `v` of a list `E`, each `f v` defined, and the
multiset of their targets together with a start `s` is the multiset of their sources together
with an end `t`. Then `f` walks from `s` to `t` in at most `|E|` steps, each from a state of
`E` (`exists_walksIn`). Category A: no source is transcribed.

The proof follows the walk: if `s = t` it is empty; otherwise `s` is a source, so `s ∈ E`, and
removing one occurrence of `s` from `E` and of `f s` from the targets leaves a balanced graph
from `f s` to `t` with one edge fewer. The remaining edges, which the walk does not use, form
closed walks; nothing is claimed about them.

`WalksIn f E n s t` says `f` walks from `s` to `t` in `n` steps, each taken from a state of `E`.

The module names no leanVM object: it is list combinatorics, a candidate for Mathlib's
`List.Perm` and graph-walk lemmas, kept here until it is proposed upstream.
-/

namespace LeanerVM.Semantics

variable {V : Type}

/-- `f` walks from `s` to `t` in `n` steps, each taken from a state of `E`. -/
def WalksIn (f : V → Option V) (E : List V) : ℕ → V → V → Prop
  | 0, s, t => s = t
  | n + 1, s, t => s ∈ E ∧ ∃ s', f s = some s' ∧ WalksIn f E n s' t

/-- A walk in a list is a walk in any list containing it. -/
theorem WalksIn.mono {f : V → Option V} {E E' : List V} (hE : E ⊆ E') :
    ∀ {n s t}, WalksIn f E n s t → WalksIn f E' n s t
  | 0, _, _, h => h
  | _ + 1, _, _, ⟨hs, s', hf, h⟩ => ⟨hE hs, s', hf, h.mono hE⟩

/-- In a balanced graph of transitions of `f` from the states of `E`, with a start `s` among the
targets and an end `t` among the sources, `f` walks from `s` to `t` in at most `|E|` steps,
each taken from a state of `E`. -/
theorem exists_walksIn [DecidableEq V] {f : V → Option V} :
    ∀ {E : List V} {s t : V}, (s :: E.filterMap f).Perm (t :: E) → (∀ v ∈ E, f v ≠ none) →
      ∃ n ≤ E.length, WalksIn f E n s t := by
  intro E
  induction hlen : E.length using Nat.strongRecOn generalizing E with
  | _ len ih =>
    intro s t hbal hE
    by_cases hst : s = t
    · exact ⟨0, Nat.zero_le _, hst⟩
    have hs : s ∈ E := (List.mem_cons.mp (hbal.subset List.mem_cons_self)).resolve_left hst
    obtain ⟨s', hs'⟩ := Option.ne_none_iff_exists'.mp (hE s hs)
    have hperm : E.Perm (s :: E.erase s) := List.perm_cons_erase hs
    have hbal' : (s' :: (E.erase s).filterMap f).Perm (t :: E.erase s) := by
      have h1 := hperm.filterMap f
      rw [List.filterMap_cons_some hs'] at h1
      exact (List.perm_cons s).mp
        ((h1.cons s).symm.trans (hbal.trans ((hperm.cons t).trans (List.Perm.swap s t _))))
    have hlt : (E.erase s).length < len := by
      rw [List.length_erase_of_mem hs, ← hlen]
      exact Nat.sub_lt (List.length_pos_of_mem hs) Nat.one_pos
    obtain ⟨n, hn, hw⟩ := ih _ hlt rfl hbal' fun v hv ↦ hE v (List.mem_of_mem_erase hv)
    refine ⟨n + 1, ?_, hs, s', hs', hw.mono fun v hv ↦ List.mem_of_mem_erase hv⟩
    rw [List.length_erase_of_mem hs] at hn
    have := List.length_pos_of_mem hs
    omega

end LeanerVM.Semantics
