/-
  LeanVM.Guest.B2C.Sites

  The call sites of a body: every call on a path is one of its body's call sites, with the site's
  argument values.
-/

module

public import LeanVM.Guest.Memory.SizeTotal

/-!
# Call sites

`Memory/SizeTotal.lean`'s `walk_callees` says a path calls only its body's callees. Here the same
with the arguments: the call sites of a statement, a block and arms (`stmtSites`, `blockSites`,
`armsSites`: a callee and its argument values), and every call on a path is a site of its body
(`walk_sites`), so a body's sites, decided by the kernel, give the argument values of its paths'
calls.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

mutual
/-- The call sites of a statement: the callee and its argument values. -/
def stmtSites : Stmt → List (String × List V)
  | .ite _ z n => blockSites z ++ blockSites n
  | .match_ _ arms => armsSites arms
  | .call f args _ => [(f, args)]
  | .callIf _ f args => [(f, args)]
  | .dispatch _ fs args _ => fs.map fun g ↦ (g, args)
  | _ => []

/-- The call sites of a block. -/
def blockSites : List Stmt → List (String × List V)
  | [] => []
  | s :: ss => stmtSites s ++ blockSites ss

/-- The call sites of arms. -/
def armsSites : List (List Stmt) → List (String × List V)
  | [] => []
  | a :: as => blockSites a ++ armsSites as
end

section Walk

variable {σ : Val}

theorem pick_sites {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ) {c : Call},
    c ∈ calls (pick σ x args rets j gs).evs → (c.f, c.args) ∈ gs.map fun g ↦ (g, args)
  | [], _, c, h => by simp [pick, Out.evs, calls] at h
  | g :: gs, j, c, h => by
      unfold pick at h
      split_ifs at h
      · simp only [Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
          List.mem_cons, List.not_mem_nil, or_false] at h
        subst h
        simp
      · exact List.mem_cons_of_mem _ (pick_sites gs (j + 1) h)

mutual
/-- **A statement's path calls at its sites.** -/
theorem walk1_sites : ∀ (s : Stmt) {c : Call}, c ∈ calls (walk1 σ s).evs → (c.f, c.args) ∈ stmtSites s
  | .atom a, c, h => by simp [walk1, Out.evs, calls, Ev.call?] at h
  | .ite b z m, c, h => by
      rw [walk1, Out.calls_pre_inK] at h
      simp only [stmtSites, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_sites z h)
      · exact Or.inr (walk_sites m h)
  | .match_ x arms, c, h => by
      rw [walk1] at h
      exact walkArms_sites x arms 0 h
  | .call f args rets, c, h => by
      simp only [walk1, Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; simp [stmtSites]
  | .callIf b f args, c, h => by
      rw [walk1] at h
      split_ifs at h <;>
        simp only [Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
          List.mem_cons, List.not_mem_nil, or_false] at h <;> subst h <;> simp [stmtSites]
  | .dispatch x gs args rets, c, h => by
      rw [walk1] at h
      exact pick_sites gs 0 h
  | .ret _, c, h => by simp [walk1, Out.evs, calls] at h

/-- **A block's path calls at its sites.** -/
theorem walk_sites : ∀ (ss : List Stmt) {c : Call}, c ∈ calls (walk σ ss).evs →
    (c.f, c.args) ∈ blockSites ss
  | [], c, h => by simp [walk, Out.evs, calls] at h
  | s :: ss, c, h => by
      rw [walk] at h
      simp only [blockSites, List.mem_append]
      rcases Out.calls_seq h with h | h
      · exact Or.inl (walk1_sites s h)
      · exact Or.inr (walk_sites ss h)

theorem walkArms_sites (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {c : Call},
    c ∈ calls (walkArms σ x j arms).evs → (c.f, c.args) ∈ armsSites arms
  | [], _, c, h => by simp [walkArms, Out.evs, calls] at h
  | a :: as, j, c, h => by
      unfold walkArms at h
      simp only [armsSites, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_sites a h)
      · exact Or.inr (walkArms_sites x as (j + 1) h)
end

end Walk

end
end LeanVM.Guest.B2C
