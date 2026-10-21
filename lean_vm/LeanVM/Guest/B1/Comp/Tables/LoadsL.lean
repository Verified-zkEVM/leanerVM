/-
  LeanVM.Guest.B1.Comp.Tables.LoadsL

  Where a call tree's load equations come from: a load atom on a node's path, a callee's tree,
  the iterations of a `mul_range` loop, and the stream words they read.
-/

module

public import LeanVM.Guest.Memory.LoadEqns
public import LeanVM.Guest.B1.Tables.VtCSizeS
public import LeanVM.Guest.B1.Tables.Flock

/-!
# Load equations of the tables' trees

`Tree.loadEqns` (`Memory/LoadEqns.lean`) collects the words the loads of an evaluation's paths
read. Here:

* a load atom of a node's path is one of its load equations (`mem_loadEqns_node`), and a
  callee's are its caller's (`mem_loadEqns_kid`);
* `loadWord`: the word a load reads at `g^(c+k)`, on a memory holding `xs` at `g^c`, is `xs[k]`;
* `loopS_loads`: the valid trees under any semantics of a `mul_range` loop from `g^j` to `g^m`
  load what each iteration's path and callees load (`vtcS_loop_total`'s induction);
* `leafS_node`: a valid tree of a straight-line function with no `HeapBuf` and no callee is its
  node, its path the body's atoms.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

section
variable {P : Core.Program} {σ : Val}

theorem mem_evLoadEqns {es : List Ev} {d p : V} {off : ℕ} (h : Ev.atom (.load d p off) ∈ es) :
    ((σ p).limb 0 * gpow off, σ d) ∈ evLoadEqns σ es :=
  List.mem_flatMap.mpr ⟨_, h, List.mem_singleton_self _⟩

theorem evLoadEqns_append (es es' : List Ev) :
    evLoadEqns σ (es ++ es') = evLoadEqns σ es ++ evLoadEqns σ es' := by
  simp [evLoadEqns, List.flatMap_append]

/-- **A load equation of a node's path is the node's.** -/
theorem mem_loadEqns_node {f : String} {bufs : List ℕ} {kids : List Tree} {fn : Fn} {es : List Ev}
    {vs : List V} (hf : P.find? f = some fn) (hw : walk σ fn.body = .ret es vs) {q : K × E}
    (hq : q ∈ evLoadEqns σ es) : q ∈ (Memory.Tree.node f σ bufs kids).loadEqns P := by
  rw [Tree.loadEqns, events_node hf hw]
  exact List.mem_append_left _ hq

theorem mem_loadEqnsKids : ∀ {ks : List Tree} {k : Tree}, k ∈ ks → ∀ {q : K × E},
    q ∈ k.loadEqns P → q ∈ Tree.loadEqnsKids P ks
  | [], _, h, _, _ => absurd h List.not_mem_nil
  | _ :: ks, _, h, q, hq => by
    rw [Tree.loadEqnsKids]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_append_left _ hq
    · exact List.mem_append_right _ (mem_loadEqnsKids h hq)

theorem loadEqnsKids_append (ks ks' : List Tree) :
    Tree.loadEqnsKids P (ks ++ ks') = Tree.loadEqnsKids P ks ++ Tree.loadEqnsKids P ks' := by
  induction ks with
  | nil => simp [Tree.loadEqnsKids]
  | cons k ks ih => simp [Tree.loadEqnsKids, ih]

/-- **A callee's load equation is its caller's.** -/
theorem mem_loadEqns_kid {f : String} {bufs : List ℕ} {kids : List Tree} {k : Tree} (hk : k ∈ kids)
    {q : K × E} (hq : q ∈ k.loadEqns P) : q ∈ (Memory.Tree.node f σ bufs kids).loadEqns P := by
  rw [Tree.loadEqns]
  exact List.mem_append_right _ (mem_loadEqnsKids hk hq)

end

/-- **The word a load reads at `g^(c+k)`**, on a memory holding `xs` at `g^c`. -/
theorem loadWord {rd : Reader} {p : E} {off : ℕ} {v : E} {c : ℕ} {xs : List E} {k : ℕ}
    (hl : LoadHolds rd p off v) (hx : ReadsAt rd (ofK (Parameters.gpow c)) xs) (hk : k < xs.length)
    (ha : p.limb 0 * Parameters.gpow off = Parameters.gpow (c + k)) : v = xs[k] := by
  have h := (hx k hk).2
  rw [Main.addr_ofK, ← ha] at h
  exact Option.some.inj (hl.2.symm.trans h)

/-- An atom of a straight-line block is an event of its path. -/
theorem mem_slEvs_of {σ : Val} {pre : List Stmt} {a : Atom} (h : Stmt.atom a ∈ pre) :
    Ev.atom a ∈ pre.flatMap (Main.slEvs σ) :=
  List.mem_flatMap.mpr ⟨_, h, by simp [Main.slEvs]⟩

/-- An atom a statement of a block is equal to (by `stmtsEqb`) is in the block. -/
theorem mem_of_stmtsEqb {l : List Stmt} {i : ℕ} {a : Atom}
    (h : stmtsEqb [.atom a] ((l.drop i).take 1) = true) : Stmt.atom a ∈ l := by
  have h1 := stmtsEqb_sound h
  have h2 : Stmt.atom a ∈ (l.drop i).take 1 := by rw [← h1]; exact List.mem_singleton_self _
  exact List.mem_of_mem_drop (List.mem_of_mem_take h2)

/-- A load in a straight-line block, from the block's loads. -/
theorem exists_load_of_loadS {l : List Stmt} {p : V} {off : ℕ} (h : (p, off) ∈ l.filterMap Stmt.loadS) :
    ∃ d, Stmt.atom (.load d p off) ∈ l := by
  obtain ⟨s, hs, he⟩ := List.mem_filterMap.mp h
  match s, he with
  | .atom (.load d p' off'), he =>
    simp only [Stmt.loadS, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨d, hs⟩

/-- **A load event reading a stream word**: on a memory holding `xs` at `g^c`, the load at
`g^(c+k)` of a path whose events hold is the load equation `(g^(c+k), xs[k])`. -/
theorem loadEq_of_event {S : BlakeSem} {rd : Reader} {σ : Val} {es : List Ev} {d p : V} {off : ℕ}
    {c : ℕ} {xs : List E} {k : ℕ} (hes : ∀ e ∈ es, e.HoldsB S rd σ)
    (hm : Ev.atom (.load d p off) ∈ es) (hx : ReadsAt rd (ofK (Parameters.gpow c)) xs)
    (hk : k < xs.length) (ha : (σ p).limb 0 * Parameters.gpow off = Parameters.gpow (c + k)) :
    (Parameters.gpow (c + k), xs[k]) ∈ evLoadEqns σ es := by
  have hl : LoadHolds rd (σ p) off (σ d) := hes _ hm
  have hv := loadWord hl hx hk ha
  rw [← ha, ← hv]
  exact mem_evLoadEqns hm

/-! ## Nodes of straight-line functions -/

section Node

variable {S : BlakeSem}

/-- **A valid tree of a straight-line function**: its node at a valuation of its parameters, its
path the body's events holding, its callees valid for the frames the path sets up. -/
theorem nodeS_straight {rd : Reader} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Main.Stmt.straight = true) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.ValidB S coreProgram rd args rets) :
    ∃ σ bufs kids, t = Memory.Tree.node f σ bufs kids ∧ fn.params.map σ = args ∧
      walk σ fn.body = .ret (pre.flatMap (Main.slEvs σ)) vs ∧
      (∀ e ∈ pre.flatMap (Main.slEvs σ), e.HoldsB S rd σ) ∧
      Tree.KidsValidB S coreProgram rd σ ((pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) kids := by
  match t, hn, hv with
  | .node g σ bufs kids, hn, hv =>
    simp only [Tree.name] at hn
    subst hn
    obtain ⟨fn', hf', hp, es, vs', hw, -, hes, hk⟩ := hv
    rw [hf, Option.some.injEq] at hf'
    subst hf'
    have hw' : walk σ fn.body = .ret (pre.flatMap (Main.slEvs σ)) vs := by
      rw [hb]; exact Main.walk_straight σ vs pre hst
    rw [hw'] at hw
    cases hw
    obtain ⟨-, -, -, i4⟩ := Main.straight_parts σ pre hst
    exact ⟨σ, bufs, kids, rfl, hp, hw', hes, by rw [← i4]; exact hk⟩

/-- **A `mul_range` loop's valid trees load what its iterations load**: from `g^j` to `g^m`,
each iteration `j'` at its valuation loading (on its path or by its other callees) the equations
`A j'`. -/
theorem loopS_loads {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre : List Stmt} {c : V} {nxt : List V} (hb : fn.body = pre ++ [.callIf c f nxt, .ret []])
    (hst : pre.all Main.Stmt.straight = true) (rd : Reader) (m : ℕ) (hm : m < 2 ^ 63)
    (rest : List E) (A : ℕ → K × E → Prop)
    (hstep : ∀ σ j, j < m → fn.params.map σ = gen ^ j :: gen ^ m :: rest →
      (∀ e ∈ pre.flatMap (Main.slEvs σ), e.HoldsB S rd σ) →
      σ c = gen ^ j * gen + gen ^ m ∧ nxt.map σ = gen ^ j * gen :: gen ^ m :: rest ∧
      ∀ kids, Tree.KidsValidB S coreProgram rd σ ((pre.filterMap Main.Stmt.callS).map (Main.mkCall σ))
        kids → ∀ q, A j q → q ∈ evLoadEqns σ (pre.flatMap (Main.slEvs σ)) ∨
          q ∈ Tree.loadEqnsKids coreProgram kids) :
    ∀ (d j : ℕ) (t : Tree) (rets : List E), j + d = m → j < m → t.name = f →
      t.ValidB S coreProgram rd (gen ^ j :: gen ^ m :: rest) rets →
      ∀ j', j ≤ j' → j' < m → ∀ q, A j' q → q ∈ t.loadEqns coreProgram := by
  have hb' : fn.body = (pre ++ [Stmt.callIf c f nxt]) ++ [Stmt.ret []] := by
    rw [hb, List.append_assoc]; rfl
  have hst' : (pre ++ [Stmt.callIf c f nxt]).all Main.Stmt.straight = true := by
    simp [hst, Main.Stmt.straight]
  intro d
  induction d with
  | zero => intro j t rets hjd hj; omega
  | succ d ih =>
    intro j t rets hjd hj hn hv j' hj1 hj2 q hq
    obtain ⟨σ, bufs, kids, rfl, hp, hw, hes, hk⟩ := nodeS_straight (S := S) hf hb' hst' hn hv
    have hes' : ∀ e ∈ pre.flatMap (Main.slEvs σ), e.HoldsB S rd σ := fun e he =>
      hes e (by rw [List.flatMap_append]; exact List.mem_append_left _ he)
    obtain ⟨hc, hnx, hK⟩ := hstep σ j hj hp hes'
    rw [List.filterMap_append, List.map_append] at hk
    obtain ⟨k1, k2, rfl, hk1, hk2⟩ := vtcS_kidsValid_append hk
    rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
    · rcases hK k1 hk1 q hq with h | h
      · refine mem_loadEqns_node hf hw ?_
        rw [List.flatMap_append, evLoadEqns_append]
        exact List.mem_append_left _ h
      · rw [Tree.loadEqns]
        refine List.mem_append_right _ ?_
        rw [loadEqnsKids_append]
        exact List.mem_append_left _ h
    · simp only [Main.Stmt.callS, List.filterMap_cons, List.filterMap_nil, List.map_cons,
        List.map_nil, Main.mkCall] at hk2
      match k2, hk2 with
      | [kl], ⟨hnl, hvl, _⟩ =>
        have hz : σ c ≠ 0 := by
          rw [hc, gen_pow_mul_gen]
          exact gen_pow_ne_of_lt (by omega) hm
        simp only [hz, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, hnx] at hvl
        rw [gen_pow_mul_gen] at hvl
        have := ih (j + 1) kl _ (by omega) (by omega) hnl hvl j' (by omega) hj2 q hq
        exact mem_loadEqns_kid (List.mem_append_right _ (List.mem_singleton_self _)) this

end Node

end
end LeanVM.Guest.B1
