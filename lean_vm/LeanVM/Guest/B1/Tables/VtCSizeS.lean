/-
  LeanVM.Guest.B1.Tables.VtCSizeS

  `VtCSize.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Tables.VtCSize
public import LeanVM.Guest.Memory.TreeB
public import LeanVM.Guest.Memory.PlacedB
public import LeanVM.Guest.CoreB

/-!
# `VtCSize.lean` under any `BLAKE2S` semantics

Each definition and lemma of `VtCSize.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem}

variable {fs : String → ℕ}

theorem vtcS_kidsValid_append {rd : Reader} {σ : Val} : ∀ {cs cs' : List Call} {ks : List Tree},
    Tree.KidsValidB S coreProgram rd σ (cs ++ cs') ks →
      ∃ k1 k2, ks = k1 ++ k2 ∧ Tree.KidsValidB S coreProgram rd σ cs k1 ∧
        Tree.KidsValidB S coreProgram rd σ cs' k2
  | [], _, ks, h => ⟨[], ks, rfl, by simp [Tree.KidsValidB], h⟩
  | _ :: _, _, [], h => by simp [Tree.KidsValidB] at h
  | c :: cs, cs', k :: ks, h => by
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨k1, k2, rfl, h4, h5⟩ := vtcS_kidsValid_append (cs := cs) (cs' := cs') h3
    exact ⟨k :: k1, k2, rfl, ⟨h1, h2, h4⟩, h5⟩

/-- **A valid tree of a straight-line function with no `HeapBuf`**: its frame and its callees'
trees, valid for the frames its path sets up. -/
theorem vtcS_node {rd : Reader} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Main.Stmt.straight = true) (hna : pre.filterMap Main.Stmt.allocSz = [])
    {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.ValidB S coreProgram rd args rets)
    (hbo : t.BufsOk coreProgram) :
    ∃ σ kids, t.total fs = fs f + Tree.totalKids fs kids ∧ fn.params.map σ = args ∧
      (∀ e ∈ pre.flatMap (Main.slEvs σ), e.HoldsB S rd σ) ∧
      Tree.KidsValidB S coreProgram rd σ ((pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) kids ∧
      Tree.BufsOkKids coreProgram kids := by
  match t, hn, hv, hbo with
  | .node g σ bufs kids, hn, hv, hbo =>
    simp only [Tree.name] at hn
    subst hn
    obtain ⟨fn', hf', hp, es, vs', hw, -, hes, hk⟩ := hv
    rw [hf, Option.some.injEq] at hf'
    subst hf'
    have hw' : walk σ fn.body = .ret (pre.flatMap (Main.slEvs σ)) vs := by
      rw [hb]; exact Main.walk_straight σ vs pre hst
    rw [hw'] at hw
    cases hw
    obtain ⟨hbuf, hbk⟩ := hbo
    have hev : (Memory.Tree.node g σ bufs kids).events coreProgram = pre.flatMap (Main.slEvs σ) := by
      simp only [Tree.events, Tree.name, Tree.val, hf, hw']
    obtain ⟨-, i2, -, i4⟩ := Main.straight_parts σ pre hst
    rw [hev, i2, hna] at hbuf
    refine ⟨σ, kids, ?_, hp, hes, by rw [← i4]; exact hk, hbk⟩
    simp [Tree.total, hbuf]

/-- **A valid tree of a straight-line function with no `HeapBuf` and no callee** is its frame. -/
theorem vtcS_leaf_total {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Main.Stmt.straight = true) (hna : pre.filterMap Main.Stmt.allocSz = [])
    (hnc : pre.filterMap Main.Stmt.callS = []) {rd : Reader} {t : Tree} {args rets : List E}
    (hn : t.name = f) (hv : t.ValidB S coreProgram rd args rets) (hbo : t.BufsOk coreProgram) :
    t.total fs = fs f := by
  obtain ⟨σ, kids, ht, -, -, hk, -⟩ := vtcS_node (S := S) (fs := fs) hf hb hst hna hn hv hbo
  rw [hnc] at hk
  match kids, hk with
  | [], _ => simpa [Tree.totalKids] using ht

/-- One event of a straight-line path: an atom of the block holds. -/
theorem vtcS_atom {rd : Reader} {σ : Val} {pre : List Stmt}
    (h : ∀ e ∈ pre.flatMap (Main.slEvs σ), e.HoldsB S rd σ) {a : Atom} (ha : Stmt.atom a ∈ pre) :
    a.HoldsB S rd σ :=
  h (.atom a) (List.mem_flatMap.mpr ⟨_, ha, by simp [Main.slEvs]⟩)

/-- **A `mul_range` loop helper's valid trees**, from `g^j` to `g^m`, are at most `m - j`
iterations of its frame and its other callees (at most `K` each), plus the frame of the last
iteration's tail, set up and not entered. -/
theorem vtcS_loop_total {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre : List Stmt} {c : V} {nxt : List V} (hb : fn.body = pre ++ [.callIf c f nxt, .ret []])
    (hst : pre.all Main.Stmt.straight = true) (hna : pre.filterMap Main.Stmt.allocSz = [])
    (rd : Reader) (m : ℕ) (rest : List E) (K : ℕ)
    (hstep : ∀ σ j, j < m → fn.params.map σ = gen ^ j :: gen ^ m :: rest →
      (∀ e ∈ pre.flatMap (Main.slEvs σ), e.HoldsB S rd σ) →
      σ c = gen ^ j * gen + gen ^ m ∧ nxt.map σ = gen ^ j * gen :: gen ^ m :: rest ∧
      ∀ kids, Tree.KidsValidB S coreProgram rd σ ((pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) kids →
        Tree.BufsOkKids coreProgram kids → Tree.totalKids fs kids ≤ K) :
    ∀ (d j : ℕ) (t : Tree) (rets : List E), j + d = m → j < m → t.name = f →
      t.ValidB S coreProgram rd (gen ^ j :: gen ^ m :: rest) rets → t.BufsOk coreProgram →
      t.total fs ≤ d * (fs f + K) + fs f := by
  have hb' : fn.body = (pre ++ [Stmt.callIf c f nxt]) ++ [Stmt.ret []] := by rw [hb, List.append_assoc]; rfl
  have hst' : (pre ++ [Stmt.callIf c f nxt]).all Main.Stmt.straight = true := by
    simp [hst, Main.Stmt.straight]
  have hna' : (pre ++ [Stmt.callIf c f nxt]).filterMap Main.Stmt.allocSz = [] := by
    simp [hna, Main.Stmt.allocSz]
  intro d
  induction d with
  | zero => intro j t rets hjd hj; omega
  | succ d ih =>
    intro j t rets hjd hj hn hv hbo
    obtain ⟨σ, kids, ht, hp, hes, hk, hbk⟩ := vtcS_node (S := S) (fs := fs) hf hb' hst' hna' hn hv hbo
    have hes' : ∀ e ∈ pre.flatMap (Main.slEvs σ), e.HoldsB S rd σ := fun e he =>
      hes e (by rw [List.flatMap_append]; exact List.mem_append_left _ he)
    obtain ⟨hc, hnx, hK⟩ := hstep σ j hj hp hes'
    rw [List.filterMap_append, List.map_append] at hk
    obtain ⟨k1, k2, rfl, hk1, hk2⟩ := vtcS_kidsValid_append hk
    obtain ⟨hb1, hb2⟩ := vtc_bufsOkKids_append hbk
    have h1 := hK k1 hk1 hb1
    simp only [Main.Stmt.callS, List.filterMap_cons, List.filterMap_nil, List.map_cons, List.map_nil,
      Main.mkCall] at hk2
    match k2, hk2, hb2 with
    | [kl], ⟨hnl, hvl, _⟩, ⟨hbl, _⟩ =>
      have h2 : kl.total fs ≤ d * (fs f + K) + fs f := by
        by_cases hz : σ c = 0
        · simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hvl
          obtain ⟨⟨g, σ', rfl⟩, -⟩ := hvl
          simp only [Tree.name] at hnl
          simp [Tree.total, hnl]
        · simp only [hz, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, hnx] at hvl
          have hj1 : j + 1 < m := by
            rcases Nat.lt_or_ge (j + 1) m with h | h
            · exact h
            · exfalso; apply hz
              rw [hc, show m = j + 1 by omega, gen_pow_mul_gen, e_add_self]
          rw [gen_pow_mul_gen] at hvl
          exact ih (j + 1) kl _ (by omega) hj1 hnl hvl hbl
      rw [ht, vtc_totalKids_append]
      simp only [Tree.totalKids, Nat.add_zero]
      rw [Nat.succ_mul]
      omega

end
end LeanVM.Guest.B1
