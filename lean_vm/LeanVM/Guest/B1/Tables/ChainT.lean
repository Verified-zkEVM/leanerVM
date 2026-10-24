/-
  LeanVM.Guest.B1.Tables.ChainT

  A counter loop helper's valid trees are chains of honest shape (`Budget.ChainHonest`).
-/

module

public import LeanVM.Guest.Budget.Chain
public import LeanVM.Guest.B1.Tables.Basic

/-!
# Counter loops' trees

A loop helper `f` of parameters `.n 0 .. .n (k + 1)` whose body is straight statements `pre`,
then `callIf cnd f (nx :: [.n 1, …, .n (k + 1)])`, then `ret []`, its counter `.n 0` advanced by
`g` (`σ nx = σ(.n 0)·g`) and its condition `σ cnd = σ(.n 0)·g + σ(.n 1)` (zero at the end
`.n 1`), places nothing. `chain_of_valid`: every valid tree of `f` from counter `g^c` to the end
`g^N` (`c + m = N`) is `ChainHonest f Q m c`: iteration `c'` pins the counter `g^c'` and the end
`g^N`, its body's calls are `pre`'s (by predicates `True`), its tail call the next iteration.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The calls of a straight block under `σ`. -/
noncomputable def slCalls (pre : List Stmt) (σ : Val) : List Call :=
  (pre.filterMap Stmt.callS).map (mkCall σ)

/-- A counter loop's iterations: counter `g^c`, end `g^N`. -/
def CounterQ (N : ℕ) (c : ℕ) (σ : Val) : Prop := σ (.n 0) = gen ^ c ∧ σ (.n 1) = gen ^ N

theorem kidsT_replicate_snoc {P : Core.Program} {rd : Reader} {σ : Val} {T : Tree → Prop}
    {c : Call} (hT : c.taken = true → ∀ k : Tree, k.name = c.f →
      k.Valid P rd (c.args.map σ) (c.rets.map σ) → k.BufsOk P → T k) :
    ∀ (cs : List Call) (ks : List Tree), Tree.KidsValid P rd σ (cs ++ [c]) ks →
      Tree.BufsOkKids P ks →
      KidsT (cs ++ [c]) (List.replicate cs.length (fun _ ↦ True) ++ [T]) ks
  | [], [], h, _ => by simp [Tree.KidsValid] at h
  | [], [k], h, hb => by
    obtain ⟨hn, hv, -⟩ := h
    refine ⟨fun ht ↦ ?_, trivial⟩
    simp only [ht, ↓reduceIte] at hv
    exact hT ht k hn hv hb.1
  | [], _ :: _ :: _, h, _ => by simp [Tree.KidsValid] at h
  | _ :: _, [], h, _ => by simp [Tree.KidsValid] at h
  | c' :: cs, k :: ks, h, hb =>
    ⟨fun _ ↦ trivial, kidsT_replicate_snoc hT cs ks h.2.2 hb.2⟩

set_option maxHeartbeats 1000000 in
/-- **A counter loop's valid trees are chains of honest shape.** -/
theorem chain_of_valid {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) {k : ℕ}
    (hp : fn.params = (List.range (k + 2)).map V.n) {pre : List Stmt} {cnd nx : V}
    (hb : fn.body = pre ++ [.callIf cnd f (nx :: (List.range (k + 1)).map fun i ↦ V.n (i + 1)),
      .ret []])
    (hst : pre.all Stmt.straight = true) (hal : pre.filterMap Stmt.allocSz = [])
    (heq : ∀ (rd : Reader) (σ : Val), (∀ e ∈ pre.flatMap (slEvs σ), e.Holds rd σ) →
      σ cnd = σ (.n 0) * gen + σ (.n 1) ∧ σ nx = σ (.n 0) * gen)
    {N : ℕ} (rd : Reader) (rest : List E) :
    ∀ m c, c + m = N → 0 < m → ∀ (t : Tree) (r : List E), t.name = f →
      t.Valid coreProgram rd (gen ^ c :: gen ^ N :: rest) r → t.BufsOk coreProgram →
      Budget.ChainHonest coreProgram f (CounterQ N) (slCalls pre)
        (fun σ ↦ mkCall σ (some cnd, f, nx :: (List.range (k + 1)).map fun i ↦ V.n (i + 1), []))
        (fun _ ↦ []) (fun _ ↦ List.replicate (pre.filterMap Stmt.callS).length fun _ ↦ True)
        m c t := by
  have hrange : (List.range (k + 2)).map V.n =
      V.n 0 :: (List.range (k + 1)).map fun i ↦ V.n (i + 1) := by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl
  set nargs : List V := nx :: (List.range (k + 1)).map fun i ↦ V.n (i + 1) with hnargs
  set pre' := pre ++ [Stmt.callIf cnd f nargs] with hpre'
  have hst' : pre'.all Stmt.straight = true := by simp [pre', hst, Stmt.straight]
  have hb' : fn.body = pre' ++ [.ret []] := by rw [hb, hpre', List.append_assoc]; rfl
  have hcalls : ∀ σ : Val, (pre'.filterMap Stmt.callS).map (mkCall σ) =
      slCalls pre σ ++ [mkCall σ (some cnd, f, nargs, [])] := by
    intro σ
    simp [pre', slCalls, List.filterMap_append, Stmt.callS]
  have hallocs : ∀ σ : Val, (pre'.filterMap Stmt.allocSz).map
      (fun x => x.2.elim id fun s => logG (σ s)) = [] := by
    intro σ
    simp [pre', List.filterMap_append, hal, Stmt.allocSz]
  intro m
  induction m with
  | zero => intro c _ h; omega
  | succ m ih =>
    intro c hcm _ t r hn hv hbo
    match t, hn, hv, hbo with
    | .node f' σ bufs ks, hn, hv, hbo =>
      simp only [Tree.name] at hn
      subst f'
      obtain ⟨fn', hf', hpar, es, vs, hw, -, hes, hkv⟩ := hv
      rw [hf, Option.some.injEq] at hf'
      subst hf'
      have hw' : walk σ fn.body = .ret (pre'.flatMap (slEvs σ)) [] := by
        rw [hb']; exact walk_straight σ [] pre' hst'
      rw [hw', Out.ret.injEq] at hw
      obtain ⟨rfl, -⟩ := hw
      obtain ⟨-, i2, -, i4⟩ := straight_parts σ pre' hst'
      have hbufs : bufs = [] := by
        rw [hbo.1, events_node hf hw', i2, hallocs]
      subst hbufs
      rw [i4, hcalls] at hkv
      rw [hp, hrange, List.map_cons, List.cons.injEq] at hpar
      obtain ⟨h0, hrest⟩ := hpar
      have h1 : σ (.n 1) = gen ^ N := by
        have h' := hrest
        rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.cons.injEq] at h'
        exact h'.1
      have hpre : ∀ e ∈ pre.flatMap (slEvs σ), e.Holds rd σ := fun e he ↦
        hes e (by simp only [pre', List.flatMap_append]; exact List.mem_append_left _ he)
      obtain ⟨hcnd, hnx⟩ := heq rd σ hpre
      refine ⟨σ, ks, rfl, ⟨h0, h1⟩, fun fn'' es' vs' hf'' hw'' ↦ ?_, by simp [slCalls], ?_⟩
      · rw [hf, Option.some.injEq] at hf''
        subst hf''
        rw [hw', Out.ret.injEq] at hw''
        rw [← hw''.1, i4, hcalls]
      · have := kidsT_replicate_snoc (T := Budget.ChainHonest coreProgram f (CounterQ N)
          (slCalls pre) (fun σ ↦ mkCall σ (some cnd, f, nargs, [])) (fun _ ↦ [])
          (fun _ ↦ List.replicate (pre.filterMap Stmt.callS).length fun _ ↦ True) m (c + 1))
          (c := mkCall σ (some cnd, f, nargs, [])) (fun ht kt hkn hkv hkb ↦ ?_) _ ks hkv hbo.2
        · simpa [slCalls] using this
        · simp only [mkCall, decide_eq_true_eq] at ht hkn hkv
          have hm : 0 < m := by
            by_contra hm0
            have hc1 : c + 1 = N := by omega
            apply ht
            rw [hcnd, h0, h1, ← pow_succ, hc1]
            exact e_add_eq_zero_iff.mpr rfl
          refine ih (c + 1) (by omega) hm kt [] hkn ?_ hkb
          rw [hnargs, List.map_cons, hnx, h0, ← pow_succ, hrest] at hkv
          exact hkv

end
end LeanVM.Guest.B1.Tables
