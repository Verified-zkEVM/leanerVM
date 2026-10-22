/-
  LeanVM.Guest.B1.Comp.Whir.LoadsT.OsInjT

  The instances of placed valid trees the stacked opening's injectivity needs: the callees'
  instances one by one, the subtrees of functions reaching only `osInjZ`, an `opening_queries`
  specialization's subtree (its node, then its loop helper's chain).
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LoadsT.OsInjS
public import LeanVM.Guest.Memory.Placed

/-!
# Instances of placed valid trees

* `osI_mem_instsKids`, `osI_kidsGet`, `osI_placedKidsGet`: an instance of a node's callees is an
  instance of its `i`-th callee, placed at the `i`-th callee frame, valid for the `i`-th call;
* `osI_instsZ`: every instance of a valid tree of a function of `osInjZ` is of `osInjZ`;
* `osI_chain`: a loop helper calling only itself at `x·g` (`OsILoop`), entered (or not) at
  `x :: rest` and placed at `p`: its instances are its iterations, the `d`-th on `x·g^d :: rest`
  at `p + d · fs L` (`OsIChainAt`);
* `osI_q`: an `opening_queries` specialization's valid placed tree at `p`: its node, then its loop
  helper's chain from `1`, its query sums' buffer `g^(p + fs q)` passed as the helper's fourth
  argument.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem osI_fs_two (f : String) : 2 ≤ B2C.fs f := by
  unfold B2C.fs
  split
  · simp [B2C.mainFrame]
  · exact le_max_left _ _
  · exact le_refl _

section Kids

variable {fs : String → ℕ} {lp : String → Bool} {H : Inst → ℕ → E × E}

/-- **An instance of the callees at `ps`** is an instance of the `i`-th at `ps[i]`. -/
theorem osI_mem_instsKids : ∀ (ks : List Tree) (ps : List ℕ) (I : Inst) (j : ℕ),
    ∀ J ∈ Tree.instsKids fs lp H I j ps ks,
      ∃ (i : ℕ) (k : Tree) (p : ℕ), ks[i]? = some k ∧ ps[i]? = some p ∧ J ∈ k.insts fs lp H p (H I (j + i))
  | [], _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, J, hJ => by rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, p :: ps, I, j, J, hJ => by
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · exact ⟨0, k, p, rfl, rfl, by simpa using hJ⟩
      · obtain ⟨i, k', p', h1, h2, h3⟩ := osI_mem_instsKids ks ps I (j + 1) J hJ
        exact ⟨i + 1, k', p', by simpa using h1, by simpa using h2,
          by rwa [show j + (i + 1) = j + 1 + i by omega]⟩

end Kids

/-- **The `i`-th callee of a valid path** is valid for the `i`-th call, or a phantom of it. -/
theorem osI_kidsGet {S : BlakeSem} {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValidB S P rd σ cs ks → ∀ {i : ℕ} {k : Tree},
      ks[i]? = some k → ∃ c, cs[i]? = some c ∧ k.name = c.f ∧
        (c.taken = true → k.ValidB S P rd (c.args.map σ) (c.rets.map σ)) ∧
        (c.taken = false → (∃ f σ', k = .phantom f σ') ∧ Phantom P k (c.args.map σ))
  | [], [], _, _, _, h => by simp at h
  | c :: cs, k' :: ks, ⟨hn, hv, hks⟩, i, k, h => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      refine ⟨c, rfl, hn, fun ht => by rwa [ite_eq_left ht] at hv, fun ht => ?_⟩
      have ht' : ¬ c.taken = true := by simp [ht]
      rwa [ite_eq_right ht'] at hv
    | succ i => simpa using osI_kidsGet hks (by simpa using h)
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

/-- The `i`-th callee of a placed node is placed at the `i`-th callee frame. -/
theorem osI_placedKidsGet {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ} :
    ∀ {ps : List ℕ} {ks : List Tree}, Tree.PlacedKids P fs cert ps ks → ∀ {i : ℕ} {k : Tree} {p : ℕ},
      ks[i]? = some k → ps[i]? = some p → k.Placed P fs cert p
  | _, [], _, _, _, _, h, _ => by simp at h
  | [], _ :: _, _, _, _, _, _, h' => by simp at h'
  | p' :: ps, k' :: ks, hp, i, k, p, h, h' => by
    rw [placedKids_cons] at hp
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h h'
      subst h h'
      exact hp.1
    | succ i => exact osI_placedKidsGet hp.2 (by simpa using h) (by simpa using h')

/-! ## The subtrees reaching `osInjZ` only -/

section Z

variable {S : BlakeSem} {rd : Reader} {fs : String → ℕ} {lp : String → Bool} {H : Inst → ℕ → E × E}

mutual
/-- **The instances of a valid tree of a function of `osInjZ`** are of `osInjZ`. -/
theorem osI_instsZ : ∀ (t : Tree) {args rets : List E}, t.ValidB S coreProgram rd args rets →
    t.name ∈ osInjZ → ∀ (p : ℕ) (hdr : E × E), ∀ I ∈ t.insts fs lp H p hdr, I.t.name ∈ osInjZ
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hn, p, hdr, I, hI => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact hn
      · exact osI_instsZKids kids _ _ 0 σ (calls es) hk
          (fun c hc => osInjZ_callsIn f hn fn hf σ es vs hw c hc) I hI
  | .phantom .., _, _, h, _, _, _, _, _ => h.elim

/-- `osI_instsZ` for the callees of a path calling `osInjZ` only. -/
theorem osI_instsZKids : ∀ (ks : List Tree) (ps : List ℕ) (J : Inst) (j : ℕ) (σ : Val) (cs : List Call),
    Tree.KidsValidB S coreProgram rd σ cs ks → (∀ c ∈ cs, c.f ∈ osInjZ) →
      ∀ I ∈ Tree.instsKids fs lp H J j ps ks, I.t.name ∈ osInjZ
  | [], _, _, _, _, _, _, _, I, hI => by rw [instsKids_nil] at hI; exact (List.not_mem_nil hI).elim
  | _ :: _, [], _, _, _, _, _, _, I, hI => by
      rw [instsKids_nil_left] at hI; exact (List.not_mem_nil hI).elim
  | k :: ks, p :: ps, J, j, σ, c :: cs, ⟨hn, hv, hks⟩, hc, I, hI => by
      rw [instsKids_cons, List.mem_append] at hI
      have hcf : k.name ∈ osInjZ := by rw [hn]; exact hc c List.mem_cons_self
      rcases hI with hI | hI
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hv
          exact osI_instsZ k hv hcf p _ I hI
        · rw [ite_eq_right ht] at hv
          obtain ⟨⟨f', σ', rfl⟩, -⟩ := hv
          rw [insts_phantom, List.mem_singleton] at hI
          subst hI
          exact hcf
      · exact osI_instsZKids ks ps J (j + 1) σ cs hks (fun c' h' => hc c' (List.mem_cons_of_mem _ h')) I hI
  | _ :: _, _ :: _, _, _, _, [], h, _, _, _ => h.elim
end

end Z

/-! ## A loop helper's chain -/

/-- **A loop helper calling only itself at `x·g`**: its function, its body before its `ret`
straight, without `HeapBuf`, its one call the tail call. -/
structure OsILoop (L : String) (lf : Fn) (pre : List Stmt) (c : V) (m k2 : ℕ) : Prop where
  find : coreProgram.find? L = some lf
  params : lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]
  body : lf.body = pre ++ [.ret []]
  straight : pre.all Main.Stmt.straight = true
  allocs : pre.filterMap Main.Stmt.allocSz = []
  calls : pre.filterMap Main.Stmt.callS = [(some c, L, [.n m, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [])]
  two : Stmt.atom (.const (.n k2) (word 2 0 0)) ∈ pre
  mul : Stmt.atom (.mul (.n m) (.n 0) (.n k2)) ∈ pre

/-- **Iteration `d` of the chain from `x :: rest` at `p`**: on `x·g^d :: rest`, at `p + d · fs L`. -/
def OsIChainAt (L : String) (lf : Fn) (fs : String → ℕ) (x : E) (rest : List E) (p : ℕ) (I : Inst) : Prop :=
  I.t.name = L ∧ ∃ d, lf.params.map I.t.val = (x * gen ^ d) :: rest ∧ I.fp = p + d * fs L

section Chain

variable {S : BlakeSem} {rd : Reader} {fs : String → ℕ} {cert : String → V → ℕ} {H : Inst → ℕ → E × E}
  {L : String} {lf : Fn} {pre : List Stmt} {c : V} {m k2 : ℕ}

/-- A placed node whose path allocates nothing has no `HeapBuf`. -/
theorem osI_bufs_nil {f : String} {σ : Val} {bufs : List ℕ} {ns : List ℕ} {es : List Ev} {fp : ℕ}
    (hN : NodeAt coreProgram fs cert fp f σ bufs ns es) (he : allocDsts es = []) : bufs = [] := by
  have h := hN.1
  rw [he, List.map_nil] at h
  have hl := congrArg List.length h
  simp only [List.length_nil, List.length_map, length_bases] at hl
  exact List.eq_nil_of_length_eq_zero hl.symm

/-- The one callee of a node without `HeapBuf`s is right after its frame. -/
theorem osI_kidPos_one (lp : String → Bool) (fp : ℕ) (f : String) (n : ℕ) :
    kidPos fs lp fp f [] [n] = [fp + fs f] := by
  unfold kidPos bufBase
  split <;> simp [bases]

/-- **A loop helper's chain.** -/
theorem osI_chain (hL : OsILoop L lf pre c m k2) : ∀ (t : Tree) (x : E) (rest : List E) (p : ℕ) (hdr : E × E),
    t.name = L →
    ((∃ rets, t.ValidB S coreProgram rd (x :: rest) rets) ∨
      ((∃ f σ', t = .phantom f σ') ∧ Phantom coreProgram t (x :: rest))) →
    t.Placed coreProgram fs cert p →
    ∀ I ∈ t.insts fs coreProgram.loop H p hdr, OsIChainAt L lf fs x rest p I
  | .node f σ bufs kids, x, rest, p, hdr, hn, hv, hpl, I, hI => by
    simp only [Tree.name] at hn
    rcases hv with ⟨rets, hv⟩ | ⟨⟨f', σ', he⟩, -⟩
    swap
    · cases he
    obtain ⟨fn, hf, hp, es, vs, hw, -, hes, hk⟩ := hv
    rw [hn] at hf
    have hfl : fn = lf := Option.some.inj (hf.symm.trans hL.find)
    rw [hfl] at hw hp hf
    have hw' : walk σ lf.body = .ret (pre.flatMap (Main.slEvs σ)) [] := by
      rw [hL.body]; exact Main.walk_straight σ [] pre hL.straight
    rw [hw'] at hw
    cases hw
    obtain ⟨i1, -, -, i4⟩ := Main.straight_parts σ pre hL.straight
    rw [i4, hL.calls] at hk
    simp only [List.map_cons, List.map_nil, Main.mkCall] at hk
    rw [hL.params] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
    obtain ⟨h0, hrest⟩ := hp
    have hat : ∀ a, Stmt.atom a ∈ pre → a.HoldsB S rd σ := fun a ha => hes _ (mem_slEvs_of ha)
    have c2 := hat _ hL.two
    have cm := hat _ hL.mul
    simp only [Atom.HoldsB] at c2 cm
    have hxm : σ (.n m) = x * gen := by rw [cm, c2, h0, word_gen]
    rw [placed_node, events_node (hn ▸ hL.find) hw'] at hpl
    obtain ⟨hNA, hPK⟩ := hpl
    have hbufs : bufs = [] := osI_bufs_nil hNA (by rw [i1, hL.allocs]; rfl)
    subst hbufs
    rw [insts_node, List.mem_cons] at hI
    rcases hI with rfl | hI
    · refine ⟨hn, 0, ?_, by simp⟩
      simp only [hL.params, List.map_cons, List.map_nil, Tree.val, pow_zero, mul_one, h0, ← hrest]
    match kids, hk with
    | [k], ⟨hkn, hkv, _⟩ =>
      simp only [List.map_cons, List.map_nil] at hPK hI
      rw [osI_kidPos_one, hn] at hPK hI
      rw [instsKids_cons, instsKids_nil, List.append_nil] at hI
      rw [placedKids_cons] at hPK
      have hargs : ([.n m, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] : List V).map σ = (x * gen) :: rest := by
        simp only [List.map_cons, List.map_nil, hxm, ← hrest]
      have hk' : (∃ rets, k.ValidB S coreProgram rd ((x * gen) :: rest) rets) ∨
          ((∃ f σ', k = .phantom f σ') ∧ Phantom coreProgram k ((x * gen) :: rest)) := by
        by_cases ht : σ c = 0
        · simp only [ht, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, hargs] at hkv
          exact .inr hkv
        · simp only [ht, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, hargs, List.map_nil] at hkv
          exact .inl ⟨_, hkv⟩
      obtain ⟨hIn, d, hd, hfp⟩ := osI_chain hL k (x * gen) rest _ _ hkn hk' hPK.1 I hI
      refine ⟨hIn, d + 1, by rw [hd, pow_succ', mul_assoc], by rw [hfp]; ring⟩
  | .phantom f σ', x, rest, p, hdr, hn, hv, _, I, hI => by
    simp only [Tree.name] at hn
    rcases hv with ⟨_, hv⟩ | ⟨-, fn, hf, hp⟩
    · exact hv.elim
    simp only [Tree.name, hn] at hf
    have hfl : fn = lf := Option.some.inj (hf.symm.trans hL.find)
    rw [hfl] at hp
    rw [insts_phantom, List.mem_singleton] at hI
    subst hI
    exact ⟨hn, 0, by simpa using hp, by simp⟩

end Chain

/-! ## An `opening_queries` specialization -/

/-- `opening_queries`' body before its `ret`. -/
def osIQPre (loop : String) : List Stmt :=
  [.atom (.const (.n 6) (word 2 0 0)), .atom (.mul (.n 7) (.n 5) (.n 6)),
    .atom (.hint (.allocDyn (.n 8) (.n 7))), .atom (.const (.n 9) (word 0 0 0)),
    .atom (.load (.n 9) (.n 8) 0), .atom (.const (.n 10) (word 1 0 0)),
    .atom (.add (.n 11) (.n 10) (.n 5)), .atom (.const (.n 12) (word 1 0 0)),
    .callIf (.n 11) loop [.n 12, .n 5, .n 4, .n 8, .n 2, .n 3, .n 1, .n 0],
    .atom (.mul (.n 13) (.n 8) (.n 5)), .atom (.load (.n 14) (.n 13) 0)]

theorem osIQPre_body (loop : String) : oqBody loop = osIQPre loop ++ [.ret [.n 14]] := rfl

/-- The loop helper's arguments from `opening_queries`' `A` at `p`. -/
def osIQRest (fs : String → ℕ) (q : String) (p : ℕ) (A : List E) : List E :=
  [A.getD 5 0, A.getD 4 0, ofK (Parameters.gpow (p + fs q)), A.getD 2 0, A.getD 3 0, A.getD 1 0, A.getD 0 0]

section Q

variable {S : BlakeSem} {rd : Reader} {fs : String → ℕ} {cert : String → V → ℕ} {H : Inst → ℕ → E × E}
  {L : String} {lf : Fn} {pre : List Stmt} {c : V} {m k2 : ℕ}

/-- **An `opening_queries` specialization's valid placed tree**: its node, then its loop helper's
chain from `1`, after its query sums' buffer. -/
theorem osI_q {q : String} {fn : Fn} (hf : coreProgram.find? q = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]) (hb : fn.body = oqBody L)
    (hlq : coreProgram.loop q = false) (hL : OsILoop L lf pre c m k2) {t : Tree} {A rets : List E}
    {p : ℕ} {hdr : E × E} (hn : t.name = q) (hv : t.ValidB S coreProgram rd A rets)
    (hpl : t.Placed coreProgram fs cert p) :
    ∀ I ∈ t.insts fs coreProgram.loop H p hdr,
      (I.t = t ∧ I.fp = p) ∨ OsIChainAt L lf fs 1 (osIQRest fs q p A) (p + fs q + t.bufs.sum) I := by
  match t, hn, hv with
  | .node g σ bufs kids, hn, hv =>
    simp only [Tree.name] at hn
    subst hn
    have hb' : fn.body = osIQPre L ++ [.ret [.n 14]] := hb
    obtain ⟨σ', bufs', kids', he, hpm, hw, -, hes, hk⟩ :=
      osL_node (S := S) hf hb' (by rfl) (rfl : Tree.name (.node g σ bufs kids) = g) hv
    simp only [Memory.Tree.node.injEq] at he
    obtain ⟨-, rfl, rfl, rfl⟩ := he
    have hcalls : (osIQPre L).filterMap Main.Stmt.callS =
        [(some (.n 11), L, [.n 12, .n 5, .n 4, .n 8, .n 2, .n 3, .n 1, .n 0], [])] := rfl
    have hal : (osIQPre L).filterMap Main.Stmt.allocSz = [(.n 8, .inr (.n 7))] := rfl
    obtain ⟨i1, -, -, -⟩ := Main.straight_parts σ (osIQPre L) rfl
    rw [hcalls] at hk
    simp only [List.map_cons, List.map_nil, Main.mkCall] at hk
    rw [hp] at hpm
    have hA : A = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] := by rw [← hpm]; rfl
    have hat : ∀ a, Stmt.atom a ∈ osIQPre L → a.HoldsB S rd σ := fun a ha => hes _ (mem_slEvs_of ha)
    have c12 := hat (.const (.n 12) (word 1 0 0)) (by simp [osIQPre])
    simp only [Atom.HoldsB, word_one] at c12
    rw [placed_node, events_node hf hw] at hpl
    obtain ⟨hNA, hPK⟩ := hpl
    have hNA1 := hNA.1
    rw [i1, hal] at hNA1
    simp only [List.map_cons, List.map_nil] at hNA1
    obtain ⟨s, rfl⟩ : ∃ s, bufs = [s] := by
      have hl := congrArg List.length hNA1
      simp only [List.length_cons, List.length_nil, List.length_map, length_bases] at hl
      match bufs, hl with
      | [s], _ => exact ⟨s, rfl⟩
    have hbb : bufBase fs coreProgram.loop p g (kids.map (Tree.total fs)) = p + fs g := by
      simp [bufBase, hlq]
    simp only [bases, hbb, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hNA1
    intro I hI
    rw [insts_node, List.mem_cons] at hI
    rcases hI with rfl | hI
    · exact .inl ⟨rfl, rfl⟩
    right
    match kids, hk with
    | [k], ⟨hkn, hkv, _⟩ =>
      have hkp : kidPos fs coreProgram.loop p g [s] [k.total fs] = [p + fs g + s] := by
        simp [kidPos, hlq, bufBase, bases]
      simp only [List.map_cons, List.map_nil, hkp] at hPK hI
      rw [instsKids_cons, instsKids_nil, List.append_nil] at hI
      rw [placedKids_cons] at hPK
      have hargs : ([.n 12, .n 5, .n 4, .n 8, .n 2, .n 3, .n 1, .n 0] : List V).map σ =
          1 :: osIQRest fs g p A := by
        simp only [List.map_cons, List.map_nil, c12, osIQRest, hA, hNA1]
        rfl
      have hk' : (∃ rets, k.ValidB S coreProgram rd (1 :: osIQRest fs g p A) rets) ∨
          ((∃ f σ', k = .phantom f σ') ∧ Phantom coreProgram k (1 :: osIQRest fs g p A)) := by
        by_cases ht : σ (.n 11) = 0
        · simp only [ht, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, hargs] at hkv
          exact .inr hkv
        · simp only [ht, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, hargs, List.map_nil] at hkv
          exact .inl ⟨_, hkv⟩
      have := osI_chain (fs := fs) (cert := cert) (H := H) hL k 1 (osIQRest fs g p A) _ _ hkn hk' hPK.1 I hI
      simpa [Tree.bufs] using this

end Q

end
end LeanVM.Guest.B1
