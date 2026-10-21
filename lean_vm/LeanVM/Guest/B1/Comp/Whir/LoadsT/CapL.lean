/-
  LeanVM.Guest.B1.Comp.Whir.LoadsT.CapL

  `verify_merkle_cap__L{cd}`'s valid trees load the cap's cells of every node the flags reach:
  the root by the body, the interior nodes by the loop's iterations.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LoadsT.KidsL
public import LeanVM.Guest.B1.Whir.Cap

/-!
# `verify_merkle_cap` loads its cap's cells

The loop's body (`capLoopBody`) is not straight: each side branches on the child's flag. Its
statements are atoms and branches between atom runs (`vmcL_stI`); such a run walks to the events
`vmcL_evs`, a branch's taken arm's atoms among them (`vmcL_walk`, `vmcL_mem_else`), and sets up no
frame (`vmcL_calls`).

* `vmcL_side`: a side whose child `g^p` is flagged loads the cap's four cells at `4p ..< 4p + 4`;
* `vmcL_loop`: the loop's valid trees from `g^j` to `g^m` load those of every flagged node
  `p ∈ [2j, 2m)`;
* `vmc_capLoads`: every valid tree of `verify_merkle_cap__L{cd}`, `4 ≤ cd ≤ 8`, loads the cap's
  cells of the root and of every flagged interior node.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- An atom statement. -/
def vmcL_isAtom : Stmt → Bool
  | .atom _ => true
  | _ => false

/-- A statement of a loop body: an atom, or a branch between atom runs. -/
def vmcL_stI : Stmt → Bool
  | .atom _ => true
  | .ite _ z n => z.all vmcL_isAtom && n.all vmcL_isAtom
  | _ => false

/-- The events of such a statement under `σ`. -/
noncomputable def vmcL_evs (σ : Val) : Stmt → List Ev
  | .atom a => [.atom a]
  | .ite c z n => .inK c :: (if σ c = 0 then z else n).flatMap (Main.slEvs σ)
  | _ => []

theorem vmcL_pre_pre (es es' : List Ev) (o : Out) : (o.pre es').pre es = o.pre (es ++ es') := by
  cases o <;> simp [Out.pre]

theorem vmcL_pre_nil (o : Out) : o.pre [] = o := by
  cases o <;> simp [Out.pre]

theorem vmcL_straight_of_atoms : ∀ l : List Stmt, l.all vmcL_isAtom = true →
    l.all Main.Stmt.straight = true
  | [], _ => rfl
  | .atom _ :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h ⊢
    exact ⟨rfl, vmcL_straight_of_atoms l h.2⟩
  | .call .. :: _, h | .callIf .. :: _, h | .ite .. :: _, h | .match_ .. :: _, h
  | .dispatch .. :: _, h | .ret _ :: _, h => by simp [vmcL_isAtom] at h

/-- **A run of atoms and branches walks to its events.** -/
theorem vmcL_walk (σ : Val) : ∀ (pre rest : List Stmt), pre.all vmcL_stI = true →
    walk σ (pre ++ rest) = (walk σ rest).pre (pre.flatMap (vmcL_evs σ))
  | [], rest, _ => by rw [List.nil_append, List.flatMap_nil, vmcL_pre_nil]
  | s :: pre, rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, vmcL_walk σ pre rest h.2, List.flatMap_cons]
    match s, h.1 with
    | .atom a, _ => simp only [walk1, Out.seq, vmcL_pre_pre, vmcL_evs]
    | .ite c z n, hzn =>
      simp only [vmcL_stI, Bool.and_eq_true] at hzn
      by_cases hc : σ c = 0
      · cases walk σ rest <;> simp [walk1, hc, Main.walk_straight_fall σ z (vmcL_straight_of_atoms z hzn.1),
          Out.pre, Out.seq, vmcL_evs]
      · cases walk σ rest <;> simp [walk1, hc, Main.walk_straight_fall σ n (vmcL_straight_of_atoms n hzn.2),
          Out.pre, Out.seq, vmcL_evs]

theorem vmcL_evs_kind (σ : Val) : ∀ (s : Stmt), vmcL_stI s = true → ∀ e ∈ vmcL_evs σ s,
    (∃ a, e = .atom a) ∨ ∃ c, e = .inK c
  | .atom a, _, e, he => .inl ⟨a, List.mem_singleton.mp he⟩
  | .ite c z n, h, e, he => by
    simp only [vmcL_stI, Bool.and_eq_true] at h
    simp only [vmcL_evs, List.mem_cons] at he
    rcases he with rfl | he
    · exact .inr ⟨c, rfl⟩
    · obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
      have ha : vmcL_isAtom s = true := by
        by_cases hc : σ c = 0
        · simp only [hc, ↓reduceIte] at hs; exact List.all_eq_true.mp h.1 s hs
        · simp only [hc, ↓reduceIte] at hs; exact List.all_eq_true.mp h.2 s hs
      match s, ha with
      | .atom a, _ => exact .inl ⟨a, List.mem_singleton.mp he⟩

/-- **Such a run sets up no frame.** -/
theorem vmcL_calls (σ : Val) (pre : List Stmt) (h : pre.all vmcL_stI = true) :
    calls (pre.flatMap (vmcL_evs σ)) = [] := by
  rw [calls, List.filterMap_eq_nil_iff]
  intro e he
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  rcases vmcL_evs_kind σ s (List.all_eq_true.mp h s hs) e he with ⟨a, rfl⟩ | ⟨c, rfl⟩ <;> rfl

theorem vmcL_mem_atom {σ : Val} {pre : List Stmt} {a : Atom} (h : Stmt.atom a ∈ pre) :
    Ev.atom a ∈ pre.flatMap (vmcL_evs σ) :=
  List.mem_flatMap.mpr ⟨_, h, List.mem_singleton_self _⟩

/-- **A taken branch's atoms are events.** -/
theorem vmcL_mem_else {σ : Val} {pre : List Stmt} {c : V} {z n : List Stmt} {a : Atom}
    (h : Stmt.ite c z n ∈ pre) (hc : σ c ≠ 0) (ha : Stmt.atom a ∈ n) :
    Ev.atom a ∈ pre.flatMap (vmcL_evs σ) := by
  refine List.mem_flatMap.mpr ⟨_, h, ?_⟩
  simp only [vmcL_evs, hc, ↓reduceIte, List.mem_cons]
  exact .inr (mem_slEvs_of ha)

/-- The loop's body before its call. -/
def vmcLP : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0))] ++ capSideT (.n 2) (.n 3) (.n 0) (.n 4) 5 ++
    [.atom (.mul (.n 27) (.n 0) (.n 0)), .atom (.const (.n 28) (word 2 0 0)),
      .atom (.mul (.n 29) (.n 27) (.n 28))] ++
    capSideT (.n 2) (.n 3) (.n 0) (.n 29) 30 ++
    [.atom (.const (.n 52) (word 2 0 0)), .atom (.mul (.n 53) (.n 0) (.n 52)),
      .atom (.add (.n 54) (.n 53) (.n 1)), .atom (.const (.n 55) (word 2 0 0)),
      .atom (.mul (.n 56) (.n 0) (.n 55))]

theorem vmcLP_body (loop : String) :
    capLoopBody loop = vmcLP ++ [.callIf (.n 54) loop [.n 56, .n 1, .n 2, .n 3], .ret []] := by
  simp [capLoopBody, vmcLP]

theorem vmcLP_stI : vmcLP.all vmcL_stI = true := rfl

/-- The cap's cell `4p + i`, through `cap·g^(4p)` at `i`. -/
theorem vmcL_addr {cap : E} (hcap : IsInK cap) (p i : ℕ) :
    (cap * gen ^ (4 * p)).limb 0 * Parameters.gpow i = cap.limb 0 * Parameters.gpow (4 * p + i) := by
  rw [gen_pow_eq_ofK, limb0_mul_ofK hcap, mul_assoc, Parameters.gpow, Parameters.gpow,
    Parameters.gpow, ← pow_add]

/-- A load of word `i` through `cap·g^(4p)` is the cap's cell `4p + i`, loaded. -/
theorem vmcL_cell {S : BlakeSem} {rd : Reader} {σ : Val} {es : List Ev} {cap : E} (hcap : IsInK cap)
    {d q : V} {p i : ℕ} (hes : ∀ e ∈ es, e.HoldsB S rd σ) (hm : Ev.atom (.load d q i) ∈ es)
    (hq : σ q = cap * gen ^ (4 * p)) :
    (cap.limb 0 * Parameters.gpow (4 * p + i), memAt rd cap (4 * p + i)) ∈ evLoadEqns σ es := by
  have hl : LoadHolds rd (σ q) i (σ d) := hes _ hm
  rw [hq, loadHolds_mul_gen_pow] at hl
  have h := mem_evLoadEqns (σ := σ) hm
  rwa [hq, vmcL_addr hcap, ← memAt_of_load hl] at h

/-- **A side whose child `g^p` is flagged loads the cap's four cells at `4p`.** -/
theorem vmcL_side {S : BlakeSem} {rd : Reader} {σ : Val} {pre : List Stmt} {fl cp x c : V} {b : ℕ}
    {flags cap : E} {p : ℕ} (hsub : ∀ s ∈ capSideT fl cp x c b, s ∈ pre)
    (hes : ∀ e ∈ pre.flatMap (vmcL_evs σ), e.HoldsB S rd σ) (hfl : σ fl = flags) (hcp : σ cp = cap)
    (hc : σ c = gen ^ p) (hcap : IsInK cap) (hf : memAt rd flags p ≠ 0) :
    ∀ i < 4, (cap.limb 0 * Parameters.gpow (4 * p + i), memAt rd cap (4 * p + i)) ∈
      evLoadEqns σ (pre.flatMap (vmcL_evs σ)) := by
  have hat : ∀ a, Stmt.atom a ∈ pre → a.HoldsB S rd σ := fun a ha => hes _ (vmcL_mem_atom ha)
  have m0 := hat (.mul (.n b) fl c) (hsub _ (by simp [capSideT]))
  have m1 := hat (.load (.n (b + 1)) (.n b) 0) (hsub _ (by simp [capSideT]))
  simp only [Atom.HoldsB] at m0 m1
  rw [m0, hfl, hc, loadHolds_mul_gen_pow, Nat.add_zero] at m1
  have hne : σ (.n (b + 1)) ≠ 0 := by rw [← memAt_of_load m1]; exact hf
  have hite := hsub (.ite (.n (b + 1)) [] ([.atom (.const (.n (b + 2)) (word 1 0 0)),
    .atom (.mul (.n (b + 3)) fl x), .atom (.load (.n (b + 2)) (.n (b + 3)) 0)] ++
      hashCapNodeT cp c (b + 4))) (by simp [capSideT])
  have hH : ∀ a, Stmt.atom a ∈ hashCapNodeT cp c (b + 4) →
      Ev.atom a ∈ pre.flatMap (vmcL_evs σ) := fun a ha =>
    vmcL_mem_else hite hne (List.mem_append_right _ ha)
  have a0 := hes _ (hH (.mul (.n (b + 4)) c c) (by simp [hashCapNodeT]))
  have a1 := hes _ (hH (.mul (.n (b + 4 + 1)) (.n (b + 4)) (.n (b + 4))) (by simp [hashCapNodeT]))
  have a2 := hes _ (hH (.mul (.n (b + 4 + 2)) cp (.n (b + 4 + 1))) (by simp [hashCapNodeT]))
  simp only [Ev.HoldsB, Atom.HoldsB] at a0 a1 a2
  have hq : σ (.n (b + 4 + 2)) = cap * gen ^ (4 * p) := by
    rw [a2, a1, a0, hcp, hc, ← pow_add, ← pow_add]; congr 2; ring
  intro i hi
  interval_cases i
  · exact vmcL_cell hcap hes (hH (.load (.n (b + 4 + 3)) (.n (b + 4 + 2)) 0) (by simp [hashCapNodeT])) hq
  · exact vmcL_cell hcap hes (hH (.load (.n (b + 4 + 4)) (.n (b + 4 + 2)) 1) (by simp [hashCapNodeT])) hq
  · exact vmcL_cell hcap hes (hH (.load (.n (b + 4 + 5)) (.n (b + 4 + 2)) 2) (by simp [hashCapNodeT])) hq
  · exact vmcL_cell hcap hes (hH (.load (.n (b + 4 + 6)) (.n (b + 4 + 2)) 3) (by simp [hashCapNodeT])) hq

/-- **A valid tree of the loop**: its node, its path the body's events holding, its one callee
the next iteration's frame. -/
theorem vmcL_loopNode {S : BlakeSem} {rd : Reader} {loop : String} {lf : Fn}
    (hlf : coreProgram.find? loop = some lf) (hlb : lf.body = capLoopBody loop) {t : Tree}
    {args rets : List E} (hn : t.name = loop) (hv : t.ValidB S coreProgram rd args rets) :
    ∃ σ bufs kids, t = Memory.Tree.node loop σ bufs kids ∧ lf.params.map σ = args ∧
      walk σ lf.body = .ret (vmcLP.flatMap (vmcL_evs σ) ++ [.inK (.n 54),
        if σ (.n 54) = 0 then .skip loop [.n 56, .n 1, .n 2, .n 3]
        else .call loop [.n 56, .n 1, .n 2, .n 3] []]) [] ∧
      (∀ e ∈ vmcLP.flatMap (vmcL_evs σ), e.HoldsB S rd σ) ∧
      Tree.KidsValidB S coreProgram rd σ [⟨loop, [.n 56, .n 1, .n 2, .n 3], [], decide (σ (.n 54) ≠ 0)⟩]
        kids := by
  match t, hn, hv with
  | .node g σ bufs kids, hn, hv =>
    simp only [Tree.name] at hn
    subst hn
    obtain ⟨fn', hf', hp, es, vs', hw, -, hes, hk⟩ := hv
    rw [hlf, Option.some.injEq] at hf'
    subst hf'
    have hw' : walk σ lf.body = .ret (vmcLP.flatMap (vmcL_evs σ) ++ [.inK (.n 54),
        if σ (.n 54) = 0 then .skip g [.n 56, .n 1, .n 2, .n 3]
        else .call g [.n 56, .n 1, .n 2, .n 3] []]) [] := by
      rw [hlb, vmcLP_body, vmcL_walk σ _ _ vmcLP_stI]
      by_cases h0 : σ (.n 54) = 0 <;> simp [walk, walk1, h0, Out.seq, Out.pre]
    rw [hw'] at hw
    cases hw
    refine ⟨σ, bufs, kids, rfl, hp, hw', fun e he => hes e (List.mem_append_left _ he), ?_⟩
    have hc : calls (vmcLP.flatMap (vmcL_evs σ) ++ [.inK (.n 54),
        if σ (.n 54) = 0 then .skip g [.n 56, .n 1, .n 2, .n 3]
        else .call g [.n 56, .n 1, .n 2, .n 3] []]) =
        [⟨g, [.n 56, .n 1, .n 2, .n 3], [], decide (σ (.n 54) ≠ 0)⟩] := by
      rw [calls, List.filterMap_append, ← calls, vmcL_calls σ _ vmcLP_stI]
      by_cases h0 : σ (.n 54) = 0 <;> simp [h0, Ev.call?, List.filterMap_cons]
    rw [← hc]; exact hk

/-- **The loop's valid trees from `g^j` load the cap's cells of every flagged node `p ∈ [2j, 2m)`.** -/
theorem vmcL_loop {S : BlakeSem} {loop : String} {lf : Fn} (hlf : coreProgram.find? loop = some lf)
    (hlp : lf.params = [.n 0, .n 1, .n 2, .n 3]) (hlb : lf.body = capLoopBody loop) (rd : Reader)
    (m : ℕ) (hm : m < 2 ^ 63) (flags cap : E) (hcap : IsInK cap) :
    ∀ (d j : ℕ) (t : Tree) (rets : List E), j + d = m → j < m → t.name = loop →
      t.ValidB S coreProgram rd [gen ^ j, gen ^ m, flags, cap] rets →
      ∀ p, 2 * j ≤ p → p < 2 * m → memAt rd flags p ≠ 0 → ∀ i < 4,
        (cap.limb 0 * Parameters.gpow (4 * p + i), memAt rd cap (4 * p + i)) ∈ t.loadEqns coreProgram := by
  intro d
  induction d with
  | zero => intro j t rets hjd hj; omega
  | succ d ih =>
    intro j t rets hjd hj hn hv p hp1 hp2 hf i hi
    obtain ⟨σ, bufs, kids, rfl, hp, hw, hes, hk⟩ := vmcL_loopNode (S := S) hlf hlb hn hv
    rw [hlp] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
    obtain ⟨h0, h1, h2, h3, -⟩ := hp
    have hsub : ∀ {l : List Stmt}, (∀ s ∈ l, s ∈ vmcLP) → ∀ s ∈ l, s ∈ vmcLP := fun h => h
    have hnode : ∀ q ∈ evLoadEqns σ (vmcLP.flatMap (vmcL_evs σ)),
        q ∈ (Memory.Tree.node loop σ bufs kids).loadEqns coreProgram := fun q hq =>
      mem_loadEqns_node hlf hw (by rw [evLoadEqns_append]; exact List.mem_append_left _ hq)
    have hat : ∀ a, Stmt.atom a ∈ vmcLP → a.HoldsB S rd σ := fun a ha => hes _ (vmcL_mem_atom ha)
    have c4 := hat (.mul (.n 4) (.n 0) (.n 0)) (by simp [vmcLP])
    have c27 := hat (.mul (.n 27) (.n 0) (.n 0)) (by simp [vmcLP])
    have c28 := hat (.const (.n 28) (word 2 0 0)) (by simp [vmcLP])
    have c29 := hat (.mul (.n 29) (.n 27) (.n 28)) (by simp [vmcLP])
    simp only [Atom.HoldsB] at c4 c27 c28 c29
    rcases Nat.lt_or_ge p (2 * j + 2) with hlt | hge
    · rcases Nat.lt_or_ge p (2 * j + 1) with hlt' | hge'
      · obtain rfl : p = 2 * j := by omega
        refine hnode _ (vmcL_side (fl := .n 2) (cp := .n 3) (x := .n 0) (c := .n 4) (b := 5)
          (hsub fun s hs => by simp only [vmcLP, List.mem_append]; tauto) hes h2 h3 ?_ hcap hf i hi)
        rw [c4, h0, ← pow_add]; congr 1; ring
      · obtain rfl : p = 2 * j + 1 := by omega
        refine hnode _ (vmcL_side (fl := .n 2) (cp := .n 3) (x := .n 0) (c := .n 29) (b := 30)
          (hsub fun s hs => by simp only [vmcLP, List.mem_append]; tauto) hes h2 h3 ?_ hcap hf i hi)
        rw [c29, c27, c28, h0, word_gen, ← pow_add, ← pow_succ]; congr 1; ring
    · have hj1 : j + 1 < m := by omega
      match kids, hk with
      | [kl], ⟨hnl, hvl, _⟩ =>
        have c52 := hat (.const (.n 52) (word 2 0 0)) (by simp [vmcLP])
        have c53 := hat (.mul (.n 53) (.n 0) (.n 52)) (by simp [vmcLP])
        have c54 := hat (.add (.n 54) (.n 53) (.n 1)) (by simp [vmcLP])
        have c55 := hat (.const (.n 55) (word 2 0 0)) (by simp [vmcLP])
        have c56 := hat (.mul (.n 56) (.n 0) (.n 55)) (by simp [vmcLP])
        simp only [Atom.HoldsB] at c52 c53 c54 c55 c56
        have hz : σ (.n 54) ≠ 0 := by
          rw [c54, c53, c52, h0, h1, word_gen, gen_pow_mul_gen]
          exact gen_pow_ne_of_lt (by omega) hm
        simp only [hz, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
          List.map_nil] at hvl
        rw [c56, c55, h0, h1, h2, h3, word_gen, gen_pow_mul_gen] at hvl
        exact mem_loadEqns_kid (List.mem_singleton_self _)
          (ih (j + 1) kl _ (by omega) hj1 hnl hvl p (by omega) hp2 hf i hi)

/-! ## `verify_merkle_cap__L{cd}` -/

/-- `verify_merkle_cap`'s body before its `ret`. -/
def vmcPreL (W : E) (loop : String) : List Stmt :=
  [.atom (.const (.n 2) (word 16 0 0)), .atom (.mul (.n 3) (.n 0) (.n 2)),
    .atom (.load (.n 4) (.n 3) 0), .atom (.load (.n 5) (.n 3) 1), .atom (.load (.n 6) (.n 3) 2),
    .atom (.load (.n 7) (.n 3) 3),
    .atom (.const (.n 8) (word 13503953895743350343 11912009169889063794 0)),
    .atom (.const (.n 9) (word 11170449402626986623 6620516960021240235 0)),
    .atom (.const (.n 10) (word 64 4294967295 0)),
    .atom (.blake2s (.n 4) (.n 5) (.n 6) (.n 7) (.n 8) (.n 9) (.n 11) (.n 12) (.n 10)),
    .atom (.load (.n 11) (.n 0) 2), .atom (.load (.n 12) (.n 0) 3),
    .atom (.const (.n 13) (word 1 0 0)), .atom (.load (.n 13) (.n 1) 1),
    .atom (.const (.n 14) (word 2 0 0)), .atom (.const (.n 15) W), .atom (.add (.n 16) (.n 14) (.n 15)),
    .atom (.const (.n 17) (word 2 0 0)), .atom (.const (.n 18) W),
    .callIf (.n 16) loop [.n 17, .n 18, .n 1, .n 0],
    .atom (.load (.n 19) (.n 0) 2), .atom (.load (.n 20) (.n 0) 3)]

theorem vmcPreL_body (W : E) (loop : String) :
    vmcBody W loop = vmcPreL W loop ++ [.ret [.n 19, .n 20]] := rfl

theorem vmcPreL_straight (W : E) (loop : String) : (vmcPreL W loop).all Main.Stmt.straight = true :=
  rfl

/-- `verify_merkle_cap__L{cd}`'s function and its loop's. -/
def VmcLInst (cd : ℕ) : Prop :=
  ∃ (f lf : Fn) (loop : String), coreProgram.find? ("verify_merkle_cap__L" ++ toString cd) = some f ∧
    f.params = [.n 0, .n 1] ∧ f.body = vmcBody (word (gSquaresBits.getD (cd - 1) 0) 0 0) loop ∧
    coreProgram.find? loop = some lf ∧ lf.params = [.n 0, .n 1, .n 2, .n 3] ∧
    lf.body = capLoopBody loop

set_option maxRecDepth 100000 in
theorem vmcL_inst4 : VmcLInst 4 := by
  rw [VmcLInst, show "verify_merkle_cap__L" ++ toString (4 : ℕ) = "verify_merkle_cap__L4" by
    rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide),
      show Nat.digitChar 4 = '4' from Nat.digitChar_eq_four.mpr rfl]
    decide]
  exact ⟨_, _, "__loop454", Program.find?_of_indexOf? (j := 674) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel), Program.find?_of_indexOf? (j := 1006) (by decide +kernel) rfl,
    rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem vmcL_inst5 : VmcLInst 5 := by
  rw [VmcLInst, show "verify_merkle_cap__L" ++ toString (5 : ℕ) = "verify_merkle_cap__L5" by
    rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide),
      show Nat.digitChar 5 = '5' from Nat.digitChar_eq_five.mpr rfl]
    decide]
  exact ⟨_, _, "__loop433", Program.find?_of_indexOf? (j := 586) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel), Program.find?_of_indexOf? (j := 978) (by decide +kernel) rfl,
    rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem vmcL_inst6 : VmcLInst 6 := by
  rw [VmcLInst, show "verify_merkle_cap__L" ++ toString (6 : ℕ) = "verify_merkle_cap__L6" by
    rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide),
      show Nat.digitChar 6 = '6' from Nat.digitChar_eq_six.mpr rfl]
    decide]
  exact ⟨_, _, "__loop431", Program.find?_of_indexOf? (j := 583) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel), Program.find?_of_indexOf? (j := 975) (by decide +kernel) rfl,
    rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem vmcL_inst7 : VmcLInst 7 := by
  rw [VmcLInst, show "verify_merkle_cap__L" ++ toString (7 : ℕ) = "verify_merkle_cap__L7" by
    rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide),
      show Nat.digitChar 7 = '7' from Nat.digitChar_eq_seven.mpr rfl]
    decide]
  exact ⟨_, _, "__loop456", Program.find?_of_indexOf? (j := 683) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel), Program.find?_of_indexOf? (j := 1008) (by decide +kernel) rfl,
    rfl, stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem vmcL_inst8 : VmcLInst 8 := by
  rw [VmcLInst, show "verify_merkle_cap__L" ++ toString (8 : ℕ) = "verify_merkle_cap__L8" by
    rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide),
      show Nat.digitChar 8 = '8' from Nat.digitChar_eq_eight.mpr rfl]
    decide]
  exact ⟨_, _, "__loop429", Program.find?_of_indexOf? (j := 579) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel), Program.find?_of_indexOf? (j := 972) (by decide +kernel) rfl,
    rfl, stmtsEqb_sound (by decide +kernel)⟩

/-- **Every valid tree of `verify_merkle_cap__L{cd}` loads the cap's cells** of the root and of
every interior node whose flag is set: the root's by the body, the others' by the loop. -/
theorem vmc_capLoads {S : BlakeSem} {cd : ℕ} (h4 : 4 ≤ cd) (h8 : cd ≤ 8) {rd : Reader} {cap flags : E}
    {rets : List E} {t : Tree} (hn : t.name = "verify_merkle_cap__L" ++ toString cd)
    (hv : t.ValidB S coreProgram rd [cap, flags] rets) (hcap : IsInK cap) (_hfl : IsInK flags) :
    ∀ p, 1 ≤ p → p < 2 ^ cd → (p = 1 ∨ memAt rd flags p ≠ 0) → ∀ i < 4,
      (cap.limb 0 * Parameters.gpow (4 * p + i), memAt rd cap (4 * p + i)) ∈ t.loadEqns coreProgram := by
  obtain ⟨f, lf, loop, hf, hp, hb, hlf, hlp, hlb⟩ : VmcLInst cd := by
    interval_cases cd
    exacts [vmcL_inst4, vmcL_inst5, vmcL_inst6, vmcL_inst7, vmcL_inst8]
  set W := word (gSquaresBits.getD (cd - 1) 0) 0 0 with hWd
  have hW : W = gen ^ 2 ^ (cd - 1) := word_gSquares (by simp only [sizeBits]; omega)
  obtain ⟨σ, bufs, kids, rfl, hpar, hw, hes, hk⟩ :=
    nodeS_straight (S := S) hf (hb.trans (vmcPreL_body W loop)) (vmcPreL_straight W loop) hn hv
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨h0, h1, -⟩ := hpar
  have hat : ∀ a, Stmt.atom a ∈ vmcPreL W loop → a.HoldsB S rd σ := fun a ha => hes _ (mem_slEvs_of ha)
  intro p hp1 hp2 hpf i hi
  rcases Nat.eq_or_lt_of_le hp1 with rfl | hlt
  · have c2 := hat (.const (.n 2) (word 16 0 0)) (by simp [vmcPreL])
    have m3 := hat (.mul (.n 3) (.n 0) (.n 2)) (by simp [vmcPreL])
    simp only [Atom.HoldsB] at c2 m3
    have hq : σ (.n 3) = cap * gen ^ (4 * 1) := by rw [m3, c2, h0, word_sixteen]
    refine mem_loadEqns_node hf hw ?_
    interval_cases i
    · exact vmcL_cell hcap hes (mem_slEvs_of (by simp [vmcPreL] :
        Stmt.atom (.load (.n 4) (.n 3) 0) ∈ vmcPreL W loop)) hq
    · exact vmcL_cell hcap hes (mem_slEvs_of (by simp [vmcPreL] :
        Stmt.atom (.load (.n 5) (.n 3) 1) ∈ vmcPreL W loop)) hq
    · exact vmcL_cell hcap hes (mem_slEvs_of (by simp [vmcPreL] :
        Stmt.atom (.load (.n 6) (.n 3) 2) ∈ vmcPreL W loop)) hq
    · exact vmcL_cell hcap hes (mem_slEvs_of (by simp [vmcPreL] :
        Stmt.atom (.load (.n 7) (.n 3) 3) ∈ vmcPreL W loop)) hq
  · have hpf' : memAt rd flags p ≠ 0 := hpf.resolve_left (by omega)
    have hm1 : 1 < 2 ^ (cd - 1) := Nat.one_lt_two_pow (by omega)
    have hm63 : 2 ^ (cd - 1) < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) (by omega)
    have hpow : 2 ^ cd = 2 * 2 ^ (cd - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ cd)]
    have c14 := hat (.const (.n 14) (word 2 0 0)) (by simp [vmcPreL])
    have c15 := hat (.const (.n 15) W) (by simp [vmcPreL])
    have a16 := hat (.add (.n 16) (.n 14) (.n 15)) (by simp [vmcPreL])
    have c17 := hat (.const (.n 17) (word 2 0 0)) (by simp [vmcPreL])
    have c18 := hat (.const (.n 18) W) (by simp [vmcPreL])
    simp only [Atom.HoldsB] at c14 c15 a16 c17 c18
    have hz : σ (.n 16) ≠ 0 := by
      rw [a16, c14, c15, hW, word_gen]
      have := gen_pow_ne_of_lt hm1 hm63
      rwa [pow_one] at this
    have hc : (⟨loop, [.n 17, .n 18, .n 1, .n 0], [], decide (σ (.n 16) ≠ 0)⟩ : Call) ∈
        ((vmcPreL W loop).filterMap Main.Stmt.callS).map (Main.mkCall σ) :=
      List.mem_map.mpr ⟨(some (.n 16), loop, [.n 17, .n 18, .n 1, .n 0], []),
        List.mem_filterMap.mpr ⟨_, (by simp [vmcPreL] :
          Stmt.callIf (.n 16) loop [.n 17, .n 18, .n 1, .n 0] ∈ vmcPreL W loop), rfl⟩, rfl⟩
    obtain ⟨kl, hkl, hnl, hvl⟩ := osL_kidOf hk _ hc (by simp [hz])
    simp only [List.map_cons, List.map_nil] at hvl
    rw [c17, c18, h1, h0, hW, word_gen] at hvl
    exact mem_loadEqns_kid hkl (vmcL_loop hlf hlp hlb rd _ hm63 flags cap hcap (2 ^ (cd - 1) - 1) 1
      kl [] (by omega) hm1 hnl (by rw [pow_one]; exact hvl) p (by omega) (by omega) hpf' i hi)

end
end LeanVM.Guest.B1
