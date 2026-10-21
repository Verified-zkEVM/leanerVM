/-
  LeanVM.Guest.Memory.RetempB

  Re-choosing the range-check temporaries of a call tree (`Retemp.lean`) under any
  semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.Retemp
public import LeanVM.Guest.Memory.RegionsB

/-!
# Re-choosing temporaries under any `BLAKE2S` semantics

`Retemp.lean`'s lemmas with `S : BlakeSem` a parameter: a re-chosen tree stays valid under `S`
(`retempB_valid`), keeps its `HeapBuf`s, placement and loads (`bufsOkB_retemp`, `placedB_retemp`,
`loadsInB_retemp`), and a placed relation moves to another reader and is uniform in the frame
pointer (`relAtInB_transfer`, `relAtInB_uniform_pure`, `relAtInB_uniform_quiet`). The
re-choice itself (`Tree.retemp`) is `Retemp.lean`'s.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem}

/-! ## Congruences -/

section Congr

variable {rd rd0 : Reader} {σ σ' : Val}

/-- An atom's relation depends only on the values it names. -/
theorem atomB_holds_congr : ∀ (a : Atom), (∀ v ∈ atomUses a ++ atomTmps a, σ' v = σ v) →
    (a.HoldsB S rd σ' ↔ a.HoldsB S rd σ)
  | .const d c, h => by simp only [Atom.HoldsB, h d (by simp [atomUses])]
  | .add d x y, h => by
      simp only [Atom.HoldsB, h d (by simp [atomUses]), h x (by simp [atomUses]), h y (by simp [atomUses])]
  | .mul d x y, h => by
      simp only [Atom.HoldsB, h d (by simp [atomUses]), h x (by simp [atomUses]), h y (by simp [atomUses])]
  | .copy d s, h => by simp only [Atom.HoldsB, h d (by simp [atomUses]), h s (by simp [atomUses])]
  | .load d p off, h => by
      simp only [Atom.HoldsB, LoadHolds, h d (by simp [atomUses]), h p (by simp [atomUses])]
  | .assertEq x y, h => by simp only [Atom.HoldsB, h x (by simp [atomUses]), h y (by simp [atomUses])]
  | .assertNe x inv p, h => by
      simp only [Atom.HoldsB, h x (by simp [atomUses]), h inv (by simp [atomUses]),
        h p (by simp [atomUses])]
  | .rangeCheck x y t1 t2 k, h => by
      simp only [Atom.HoldsB, LoadHolds, h x (by simp [atomUses]), h y (by simp [atomUses]),
        h t1 (by simp [atomTmps]), h t2 (by simp [atomTmps]), h k (by simp [atomUses])]
  | .assertInK x y, h => by simp only [Atom.HoldsB, h x (by simp [atomUses]), h y (by simp [atomUses])]
  | .blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md, h => by
      simp only [Atom.HoldsB, h m0 (by simp [atomUses]), h m1 (by simp [atomUses]),
        h m2 (by simp [atomUses]), h m3 (by simp [atomUses]), h cv0 (by simp [atomUses]),
        h cv1 (by simp [atomUses]), h o0 (by simp [atomUses]), h o1 (by simp [atomUses]),
        h md (by simp [atomUses])]
  | .frameAddr p run, h => by
      have hp := h p (by simp [atomUses])
      have hr : ∀ (k : ℕ) (hk : k < run.length), σ' run[k] = σ run[k] := fun k hk =>
        h _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.getElem_mem hk)))
      simp only [Atom.HoldsB, hp]
      exact and_congr_right fun _ => forall_congr' fun k => forall_congr' fun hk =>
        forall_congr' fun w => by rw [hr k hk]
  | .hint _, _ => Iff.rfl

/-- An atom holds on any reader agreeing with one it holds on where it reads. -/
theorem atomB_holds_agree : ∀ (a : Atom), a.HoldsB S rd0 σ →
    (∀ q ∈ atomEqns σ a, rd q.1 = rd0 q.1) → a.HoldsB S rd σ
  | .load .., h, he => ⟨h.1, (he _ (List.mem_singleton_self _)).trans h.2⟩
  | .rangeCheck .., h, he =>
      ⟨⟨h.1.1, (he _ List.mem_cons_self).trans h.1.2⟩, h.2.1,
        ⟨h.2.2.1, (he _ (List.mem_cons_of_mem _ List.mem_cons_self)).trans h.2.2.2⟩⟩
  | .frameAddr p run, h, he => ⟨h.1, fun k hk w hw => h.2 k hk w <| by
      have hm : ((σ p).limb 0 * gpow k, σ run[k]) ∈ atomEqns σ (.frameAddr p run) :=
        List.mem_mapIdx.mpr ⟨k, hk, rfl⟩
      exact (he _ hm).symm.trans hw⟩
  | .const .., h, _ => h
  | .add .., h, _ => h
  | .mul .., h, _ => h
  | .copy .., h, _ => h
  | .assertEq .., h, _ => h
  | .assertNe .., h, _ => h
  | .assertInK .., h, _ => h
  | .blake2s .., h, _ => h
  | .hint _, h, _ => h

end Congr

/-! ## The re-chosen tree -/

variable (P : Core.Program) (fs : String → ℕ) (ν : ℕ → String → Val → V → E)

variable {P fs ν}

/-! ## Validity -/

variable (P fs ν) (rd rd0 : Reader)

variable {P fs ν rd rd0}

section Valid

/-- The events of a re-chosen path hold on the new reader. -/
theorem eventsB_holds_retemp (hF : P.Fresh) {fn : Fn} {f : String} (hf : P.find? f = some fn) {fp : ℕ} {σ : Val}
    {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs)
    (hes : ∀ e ∈ es, e.HoldsB S rd0 σ)
    (hna : ∀ a, Ev.atom a ∈ es → atomTmps a = [] → ∀ q ∈ atomEqns σ a, rd q.1 = rd0 q.1)
    (hrc : ∀ x y t1 t2 k, Ev.atom (.rangeCheck x y t1 t2 k) ∈ es →
      rd ((σ x).limb 0 * gpow 0) = some (ν fp f σ t1) ∧
        rd ((σ y).limb 0 * gpow 0) = some (ν fp f σ t2)) :
    ∀ e ∈ es, e.HoldsB S rd (retempVal P ν fp f σ) := by
  have hag := evAgree_retemp (ν := ν) hF hf (fp := fp) hw
  intro e he
  cases e with
  | atom a =>
      by_cases ht : atomTmps a = []
      · have h1 := atomB_holds_agree a (hes _ he) (hna a he ht)
        refine (atomB_holds_congr a fun v hv => ?_).mpr h1
        rw [ht, List.append_nil] at hv
        exact hag _ he v hv
      · rcases a with _ | _ | _ | _ | _ | _ | _ | ⟨x, y, t1, t2, k⟩ | _ | _ | _ | _ <;>
          simp only [atomTmps, not_true_eq_false] at ht
        have h0 := hes _ he
        obtain ⟨hx, hy⟩ := hrc x y t1 t2 k he
        obtain ⟨ht1, ht2⟩ := mem_temps_of_event hf hw he
        have hu : ∀ v ∈ [x, y, k], retempVal P ν fp f σ v = σ v := fun v hv =>
          hag _ he v (by simpa [Ev.uses, atomUses] using hv)
        refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
        · rw [hu x (by simp)]; exact h0.1.1
        · rw [hu x (by simp), hx]; simp [retempVal, ht1]
        · rw [hu x (by simp), hu y (by simp), hu k (by simp)]; exact h0.2.1
        · rw [hu y (by simp)]; exact h0.2.2.1
        · rw [hu y (by simp), hy]; simp [retempVal, ht2]
  | inK c =>
      have := hes _ he
      simp only [Ev.HoldsB] at this ⊢
      rw [hag _ he c (by simp [Ev.uses])]
      exact this
  | call _ _ _ => trivial
  | skip _ _ => trivial

mutual
/-- **The re-chosen tree is valid** on a reader giving it what it reads. -/
theorem retempB_valid (hF : P.Fresh) : ∀ (t : Tree) (fp : ℕ) {args rets : List E}, t.ValidB S P rd0 args rets →
    t.ReadsAs P fs ν rd rd0 fp → (t.retemp P fs ν fp).ValidB S P rd args rets
  | .node f σ bufs kids, fp, args, rets, ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩, hra => by
      have hag := evAgree_retemp (ν := ν) hF hf (fp := fp) hw
      have hw' : walk (retempVal P ν fp f σ) fn.body = .ret es vs := by
        rw [walk_retemp hF hf]; exact hw
      have hev : (Tree.node f σ bufs kids).events P = es := events_node hf hw
      rw [readsAs_node, hev] at hra
      have hvs : vs.map (retempVal P ν fp f σ) = vs.map σ := by
        have := walk_within (σ := σ) fn.body
        rw [hw] at this
        exact List.map_congr_left fun v hv => retempVal_uses hF hf (this.2.2 v hv)
      rw [retemp_node]
      refine ⟨fn, hf, by rw [retempVal_params hF hf]; exact hp, es, vs, hw', by rw [hvs]; exact hr,
        eventsB_holds_retemp hF hf hw hes hra.1 hra.2.1, ?_⟩
      refine retempKidsB_valid hF kids σ _ (calls es) _ (by rw [length_kidPos, List.length_map])
        (fun c hc v hv => ?_) hk hra.2.2
      obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
      cases e with
      | call g a r =>
          cases hce
          exact hag _ he v (by simpa [Ev.uses] using hv)
      | skip g a =>
          cases hce
          exact hag _ he v (by simpa [Ev.uses] using hv)
      | atom _ => simp [Ev.call?] at hce
      | inK _ => simp [Ev.call?] at hce
  | .phantom .., _, _, _, h, _ => h.elim

/-- `retempB_valid` for the callees. -/
theorem retempKidsB_valid (hF : P.Fresh) : ∀ (ks : List Tree) (σ σ' : Val) (cs : List Call) (ps : List ℕ),
    ps.length = ks.length → (∀ c ∈ cs, ∀ v ∈ c.args ++ c.rets, σ' v = σ v) →
    Tree.KidsValidB S P rd0 σ cs ks → Tree.ReadsAsKids P fs ν rd rd0 ps ks →
      Tree.KidsValidB S P rd σ' cs (Tree.retempKids P fs ν ps ks)
  | [], _, _, [], _, _, _, _, _ => by rw [retempKids_nil]; trivial
  | _ :: _, _, _, _, [], hl, _, _, _ => absurd hl (by simp)
  | k :: ks, σ, σ', c :: cs, p :: ps, hl, hag, ⟨hn, hc, hks⟩, hra => by
      rw [readsAsKids_cons] at hra
      rw [retempKids_cons]
      have hargs : c.args.map σ' = c.args.map σ :=
        List.map_congr_left fun v hv => hag c List.mem_cons_self v (List.mem_append_left _ hv)
      have hrets : c.rets.map σ' = c.rets.map σ :=
        List.map_congr_left fun v hv => hag c List.mem_cons_self v (List.mem_append_right _ hv)
      refine ⟨by rw [name_retemp]; exact hn, ?_, retempKidsB_valid hF ks σ σ' cs ps (by simpa using hl)
        (fun c' hc' => hag c' (List.mem_cons_of_mem _ hc')) hks hra.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc ⊢
        rw [hargs, hrets]
        exact retempB_valid hF k p hc hra.1
      · rw [ite_eq_right ht] at hc ⊢
        obtain ⟨⟨f, σk, rfl⟩, hph⟩ := hc
        rw [retemp_phantom, hargs]
        exact ⟨⟨f, σk, rfl⟩, hph⟩
  | [], _, _, _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, _, _, [], _ :: _, _, _, h, _ => h.elim
end

end Valid

/-! ## What a re-chosen valid tree keeps -/

section Keep

mutual
theorem bufsOkB_retemp (hF : P.Fresh) : ∀ (t : Tree) (fp : ℕ) {args rets : List E}, t.ValidB S P rd0 args rets →
    t.BufsOk P → (t.retemp P fs ν fp).BufsOk P
  | .node f σ bufs kids, fp, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hb => by
      rw [Tree.BufsOk, events_node hf hw] at hb
      rw [retemp_node, Tree.BufsOk, events_retemp hF, events_node hf hw (bufs := bufs) (kids := kids),
        allocs_congr (evAgree_retemp hF hf hw)]
      exact ⟨hb.1, bufsOkKidsB_retemp hF kids σ (calls es) _ hk hb.2⟩
  | .phantom .., fp, _, _, _, _ => by rw [retemp_phantom, Tree.BufsOk]; trivial

theorem bufsOkKidsB_retemp (hF : P.Fresh) : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (ps : List ℕ),
    Tree.KidsValidB S P rd0 σ cs ks → Tree.BufsOkKids P ks →
      Tree.BufsOkKids P (Tree.retempKids P fs ν ps ks)
  | [], _, _, _, _, _ => by rw [retempKids_nil, Tree.BufsOkKids]; trivial
  | _ :: _, _, _, [], _, h => by rw [Tree.retempKids]; exact h
  | k :: ks, σ, c :: cs, p :: ps, ⟨_, hc, hks⟩, hb => by
      rw [Tree.BufsOkKids] at hb
      rw [retempKids_cons, Tree.BufsOkKids]
      refine ⟨?_, bufsOkKidsB_retemp hF ks σ cs ps hks hb.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact bufsOkB_retemp hF k p hc hb.1
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σk, rfl⟩, -⟩ := hc
        rw [retemp_phantom, Tree.BufsOk]; trivial
  | _ :: _, _, [], _ :: _, h, _ => h.elim
end

variable {cert : String → V → ℕ}

mutual
theorem placedB_retemp (hF : P.Fresh) : ∀ (t : Tree) (fp : ℕ) {args rets : List E}, t.ValidB S P rd0 args rets →
    t.Placed P fs cert fp → (t.retemp P fs ν fp).Placed P fs cert fp
  | .node f σ bufs kids, fp, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hp => by
      rw [placed_node, events_node hf hw] at hp
      have hag := evAgree_retemp (ν := ν) hF hf (fp := fp) hw
      rw [retemp_node, placed_node, events_retemp hF, events_node hf hw (bufs := bufs) (kids := kids),
        map_total_retempKids_kidPos]
      refine ⟨⟨by rw [allocDsts_congr hag]; exact hp.1.1, fun q hq => by
        rw [addrs_congr hag q hq]; exact hp.1.2 q hq⟩, ?_⟩
      exact placedKidsB_retemp hF kids σ (calls es) _ hk hp.2
  | .phantom .., fp, _, _, _, _ => by rw [retemp_phantom]; exact placed_phantom

theorem placedKidsB_retemp (hF : P.Fresh) : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (ps : List ℕ),
    Tree.KidsValidB S P rd0 σ cs ks → Tree.PlacedKids P fs cert ps ks →
      Tree.PlacedKids P fs cert ps (Tree.retempKids P fs ν ps ks)
  | [], _, _, _, _, _ => by rw [retempKids_nil]; exact placedKids_nil
  | _ :: _, _, _, [], _, h => by rw [Tree.retempKids]; exact h
  | k :: ks, σ, c :: cs, p :: ps, ⟨_, hc, hks⟩, hp => by
      rw [placedKids_cons] at hp
      rw [retempKids_cons, placedKids_cons]
      refine ⟨?_, placedKidsB_retemp hF ks σ cs ps hks hp.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact placedB_retemp hF k p hc hp.1
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σk, rfl⟩, -⟩ := hc
        rw [retemp_phantom]; exact placed_phantom
  | _ :: _, _, [], _ :: _, h, _ => h.elim
end

mutual
theorem loadsInB_retemp (hF : P.Fresh) : ∀ (t : Tree) (R : ℕ → Prop) (fp : ℕ) {args rets : List E},
    t.ValidB S P rd0 args rets → t.LoadsIn P fs cert R fp → (t.retemp P fs ν fp).LoadsIn P fs cert R fp
  | .node f σ bufs kids, R, fp, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hl => by
      have hag := evAgree_retemp (ν := ν) hF hf (fp := fp) hw
      rw [loadsIn_node, events_node hf hw] at hl
      have hd : ∀ i, (Tree.node f (retempVal P ν fp f σ) bufs
          (Tree.retempKids P fs ν (kidPos fs P.loop fp f bufs (kids.map (Tree.total fs))) kids)).Data
            P fs cert fp i ↔ (Tree.node f σ bufs kids).Data P fs cert fp i := fun i => by
        rw [← retemp_node]; exact data_retemp hF _ fp i
      rw [retemp_node, loadsIn_node, events_retemp hF, events_node hf hw (bufs := bufs) (kids := kids),
        map_total_retempKids_kidPos, loadAddrs_congr hag]
      refine ⟨fun A hA => ?_, ?_⟩
      · obtain ⟨i, hi, h⟩ := hl.1 A hA
        exact ⟨i, hi, h.imp_left (hd i).mpr⟩
      · exact loadsInKids_mono _ _ (fun i h => h.imp_left (hd i).mpr)
          (loadsInKidsB_retemp hF kids σ (calls es) _ _ hk hl.2)
  | .phantom .., _, fp, _, _, _, _ => by rw [retemp_phantom]; exact loadsIn_phantom

theorem loadsInKidsB_retemp (hF : P.Fresh) : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (R : ℕ → Prop)
    (ps : List ℕ), Tree.KidsValidB S P rd0 σ cs ks → Tree.LoadsInKids P fs cert R ps ks →
      Tree.LoadsInKids P fs cert R ps (Tree.retempKids P fs ν ps ks)
  | [], _, _, _, _, _, _ => by rw [retempKids_nil]; exact loadsInKids_nil
  | _ :: _, _, _, _, [], _, h => by rw [Tree.retempKids]; exact h
  | k :: ks, σ, c :: cs, R, p :: ps, ⟨_, hc, hks⟩, hl => by
      rw [loadsInKids_cons] at hl
      rw [retempKids_cons, loadsInKids_cons]
      refine ⟨?_, loadsInKidsB_retemp hF ks σ cs R ps hks hl.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact loadsInB_retemp hF k R p hc hl.1
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σk, rfl⟩, -⟩ := hc
        rw [retemp_phantom]; exact loadsIn_phantom
  | _ :: _, _, [], _, _ :: _, h, _ => h.elim
end

mutual
theorem loadsRB_retemp (hF : P.Fresh) : ∀ (t : Tree) (R : ℕ → Prop) (fp : ℕ) {args rets : List E},
    t.ValidB S P rd0 args rets → t.LoadsR P R → (t.retemp P fs ν fp).LoadsR P R
  | .node f σ bufs kids, R, fp, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hl => by
      rw [Tree.LoadsR, events_node hf hw] at hl
      rw [retemp_node, Tree.LoadsR, events_retemp hF, events_node hf hw (bufs := bufs) (kids := kids),
        loadAddrs_congr (evAgree_retemp hF hf hw)]
      exact ⟨hl.1, loadsRKidsB_retemp hF kids σ (calls es) R _ hk hl.2⟩
  | .phantom .., _, fp, _, _, _, _ => by rw [retemp_phantom, Tree.LoadsR]; trivial

theorem loadsRKidsB_retemp (hF : P.Fresh) : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (R : ℕ → Prop)
    (ps : List ℕ), Tree.KidsValidB S P rd0 σ cs ks → Tree.LoadsRKids P R ks →
      Tree.LoadsRKids P R (Tree.retempKids P fs ν ps ks)
  | [], _, _, _, _, _, _ => by rw [retempKids_nil, Tree.LoadsRKids]; trivial
  | _ :: _, _, _, _, [], _, h => by rw [Tree.retempKids]; exact h
  | k :: ks, σ, c :: cs, R, p :: ps, ⟨_, hc, hks⟩, hl => by
      rw [Tree.LoadsRKids] at hl
      rw [retempKids_cons, Tree.LoadsRKids]
      refine ⟨?_, loadsRKidsB_retemp hF ks σ cs R ps hks hl.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact loadsRB_retemp hF k R p hc hl.1
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σk, rfl⟩, -⟩ := hc
        rw [retemp_phantom, Tree.LoadsR]; trivial
  | _ :: _, _, [], _, _ :: _, h, _ => h.elim
end

end Keep

/-! ## Transfer to another reader -/

section Transfer

variable {cert : String → V → ℕ} {rd rd0 : Reader}

mutual
/-- **A reader agreeing on a tree's region and data gives the re-chosen tree what it reads**,
the temporaries read from it. -/
theorem readsAsB_nuRead (hF : P.Fresh) (hdef : ∀ A, (rd0 A).isSome → (rd A).isSome) :
    ∀ (t : Tree) (R : ℕ → Prop) (fp : ℕ) {args rets : List E}, t.ValidB S P rd0 args rets →
    t.Placed P fs cert fp → t.LoadsIn P fs cert R fp →
    (∀ i, R i ∨ t.Data P fs cert fp i → rd (gpow i) = rd0 (gpow i)) →
    t.ReadsAs P fs (nuRead P rd) rd rd0 fp
  | .node f σ bufs kids, R, fp, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩, hp, hl, hag => by
      have hev : (Tree.node f σ bufs kids).events P = es := events_node hf hw
      rw [readsAs_node, hev]
      rw [placed_node, hev] at hp
      rw [loadsIn_node, hev] at hl
      refine ⟨fun a ha hta q hq => ?_, fun x y t1 t2 k he => ?_, ?_⟩
      · cases a with
        | load d p off =>
            rw [List.mem_singleton.mp hq]
            obtain ⟨i, hi, hd⟩ := hl.1 ((σ p).limb 0 * gpow off) (List.mem_filterMap.mpr ⟨_, ha, rfl⟩)
            simp only
            rw [hi]
            exact hag i hd.symm
        | frameAddr p run =>
            obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hq
            cases run with
            | nil => exact absurd hk (by simp)
            | cons r rs =>
                have hpv := hp.1.2 (p, r) (List.mem_filterMap.mpr ⟨_, ha, rfl⟩)
                simp only at hpv hk ⊢
                rw [hpv, show (ofK (gpow (fp + cert f r))).limb 0 = gpow (fp + cert f r) by simp,
                  show gpow (fp + cert f r) * gpow k = gpow (fp + cert f r + k) by
                    simp only [gpow, pow_add]]
                refine hag _ (Or.inr (data_node.mpr (Or.inl (Or.inr ⟨(r, rs.length + 1),
                  by rw [hev]; exact List.mem_filterMap.mpr ⟨_, ha, rfl⟩, ?_, ?_⟩))))
                · simp only; omega
                · simp only [List.length_cons] at hk ⊢; omega
        | rangeCheck _ _ _ _ _ => simp [atomTmps] at hta
        | const _ _ => exact (List.not_mem_nil hq).elim
        | add _ _ _ => exact (List.not_mem_nil hq).elim
        | mul _ _ _ => exact (List.not_mem_nil hq).elim
        | copy _ _ => exact (List.not_mem_nil hq).elim
        | assertEq _ _ => exact (List.not_mem_nil hq).elim
        | assertNe _ _ _ => exact (List.not_mem_nil hq).elim
        | assertInK _ _ => exact (List.not_mem_nil hq).elim
        | blake2s _ _ _ _ _ _ _ _ _ => exact (List.not_mem_nil hq).elim
        | hint _ => exact (List.not_mem_nil hq).elim
      · have h0 := hes _ he
        have hmem : Ev.atom (.rangeCheck x y t1 t2 k) ∈ (Tree.node f σ [] []).events P := by
          show Ev.atom _ ∈ (Tree.node f σ bufs kids).events P
          rw [hev]; exact he
        have side : ∀ (t' : V) (A : K) (w0 : E), RcRead P f σ t' A → rd0 A = some w0 →
            rd A = some (nuRead P rd fp f σ t') := by
          intro t' A w0 hr h0'
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hdef A (by rw [h0']; rfl))
          rw [hw, nuRead_eq hF hr hw]
        exact ⟨side t1 _ _ ⟨x, y, t1, t2, k, hmem, Or.inl ⟨rfl, rfl⟩⟩ h0.1.2,
          side t2 _ _ ⟨x, y, t1, t2, k, hmem, Or.inr ⟨rfl, rfl⟩⟩ h0.2.2.2⟩
      · exact readsAsKidsB_nuRead hF hdef kids σ (calls es) _ _ hk hp.2 hl.2 fun i hi =>
          hi.elim (fun h => h.elim (fun hd => hag i (Or.inr hd)) fun hr => hag i (Or.inl hr))
            fun hd => hag i (Or.inr (data_node.mpr (Or.inr hd)))
  | .phantom .., _, _, _, _, h, _, _, _ => h.elim

/-- `readsAsB_nuRead` for the callees. -/
theorem readsAsKidsB_nuRead (hF : P.Fresh) (hdef : ∀ A, (rd0 A).isSome → (rd A).isSome) :
    ∀ (ks : List Tree) (σ : Val) (cs : List Call) (R : ℕ → Prop) (ps : List ℕ),
    Tree.KidsValidB S P rd0 σ cs ks → Tree.PlacedKids P fs cert ps ks →
    Tree.LoadsInKids P fs cert R ps ks →
    (∀ i, R i ∨ Tree.DataKids P fs cert ps ks i → rd (gpow i) = rd0 (gpow i)) →
    Tree.ReadsAsKids P fs (nuRead P rd) rd rd0 ps ks
  | [], _, _, _, ps, _, _, _, _ => by cases ps <;> (rw [Tree.ReadsAsKids]; trivial)
  | _ :: _, _, _, _, [], _, _, _, _ => by rw [Tree.ReadsAsKids]; trivial
  | k :: ks, σ, c :: cs, R, p :: ps, ⟨_, hc, hks⟩, hp, hl, hag => by
      rw [placedKids_cons] at hp
      rw [loadsInKids_cons] at hl
      rw [readsAsKids_cons]
      refine ⟨?_, readsAsKidsB_nuRead hF hdef ks σ cs R ps hks hp.2 hl.2 fun i hi =>
        hag i (hi.imp_right fun h => dataKids_cons.mpr (Or.inr h))⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact readsAsB_nuRead hF hdef k R p hc hp.1 hl.1 fun i hi =>
          hag i (hi.imp_right fun h => dataKids_cons.mpr (Or.inl h))
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σk, rfl⟩, -⟩ := hc
        rw [Tree.ReadsAs]; trivial
  | _ :: _, _, [], _, _ :: _, h, _, _, _ => h.elim
end

/-- **A tree moves to another reader** agreeing with its own on its region and data and defined
wherever it is: its temporaries re-read, it keeps everything else. -/
theorem transferB (hF : P.Fresh) (hdef : ∀ A, (rd0 A).isSome → (rd A).isSome) {t : Tree}
    {R : ℕ → Prop} {fp : ℕ} {args rets : List E} (hv : t.ValidB S P rd0 args rets)
    (hp : t.Placed P fs cert fp) (hl : t.LoadsIn P fs cert R fp)
    (hag : ∀ i, R i ∨ t.Data P fs cert fp i → rd (gpow i) = rd0 (gpow i)) :
    (t.retemp P fs (nuRead P rd) fp).name = t.name ∧
      (t.retemp P fs (nuRead P rd) fp).ValidB S P rd args rets ∧
      (t.BufsOk P → (t.retemp P fs (nuRead P rd) fp).BufsOk P) ∧
      (t.retemp P fs (nuRead P rd) fp).Placed P fs cert fp ∧
      (t.retemp P fs (nuRead P rd) fp).total fs = t.total fs ∧
      (t.retemp P fs (nuRead P rd) fp).LoadsIn P fs cert R fp ∧
      ∀ i, (t.retemp P fs (nuRead P rd) fp).Data P fs cert fp i ↔ t.Data P fs cert fp i :=
  ⟨name_retemp fp t, retempB_valid hF t fp hv (readsAsB_nuRead hF hdef t R fp hv hp hl hag),
    bufsOkB_retemp hF t fp hv, placedB_retemp hF t fp hv hp, total_retemp t fp,
    loadsInB_retemp hF t R fp hv hl, data_retemp hF t fp⟩

/-- **The placed relation of a tree on every reader** agreeing on its region and data. -/
theorem relAtInB_transfer (hF : P.Fresh) {t : Tree} {R D : ℕ → Prop} {fp : ℕ} {f : String}
    {args rets : List E} (hn : t.name = f) (hv : t.ValidB S P rd0 args rets) (hb : t.BufsOk P)
    (hp : t.Placed P fs cert fp) (hl : t.LoadsIn P fs cert R fp)
    (hD : ∀ i, D i → t.Data P fs cert fp i) (rd : Reader)
    (hag : ∀ i, R i ∨ t.Data P fs cert fp i → rd (gpow i) = rd0 (gpow i))
    (hdef : ∀ A, (rd0 A).isSome → (rd A).isSome) :
    RelAtInB S P fs cert rd R D fp (t.total fs) f args rets := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := transferB (rd := rd) hF hdef hv hp hl hag
  exact ⟨_, h1.trans hn, h2, h3 hb, h4, h5, h6, fun i hi => (h7 i).mpr (hD i hi)⟩

theorem RelAtInB.mono {R R' D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAtInB S P fs cert rd R D fp n f args rets) (hR : ∀ i, R i → R' i) :
    RelAtInB S P fs cert rd R' D fp n f args rets :=
  let ⟨t, hn, hv, hb, hp, ht, hl, hd⟩ := h
  ⟨t, hn, hv, hb, hp, ht, loadsIn_mono t fp hR hl, hd⟩

/-! ### Pure functions on every reader -/

section Pure

variable {Sz : List String}

mutual
/-- A valid tree of a function of a pure set has no data. -/
theorem notB_data_of_pure (hS : P.PureIn Sz) : ∀ (t : Tree) {args rets : List E},
    t.ValidB S P rd0 args rets → t.BufsOk P → t.name ∈ Sz → ∀ fp i, ¬ t.Data P fs cert fp i
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hb, hn, fp, i => by
      have hpure : ∀ e ∈ es, e.pure Sz := by
        have := walk_pure (σ := σ) fn.body (hS f hn fn hf)
        rwa [hw] at this
      rw [Tree.BufsOk, events_node hf hw, allocs_pure hpure] at hb
      obtain ⟨rfl, hkb⟩ := hb
      rw [data_node, events_node hf hw]
      rintro ((⟨q, hq, -⟩ | ⟨q, hq, -⟩) | hd)
      · simp at hq
      · rw [runs_pure hpure] at hq; exact List.not_mem_nil hq
      · exact notB_dataKids_of_pure hS kids σ (calls es) hk hkb (calls_pure hpure) _ i hd
  | .phantom .., _, _, h, _, _, _, _ => h.elim

/-- `notB_data_of_pure` for the callees. -/
theorem notB_dataKids_of_pure (hS : P.PureIn Sz) : ∀ (ks : List Tree) (σ : Val) (cs : List Call),
    Tree.KidsValidB S P rd0 σ cs ks → Tree.BufsOkKids P ks → (∀ c ∈ cs, c.f ∈ Sz) →
      ∀ ps i, ¬ Tree.DataKids P fs cert ps ks i
  | [], _, _, _, _, _, _, i => not_dataKids_nil
  | _ :: _, _, _, _, _, _, [], i => by rw [Tree.DataKids]; exact id
  | k :: ks, σ, c :: cs, ⟨hn, hc, hks⟩, hb, hS', p :: ps, i => by
      rw [Tree.BufsOkKids] at hb
      rw [dataKids_cons]
      rintro (hd | hd)
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact notB_data_of_pure hS k hc hb.1 (hn ▸ hS' c List.mem_cons_self) p i hd
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          exact data_phantom hd
      · exact notB_dataKids_of_pure hS ks σ cs hks hb.2
          (fun c' h => hS' c' (List.mem_cons_of_mem _ h)) ps i hd
  | _ :: _, _, [], h, _, _, _ :: _, _ => h.elim
end

/-- **A function of a pure set loading from `R`, on every reader**: the size is fixed first, then
on any reader agreeing with `rd0` on `R` and defined wherever it is, at any frame pointer. -/
theorem relAtInB_uniform_pure (hF : P.Fresh) (hS : P.PureIn Sz) {g : String} (hg : g ∈ Sz)
    {R : ℕ → Prop} {args rets : List E} (h : P.RelInB S rd0 R g args rets) :
    ∃ n, ∀ (fp : ℕ) (rd : Reader), (∀ i, R i → rd (gpow i) = rd0 (gpow i)) →
      (∀ A, (rd0 A).isSome → (rd A).isSome) →
      RelAtInB S P fs cert rd R (fun _ => False) fp n g args rets := by
  obtain ⟨t, hn, hv, hb, hl⟩ := h
  refine ⟨t.total fs, fun fp rd hag hdef => ?_⟩
  exact relAtInB_transfer hF hn hv hb (placedB_of_pure hS t hv hb (hn ▸ hg) fp)
    (loadsIn_of_loadsR t R fp hl) (fun _ h => h.elim) rd
    (fun i hi => hi.elim (hag i) fun hd => (notB_data_of_pure hS t hv hb (hn ▸ hg) fp i hd).elim) hdef

/-- **A function of a quiet set, on every reader**: `Program.RelB` on `rd0` gives the placed
relation on any reader defined wherever `rd0` is, at any frame pointer and region. -/
theorem relAtInB_uniform_quiet (hP : P.Wf) (hF : P.Fresh) (hS : P.QuietIn Sz) {g : String}
    (hg : g ∈ Sz) {args rets : List E} (h : P.RelB S rd0 g args rets) :
    ∃ n, ∀ (fp : ℕ) (R : ℕ → Prop) (rd : Reader), (∀ A, (rd0 A).isSome → (rd A).isSome) →
      RelAtInB S P fs cert rd R (fun _ => False) fp n g args rets := by
  obtain ⟨t, hn, hv, hb⟩ := Program.RelB.tree hP h
  obtain ⟨n, hn'⟩ := relAtInB_uniform_pure (fs := fs) (cert := cert) hF hS.pureIn hg
    ⟨t, hn, hv, hb, loadsRB_of_quiet hS (fun _ => False) t hv (hn ▸ hg)⟩
  exact ⟨n, fun fp R rd hdef => (hn' fp rd (fun _ h => h.elim) hdef).mono fun _ h => h.elim⟩

end Pure

end Transfer

end
end LeanVM.Guest.Memory
