/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsHonest

  Bridges from `open_stacked`'s tree form to the honest memory's decoding: the decoded callees are
  plain, `NodeAgree` survives re-choosing the temporaries, `KidsLink` from the honest instances.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsAllT
public import LeanVM.E2E.Complete.DecodeInsts
public import LeanVM.Guest.Memory.GuestFresh

/-!
# The decoded callees, at the honest memory

`osDec_plain`: `open_stacked`'s specializations and the callees its decoder reads (`osDecNames`) are
plain compiled functions (no pre-, memory or semantic obligations): `honest_bodyAt_plain` applies.
`nodeAgree_of_retemp`: agreeing with a re-chosen node on its named cells is agreeing with the node.
`kidsLink_of_vagree`: a tree whose re-chosen tree is an instance of `T` is linked to frame
valuations agreeing with every instance's decoded callees (`VAgree`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.VerifySub

@[expose] public section

set_option maxRecDepth 100000 in
theorem osDec_plain_b : (osDecNames ++ openNames).all (fun f => match B2C.idxOf f with
    | some j => j != 1 && (certOf j).pre.isEmpty && (certOf j).mem.isEmpty && (certOf j).sem.isEmpty
    | none => false) = true := by
  decide +kernel

/-- **The decoded callees and `open_stacked`'s specializations are plain.** -/
theorem osDec_plain : ∀ f ∈ osDecNames ++ openNames, ∃ j, B2C.idxOf f = some j ∧ j ≠ 1 ∧ (certOf j).pre = [] ∧
    (certOf j).mem = [] ∧ (certOf j).sem = [] := by
  intro f hf
  have h := List.all_eq_true.mp osDec_plain_b f hf
  revert h
  split
  · rename_i j hj
    intro h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.isEmpty_iff] at h
    exact ⟨j, hj, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · intro h; cases h

theorem openName_mem {μ r : ℕ} (h22 : 22 ≤ μ) (h28 : μ ≤ 28) (h1 : 1 ≤ r) (h4 : r ≤ 4) : openName μ r ∈ openNames := by
  unfold openName
  rw [List.getD_eq_getElem _ _ (by simp [openNames]; omega)]
  exact List.getElem_mem _

/-- **Agreeing with a re-chosen node on its named cells is agreeing with the node**: re-choosing
changes only temporaries, which no path names. -/
theorem nodeAgree_of_retemp {ν : ℕ → String → Val → V → E} : ∀ {t : Tree} {fp : ℕ} {σ' : Val},
    B2C.NodeAgree (t.retemp coreProgram B2C.fs ν fp) σ' → B2C.NodeAgree t σ'
  | .phantom f σ, fp, σ', h => by rwa [retemp_phantom] at h
  | .node f σ bufs ks, fp, σ', h => by
    intro j hj es vs hw v hv h2 h3
    simp only [Memory.Tree.name, Memory.Tree.val] at hj hw
    rw [retemp_node] at h
    obtain ⟨i, -, hi, -, hfi, hco, -⟩ := B2C.fn_of_idx hj
    have hf : coreProgram.find? f = some (coreOf j) := by rw [hfi, hco]
    have hw' : walk (retempVal coreProgram ν fp f σ) (coreOf j).body = .ret es vs := by
      rw [walk_retemp coreProgram_fresh hf]; exact hw
    have e := h j hj es vs hw' v hv h2 h3
    simp only [Memory.Tree.val] at e ⊢
    rw [e]
    have hu : v ∈ (coreOf j).params ∨ v ∈ Stmt.usesList (coreOf j).body := by
      have hwi := walk_within (σ := σ) (coreOf j).body
      rw [hw] at hwi
      simp only [B2C.namedOf, List.mem_append, List.mem_flatMap] at hv
      rcases hv with (hv | ⟨e, he, hv⟩) | hv
      · exact Or.inl hv
      · exact Or.inr (hwi.1 e he v hv)
      · exact Or.inr (hwi.2.2 v hv)
    rcases hu with hu | hu
    · have hm := retempVal_params (ν := ν) coreProgram_fresh hf (fp := fp) (σ := σ)
      obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hu
      have := congrArg (fun l => l[n]?) hm
      simpa [List.getElem?_map, List.getElem?_eq_getElem hn] using this
    · exact retempVal_uses coreProgram_fresh hf hu

/-- **The honest instances' decoded callees agree with the frame valuations**: at every instance,
every entered call to a decoded callee has, under `V`, a valuation agreeing with its callee tree. -/
def VAgree (V : FrameVals) (Is : List Inst) : Prop :=
  ∀ I ∈ Is, ∀ (f : String) (σ : Val) (bufs : List ℕ) (kids : List Tree), I.t = .node f σ bufs kids →
    ∀ (i : ℕ) (c : Call) (k : Tree), (calls (I.t.events coreProgram))[i]? = some c →
    kids[i]? = some k → c.taken = true → c.f ∈ osDecNames → B2C.NodeAgree k (V c.f (c.args.map σ) (c.rets.map σ))

theorem kidsLinkCalls_of_index {V : FrameVals} {σ : Val} : ∀ {cs : List Call} {ks : List Tree},
    (∀ (i : ℕ) (c : Call) (k : Tree), cs[i]? = some c → ks[i]? = some k → c.taken = true → c.f ∈ osDecNames →
      B2C.NodeAgree k (V c.f (c.args.map σ) (c.rets.map σ))) → KidsLinkCalls V σ cs ks
  | [], _, _ => by simp [KidsLinkCalls]
  | _ :: _, [], _ => by simp [KidsLinkCalls]
  | c :: cs, k :: ks, h => ⟨fun ht hf => h 0 c k rfl rfl ht hf,
      kidsLinkCalls_of_index fun i c' k' hc hk => h (i + 1) c' k' hc hk⟩

theorem kidsLinkKids_of_mem {V : FrameVals} : ∀ {ks : List Tree}, (∀ k ∈ ks, KidsLink V k) → KidsLinkKids V ks
  | [], _ => by simp [KidsLinkKids]
  | k :: ks, h => ⟨h k List.mem_cons_self, kidsLinkKids_of_mem fun k' hk' => h k' (List.mem_cons_of_mem _ hk')⟩

/-- A call's words read the same at the re-chosen valuation: they are named by the path. -/
theorem callVals_retemp {ν : ℕ → String → Val → V → E} {f : String} {σ : Val} {bufs : List ℕ} {ks : List Tree}
    {fp : ℕ} {c : Call} (hc : c ∈ calls ((Memory.Tree.node f σ bufs ks).events coreProgram)) :
    c.args.map (retempVal coreProgram ν fp f σ) = c.args.map σ ∧
      c.rets.map (retempVal coreProgram ν fp f σ) = c.rets.map σ := by
  unfold Tree.events at hc
  simp only [Memory.Tree.name, Memory.Tree.val] at hc
  split at hc
  · rename_i fn hf
    split at hc
    · rename_i es vs hw
      have hwi := walk_within (σ := σ) fn.body
      rw [hw] at hwi
      obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
      have hu : ∀ v ∈ e.uses, retempVal coreProgram ν fp f σ v = σ v := fun v hv =>
        retempVal_uses coreProgram_fresh hf (hwi.1 e he v hv)
      match e, hce with
      | .call g a r, hce =>
        simp only [Memory.Ev.call?, Option.some.injEq] at hce
        subst hce
        exact ⟨List.map_congr_left fun v hv => hu v (by simp [Memory.Ev.uses, hv]),
          List.map_congr_left fun v hv => hu v (by simp [Memory.Ev.uses, hv])⟩
      | .skip g a, hce =>
        simp only [Memory.Ev.call?, Option.some.injEq] at hce
        subst hce
        exact ⟨List.map_congr_left fun v hv => hu v (by simp [Memory.Ev.uses, hv]), rfl⟩
    · simp [calls] at hc
  · simp [calls] at hc

/-- **A tree whose re-chosen tree is an instance is linked** to frame valuations agreeing with the
instances' decoded callees. -/
theorem kidsLink_of_vagree {ν : ℕ → String → Val → V → E} {V : FrameVals} {T : Tree} {fp0 : ℕ} {hdr : E × E}
    {H : Inst → ℕ → E × E} (hV : VAgree V (T.insts B2C.fs coreProgram.loop H fp0 hdr)) :
    ∀ (t : Tree) (J : Inst), J ∈ T.insts B2C.fs coreProgram.loop H fp0 hdr →
      J.t = t.retemp coreProgram B2C.fs ν J.fp → KidsLink V t
  | .phantom f σ, _, _, _ => by simp [KidsLink]
  | .node f σ bufs ks, J, hJ, hJt => by
    have hJt' := hJt
    rw [retemp_node] at hJt'
    have hpos : ∀ i (k : Tree), ks[i]? = some k → ∃ p,
        (kidPos B2C.fs coreProgram.loop J.fp f bufs (ks.map (Tree.total B2C.fs)))[i]? = some p := fun i k hk => by
      have hi : i < (kidPos B2C.fs coreProgram.loop J.fp f bufs (ks.map (Tree.total B2C.fs))).length := by
        rw [length_kidPos, List.length_map]; exact (List.getElem?_eq_some_iff.mp hk).1
      exact ⟨_, List.getElem?_eq_getElem hi⟩
    refine ⟨kidsLinkCalls_of_index fun i c k hc hk ht hfn => ?_, kidsLinkKids_of_mem fun k hk => ?_⟩
    · obtain ⟨p, hp⟩ := hpos i k hk
      have hk' := E2E.Complete.getElem?_retempKids (P := coreProgram) (fs := B2C.fs) (ν := ν) ks _ hk hp
      have hev : J.t.events coreProgram = (Memory.Tree.node f σ bufs ks).events coreProgram := by
        rw [hJt', events_retemp coreProgram_fresh]
      have := hV J hJ f _ _ _ hJt' i c _ (by rw [hev]; exact hc) hk' ht hfn
      obtain ⟨ha, hr⟩ := callVals_retemp (ν := ν) (fp := J.fp) (List.mem_of_getElem? hc)
      rw [ha, hr] at this
      exact nodeAgree_of_retemp this
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
      obtain ⟨p, hp⟩ := hpos i _ (List.getElem?_eq_getElem hi)
      obtain ⟨J', hJ', hJ't, hJ'p, -⟩ := E2E.Complete.retemp_kid_inst (P := coreProgram) (fs := B2C.fs) (ν := ν)
        hJ hJt (List.getElem?_eq_getElem hi) hp
      have := List.getElem_mem hi
      exact kidsLink_of_vagree hV ks[i] J' hJ' (by rw [hJ't, hJ'p])
termination_by t => sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem (List.getElem_mem hi)
  simp only [Memory.Tree.node.sizeOf_spec]
  omega

end
end LeanVM.Guest.B1
