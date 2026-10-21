/-
  LeanVM.Guest.B2C.FrameB

  The frame an instance runs on (`Frame.lean`) under any functional semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.Frame
public import LeanVM.Guest.B2C.ShareSoundB
public import LeanVM.Guest.MemoryB

/-!
# The frame an instance runs on under any `BLAKE2S` semantics

`Frame.lean`'s reads of the honest memory with its tree valid under `S : BlakeSem` (`HonestB`):
`readB_val`, `readB_stat` (by `shareOkB_path`, so under a functional `S`), `readB_tmp`,
`readB_arm`, `readB_args`, `readB_self`, `nodeB_valid`, `kidB_inst`, `kidsValidB_at`,
`kidsValidB_length`, `frameB_len`, `frameB_addr`. The candidates (`C`, `cand_val`, …) are
`Frame.lean`'s.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

variable {S : BlakeSem}

/-! ## A value's cell -/

section Val

variable {j : ℕ} {G : Glob} {fc : CompiledFn} {main : Bool}

/-- **The honest memory reads each named value at its cell.** -/
theorem readB_val (hfun : SemFunctional S) {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : HonestB S coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) (he : ∀ e ∈ es, e.HoldsB S rd σ)
    {v : V} (hv : v ∈ namedOf (coreOf j).params es vs) (h2 : 2 ≤ cellJ j v) (hn : cellJ j v < fsN j) :
    (honest coreProgram fs H C hdr T).read (gpow (I.fp + cellJ j v)) = some (σ v) := by
  obtain ⟨Ψ, hΨ, hst⟩ := shareOkB_path hfun hS hchk hw he
  obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
  have hmem : (cellJ (i + 1) v, σ v) ∈ C I := by
    rw [C_node ht hj, hfs]
    refine frameE_cell ⟨(cert f v, σ v), ?_, hcert v⟩ h2 hn fun x hx hxc ↦
      cand_val hS hchk ht hj hw (Ψ := Ψ) (fun u hu hc ↦ hΨ u (by simpa [namedOf, List.append_assoc] using hu) hc)
        hst hv h2 hx hxc
    obtain ⟨hev, hvs⟩ := node_path ht hj hw
    simp only [nodeE, List.mem_append, valE, List.mem_map, hev, hvs]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨v, hv, rfl⟩)))
  rw [gpow, pow_add]
  exact h.read_C hI hmem

end Val

/-! ## The fixed cells, the temporaries, the table targets -/

section Others

variable {j : ℕ} {G : Glob} {fc : CompiledFn} {main : Bool}

/-- **The honest memory reads each fixed cell's word.** -/
theorem readB_stat (hfun : SemFunctional S) {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : HonestB S coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) (he : ∀ e ∈ es, e.HoldsB S rd σ)
    {q : ℕ × PC} (hq : q ∈ (plumbOf j).stat) (h2 : 2 ≤ q.1) (hn : q.1 < fsN j) :
    (honest coreProgram fs H C hdr T).read (gpow (I.fp + q.1)) = some (q.2.word I.fp) := by
  obtain ⟨Ψ, hΨ, hst⟩ := shareOkB_path hfun hS hchk hw he
  have hΨ' : ∀ u ∈ namedOf (coreOf j).params es vs, 2 ≤ cellJ j u → σ u = Ψ (cellJ j u) :=
    fun u hu hc ↦ hΨ u (by simpa [namedOf, List.append_assoc] using hu) hc
  have FS := fnStatic hS hchk
  have AP := apart_j hS
  obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
  have hcJ : ∀ u, cert f u = cellJ (i + 1) u := fun u ↦ hcert u
  obtain ⟨hev, hvs⟩ := node_path ht hj hw
  -- a value at the cell: the cell holds a constant, the value's word
  have hval : ∀ u ∈ namedOf (coreOf (i + 1)).params es vs, cellJ (i + 1) u = q.1 → σ u = q.2.word I.fp := by
    intro u hu hcu
    obtain ⟨-, -, hfc, -⟩ := valOk_global hS hchk (namedOf_sub hw hu)
    rcases q with ⟨o, ⟨a, b, c⟩ | e⟩
    · simp only at hcu ⊢
      rw [hΨ' u hu (by rw [hcu]; exact h2), hcu, hst o a b c hq]; rfl
    · simp only at hcu
      have : (fpgCells (plumbOf (i + 1))).testBit o = true := mem_bitsOf (List.mem_filterMap.mpr ⟨_, hq, rfl⟩)
      rw [bitN_eq, hcu, this] at hfc; cases hfc
  have hmem : (q.1, q.2.word I.fp) ∈ C I := by
    rw [C_node ht hj, hfs]
    refine frameE_cell ⟨(q.1, q.2.word I.fp), ?_, rfl⟩ h2 hn fun x hx hxc ↦ ?_
    · simp only [nodeE, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩))))
    simp only [nodeE, List.mem_append, hev, hvs] at hx
    rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) | hx
    · simp only [valE, List.mem_map] at hx
      obtain ⟨t, htm, rfl⟩ := hx
      obtain ⟨j', hj', htl⟩ := temps_of htm
      rw [hj] at hj'; cases hj'
      have := (FS.tmp t htl).2
      exact absurd (by rw [← hcJ]; exact hxc) (AP.statTmp q hq _ this)
    · obtain ⟨u, hu, hcu, hx2⟩ := run_named hj hw FS hx
      rw [hx2]; exact hval u hu (hcu.trans hxc)
    · simp only [List.mem_map] at hx
      obtain ⟨q', hq', rfl⟩ := hx
      simp only at hxc ⊢
      rw [List.inj_on_of_nodup_map AP.statNodup hq' hq hxc]
    · simp only [valE, List.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      simp only [hcJ] at hxc ⊢
      exact hval u hu hxc
    · exact absurd hxc ((AP.site _ (mem_siteE hx)).2.2.1 q hq).symm
    · simp only [List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact absurd hxc ((AP.arm a ha).2.2.1 q hq).symm
    · split_ifs at hx with h1
      · have hlt := (AP.main h1).2.2.1 q hq
        have : x.1 ∈ tableCells.map Prod.fst := List.mem_map_of_mem hx
        rw [tableCells_offsets, List.mem_range'] at this
        omega
      · cases hx
  rw [gpow, pow_add]
  exact h.read_C hI hmem

/-- **The honest memory reads each temporary of the path at its cell.** -/
theorem readB_tmp {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : HonestB S coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) {t : V} (htm : t ∈ coreProgram.temps f)
    (h2 : 2 ≤ cellJ j t) (hn : cellJ j t < fsN j) :
    (honest coreProgram fs H C hdr T).read (gpow (I.fp + cellJ j t)) = some (σ t) := by
  have FS := fnStatic hS hchk
  have AP := apart_j hS
  obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
  have hcJ : ∀ u, cert f u = cellJ (i + 1) u := fun u ↦ hcert u
  obtain ⟨hev, hvs⟩ := node_path ht hj hw
  obtain ⟨j', hj', htl⟩ := temps_of htm
  rw [hj] at hj'; cases hj'
  obtain ⟨ht1, ht2⟩ := FS.tmp t htl
  -- a value at a temporary's cell is that temporary
  have same : ∀ u : V, u = V.n u.idx → (u.idx, cellJ (i + 1) t) ∈ (plumbOf (i + 1)).tmps → u = t := by
    intro u hu hl
    have := FS.tmpsFun _ hl _ ht2 rfl
    simp only at this
    rw [hu, ht1, this]
  have hmem : (cellJ (i + 1) t, σ t) ∈ C I := by
    rw [C_node ht hj, hfs]
    refine frameE_cell ⟨(cert f t, σ t), ?_, hcert t⟩ h2 hn fun x hx hxc ↦ ?_
    · simp only [nodeE, List.mem_append, valE, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨t, htm, rfl⟩)))))
    simp only [nodeE, List.mem_append, hev, hvs] at hx
    rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) | hx
    · simp only [valE, List.mem_map] at hx
      obtain ⟨t', htm', rfl⟩ := hx
      obtain ⟨j', hj', htl'⟩ := temps_of htm'
      rw [hj] at hj'; cases hj'
      obtain ⟨ht1', ht2'⟩ := FS.tmp t' htl'
      simp only [hcJ] at hxc ⊢
      rw [same t' ht1' (hxc ▸ ht2')]
    · obtain ⟨p, r, rs, he', k, hk, rfl⟩ := mem_runsE hx
      have ha : Atom.frameAddr p (r :: rs) ∈ lAtoms (coreOf (i + 1)).body := walk_atoms _ (by rw [hw]; exact he')
      obtain ⟨-, -, hrun⟩ := FS.run p r rs ha k hk
      exact absurd (by simp only [hcJ] at hxc; exact hxc) (FS.runsTmp _ hrun _ ht2).symm
    · simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact absurd hxc.symm (AP.statTmp q hq _ ht2)
    · simp only [valE, List.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      simp only [hcJ] at hxc ⊢
      obtain ⟨hu1, -, -, htc⟩ := valOk_global hS hchk (namedOf_sub hw hu)
      rw [hxc] at htc
      rw [same u hu1 (cellJ_tmp_listed htc ht2)]
    · exact absurd (hxc ▸ rfl) ((AP.site _ (mem_siteE hx)).1 _ ht2)
    · simp only [List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact absurd hxc.symm ((AP.arm a ha).1 _ ht2)
    · split_ifs at hx with h1
      · have hlt := (AP.main h1).1 _ ht2
        have : x.1 ∈ tableCells.map Prod.fst := List.mem_map_of_mem hx
        rw [tableCells_offsets, List.mem_range'] at this
        simp only at hlt
        omega
      · cases hx
  rw [gpow, pow_add]
  exact h.read_C hI hmem

/-- **The honest memory reads each table jump's target.** -/
theorem readB_arm {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : HonestB S coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs)
    {a : ℕ × ℕ × ℕ} (ha : a ∈ (plumbOf j).arms) (h2 : 2 ≤ a.2.1) (hn : a.2.1 < fsN j) :
    (honest coreProgram fs H C hdr T).read (gpow (I.fp + a.2.1)) = some (armWord σ a.1 a.2.2) := by
  have FS := fnStatic hS hchk
  have AP := apart_j hS
  obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
  have hcJ : ∀ u, cert f u = cellJ (i + 1) u := fun u ↦ hcert u
  obtain ⟨hev, hvs⟩ := node_path ht hj hw
  obtain ⟨hat, har, has, hal, hsc⟩ := AP.arm a ha
  have hmem : (a.2.1, armWord σ a.1 a.2.2) ∈ C I := by
    rw [C_node ht hj, hfs]
    refine frameE_cell ⟨(a.2.1, armWord σ a.1 a.2.2), ?_, rfl⟩ h2 hn fun x hx hxc ↦ ?_
    · simp only [nodeE, List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨a, ha, rfl⟩)
    simp only [nodeE, List.mem_append, hev, hvs] at hx
    rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) | hx
    · simp only [valE, List.mem_map] at hx
      obtain ⟨t, htm, rfl⟩ := hx
      obtain ⟨j', hj', htl⟩ := temps_of htm
      rw [hj] at hj'; cases hj'
      exact absurd (by simp only [hcJ] at hxc; exact hxc) (hat _ (FS.tmp t htl).2)
    · obtain ⟨u, hu, hcu, -⟩ := run_named hj hw FS hx
      obtain ⟨p, r, rs, he', k, hk, rfl⟩ := mem_runsE hx
      have ha' : Atom.frameAddr p (r :: rs) ∈ lAtoms (coreOf (i + 1)).body := walk_atoms _ (by rw [hw]; exact he')
      obtain ⟨-, -, hrun⟩ := FS.run p r rs ha' k hk
      exact absurd (by simp only [hcJ] at hxc; exact hxc) (har _ hrun)
    · simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact absurd hxc (has q hq)
    · simp only [valE, List.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      simp only [hcJ] at hxc
      exact absurd (hxc ▸ cellJ_mem (hxc ▸ h2)) hal
    · exact absurd (hxc ▸ mem_siteE hx) hsc
    · simp only [List.mem_map] at hx
      obtain ⟨a', ha', rfl⟩ := hx
      simp only at hxc ⊢
      rw [List.inj_on_of_nodup_map (f := fun a : ℕ × ℕ × ℕ ↦ a.2.1) AP.armNodup ha' ha hxc]
    · split_ifs at hx with h1
      · have hlt := (AP.main h1).2.2.2.2.2 a ha
        have : x.1 ∈ tableCells.map Prod.fst := List.mem_map_of_mem hx
        rw [tableCells_offsets, List.mem_range'] at this
        omega
      · cases hx
  rw [gpow, pow_add]
  exact h.read_C hI hmem

end Others

/-! ## A callee's arguments -/

section Args

variable {j : ℕ} {G : Glob} {fc : CompiledFn} {main : Bool}

/-- **A callee's frame holds its arguments** at cells `2 + k`, whether it runs or not. -/
theorem readB_args (hfun : SemFunctional S) {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : HonestB S coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {J : Inst} (hJ : J ∈ honestInsts coreProgram fs H hdr T) {g : String} (hj : idxOf g = some j)
    (hgood : (∃ σ bufs kids es vs, J.t = .node g σ bufs kids ∧
      walk σ (coreOf j).body = .ret es vs ∧ ∀ e ∈ es, e.HoldsB S rd σ) ∨ ∃ σ, J.t = .phantom g σ)
    (k : ℕ) (hk : k < (coreOf j).params.length) :
    (honest coreProgram fs H C hdr T).read (gpow (J.fp + (2 + k))) = some (J.t.val (coreOf j).params[k]) := by
  have hcont := cont_of hchk
  have hpc := checkWin_params (hchk 0 (Nat.zero_le _)) hcont k hk
  have hpk : (coreOf j).params[k] ∈ (coreOf j).params ++ Stmt.usesList (coreOf j).body ++
      Stmt.tmpsList (coreOf j).body := List.mem_append_left _ (List.mem_append_left _ (List.getElem_mem hk))
  obtain ⟨hvn, hlt, hfc, -⟩ := valOk_global hS hchk hpk
  rw [show cellJ j (coreOf j).params[k] = 2 + k from hpc] at hlt hfc
  rcases hgood with ⟨σ, bufs, kids, es, vs, ht, hw, he⟩ | ⟨σ, ht⟩
  · have := readB_val hfun h hS hchk hJ ht hj hw he (v := (coreOf j).params[k])
      (by simp only [namedOf, List.mem_append]; exact Or.inl (Or.inl (List.getElem_mem hk)))
      (by rw [show cellJ j (coreOf j).params[k] = 2 + k from hpc]; omega)
      (by rw [show cellJ j (coreOf j).params[k] = 2 + k from hpc]; exact hlt)
    rw [show cellJ j (coreOf j).params[k] = 2 + k from hpc] at this
    rw [ht]; exact this
  · obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
    have AP := apart_j hS
    have hmem : (2 + k, σ (coreOf (i + 1)).params[k]) ∈ C J := by
      rw [C_phantom ht hj, hfs]
      refine frameE_cell ⟨(cert g (coreOf (i + 1)).params[k], σ (coreOf (i + 1)).params[k]), ?_, ?_⟩
        (by omega) hlt fun x hx hxc ↦ ?_
      · simp only [phantomE, List.mem_append, valE, List.mem_map]
        exact Or.inl ⟨_, List.getElem_mem hk, rfl⟩
      · rw [hcert]; exact hpc
      simp only [phantomE, List.mem_append, valE, List.mem_map] at hx
      rcases hx with ⟨u, hu, rfl⟩ | ⟨p, hp, rfl⟩
      · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hu
        simp only at hxc ⊢
        rw [hcert, checkWin_params (hchk 0 (Nat.zero_le _)) hcont m hm] at hxc
        obtain rfl : m = k := by omega
        rfl
      · simp only at hxc
        have hst := AP.env p hp
        have : (fpgCells (plumbOf (i + 1))).testBit p.1 = true := mem_bitsOf (List.mem_filterMap.mpr ⟨_, hst, rfl⟩)
        rw [bitN_eq, ← hxc, this] at hfc; cases hfc
    rw [gpow, pow_add, ht]
    exact h.read_C hJ hmem

/-- **A callee's frame holds its frame pointer** in its entry environment's cells, whether it runs
or not. -/
theorem readB_self (hfun : SemFunctional S) {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : HonestB S coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {J : Inst} (hJ : J ∈ honestInsts coreProgram fs H hdr T) {g : String} (hj : idxOf g = some j)
    (hgood : (∃ σ bufs kids es vs, J.t = .node g σ bufs kids ∧
      walk σ (coreOf j).body = .ret es vs ∧ ∀ e ∈ es, e.HoldsB S rd σ) ∨ ∃ σ, J.t = .phantom g σ)
    {o : ℕ} (ho : o ∈ (certOf j).facts.env.map Prod.fst) :
    (honest coreProgram fs H C hdr T).read (gpow (J.fp + o)) = some (ofK (gpow J.fp)) := by
  have AP := apart_j hS
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
  have hst := AP.env p hp
  obtain ⟨h2, hn⟩ := stat_in hS hst
  rcases hgood with ⟨σ, bufs, kids, es, vs, ht, hw, he⟩ | ⟨σ, ht⟩
  · have := readB_stat hfun h hS hchk hJ ht hj hw he hst h2 hn
    simpa [PC.word] using this
  · obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
    have hmem : (p.1, ofK (gpow J.fp)) ∈ C J := by
      rw [C_phantom ht hj, hfs]
      refine frameE_cell ⟨(p.1, ofK (gpow J.fp)), ?_, rfl⟩ h2 hn fun x hx hxc ↦ ?_
      · simp only [phantomE, List.mem_append, List.mem_map]
        exact Or.inr ⟨p, hp, rfl⟩
      simp only [phantomE, List.mem_append, valE, List.mem_map] at hx
      rcases hx with ⟨u, hu, rfl⟩ | ⟨p', -, rfl⟩
      · simp only [hcert] at hxc
        obtain ⟨-, -, hfc, -⟩ := valOk_global hS hchk (v := u)
          (List.mem_append_left _ (List.mem_append_left _ hu))
        have : (fpgCells (plumbOf (i + 1))).testBit p.1 = true := mem_bitsOf (List.mem_filterMap.mpr ⟨_, hst, rfl⟩)
        rw [bitN_eq, show cellJ (i + 1) u = p.1 from hxc, this] at hfc; cases hfc
      · rfl
    rw [gpow, pow_add]
    exact h.read_C hJ hmem

end Args

/-! ## The frame's placement -/

section Place

variable {j : ℕ}

theorem kidsValidB_length {rd : Reader} {σ : Val} : ∀ {cs : List Call} {ks : List Tree},
    Tree.KidsValidB S coreProgram rd σ cs ks → ks.length = cs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.length_cons, kidsValidB_length h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- A node instance valid on a reader, along its function's path. -/
theorem nodeB_valid {rd : Reader} {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) (hg : I.GoodB S coreProgram rd) :
    ∃ es vs, walk σ (coreOf j).body = .ret es vs ∧ (∀ e ∈ es, e.HoldsB S rd σ) ∧
      Tree.KidsValidB S coreProgram rd σ (calls es) kids := by
  obtain ⟨i, rfl, hi, -, hf, hc, -⟩ := fn_of_idx hj
  rcases hg with ⟨args, rets, hv⟩ | ⟨f', σ', hp⟩
  · rw [ht] at hv
    obtain ⟨fn, hfn, -, es, vs, hw, -, he, hk⟩ := hv
    rw [hf] at hfn; cases hfn
    exact ⟨es, vs, by rw [hc]; exact hw, he, hk⟩
  · rw [ht] at hp; cases hp

/-- **One callee frame per call.** -/
theorem frameB_len {hdr : E × E} {T : Tree} {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T)
    {rd : Reader} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {es : List Ev} (hk : Tree.KidsValidB S coreProgram rd σ (calls es) kids) :
    I.kidFps.length = (calls es).length := by
  rw [honest_kidFps hI, length_kidPos, List.length_map, ht]
  exact kidsValidB_length hk

/-- **The frame addresses** are the runs' addresses in the frame. -/
theorem frameB_addr {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : HonestAtB S coreProgram fs H C hdr T cert rd args rets) {I : Inst}
    (hI : I ∈ honestInsts coreProgram fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) :
    ∀ q ∈ addrs es, σ q.1 = ofK (gpow (I.fp + cellJ j q.2)) := by
  obtain ⟨hev, -⟩ := node_path ht hj hw
  obtain ⟨i, rfl, -, -, -, -, -, hcert, -⟩ := fn_of_idx hj
  intro q hq
  rw [(h.nodeAt hI ht).2 q (by rw [hev]; exact hq), hcert]; rfl

end Place

/-! ## The callees -/

section Kids

theorem kidsValidB_at {rd : Reader} {σ : Val} : ∀ {cs : List Call} {ks : List Tree},
    Tree.KidsValidB S coreProgram rd σ cs ks → ∀ (i : ℕ) (c : Call), cs[i]? = some c →
      ∃ k, ks[i]? = some k ∧ k.name = c.f ∧
        (if c.taken then k.ValidB S coreProgram rd (c.args.map σ) (c.rets.map σ)
          else (∃ f σ', k = .phantom f σ') ∧ Phantom coreProgram k (c.args.map σ))
  | [], [], _, _, _, h => by simp at h
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim
  | c :: cs, k :: ks, ⟨hn, hk, h⟩, i, c', hc => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨k, rfl, hn, hk⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact kidsValidB_at h i c' hc

/-- **The `i`-th callee of a path**: an instance at the `i`-th callee frame, with the header
`H I i`, valid if the call is taken, else a phantom with the arguments. -/
theorem kidB_inst {hdr : E × E} {T : Tree} {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T)
    {rd : Reader} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {es : List Ev} (hk : Tree.KidsValidB S coreProgram rd σ (calls es) kids) {i : ℕ} {c : Call} {kfp : ℕ}
    (hc : (calls es)[i]? = some c) (hp : I.kidFps[i]? = some kfp) :
    ∃ J ∈ honestInsts coreProgram fs H hdr T, J.fp = kfp ∧ J.hdr = H I i ∧ J.t.name = c.f ∧
      (if c.taken then J.t.ValidB S coreProgram rd (c.args.map σ) (c.rets.map σ)
        else (∃ f σ', J.t = .phantom f σ') ∧ Phantom coreProgram J.t (c.args.map σ)) := by
  obtain ⟨k, hki, hn, hv⟩ := kidsValidB_at hk i c hc
  obtain ⟨J, hJ, rfl, hfp, hh⟩ := honest_kid hI (by rw [ht]; exact hki)
  rw [hp] at hfp
  exact ⟨J, hJ, (Option.some.inj hfp).symm, hh, hn, hv⟩

end Kids

end
end LeanVM.Guest.B2C
