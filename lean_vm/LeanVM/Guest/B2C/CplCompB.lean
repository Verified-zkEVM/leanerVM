/-
  LeanVM.Guest.B2C.CplCompB

  The composition of a function's parts (`CplComp.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.CplComp
public import LeanVM.Guest.B2C.CplRunB
public import LeanVM.Guest.B2C.CplWalkZB

/-!
# The composition under any `BLAKE2S` semantics

`CplComp.lean`'s `PartArr`, `PartReach`, `CplGoal` with `S : BlakeSem` a parameter (`PartArrB`,
`PartReachB`, `CplGoalB`) and the composition along a path (`partB_step`, `partB_last`,
`reachB_zero`, `winsB_goal`), giving `cplB_run`: from the completeness check, `CplRunB S j`.

* `partArrB_deployed`, `partReachB_deployed`, `cplGoalB_deployed`: at `blakeDeployed`, they are
  `CplComp.lean`'s.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

variable {S : BlakeSem}

variable (S) in
/-- **The run is at part `k`'s start**: at its segment's start, or past the items the part
starts after, within its counts, the separately counted arms passed counting `x`, and the first
`n` callees'. -/
def PartArrB {κ : ℕ} (L : MemImage κ) (j fp : ℕ) (ck : List (Opcode → ℕ)) (i k n : ℕ)
    (x : Opcode → ℕ) : Prop :=
  if partM j i k = 0 then
    ArrB S L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) (partJ j i k) (partC j i k) n x
  else ArrMidB S L fp (Xp j i k) ck (entryRegs j fp) (partJ j i k) (partM j i k) (partC j i k) n x

variable (S) in
/-- **The run reaches part `k` of window `i`** on a path: the path from there returns, and the
run is at the part's start within its counts and the callees' before it. -/
def PartReachB {κ : ℕ} (L : MemImage κ) (j fp : ℕ) (σ : Val) (es : List Ev) (vs : List V)
    (ck : List (Opcode → ℕ)) (i k : ℕ) : Prop :=
  ∃ ebef erest xc, walk σ ((coreOf j).body.drop (partPos j i k)) = .ret erest vs ∧ es = ebef ++ erest ∧
    xc + costW (nth Data.cplArms j []) σ ((coreOf j).body.drop (partPos j i k)) =
      costW (nth Data.cplArms j []) σ (coreOf j).body ∧
    PartArrB S L j fp ck i k (calls ebef).length xc

variable (S) in
/-- What `CplRunB` concludes of one path. -/
def CplGoalB {κ : ℕ} (L : MemImage κ) (j fp : ℕ) (σ : Val) (vs : List V) (ck : List (Opcode → ℕ)) :
    Prop :=
  ∃ (r : Regs K) (c : Opcode → ℕ), (if j = 1 then r = Regs.final guest else retRegs L (gpow fp) = some r) ∧
    RunCB S guest L ⟨gpow (fnOf j).entry, gpow fp⟩ r c ∧
    (∀ op, c op ≤ pathCount j σ op + (ck.map (· op)).sum) ∧
    ∀ k (hk : k < vs.length),
      L.read (gpow (fp + (2 + (coreOf j).params.length + k))) = some (σ vs[k])

/-! ## The body returns only at its end -/

section Comp

variable {κ : ℕ} {L : MemImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
  {kfps : List ℕ} {hdr : E × E} {ck : List (Opcode → ℕ)}

theorem partArrB_zero {i k n : ℕ} {x : Opcode → ℕ} (h : partM j i k = 0) : PartArrB S L j fp ck i k n x ↔
    ArrB S L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) (partJ j i k) (partC j i k) n x := by
  unfold PartArrB
  simp only [h, ↓reduceIte]

theorem partArrB_mid {i k n : ℕ} {x : Opcode → ℕ} (h : partM j i k ≠ 0) : PartArrB S L j fp ck i k n x ↔
    ArrMidB S L fp (Xp j i k) ck (entryRegs j fp) (partJ j i k) (partM j i k) (partC j i k) n x := by
  unfold PartArrB
  simp only [h, ↓reduceIte]

theorem arrB_mono {X : CX} {wJ : ℕ} {wenv : Trie Sym} {W0 : Regs K} {J n : ℕ} {x : Opcode → ℕ}
    {c c' : Cnt} (h : ArrB S L fp X wJ wenv ck W0 J c n x) (hc : c.le c' = true) :
    ArrB S L fp X wJ wenv ck W0 J c' n x := by
  obtain ⟨⟨cr, hr, hle⟩, he⟩ := h
  exact ⟨⟨cr, hr, fun op ↦ by have := hle op; have := Cnt.le_spec hc op; omega⟩, he⟩

theorem arrMidB_mono {X : CX} {W0 : Regs K} {J m n : ℕ} {x : Opcode → ℕ} {c c' : Cnt}
    (h : ArrMidB S L fp X ck W0 J m c n x) (hc : c.le c' = true) : ArrMidB S L fp X ck W0 J m c' n x := by
  obtain ⟨s, hs, hst, hm, he, cr, hf, hr, hle⟩ := h
  exact ⟨s, hs, hst, hm, he, cr, hf, hr, fun op ↦ by have := hle op; have := Cnt.le_spec hc op; omega⟩

/-- At a segment's start, no item passed. -/
theorem arrMidB_zero {X : CX} {wJ : ℕ} {wenv : Trie Sym} {W0 : Regs K} {J n : ℕ} {x : Opcode → ℕ}
    {c : Cnt} {s : Exec.Seg}
    (h : ArrB S L fp X wJ wenv ck W0 J c n x) (hs : getF X.idx J = some s) (hst : s.start = J) :
    ArrMidB S L fp X ck W0 J 0 c n x := by
  obtain ⟨⟨cr, hr, hle⟩, he⟩ := h
  exact ⟨s, hs, hst, Nat.zero_le _, he.1 s hs hst, cr, trivial, hr, fun op ↦ by simpa [itemOps] using hle op⟩

/-- **Into the next window**: the environment window `i` hands on holds the next window's. -/
theorem arrB_win (F : FnHB S L j fp σ es vs kfps hdr ck) {i k : ℕ} (hi : i < (certOf j).cuts.length)
    {c c' : Cnt} {n : ℕ} {x : Opcode → ℕ}
    (h : ArrB S L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) ((certOf j).cutAt (i + 1)).J c n x)
    (hc : c.le c' = true) :
    ArrB S L fp (Xp j (i + 1) 0) (wJW j (i + 1)) (wenvW j (i + 1)) ck (entryRegs j fp)
      (partJ j (i + 1) 0) c' n x := by
  obtain ⟨⟨cr, hr, hle⟩, he1, he2⟩ := h
  have hb : Nat.blt i (certOf j).cuts.length = true := Nat.blt_eq.mpr hi
  have hc1 := checkWin_cpl (F.chk i hi.le)
  have hc2 := checkWin_cpl (F.chk (i + 1) hi)
  obtain ⟨s0, hs0, -, hsub0⟩ := hc2.2.2.2.1
  have hwJ : wJW j i = ((certOf j).cutAt (i + 1)).J := by simp only [wJW, hb, Bool.cond_true]
  have hwenv : wenvW j i = envOf ((certOf j).cutAt (i + 1)).env := by simp only [wenvW, hb, Bool.cond_true]
  have hE : EnvHolds L (gpow fp) (envOf ((certOf j).cutAt (i + 1)).env) := by
    cases hg : getF (index (segsW j i)) ((certOf j).cutAt (i + 1)).J with
    | none =>
      rw [← hwenv]
      exact he2 hwJ.symm hg
    | some s =>
      obtain ⟨hst, hsub⟩ := (hc1.2.2.2.2 hi).2 s hg
      exact (he1 s hg hst).sub hsub
  refine ⟨⟨cr, hr, fun op ↦ by have := hle op; have := Cnt.le_spec hc op; omega⟩,
    fun s hs _ ↦ ?_, fun _ hn ↦ ?_⟩
  · have hs' : getF (index (segsW j (i + 1))) ((certOf j).cutAt (i + 1)).J = some s := hs
    obtain rfl := Option.some.inj (hs'.symm.trans hs0)
    exact hE.sub hsub0
  · have hn' : getF (index (segsW j (i + 1))) ((certOf j).cutAt (i + 1)).J = none := hn
    rw [hn'] at hs0
    cases hs0

/-- The run at the function's entry, in window `0`'s first part. -/
theorem reachB_zero (F : FnHB S L j fp σ es vs kfps hdr ck) : PartReachB S L j fp σ es vs ck 0 0 := by
  have hc0 := F.ok 0 (Nat.zero_le _) 0 (one_le_nParts j 0)
  obtain ⟨s0, hs0, -, hsub0⟩ := (checkWin_cpl (F.chk 0 (Nat.zero_le _))).2.2.2.1
  have hw0 := winOkC_of hc0
  simp only [winOkC, Bool.and_eq_true, Nat.beq_refl, Bool.cond_true] at hw0
  have henv := hw0.2.2
  have hX := cxOk F.frame F.pows (index (segsW j 0)) (clocW (certOf j) 0) (nvOf (partStmts j 0 0) 0) none
  have hE : EnvHolds L (gpow fp) (envOf (certOf j).facts.env) := by
    refine envOf_holds fun p hp ↦ ?_
    have := List.all_eq_true.mp henv p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨h1, h2⟩ := this
    have := hX.stat p.1 _ h2
    rw [Sym.beq_eq h1]
    simp only [PC.word, Nat.add_zero] at this
    simpa [Sym.val, gpow_addC] using this
  refine ⟨[], es, 0, ?_, rfl, ?_, (partArrB_zero (partM_zero hc0)).mpr ?_⟩
  · rw [partPos, partS_zero hc0]
    exact F.walk
  · rw [zero_add, partPos, partS_zero hc0]
    rfl
  refine ⟨⟨0, RunCB.refl _, fun _ ↦ Nat.zero_le _⟩, fun s hs _ ↦ ?_, fun _ hn ↦ ?_⟩
  · have hs' : getF (index (segsW j 0)) ((certOf j).cutAt 0).J = some s := hs
    obtain rfl := Option.some.inj (hs'.symm.trans hs0)
    exact hE.sub hsub0
  · have hn' : getF (index (segsW j 0)) ((certOf j).cutAt 0).J = none := hn
    rw [hn'] at hs0
    cases hs0

/-- The walk's start of a part, from the run arriving there. -/
theorem posZB_start {i k : ℕ}
    (H : WHB S L j fp (Xp j i k) (segsW j i) (wJW j i) (wenvW j i) σ es vs kfps hdr ck) {s : Exec.Seg}
    (hs : getF (index (segsW j i)) (partJ j i k) = some s) (hst : s.start = partJ j i k) {n : ℕ}
    {x : Opcode → ℕ} (hA : PartArrB S L j fp ck i k n x)
    (hatoms : ∀ a, Stmt.atom a ∈ partStmts j i k → Ev.atom a ∈ es) :
    PosZB S H (st0 j i k s) (entryRegs j fp) n x := by
  have hM : ArrMidB S L fp (Xp j i k) ck (entryRegs j fp) (partJ j i k) (partM j i k) (partC j i k) n x := by
    unfold PartArrB at hA
    split_ifs at hA with h0
    · rw [h0]
      exact arrMidB_zero hA hs hst
    · exact hA
  obtain ⟨s', hs', -, hm, he, cr, hf, hr, hle⟩ := hM
  have hs1 : getF (Xp j i k).idx (partJ j i k) = some s := hs
  obtain rfl := Option.some.inj (hs'.symm.trans hs1)
  have hmem : s' ∈ segsW j i := by
    rw [getF_eq] at hs
    exact index_get hs
  refine ⟨hmem, ⟨he, fileBB_ok H.frame H.loc H.hev _ _
    (fun _ _ h ↦ absurd (show _ ∈ ([] : List LAtom) from h) (by simp)) hatoms,
    fun _ h ↦ (by cases h), fun _ h ↦ (by cases h), fun _ h ↦ (by cases h)⟩,
    ⟨s'.items.take (partM j i k), cr, List.take_append_drop _ _, hf,
      (by simp only [st0]; rw [hst]; exact hr), hle⟩,
    fun t ht ↦ ?_, fun _ h ↦ absurd h (by simp [st0]), (by simp only [st0]; rw [hst]; exact hs)⟩
  unfold st0 at ht
  cases h0 : Nat.beq (partM j i k) 0
  · rw [h0] at ht
    cases ht
  · rw [h0] at ht
    obtain rfl := Option.some.inj ht
    refine ⟨hst, ?_, hs⟩
    show s'.items.drop (partM j i k) = s'.items
    rw [Nat.eq_of_beq_eq_true h0, List.drop_zero]

/-- **A part before the last**: its walk takes the run to where it ends. -/
theorem partB_mid (F : FnHB S L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) {i k : ℕ}
    (hi : i ≤ (certOf j).cuts.length) (hk : k < nParts j i) (hr : PartReachB S L j fp σ es vs ck i k)
    (hnr : Stmt.noRetList (partStmts j i k) = true) :
    ∃ ebef erest xc, walk σ ((coreOf j).body.drop (nextPos j i k)) = .ret erest vs ∧ es = ebef ++ erest ∧
      xc + costW (nth Data.cplArms j []) σ ((coreOf j).body.drop (nextPos j i k)) =
        costW (nth Data.cplArms j []) σ (coreOf j).body ∧
      ((∃ J c u, cplRes j i k = .join J c u ∧
        ArrB S L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) J c (calls ebef).length xc) ∨
       (∃ J m c u, cplRes j i k = .mid J m c u ∧
        ArrMidB S L fp (Xp j i k) ck (entryRegs j fp) J m c (calls ebef).length xc)) := by
  obtain ⟨ebef, erest, xc, hwr, hes, hxc, hA⟩ := hr
  have hc := F.ok i hi
  have hsplit := part_split hk (fun h ↦ ((checkWin_cpl (F.chk i hi)).2.2.2.2 h).1) hc
  have hend := cplWin_end (hc k hk)
  obtain ⟨s, hs, hst, hres⟩ := cplRes_some hend
  unfold partPos at hwr hxc
  rw [hsplit, walk_appendC] at hwr
  rw [hsplit, costW_append, ← add_assoc] at hxc
  rcases walk_noRetC _ hnr with ⟨e1, hw1⟩ | hw1
  · rw [hw1] at hwr
    obtain ⟨e2, hw2, he⟩ := seq_fall_ret hwr
    have hatoms : ∀ a, Stmt.atom a ∈ partStmts j i k → Ev.atom a ∈ es := fun a ha ↦ by
      rw [hes, he]
      exact List.mem_append_right _ (List.mem_append_left _ (atom_on_pathC hw1 ha))
    have H := whB_part F hlb hi (k := k)
    have hp := posZB_start H hs hst hA hatoms
    have hes' : es = ebef ++ (Out.fall e1).evs ++ e2 := by rw [hes, he, List.append_assoc]; rfl
    obtain ⟨h1, hm, h2⟩ := walkB_Z H _ _ ebef e2 _ (entryRegs j fp) ((coreOf j).body.take (partPos j i k))
      xc hw1 hes' (fun h ↦ by cases h) (Or.inl hnr) hp (cw_ok_of hres hend)
    have hes2 : es = (ebef ++ e1) ++ e2 := by rw [hes, he, List.append_assoc]
    rcases hcr : cplRes j i k with ⟨J, c, u⟩ | ⟨J, m, c, u⟩ | _ | e
    · obtain ⟨es', he', ha⟩ := h1 J c u (hres.symm.trans hcr)
      cases he'
      exact ⟨ebef ++ e1, e2, _, hw2, hes2, hxc, Or.inl ⟨J, c, u, rfl, ha⟩⟩
    · obtain ⟨es', he', ha⟩ := hm J m c u (hres.symm.trans hcr)
      cases he'
      exact ⟨ebef ++ e1, e2, _, hw2, hes2, hxc, Or.inr ⟨J, m, c, u, rfl, ha⟩⟩
    · obtain ⟨es', vs', he', -⟩ := h2 (hres.symm.trans hcr)
      cases he'
    · rw [hcr] at hend
      simp [partEnd] at hend
  · rw [hw1] at hwr
    cases hwr

/-- **The last part**: its walk takes the run to the return. -/
theorem partB_last (F : FnHB S L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) {i k : ℕ}
    (hi : i ≤ (certOf j).cuts.length) (hk : k < nParts j i) (hr : PartReachB S L j fp σ es vs ck i k)
    (hn : ¬ k + 1 < nParts j i) (hci : ¬ i < (certOf j).cuts.length) : CplGoalB S L j fp σ vs ck := by
  obtain ⟨ebef, erest, xc, hwr, hes, hxc, hA⟩ := hr
  have hc := F.ok i hi
  have hsplit := part_split hk (fun h ↦ ((checkWin_cpl (F.chk i hi)).2.2.2.2 h).1) hc
  have hend := cplWin_end (hc k hk)
  obtain ⟨s, hs, hst, hres⟩ := cplRes_some hend
  have hlp : lastPart j i k = true := by simp only [lastPart, blt_falseC hn, blt_falseC hci]; rfl
  have hshp := cplWin_last (hc k hk) hlp
  have hnext : nextPos j i k = (coreOf j).body.length := by
    unfold nextPos
    rw [blt_falseC hn, blt_falseC hci]
    rfl
  have hd : (coreOf j).body.drop (partPos j i k) = partStmts j i k := by
    unfold partPos
    rw [hsplit, hnext, List.drop_length, List.append_nil]
  rw [hd] at hwr hxc
  have hatoms : ∀ a, Stmt.atom a ∈ partStmts j i k → Ev.atom a ∈ es := fun a ha ↦ by
    rw [hes]
    exact List.mem_append_right _ (atoms_last hshp hwr (fun h ↦ by cases h) ha)
  have H := whB_part F hlb hi (k := k)
  have hp := posZB_start H hs hst hA hatoms
  have hes' : es = ebef ++ (Out.ret erest vs).evs ++ [] := by rw [hes, List.append_nil]; rfl
  have hbody : (coreOf j).body = (coreOf j).body.take (partPos j i k) ++ partStmts j i k := by
    rw [← hd, List.take_append_drop]
  obtain ⟨-, -, h2⟩ := walkB_Z H _ _ ebef [] _ (entryRegs j fp) _ xc hwr hes' (fun h ↦ by cases h)
    (Or.inr ⟨hshp, rfl, hbody⟩) hp (cw_ok_of hres hend)
  have hdone : cw (Xp j i k) (partStmts j i k) (st0 j i k s) = .done := by
    rw [← hres]
    rcases hcr : cplRes j i k with ⟨J, c, u⟩ | ⟨J, m, c, u⟩ | _ | e
    · rw [hcr] at hend
      simp only [partEnd, blt_falseC hn, blt_falseC hci, Bool.cond_false, Bool.false_and] at hend
      cases hend
    · rw [hcr] at hend
      simp only [partEnd, blt_falseC hn, Bool.false_and] at hend
      cases hend
    · rfl
    · rw [hcr] at hend
      simp [partEnd] at hend
  obtain ⟨es', vs', he', ⟨r, cr, hr0, hrun, hcr⟩, hcells⟩ := h2 hdone
  cases he'
  refine ⟨r, cr, hr0, hrun, fun op ↦ ?_, fun k' hk' ↦ ?_⟩
  · have h1 := hcr op
    have h2 := ksum_le_sum ck (calls (ebef ++ erest)).length op
    have h3 : (xc + costW (Xp j i k).acs σ (partStmts j i k)) op =
        costW (nth Data.cplArms j []) σ (coreOf j).body op := congrFun hxc op
    rw [pmax_get j i k op, h3] at h1
    unfold pathCount
    omega
  · obtain ⟨hc1, hc2, hc3⟩ := hcells k' hk'
    have hv : vs[k'] ∈ namedOf (coreOf j).params es vs :=
      List.mem_append_right _ (List.getElem_mem hk')
    have := val_cell H.frame H.loc hv hc2 (H.fs ▸ hc3)
    rw [hc1] at this
    rw [gpow_addC]
    exact this

/-- **One part**: on to the next part, the next window, or the return. -/
theorem partB_step (F : FnHB S L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) {i k : ℕ}
    (hi : i ≤ (certOf j).cuts.length) (hk : k < nParts j i) (hr : PartReachB S L j fp σ es vs ck i k) :
    (k + 1 < nParts j i ∧ PartReachB S L j fp σ es vs ck i (k + 1)) ∨ CplGoalB S L j fp σ vs ck ∨
      (i < (certOf j).cuts.length ∧ PartReachB S L j fp σ es vs ck (i + 1) 0) := by
  have hc := F.ok i hi
  have hend := cplWin_end (hc k hk)
  by_cases hn : k + 1 < nParts j i
  · have hb : Nat.blt (k + 1) (nParts j i) = true := Nat.blt_eq.mpr hn
    have hlp : lastPart j i k = false := by simp only [lastPart, hb]; rfl
    have hnext : nextPos j i k = partPos j i (k + 1) := by
      unfold nextPos
      rw [hb]
      rfl
    obtain ⟨ebef, erest, xc, hw, hes, hxc, hres⟩ := partB_mid F hlb hi hk hr (cplWin_mid (hc k hk) hlp)
    refine Or.inl ⟨hn, ebef, erest, xc, hnext ▸ hw, hes, hnext ▸ hxc, ?_⟩
    rcases hres with ⟨J, c, u, hres, hA⟩ | ⟨J, m, c, u, hres, hA⟩
    · rw [hres] at hend
      simp only [partEnd, hb, Bool.cond_true, Bool.and_eq_true] at hend
      obtain ⟨⟨⟨hJ, hm0⟩, hle⟩, -⟩ := hend
      obtain rfl := Nat.eq_of_beq_eq_true hJ
      exact (partArrB_zero (Nat.eq_of_beq_eq_true hm0)).mpr (arrB_mono hA hle)
    · rw [hres] at hend
      simp only [partEnd, hb, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true'] at hend
      obtain ⟨⟨⟨⟨hJ, hm⟩, hm0⟩, hle⟩, -⟩ := hend
      obtain rfl := Nat.eq_of_beq_eq_true hJ
      obtain rfl := Nat.eq_of_beq_eq_true hm
      exact (partArrB_mid (fun h ↦ by rw [h, Nat.beq_refl] at hm0; cases hm0)).mpr (arrMidB_mono hA hle)
  · by_cases hci : i < (certOf j).cuts.length
    · have hbi : Nat.blt i (certOf j).cuts.length = true := Nat.blt_eq.mpr hci
      have hlp : lastPart j i k = false := by simp only [lastPart, blt_falseC hn, hbi]; rfl
      obtain ⟨ebef, erest, xc, hw, hes, hxc, hres⟩ := partB_mid F hlb hi hk hr (cplWin_mid (hc k hk) hlp)
      have hnext : nextPos j i k = partPos j (i + 1) 0 := by
        unfold nextPos partPos
        rw [blt_falseC hn, hbi, partS_zero (F.ok (i + 1) hci 0 (one_le_nParts j (i + 1)))]
        rfl
      refine Or.inr (Or.inr ⟨hci, ebef, erest, xc, hnext ▸ hw, hes, hnext ▸ hxc,
        (partArrB_zero (partM_zero (F.ok (i + 1) hci 0 (one_le_nParts j (i + 1))))).mpr ?_⟩)
      rcases hres with ⟨J, c, u, hres, hA⟩ | ⟨J, m, c, u, hres, -⟩
      · rw [hres] at hend
        simp only [partEnd, blt_falseC hn, hbi, Bool.cond_false, Bool.true_and,
          Bool.and_eq_true] at hend
        obtain ⟨⟨hJ, hle⟩, -⟩ := hend
        obtain rfl := Nat.eq_of_beq_eq_true hJ
        exact arrB_win F hci hA hle
      · rw [hres] at hend
        simp only [partEnd, blt_falseC hn, Bool.false_and] at hend
        cases hend
    · exact Or.inr (Or.inl (partB_last F hlb hi hk hr hn hci))

theorem partsB_goal (F : FnHB S L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) {i : ℕ}
    (hi : i ≤ (certOf j).cuts.length) : ∀ m k, nParts j i - k = m → k < nParts j i →
      PartReachB S L j fp σ es vs ck i k →
      CplGoalB S L j fp σ vs ck ∨ (i < (certOf j).cuts.length ∧ PartReachB S L j fp σ es vs ck (i + 1) 0) := by
  intro m
  induction m with
  | zero => intro k hm hk; omega
  | succ m ih =>
    intro k hm hk hr
    rcases partB_step F hlb hi hk hr with ⟨hk', hr'⟩ | h | h
    · exact ih (k + 1) (by omega) hk' hr'
    · exact Or.inl h
    · exact Or.inr h

theorem winsB_goal (F : FnHB S L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) :
    ∀ m i, (certOf j).cuts.length - i = m → i ≤ (certOf j).cuts.length →
      PartReachB S L j fp σ es vs ck i 0 → CplGoalB S L j fp σ vs ck := by
  intro m
  induction m with
  | zero =>
    intro i hm hi hr
    rcases partsB_goal F hlb hi _ 0 rfl (one_le_nParts j i) hr with h | ⟨hci, -⟩
    · exact h
    · omega
  | succ m ih =>
    intro i hm hi hr
    rcases partsB_goal F hlb hi _ 0 rfl (one_le_nParts j i) hr with h | ⟨hci, hr'⟩
    · exact h
    · exact ih (i + 1) (by omega) hci hr'

end Comp

/-- **B2's completeness for one compiled function**: a function the completeness check and the
soundness windows' checks accept runs, on every path, from its entry to its return within
`pathMax` and its callees' counts. -/
theorem cplB_run {j : ℕ} (h1 : 1 ≤ j) (hj : j < nFns) (hok : CplOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length,
      checkWin glob (fnOf j) (coreOf j) (certOf j) (j == 1) i = true)
    (hpows : (certOf j).facts.pows.Ok) : CplRunB S j := by
  intro κ L hκ hjt htab fp hfp σ es vs hw hev kfps hdr hF ck hK
  have F : FnHB S L j fp σ es vs kfps hdr ck := ⟨h1, hj, hok, hchk, hpows, hκ, hjt, htab, hfp, hF, hK, hev, hw⟩
  exact winsB_goal F (lastBody hok hchk) _ 0 rfl (Nat.zero_le _) (reachB_zero F)


/-! ## At the deployed semantics -/

section Deployed

variable {κ : ℕ} {L : MemImage κ}

/-- At the deployed semantics, `PartArrB` is `CplComp.lean`'s `PartArr`. -/
theorem partArrB_deployed (j fp : ℕ) (ck : List (Opcode → ℕ)) (i k n : ℕ) (x : Opcode → ℕ) :
    PartArrB blakeDeployed L j fp ck i k n x = PartArr L j fp ck i k n x := by
  simp only [PartArrB, PartArr, arrB_deployed, arrMidB_deployed]

/-- At the deployed semantics, `PartReachB` is `CplComp.lean`'s `PartReach`. -/
theorem partReachB_deployed (j fp : ℕ) (σ : Val) (es : List Ev) (vs : List V)
    (ck : List (Opcode → ℕ)) (i k : ℕ) :
    PartReachB blakeDeployed L j fp σ es vs ck i k = PartReach L j fp σ es vs ck i k := by
  simp only [PartReachB, PartReach, partArrB_deployed]

/-- At the deployed semantics, `CplGoalB` is `CplComp.lean`'s `CplGoal`. -/
theorem cplGoalB_deployed (j fp : ℕ) (σ : Val) (vs : List V) (ck : List (Opcode → ℕ)) :
    CplGoalB blakeDeployed L j fp σ vs ck = CplGoal L j fp σ vs ck := by
  simp only [CplGoalB, CplGoal, runCB_deployed]

end Deployed

end
end LeanVM.Guest.B2C
