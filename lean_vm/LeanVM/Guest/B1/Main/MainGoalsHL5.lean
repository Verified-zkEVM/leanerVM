/-
  LeanVM.Guest.B1.Main.MainGoalsHL5

  `main`'s honest children loop `__loop4`: complete at `main`'s words (`MainGoalL5`).
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHKid
public import LeanVM.Guest.B1.Digest.ChildListAt

/-!
# The children loop on an honest run

`plan_slot`: child `c`'s claim `j` takes a slot of its region's table, the table holds the claim
there, and the coverage word there marks the claim's global index (`cover_x`, `cover_s`,
`cover_d`: `g^(hW c + j)`, after the child's leanXMSS claims for leanSPHINCS, after both for DA).
`kidOk`: child `c` is `KidOkC` at `main`'s words, its two `child_claim_list_digest` calls
complete by `child_claim_list_digest_completeAt` and its `verify_sub` call by hypothesis.
`mainGoalL5`: `l5_completeAt` from the counter `0`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (Limits coverage)
open LeanVM.Guest.Hints (claimCells direct plan Region)
open LeanVM.Guest.B1 (CompleteAtD Returns bufL)

@[expose] public section

/-! ## A child's slots -/

/-- **Child `c`'s claim `j`'s slot**: in the table, its index among the slots, the table's claim
there. -/
theorem plan_slot {α : Type} [BEq α] [LawfulBEq α] (D R : List α) (Cs : List (List α)) {c j : ℕ}
    (hc : c < Cs.length) (hj : j < (Cs[c]).length) :
    ((plan D R Cs).children.getD c []).getD j 0 < (D ++ (plan D R Cs).dups).length ∧
      (slotsOf (plan D R Cs)).idxOf (((plan D R Cs).children.getD c []).getD j 0) = base R Cs c + j ∧
      (D ++ (plan D R Cs).dups)[((plan D R Cs).children.getD c []).getD j 0]? = some (Cs[c])[j] := by
  obtain ⟨hc', hk', hs, e1, e2⟩ := plan_child D R Cs hc hj
  have eo : ((plan D R Cs).children.getD c []).getD j 0 = ((plan D R Cs).children[c])[j] := by
    rw [List.getD_eq_getElem _ _ hc', List.getD_eq_getElem _ _ hk']
  rw [eo]
  refine ⟨plan_lt D R Cs _ (e1 ▸ List.getElem_mem hs), ?_, e2⟩
  rw [← e1]
  exact (plan_nodup D R Cs).idxOf_getElem _ hs

theorem take_map_lengths {β : Type} (L : List Child) (f : Child → List β) (c : ℕ) :
    ((L.map f).take c).map List.length = (L.map fun ch => (f ch).length).take c := by
  rw [List.map_take, List.map_map]
  rfl

variable {s : NodeStatement} {w : NodeWitness}

theorem kid_hMarkX_child {c j : ℕ} (hc : c < w.children.length)
    (hj : j < w.children[c].statement.claims.xmss.length) :
    hMarkX s w (base ((direct s.claims.xmss w.xmss).map (·.1))
      (w.children.map (·.statement.claims.xmss)) c + j) = hW s w c + j := by
  have e := kid_segOf_sum (w.children.map (·.statement.claims.xmss.length)) c j (by simpa using hc)
    (by simpa using hj)
  unfold hMarkX base
  rw [List.length_map, take_map_lengths]
  rw [ite_neg' (by unfold hRawX; omega)]
  simp only [hRawX, Nat.add_assoc, Nat.add_sub_cancel_left, e]

theorem kid_hMarkS_child {c j : ℕ} (hc : c < w.children.length)
    (hj : j < w.children[c].statement.claims.sphincs.length) :
    hMarkS s w (base ((direct s.claims.sphincs w.sphincs).map (·.1))
      (w.children.map (·.statement.claims.sphincs)) c + j) = hW s w c + hEx w c + j := by
  have e := kid_segOf_sum (w.children.map (·.statement.claims.sphincs.length)) c j (by simpa using hc)
    (by simpa using hj)
  unfold hMarkS base
  rw [List.length_map, take_map_lengths]
  rw [ite_neg' (by unfold hRawS; omega)]
  simp only [hRawS, Nat.add_assoc, Nat.add_sub_cancel_left, e]

theorem kid_hMarkD_child {c j : ℕ} (hc : c < w.children.length)
    (hj : j < w.children[c].statement.claims.da.length) :
    hMarkD s w (base ((direct s.claims.da w.da).map (·.1))
      (w.children.map (·.statement.claims.da)) c + j) = hW s w c + hEx w c + hEs w c + j := by
  have e := kid_segOf_sum (w.children.map (·.statement.claims.da.length)) c j (by simpa using hc)
    (by simpa using hj)
  unfold hMarkD base
  rw [List.length_map, take_map_lengths]
  rw [ite_neg' (by unfold hRawD; omega)]
  simp only [hRawD, Nat.add_assoc, Nat.add_sub_cancel_left, e]

/-! ## The coverage table -/

theorem kid_length_hCover : (hCover s w).length = s.claims.xmss.length + (xPlan s w).dups.length +
    (s.claims.sphincs.length + (sPlan s w).dups.length) +
    (s.claims.da.length + (dPlan s w).dups.length) := by
  simp only [hCover, List.length_append, List.length_map, List.length_range]

theorem kid_hCover_x {t : ℕ} (ht : t < s.claims.xmss.length + (xPlan s w).dups.length) :
    (hCover s w).getD t 0 = gen ^ hMarkX s w ((slotsOf (xPlan s w)).idxOf t) := by
  unfold hCover
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_left (by simpa using ht),
    List.getElem?_map, List.getElem?_range (by simpa using ht)]
  rfl

theorem kid_hCover_s {t : ℕ} (ht : t < s.claims.sphincs.length + (sPlan s w).dups.length) :
    (hCover s w).getD (s.claims.xmss.length + (xPlan s w).dups.length + t) 0 =
      gen ^ hMarkS s w ((slotsOf (sPlan s w)).idxOf t) := by
  unfold hCover
  rw [List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right (by simp only [List.length_map, List.length_range, List.length_append]; omega),
    List.getElem?_append_left (by simp only [List.length_map, List.length_range, List.length_append]; omega),
    List.getElem?_map]
  simp only [List.length_map, List.length_range, List.length_append, Nat.add_sub_cancel_left]
  rw [List.getElem?_range (by simpa using ht)]
  rfl

theorem kid_hCover_d {t : ℕ} (ht : t < s.claims.da.length + (dPlan s w).dups.length) :
    (hCover s w).getD (s.claims.xmss.length + (xPlan s w).dups.length +
      (s.claims.sphincs.length + (sPlan s w).dups.length) + t) 0 =
      gen ^ hMarkD s w ((slotsOf (dPlan s w)).idxOf t) := by
  unfold hCover
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp only [List.length_append, List.length_map, List.length_range]; omega),
    List.getElem?_map]
  simp only [List.length_append, List.length_map, List.length_range, Nat.add_sub_cancel_left]
  rw [List.getElem?_range (by simpa using ht)]
  rfl

theorem loadHolds_getD {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ}
    (hk : k < xs.length) : LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

theorem kid_length_flatMap_const {α : Type} {f : α → List E} {k : ℕ} :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = k) → (l.flatMap f).length = k * l.length
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, h a List.mem_cons_self,
      kid_length_flatMap_const l fun b hb => h b (List.mem_cons_of_mem _ hb), List.length_cons]
    ring

theorem getD_range_map (f : ℕ → E) {n c : ℕ} (hc : c < n) : ((List.range n).map f).getD c 0 = f c := by
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]

/-! ## `main`'s words -/

/-- Buffer `i`'s first word. -/
abbrev hP (fs : String → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement) (w : NodeWitness) (i : ℕ) :
    ℕ :=
  (mPos (hData seed s w) (fp + fs "main")).getD i 0

/-- **`main`'s honest buffers**, as the children loop reads them. -/
theorem reads_buf (fs : String → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement) (w : NodeWitness)
    {rd : Reader} (hM : B1.Main.MemL rd (hLmain fs fp seed s w)) :
    ReadsAt rd (gen ^ hP fs fp seed s w 0) ((s.claims.da ++ (dPlan s w).dups).flatMap daCells) ∧
    ReadsAt rd (gen ^ hP fs fp seed s w 1)
      ((s.claims.xmss ++ (xPlan s w).dups).flatMap fun c => claimCells c.1.root c.1.parameter c.2) ∧
    ReadsAt rd (gen ^ hP fs fp seed s w 2)
      ((s.claims.sphincs ++ (sPlan s w).dups).flatMap fun c => claimCells c.1.root c.1.parameter c.2) ∧
    ReadsAt rd (gen ^ hP fs fp seed s w 3) (hCover s w) ∧
    ReadsAt rd (gen ^ hP fs fp seed s w 5)
      (w.children.flatMap fun c => B1.Digest.digestCells (statementDigest seed c.statement)) ∧
    ReadsAt rd (gen ^ hP fs fp seed s w 7) (w.children.flatMap fun c => c.statement.defer.cells) ∧
    ReadsAt rd (gen ^ hP fs fp seed s w 8)
      ((List.range (w.children.length + 1)).map fun c => gen ^ hW s w c) := by
  have r0 := reads_hLmain fs fp seed s w hM (i := 0) (by omega)
  have r1 := reads_hLmain fs fp seed s w hM (i := 1) (by omega)
  have r2 := reads_hLmain fs fp seed s w hM (i := 2) (by omega)
  have r4 := reads_hLmain fs fp seed s w hM (i := 3) (by omega)
  have r6 := reads_hLmain fs fp seed s w hM (i := 5) (by omega)
  have r8 := reads_hLmain fs fp seed s w hM (i := 7) (by omega)
  have r9 := reads_hLmain fs fp seed s w hM (i := 8) (by omega)
  simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero] at r0 r1 r2 r4 r6 r8 r9
  exact ⟨r0, r1, r2, r4, r6, r8, r9⟩

theorem region_buf (fs : String → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement) (w : NodeWitness)
    {i k : ℕ} (hi : i < 10) (hk : k < ((hOwn seed s w).getD i []).length) :
    B1.Main.RegionL (hLmain fs fp seed s w) (hP fs fp seed s w i + k) :=
  B1.Da.regionL_of_mem (mem_hLmain fs fp seed s w hi) hk

variable {fs : String → ℕ} {fp : ℕ} {seed : Digest}

/-! ## Child `c` -/

theorem belowLog_of {o L : ℕ} (h : o < L) (hL : L < 2 ^ 32) : B1.Digest.BelowLog (gen ^ L) o :=
  ⟨by omega, L - o - 1, by omega, by congr 1; omega⟩

theorem cover_bound (hl : Limits s w) :
    s.claims.xmss.length + (xPlan s w).dups.length +
      (s.claims.sphincs.length + (sPlan s w).dups.length) +
      (s.claims.da.length + (dPlan s w).dups.length) < 2 ^ 16 := by
  have hcov := hl.coverage
  rw [coverage_eq] at hcov
  simp only [List.length_append] at hcov
  omega

/-- **Child `c`'s leanXMSS list is complete.** -/
theorem kid_hX (cert : String → V → ℕ) (hl : Limits s w) {c : ℕ}
    (hc : c < w.children.length) :
    CompleteAtD fs cert 16 "child_claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a77, (hm fs fp seed s w).a117, (hKid s w c).base, 1,
        gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd), gen ^ (hKid s w c).ex]
      (Returns [(hKid s w c).cx.1, (hKid s w c).cx.2]) := by
  have hcov := cover_bound hl
  have hlen := (hl.lists _ (List.getElem_mem hc)).1
  have hT := kid_length_flatMap_const (f := fun c : XmssClaim => claimCells c.1.root c.1.parameter c.2)
    (s.claims.xmss ++ (xPlan s w).dups) fun a _ => kid_length_claimCells _ _ _
  rw [List.length_append] at hT
  have slot := fun j (hj : j < w.children[c].statement.claims.xmss.length) =>
    plan_slot s.claims.xmss ((direct s.claims.xmss w.xmss).map (·.1))
      (w.children.map (·.statement.claims.xmss)) (c := c) (j := j) (by simpa using hc)
      (by simpa using hj)
  have := B1.Digest.child_claim_list_digest_completeAt fs cert (κ := 16) le_rfl
    (Lin := hLmain fs fp seed s w) (eP := hP fs fp seed s w 1) (cv := hP fs fp seed s w 3) (og := 0)
    (L := s.claims.xmss.length + (xPlan s w).dups.length) (n := (hKid s w c).ex)
    (base := (hKid s w c).base) (o := fun j => ((xPlan s w).children.getD c []).getD j 0)
    (cells := w.children[c].statement.claims.xmss.flatMap fun c => claimCells c.1.root c.1.parameter c.2)
    (by rw [hKid_ex hc]; simp only [B1.Digest.claimGroup, B1.Digest.maxKeys]; omega)
    (by rw [hKid_ex hc]; exact kid_length_flatMap_const _ fun a _ => kid_length_claimCells _ _ _)
    (fun x hx => by
      obtain ⟨a, -, hx⟩ := List.mem_flatMap.mp hx
      exact claimCells_canonical _ _ _ x hx)
    (by omega) (by omega)
    (fun rd hM j hj => by
      rw [hKid_ex hc] at hj
      obtain ⟨hlt, hidx, hget⟩ := slot j hj
      have hlt' : ((xPlan s w).children.getD c []).getD j 0 <
          s.claims.xmss.length + (xPlan s w).dups.length := by
        have := hlt; rw [List.length_append] at this; exact this
      obtain ⟨r0, r1, r2, r4, -⟩ := reads_buf fs fp seed s w hM
      refine ⟨belowLog_of hlt' (by omega), ?_, fun i hi => ?_⟩
      · rw [pow_zero, one_mul, loadHolds_mul_gen_pow, Nat.add_zero,
          show (hKid s w c).base * gen ^ j = gen ^ (hW s w c + j) from (pow_add _ _ _).symm]
        have := loadHolds_getD r4 (k := ((xPlan s w).children.getD c []).getD j 0)
          (by rw [kid_length_hCover]; omega)
        rw [kid_hCover_x hlt', show (slotsOf (xPlan s w)).idxOf (((xPlan s w).children.getD c []).getD j 0) =
          _ from hidx, kid_hMarkX_child hc hj] at this
        exact this
      · have hlt2 : ((xPlan s w).children.getD c []).getD j 0 <
            (s.claims.xmss ++ (xPlan s w).dups).length := hlt
        have := loadHolds_getD r1 (k := 4 * ((xPlan s w).children.getD c []).getD j 0 + i)
          (by rw [hT]; omega)
        rw [getD_flatMap_uniform (f := fun c => claimCells c.1.root c.1.parameter c.2) _
          (fun a _ => kid_length_claimCells _ _ _) _ hlt2 i hi] at this
        have eT : (s.claims.xmss ++ (xPlan s w).dups)[((xPlan s w).children.getD c []).getD j 0]'hlt2 =
            w.children[c].statement.claims.xmss[j] := by
          have h := hget
          change (s.claims.xmss ++ (xPlan s w).dups)[((xPlan s w).children.getD c []).getD j 0]? = _ at h
          rw [List.getElem?_eq_getElem hlt2] at h
          simpa using h
        rw [eT] at this
        rw [getD_flatMap_uniform (f := fun c => claimCells c.1.root c.1.parameter c.2) _
          (fun a _ => kid_length_claimCells _ _ _) j hj i hi]
        exact this)
    (fun j hj => by
      rw [hKid_ex hc] at hj
      have hlt' : ((xPlan s w).children.getD c []).getD j 0 <
          s.claims.xmss.length + (xPlan s w).dups.length := by
        have := (slot j hj).1; rw [List.length_append] at this; exact this
      rw [Nat.add_assoc]
      exact region_buf fs fp seed s w (i := 3) (by omega)
        (show _ < (hCover s w).length by rw [kid_length_hCover]; omega))
    (fun j hj i hi => by
      rw [hKid_ex hc] at hj
      have hlt' : ((xPlan s w).children.getD c []).getD j 0 <
          s.claims.xmss.length + (xPlan s w).dups.length := by
        have := (slot j hj).1; rw [List.length_append] at this; exact this
      rw [Nat.add_assoc]
      exact region_buf fs fp seed s w (i := 1) (by omega)
        (show _ < ((s.claims.xmss ++ (xPlan s w).dups).flatMap
          fun c => claimCells c.1.root c.1.parameter c.2).length by rw [hT]; omega))
  rw [hKid_cx hc, xmssList_cells]
  rwa [pow_zero] at this

/-- **Child `c`'s leanSPHINCS list is complete.** -/
theorem kid_hS (cert : String → V → ℕ) (hl : Limits s w) {c : ℕ}
    (hc : c < w.children.length) :
    CompleteAtD fs cert 16 "child_claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a80, (hm fs fp seed s w).a117, (hKid s w c).base * gen ^ (hKid s w c).ex,
        gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd), gen ^ (hKid s w c).es]
      (Returns [(hKid s w c).cs.1, (hKid s w c).cs.2]) := by
  have hcov := cover_bound hl
  have hlen := (hl.lists _ (List.getElem_mem hc)).2
  have hT := kid_length_flatMap_const (f := fun c : SphincsClaim => claimCells c.1.root c.1.parameter c.2)
    (s.claims.sphincs ++ (sPlan s w).dups) fun a _ => kid_length_claimCells _ _ _
  rw [List.length_append] at hT
  have slot := fun j (hj : j < w.children[c].statement.claims.sphincs.length) =>
    plan_slot s.claims.sphincs ((direct s.claims.sphincs w.sphincs).map (·.1))
      (w.children.map (·.statement.claims.sphincs)) (c := c) (j := j) (by simpa using hc)
      (by simpa using hj)
  have := B1.Digest.child_claim_list_digest_completeAt fs cert (κ := 16) le_rfl
    (Lin := hLmain fs fp seed s w) (eP := hP fs fp seed s w 2) (cv := hP fs fp seed s w 3)
    (og := s.claims.xmss.length + (xPlan s w).dups.length)
    (L := s.claims.sphincs.length + (sPlan s w).dups.length) (n := (hKid s w c).es)
    (base := (hKid s w c).base * gen ^ (hKid s w c).ex)
    (o := fun j => ((sPlan s w).children.getD c []).getD j 0)
    (cells := w.children[c].statement.claims.sphincs.flatMap
      fun c => claimCells c.1.root c.1.parameter c.2)
    (by rw [hKid_es hc]; simp only [B1.Digest.claimGroup, B1.Digest.maxKeys]; omega)
    (by rw [hKid_es hc]; exact kid_length_flatMap_const _ fun a _ => kid_length_claimCells _ _ _)
    (fun x hx => by
      obtain ⟨a, -, hx⟩ := List.mem_flatMap.mp hx
      exact claimCells_canonical _ _ _ x hx)
    (by omega) (by omega)
    (fun rd hM j hj => by
      rw [hKid_es hc] at hj
      obtain ⟨hlt, hidx, hget⟩ := slot j hj
      have hlt' : ((sPlan s w).children.getD c []).getD j 0 <
          s.claims.sphincs.length + (sPlan s w).dups.length := by
        have := hlt; rw [List.length_append] at this; exact this
      obtain ⟨r0, r1, r2, r4, -⟩ := reads_buf fs fp seed s w hM
      refine ⟨belowLog_of hlt' (by omega), ?_, fun i hi => ?_⟩
      · rw [← pow_add, loadHolds_mul_gen_pow, Nat.add_zero,
          show (hKid s w c).base * gen ^ (hKid s w c).ex * gen ^ j = gen ^ (hW s w c + hEx w c + j) by
            rw [pow_add, pow_add]; rfl]
        have := loadHolds_getD r4 (k := s.claims.xmss.length + (xPlan s w).dups.length +
          ((sPlan s w).children.getD c []).getD j 0) (by rw [kid_length_hCover]; omega)
        rw [kid_hCover_s hlt', show (slotsOf (sPlan s w)).idxOf (((sPlan s w).children.getD c []).getD j 0) =
          _ from hidx, kid_hMarkS_child hc hj] at this
        exact this
      · have hlt2 : ((sPlan s w).children.getD c []).getD j 0 <
            (s.claims.sphincs ++ (sPlan s w).dups).length := hlt
        have := loadHolds_getD r2 (k := 4 * ((sPlan s w).children.getD c []).getD j 0 + i)
          (by rw [hT]; omega)
        rw [getD_flatMap_uniform (f := fun c => claimCells c.1.root c.1.parameter c.2) _
          (fun a _ => kid_length_claimCells _ _ _) _ hlt2 i hi] at this
        have eT : (s.claims.sphincs ++ (sPlan s w).dups)[((sPlan s w).children.getD c []).getD j 0]'hlt2 =
            w.children[c].statement.claims.sphincs[j] := by
          have h := hget
          change (s.claims.sphincs ++ (sPlan s w).dups)[((sPlan s w).children.getD c []).getD j 0]? = _ at h
          rw [List.getElem?_eq_getElem hlt2] at h
          simpa using h
        rw [eT] at this
        rw [getD_flatMap_uniform (f := fun c => claimCells c.1.root c.1.parameter c.2) _
          (fun a _ => kid_length_claimCells _ _ _) j hj i hi]
        exact this)
    (fun j hj => by
      rw [hKid_es hc] at hj
      have hlt' : ((sPlan s w).children.getD c []).getD j 0 <
          s.claims.sphincs.length + (sPlan s w).dups.length := by
        have := (slot j hj).1; rw [List.length_append] at this; exact this
      rw [Nat.add_assoc]
      exact region_buf fs fp seed s w (i := 3) (by omega)
        (show _ < (hCover s w).length by rw [kid_length_hCover]; omega))
    (fun j hj i hi => by
      rw [hKid_es hc] at hj
      have hlt' : ((sPlan s w).children.getD c []).getD j 0 <
          s.claims.sphincs.length + (sPlan s w).dups.length := by
        have := (slot j hj).1; rw [List.length_append] at this; exact this
      rw [Nat.add_assoc]
      exact region_buf fs fp seed s w (i := 2) (by omega)
        (show _ < ((s.claims.sphincs ++ (sPlan s w).dups).flatMap
          fun c => claimCells c.1.root c.1.parameter c.2).length by rw [hT]; omega))
  rw [hKid_cs hc, sphincsList_cells]
  exact this

/-- The children's statement digests' cells, two a child. -/
theorem length_piCells : (w.children.flatMap fun c =>
    B1.Digest.digestCells (statementDigest seed c.statement)).length = 2 * w.children.length :=
  kid_length_flatMap_const _ fun _ _ => rfl

/-- **Child `c` is as `__loop4` needs it**, at `main`'s honest words. -/
theorem kidOk (cert : String → V → ℕ) {bytecode : List K}
    (hbl : bytecode.length = 2 ^ bytecodeVars) (hrel : NodeRel bytecode seed s w)
    (hl : Limits s w)
    (hV : ∀ c (hc : c < w.children.length), CompleteAtD fs cert 16 "verify_sub" (hLmain fs fp seed s w)
      [(digestScalars (statementDigest seed w.children[c].statement)).1,
        (digestScalars (statementDigest seed w.children[c].statement)).2,
        (digestScalars seed).1, (digestScalars seed).2, (hm fs fp seed s w).et1,
        (hm fs fp seed s w).et2, (hm fs fp seed s w).a400 * gen ^ (24 * c)] (Returns []))
    {c : ℕ} (hc : c < w.children.length) :
    KidOkC fs cert (hLmain fs fp seed s w) (hP fs fp seed s w 8) (hP fs fp seed s w 5)
      (hP fs fp seed s w 7) (hP fs fp seed s w 0)
      (hP fs fp seed s w 3 + (s.claims.xmss.length + (xPlan s w).dups.length +
        (s.claims.sphincs.length + (sPlan s w).dups.length)))
      (s.claims.da.length + (dPlan s w).dups.length)
      (hm fs fp seed s w).a77 (hm fs fp seed s w).a117
      (gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd)) (hm fs fp seed s w).a80
      (gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd))
      (digestScalars seed).1 (digestScalars seed).2 (hm fs fp seed s w).et1 (hm fs fp seed s w).et2
      (hm fs fp seed s w).a400 c (hKid s w c) := by
  have hcov := cover_bound hl
  have hsh := kid_shapes hbl hrel
  have hb : bytecodeVars = 23 := rfl
  have hmem := List.getElem_mem hc
  have hdl : w.children[c].statement.defer.cells.length = 24 := by
    simp [DeferredClaim.cells, (hsh _ hmem).2, hb]
  have hpi := hKid_pi seed (s := s) hc hdl
  have hed : (hKid s w c).ed = w.children[c].statement.claims.da.length := hKid_ed hc
  have hed16 := hl.daRoots.2 _ hmem
  have hDT := kid_length_flatMap_const (f := daCells) (s.claims.da ++ (dPlan s w).dups)
    fun a _ => kid_length_daCells a
  rw [List.length_append] at hDT
  have slot := fun d (hd : d < w.children[c].statement.claims.da.length) =>
    plan_slot s.claims.da ((direct s.claims.da w.da).map (·.1))
      (w.children.map (·.statement.claims.da)) (c := c) (j := d) (by simpa using hc)
      (by simpa using hd)
  have hslot : ∀ d < (hKid s w c).ed, (hKid s w c).slot d <
      s.claims.da.length + (dPlan s w).dups.length := fun d hd => by
    rw [hed] at hd
    have := (slot d hd).1; rw [List.length_append] at this; exact this
  have hW1 : hW s w (c + 1) = hW s w c + (hEx w c + hEs w c) + hEd w c := by
    simp only [hW]; omega
  refine ⟨?_, ?_, by rw [hed]; exact hed16, ?_, hKid_root_len c, ?_, hslot,
    by rw [hKid_defer hc]; exact hdl, fun rd hM => ?_, ?_, kid_hX cert hl hc, kid_hS cert hl hc,
    by rw [hpi]; exact hV c hc⟩
  · rw [hKid_ex hc]; have := (hl.lists _ hmem).1; omega
  · rw [hKid_es hc]; have := (hl.lists _ hmem).2; omega
  · rw [hKid_cx hc, hKid_cs hc]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (digestScalars_canonical _).1
    · exact (digestScalars_canonical _).2
    · exact (digestScalars_canonical _).1
    · exact (digestScalars_canonical _).2
  · rw [hKid_cdaW hc]
    intro x hx
    obtain ⟨a, -, hx⟩ := List.mem_flatMap.mp hx
    exact daCells_canonical a x hx
  · -- the memory
    obtain ⟨r0, -, -, r4, r6, r8, r9⟩ := reads_buf fs fp seed s w hM
    have p6 := readsAt_flatMap_of (w := 2) w.children (fun _ _ => rfl) r6 c hc
    have p8 := readsAt_flatMap_of (w := 24) w.children
      (fun a ha => by simp [DeferredClaim.cells, (hsh a ha).2, hb]) r8 c hc
    refine ⟨?_, ?_, ?_, ?_, ?_, fun d hd => ⟨?_, ?_⟩⟩
    · have := loadHolds_getD r9 (k := c) (by simp; omega)
      rwa [getD_range_map _ (by omega)] at this
    · have := loadHolds_getD r9 (k := c + 1) (by simp; omega)
      rw [getD_range_map _ (by omega), hW1, pow_add, pow_add, pow_add] at this
      exact this
    · have := p6 0 (by simp [B1.Digest.digestCells])
      rw [loadHolds_mul_gen_pow, Nat.add_zero] at this
      rw [hpi]; exact this
    · have := p6 1 (by simp [B1.Digest.digestCells])
      rw [loadHolds_mul_gen_pow] at this
      rw [hpi]; exact this
    · rw [pow_add, hKid_defer hc]; exact p8
    · have hd' := hd
      rw [hed] at hd'
      obtain ⟨hlt, hidx, -⟩ := slot d hd'
      have hlt' : (hKid s w c).slot d < s.claims.da.length + (dPlan s w).dups.length := by
        have := hlt; rw [List.length_append] at this; exact this
      rw [pow_add, loadHolds_mul_gen_pow]
      have := loadHolds_getD r4 (k := s.claims.xmss.length + (xPlan s w).dups.length +
        (s.claims.sphincs.length + (sPlan s w).dups.length) + (hKid s w c).slot d)
        (by rw [kid_length_hCover]; omega)
      rw [kid_hCover_d hlt', show (slotsOf (dPlan s w)).idxOf ((hKid s w c).slot d) = _ from hidx,
        kid_hMarkD_child hc hd', pow_add, pow_add, pow_add] at this
      rw [← mul_assoc]
      exact this
    · have hd' := hd
      rw [hed] at hd'
      obtain ⟨hlt, -, hget⟩ := slot d hd'
      have hlt2 : (hKid s w c).slot d < (s.claims.da ++ (dPlan s w).dups).length := hlt
      have := readsAt_flatMap_of (w := 4) _ (fun a _ => kid_length_daCells a) r0 _ hlt2
      have eT : (s.claims.da ++ (dPlan s w).dups)[(hKid s w c).slot d]'hlt2 =
          w.children[c].statement.claims.da[d] := by
        have h := hget
        change (s.claims.da ++ (dPlan s w).dups)[(hKid s w c).slot d]? = _ at h
        rw [List.getElem?_eq_getElem hlt2] at h
        simpa using h
      rw [eT, ← pow_add] at this
      rw [hKid_root hc hd']
      exact this
  · -- the regions
    have hlenW : ((hOwn seed s w).getD 8 []).length = w.children.length + 1 := by
      simp [hOwn]
    have hlenPi : ((hOwn seed s w).getD 5 []).length = 2 * w.children.length := length_piCells
    refine ⟨region_buf fs fp seed s w (by omega) (by rw [hlenW]; omega), ?_,
      region_buf fs fp seed s w (by omega) (by rw [hlenPi]; omega), ?_, fun d hd => ⟨?_, fun i hi => ?_⟩⟩
    · rw [Nat.add_assoc]; exact region_buf fs fp seed s w (by omega) (by rw [hlenW]; omega)
    · rw [Nat.add_assoc]; exact region_buf fs fp seed s w (by omega) (by rw [hlenPi]; omega)
    · have := hslot d hd
      rw [Nat.add_assoc]
      exact region_buf fs fp seed s w (i := 3) (by omega)
        (show _ < (hCover s w).length by rw [kid_length_hCover]; omega)
    · have := hslot d hd
      rw [Nat.add_assoc]
      exact region_buf fs fp seed s w (i := 0) (by omega)
        (show _ < ((s.claims.da ++ (dPlan s w).dups).flatMap daCells).length by rw [hDT]; omega)

/-- **`main`'s honest children loop is complete**: under `NodeRel` and `Limits`, for a bytecode of
`2^bytecodeVars` words, given each child's `verify_sub` call complete at `main`'s words. -/
theorem mainGoalL5 (cert : String → V → ℕ) {bytecode : List K}
    (hbl : bytecode.length = 2 ^ bytecodeVars) (hrel : NodeRel bytecode seed s w)
    (hl : Limits s w)
    (hV : ∀ c (hc : c < w.children.length), CompleteAtD fs cert 16 "verify_sub" (hLmain fs fp seed s w)
      [(digestScalars (statementDigest seed w.children[c].statement)).1,
        (digestScalars (statementDigest seed w.children[c].statement)).2,
        (digestScalars seed).1, (digestScalars seed).2, (hm fs fp seed s w).et1,
        (hm fs fp seed s w).et2, (hm fs fp seed s w).a400 * gen ^ (24 * c)] (Returns [])) :
    MainGoalL5 fs cert fp seed s w := by
  intro hnc
  have hcov := cover_bound hl
  have hnc16 := hl.children
  have h := l5_completeAt fs cert (Lin := hLmain fs fp seed s w) (W := hP fs fp seed s w 8)
    (Pi := hP fs fp seed s w 5) (Cr := hP fs fp seed s w 7) (R := hP fs fp seed s w 0)
    (C := hP fs fp seed s w 3 + (s.claims.xmss.length + (xPlan s w).dups.length +
      (s.claims.sphincs.length + (sPlan s w).dups.length)))
    (n := s.claims.da.length + (dPlan s w).dups.length) (nk := w.children.length)
    (kid := hKid s w) (by omega) (by omega)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact (digestScalars_canonical _).1
      · exact (digestScalars_canonical _).2)
    (fun c hc => kidOk cert hbl hrel hl hV hc) 0 (by have : w.children.length ≠ 0 := hnc; omega)
  rw [show (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd +
      ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd)) = gen ^ (hP fs fp seed s w 3 +
      (s.claims.xmss.length + (xPlan s w).dups.length +
        (s.claims.sphincs.length + (sPlan s w).dups.length))) from (pow_add _ _ _).symm]
  rw [pow_zero] at h
  exact h

end
end LeanVM.Guest.B1.Main
