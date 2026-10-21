/-
  LeanVM.Guest.B1.Main.CoverUnique

  The marks of `main`'s honest coverage table are distinct: its writers' numbers are the numbers
  below the table's size, each once.
-/

module

public import LeanVM.Guest.B1.Main.Cover
public import LeanVM.Guest.B1.Main.HonestOk
public import LeanVM.Guest.B1.Main.HonestWordsC

/-!
# The honest marks are distinct

A region's marks (`covOf`) are its writers' marks `g^(gl r)`, reordered: its slots are a
permutation of the region (`covOf_perm`). Over the three regions, the writers' numbers (`numsOf`)
reach every number below the coverage table's size `T` (`numsOf_cover`: a raw claim or a child's
claim, by `exists_segment`), and are `T` many (`numsOf_length`), so each is taken once
(`numsOf_nodup`): `gX`, `gS` and `gD` are injective on their writers, with disjoint ranges
(`gX_injOn`, …, `gX_ne_gS`, …). Below `2^16`, distinct numbers give distinct marks: the honest
coverage table has no repeated value (`honestCov_nodup`), over a hash too (`honestCovC_nodup`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)
open LeanVM.Guest.End (Limits)

@[expose] public section

/-! ## A region's marks -/

theorem map_idxOf_of_nodup {sl : List ℕ} (hnd : sl.Nodup) :
    sl.map sl.idxOf = List.range sl.length := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact hnd.idxOf_getElem i (by simpa using h1)

/-- **A region's marks are its writers' marks, reordered**, when its slots fill it. -/
theorem covOf_perm {sl : List ℕ} {gl : ℕ → ℕ} {n : ℕ} (hnd : sl.Nodup) (hl : sl.length = n)
    (hlt : ∀ x ∈ sl, x < n) :
    (covOf sl gl n).Perm ((List.range n).map fun r => gen ^ gl r) := by
  have hp : sl.Perm (List.range n) := by
    refine ((List.subperm_of_subset hnd fun x hx => List.mem_range.mpr (hlt x hx)).perm_of_length_le
      ?_)
    simp [hl]
  have e : (List.range n).map (fun r => gen ^ gl r) =
      sl.map (fun k => gen ^ gl (sl.idxOf k)) := by
    rw [← hl, ← map_idxOf_of_nodup hnd, List.map_map]; rfl
  rw [e, covOf]
  exact (hp.map _).symm

theorem plan_slots {α : Type} [DecidableEq α] {D W : List α} (hc : ∀ x, D.count x ≤ W.count x) :
    (assign D [] [] W).1.Nodup ∧ (assign D [] [] W).1.length = W.length ∧
      ∀ x ∈ (assign D [] [] W).1, x < W.length := by
  obtain ⟨l1, hnd, hsl⟩ := region_slots D W
  refine ⟨hnd, l1, fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := (hsl i (by omega)).1
  rw [List.getD_eq_getElem _ _ hi] at this
  rw [← assign_length_total hc] at this
  exact this

/-! ## The writers' numbers -/

section Node

variable (s : NodeStatement) (w : NodeWitness)

/-- **The writers' numbers**: the leanXMSS region's, the leanSPHINCS region's, the DA region's. -/
def numsOf : List ℕ :=
  (List.range (writersX s w).length).map (gX s w) ++ (List.range (writersS s w).length).map (gS s w) ++
    (List.range (writersD s w).length).map (gD s w)

variable {s w}

theorem hbase_mono (c : ℕ) : hbase s w c ≤ hbase s w (c + 1) := by
  unfold hbase
  have := sum_take_map_le cnw (w.children.take (c + 1)) c
  rw [List.take_take, Nat.min_eq_left (Nat.le_succ c)] at this
  omega

theorem sum_take_succ_le {γ : Type} (g : γ → ℕ) (L : List γ) {c : ℕ} (hc : c < L.length) :
    ((L.take c).map g).sum + g L[c] ≤ (L.map g).sum := by
  rw [← sum_take_succ g L c hc]; exact sum_take_map_le g L (c + 1)

/-- **Every number below the coverage table's size is a writer's.** -/
theorem numsOf_cover : ∀ e < hbase s w w.children.length, e ∈ numsOf s w := by
  intro e he
  have hx := writersX_len (s := s) (w := w)
  have hs := writersS_len (s := s) (w := w)
  have hd := writersD_len (s := s) (w := w)
  simp only [numsOf, List.mem_append, List.mem_map, List.mem_range]
  have h0 : hbase s w 0 = hrx s w + hrs s w + hrd s w := by simp [hbase]
  by_cases e1 : e < hrx s w
  · exact Or.inl (Or.inl ⟨e, by omega, gX_raw e1⟩)
  by_cases e2 : e < hrx s w + hrs s w
  · exact Or.inl (Or.inr ⟨e - hrx s w, by omega, by rw [gS_raw (by omega)]; omega⟩)
  by_cases e3 : e < hrx s w + hrs s w + hrd s w
  · exact Or.inr ⟨e - (hrx s w + hrs s w), by omega, by rw [gD_raw (by omega)]; omega⟩
  obtain ⟨c, hc, hc1, hc2⟩ := exists_segment (hbase s w) hbase_mono (by omega) _ he
  rw [hbase_succ hc, cnw] at hc2
  have sx := sum_take_succ_le cnx w.children hc
  have ss := sum_take_succ_le cns w.children hc
  have sd := sum_take_succ_le cnda w.children hc
  by_cases o1 : e - hbase s w c < cnx w.children[c]
  · refine Or.inl (Or.inl ⟨hrx s w + ((w.children.take c).map cnx).sum + (e - hbase s w c),
      by omega, ?_⟩)
    rw [gX_child hc o1]; omega
  by_cases o2 : e - hbase s w c - cnx w.children[c] < cns w.children[c]
  · refine Or.inl (Or.inr ⟨hrs s w + ((w.children.take c).map cns).sum +
      (e - hbase s w c - cnx w.children[c]), by omega, ?_⟩)
    rw [gS_child hc o2]; omega
  have o3 : e - hbase s w c - (cnx w.children[c] + cns w.children[c]) < cnda w.children[c] := by
    omega
  refine Or.inr ⟨hrd s w + ((w.children.take c).map cnda).sum +
    (e - hbase s w c - (cnx w.children[c] + cns w.children[c])), by omega, ?_⟩
  rw [gD_child hc o3]; omega

theorem numsOf_length : (numsOf s w).length = hbase s w w.children.length := by
  simp only [numsOf, List.length_append, List.length_map, List.length_range, writersX_len,
    writersS_len, writersD_len, hbase, List.take_length, sum_cnw]
  omega

/-- **The writers' numbers are those below the coverage table's size.** -/
theorem numsOf_perm : (List.range (hbase s w w.children.length)).Perm (numsOf s w) :=
  (List.subperm_of_subset List.nodup_range fun e he => numsOf_cover e (List.mem_range.mp he)
    ).perm_of_length_le (by rw [numsOf_length]; simp)

/-- **Each writer's number is taken once.** -/
theorem numsOf_nodup : (numsOf s w).Nodup :=
  numsOf_perm.nodup_iff.mp List.nodup_range

theorem numsOf_lt : ∀ e ∈ numsOf s w, e < hbase s w w.children.length :=
  fun _ he => List.mem_range.mp (numsOf_perm.mem_iff.mpr he)

/-- **The leanXMSS writers' numbers are distinct.** -/
theorem gX_injOn {r r' : ℕ} (hr : r < (writersX s w).length)
    (hr' : r' < (writersX s w).length) (h : gX s w r = gX s w r') : r = r' := by
  have hn := numsOf_nodup (s := s) (w := w)
  simp only [numsOf, List.nodup_append] at hn
  exact List.inj_on_of_nodup_map hn.1.1 (List.mem_range.mpr hr) (List.mem_range.mpr hr') h

/-- **The leanSPHINCS writers' numbers are distinct.** -/
theorem gS_injOn {r r' : ℕ} (hr : r < (writersS s w).length)
    (hr' : r' < (writersS s w).length) (h : gS s w r = gS s w r') : r = r' := by
  have hn := numsOf_nodup (s := s) (w := w)
  simp only [numsOf, List.nodup_append] at hn
  exact List.inj_on_of_nodup_map hn.1.2.1 (List.mem_range.mpr hr) (List.mem_range.mpr hr') h

/-- **The DA writers' numbers are distinct.** -/
theorem gD_injOn {r r' : ℕ} (hr : r < (writersD s w).length)
    (hr' : r' < (writersD s w).length) (h : gD s w r = gD s w r') : r = r' := by
  have hn := numsOf_nodup (s := s) (w := w)
  simp only [numsOf, List.nodup_append] at hn
  exact List.inj_on_of_nodup_map hn.2.1 (List.mem_range.mpr hr) (List.mem_range.mpr hr') h

/-- **A leanXMSS writer's and a leanSPHINCS writer's numbers differ.** -/
theorem gX_ne_gS {r r' : ℕ} (hr : r < (writersX s w).length)
    (hr' : r' < (writersS s w).length) : gX s w r ≠ gS s w r' := by
  have hn := numsOf_nodup (s := s) (w := w)
  simp only [numsOf, List.nodup_append] at hn
  exact hn.1.2.2 _ (List.mem_map_of_mem (List.mem_range.mpr hr)) _
    (List.mem_map_of_mem (List.mem_range.mpr hr'))

/-- **A leanXMSS writer's and a DA writer's numbers differ.** -/
theorem gX_ne_gD {r r' : ℕ} (hr : r < (writersX s w).length)
    (hr' : r' < (writersD s w).length) : gX s w r ≠ gD s w r' := by
  have hn := numsOf_nodup (s := s) (w := w)
  simp only [numsOf, List.nodup_append] at hn
  exact hn.2.2 _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.mpr hr))) _
    (List.mem_map_of_mem (List.mem_range.mpr hr'))

/-- **A leanSPHINCS writer's and a DA writer's numbers differ.** -/
theorem gS_ne_gD {r r' : ℕ} (hr : r < (writersS s w).length)
    (hr' : r' < (writersD s w).length) : gS s w r ≠ gD s w r' := by
  have hn := numsOf_nodup (s := s) (w := w)
  simp only [numsOf, List.nodup_append] at hn
  exact hn.2.2 _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hr))) _
    (List.mem_map_of_mem (List.mem_range.mpr hr'))

/-! ## The coverage table -/

/-- **The honest coverage table is the writers' marks, reordered.** -/
theorem honestCov_perm {seed : Digest} (hlim : Limits s w) :
    (honestWords seed s w).cov.Perm ((numsOf s w).map fun e => gen ^ e) := by
  obtain ⟨nx, lx, ltx⟩ := plan_slots (count_writersX hlim)
  obtain ⟨ns, ls, lts⟩ := plan_slots (count_writersS hlim)
  obtain ⟨nd, ld, ltd⟩ := plan_slots (count_writersD hlim)
  have ex := writersX_length hlim
  have es := writersS_length hlim
  have ed := writersD_length hlim
  simp only [numsOf, List.map_append, List.map_map, Function.comp_def, honestWords]
  rw [← ex, ← es, ← ed]
  exact ((covOf_perm nx lx ltx).append (covOf_perm ns ls lts)).append (covOf_perm nd ld ltd)

/-- **The honest coverage table has no repeated value.** -/
theorem honestCov_nodup {seed : Digest} (hlim : Limits s w) : (honestWords seed s w).cov.Nodup := by
  rw [(honestCov_perm hlim).nodup_iff]
  have ht := honest_total (seed := seed) hlim
  rw [← hbase_children (seed := seed) hlim] at ht
  refine numsOf_nodup.map_on fun a ha b hb h => gen_pow_inj' ?_ ?_ h
  · have := numsOf_lt a ha; omega
  · have := numsOf_lt b hb; omega

/-- The coverage table over a hash is the one without. -/
theorem honestWordsC_cov (Ht : List UInt8 → Digest) (seed : Digest) :
    (honestWordsC Ht seed s w).cov = (honestWords seed s w).cov := rfl

/-- **The honest coverage table over a hash has no repeated value.** -/
theorem honestCovC_nodup (Ht : List UInt8 → Digest) {seed : Digest} (hlim : Limits s w) :
    (honestWordsC Ht seed s w).cov.Nodup := by
  rw [honestWordsC_cov]; exact honestCov_nodup hlim

/-- **The honest coverage table's size**: the three regions' declared claims and duplicates. -/
theorem honestWordsC_cov_length (Ht : List UInt8 → Digest) (seed : Digest) :
    (honestWordsC Ht seed s w).cov.length = s.claims.xmss.length + (planX s w).2.length +
      (s.claims.sphincs.length + (planS s w).2.length) + (s.claims.da.length + (planD s w).2.length) := by
  simp only [honestWordsC, List.length_append, covOf_length]

end Node

end
end LeanVM.Guest.B1.Main
