/-
  LeanVM.Guest.B1.Main.ChildSlots

  Each claim of a child of `main` has a slot of its region in the honest coverage table, marked
  with the writer's number the running counts give it, where the region's table holds the claim.
-/

module

public import LeanVM.Guest.B1.Main.CoverUnique

/-!
# A child's slots

Child `c`'s writers are numbered from `hbase s w c`: its leanXMSS claims, then its leanSPHINCS
claims, then its DA claims (`hbase_succ`, `gX_child`, …). Each has a slot of its region
(`region_writer_slot`, from `region_slots`) where the honest coverage table holds its mark and the
region's table its claim (`honest_child_slots`). The running counts' table holds `g^(hbase s w c)`
(`honestWordsC_wTab`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)

@[expose] public section

theorem covOf_getElem? {sl : List ℕ} {gl : ℕ → ℕ} {n : ℕ} (hnd : sl.Nodup) {r : ℕ}
    (hr : r < sl.length) (hn : sl.getD r 0 < n) :
    (covOf sl gl n)[sl.getD r 0]? = some (gen ^ gl r) := by
  rw [List.getElem?_eq_getElem (by rw [covOf_length]; exact hn), covOf_slot hnd hr hn]

/-- **A region's writer has a slot**, marked with its number, holding its claim. -/
theorem region_writer_slot {α : Type} [DecidableEq α] (D W : List α) (gl : ℕ → ℕ) {r : ℕ}
    (hr : r < W.length) : ∃ sl < D.length + (assign D [] [] W).2.length,
      (covOf (assign D [] [] W).1 gl (D.length + (assign D [] [] W).2.length))[sl]? =
        some (gen ^ gl r) ∧ (D ++ (assign D [] [] W).2)[sl]? = W[r]? := by
  obtain ⟨l1, hnd, hsl⟩ := region_slots D W
  obtain ⟨h1, h2⟩ := hsl r hr
  exact ⟨_, h1, covOf_getElem? hnd (by omega) h1, h2⟩

section Node

variable {s : NodeStatement} {w : NodeWitness}

theorem honestWordsC_cov_eq (Ht : List UInt8 → Digest) (seed : Digest) :
    (honestWordsC Ht seed s w).cov =
      covOf (planX s w).1 (gX s w) (s.claims.xmss.length + (planX s w).2.length) ++
      covOf (planS s w).1 (gS s w) (s.claims.sphincs.length + (planS s w).2.length) ++
      covOf (planD s w).1 (gD s w) (s.claims.da.length + (planD s w).2.length) := rfl

/-- **Child `c`'s claims in the coverage table**: its writers' numbers run from `hbase s w c`,
its leanXMSS claims', then its leanSPHINCS claims', then its DA claims'; each claim has a slot of
its region, marked with its writer's number, where the region's table holds the claim. -/
theorem honest_child_slots (Ht : List UInt8 → Digest) (seed : Digest) {c : ℕ}
    (hc : c < w.children.length) :
    hbase s w (c + 1) = hbase s w c + (w.children[c].statement.claims.xmss.length +
      w.children[c].statement.claims.sphincs.length + w.children[c].statement.claims.da.length) ∧
    (∀ j (hj : j < w.children[c].statement.claims.xmss.length),
      ∃ sl < s.claims.xmss.length + (planX s w).2.length,
        (honestWordsC Ht seed s w).cov[sl]? = some (gen ^ (hbase s w c + j)) ∧
        (s.claims.xmss ++ (planX s w).2)[sl]? = some w.children[c].statement.claims.xmss[j]) ∧
    (∀ j (hj : j < w.children[c].statement.claims.sphincs.length),
      ∃ sl < s.claims.sphincs.length + (planS s w).2.length,
        (honestWordsC Ht seed s w).cov[s.claims.xmss.length + (planX s w).2.length + sl]? =
          some (gen ^ (hbase s w c + (w.children[c].statement.claims.xmss.length + j))) ∧
        (s.claims.sphincs ++ (planS s w).2)[sl]? = some w.children[c].statement.claims.sphincs[j]) ∧
    (∀ j (hj : j < w.children[c].statement.claims.da.length),
      ∃ i < s.claims.da.length + (planD s w).2.length,
        (honestWordsC Ht seed s w).cov[s.claims.xmss.length + (planX s w).2.length +
          (s.claims.sphincs.length + (planS s w).2.length) + i]? =
          some (gen ^ (hbase s w c + (w.children[c].statement.claims.xmss.length +
            w.children[c].statement.claims.sphincs.length + j))) ∧
        (s.claims.da ++ (planD s w).2)[i]? = some w.children[c].statement.claims.da[j]) := by
  have sx := sum_take_succ_le cnx w.children hc
  have ss := sum_take_succ_le cns w.children hc
  have sd := sum_take_succ_le cnda w.children hc
  have lx := writersX_len (s := s) (w := w)
  have ls := writersS_len (s := s) (w := w)
  have ld := writersD_len (s := s) (w := w)
  rw [honestWordsC_cov_eq]
  refine ⟨by rw [hbase_succ hc]; rfl, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have hr : hrx s w + ((w.children.take c).map cnx).sum + j < (writersX s w).length := by
      simp only [cnx] at sx ⊢; omega
    obtain ⟨sl, h1, h2, h3⟩ := region_writer_slot s.claims.xmss (writersX s w) (gX s w) hr
    change sl < s.claims.xmss.length + (planX s w).2.length at h1
    refine ⟨sl, h1, ?_, ?_⟩
    · rw [List.append_assoc, List.getElem?_append_left (by rw [covOf_length]; exact h1)]
      rw [gX_child hc hj] at h2
      exact h2
    · rw [show s.claims.xmss ++ (planX s w).2 = s.claims.xmss ++ (assign s.claims.xmss [] []
        (writersX s w)).2 from rfl, h3, writersX_child hc hj, List.getElem?_eq_getElem hj]
  · have hr : hrs s w + ((w.children.take c).map cns).sum + j < (writersS s w).length := by
      simp only [cns] at ss ⊢; omega
    obtain ⟨sl, h1, h2, h3⟩ := region_writer_slot s.claims.sphincs (writersS s w) (gS s w) hr
    change sl < s.claims.sphincs.length + (planS s w).2.length at h1
    refine ⟨sl, h1, ?_, ?_⟩
    · rw [List.getElem?_append_left (by simp only [List.length_append, covOf_length]; omega),
        List.getElem?_append_right (by rw [covOf_length]; omega), covOf_length,
        Nat.add_sub_cancel_left]
      rw [gS_child hc hj, Nat.add_assoc] at h2
      exact h2
    · rw [show s.claims.sphincs ++ (planS s w).2 = s.claims.sphincs ++ (assign s.claims.sphincs []
        [] (writersS s w)).2 from rfl, h3, writersS_child hc hj, List.getElem?_eq_getElem hj]
  · have hr : hrd s w + ((w.children.take c).map cnda).sum + j < (writersD s w).length := by
      simp only [cnda] at sd ⊢; omega
    obtain ⟨i, h1, h2, h3⟩ := region_writer_slot s.claims.da (writersD s w) (gD s w) hr
    change i < s.claims.da.length + (planD s w).2.length at h1
    refine ⟨i, h1, ?_, ?_⟩
    · rw [List.getElem?_append_right (by simp only [List.length_append, covOf_length]; omega)]
      simp only [List.length_append, covOf_length, Nat.add_sub_cancel_left]
      rw [gD_child hc hj, Nat.add_assoc] at h2
      exact h2
    · rw [show s.claims.da ++ (planD s w).2 = s.claims.da ++ (assign s.claims.da [] []
        (writersD s w)).2 from rfl, h3, writersD_child hc hj, List.getElem?_eq_getElem hj]

/-- **The running counts' table** holds `g^(hbase s w c)` at each child `c`, and after the last. -/
theorem honestWordsC_wTab (Ht : List UInt8 → Digest) (seed : Digest) {c : ℕ}
    (hc : c ≤ w.children.length) :
    (honestWordsC Ht seed s w).wTab[c]? = some (gen ^ hbase s w c) := by
  simp only [honestWordsC, List.getElem?_map, List.getElem?_range (Nat.lt_succ_of_le hc),
    Option.map_some]

end Node

end
end LeanVM.Guest.B1.Main
