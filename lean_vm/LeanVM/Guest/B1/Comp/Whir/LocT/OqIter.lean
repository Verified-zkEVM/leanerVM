/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OqIter

  One query of `opening_queries`' loop decoded at its honest valuation over a completeness model,
  on any reader agreeing with the honest memory on the query's bits.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.QueriesAt
public import LeanVM.Guest.B1.Comp.Whir.LocT.Agree

/-!
# One query, decoded

`oqOpeningOf_iterC`: at `oqIterValC` (the honest valuation of one iteration), the opening the
decoder reads (`oqOpeningOf`) is the query's leaf, its siblings below the cap, then the cap's
siblings from its cap leaf, on any reader agreeing with the honest memory on the query's bits.
`oqLoopPre_bitLoad`: every bit is loaded by the iteration's path.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

theorem bitsVal_congr {f g : ℕ → Bool} : ∀ n, (∀ l < n, f l = g l) → bitsVal f n = bitsVal g n
  | 0, _ => rfl
  | n + 1, h => by simp only [bitsVal, bitsVal_congr n (fun l hl => h l (by omega)), h n (by omega)]

/-- `bitsPos` on readers agreeing on the bits. -/
theorem bitsPos_agree {rd rd' : Reader} {dbp : E} {n : ℕ} (h : ∀ l < n, memAt rd' dbp l = memAt rd dbp l) :
    bitsPos rd' dbp n = bitsPos rd dbp n :=
  bitsVal_congr n fun l hl => by rw [h l hl]

/-- `bitsPos` of a bit run spelling `q`. -/
theorem bitsPos_of_memAt {rd : Reader} {dbp : E} {n q : ℕ} (hq : q < 2 ^ n)
    (h : ∀ l < n, memAt rd dbp l = bitE (q.testBit l)) : bitsPos rd dbp n = q := by
  have e : bitsPos rd dbp n = bitsVal (fun t => q.testBit (0 + t)) n :=
    bitsVal_congr n fun l hl => by rw [h l hl, decide_bitE_eq_one, Nat.zero_add]
  rw [e, bitsVal_shift, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hq]

/-- **The hinted children of a climb spell its siblings.** -/
theorem pathSibs_climbCellsW (Ht : Bytes → Digest) (D : Digest) (q : ℕ) (sibs : List Digest) :
    pathSibs (fun k => (climbCellsW Ht D q sibs).getD k 0) q sibs.length = sibs := by
  apply List.ext_getElem (by simp [pathSibs])
  intro l h1 h2
  simp only [pathSibs, List.getElem_map, List.getElem_range]
  have hc : ∀ i < 4, (climbCellsW Ht D q sibs).getD (4 * l + i) 0 =
      (lvlCells (climbAtW Ht D q sibs l) (sibs.getD l default) (q.testBit l)).getD i 0 := fun i hi => by
    rw [climbCellsW, List.flatMap, oq_getD_flatten_uniform _ 4 (fun _ => length_lvlCells _ _ _) _ l i h2 hi]
  have hs : sibs.getD l default = sibs[l] := by simp [List.getD_eq_getElem?_getD, h2]
  rw [show 4 * l = 4 * l + 0 from rfl, hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega), hs]
  cases q.testBit l <;> simp [lvlCells, pairDigest_digestScalars]

/-- The rows and the hinted children of one iteration's honest valuation. -/
theorem oqIterValC_rowsPath {CM : CompModel} {Ht : Bytes → Digest} {base I blocks pd cd : ℕ}
    (hs : OqShape base I blocks pd cd) {rd : Reader} {x N rew qsc qw qbp flags cap ptr : E} {leaf : List K}
    (hleaf : leaf.length = oqR base I) {q : ℕ} {sibs : List Digest} (hsl : sibs.length = pd) :
    leafWords base I (rowv (oqIterValC CM Ht rd [x, N, rew, qsc, qw, qbp, flags, cap] base I blocks pd cd leaf q sibs ptr)) =
        leaf ∧
      ∀ k < 4 * pd, oqIterValC CM Ht rd [x, N, rew, qsc, qw, qbp, flags, cap] base I blocks pd cd leaf q sibs ptr
        (.n (oqP base I blocks + k)) = (climbCellsW Ht (hashWordsW Ht leaf) q sibs).getD k 0 := by
  obtain ⟨hb, hI, h4, hbl, hfill, hpd1, hpd20, hcd1, hcd8⟩ := hs
  set args := [x, N, rew, qsc, qw, qbp, flags, cap] with hargs
  set R := oqR base I
  set K1 := oqK1 base I
  set K2 := oqK2 base I blocks
  set P := oqP base I blocks
  set r := oqRowR leaf
  set σ1 := oqVal1 rd args base I leaf with hσ1
  obtain ⟨rowsV, hrowsV⟩ : ∃ l, l = oqRowsVals base I (oqRowR leaf) (memAt rd rew) := ⟨_, rfl⟩
  set leafV := oqLeafValsC CM (leaf.flatMap kBytes) (hashWordsW Ht leaf) blocks with hleafV
  set dot := σ1 (.n (K1 - 1))
  set sumV := oqSumVals rd x qsc qw qbp dot
  set D := hashWordsW Ht leaf
  set pathV := oqPathValsW Ht rd ptr D q pd sibs with hpathV
  set dbp := memAt rd (qbp * x) 0
  set capV := oqCapVals rd dbp flags cap x N pd cd with hcapV
  set σ := oqIterValC CM Ht rd args base I blocks pd cd leaf q sibs ptr with hσ
  have hRlen : 8 + R + rowsV.length = K1 := by rw [hrowsV]; exact oq_length_rowsVals hb hI _ _
  have hK2 : K2 = K1 + 2 + 3 * blocks := by simp only [K2, K1, oqK2]; ring
  have hP : P = K2 + 9 := rfl
  have hlv : leafV.length = 2 + 3 * blocks := oq_length_leafValsC _ _ _ _
  have hpv : pathV.length = 79 + 13 * pd := oq_length_pathValsW Ht rd ptr D q pd sibs hsl hpd1 hpd20
  have hσeq : σ = setl (setl (setl (setl σ1 K1 leafV) K2 sumV) P pathV) (P + 79 + 13 * pd) capV := rfl
  have l1 : ∀ i, i < K1 → σ (.n i) = σ1 (.n i) := fun i hi => by
    rw [hσeq]; simp only [setl]
    rw [set_n_lt (by omega), set_n_lt (by omega), set_n_lt (by omega), set_n_lt (by omega)]
  have lrow : ∀ j < R, σ (.n (8 + j)) = r j := fun j hj => by
    rw [l1 _ (by omega), hσ1, oqVal1]; simp only [setl]
    rw [set_n_lt (by omega), set_n_in (by omega) (by simp; omega), Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_range (show j < oqR base I from hj), r]
  have lpath : ∀ k < 79 + 13 * pd, σ (.n (P + k)) = pathV.getD k 0 := fun k hk => by
    rw [hσeq]; simp only [setl]
    rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have hcl : (climbCellsW Ht D q sibs).length = 4 * pd := by
    rw [climbCellsW, List.flatMap, ← hsl]
    exact (oq_length_flatten_uniform _ 4 (fun _ => length_lvlCells _ _ _) _).trans (by ring)
  refine ⟨?_, fun k hk => ?_⟩
  · rw [← oq_leafWords_rowR (base := base) (I := I) hleaf]
    exact List.map_congr_left fun j hj => by rw [rowv, lrow j (List.mem_range.mp hj)]
  · rw [lpath k (by omega), hpathV, oqPathValsW, oq_getD_app_lt (by simp [hcl]; omega),
      oq_getD_app_lt (by simp [hcl]; omega), oq_getD_app_lt (by simp [hcl]; omega),
      oq_getD_app_lt (by simp [hcl]; omega)]

/-- **One query decoded**: at the honest valuation of an iteration, on a reader agreeing with the
honest memory on the query's bits, `oqOpeningOf` is the query's leaf, its siblings below the cap
and the cap's siblings that reader holds from its cap leaf. -/
theorem oqOpeningOf_iterC {CM : CompModel} {Ht : Bytes → Digest} {base I blocks pd cd : ℕ}
    (hs : OqShape base I blocks pd cd) {rd rd' : Reader} {x N rew qsc qw qbp flags cap ptr : E} {leaf : List K}
    (hleaf : leaf.length = oqR base I) {q : ℕ} (hq : q < 2 ^ (pd + cd)) {sibs : List Digest}
    (hsl : sibs.length = pd) (hbits : ∀ l < pd + cd, memAt rd (memAt rd (qbp * x) 0) l = bitE (q.testBit l))
    (hag : ∀ l < pd + cd, memAt rd' (memAt rd (qbp * x) 0) l = memAt rd (memAt rd (qbp * x) 0) l) :
    oqOpeningOf base I blocks pd cd rd'
        (oqIterValC CM Ht rd [x, N, rew, qsc, qw, qbp, flags, cap] base I blocks pd cd leaf q sibs ptr) =
      ⟨leaf, sibs ++ capSibs rd' cap cd (2 ^ cd + q / 2 ^ pd)⟩ := by
  obtain ⟨-, -, -, -, -, pdb, -, -, -, -, -, -, -, -, parg⟩ :=
    oqIterValC_ptrs (CM := CM) (Ht := Ht) (rd := rd) (N := N) (rew := rew) (flags := flags) (cap := cap) (ptr := ptr)
      (leaf := leaf) hs hq hsl hbits
  obtain ⟨hlw, hcells⟩ := oqIterValC_rowsPath (CM := CM) (Ht := Ht) (rd := rd) (x := x) (N := N) (rew := rew)
    (qsc := qsc) (qw := qw) (qbp := qbp) (flags := flags) (cap := cap) (ptr := ptr) hs hleaf (q := q) hsl
  have e8 : oqK2 base I blocks + 8 = oqP base I blocks - 1 := by simp only [oqP]; omega
  have hpos : bitsPos rd' (oqIterValC CM Ht rd [x, N, rew, qsc, qw, qbp, flags, cap] base I blocks pd cd leaf q sibs ptr
      (.n (oqK2 base I blocks + 8))) (pd + cd) = q := by
    rw [e8, pdb, bitsPos_agree hag]
    exact bitsPos_of_memAt hq hbits
  have hps : pathSibs (fun k => oqIterValC CM Ht rd [x, N, rew, qsc, qw, qbp, flags, cap] base I blocks pd cd leaf q
      sibs ptr (.n (oqP base I blocks + k))) q pd = sibs := by
    have e : pathSibs (fun k => oqIterValC CM Ht rd [x, N, rew, qsc, qw, qbp, flags, cap] base I blocks pd cd leaf q
        sibs ptr (.n (oqP base I blocks + k))) q pd =
        pathSibs (fun k => (climbCellsW Ht (hashWordsW Ht leaf) q sibs).getD k 0) q pd := by
      simp only [pathSibs]
      refine List.map_congr_left fun l hl => ?_
      have hl' := List.mem_range.mp hl
      rw [hcells (4 * l) (by omega), hcells (4 * l + 1) (by omega), hcells (4 * l + 2) (by omega),
        hcells (4 * l + 3) (by omega)]
    rw [e, ← hsl, pathSibs_climbCellsW]
  simp only [oqOpeningOf]
  rw [hpos, hps, hlw, parg 7 (by omega)]
  rfl

/-- A statement of the loop body other than its return is in its path's statements. -/
theorem mem_oqLoopPre {base I blocks pd cd : ℕ} {loop : String} {a : Atom}
    (h : Stmt.atom a ∈ oqLoopBody base I blocks pd cd loop) : Stmt.atom a ∈ oqLoopPre base I blocks pd cd loop := by
  rw [oqLoopBody_split] at h
  rcases List.mem_append.mp h with h | h
  · exact h
  · simp at h

/-- **Every bit of the query is loaded** by the iteration's path, from the bit run's pointer. -/
theorem oqLoopPre_bitLoad {base I blocks pd cd : ℕ} (hcd : 1 ≤ cd) (loop : String) :
    ∀ l < pd + cd, ∃ d, Stmt.atom (.load d (.n (oqP base I blocks - 1)) l) ∈ oqLoopPre base I blocks pd cd loop := by
  intro l hl
  refine Exists.imp (fun d hd => mem_oqLoopPre hd) ?_
  simp only [oqLoopBody, List.mem_append]
  rcases Nat.lt_or_ge l pd with h1 | h1
  · rcases Nat.eq_zero_or_pos l with rfl | h0
    · exact ⟨.n (oqP base I blocks + 81), Or.inl (Or.inr (by simp [oqPathT]))⟩
    · refine ⟨.n (oqP base I blocks + 79 + 13 * l), Or.inl (Or.inr ?_)⟩
      simp only [oqPathT, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
      exact Or.inr ⟨_, ⟨l - 1, by omega, rfl⟩, by simp [oqLevel, levelT, show l - 1 + 1 = l by omega]⟩
  · rcases Nat.eq_or_lt_of_le h1 with rfl | h2
    · exact ⟨.n (oqP base I blocks + 79 + 13 * pd + 6 * cd - 5 + 4), Or.inr (by simp [oqCapT])⟩
    · refine ⟨.n (oqP base I blocks + 80 + 13 * pd + 6 * (l - pd - 1) + 1), Or.inr ?_⟩
      unfold oqCapT
      refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr
        ⟨oqCapBit (oqP base I blocks) pd (l - pd - 1), List.mem_map.mpr ⟨l - pd - 1, List.mem_range.mpr (by omega), rfl⟩,
          ?_⟩))
      simp [oqCapBit, capBitT, show pd + 1 + (l - pd - 1) = l by omega]

end
end LeanVM.Guest.B1
