/-
  LeanVM.Guest.B1.Comp.Tables.GkrHoldsC

  `verify_bus_gkr` over a completeness model: its body and its two loops hold under the model's
  semantics on a memory holding an answered run's honest trace and the caller's words.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.GkrBodyC
public import LeanVM.Guest.B1.Tables.GkrHolds

/-!
# `verify_bus_gkr`, honest, over a completeness model

`GkrOwn.lean` and `GkrHolds.lean` under a completeness model: `GkrMemC` (`GkrMem` at the total
hash, `gLay0T`), the facts of an answered trace (`GkrTrace.OkM`), and `gkr_loop10C`,
`gkr_loop11C`, `gkr_holdsC`: the loops and the body at `vbgσT CM.hm` under the model's semantics,
returning the run's state, cursor and values.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete LeanVM.Guest.Memory

@[expose] public section

/-- Layer `0`'s slots at the total hash (`gLay0`). -/
noncomputable def gLay0T (M : HashModel) (T : GkrTrace) (cv : Digest) (cur pts : E) : List E :=
  [(digestScalars (obsCvT M (obsCvT M cv T.x0) T.cnt)).1, (digestScalars (obsCvT M (obsCvT M cv T.x0) T.cnt)).2,
    cur * gen ^ 2, T.x0, T.x0, T.cnt, pts, gen ^ 0]

/-- `layers` at the total hash (`gLayW`). -/
noncomputable def gLayWT (M : HashModel) (T : GkrTrace) (μ : ℕ) (cv : Digest) (cur pts : E) : List E :=
  (if μ % 2 = 1 then gLay0T M T cv cur pts else []) ++
    (List.range (μ / 2 + 1)).flatMap fun i => gLay T (μ % 2) cur pts i ++ List.replicate 8 0

/-- The buffers' words at the total hash (`gkrOwn`). -/
noncomputable def gkrOwnT (M : HashModel) (T : GkrTrace) (μ : ℕ) (cv : Digest) (cur pts : E) : List (List E) :=
  [gLayWT M T μ cv cur pts, gRndW T μ cur, gPtsW T μ, vbgPb, vbgDs]

/-- **What the buffers' memory loads**, at the total hash (`GkrMem`). -/
structure GkrMemC (M : HashModel) (rd : Reader) (T : GkrTrace) (μ : ℕ) (cv : Digest) (cur layers rounds pts pb dsb : E) :
    Prop where
  pb : ∀ k < 33, LoadHolds rd pb k (vbgPb.getD k 0)
  ds : ∀ k < 33, LoadHolds rd dsb k (vbgDs.getD k 0)
  lay0 : μ % 2 = 1 → ∀ k < 8, LoadHolds rd layers k ((gLay0T M T cv cur pts).getD k 0)
  lay : ∀ i ≤ μ / 2, ∀ k < 8, LoadHolds rd layers (8 * gL (μ % 2) i + k) ((gLay T (μ % 2) cur pts i).getD k 0)
  rnd : ∀ i < μ / 2, ∀ r ≤ gL (μ % 2) i, ∀ k < 4,
    LoadHolds rd rounds (4 * (gPos (μ % 2) i + r) + k) ((gRnd T (μ % 2) cur i r).getD k 0)
  row : ∀ i ≤ μ / 2, ∀ j < 40, LoadHolds rd pts (40 * (μ % 2 + i) + j) ((T.P i).point.getD j 0)

theorem gkrMemC_of {M : HashModel} {rd : Reader} {T : GkrTrace} {μ : ℕ} {cv : Digest} {cur layers rounds pts pb dsb : E}
    (hL : ReadsAt rd layers (gLayWT M T μ cv cur pts)) (hR : ReadsAt rd rounds (gRndW T μ cur))
    (hP : ReadsAt rd pts (gPtsW T μ)) (hB : ReadsAt rd pb vbgPb) (hD : ReadsAt rd dsb vbgDs) :
    GkrMemC M rd T μ cv cur layers rounds pts pb dsb := by
  have hl : ∀ i, (gLay T (μ % 2) cur pts i ++ List.replicate 8 0).length = 16 := fun i => rfl
  have hr : ∀ i, (gRow (T.P i)).length = 40 := fun i => by simp [gRow]
  have hsh : μ % 2 = 0 ∨ μ % 2 = 1 := Nat.mod_two_eq_zero_or_one μ
  refine ⟨fun k hk => readsAt_getD hB (by simpa [vbgPb] using hk),
    fun k hk => readsAt_getD hD (by simpa [vbgDs] using hk), fun h k hk => ?_, fun i hi k hk => ?_,
    fun i hi r hr' k hk => ?_, fun i hi j hj => ?_⟩
  · rw [gLayWT, ite_pos' h] at hL
    exact readsAt_getD (readsAt_split hL).1 (by simpa [gLay0T] using hk)
  · rw [gLayWT] at hL
    have hb := readsAt_flatMap_block (readsAt_split hL).2 (Nat.lt_succ_of_le hi)
    have := readsAt_getD (readsAt_split hb).1 (k := k) (by simpa [gLay] using hk)
    rw [length_flatMap_range_const hl, mul_assoc, ← pow_add] at this
    refine loadHolds_shift this ?_
    rcases hsh with h | h <;> simp [h, gL, gLay0T] <;> omega
  · rw [gRndW] at hR
    have hb := readsAt_flatMap_block (readsAt_split hR).2 hi
    have hb2 := readsAt_flatMap_block hb (Nat.lt_succ_of_le hr')
    have := readsAt_getD hb2 (k := k) (by rw [gRnd_length]; exact hk)
    rw [length_flatMap_range_const (gRnd_length T _ cur i), gRnds_length, mul_assoc, ← pow_add,
      mul_assoc, ← pow_add] at this
    refine loadHolds_shift this ?_
    have := gPos_eq (μ % 2) i
    simp only [List.length_replicate]
    rcases hsh with h | h <;> rw [h] at this ⊢ <;> omega
  · rw [gPtsW] at hP
    have hb := readsAt_flatMap_block (readsAt_split hP).2 (Nat.lt_succ_of_le hi)
    have := readsAt_getD hb (k := j) (by rw [hr]; exact hj)
    rw [length_flatMap_range_const hr, mul_assoc, ← pow_add, gRow, gk_getD_map_range _ hj] at this
    refine loadHolds_shift this ?_
    simp only [List.length_replicate]; ring

section
variable {CM : CompModel} {T : GkrTrace} {μ : ℕ} {cv cv' : Digest} {xs : List E}
  {r : E × List E × List E}

theorem GkrTrace.OkM.vals (hT : T.OkM CM.hm μ cv xs r cv') {i : ℕ} (hi : i ≤ μ / 2) :
    (T.P i).values = [(T.P i).values.getD 0 0, (T.P i).values.getD 1 0, (T.P i).values.getD 2 0] := by
  refine gk_getD_three _ ?_
  match i with
  | 0 =>
    rcases Nat.mod_two_eq_zero_or_one μ with h | h
    · rw [(hT.even h).1]; rfl
    · rw [(hT.odd h).2.2.2.2.2.1]; rfl
  | i + 1 => rw [(hT.pair i (by omega)).2.2.2.2.2.2.2.2.2.2.1]; rfl

theorem GkrTrace.OkM.ylen (hT : T.OkM CM.hm μ cv xs r cv') {i : ℕ} (hi : i < μ / 2) :
    (T.Y i).length = 4 * gL (μ % 2) i + 12 := by
  obtain ⟨-, -, -, hr, hys, -⟩ := hT.pair i hi
  rw [hys, List.length_append, length_flatMap_range_lt (w := 4) _ (fun r hr' => (hr r hr').1)]
  simp

theorem GkrTrace.OkM.ys_len (hT : T.OkM CM.hm μ cv xs r cv') :
    ∀ j ≤ μ / 2, ((List.range j).flatMap T.Y).length + gCur (μ % 2) 0 = gCur (μ % 2) j
  | 0, _ => by simp
  | j + 1, hj => by
    rw [length_flatMap_range_succ, hT.ylen (by omega),
      show gCur (μ % 2) (j + 1) = gCur (μ % 2) j + 4 * gL (μ % 2) j + 12 from rfl, ← hT.ys_len j (by omega)]
    omega

theorem GkrTrace.OkM.xs_len (hT : T.OkM CM.hm μ cv xs r cv') : xs.length = gCur (μ % 2) (μ / 2) := by
  rw [← hT.ys_len _ le_rfl, hT.hxs]
  rcases Nat.mod_two_eq_zero_or_one μ with h | h
  · simp [h, gCur]
  · simp [h, gCur]; omega

/-- The odd step's words and each pair's, read at the cursor. -/
theorem GkrTrace.OkM.reads (hT : T.OkM CM.hm μ cv xs r cv') {rd : Reader} {cur : E} (h : ReadsAt rd cur xs) :
    LoadHolds rd cur 0 T.x0 ∧ LoadHolds rd cur 1 T.cnt ∧
      (μ % 2 = 1 → ∀ i < 6, LoadHolds rd (cur * gen ^ 2) i (T.oes i)) ∧
      ∀ i < μ / 2, ReadsAt rd (cur * gen ^ gCur (μ % 2) i) (T.Y i) := by
  rw [hT.hxs] at h
  have h' : ReadsAt rd cur ([T.x0, T.cnt] ++ ((if μ % 2 = 1 then (List.range 6).map T.oes else []) ++
      (List.range (μ / 2)).flatMap T.Y)) := h
  have h2 := (readsAt_split h').2
  refine ⟨h' 0 (by simp), h' 1 (by simp), fun hs i hi => ?_, fun i hi => ?_⟩
  · have := (readsAt_split h2).1
    rw [ite_pos' hs] at this
    have := readsAt_getD this (k := i) (by simpa using hi)
    rwa [gk_getD_map_range _ hi] at this
  · have := readsAt_flatMap_block (readsAt_split h2).2 hi
    rw [gen_pow_mul_mul, gen_pow_mul_mul] at this
    convert this using 3
    rw [← hT.ys_len i (by omega)]
    rcases Nat.mod_two_eq_zero_or_one μ with h | h
    · simp [h, gCur]; omega
    · simp [h, gCur]; omega

theorem GkrTrace.OkM.next_lay (hT : T.OkM CM.hm μ cv xs r cv') {j : ℕ} (hj : j < μ / 2) (cur pts : E) :
    gLay T (μ % 2) cur pts (j + 1) =
      [(digestScalars (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))).1,
        (digestScalars (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))).2,
        cur * gen ^ gCur (μ % 2) j * gen ^ (4 * gL (μ % 2) j) * gen ^ 12,
        l10Next (T.ES j) 0 (challengeOf (sqCvT CM.hm (l10cvT CM.hm (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))
          (challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))),
        l10Next (T.ES j) 4 (challengeOf (sqCvT CM.hm (l10cvT CM.hm (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))
          (challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))),
        l10Next (T.ES j) 8 (challengeOf (sqCvT CM.hm (l10cvT CM.hm (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))
          (challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))),
        pts * gen ^ (40 * (μ % 2 + j)) * gen ^ 40, gen ^ (gPos (μ % 2) j + gL (μ % 2) j + 1)] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hvl, hcvn⟩ := hT.pair j hj
  simp only [gLay, hcvn, hvl, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq, and_true]
  refine ⟨trivial, trivial, ?_, trivial, trivial, trivial, ?_, rfl⟩
  · show cur * gen ^ (gCur (μ % 2) j + 4 * gL (μ % 2) j + 12) = _
    rw [pow_add, pow_add]; ring
  · rw [mul_assoc, ← pow_add, show 40 * (μ % 2 + j) + 40 = 40 * (μ % 2 + (j + 1)) by ring]

/-- **`__loop10` over a completeness model** on an honest memory (`gkr_loop10`). -/
theorem gkr_loop10C (hT : T.OkM CM.hm μ cv xs r cv') (hμ : μ < 33) {rd : Reader}
    {cur layers rounds pts pb dsb : E} (hM : GkrMemC CM.hm rd T μ cv cur layers rounds pts pb dsb)
    (hx : ReadsAt rd cur xs) (hm : 0 < μ / 2) :
    coreProgram.RelB CM.sem rd "__loop10" [1, gen ^ (μ / 2), dsb, gen ^ μ, layers, rounds] [] := by
  obtain ⟨-, -, -, hY⟩ := hT.reads hx
  refine loop10_completeC hm fun j hj => ?_
  obtain ⟨hq0, hc0, hcv0, hr, hys, hA, hq1, hq2, hfin, hpt, -, -⟩ := hT.pair j hj
  have hv := hT.vals (i := j) (by omega)
  have hL : gL (μ % 2) j + 2 ≤ μ := by unfold gL; omega
  have hpt' : ∀ t < gL (μ % 2) j + 2, (T.P (j + 1)).point.getD t 0 =
      ([challengeOf (sqCvT CM.hm (l10cvT CM.hm (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)),
        challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))] ++
        (List.range (gL (μ % 2) j)).map (T.CH j)).getD t 0 := fun t _ => by rw [hpt]
  have hds : LoadHolds rd (dsb * gen ^ μ) 0 (gen ^ (μ % 2)) :=
    loadHolds_unshift (by rw [← vbgDs_get hμ]; exact hM.ds μ (by omega)) rfl
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, pair_iterC (T.CL j) (T.CVR j) (T.WSR j) (T.CH j) (T.ES j)
    hv hc0 hcv0 hr hfin (N := gen ^ (μ / 2)) (j := j) (sh := μ % 2) (posE := gPos (μ % 2) j)
    (row := pts * gen ^ (40 * (μ % 2 + j))) (cur := cur * gen ^ gCur (μ % 2) j) rfl hds
    (fun k hk => hM.lay j (by omega) k hk) (fun t ht => loadHolds_unshift (hM.row j (by omega) t (by omega)) rfl)
    (fun t ht k hk => hM.rnd j hj t ht k hk) (fun t ht => ?_) ?_ ?_ (fun k hk => ?_) (by rw [← hys]; exact hY j hj) hq0 hA hq1 hq2⟩
  · have := hM.row (j + 1) (by omega) (2 + t) (by omega)
    rw [hpt' _ (by omega)] at this
    simp only [List.cons_append, List.nil_append] at this
    rw [show 2 + t = t + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
      gk_getD_map_range _ ht] at this
    exact loadHolds_unshift this (by ring)
  · have := hM.row (j + 1) (by omega) 0 (by omega)
    rw [hpt' _ (by omega)] at this
    exact loadHolds_unshift this (by ring)
  · have := hM.row (j + 1) (by omega) 1 (by omega)
    rw [hpt' _ (by omega)] at this
    exact loadHolds_unshift this (by ring)
  · have := hM.lay (j + 1) (by omega) k hk
    rw [hT.next_lay hj] at this
    rwa [show 8 * gL (μ % 2) (j + 1) + k = 8 * gL (μ % 2) j + 16 + k by unfold gL; ring] at this

/-- **`__loop11` under a completeness model's semantics** on an honest memory (`gkr_loop11`). -/
theorem gkr_loop11C (hT : T.OkM CM.hm μ cv xs r cv') {rd : Reader} {cur layers rounds pts pb dsb zeta : E}
    (hM : GkrMemC CM.hm rd T μ cv cur layers rounds pts pb dsb) (hz : ReadsAt rd zeta r.2.1) (hμ : μ < 33)
    (hm : 0 < μ) :
    coreProgram.RelB CM.sem rd "__loop11" [1, gen ^ μ, zeta, pts * gen ^ (40 * (μ % 2 + μ / 2))] [] := by
  rw [relB_loop11]
  have hl := hT.hlen _ le_rfl
  have hμL : gL (μ % 2) (μ / 2) = μ := by unfold gL; omega
  refine loop11_complete hm fun j hj => ⟨(T.P (μ / 2)).point.getD j 0,
    loadHolds_unshift (loadHolds_unshift (hM.row _ le_rfl j (by omega)) rfl) (by ring),
    loadHolds_unshift ?_ (by ring)⟩
  rw [hT.hr] at hz
  have := readsAt_getD hz (k := j) (by simp only; rw [hl, hμL]; exact hj)
  exact this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`verify_bus_gkr`'s body holds over a completeness model** (`gkr_holds`) on an honest memory
at the total hash, the walk's hashes answered, returning the run's state, cursor and
values. -/
theorem gkr_holdsC (hT : T.OkM CM.hm μ cv xs r cv') (hμ : μ < 33) {rd : Reader}
    {cur zeta layers rounds pts pb dsb rcy rct1 rct2 : E}
    (hM : GkrMemC CM.hm rd T μ cv cur layers rounds pts pb dsb) (hx : ReadsAt rd cur xs)
    (hz : ReadsAt rd zeta r.2.1) (hrc1 : LoadHolds rd (gen ^ μ) 0 rct1) (hrc2 : LoadHolds rd rcy 0 rct2)
    (hrck : word 4294967296 0 0 = gen ^ μ * rcy) :
    Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd (vbgσT CM.hm zeta (digestScalars cv).1 (digestScalars cv).2 cur
      (gen ^ μ) layers rounds pts pb dsb rcy rct1 rct2 T.cnt⁻¹ T.x0 T.cnt (gen ^ (μ % 2))
      (gen ^ (μ / 2)) (cur * gen ^ gCur (μ % 2) (μ / 2)) (pts * gen ^ (40 * (μ % 2 + μ / 2)))
      ((T.P (μ / 2)).values.getD 0 0) ((T.P (μ / 2)).values.getD 1 0) ((T.P (μ / 2)).values.getD 2 0)
      cv (T.C (μ / 2)) T.oes) (Fn.body Data.core10) False
      (fun rs => rs = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ xs.length] ++ r.2.2) := by
  obtain ⟨hx0, hcnt, hodd, -⟩ := hT.reads hx
  have hμL : gL (μ % 2) (μ / 2) = μ := by unfold gL; omega
  have hret : [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ xs.length] ++ r.2.2 =
      [(digestScalars (T.C (μ / 2))).1, (digestScalars (T.C (μ / 2))).2, cur * gen ^ gCur (μ % 2) (μ / 2),
        (T.P (μ / 2)).values.getD 0 0, (T.P (μ / 2)).values.getD 1 0, (T.P (μ / 2)).values.getD 2 0] := by
    rw [hT.hcv, hT.xs_len, hT.hr]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and]
    exact hT.vals le_rfl
  rw [hret]
  have e0 : [(digestScalars (vbgCv0T CM.hm cv T.x0 T.cnt)).1, (digestScalars (vbgCv0T CM.hm cv T.x0 T.cnt)).2,
      cur * word 4 0 0, T.x0, T.x0, T.cnt, pts, word 1 0 0] = gLay0T CM.hm T cv cur pts := by
    rw [gk_word4, word_one, gLay0T, pow_zero]
  have hl0 : ∀ k < 8, LoadHolds rd layers k ([(digestScalars (vbgCv0T CM.hm cv T.x0 T.cnt)).1,
      (digestScalars (vbgCv0T CM.hm cv T.x0 T.cnt)).2, cur * word 4 0 0, T.x0, T.x0, T.cnt, pts,
      word 1 0 0].getD k 0) := by
    rw [e0]
    rcases Nat.mod_two_eq_zero_or_one μ with h | h
    · intro k hk
      have := hM.lay 0 (Nat.zero_le _) k hk
      obtain ⟨hp, hc⟩ := hT.even h
      have e : gLay T (μ % 2) cur pts 0 = gLay0T CM.hm T cv cur pts := by
        rw [gLay, gLay0T, hp, hc, h]; simp [gCur, gPos]
      rwa [e, show 8 * gL (μ % 2) 0 + k = k by unfold gL; omega] at this
    · exact hM.lay0 h
  have hds : LoadHolds rd (dsb * gen ^ μ) 0 (gen ^ (μ % 2)) :=
    loadHolds_unshift (by rw [← vbgDs_get hμ]; exact hM.ds μ (by omega)) rfl
  have hnp : LoadHolds rd (pb * gen ^ μ) 0 (gen ^ (μ / 2)) :=
    loadHolds_unshift (by rw [← vbgPb_get hμ]; exact hM.pb μ (by omega)) rfl
  refine vbg_holdsC (oes := T.oes) rfl (by simpa using hrc1) hrc2 hrck hx0 hcnt
    (by rw [word_zero, add_zero]; exact mul_inv_cancel₀ hT.hcnt) hT.ax0 hT.acnt hl0 hM.pb hM.ds hds
    (by rw [add_comm]; exact gk_isInK_one_add _) (fun hne => ?_) hnp (gk_isInK_one_add _)
    (fun hne => ?_) (fun k hk => ?_) (gk_isInK_one_add _) (fun hne => ?_)
  · have hs : μ % 2 = 1 := by
      have := gk_one_add_ne (a := μ % 2) (by omega) (by rwa [add_comm] at hne)
      omega
    obtain ⟨oq0, oA, oq1, hchk, hpt, hvl, hcv0⟩ := hT.odd hs
    refine ⟨fun i hi => by rw [gk_word4]; exact hodd hs i hi, ?_, ?_, oq0, oA, oq1, fun k hk => ?_⟩
    · rw [← hchk, polyEval_three]
    · have := hM.row 0 (Nat.zero_le _) 0 (by omega)
      rw [hpt, hs] at this
      rw [word_g40]; exact loadHolds_unshift this rfl
    · have := hM.lay 0 (Nat.zero_le _) k hk
      have e : gLay T (μ % 2) cur pts 0 = [(digestScalars (sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv T.x0 T.cnt)) T.oes 6))).1,
          (digestScalars (sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv T.x0 T.cnt)) T.oes 6))).2,
          cur * word 4 0 0 * word 64 0 0,
          T.oes 0 + (challengeOf (sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv T.x0 T.cnt)) T.oes 6))) * (T.oes 0 + T.oes 1),
          T.oes 2 + (challengeOf (sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv T.x0 T.cnt)) T.oes 6))) * (T.oes 2 + T.oes 3),
          T.oes 4 + (challengeOf (sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv T.x0 T.cnt)) T.oes 6))) * (T.oes 4 + T.oes 5),
          pts * word 1099511627776 0 0, word 2 0 0] := by
        rw [gLay, hcv0, hvl, hs, gk_word4, word_g6, word_g40, word_gen]
        simp only [List.getD_cons_zero, List.getD_cons_succ, gCur, gPos, List.cons.injEq, and_true]
        refine ⟨trivial, trivial, by rw [mul_assoc, ← pow_add], trivial, trivial, trivial, trivial, pow_one gen⟩
      rwa [e, show 8 * gL (μ % 2) 0 + k = 8 + k by unfold gL; omega] at this
  · have := gk_one_add_ne (by omega) hne
    rw [word_one]; exact gkr_loop10C hT hμ hM hx this
  · have := hM.lay (μ / 2) le_rfl k (by omega)
    rw [hμL] at this
    have e : (gLay T (μ % 2) cur pts (μ / 2)).getD k 0 = [(digestScalars (T.C (μ / 2))).1,
        (digestScalars (T.C (μ / 2))).2, cur * gen ^ gCur (μ % 2) (μ / 2), (T.P (μ / 2)).values.getD 0 0,
        (T.P (μ / 2)).values.getD 1 0, (T.P (μ / 2)).values.getD 2 0,
        pts * gen ^ (40 * (μ % 2 + μ / 2))].getD k 0 := by
      interval_cases k <;> rfl
    rw [e] at this
    rw [← pow_mul, mul_comm μ 8]; exact loadHolds_unshift this rfl
  · have := gk_one_add_ne hμ hne
    rw [word_one]; exact gkr_loop11C hT hM hz hμ this

end

end
end LeanVM.Guest.B1.VerifySub
