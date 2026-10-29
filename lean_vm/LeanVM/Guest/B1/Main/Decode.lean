/-
  LeanVM.Guest.B1.Main.Decode

  The decoders of `main`'s witness against the filled coverage table: the marks, the running
  counts, the child of a mark, the slot of a mark, a segment's count in a region.
-/

module

public import LeanVM.Guest.B1.Main.World

/-!
# The decoders, read off the coverage table

With the coverage table filled (`Cover`, `cover_bij` of `writers`): `markOf` is the mark of the
slot's writer (`markOf_sl`), `countOf` the base `a c` (`countOf_eq`), `kidOf` the child whose
segment holds a mark (`kidOf_eq`), `slotOf` the writer's slot (`slotOf_eq`), and `segCount` a
child's count in each region (`segCount_x`, `segCount_s`, `segCount_d`); a child's records are
the writers of its marks (`ox_eq`, `os_eq`, `di_eq`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

variable {rd : Reader} {σ : Val} {K : ℕ → KidRec} {sl : ℕ → ℕ}

/-! ## Counts -/

theorem lg_eq_gLog (σ : Val) (v : ℕ) : lg σ v = gLog (σ (.n v)) := by unfold lg; rfl

theorem lxSlots_eq (MF : MainFacts C rd σ) : lxSlots σ = LXS σ := by
  have hT := MF.total.2
  unfold lxSlots; rw [MF.lxs, gLog_gen_pow (by omega)]

theorem lsSlots_eq (MF : MainFacts C rd σ) : lsSlots σ = LSS σ := by
  have hT := MF.total.2
  unfold lsSlots; rw [MF.lss, gLog_gen_pow (by omega)]

theorem daSlots_eq (MF : MainFacts C rd σ) : daSlots σ = DAS σ := by
  have hT := MF.total.2
  unfold daSlots; rw [MF.daslots.1, gLog_gen_pow (by omega)]

theorem nKids_eq (σ : Val) : nKids σ = lg σ 6 := by unfold nKids; rw [lg_eq_gLog]

theorem nRawX_eq (σ : Val) : nRawX σ = lg σ 2 := by unfold nRawX; rw [lg_eq_gLog]
theorem nRawS_eq (σ : Val) : nRawS σ = lg σ 5 := by unfold nRawS; rw [lg_eq_gLog]
theorem nDirect_eq (σ : Val) : nDirect σ = lg σ 7 := by unfold nDirect; rw [lg_eq_gLog]

theorem countOf_eq (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) {c : ℕ}
    (hc : c ≤ lg σ 6) : countOf rd σ c = (segsOf σ K).a c := by
  have hb := a_le MF hK c hc
  have hk6 := MF.kids.2
  unfold countOf
  rw [cellAt_eq_memAt, memAt_of_load (written_eq MF hK c hc), gLog_gen_pow (by omega)]

/-! ## The marks -/

theorem markOf_eq (s : ℕ) : markOf rd σ s = markAt rd (σ (.n 97)) s := by
  unfold markOf markAt; rw [cellAt_eq_memAt]

theorem markAt_sl {cover : E} {S : Segs} {X Y Z : ℕ} (hC : Cover rd cover S X Y Z sl) {m : ℕ}
    (hm : m < X + Y + Z) (hs : X + Y + Z < 2 ^ 34) : markAt rd cover (sl m) = m := by
  unfold markAt; rw [memAt_of_load (hC.wr m hm), gLog_gen_pow (by omega)]

/-! ## The child of a mark -/

theorem find_first' {A : ℕ → ℕ} {n c e : ℕ} (hc : c < n) (hlow : ∀ j < c, A (j + 1) ≤ e)
    (h2 : e < A (c + 1)) :
    ((List.range n).find? fun c' => decide (e < A (c' + 1))).getD 0 = c := by
  have key : (List.range n).find? (fun c' => decide (e < A (c' + 1))) = some c := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using h2, c, by simpa using hc, by simp, fun j hj => ?_⟩
    simp only [List.getElem_range, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      not_lt]
    exact hlow j hj
  rw [key]; rfl

theorem kidOf_eq (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) {c e : ℕ}
    (hc : c < lg σ 6) (h1 : (segsOf σ K).a c ≤ e) (h2 : e < (segsOf σ K).a (c + 1)) :
    kidOf rd σ e = c := by
  unfold kidOf
  rw [nKids_eq]
  have hA : ∀ j ≤ lg σ 6, countOf rd σ j = (segsOf σ K).a j := fun j hj => countOf_eq MF hK hj
  refine find_first' (A := countOf rd σ) hc (fun j hj => ?_) (by rw [hA _ (by omega)]; exact h2)
  rw [hA _ (by omega)]
  exact le_trans ((segsOf σ K).a_mono (show j + 1 ≤ c by omega)) h1

theorem kid_eq {S : Segs} {c m : ℕ} (hc : c < S.NC) (h1 : S.a c ≤ m) (h2 : m < S.a (c + 1)) :
    S.kid m = c := find_first S.a_mono hc h1 h2

/-! ## Regions of a child's marks -/

theorem region_x {S : Segs} {c j : ℕ} (hc : c < S.NC) (hj : j < S.ex c) :
    S.region (S.a c + j) = 0 := by
  have ha0 : S.a 0 ≤ S.a c := S.a_mono (Nat.zero_le c)
  have hk : S.kid (S.a c + j) = c := kid_eq hc (by omega) (by simp only [Segs.a]; omega)
  have h0 : S.a 0 = S.RX + S.RS + S.ND := rfl
  unfold Segs.region
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), hk, ite_pos' (by omega)]

end
end LeanVM.Guest.B1.Main

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

variable {rd : Reader} {σ : Val} {K : ℕ → KidRec} {sl : ℕ → ℕ}

/-! ## Regions of the marks -/

/-- The region of a mark in child `c`'s segment. -/
theorem region_kid {S : Segs} {c m : ℕ} (hc : c < S.NC) (h1 : S.a c ≤ m) (h2 : m < S.a (c + 1)) :
    S.region m = if m - S.a c < S.ex c then 0 else if m - S.a c < S.ex c + S.es c then 1 else 2 := by
  have ha0 : S.a 0 ≤ S.a c := S.a_mono (Nat.zero_le c)
  have h0 : S.a 0 = S.RX + S.RS + S.ND := rfl
  have hk : S.kid m = c := kid_eq hc h1 h2
  unfold Segs.region
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), hk]

/-- The slot of a mark lies in its region's range, and conversely. -/
theorem inRegion_iff {X Y r s : ℕ} (h : InRegion X Y r s) (hr : r ≤ 2) :
    (s < X ↔ r = 0) ∧ (X ≤ s ∧ s < X + Y ↔ r = 1) := by
  obtain ⟨h0, h1, h2⟩ := h
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
  · have := h0 rfl; omega
  · have := h1 rfl; omega
  · have := h2 rfl; omega

theorem region_kid' {S : Segs} {c m : ℕ} (hc : c < S.NC) (h1 : S.a c ≤ m) (h2 : m < S.a (c + 1)) :
    (S.region m = 0 ↔ m < S.a c + S.ex c) ∧
      (S.region m = 1 ↔ S.a c + S.ex c ≤ m ∧ m < S.a c + S.ex c + S.es c) := by
  rw [region_kid hc h1 h2]
  have hm := Nat.sub_add_cancel h1
  by_cases ha : m - S.a c < S.ex c
  · rw [ite_pos' ha]
    exact ⟨⟨fun _ => by omega, fun _ => rfl⟩, ⟨fun h => absurd h (by decide), fun h => by omega⟩⟩
  · rw [ite_neg' ha]
    by_cases hb : m - S.a c < S.ex c + S.es c
    · rw [ite_pos' hb]
      exact ⟨⟨fun h => absurd h (by decide), fun h => by omega⟩, ⟨fun _ => ⟨by omega, by omega⟩,
        fun _ => rfl⟩⟩
    · rw [ite_neg' hb]
      exact ⟨⟨fun h => absurd h (by decide), fun h => by omega⟩, ⟨fun h => absurd h (by decide),
        fun h => by omega⟩⟩

theorem region_le (S : Segs) (m : ℕ) : S.region m ≤ 2 := by
  unfold Segs.region; split_ifs <;> omega

/-! ## The slot of a mark, a segment's count -/

section Cov

variable {cover : E} {S : Segs} {X Y Z : ℕ}

/-- **The slot holding the mark `e`**, in a range `[lo, lo + len)` of the table. -/
theorem slot_search (hC : Cover rd cover S X Y Z sl) (hs : X + Y + Z < 2 ^ 34) {lo len e : ℕ}
    (he : e < X + Y + Z) (hlo : lo ≤ sl e) (hhi : sl e < lo + len) (hlen : lo + len ≤ X + Y + Z) :
    ((List.range len).find? fun s => decide (markAt rd cover (lo + s) = e)).getD 0 = sl e - lo := by
  refine find_unique (by omega) ?_ (fun t ht hp => ?_)
  · simp only [decide_eq_true_eq, Nat.add_sub_cancel' hlo]
    exact markAt_sl hC he hs
  · simp only [decide_eq_true_eq] at hp
    have := (hC.mark (lo + t) (by omega)).2
    rw [hp] at this
    omega

/-- **A segment's count in a range**: the marks of `[a, b)` whose slots lie in `[lo, lo + len)`
are exactly `[m0, m0 + k)`. -/
theorem seg_count (hC : Cover rd cover S X Y Z sl) (hs : X + Y + Z < 2 ^ 34) {lo len a b m0 k : ℕ}
    (hlen : lo + len ≤ X + Y + Z) (hb : b ≤ X + Y + Z) (hm : a ≤ m0 ∧ m0 + k ≤ b)
    (hreg : ∀ m, a ≤ m → m < b → (lo ≤ sl m ∧ sl m < lo + len ↔ m0 ≤ m ∧ m < m0 + k)) :
    ((List.range len).filter fun s => decide (a ≤ markAt rd cover (lo + s) ∧
      markAt rd cover (lo + s) < b)).length = k := by
  refine filter_card (fun j => sl (m0 + j) - lo) (fun j hj => ?_) (fun i hi j hj h => ?_)
    (fun s hs' hP => ?_)
  · have hr := (hreg (m0 + j) (by omega) (by omega)).mpr ⟨by omega, by omega⟩
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel' hr.1, markAt_sl hC (by omega) hs]
    simp only [decide_eq_true_eq]; omega
  · have hri := (hreg (m0 + i) (by omega) (by omega)).mpr ⟨by omega, by omega⟩
    have hrj := (hreg (m0 + j) (by omega) (by omega)).mpr ⟨by omega, by omega⟩
    have : sl (m0 + i) = sl (m0 + j) := by omega
    have := congrArg (markAt rd cover) this
    rw [markAt_sl hC (by omega) hs, markAt_sl hC (by omega) hs] at this
    omega
  · simp only [decide_eq_true_eq] at hP
    obtain ⟨hlt, hsl⟩ := hC.mark (lo + s) (by omega)
    set m := markAt rd cover (lo + s)
    have hr := (hreg m hP.1 hP.2).mp ⟨by omega, by omega⟩
    exact ⟨m - m0, by omega, by rw [Nat.add_sub_cancel' hr.1, hsl]; omega⟩

end Cov

end
end LeanVM.Guest.B1.Main

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

variable {rd : Reader} {σ : Val} {K : ℕ → KidRec} {sl : ℕ → ℕ}

/-! ## A child's writes -/

theorem kid_base (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) {c : ℕ}
    (hc : c < lg σ 6) : (K c).base = gen ^ (segsOf σ K).a c :=
  loadHolds_unique (hK c hc).base (written_eq MF hK c (by omega))

theorem kid_wx (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) {c j : ℕ}
    (hc : c < lg σ 6) (hj : j < (K c).ex) :
    (K c).ox j < LXS σ ∧ LoadHolds rd (σ (.n 97)) ((K c).ox j) (gen ^ ((segsOf σ K).a c + j)) := by
  have hT := MF.total.2
  obtain ⟨hbl, hl, -⟩ := (hK c hc).xrec j hj
  refine ⟨belowLog_lt (by unfold LXS; omega) MF.lxs hbl, ?_⟩
  rw [one_mul, loadHolds_gen_pow_iff, kid_base MF hK hc, ← pow_add, Nat.add_zero] at hl
  exact hl

theorem kid_ws (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) {c j : ℕ}
    (hc : c < lg σ 6) (hj : j < (K c).es) :
    (K c).os j < LSS σ ∧ LoadHolds rd (σ (.n 97)) (LXS σ + (K c).os j)
      (gen ^ ((segsOf σ K).a c + (K c).ex + j)) := by
  have hT := MF.total.2
  obtain ⟨hbl, hl, -⟩ := (hK c hc).srec j hj
  refine ⟨belowLog_lt (by unfold LSS; omega) MF.lss hbl, ?_⟩
  rw [MF.lxs, ← pow_add, loadHolds_gen_pow_iff, kid_base MF hK hc, ← pow_add, ← pow_add,
    Nat.add_zero] at hl
  exact hl

theorem kid_wd (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) {c d : ℕ}
    (hc : c < lg σ 6) (hd : d < (K c).ed) :
    (K c).di d < DAS σ ∧ LoadHolds rd (σ (.n 97)) (LXS σ + LSS σ + (K c).di d)
      (gen ^ ((segsOf σ K).a c + (K c).ex + (K c).es + d)) := by
  have hT := MF.total.2
  obtain ⟨-, hbl, hl, -, -⟩ := (hK c hc).drec d hd
  refine ⟨belowLog_lt (by unfold DAS; omega) MF.daslots.1 hbl, ?_⟩
  rw [MF.dacover, loadHolds_gen_pow_iff, kid_base MF hK hc, ← pow_add, ← pow_add, ← pow_add,
    show (segsOf σ K).a c + ((K c).ex + (K c).es) + d =
      (segsOf σ K).a c + (K c).ex + (K c).es + d by ring] at hl
  exact hl

/-! ## A child's statement -/

/-- **Child `c`'s statement, read off the coverage table**, is its records'. -/
theorem kidStmt_eq (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c))
    (hW : Writers rd (σ (.n 97)) (segsOf σ K) (LXS σ) (LSS σ) (DAS σ))
    (hC : Cover rd (σ (.n 97)) (segsOf σ K) (LXS σ) (LSS σ) (DAS σ) sl) {c : ℕ}
    (hc : c < lg σ 6) :
    kidStmt rd σ c =
      ⟨⟨(List.range (K c).ex).map fun j => xmssAt rd (σ (.n 77)) ((K c).ox j),
        (List.range (K c).es).map fun j => sphincsAt rd (σ (.n 80)) ((K c).os j),
        (List.range (K c).ed).map fun d => daAt rd (σ (.n 69)) ((K c).di d)⟩,
       deferOfCells (readCells rd (σ (.n 386) * gen ^ (24 * c)) 24)⟩ := by
  have hT := MF.total.2
  have hs : LXS σ + LSS σ + DAS σ < 2 ^ 34 := by unfold LXS LSS DAS; omega
  have hcN : c < (segsOf σ K).NC := by rw [segsOf_NC]; exact hc
  have htot := hW.total
  have hab : (segsOf σ K).a (c + 1) ≤ LXS σ + LSS σ + DAS σ := by
    rw [← htot]; exact (segsOf σ K).a_mono (by omega)
  have hsucc : (segsOf σ K).a (c + 1) = (segsOf σ K).a c + ((K c).ex + (K c).es + (K c).ed) := by
    rw [Segs.a.eq_2, segsOf_ex, segsOf_es, segsOf_ed]
  -- the regions of the child's marks
  have hregm : ∀ m, (segsOf σ K).a c ≤ m → m < (segsOf σ K).a (c + 1) →
      (sl m < LXS σ ↔ m < (segsOf σ K).a c + (K c).ex) ∧
      (LXS σ ≤ sl m ∧ sl m < LXS σ + LSS σ ↔
        (segsOf σ K).a c + (K c).ex ≤ m ∧ m < (segsOf σ K).a c + (K c).ex + (K c).es) := by
    intro m h1 h2
    have hm : m < LXS σ + LSS σ + DAS σ := by omega
    obtain ⟨hx, hy⟩ := inRegion_iff (hC.reg m hm) (region_le _ _)
    obtain ⟨r0, r1⟩ := region_kid' hcN h1 h2
    rw [hx, hy, r0, r1, segsOf_ex, segsOf_es]
    exact ⟨Iff.rfl, Iff.rfl⟩
  have hlt : ∀ m < LXS σ + LSS σ + DAS σ, sl m < LXS σ + LSS σ + DAS σ := hC.lt
  have hmk : ∀ s, markOf rd σ s = markAt rd (σ (.n 97)) s := fun s => markOf_eq s
  -- the counts
  have hnx : segCount rd σ 0 (LXS σ) ((segsOf σ K).a c) ((segsOf σ K).a (c + 1)) = (K c).ex := by
    unfold segCount; simp only [hmk]
    refine seg_count hC hs (by omega) hab ⟨le_rfl, by omega⟩ (fun m h1 h2 => ?_)
    have := (hregm m h1 h2).1
    omega
  have hns : segCount rd σ (LXS σ) (LSS σ) ((segsOf σ K).a c) ((segsOf σ K).a (c + 1)) =
      (K c).es := by
    unfold segCount; simp only [hmk]
    refine seg_count hC hs (m0 := (segsOf σ K).a c + (K c).ex) (by omega) hab ⟨by omega, by omega⟩
      (fun m h1 h2 => ?_)
    have := (hregm m h1 h2).2
    omega
  have hnd : segCount rd σ (LXS σ + LSS σ) (DAS σ) ((segsOf σ K).a c) ((segsOf σ K).a (c + 1)) =
      (K c).ed := by
    unfold segCount; simp only [hmk]
    refine seg_count hC hs (m0 := (segsOf σ K).a c + (K c).ex + (K c).es) (by omega) hab
      ⟨by omega, by omega⟩ (fun m h1 h2 => ?_)
    have h1' := (hregm m h1 h2).1
    have h2' := (hregm m h1 h2).2
    have := hlt m (by omega)
    omega
  -- the slots
  have hox : ∀ j < (K c).ex, slotOf rd σ 0 (LXS σ) ((segsOf σ K).a c + j) = (K c).ox j := by
    intro j hj
    obtain ⟨hlt', hl⟩ := kid_wx MF hK hc hj
    have hsl := hC.uniq _ (by omega) _ (by omega) hl
    unfold slotOf; simp only [hmk]
    rw [slot_search hC hs (by omega) (by omega) (by omega) (by omega), ← hsl]
    omega
  have hos : ∀ j < (K c).es,
      slotOf rd σ (LXS σ) (LSS σ) ((segsOf σ K).a c + (K c).ex + j) = (K c).os j := by
    intro j hj
    obtain ⟨hlt', hl⟩ := kid_ws MF hK hc hj
    have hsl := hC.uniq _ (by omega) _ (by omega) hl
    unfold slotOf; simp only [hmk]
    rw [slot_search hC hs (by omega) (by omega) (by omega) (by omega), ← hsl]
    omega
  have hdi : ∀ d < (K c).ed, slotOf rd σ (LXS σ + LSS σ) (DAS σ)
      ((segsOf σ K).a c + (K c).ex + (K c).es + d) = (K c).di d := by
    intro d hd
    obtain ⟨hlt', hl⟩ := kid_wd MF hK hc hd
    have hsl := hC.uniq _ (by omega) _ (by omega) hl
    unfold slotOf; simp only [hmk]
    rw [slot_search hC hs (by omega) (by omega) (by omega) (by omega), ← hsl]
    omega
  have ex : (List.range (K c).ex).map (fun j => xmssAt rd (σ (.n 77))
      (slotOf rd σ 0 (LXS σ) ((segsOf σ K).a c + j))) =
      (List.range (K c).ex).map fun j => xmssAt rd (σ (.n 77)) ((K c).ox j) :=
    List.map_congr_left fun j hj => by rw [hox j (List.mem_range.mp hj)]
  have es : (List.range (K c).es).map (fun j => sphincsAt rd (σ (.n 80))
      (slotOf rd σ (LXS σ) (LSS σ) ((segsOf σ K).a c + (K c).ex + j))) =
      (List.range (K c).es).map fun j => sphincsAt rd (σ (.n 80)) ((K c).os j) :=
    List.map_congr_left fun j hj => by rw [hos j (List.mem_range.mp hj)]
  have ed : (List.range (K c).ed).map (fun j => daAt rd (σ (.n 69))
      (slotOf rd σ (LXS σ + LSS σ) (DAS σ) ((segsOf σ K).a c + (K c).ex + (K c).es + j))) =
      (List.range (K c).ed).map fun d => daAt rd (σ (.n 69)) ((K c).di d) :=
    List.map_congr_left fun j hj => by rw [hdi j (List.mem_range.mp hj)]
  unfold kidStmt
  simp only [countOf_eq MF hK (show c ≤ lg σ 6 by omega), countOf_eq MF hK (show c + 1 ≤ lg σ 6 by omega),
    lxSlots_eq MF, lsSlots_eq MF, daSlots_eq MF, hnx, hns, hnd, ex, es, ed]

end
end LeanVM.Guest.B1.Main
