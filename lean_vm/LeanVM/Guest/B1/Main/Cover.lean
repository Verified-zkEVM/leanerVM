/-
  LeanVM.Guest.B1.Main.Cover

  The coverage table of `main` as a bijection: every mark below the total is written into one
  slot of its region, so every slot holds one mark, and the decoders' searches find them.
-/

module

public import LeanVM.Guest.B1.Main.Facts
public import LeanVM.Guest.Value.Pigeonhole

/-!
# The coverage table

The writers of `main`'s coverage table (G:4141-4205) store the marks `g^m`, `m < T`, one each:
the raw leanXMSS signatures (`m < RX`), the raw leanSPHINCS ones (`RX ≤ m < RX + RS`), and child
`c`'s claims, from its base `a c`: its leanXMSS claims, then its leanSPHINCS ones (`Segs`). Each
writer's slot lies in its region: leanXMSS slots below `LXS`, leanSPHINCS slots in
`[LXS, LXS + LSS)` (`region`, `InRegion`). The slots lie below `T = LXS + LSS`, write-once memory
keeps the marks apart, so the writers fill every slot once (`cover_bij`, from
`Value.cover_of_writeOnce`): the mark in slot `s` (`markAt`) has its writer there, in the slot's
region.

For the decoders: `find_first` (the child whose segment holds a mark), `find_unique` (the slot
holding a mark), `filter_card` (the number of a segment's marks in a region).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

/-! ## Searches over a range -/

/-- The first index below `n` at which a monotone `A` passes `e` is the `c` with
`A c ≤ e < A (c + 1)`. -/
theorem find_first {A : ℕ → ℕ} (hA : Monotone A) {n c e : ℕ} (hc : c < n) (h1 : A c ≤ e)
    (h2 : e < A (c + 1)) :
    ((List.range n).find? fun c' => decide (e < A (c' + 1))).getD 0 = c := by
  have key : (List.range n).find? (fun c' => decide (e < A (c' + 1))) = some c := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using h2, c, by simpa using hc, by simp, fun j hj => ?_⟩
    simp only [List.getElem_range, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      not_lt]
    exact le_trans (hA (show j + 1 ≤ c by omega)) h1
  rw [key]; rfl

/-- A search for the unique index below `n` passing `p`. -/
theorem find_unique {p : ℕ → Bool} {n s : ℕ} (hs : s < n) (hp : p s = true)
    (hu : ∀ t < n, p t = true → t = s) : ((List.range n).find? p).getD 0 = s := by
  have key : (List.range n).find? p = some s := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨hp, s, by simpa using hs, by simp, fun j hj => ?_⟩
    simp only [List.getElem_range]
    by_contra hc
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
    have := hu j (by omega) hc
    omega
  rw [key]; rfl

/-- The indices below `len` passing `P` are the images of `j < k` under an injective `f`: as many
as `k`. -/
theorem filter_card {P : ℕ → Bool} {len k : ℕ} (f : ℕ → ℕ) (hf : ∀ j < k, f j < len ∧ P (f j))
    (hinj : ∀ i < k, ∀ j < k, f i = f j → i = j)
    (hall : ∀ s < len, P s = true → ∃ j < k, f j = s) :
    ((List.range len).filter P).length = k := by
  have hnd1 : ((List.range len).filter P).Nodup := (List.nodup_range).filter _
  have hnd2 : ((List.range k).map f).Nodup := by
    rw [List.nodup_map_iff_inj_on List.nodup_range]
    intro i hi j hj h
    exact hinj i (List.mem_range.mp hi) j (List.mem_range.mp hj) h
  have hp : ((List.range len).filter P).Perm ((List.range k).map f) := by
    rw [List.perm_ext_iff_of_nodup hnd1 hnd2]
    intro s
    simp only [List.mem_filter, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨hs, hP⟩
      exact hall s hs hP
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(hf j hj).1, (hf j hj).2⟩
  rw [hp.length_eq, List.length_map, List.length_range]

/-! ## The segments -/

/-- The writers' structure: raw signature counts, the children's counts. -/
structure Segs where
  RX : ℕ
  RS : ℕ
  NC : ℕ
  ex : ℕ → ℕ
  es : ℕ → ℕ

namespace Segs

variable (S : Segs)

/-- Child `c`'s base: the marks before its segment. -/
def a : ℕ → ℕ
  | 0 => S.RX + S.RS
  | c + 1 => a c + (S.ex c + S.es c)

theorem a_mono : Monotone S.a := monotone_nat_of_le_succ fun c => by simp [a]

/-- The child whose segment holds the mark `m`. -/
noncomputable def kid (m : ℕ) : ℕ := ((List.range S.NC).find? fun c => decide (m < S.a (c + 1))).getD 0

/-- The region of the mark `m`'s writer: `0` leanXMSS, `1` leanSPHINCS. -/
noncomputable def region (m : ℕ) : ℕ :=
  if m < S.RX then 0 else if m < S.RX + S.RS then 1 else
  if m - S.a (S.kid m) < S.ex (S.kid m) then 0 else 1

theorem seg_exists {m : ℕ} (h0 : S.a 0 ≤ m) :
    ∀ n, m < S.a n → ∃ c, c < n ∧ S.a c ≤ m ∧ m < S.a (c + 1) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h1
    by_cases hn : m < S.a n
    · obtain ⟨c, hc, h⟩ := ih hn
      exact ⟨c, by omega, h⟩
    · exact ⟨n, by omega, by omega, h1⟩

theorem kid_spec {m : ℕ} (h0 : S.a 0 ≤ m) (h1 : m < S.a S.NC) :
    S.kid m < S.NC ∧ S.a (S.kid m) ≤ m ∧ m < S.a (S.kid m + 1) := by
  obtain ⟨c, hc, hc1, hc2⟩ := S.seg_exists h0 S.NC h1
  have := find_first S.a_mono hc hc1 hc2
  unfold kid
  rw [this]
  exact ⟨hc, hc1, hc2⟩

end Segs

/-- The slot `s` lies in the region `r` of a table of `LXS` leanXMSS slots, then `LSS`
leanSPHINCS slots. -/
def InRegion (LXS LSS : ℕ) (r s : ℕ) : Prop :=
  (r = 0 → s < LXS) ∧ (r = 1 → LXS ≤ s ∧ s < LXS + LSS)

/-! ## The writers -/

/-- **What the writers establish**, for the coverage table at `cover`. -/
structure Writers (rd : Reader) (cover : E) (S : Segs) (LXS LSS : ℕ) : Prop where
  rawx : ∀ i < S.RX, ∃ s < LXS, LoadHolds rd cover s (gen ^ i)
  raws : ∀ j < S.RS, ∃ s < LSS, LoadHolds rd cover (LXS + s) (gen ^ (S.RX + j))
  kidx : ∀ c < S.NC, ∀ j < S.ex c, ∃ s < LXS, LoadHolds rd cover s (gen ^ (S.a c + j))
  kids : ∀ c < S.NC, ∀ j < S.es c, ∃ s < LSS,
    LoadHolds rd cover (LXS + s) (gen ^ (S.a c + S.ex c + j))
  total : S.a S.NC = LXS + LSS
  small : LXS + LSS < 2 ^ 34

namespace Writers

variable {rd : Reader} {cover : E} {S : Segs} {LXS LSS : ℕ}

/-- Every mark below the total is written into a slot of its region. -/
theorem slot_exists (W : Writers rd cover S LXS LSS) :
    ∀ m < LXS + LSS, ∃ s, s < LXS + LSS ∧ LoadHolds rd cover s (gen ^ m) ∧
      InRegion LXS LSS (S.region m) s := by
  intro m hm
  unfold Segs.region
  by_cases h1 : m < S.RX
  · obtain ⟨s, hs, hl⟩ := W.rawx m h1
    exact ⟨s, by omega, hl, by simp [InRegion, h1]; omega⟩
  by_cases h2 : m < S.RX + S.RS
  · obtain ⟨s, hs, hl⟩ := W.raws (m - S.RX) (by omega)
    rw [show S.RX + (m - S.RX) = m by omega] at hl
    exact ⟨LXS + s, by omega, hl, by simp [InRegion, h1, h2]; omega⟩
  obtain ⟨hc, hc1, hc2⟩ := S.kid_spec (m := m) (by simp [Segs.a]; omega)
    (by rw [W.total]; exact hm)
  set c := S.kid m
  have hac : S.a (c + 1) = S.a c + (S.ex c + S.es c) := rfl
  simp only [h1, h2, ↓reduceIte]
  by_cases h4 : m - S.a c < S.ex c
  · obtain ⟨s, hs, hl⟩ := W.kidx c hc (m - S.a c) h4
    rw [show S.a c + (m - S.a c) = m by omega] at hl
    exact ⟨s, by omega, hl, by simp [InRegion, h4]; omega⟩
  · obtain ⟨s, hs, hl⟩ := W.kids c hc (m - S.a c - S.ex c) (by omega)
    rw [show S.a c + S.ex c + (m - S.a c - S.ex c) = m by omega] at hl
    exact ⟨LXS + s, by omega, hl, by simp [InRegion, h4]; omega⟩

end Writers

/-- The mark in slot `s` of the table at `cover`, as a log. -/
noncomputable def markAt (rd : Reader) (cover : E) (s : ℕ) : ℕ := gLog (memAt rd cover s)

/-- **The coverage table**: a slot function for the marks below `T`, each in its region, and every
slot below `T` holding the mark whose slot it is. -/
structure Cover (rd : Reader) (cover : E) (S : Segs) (LXS LSS : ℕ) (sl : ℕ → ℕ) : Prop where
  lt : ∀ m < LXS + LSS, sl m < LXS + LSS
  wr : ∀ m < LXS + LSS, LoadHolds rd cover (sl m) (gen ^ m)
  reg : ∀ m < LXS + LSS, InRegion LXS LSS (S.region m) (sl m)
  mark : ∀ s < LXS + LSS, markAt rd cover s < LXS + LSS ∧ sl (markAt rd cover s) = s
  uniq : ∀ s < LXS + LSS, ∀ m < LXS + LSS, LoadHolds rd cover s (gen ^ m) → s = sl m

/-- **The writers fill the table once.** -/
theorem cover_bij {rd : Reader} {cover : E} {S : Segs} {LXS LSS : ℕ}
    (W : Writers rd cover S LXS LSS) : ∃ sl, Cover rd cover S LXS LSS sl := by
  have hex := W.slot_exists
  choose! sl hlt hwr hreg using hex
  have hT := W.small
  have hmem : ∀ m < LXS + LSS, memAt rd cover (sl m) = gen ^ m :=
    fun m hm => memAt_of_load (hwr m hm)
  have hbij := cover_of_writeOnce (N := LXS + LSS) (M := LXS + LSS) (slot := sl)
    (mark := fun m => gen ^ m) (mem := memAt rd cover) hlt
    (fun i hi j hj h => gen_pow_inj34 (by omega) (by omega) h) hmem le_rfl
  have hmark : ∀ s < LXS + LSS, markAt rd cover s < LXS + LSS ∧ sl (markAt rd cover s) = s := by
    intro s hs
    obtain ⟨m, ⟨hm, hms⟩, -⟩ := hbij s hs
    have : markAt rd cover s = m := by
      rw [markAt, ← hms, hmem m hm, gLog_gen_pow (by omega)]
    rw [this]
    exact ⟨hm, hms⟩
  refine ⟨sl, hlt, hwr, hreg, hmark, fun s hs m hm hl => ?_⟩
  obtain ⟨hlt', hsl⟩ := hmark s hs
  have : markAt rd cover s = m := by
    rw [markAt, memAt_of_load hl, gLog_gen_pow (by omega)]
  rw [← this, hsl]

end
end LeanVM.Guest.B1.Main
