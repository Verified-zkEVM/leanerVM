/-
  LeanVM.Guest.B1.Main.WritersW

  `main`'s coverage argument with the holders given: every mark's writer certifies its slot by the
  holder a function of the mark and the slot names, and a child's statement decoded from the slots
  of its marks.
-/

module

public import LeanVM.Guest.B1.Main.Sound
public import LeanVM.Guest.B1.Main.Decode

/-!
# The writers, with their holders

`SlotGoodW … hX hS hD e s`: slot `s` of the coverage table, holding the mark `g^e`, is certified by
the holder `hX e s` (`hS`, `hD` in the leanSPHINCS and DA regions), raw or a child's.
`writers_good_w` is `writers_good` with the holders given: when every mark below a child's
segment's start is a raw writer's whose holder certifies its slot, and every mark of child `c`'s
segment names child `c`, every mark certifies its slot.

`kidStmt rd F T cnt c` is child `c`'s statement read off the coverage table: the slots of its
marks `g^e`, `cnt c ≤ e < cnt (c + 1)`, in order, the leanXMSS region's its leanXMSS claims, the
leanSPHINCS region's its leanSPHINCS claims, the DA region's its DA claims, and its deferred cells
at `carried·g^(53c)`. `kidStmt_eq`: it is the statement of `ChildAt` when each mark has one slot.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {bytecode : List K} {rd : Reader}

/-! ## Lists of ranges -/

theorem map_range_eq_of_getElem? {α : Type} {n : ℕ} {g : ℕ → α} {l : List α} (hl : l.length = n)
    (h : ∀ j < n, l[j]? = some (g j)) : (List.range n).map g = l := by
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range]
  have := h j (by simpa using h1)
  rw [List.getElem?_eq_getElem h2, Option.some.injEq] at this
  exact this.symm

theorem range_map_split3 {α : Type} (f : ℕ → α) (a b c : ℕ) :
    (List.range (a + (b + c))).map f = (List.range a).map f ++
      (List.range b).map (fun j => f (a + j)) ++ (List.range c).map (fun j => f (a + b + j)) := by
  simp [List.range_add, List.map_append, Function.comp_def, Nat.add_assoc]

theorem filter_map_range_true {α : Type} (f : ℕ → α) (P : α → Bool) (a : ℕ)
    (h : ∀ j < a, P (f j) = true) : ((List.range a).map f).filter P = (List.range a).map f :=
  List.filter_eq_self.mpr fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact h j (List.mem_range.mp hj)

theorem filter_map_range_false {α : Type} (f : ℕ → α) (P : α → Bool) (a : ℕ)
    (h : ∀ j < a, P (f j) = false) : ((List.range a).map f).filter P = [] :=
  List.filter_eq_nil_iff.mpr fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    simp [h j (List.mem_range.mp hj)]

theorem forall₂_of_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i]) → List.Forall₂ R l₁ l₂
  | [], [], _, _ => List.Forall₂.nil
  | a :: l₁, b :: l₂, hl, h => List.Forall₂.cons (h 0 (by simp) (by simp))
      (forall₂_of_getElem (by simpa using hl) fun i h₁ h₂ =>
        h (i + 1) (by simpa using h₁) (by simpa using h₂))
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)

/-! ## Certified slots -/

/-- **Slot `s`, with the mark `g^e`, is certified by its holder**: `hX e s` holds the leanXMSS
table's claim `s`, `hS` the leanSPHINCS claim, `hD` the DA claim, by the slot's region. -/
def SlotGoodW (rd : Reader) (F : Frame) (chs : List Child)
    (hX : ℕ → ℕ → Holder LeanXmss.Signature) (hS : ℕ → ℕ → Holder Sphincs.Signature)
    (hD : ℕ → ℕ → Holder Da.Witness) (e s : ℕ) : Prop :=
  (s < F.Lx → XmssHeld chs (entryX rd F.lxT s) (hX e s)) ∧
    (F.Lx ≤ s → s < F.Lx + F.Ls →
      SphincsHeld chs (entryS rd F.spT (s - F.Lx)) (hS e (s - F.Lx))) ∧
    (F.Lx + F.Ls ≤ s → ∀ cl, DaAt rd F.daR (s - (F.Lx + F.Ls)) cl →
      DaHeld chs cl (hD e (s - (F.Lx + F.Ls))))

/-- **Every mark certifies its slot, by its holder**: `writers_good` with the holders given. -/
theorem writers_good_w {F : Frame} {seed : Digest} {chs : List Child} {a2 a5 a7 : ℕ}
    {hX : ℕ → ℕ → Holder LeanXmss.Signature} {hS : ℕ → ℕ → Holder Sphincs.Signature}
    {hD : ℕ → ℕ → Holder Da.Witness}
    (hdaC : F.daC = F.cover * gen ^ (F.Lx + F.Ls))
    (h3 : ∀ i < a2, ∃ s < F.Lx, LoadHolds rd F.cover s (gen ^ i) ∧
      XmssHeld chs (entryX rd F.lxT s) (hX i s))
    (h4 : ∀ j < a5, ∃ s < F.Ls, LoadHolds rd F.cover (F.Lx + s) (gen ^ (a2 + j)) ∧
      SphincsHeld chs (entryS rd F.spT s) (hS (a2 + j) s))
    (ha7 : a7 ≤ 1)
    (hd : a7 = 1 → ∃ i < F.Md, LoadHolds rd F.daC i (gen ^ (a2 + a5)) ∧
      ∀ cl, DaAt rd F.daR i cl → DaHeld chs cl (hD (a2 + a5) i))
    (hch : ∀ c (hc : c < chs.length), ChildAt bytecode rd F seed c chs[c])
    (hbase : ∀ c ≤ chs.length, LoadHolds rd F.written c (gen ^ counts (a2 + a5 + a7) chs c))
    (hkid : ∀ e c, c < chs.length → counts (a2 + a5 + a7) chs c ≤ e →
      e < counts (a2 + a5 + a7) chs (c + 1) →
        ∀ s, hX e s = .child c ∧ hS e s = .child c ∧ hD e s = .child c) :
    ∀ e < counts (a2 + a5 + a7) chs chs.length, ∃ s < F.Lx + F.Ls + F.Md,
      LoadHolds rd F.cover s (gen ^ e) ∧ SlotGoodW rd F chs hX hS hD e s := by
  intro e he
  rcases Nat.lt_or_ge e a2 with h1 | h1
  · obtain ⟨s, hs, hl, hh⟩ := h3 e h1
    exact ⟨s, by omega, hl, fun _ => hh, fun h _ => absurd h (by omega),
      fun h => absurd h (by omega)⟩
  rcases Nat.lt_or_ge e (a2 + a5) with h2 | h2
  · obtain ⟨s, hs, hl, hh⟩ := h4 (e - a2) (by omega)
    rw [show a2 + (e - a2) = e by omega] at hl hh
    refine ⟨F.Lx + s, by omega, hl, fun h => absurd h (by omega), fun _ _ => ?_,
      fun h => absurd h (by omega)⟩
    rwa [Nat.add_sub_cancel_left]
  rcases Nat.lt_or_ge e (a2 + a5 + a7) with h5 | h5
  · obtain ⟨i, hi, hl, hw⟩ := hd (by omega)
    rw [hdaC, loadHolds_mul_gen_pow, show a2 + a5 = e by omega] at hl
    rw [show a2 + a5 = e by omega] at hw
    refine ⟨F.Lx + F.Ls + i, by omega, hl, fun h => absurd h (by omega),
      fun _ h => absurd h (by omega), fun _ => ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact hw
  obtain ⟨c, hc, hc1, hc2⟩ := exists_segment (counts (a2 + a5 + a7) chs)
    (counts_mono (a2 + a5 + a7) chs) (show counts (a2 + a5 + a7) chs 0 ≤ e by simpa [counts])
    chs.length he
  have hk := hkid e c hc hc1 hc2
  rw [counts_succ _ _ _ hc, nOf] at hc2
  obtain ⟨base, hw0, -, -, -, -, hXc, hSc, hDc, -⟩ := hch c hc
  have hb := loadHolds_unique hw0 (hbase c (by omega))
  subst hb
  set b := counts (a2 + a5 + a7) chs c
  have hget : chs[c]? = some chs[c] := List.getElem?_eq_getElem hc
  rcases Nat.lt_or_ge e (b + chs[c].statement.claims.xmss.length) with g1 | g1
  · obtain ⟨s, hs, hl, he'⟩ := hXc (e - b) (by omega)
    rw [← pow_add, show b + (e - b) = e by omega] at hl
    refine ⟨s, by omega, hl, fun _ => ?_, fun h => absurd h (by omega),
      fun h => absurd h (by omega)⟩
    rw [(hk s).1]
    exact ⟨chs[c], hget, List.mem_of_getElem? he'⟩
  rcases Nat.lt_or_ge e (b + chs[c].statement.claims.xmss.length +
    chs[c].statement.claims.sphincs.length) with g2 | g2
  · obtain ⟨s, hs, hl, he'⟩ := hSc (e - b - chs[c].statement.claims.xmss.length) (by omega)
    rw [← pow_add, show b + (chs[c].statement.claims.xmss.length +
      (e - b - chs[c].statement.claims.xmss.length)) = e by omega] at hl
    refine ⟨F.Lx + s, by omega, hl, fun h => absurd h (by omega), fun _ _ => ?_,
      fun h => absurd h (by omega)⟩
    rw [Nat.add_sub_cancel_left, (hk s).2.1]
    exact ⟨chs[c], hget, List.mem_of_getElem? he'⟩
  · obtain ⟨i, hi, hl, hcl⟩ := hDc (e - b - chs[c].statement.claims.xmss.length -
      chs[c].statement.claims.sphincs.length) (by omega)
    rw [← pow_add, show b + (chs[c].statement.claims.xmss.length +
      chs[c].statement.claims.sphincs.length + (e - b - chs[c].statement.claims.xmss.length -
      chs[c].statement.claims.sphincs.length)) = e by omega, hdaC, loadHolds_mul_gen_pow] at hl
    refine ⟨F.Lx + F.Ls + i, by omega, hl, fun h => absurd h (by omega),
      fun _ h => absurd h (by omega), fun _ cl hcl' => ?_⟩
    rw [Nat.add_sub_cancel_left] at hcl' ⊢
    rw [(hk i).2.2]
    have hcl'' := List.getElem?_eq_getElem (l := chs[c].statement.claims.da)
      (i := e - b - chs[c].statement.claims.xmss.length - chs[c].statement.claims.sphincs.length)
      (by omega)
    have := daAt_unique hcl' (hcl _ hcl'')
    subst this
    exact ⟨chs[c], hget, List.mem_of_getElem? hcl''⟩

/-! ## A child's statement, read off the coverage table -/

/-- The slots of the marks `g^e`, `b₀ ≤ e < b₁`, in order. -/
def kidSlots (rd : Reader) (cover : E) (T b0 b1 : ℕ) : List ℕ :=
  (List.range (b1 - b0)).map fun j => slotOf rd cover T (b0 + j)

/-- **Child `c`'s statement, read off the coverage table** of `T` slots, the running counts `cnt`:
the claims of its marks' slots, by region, and its deferred cells. -/
def kidStmt (rd : Reader) (F : Frame) (T : ℕ) (cnt : ℕ → ℕ) (c : ℕ) : NodeStatement :=
  ⟨⟨((kidSlots rd F.cover T (cnt c) (cnt (c + 1))).filter fun s => decide (s < F.Lx)).map
      (entryX rd F.lxT),
    ((kidSlots rd F.cover T (cnt c) (cnt (c + 1))).filter fun s =>
      decide (F.Lx ≤ s ∧ s < F.Lx + F.Ls)).map fun s => entryS rd F.spT (s - F.Lx),
    ((kidSlots rd F.cover T (cnt c) (cnt (c + 1))).filter fun s =>
      decide (F.Lx + F.Ls ≤ s)).map fun s => daOf rd F.daR (s - (F.Lx + F.Ls))⟩,
    decDefer rd (F.carried * gen ^ (53 * c))⟩

/-- **A child's statement is the one its marks' slots hold**: when the counts give child `c` the
segment `b ≤ e < b + n` of `n` marks, each with one slot below `T`, the statement `ChildAt` reads
is `kidStmt`'s. -/
theorem kidStmt_eq {F : Frame} {T : ℕ} {cnt : ℕ → ℕ} {c b : ℕ} {st : NodeStatement}
    (hdaC : F.daC = F.cover * gen ^ (F.Lx + F.Ls)) (hT : F.Lx + F.Ls + F.Md ≤ T)
    (hb0 : cnt c = b)
    (hb1 : cnt (c + 1) = b + (st.claims.xmss.length + st.claims.sphincs.length +
      st.claims.da.length))
    (hsl : ∀ j < st.claims.xmss.length + st.claims.sphincs.length + st.claims.da.length,
      ∀ s < T, LoadHolds rd F.cover s (gen ^ (b + j)) → slotOf rd F.cover T (b + j) = s)
    (hX : ∀ j < st.claims.xmss.length, ∃ s < F.Lx, LoadHolds rd F.cover s (gen ^ b * gen ^ j) ∧
      st.claims.xmss[j]? = some (entryX rd F.lxT s))
    (hS : ∀ j < st.claims.sphincs.length, ∃ s < F.Ls,
      LoadHolds rd F.cover (F.Lx + s) (gen ^ b * gen ^ (st.claims.xmss.length + j)) ∧
      st.claims.sphincs[j]? = some (entryS rd F.spT s))
    (hD : ∀ j < st.claims.da.length, ∃ i < F.Md,
      LoadHolds rd F.daC i (gen ^ b * gen ^ (st.claims.xmss.length +
        st.claims.sphincs.length + j)) ∧
      ∀ cl, st.claims.da[j]? = some cl → DaAt rd F.daR i cl)
    (h22 : st.defer.bytecodePoint.length = 22) (h28 : st.defer.matrixPoint.length = 28)
    (hdef : ReadsAt rd (F.carried * gen ^ (53 * c)) st.defer.cells) :
    kidStmt rd F T cnt c = st := by
  obtain ⟨⟨xs, ss, ds⟩, df⟩ := st
  simp only at hb1 hsl hX hS hD h22 h28 hdef
  have hsl' : kidSlots rd F.cover T (cnt c) (cnt (c + 1)) =
      (List.range xs.length).map (fun j => slotOf rd F.cover T (b + j)) ++
      (List.range ss.length).map (fun j => slotOf rd F.cover T (b + (xs.length + j))) ++
      (List.range ds.length).map
        (fun j => slotOf rd F.cover T (b + (xs.length + ss.length + j))) := by
    rw [kidSlots, hb0, hb1, Nat.add_sub_cancel_left, Nat.add_assoc, range_map_split3]
  -- each mark's slot
  have fX : ∀ j < xs.length, ∃ s < F.Lx, slotOf rd F.cover T (b + j) = s ∧
      xs[j]? = some (entryX rd F.lxT s) := by
    intro j hj
    obtain ⟨s, hs, hl, he⟩ := hX j hj
    rw [← pow_add] at hl
    exact ⟨s, hs, hsl j (by omega) s (by omega) hl, he⟩
  have fS : ∀ j < ss.length, ∃ s < F.Ls, slotOf rd F.cover T (b + (xs.length + j)) = F.Lx + s ∧
      ss[j]? = some (entryS rd F.spT s) := by
    intro j hj
    obtain ⟨s, hs, hl, he⟩ := hS j hj
    rw [← pow_add] at hl
    exact ⟨s, hs, hsl (xs.length + j) (by omega) _ (by omega) hl, he⟩
  have fD : ∀ j < ds.length, ∃ i < F.Md,
      slotOf rd F.cover T (b + (xs.length + ss.length + j)) = F.Lx + F.Ls + i ∧
      ds[j]? = some (daOf rd F.daR i) := by
    intro j hj
    obtain ⟨i, hi, hl, he⟩ := hD j hj
    rw [← pow_add, hdaC, loadHolds_mul_gen_pow] at hl
    exact ⟨i, hi, hsl (xs.length + ss.length + j) (by omega) _ (by omega) hl,
      by rw [List.getElem?_eq_getElem hj, daOf_of_daAt (he _ (List.getElem?_eq_getElem hj))]⟩
  rw [kidStmt, hsl', decDefer_eq h22 h28 hdef]
  simp only [List.filter_append, NodeStatement.mk.injEq, Claims.mk.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [filter_map_range_true _ _ _ fun j hj => by
        obtain ⟨s, hs, e, -⟩ := fX j hj; simpa [e] using hs,
      filter_map_range_false _ _ _ fun j hj => by
        obtain ⟨s, hs, e, -⟩ := fS j hj; simp [e],
      filter_map_range_false _ _ _ fun j hj => by
        obtain ⟨i, hi, e, -⟩ := fD j hj; simp only [e, decide_eq_false_iff_not]; omega,
      List.append_nil, List.append_nil, List.map_map]
    exact map_range_eq_of_getElem? rfl fun j hj => by
      obtain ⟨s, hs, e, he⟩ := fX j hj
      simp [e, he]
  · rw [filter_map_range_false _ _ _ fun j hj => by
        obtain ⟨s, hs, e, -⟩ := fX j hj; simp only [e, decide_eq_false_iff_not]; omega,
      filter_map_range_true _ _ _ fun j hj => by
        obtain ⟨s, hs, e, -⟩ := fS j hj; simp only [e, decide_eq_true_eq]; omega,
      filter_map_range_false _ _ _ fun j hj => by
        obtain ⟨i, hi, e, -⟩ := fD j hj; simp only [e, decide_eq_false_iff_not]; omega,
      List.nil_append, List.append_nil, List.map_map]
    exact map_range_eq_of_getElem? rfl fun j hj => by
      obtain ⟨s, hs, e, he⟩ := fS j hj
      simp [e, he]
  · rw [filter_map_range_false _ _ _ fun j hj => by
        obtain ⟨s, hs, e, -⟩ := fX j hj; simp only [e, decide_eq_false_iff_not]; omega,
      filter_map_range_false _ _ _ fun j hj => by
        obtain ⟨s, hs, e, -⟩ := fS j hj; simp only [e, decide_eq_false_iff_not]; omega,
      filter_map_range_true _ _ _ fun j hj => by
        obtain ⟨i, hi, e, -⟩ := fD j hj; simp [e],
      List.nil_append, List.nil_append, List.map_map]
    exact map_range_eq_of_getElem? rfl fun j hj => by
      obtain ⟨i, hi, e, he⟩ := fD j hj
      simp [e, he]

end
end LeanVM.Guest.B1.Main
