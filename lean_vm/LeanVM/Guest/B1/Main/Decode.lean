/-
  LeanVM.Guest.B1.Main.Decode

  Decoders of what `main` reads from memory: bounded discrete logs, cells, digests, DA claims,
  deferred claims, fresh claims and coverage slots, each with the uniqueness lemma that makes it
  the value a run reads.
-/

module

public import LeanVM.Guest.B1.Main.Cover
public import LeanVM.Guest.B1.Main.FreshWeight

/-!
# Decoding `main`'s reads

Every value `main`'s soundness proof obtains as an existential is determined by the memory and by
`main`'s valuation. These are the decoders, explicit functions with no choice:

* `gLog x`: the first `n < 2^18` with `g^n = x` (`gLog_gen_pow`);
* `readCells rd p n`: the `n` words from `p` (`readCells_of_readsAt`);
* `digestAt x₀ x₁`: the digest of two cells (`digestAt_eq`);
* `daOf rd p i`: DA slot `i`'s claim (`daOf_of_daAt`);
* `decDefer rd p`, `decFresh rd p`: a deferred claim of `53` cells and a fresh claim of `106`
  (`decDefer_eq`, `decFresh_eq`);
* `slotOf rd cover T e`: the first slot below `T` whose word is `g^e` (`slotOf_eq`), the slot when
  only one holds it; `cover_all_w` and `cover_slot_unique` say each mark has one slot and each slot
  one mark when `T` marks fill `T` slots.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-! ## Lists of a function -/

theorem map_range_eq {α : Type} [Inhabited α] {n : ℕ} {g : ℕ → α} {l : List α}
    (hl : l.length = n) (h : ∀ k < n, g k = l.getD k default) : (List.range n).map g = l := by
  apply List.ext_getElem (by simp [hl])
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [h k (by simpa using h1), List.getD_eq_getElem _ _ h2]

/-! ## Bounded discrete logs -/

/-- The first `n < 2^18` with `g^n = x`, `0` when there is none. Irreducible: unfolding it would
run the search over `2^18` candidates. -/
@[irreducible] def gLog (x : E) : ℕ := ((List.range (2 ^ 18)).find? fun n => decide (gen ^ n = x)).getD 0

theorem gLog_gen_pow {n : ℕ} (h : n < 2 ^ 18) : gLog (gen ^ n) = n := by
  unfold gLog
  cases hf : (List.range (2 ^ 18)).find? (fun m => decide (gen ^ m = gen ^ n)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (decide_eq_true rfl) (hf n (List.mem_range.mpr h))
  | some m =>
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    rw [List.mem_range] at hm
    rw [Option.getD_some]
    exact gen_pow_inj' (by omega) (by omega) hp

/-! ## Cells -/

theorem cellAt_eq_getD {p : E} {cs : List E} (h : ReadsAt rd p cs) {k : ℕ} (hk : k < cs.length) :
    cellAt rd p k = cs.getD k 0 := by
  rw [List.getD_eq_getElem _ _ hk]; exact cellAt_of_load (h k hk)

/-- The `n` words from `p`, zero where there is none. -/
def readCells (rd : Reader) (p : E) (n : ℕ) : List E := (List.range n).map (cellAt rd p)

theorem readCells_of_readsAt {p : E} {cs : List E} (h : ReadsAt rd p cs) :
    readCells rd p cs.length = cs :=
  map_range_eq rfl fun _ hk => cellAt_eq_getD h hk

/-! ## Digests and DA claims -/

/-- The digest of two cells, zero where they are none. -/
def digestAt (x0 x1 : E) : Digest := (digestOfScalars (x0, x1)).getD (Vector.replicate 8 0)

theorem digestAt_eq {x0 x1 : E} {d : Digest} (h : (x0, x1) = digestScalars d) :
    digestAt x0 x1 = d := by
  rw [digestAt, h, digestOfScalars_digestScalars]; rfl

theorem digestAt_digestScalars (d : Digest) :
    digestAt (digestScalars d).1 (digestScalars d).2 = d := digestAt_eq rfl

/-- DA slot `i`'s claim at `p`: the root of its first two cells, the vector digest of the next
two. -/
def daOf (rd : Reader) (p : E) (i : ℕ) : DaClaim :=
  (digestAt (cellAt rd p (4 * i)) (cellAt rd p (4 * i + 1)),
    digestAt (cellAt rd p (4 * i + 2)) (cellAt rd p (4 * i + 3)))

theorem daOf_of_daAt {p : E} {i : ℕ} {cl : DaClaim} (h : DaAt rd p i cl) : daOf rd p i = cl := by
  obtain ⟨h0, h1, h2, h3⟩ := cells_of_reads (s := i) h
  rw [daOf, h0, h1, h2, h3, digestAt_digestScalars, digestAt_digestScalars]

theorem daOf_of_claimsAt {p : E} {cls : List DaClaim} (h : DaClaimsAt rd p cls) :
    (List.range cls.length).map (daOf rd p) = cls :=
  map_range_eq rfl fun k hk => by
    rw [daOf_of_daAt (daAt_of_claimsAt h k hk), List.getD_eq_getElem _ _ hk]

/-! ## Deferred and fresh claims -/

/-- The deferred claim of the `53` cells at `p`. -/
def decDefer (rd : Reader) (p : E) : DeferredClaim := deferOfCells (readCells rd p 53)

theorem decDefer_eq {p : E} {d : DeferredClaim} (h1 : d.bytecodePoint.length = 22)
    (h2 : d.matrixPoint.length = 28) (h : ReadsAt rd p d.cells) : decDefer rd p = d := by
  have hl : d.cells.length = 53 := by simp [DeferredClaim.cells, h1, h2]
  rw [decDefer, ← hl, readCells_of_readsAt h, deferOfCells_cells h1 h2]

/-- The fresh claims of the `106` cells at `p`, by their `FRESH_*` offsets. -/
def decFresh (rd : Reader) (p : E) : FixedClaims :=
  ⟨(List.range 22).map (cellAt rd p), cellAt rd p 22, cellAt rd p 23, cellAt rd p 24,
    (List.range 8).map fun k => cellAt rd p (25 + k),
    (List.range 8).map fun j => cellAt rd p (33 + (7 - j)),
    (List.range 64).map fun i => cellAt rd p (41 + i), cellAt rd p 105⟩

theorem decFresh_eq {p : E} {f : FixedClaims} (hf : FreshShaped f) (h : ReadsAt rd p (fixedCells f)) :
    decFresh rd p = f := by
  obtain ⟨hl, hbp, hbv, hal, hz, hrp, hcp, hsl, hmv⟩ := fixedCells_getD hf
  have hc : ∀ k < 106, cellAt rd p k = (fixedCells f).getD k 0 :=
    fun k hk => cellAt_eq_getD h (by omega)
  obtain ⟨h1, h2, h3, h4⟩ := hf
  obtain ⟨bp, bv, al, zs, rp, cp, sl, mv⟩ := f
  simp only at h1 h2 h3 h4 hbp hbv hal hz hrp hcp hsl hmv
  simp only [decFresh, FixedClaims.mk.injEq]
  refine ⟨map_range_eq h1 fun k hk => ?_, by rw [hc 22 (by omega), hbv],
    by rw [hc 23 (by omega), hal], by rw [hc 24 (by omega), hz],
    map_range_eq h2 fun k hk => ?_, map_range_eq h3 fun j hj => ?_,
    map_range_eq h4 fun i hi => ?_, by rw [hc 105 (by omega), hmv]⟩
  · rw [hc k (by omega), hbp k hk]; rfl
  · rw [hc (25 + k) (by omega), hrp k hk]; rfl
  · rw [hc (33 + (7 - j)) (by omega), hcp (7 - j) (by omega), show 7 - (7 - j) = j by omega]; rfl
  · rw [hc (41 + i) (by omega), hsl i hi]; rfl

/-! ## Coverage slots -/

/-- The first slot below `T` of the coverage table at `cover` whose word is `g^e`. -/
def slotOf (rd : Reader) (cover : E) (T e : ℕ) : ℕ :=
  ((List.range T).find? fun s => decide (cellAt rd cover s = gen ^ e)).getD 0

theorem slotOf_eq {cover : E} {T e s : ℕ} (hs : s < T) (hl : cellAt rd cover s = gen ^ e)
    (hu : ∀ s' < T, cellAt rd cover s' = gen ^ e → s' = s) : slotOf rd cover T e = s := by
  unfold slotOf
  cases hf : (List.range T).find? (fun s => decide (cellAt rd cover s = gen ^ e)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (decide_eq_true hl) (hf s (List.mem_range.mpr hs))
  | some m =>
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    rw [Option.getD_some]
    exact hu m (List.mem_range.mp hm) hp

/-- **The coverage table, with marks**: if each mark `g^e`, `e < T`, sits in a slot below `T`
that it certifies, every slot below `T` holds a mark that certifies it. -/
theorem cover_all_w {cover : E} {T : ℕ} (hT : T < 2 ^ 34) {Good : ℕ → ℕ → Prop}
    (hw : ∀ e < T, ∃ s < T, LoadHolds rd cover s (gen ^ e) ∧ Good e s) :
    ∀ s < T, ∃ e < T, LoadHolds rd cover s (gen ^ e) ∧ Good e s := by
  classical
  choose! slot hslot hload hgood using hw
  have hcov := cover_of_writeOnce (N := T) (M := T) (slot := slot) (mark := fun e => gen ^ e)
    (mem := fun s => cellAt rd cover s) hslot
    (fun i hi j hj h => gen_pow_inj' (by omega) (by omega) h)
    (fun i hi => cellAt_of_load (hload i hi)) le_rfl
  intro s hs
  obtain ⟨e, ⟨he, hse⟩, -⟩ := hcov s hs
  exact ⟨e, he, hse ▸ hload e he, hse ▸ hgood e he⟩

/-- **A mark has one slot**: when every mark `g^e`, `e < T`, sits in a slot below `T`, two slots
below `T` holding the same mark are one. -/
theorem cover_slot_unique {cover : E} {T : ℕ} (hT : T < 2 ^ 34)
    (hw : ∀ e < T, ∃ s < T, LoadHolds rd cover s (gen ^ e)) {e s1 s2 : ℕ} (he : e < T)
    (h1 : s1 < T) (h2 : s2 < T) (l1 : cellAt rd cover s1 = gen ^ e)
    (l2 : cellAt rd cover s2 = gen ^ e) : s1 = s2 := by
  classical
  choose! slot hslot hload using hw
  have hcov := cover_of_writeOnce (N := T) (M := T) (slot := slot) (mark := fun e => gen ^ e)
    (mem := fun s => cellAt rd cover s) hslot
    (fun i hi j hj h => gen_pow_inj' (by omega) (by omega) h)
    (fun i hi => cellAt_of_load (hload i hi)) le_rfl
  have key : ∀ s < T, cellAt rd cover s = gen ^ e → s = slot e := by
    intro s hs hl
    obtain ⟨i, ⟨hi, his⟩, -⟩ := hcov s hs
    have hc : cellAt rd cover s = gen ^ i := by rw [← his]; exact cellAt_of_load (hload i hi)
    have := gen_pow_inj' (by omega) (by omega) (hc.symm.trans hl)
    rw [← his, this]
  rw [key s1 h1 l1, key s2 h2 l2]

end
end LeanVM.Guest.B1.Main
