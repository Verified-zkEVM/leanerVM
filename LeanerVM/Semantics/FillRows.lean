/-
  LeanerVM.Semantics.FillRows

  The rows the fill blocks add: one skeleton per row, and the proof that they are valid fillers.
-/

module

public import LeanerVM.Semantics.FillCycle
public import LeanerVM.Semantics.FillerRows

/-!
# The rows of a fill

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category A. A row of an arithmetization table is a state
and the instruction fetched at it. `Skel` is that pair, before any column is built from it: the
witness of the next layer builds each table's rows from the skeletons of its instructions.

**The skeletons of a traversal.** One traversal of the cycle `(t, k)` visits the `s + 1` slots of
the block, `s = sizeAt k`, in the cycle's frame: the first `s` fetch the dummy of `t` and the last
fetches the closing jump (`cycleSkels`). The fill of a table is the traversals its plan lists, each
cycle traversed some number of times (`padSkels`).

**The padding rows are valid fillers.** The repository's own check on filler rows
(`FillerRowsValid`, Layer 8) asks that none starts at the sentinel and that the multiset of starts
equals the multiset of successors. A traversal's starts are `x_0, ..., x_s`, their successors are
`x_1, ..., x_s, x_0` (`fill_dummy_step`, `fill_close_step`), a rotation, so the multisets agree, and
a concatenation of valid fillers is valid (`SkelsValid.append`). Hence the rows of any plan are
valid fillers over the padded image (`padSkels_valid`). The state channel of the bus balances for
the same reason: a traversal pulls what it pushes.

## Wrong readings excluded

* A traversal is not a path from the start to the closing slot: the `s + 1` states close on
  themselves, and that is the whole reason its state tuples cancel (`cycleSkels_valid`).
* Skeletons are not table rows: the closing jump of a block of table `t` is a `JUMP` skeleton, so
  the rows of one cycle spread over two tables (`Semantics.PaddedRows` counts them per table).
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-- The skeleton of a table row: the program counter and frame pointer it is stepped from, and the
instruction fetched there. -/
structure Skel where
  /-- The program counter of the state. -/
  pc : K
  /-- The frame pointer of the state. -/
  fp : K
  /-- The instruction fetched at `pc`. -/
  ins : Instr

/-- The state a skeleton is stepped from. -/
def Skel.regs (s : Skel) : Regs K := ⟨s.pc, s.fp⟩

/-- The skeletons of one traversal of the cycle `(t, k)`: the `s` dummies and the closing jump, in
the cycle's frame. The block of size `s` of table `t` starts at slot `pcs t s`. -/
def cycleSkels (κ : ℕ) (pcs : Opcode → ℕ → ℕ) (t : Opcode) (k : ℕ) : List Skel :=
  (List.range (sizeAt k + 1)).map fun i ↦
    ⟨gpow (pcs t (sizeAt k) + i), gpow (frameBase κ (8 * tableIdx t + k)),
      if i < sizeAt k then fillDummy t else fillClose⟩

/-- The skeletons of a fill: each cycle `(t, k)` traversed `count t k` times, table by table and
size by size. -/
def padSkels (κ : ℕ) (pcs : Opcode → ℕ → ℕ) (count : Opcode → ℕ → ℕ) : List Skel :=
  fillTables.flatMap fun t ↦ (List.range 8).flatMap fun k ↦
    (List.replicate (count t k) (cycleSkels κ pcs t k)).flatten

/-- The skeletons are valid fillers: their states are valid fillers in the sense of Layer 8. -/
def SkelsValid {κ : ℕ} (prog : Program) (image : MemImage κ) (l : List Skel) : Prop :=
  FillerRowsValid prog image (l.map Skel.regs)

/-! ## Valid fillers compose -/

/-- No skeletons are valid fillers. -/
theorem SkelsValid.nil {κ : ℕ} {prog : Program} {image : MemImage κ} :
    SkelsValid prog image [] :=
  ⟨by simp, by simp⟩

/-- Valid fillers concatenate: the starts and the successors both concatenate, and a permutation of
each part is a permutation of the whole. -/
theorem SkelsValid.append {κ : ℕ} {prog : Program} {image : MemImage κ} {a b : List Skel}
    (ha : SkelsValid prog image a) (hb : SkelsValid prog image b) :
    SkelsValid prog image (a ++ b) := by
  refine ⟨?_, ?_⟩
  · intro r hr
    rcases List.mem_append.mp (by simpa only [List.map_append] using hr) with h | h
    · exact ha.1 r h
    · exact hb.1 r h
  · simpa only [List.map_append] using ha.2.append hb.2

/-- A concatenation of valid fillers is valid. -/
theorem SkelsValid.flatten {κ : ℕ} {prog : Program} {image : MemImage κ} {L : List (List Skel)}
    (h : ∀ l ∈ L, SkelsValid prog image l) : SkelsValid prog image L.flatten := by
  induction L with
  | nil => exact SkelsValid.nil
  | cons l L ih =>
    rw [List.flatten_cons]
    exact (h l List.mem_cons_self).append (ih fun l' hl' ↦ h l' (List.mem_cons_of_mem _ hl'))

/-- Any number of copies of a valid filler is valid. -/
theorem SkelsValid.replicate {κ : ℕ} {prog : Program} {image : MemImage κ} {l : List Skel}
    (h : SkelsValid prog image l) (n : ℕ) :
    SkelsValid prog image (List.replicate n l).flatten :=
  SkelsValid.flatten fun l' hl' ↦ by rw [List.eq_of_mem_replicate hl']; exact h

/-- A family of valid fillers, concatenated over a list, is valid. -/
theorem SkelsValid.flatMap {κ : ℕ} {prog : Program} {image : MemImage κ} {α : Type}
    {f : α → List Skel} {l : List α} (h : ∀ a ∈ l, SkelsValid prog image (f a)) :
    SkelsValid prog image (l.flatMap f) := by
  rw [List.flatMap_def]
  exact SkelsValid.flatten fun x hx ↦ by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact h a ha

/-! ## A traversal is a rotation -/

/-- The cycle's states, by position: the `i`-th slot of the block, in the cycle's frame. -/
def cycleState (κ : ℕ) (pcs : Opcode → ℕ → ℕ) (t : Opcode) (k i : ℕ) : Regs K :=
  ⟨gpow (pcs t (sizeAt k) + i), gpow (frameBase κ (8 * tableIdx t + k))⟩

/-- The successor of position `i` is position `i + 1`, and the closing jump's is position `0`. -/
theorem cycleSkels_step {κ : ℕ} (hκ : 10 ≤ κ) (hκ' : κ < 63) (img : MemImage κ)
    (pcs : Opcode → ℕ → ℕ) (t : Opcode) {k : ℕ} (hk : k < 8) {prog : Program}
    (hb : IsFillBlock prog t (sizeAt k) (pcs t (sizeAt k))) {i : ℕ} (hi : i ≤ sizeAt k) :
    step prog (padImage img pcs) (cycleState κ pcs t k i) =
      some (cycleState κ pcs t k (if i < sizeAt k then i + 1 else 0)) := by
  by_cases h : i < sizeAt k
  · simp only [h, ↓reduceIte]
    have := fill_dummy_step hκ hκ' img pcs t hk (hb.dummies i h)
    unfold cycleState
    rw [this, ← gpow_succ]
    rfl
  · have hs : i = sizeAt k := by omega
    subst hs
    simp only [h, ↓reduceIte]
    exact fill_close_step hκ hκ' img pcs t hk hb.close

/-- Positions `1, ..., s, 0` are positions `0, ..., s` in another order: the successors of a
traversal's states are a rotation of its states. -/
theorem rotate_range_perm (s : ℕ) :
    ((List.range (s + 1)).map fun i ↦ if i < s then i + 1 else 0).Perm (List.range (s + 1)) := by
  have h1 : (List.range (s + 1)).map (fun i ↦ if i < s then i + 1 else 0) =
      (List.range s).map (· + 1) ++ [0] := by
    rw [List.range_succ, List.map_append]
    congr 1
    · exact List.map_congr_left fun i hi ↦ by simp [List.mem_range.mp hi]
    · simp
  rw [h1, List.range_succ_eq_map]
  exact List.perm_append_singleton _ _

/-- **A traversal is a valid filler.** The `s + 1` states of a traversal, stepped, are the same
states in a rotated order, and none is the sentinel. -/
theorem cycleSkels_valid {κ : ℕ} (hκ : 10 ≤ κ) (hκ' : κ < 63) (img : MemImage κ)
    (pcs : Opcode → ℕ → ℕ) (t : Opcode) {k : ℕ} (hk : k < 8) {prog : Program}
    (hb : IsFillBlock prog t (sizeAt k) (pcs t (sizeAt k))) :
    SkelsValid prog (padImage img pcs) (cycleSkels κ pcs t k) := by
  have hstarts : (cycleSkels κ pcs t k).map Skel.regs =
      (List.range (sizeAt k + 1)).map (cycleState κ pcs t k) := by
    simp only [cycleSkels, List.map_map]
    rfl
  refine ⟨?_, ?_⟩
  · intro r hr
    rw [hstarts] at hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have hi' := List.mem_range.mp hi
    have := hb.below
    exact gpow_ne_finalPc prog (n := pcs t (sizeAt k) + i) (by omega)
  · rw [hstarts]
    have hstep : ((List.range (sizeAt k + 1)).map (cycleState κ pcs t k)).map
        (step prog (padImage img pcs)) =
        ((List.range (sizeAt k + 1)).map fun i ↦ if i < sizeAt k then i + 1 else 0).map
          (fun j ↦ some (cycleState κ pcs t k j)) := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun i hi ↦
        cycleSkels_step hκ hκ' img pcs t hk hb (Nat.le_of_lt_succ (List.mem_range.mp hi))
    rw [hstep]
    have hp := (rotate_range_perm (sizeAt k)).map (fun j ↦ some (cycleState κ pcs t k j))
    simpa only [List.map_map, Function.comp_def] using hp.symm

/-- **The padding rows are valid fillers.** Whatever the traversal counts, the skeletons of a fill
are valid fillers over the padded image, given a block for every size: no padding row starts at the
sentinel and the multiset of its starts is the multiset of its successors. -/
theorem padSkels_valid {κ : ℕ} (hκ : 10 ≤ κ) (hκ' : κ < 63) (img : MemImage κ)
    (pcs : Opcode → ℕ → ℕ) {prog : Program}
    (hpcs : ∀ t, ∀ k < 8, IsFillBlock prog t (sizeAt k) (pcs t (sizeAt k)))
    (count : Opcode → ℕ → ℕ) : SkelsValid prog (padImage img pcs) (padSkels κ pcs count) :=
  SkelsValid.flatMap fun t _ ↦ SkelsValid.flatMap fun k hk ↦
    (cycleSkels_valid hκ hκ' img pcs t (List.mem_range.mp hk)
      (hpcs t k (List.mem_range.mp hk))).replicate _

/-- Well formed bytecode has a block of every size at some slot: the starting slots the padding
uses. -/
theorem HasFillBlocks.exists_starts {prog : Program} (h : HasFillBlocks prog) :
    ∃ pcs : Opcode → ℕ → ℕ, ∀ t, ∀ k < 8, IsFillBlock prog t (sizeAt k) (pcs t (sizeAt k)) := by
  classical
  refine ⟨fun t s ↦ if hs : s ∈ fillSizes then Classical.choose (h t s hs) else 0, ?_⟩
  intro t k hk
  have hs := sizeAt_mem hk
  simp only [hs, ↓reduceDIte]
  exact Classical.choose_spec (h t _ hs)

end
end LeanerVM.Semantics
