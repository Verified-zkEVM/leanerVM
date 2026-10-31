/-
  LeanVM.Guest.B1.Opening.QueriesPlacedL

  `opening_queries`' own words as layouts: its chain buffer, its queries' frame runs; an honest
  query from the memory holding them.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced10
public import LeanVM.Guest.Memory.Uniform

/-!
# The function's own words, as layouts

`oqChainVals`: the chain buffer's `N + 1` words `oqChain … i`. `oqRunCells`: a query's frame run's
first `4·pd` cells, its path's `pathCell`s. `qdOk_of_run`: a memory holding a query's frame run at
`g^c` and its weights, cap leaf and flag gives the honest query `QD.Ok` with the frame address
`g^c`. `disjL_flatMap_range`: blocks in consecutive windows are disjoint.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The chain buffer's words. -/
def oqChainVals (odd base : ℕ) (lam : E) (ds : ℕ → E) (N : ℕ) : List E :=
  (List.range (N + 1)).map (oqChain odd base lam⁻¹ ds)

/-- A query's frame run's first `4·pd` cells. -/
def oqRunCells (pd : ℕ) (row : List K) (q : ℕ) (sibs : List Digest) : List E :=
  (List.range (4 * pd)).map (pathCell (hashWords row) q sibs)

theorem pathCell_node (leaf : Digest) (q : ℕ) (sibs : List Digest) (l e : ℕ) (he : e < 2) :
    pathCell leaf q sibs (4 * l + (if q.testBit l then 2 else 0) + e) =
      if e = 0 then (digestScalars (climbNode leaf q sibs l)).1
      else (digestScalars (climbNode leaf q sibs l)).2 := by
  have h1 : (4 * l + (if q.testBit l then 2 else 0) + e) / 4 = l := by split <;> omega
  have h2 : (4 * l + (if q.testBit l then 2 else 0) + e) % 4 / 2 =
      (if q.testBit l then 1 else 0) := by split <;> omega
  have h3 : (4 * l + (if q.testBit l then 2 else 0) + e) % 2 = e := by split <;> omega
  unfold pathCell
  rw [h1, h2, h3]
  interval_cases e <;> simp

/-- **An honest query from the memory holding its frame run.** -/
theorem qdOk_of_run {rd : Reader} {s : Oq} {b : ℕ} {emit : Bool} {pr : ℕ} {row : List K}
    {w : ℕ → E} {q : ℕ} {sibs : List Digest} {c : ℕ} {cap flags wp : E}
    (hrow : row.length = s.R) (hsl : sibs.length = s.pd) (hq : q < 2 ^ (s.pd + s.cd))
    (hrun : ReadsAt rd (ofK (Parameters.gpow c)) (oqRunCells s.pd row q sibs))
    (hw : ∀ l < s.lo + s.I / s.lo, LoadHolds rd wp l (w l))
    (hc0 : LoadHolds rd cap (2 * (2 ^ s.cd + q / 2 ^ s.pd))
      (digestScalars (climbD (hashWords row) q sibs)).1)
    (hc1 : LoadHolds rd cap (2 * (2 ^ s.cd + q / 2 ^ s.pd) + 1)
      (digestScalars (climbD (hashWords row) q sibs)).2)
    (hfl : LoadHolds rd flags (2 ^ (s.cd - 1) + q / 2 ^ (s.pd + 1)) 1) :
    (⟨s, b, emit, pr, row, w, q, sibs, ofK (Parameters.gpow c), cap, flags, rd⟩ : QD).Ok rd wp := by
  have hlen : (oqRunCells s.pd row q sibs).length = 4 * s.pd := by simp [oqRunCells]
  refine ⟨hsl, hrow, ⟨ofK_isInK _, fun k hk x hx ↦ ?_, fun l hl ↦ ?_, hc0, hc1, hfl⟩, rfl, hw, hq⟩
  · have := (hrun k (by rw [hlen]; exact hk)).2
    rw [hx] at this
    have e := Option.some.inj this
    simp only [oqRunCells, List.getElem_map, List.getElem_range] at e
    exact e
  · have hl' : l < s.pd := hl
    have hcell : ∀ e < 2, LoadHolds rd (ofK (Parameters.gpow c) *
        gen ^ (if q.testBit l then 2 else 0)) (4 * l + e)
        ((oqRunCells s.pd row q sibs).getD (4 * l + (if q.testBit l then 2 else 0) + e) 0) := by
      intro e he
      rw [loadHolds_mul_gen_pow, show (if q.testBit l then 2 else 0) + (4 * l + e) =
        4 * l + (if q.testBit l then 2 else 0) + e by ring,
        List.getD_eq_getElem _ _ (by rw [hlen]; split <;> omega)]
      exact hrun _ (by rw [hlen]; split <;> omega)
    have h0 := hcell 0 (by omega)
    have h1 := hcell 1 (by omega)
    simp only [oqRunCells, Nat.add_zero] at h0 h1
    rw [List.getD_eq_getElem _ _ (by simp; split <;> omega)] at h0 h1
    simp only [List.getElem_map, List.getElem_range] at h0 h1
    have p0 := pathCell_node (hashWords row) q sibs l 0 (by omega)
    have p1 := pathCell_node (hashWords row) q sibs l 1 (by omega)
    simp only [Nat.add_zero, ↓reduceIte, one_ne_zero] at p0 p1
    rw [p0] at h0
    rw [p1] at h1
    exact ⟨h0, h1⟩

/-- **Blocks in consecutive windows**: a layout of `N` blocks, block `j` within
`[b + j·S, b + (j + 1)·S)` and disjoint, is disjoint and within `[b, b + N·S)`. -/
theorem disjL_flatMap_range (b S : ℕ) (f : ℕ → Main.Layout) (hw : ∀ j, Within (f j) (b + j * S) S)
    (hd : ∀ j, DisjL (f j)) :
    ∀ N, DisjL ((List.range N).flatMap f) ∧ Within ((List.range N).flatMap f) b (N * S)
  | 0 => by simp [disj_nil, Within]
  | N + 1 => by
    obtain ⟨ih1, ih2⟩ := disjL_flatMap_range b S f hw hd N
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine ⟨disj_append ih1 (hd N) ih2 (hw N) le_rfl, fun q hq ↦ ?_⟩
    rcases List.mem_append.mp hq with hq | hq
    · have := ih2 q hq; constructor <;> nlinarith [this.1, this.2]
    · have := hw N q hq; constructor <;> nlinarith [this.1, this.2]

end
end LeanVM.Guest.B1
