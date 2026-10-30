/-
  LeanVM.Guest.B1.Gkr.Loop7C

  `__loop6`, completely: on a memory holding a layer's slot, its step's words, its round records
  and the next slot, an iteration's honest valuation satisfies its body; the iterations chain to
  the loop's relation.
-/

module

public import LeanVM.Guest.B1.Gkr.LayerStep
public import LeanVM.Guest.B1.Gkr.EvalC
public import LeanVM.Guest.B1.Gkr.RecsC
public import LeanVM.Guest.B1.Gkr.SpecInv
public import LeanVM.Guest.B1.Gkr.Loop29Complete
public import LeanVM.Guest.B1.Sumcheck.Gkr

/-!
# `__loop6`, completely (G:1682-1770)

An iteration at `x = g^j` from the slot of `L = 2j + sh` (`GkSlotC`, the slot's words exactly)
runs one step of two levels (`GkStepD`, read back from the walk by `gkrStep_inv`). On a memory
holding the slot, the step's words at the cursor, the round records (`RecsAt`) and the next slot,
the body evaluated forward (`lyEvL`, its `ite`s' branches in order) holds: `ly_iter`. The
regions of the body (`lyR1 .. lyR6`):

* `lyc_head`: the combiner's permutation, the first record stored, `half` and `parity`;
* `lyc_rounds`: `__loop27`, `gkr_rounds__L2` at an odd `j`, `gkr_rounds__L1` at an odd depth;
* `lyc_last`: the last record read;
* `lyc_children`: the twelve children read and absorbed;
* `lyc_check`: their check and the two new coordinates;
* `lyc_stores`: the next slot stored and the next iteration called.

`ly_complete`: iterations at every `g^j`, `j < m`, give `__loop6` from `1` below `g^m`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The slot, completely -/

/-- **The slot of point length `L`, completely**: the sponge's capacity and rate cells (at most
two scalars waiting), the cursor, the values, the row holding the point, the position, `half` and
`parity`. -/
def GkSlotC (rd : Reader) (layers : E) (L : ℕ) (s : Fs) (cur : E) (st : GkrState)
    (row pos half parity : E) : Prop :=
  s.cap.length = 5 ∧ AllCanonical s.cap ∧ s.pend.length ≤ 2 ∧
    (∀ k < 5, LoadHolds rd layers (17 * L + k) (s.cap.getD k 0)) ∧
    (∀ k < 4, LoadHolds rd layers (17 * L + 13 + k) ((rateOf s.pend).getD k 0)) ∧
    LoadHolds rd layers (17 * L + 5) cur ∧ st.values.length = 3 ∧
    (∀ t < 3, LoadHolds rd layers (17 * L + 6 + t) (st.values.getD t 0)) ∧
    LoadHolds rd layers (17 * L + 9) row ∧ st.point.length = L ∧ TbReadsAt rd row st.point ∧
    LoadHolds rd layers (17 * L + 10) pos ∧ LoadHolds rd layers (17 * L + 11) half ∧
    LoadHolds rd layers (17 * L + 12) parity

theorem tb_zero_canonical : IsCanonical128 (0 : E) := by
  rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

/-- The rate cells of at most four scalars are canonical. -/
theorem rateOf_canonical {pend : List (E × ℕ)} (h : pend.length ≤ 4) : AllCanonical (rateOf pend) := by
  rw [rateOf_eq_cells _ h]
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨p, -, hp⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (scalarCells_canonical _ _).1
    · exact (scalarCells_canonical _ _).2
  · rw [List.eq_of_mem_replicate hc]; exact tb_zero_canonical

theorem capOf_getD (S : KeccakState) {k : ℕ} (hk : k < 5) :
    (capOf S).getD k 0 = cellsOfState S false ⟨8 + k, by omega⟩ := by
  interval_cases k <;> rfl

theorem tbCapAt_getD {rd : Reader} {rec : E} {off stride : ℕ} {cap : List E}
    (h : TbCapAt rd rec off stride cap) {k : ℕ} (hk : k < 5) :
    LoadHolds rd rec (off + k * stride) (cap.getD k 0) := by
  have := h.2 k (by rw [h.1]; exact hk)
  rwa [List.getD_eq_getElem _ _ (by rw [h.1]; exact hk)]

/-! ## The evaluation list -/

/-- `__loop6`'s evaluation list: its body, each `ite`'s branches in order. -/
def lyEvL : List Stmt := flatIte lyPre

theorem ly_chk : (chk 6 lyEvL).isSome = true := by decide +kernel

/-- `__loop6`'s stores. -/
def lyS : List Atom := storesOf 6 lyEvL

/-- **The regions of the body.** The head: the combiner, the first record, `half`, `parity`. -/
def lyR1 : List Stmt :=
  [.atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 2) (.n 3)),
    .atom (.load (.n 8) (.n 7) 0), .atom (.mul (.n 9) (.n 6) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.mul (.n 12) (.n 11) (.n 11)), .atom (.mul (.n 13) (.n 12) (.n 12)),
    .atom (.mul (.n 14) (.n 13) (.n 9)), .atom (.mul (.n 15) (.n 4) (.n 14))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (16 + k)) (.n 15) k)) ++
  (List.range 4).map (fun k ↦ .atom (.load (.n (21 + k)) (.n 15) (13 + k))) ++
  [.atom (.const (.n 25) (word 1 0 0)), .atom (.const (.n 26) (word 0 0 0)),
    .atom (.const (.n 27) (word 0 0 0)), .atom (.const (.n 28) (word 0 0 0)),
    .atom (.const (.n 29) (word 0 0 0)),
    keccakA ([.n 21, .n 22, .n 23, .n 24, .n 26, .n 27, .n 28, .n 29] ++
      (List.range 5).map fun k ↦ .n (16 + k)) (lyOuts 30)] ++
  challengeT (.n 30) (.n 31) 43 ++
  [.atom (.load (.n 50) (.n 15) 9), .atom (.load (.n 51) (.n 15) 10),
    .atom (.mul (.n 52) (.n 5) (.n 51))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (38 + k)) (.n 52) (862 * k))) ++
  [.atom (.load (.n 53) (.n 15) 5), .atom (.load (.n 53) (.n 52) 4310),
    .atom (.load (.n 54) (.n 15) 6), .atom (.load (.n 55) (.n 15) 7),
    .atom (.load (.n 56) (.n 15) 8), .atom (.mul (.n 57) (.n 49) (.n 56)),
    .atom (.add (.n 58) (.n 55) (.n 57)), .atom (.mul (.n 59) (.n 49) (.n 58)),
    .atom (.add (.n 60) (.n 54) (.n 59)), .atom (.load (.n 60) (.n 52) 5172),
    .atom (.load (.n 61) (.n 15) 11), .atom (.load (.n 62) (.n 15) 12),
    .atom (.const (.n 63) (word 1 0 0)), .atom (.add (.n 64) (.n 63) (.n 61)),
    .atom (.const (.n 65) (word 1 0 0))]

/-- The rounds. -/
def lyR2 : List Stmt :=
  [.callIf (.n 64) "__loop27" [.n 65, .n 61, .n 52, .n 50],
    .ite (.n 62) [] [.atom (.mul (.n 66) (.n 61) (.n 61)), .atom (.mul (.n 67) (.n 66) (.n 66)),
      .atom (.mul (.n 68) (.n 52) (.n 67)), .atom (.mul (.n 69) (.n 50) (.n 67)),
      .call "gkr_rounds__L2" [.n 68, .n 69] []],
    .atom (.add (.n 70) (.n 9) (.n 6)),
    .ite (.n 70) [] [.atom (.mul (.n 71) (.n 52) (.n 6)), .atom (.mul (.n 72) (.n 50) (.n 6)),
      .call "gkr_rounds__L1" [.n 71, .n 72] []]]

/-- The last record. -/
def lyR3 : List Stmt :=
  [.atom (.mul (.n 73) (.n 52) (.n 9))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (74 + k)) (.n 73) (862 * k))) ++
  [.atom (.load (.n 79) (.n 73) 4310), .atom (.load (.n 80) (.n 73) 5172)]

/-- The children. -/
def lyR4 : List Stmt :=
  ((List.range 4).map lyEvT).flatten ++
  [keccakA (lyRate 0 ++ (List.range 5).map fun k ↦ .n (74 + k)) (lyOuts 125)] ++
  ((List.range 4).map fun i ↦ lyEvT (4 + i)).flatten ++
  [keccakA (lyRate 1 ++ lyCap 125) (lyOuts 182)] ++
  ((List.range 4).map fun i ↦ lyEvT (8 + i)).flatten

/-- The check and the new coordinates. -/
def lyR5 : List Stmt :=
  [.atom (.mul (.n 239) (.n 205) (.n 216)), .atom (.mul (.n 240) (.n 239) (.n 227)),
    .atom (.mul (.n 241) (.n 240) (.n 238)), .atom (.const (.n 242) (word 0 0 0)),
    .atom (.mul (.n 243) (.n 49) (.n 242)), .atom (.add (.n 244) (.n 241) (.n 243)),
    .atom (.mul (.n 245) (.n 148) (.n 159)), .atom (.mul (.n 246) (.n 245) (.n 170)),
    .atom (.mul (.n 247) (.n 246) (.n 181)), .atom (.mul (.n 248) (.n 49) (.n 244)),
    .atom (.add (.n 249) (.n 247) (.n 248)), .atom (.mul (.n 250) (.n 91) (.n 102)),
    .atom (.mul (.n 251) (.n 250) (.n 113)), .atom (.mul (.n 252) (.n 251) (.n 124)),
    .atom (.mul (.n 253) (.n 49) (.n 249)), .atom (.add (.n 254) (.n 252) (.n 253)),
    .atom (.assertEq (.n 80) (.n 254)),
    keccakA (lyRate 2 ++ lyCap 182) (lyOuts 255)] ++
  challengeT (.n 255) (.n 256) 268 ++
  [keccakA ([.n 26, .n 26, .n 26, .n 26, .n 26, .n 27, .n 28, .n 29] ++ lyCap 255) (lyOuts 275)] ++
  challengeT (.n 275) (.n 276) 288

/-- The next slot and the next iteration. -/
def lyR6 : List Stmt :=
  [.atom (.load (.n 274) (.n 50) 40), .atom (.load (.n 294) (.n 50) 41)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (283 + k)) (.n 15) (34 + k))) ++
  ((List.range 4).map fun k ↦ [.atom (.const (.n (295 + k)) (word 0 0 0)),
    .atom (.load (.n (295 + k)) (.n 15) (47 + k))]).flatten ++
  [.atom (.const (.n 299) (word 4096 0 0)), .atom (.mul (.n 300) (.n 79) (.n 299)),
    .atom (.load (.n 300) (.n 15) 39)] ++
  lyVal 0 301 40 ++ lyVal 1 310 41 ++ lyVal 2 319 42 ++
  [.atom (.const (.n 328) (word 1099511627776 0 0)), .atom (.mul (.n 329) (.n 50) (.n 328)),
    .atom (.load (.n 329) (.n 15) 43), .atom (.mul (.n 330) (.n 51) (.n 9)),
    .atom (.const (.n 331) (word 2 0 0)), .atom (.mul (.n 332) (.n 330) (.n 331)),
    .atom (.load (.n 332) (.n 15) 44), .atom (.const (.n 333) (word 1 0 0)),
    .atom (.const (.n 334) (word 3 0 0)), .atom (.mul (.n 335) (.n 62) (.n 334)),
    .atom (.add (.n 336) (.n 333) (.n 335)), .atom (.mul (.n 337) (.n 61) (.n 336)),
    .atom (.load (.n 337) (.n 15) 45), .atom (.const (.n 338) (word 1 0 0)),
    .atom (.add (.n 339) (.n 338) (.n 62)), .atom (.load (.n 339) (.n 15) 46),
    .atom (.const (.n 340) (word 2 0 0)), .atom (.mul (.n 341) (.n 0) (.n 340)),
    .atom (.add (.n 342) (.n 341) (.n 1)), .atom (.const (.n 343) (word 2 0 0)),
    .atom (.mul (.n 344) (.n 0) (.n 343)),
    .callIf (.n 342) "__loop6" [.n 344, .n 1, .n 2, .n 3, .n 4, .n 5]]

theorem lyPre_eq : lyPre = lyR1 ++ lyR2 ++ lyR3 ++ lyR4 ++ lyR5 ++ lyR6 :=
  tbStmtsEqb_sound (by decide +kernel)

section Eval

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- An atom of the body satisfies its equations. -/
theorem ly_good (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((lyPre.drop n).take 1) = true) :
    Good rd lyS (fun _ => 0) σ a :=
  good_slice hG n [.atom a] heq rfl _ List.mem_cons_self

/-- A permutation's thirteen outputs from `b`, and its capacity cells, on its equations. -/
theorem lyc_keccak {S : List Atom} {w : ℕ → E} {ins : List V} {b : ℕ}
    (hg : Good rd S w σ (.keccak ins (lyOuts b) false false))
    (hc : AllCanonical (ins.map σ)) :
    (Atom.keccak ins (lyOuts b) false false).Holds rd σ ∧
      (∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = capOf (permOf (ins.map σ)) := by
  obtain ⟨hk, hout⟩ := keccak_good hg hc
  have hP : ∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩ := by
    intro k hk
    have := outs_eq hout ⟨k, hk⟩ (by simpa [lyOuts] using hk)
    simpa [lyOuts] using this
  refine ⟨hk, hP, ?_⟩
  simp only [lyCap, capOf, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rw [hP (8 + 0) (by omega), hP (8 + 1) (by omega), hP (8 + 2) (by omega), hP (8 + 3) (by omega),
    hP (8 + 4) (by omega)]
  rfl

/-- **The head**: the combiner's permutation over the slot's sponge, the first record stored
(its capacity, cursor and combined claim), `half` and `parity`. -/
theorem lyc_head (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {j sh : ℕ}
    (hx : σ (.n 0) = gen ^ j) (hsh : LoadHolds rd (σ (.n 2) * σ (.n 3)) 0 (gen ^ sh)) {s : Fs}
    {cur : E} {st : GkrState} {row pos half parity : E}
    (hS : GkSlotC rd (σ (.n 4)) (2 * j + sh) s cur st row pos half parity)
    (hc0 : TbCapAt rd (σ (.n 5) * pos) 0 gkCap s.squeeze.2.cap)
    (hu0 : LoadHolds rd (σ (.n 5) * pos) (5 * gkCap) cur)
    (hl0 : LoadHolds rd (σ (.n 5) * pos) (6 * gkCap) (polyEval st.values s.squeeze.1)) :
    Stmt.HoldsList C rd σ lyR1 True kret ∧ σ (.n 6) = gen ^ (2 * j) ∧
      σ (.n 9) = gen ^ (2 * j + sh) ∧ σ (.n 15) = σ (.n 4) * gen ^ (17 * (2 * j + sh)) ∧
      σ (.n 49) = s.squeeze.1 ∧ σ (.n 50) = row ∧ σ (.n 51) = pos ∧
      σ (.n 52) = σ (.n 5) * pos ∧ σ (.n 61) = half ∧ σ (.n 62) = parity ∧
      σ (.n 64) = 1 + half ∧ σ (.n 65) = 1 ∧ σ (.n 26) = 0 ∧ σ (.n 27) = 0 ∧
      σ (.n 28) = 0 ∧ σ (.n 29) = 0 := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  obtain ⟨hcl, hcan, hpl, hcap, hrate, hcur, hvl, hval, hrow, -, -, hpos, hhalf, hpar⟩ := hS
  set L := 2 * j + sh with hL
  have m6 := good_mul (g 0 (.mul (.n 6) (.n 0) (.n 0)) (by decide +kernel)) (by omega) (by omega)
  have m7 := good_mul (g 1 (.mul (.n 7) (.n 2) (.n 3)) (by decide +kernel)) (by omega) (by omega)
  rw [← m7] at hsh
  obtain ⟨e8, l8⟩ := good_read (g 2 (.load (.n 8) (.n 7) 0) (by decide +kernel))
    (by decide +kernel) hsh
  have m9 := good_mul (g 3 (.mul (.n 9) (.n 6) (.n 8)) (by decide +kernel)) (by omega) (by omega)
  have m10 := good_mul (g 4 (.mul (.n 10) (.n 9) (.n 9)) (by decide +kernel)) (by omega) (by omega)
  have m11 := good_mul (g 5 (.mul (.n 11) (.n 10) (.n 10)) (by decide +kernel)) (by omega)
    (by omega)
  have m12 := good_mul (g 6 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel)) (by omega)
    (by omega)
  have m13 := good_mul (g 7 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel)) (by omega)
    (by omega)
  have m14 := good_mul (g 8 (.mul (.n 14) (.n 13) (.n 9)) (by decide +kernel)) (by omega) (by omega)
  have m15 := good_mul (g 9 (.mul (.n 15) (.n 4) (.n 14)) (by decide +kernel)) (by omega) (by omega)
  have e6 : σ (.n 6) = gen ^ (2 * j) := by rw [m6, hx, ← pow_add]; ring_nf
  have e9 : σ (.n 9) = gen ^ L := by rw [m9, e6, e8, ← pow_add]
  have e15 : σ (.n 15) = σ (.n 4) * gen ^ (17 * L) := by
    rw [m15, m14, m13, m12, m11, m10, e9, ← pow_add, ← pow_add, ← pow_add, ← pow_add]; ring_nf
  have ld : ∀ k w, LoadHolds rd (σ (.n 15)) k w ↔ LoadHolds rd (σ (.n 4)) (17 * L + k) w := by
    intro k w; rw [e15, tb_loadHolds_mul_gen_pow]
  -- the slot's capacity and waiting cells
  have gcap := good_slice hG 10 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (16 + k)) (.n 15) k)) (by decide +kernel) (by decide +kernel)
  have kcap : ∀ k < 5, some (16 + k, 15, k) ∉ lyS.map loadKey := by decide +kernel
  have rcap : ∀ k < 5, σ (.n (16 + k)) = s.cap.getD k 0 ∧
      LoadHolds rd (σ (.n 15)) k (σ (.n (16 + k))) := fun k hk =>
    good_readS (gcap _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (kcap k hk)
      ((ld k _).mpr (hcap k hk))
  have grate := good_slice hG 15 ((List.range 4).map fun k ↦
    Stmt.atom (.load (.n (21 + k)) (.n 15) (13 + k))) (by decide +kernel) (by decide +kernel)
  have krate : ∀ k < 4, some (21 + k, 15, 13 + k) ∉ lyS.map loadKey := by decide +kernel
  have rrate : ∀ k < 4, σ (.n (21 + k)) = (rateOf s.pend).getD k 0 ∧
      LoadHolds rd (σ (.n 15)) (13 + k) (σ (.n (21 + k))) := fun k hk =>
    good_readS (grate _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (krate k hk)
      ((ld _ _).mpr (by rw [← Nat.add_assoc]; exact hrate k hk))
  have c25 : σ (.n 25) = word 1 0 0 := g 19 (.const (.n 25) (word 1 0 0)) (by decide +kernel)
  have c26 : σ (.n 26) = word 0 0 0 := g 20 (.const (.n 26) (word 0 0 0)) (by decide +kernel)
  have c27 : σ (.n 27) = word 0 0 0 := g 21 (.const (.n 27) (word 0 0 0)) (by decide +kernel)
  have c28 : σ (.n 28) = word 0 0 0 := g 22 (.const (.n 28) (word 0 0 0)) (by decide +kernel)
  have c29 : σ (.n 29) = word 0 0 0 := g 23 (.const (.n 29) (word 0 0 0)) (by decide +kernel)
  rw [tb_word_zero] at c26 c27 c28 c29
  -- the combiner's permutation
  have hrl : (rateOf s.pend).length = 8 := by simp [rateOf]
  have hins : (([.n 21, .n 22, .n 23, .n 24, .n 26, .n 27, .n 28, .n 29] ++
      (List.range 5).map fun k ↦ V.n (16 + k)) : List V).map σ = rateOf s.pend ++ s.cap := by
    rw [tb_eq_map_getD hrl, tb_eq_map_getD hcl]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.cons.injEq, and_true]
    refine ⟨(rrate 0 (by omega)).1, (rrate 1 (by omega)).1, (rrate 2 (by omega)).1,
      (rrate 3 (by omega)).1, ?_, ?_, ?_, ?_, (rcap 0 (by omega)).1, (rcap 1 (by omega)).1,
      (rcap 2 (by omega)).1, (rcap 3 (by omega)).1, (rcap 4 (by omega)).1⟩
    · rw [c26, rateOf_getD_four (by omega) (by omega) (by omega)]
    · rw [c27, rateOf_getD_four (by omega) (by omega) (by omega)]
    · rw [c28, rateOf_getD_four (by omega) (by omega) (by omega)]
    · rw [c29, rateOf_getD_four (by omega) (by omega) (by omega)]
  have hcanI : AllCanonical (rateOf s.pend ++ s.cap) := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact rateOf_canonical (by omega) c hc
    · exact hcan c hc
  obtain ⟨k24, hP, -⟩ := lyc_keccak (g 24 (.keccak ([.n 21, .n 22, .n 23, .n 24, .n 26, .n 27,
    .n 28, .n 29] ++ (List.range 5).map fun k ↦ .n (16 + k)) (lyOuts 30) false false)
    (by decide +kernel)) (by rw [hins]; exact hcanI)
  rw [hins] at hP
  -- the combiner
  have hco := challengeT_good (good_slice hG 25 (challengeT (.n 30) (.n 31) 43) (by decide +kernel)
    (by decide +kernel)) (by rw [hP 1 (by omega)]; exact cellsOfState_canonical _ _ _)
  have e49 : σ (.n 49) = s.squeeze.1 :=
    challengeT_value hco (hP 0 (by omega)) (hP 1 (by omega))
  -- the row, the position, the first record
  obtain ⟨e50, l50⟩ := good_read (g 33 (.load (.n 50) (.n 15) 9) (by decide +kernel))
    (by decide +kernel) ((ld 9 _).mpr hrow)
  obtain ⟨e51, l51⟩ := good_read (g 34 (.load (.n 51) (.n 15) 10) (by decide +kernel))
    (by decide +kernel) ((ld 10 _).mpr hpos)
  have m52 := good_mul (g 35 (.mul (.n 52) (.n 5) (.n 51)) (by decide +kernel)) (by omega)
    (by omega)
  rw [e51] at m52
  have s38 : ∀ k < 5, LoadHolds rd (σ (.n 52)) (862 * k) (σ (.n (38 + k))) := by
    intro k hk
    have := tbCapAt_getD hc0 hk
    rw [show 0 + k * gkCap = 862 * k by unfold gkCap; ring] at this
    rw [m52, show 38 + k = 30 + (8 + k) by omega, hP (8 + k) (by omega)]
    rwa [Fs.squeeze, capOf_getD _ hk] at this
  obtain ⟨e53, l53⟩ := good_read (g 41 (.load (.n 53) (.n 15) 5) (by decide +kernel))
    (by decide +kernel) ((ld 5 _).mpr hcur)
  have s53 : LoadHolds rd (σ (.n 52)) 4310 (σ (.n 53)) := by rw [m52, e53]; exact hu0
  obtain ⟨e54, l54⟩ := good_read (g 43 (.load (.n 54) (.n 15) 6) (by decide +kernel))
    (by decide +kernel) ((ld 6 _).mpr (hval 0 (by omega)))
  obtain ⟨e55, l55⟩ := good_read (g 44 (.load (.n 55) (.n 15) 7) (by decide +kernel))
    (by decide +kernel) ((ld 7 _).mpr (hval 1 (by omega)))
  obtain ⟨e56, l56⟩ := good_read (g 45 (.load (.n 56) (.n 15) 8) (by decide +kernel))
    (by decide +kernel) ((ld 8 _).mpr (hval 2 (by omega)))
  have m57 := good_mul (g 46 (.mul (.n 57) (.n 49) (.n 56)) (by decide +kernel)) (by omega)
    (by omega)
  have a58 : σ (.n 58) = σ (.n 55) + σ (.n 57) := g 47 (.add (.n 58) (.n 55) (.n 57))
    (by decide +kernel)
  have m59 := good_mul (g 48 (.mul (.n 59) (.n 49) (.n 58)) (by decide +kernel)) (by omega)
    (by omega)
  have a60 : σ (.n 60) = σ (.n 54) + σ (.n 59) := g 49 (.add (.n 60) (.n 54) (.n 59))
    (by decide +kernel)
  have e60 : σ (.n 60) = polyEval st.values s.squeeze.1 := by
    obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
      match st.values, hvl with
      | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
    rw [a60, m59, a58, m57, e54, e55, e56, e49, hv3]
    simp only [polyEval, List.foldr, List.getD_cons_zero, List.getD_cons_succ]
    ring
  have s60 : LoadHolds rd (σ (.n 52)) 5172 (σ (.n 60)) := by rw [m52, e60]; exact hl0
  obtain ⟨e61, l61⟩ := good_read (g 51 (.load (.n 61) (.n 15) 11) (by decide +kernel))
    (by decide +kernel) ((ld 11 _).mpr hhalf)
  obtain ⟨e62, l62⟩ := good_read (g 52 (.load (.n 62) (.n 15) 12) (by decide +kernel))
    (by decide +kernel) ((ld 12 _).mpr hpar)
  have c63 : σ (.n 63) = word 1 0 0 := g 53 (.const (.n 63) (word 1 0 0)) (by decide +kernel)
  have a64 : σ (.n 64) = σ (.n 63) + σ (.n 61) := g 54 (.add (.n 64) (.n 63) (.n 61))
    (by decide +kernel)
  have c65 : σ (.n 65) = word 1 0 0 := g 55 (.const (.n 65) (word 1 0 0)) (by decide +kernel)
  rw [tb_word_one] at c63 c65
  refine ⟨?_, e6, e9, e15, e49, e50, e51, m52, e61, e62, by rw [a64, c63, e61], c65, c26, c27,
    c28, c29⟩
  -- the region holds
  unfold lyR1
  repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨m6, m7, l8, m9, m10, m11, m12, m13, m14, m15⟩
  · exact (tb_holdsList_mapAtoms 5 _).mpr fun k hk => (rcap k hk).2
  · exact (tb_holdsList_mapAtoms 4 _).mpr fun k hk => (rrate k hk).2
  · simp only [keccakA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨c25, by rw [c26, tb_word_zero], by rw [c27, tb_word_zero], by rw [c28, tb_word_zero],
      by rw [c29, tb_word_zero], k24⟩
  · exact (holds_challengeT _ _ _ _ _).mpr ⟨hco, trivial⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨l50, l51, by rw [m52, e51]⟩
  · exact (tb_holdsList_mapAtoms 5 _).mpr fun k hk => s38 k hk
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨l53, s53, l54, l55, l56, m57, a58, m59, a60, s60, l61, l62, by rw [c63, tb_word_one],
      a64, by rw [c65, tb_word_one]⟩

theorem tb_isInK_one : IsInK (1 : E) := by simpa using tb_gen_pow_isInK 0

theorem tb_bitE_isInK (b : Bool) : IsInK (bitE b) := by
  cases b
  · have := tb_isInK_add tb_isInK_one tb_isInK_one
    rwa [e_add_self] at this
  · exact tb_isInK_one

/-- **The rounds**: `__loop27` (`4·(j/2)` rounds), `gkr_rounds__L2` at an odd `j`, and
`gkr_rounds__L1` at an odd depth, each from its record, when the records hold every run of
consecutive rounds. -/
theorem lyc_rounds (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {j sh : ℕ}
    (hj : j < 2 ^ 30) (hsh2 : sh < 2)
    (e6 : σ (.n 6) = gen ^ (2 * j)) (e9 : σ (.n 9) = gen ^ (2 * j + sh))
    (e61 : σ (.n 61) = gen ^ (j / 2)) (e62 : σ (.n 62) = bitE (j % 2 = 1))
    (e64 : σ (.n 64) = 1 + gen ^ (j / 2)) (e65 : σ (.n 65) = 1)
    (hT : ∀ a k, a + k ≤ 2 * j + sh →
      TbGkrRoundsOut k rd (σ (.n 52) * gen ^ a) (σ (.n 50) * gen ^ a)) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ lyR2 True kret := by
  refine holdsList_of_vsh lyR2 (by decide +kernel) (fun s hs => ?_) trivial
  simp only [lyR2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · -- `__loop27`
    refine ⟨by rw [e64]; exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _), fun hne => ?_⟩
    have hpos : 0 < j / 2 := by
      rcases Nat.eq_zero_or_pos (j / 2) with h0 | h0
      · rw [e64, h0, pow_zero, e_add_self] at hne; exact absurd rfl hne
      · exact h0
    simp only [List.map_cons, List.map_nil, e65, e61]
    exact l29_complete hpos (by omega) fun i hi => hT (4 * i) 4 (by omega)
  · -- `gkr_rounds__L2` at an odd `j`
    have gb := good_ite hG 57 (.n 62) [] [.atom (.mul (.n 66) (.n 61) (.n 61)),
      .atom (.mul (.n 67) (.n 66) (.n 66)), .atom (.mul (.n 68) (.n 52) (.n 67)),
      .atom (.mul (.n 69) (.n 50) (.n 67)), .call "gkr_rounds__L2" [.n 68, .n 69] []]
      (by decide +kernel)
    refine ⟨by rw [e62]; exact tb_bitE_isInK _, fun _ s hs => absurd hs (by simp), fun hne s hs => ?_⟩
    have hodd : j % 2 = 1 := by
      by_contra h
      rw [e62] at hne
      exact hne (by simp [bitE, h])
    have m66 := good_mulS (gb (.atom (.mul (.n 66) (.n 61) (.n 61))) (by simp)) (by omega) (by omega)
    have m67 := good_mulS (gb (.atom (.mul (.n 67) (.n 66) (.n 66))) (by simp)) (by omega) (by omega)
    have m68 := good_mulS (gb (.atom (.mul (.n 68) (.n 52) (.n 67))) (by simp)) (by omega) (by omega)
    have m69 := good_mulS (gb (.atom (.mul (.n 69) (.n 50) (.n 67))) (by simp)) (by omega) (by omega)
    have e67 : σ (.n 67) = gen ^ (4 * (j / 2)) := by
      rw [m67, m66, e61, ← pow_add, ← pow_add]; ring_nf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact m66
    · exact m67
    · exact m68
    · exact m69
    · show coreProgram.Rel rd "gkr_rounds__L2" [σ (.n 68), σ (.n 69)] []
      rw [m68, m69, e67]
      exact (gkr_rounds_holds.2 rd _ _).mpr ⟨rfl, hT (4 * (j / 2)) 2 (by omega)⟩
  · exact ly_good hG 58 (.add (.n 70) (.n 9) (.n 6)) (by decide +kernel)
  · -- `gkr_rounds__L1` at an odd depth
    have gb := good_ite hG 59 (.n 70) [] [.atom (.mul (.n 71) (.n 52) (.n 6)),
      .atom (.mul (.n 72) (.n 50) (.n 6)), .call "gkr_rounds__L1" [.n 71, .n 72] []]
      (by decide +kernel)
    have a70 : σ (.n 70) = σ (.n 9) + σ (.n 6) :=
      ly_good hG 58 (.add (.n 70) (.n 9) (.n 6)) (by decide +kernel)
    refine ⟨by rw [a70, e9, e6]; exact tb_isInK_add (tb_gen_pow_isInK _) (tb_gen_pow_isInK _),
      fun _ s hs => absurd hs (by simp), fun hne s hs => ?_⟩
    have hsh1 : sh = 1 := by
      by_contra h
      rw [a70, e9, e6, show sh = 0 by omega, Nat.add_zero, e_add_self] at hne
      exact hne rfl
    have m71 := good_mulS (gb (.atom (.mul (.n 71) (.n 52) (.n 6))) (by simp)) (by omega) (by omega)
    have m72 := good_mulS (gb (.atom (.mul (.n 72) (.n 50) (.n 6))) (by simp)) (by omega) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact m71
    · exact m72
    · show coreProgram.Rel rd "gkr_rounds__L1" [σ (.n 71), σ (.n 72)] []
      rw [m71, m72, e6]
      exact (gkr_rounds_holds.1 rd _ _).mpr ⟨rfl, hT (2 * j) 1 (by omega)⟩

/-- **The last record**: its capacity, cursor and claim, at `rec·g^L`. -/
theorem lyc_last (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {L : ℕ}
    (e9 : σ (.n 9) = gen ^ L) {cap : List E} {cur claim : E}
    (hc : TbCapAt rd (σ (.n 52) * gen ^ L) 0 gkCap cap)
    (hu : LoadHolds rd (σ (.n 52) * gen ^ L) (5 * gkCap) cur)
    (hl : LoadHolds rd (σ (.n 52) * gen ^ L) (6 * gkCap) claim) :
    Stmt.HoldsList C rd σ lyR3 True kret ∧ (∀ k < 5, σ (.n (74 + k)) = cap.getD k 0) ∧
      σ (.n 79) = cur ∧ σ (.n 80) = claim := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have m73 := good_mul (g 60 (.mul (.n 73) (.n 52) (.n 9)) (by decide +kernel)) (by omega)
    (by omega)
  rw [e9] at m73
  have gc := good_slice hG 61 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (74 + k)) (.n 73) (862 * k))) (by decide +kernel) (by decide +kernel)
  have kc : ∀ k < 5, some (74 + k, 73, 862 * k) ∉ lyS.map loadKey := by decide +kernel
  have rc : ∀ k < 5, σ (.n (74 + k)) = cap.getD k 0 ∧
      LoadHolds rd (σ (.n 73)) (862 * k) (σ (.n (74 + k))) := fun k hk =>
    good_readS (gc _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (kc k hk)
      (by have := tbCapAt_getD hc hk
          rwa [m73, show 862 * k = 0 + k * gkCap by unfold gkCap; ring])
  obtain ⟨e79, l79⟩ := good_read (g 66 (.load (.n 79) (.n 73) 4310) (by decide +kernel))
    (by decide +kernel) (by rw [m73]; exact hu)
  obtain ⟨e80, l80⟩ := good_read (g 67 (.load (.n 80) (.n 73) 5172) (by decide +kernel))
    (by decide +kernel) (by rw [m73]; exact hl)
  refine ⟨?_, fun k hk => (rc k hk).1, e79, e80⟩
  unfold lyR3
  repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    rw [m73, e9]
  · exact (tb_holdsList_mapAtoms 5 _).mpr fun k hk => (rc k hk).2
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨l79, l80⟩

theorem lyEvT_noRet (i : ℕ) : Stmt.noRetList (lyEvT i) = true := by
  simp [lyEvT, fsNextT, fsPackT, Stmt.noRetList, Stmt.noRet]

/-- The rate cells of four children read are canonical. -/
theorem lyRate_canonical {m : ℕ}
    (hc : ∀ i < 4, (σ (.n (lyEv (4 * m + i) + 7)), σ (.n (lyEv (4 * m + i) + 9))) =
      Keccak.scalarCells (σ (.n (lyEv (4 * m + i)))) dsObserve) :
    AllCanonical ((lyRate m).map σ) := by
  intro c hc'
  simp only [lyRate, List.map_flatMap, List.mem_flatMap, List.mem_range, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc'
  obtain ⟨i, hi, rfl | rfl⟩ := hc'
  · rw [show σ (.n (lyEv (4 * m + i) + 7)) = _ from (Prod.ext_iff.mp (hc i hi)).1]
    exact (scalarCells_canonical _ _).1
  · rw [show σ (.n (lyEv (4 * m + i) + 9)) = _ from (Prod.ext_iff.mp (hc i hi)).2]
    exact (scalarCells_canonical _ _).2

/-- **The children**: the twelve words at the last record's cursor, read, and absorbed four at a
time over the last record's capacity. -/
theorem lyc_children (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {cap : List E}
    (hcl : cap.length = 5) (hcan : AllCanonical cap)
    (e74 : ∀ k < 5, σ (.n (74 + k)) = cap.getD k 0) {ch : List E} (hch : ch.length = 12)
    (hr : TbReadsAt rd (σ (.n 79)) ch) :
    Stmt.HoldsList C rd σ lyR4 True kret ∧
      (∀ i < 12, σ (.n (lyEv i)) = ch.getD i 0 ∧ σ (.n (lyEv i + 10)) = σ (.n (lyEv i)) ∧
        FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve ∧
        (σ (.n (lyEv i + 7)), σ (.n (lyEv i + 9))) =
          Keccak.scalarCells (σ (.n (lyEv i))) dsObserve) ∧
      (lyCap 182).map σ = capOf (Fs.perm ⟨capOf (Fs.perm ⟨cap, (lyCh σ 0).map (·, dsObserve)⟩),
        (lyCh σ 1).map (·, dsObserve)⟩) := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have hni : ∀ i < 12, (lyEvT i).all notIteB = true := by decide +kernel
  have hk : ∀ i < 12, some (lyEv i, 79, i) ∉ lyS.map loadKey := by decide +kernel
  have EV : ∀ i < 12, Stmt.HoldsList C rd σ (lyEvT i) True kret ∧
      σ (.n (lyEv i)) = ch.getD i 0 ∧ σ (.n (lyEv i + 10)) = σ (.n (lyEv i)) ∧
      FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve ∧
      (σ (.n (lyEv i + 7)), σ (.n (lyEv i + 9))) =
        Keccak.scalarCells (σ (.n (lyEv i))) dsObserve := by
    intro i hi
    have gb := good_slice hG (lyPos i) (lyEvT i) (lyEvs_check i hi) (hni i hi)
    have hl : LoadHolds rd (σ (.n 79)) i (ch.getD i 0) := by
      have := hr i (by rw [hch]; exact hi)
      rwa [← List.getD_eq_getElem _ 0] at this
    obtain ⟨e0, hcells, hfs⟩ := fsNextT_good (C := C) (kret := kret)
      (fun s hs => gb s (List.mem_append_left _ hs)) (hk i hi) hl
    have cp : σ (.n (lyEv i + 10)) = σ (.n (lyEv i)) :=
      gb (.atom (.copy (.n (lyEv i + 10)) (.n (lyEv i)))) (by simp [lyEvT])
    have hok := ((holds_fsNextT _ _ _ _ _).mp hfs).1.2
    refine ⟨?_, e0, cp, hok, by rw [e0]; exact hcells⟩
    unfold lyEvT
    rw [tb_holdsList_append_noRet (by simp [fsNextT, fsPackT, Stmt.noRetList, Stmt.noRet])]
    refine ⟨hfs, ?_⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact cp
  have hp : ∀ m < 3, ∀ i < 4,
      FsPackOk σ (.n (lyEv (4 * m + i))) (lyEv (4 * m + i) + 1) dsObserve :=
    fun m hm i hi => (EV (4 * m + i) (by omega)).2.2.2.1
  have hc : ∀ m < 3, ∀ i < 4, (σ (.n (lyEv (4 * m + i) + 7)), σ (.n (lyEv (4 * m + i) + 9))) =
      Keccak.scalarCells (σ (.n (lyEv (4 * m + i)))) dsObserve :=
    fun m hm i hi => (EV (4 * m + i) (by omega)).2.2.2.2
  -- the first four children's permutation
  have hS0 : ((List.range 5).map fun k ↦ V.n (74 + k)).map σ = cap := by
    rw [tb_eq_map_getD hcl, List.map_map]
    apply List.map_congr_left
    intro k hk'
    exact e74 k (List.mem_range.mp hk')
  have hcan0 : AllCanonical ((lyRate 0 ++ (List.range 5).map fun k ↦ V.n (74 + k)).map σ) := by
    rw [List.map_append, hS0]
    intro c hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact lyRate_canonical (hc 0 (by omega)) c hc'
    · exact hcan c hc'
  obtain ⟨k108, -⟩ := keccak_good (g 108 (.keccak (lyRate 0 ++ (List.range 5).map fun k ↦
    .n (74 + k)) (lyOuts 125) false false) (by decide +kernel)) hcan0
  obtain ⟨-, B0⟩ := ly_perm_block (hp 0 (by omega)) k108
  rw [hS0] at B0
  have hcan1 : AllCanonical ((lyRate 1 ++ lyCap 125).map σ) := by
    rw [List.map_append, B0]
    intro c hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact lyRate_canonical (hc 1 (by omega)) c hc'
    · exact tb_capOf_canonical _ c hc'
  obtain ⟨k149, -⟩ := keccak_good (g 149 (.keccak (lyRate 1 ++ lyCap 125) (lyOuts 182) false false)
    (by decide +kernel)) hcan1
  obtain ⟨-, B1⟩ := ly_perm_block (hp 1 (by omega)) k149
  rw [B0] at B1
  refine ⟨?_, fun i hi => (EV i hi).2, B1⟩
  unfold lyR4
  repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact (tb_holdsList_flatten_range 4 _ lyEvT_noRet).mpr fun i hi => (EV i (by omega)).1
  · simp only [keccakA, Stmt.HoldsList, Stmt.Holds, and_true]; exact k108
  · exact (tb_holdsList_flatten_range 4 _ fun i => lyEvT_noRet _).mpr
      fun i hi => (EV (4 + i) (by omega)).1
  · simp only [keccakA, Stmt.HoldsList, Stmt.Holds, and_true]; exact k149
  · exact (tb_holdsList_flatten_range 4 _ fun i => lyEvT_noRet _).mpr
      fun i hi => (EV (8 + i) (by omega)).1

/-- **The check and the two new coordinates**: the children's products check the last claim at
the combiner; the sponge after the twelve children squeezes the two coordinates and leaves the
capacity at `283 ..`. -/
theorem lyc_check (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {P1 : KeccakState}
    (cp : ∀ i < 12, σ (.n (lyEv i + 10)) = σ (.n (lyEv i)))
    (hpk : ∀ i < 12, FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve)
    (hcells : ∀ i < 12, (σ (.n (lyEv i + 7)), σ (.n (lyEv i + 9))) =
      Keccak.scalarCells (σ (.n (lyEv i))) dsObserve)
    (hB1 : (lyCap 182).map σ = capOf P1)
    (hcheck : σ (.n 80) =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 49)))
    (c26 : σ (.n 26) = 0) (c27 : σ (.n 27) = 0) (c28 : σ (.n 28) = 0) (c29 : σ (.n 29) = 0) :
    Stmt.HoldsList C rd σ lyR5 True kret ∧
      σ (.n 274) = challengeOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩) ∧
      σ (.n 294) = challengeOf (permOf (rateOf [] ++
        capOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩))) ∧
      ((List.range 5).map fun k ↦ σ (.n (283 + k))) = capOf (permOf (rateOf [] ++
        capOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩))) := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  -- the check
  have m239 := good_mul (g 190 (.mul (.n 239) (.n 205) (.n 216)) (by decide +kernel)) (by omega)
    (by omega)
  have m240 := good_mul (g 191 (.mul (.n 240) (.n 239) (.n 227)) (by decide +kernel)) (by omega)
    (by omega)
  have m241 := good_mul (g 192 (.mul (.n 241) (.n 240) (.n 238)) (by decide +kernel)) (by omega)
    (by omega)
  have c242 : σ (.n 242) = word 0 0 0 := g 193 (.const (.n 242) (word 0 0 0)) (by decide +kernel)
  have m243 := good_mul (g 194 (.mul (.n 243) (.n 49) (.n 242)) (by decide +kernel)) (by omega)
    (by omega)
  have a244 : σ (.n 244) = σ (.n 241) + σ (.n 243) :=
    g 195 (.add (.n 244) (.n 241) (.n 243)) (by decide +kernel)
  have m245 := good_mul (g 196 (.mul (.n 245) (.n 148) (.n 159)) (by decide +kernel)) (by omega)
    (by omega)
  have m246 := good_mul (g 197 (.mul (.n 246) (.n 245) (.n 170)) (by decide +kernel)) (by omega)
    (by omega)
  have m247 := good_mul (g 198 (.mul (.n 247) (.n 246) (.n 181)) (by decide +kernel)) (by omega)
    (by omega)
  have m248 := good_mul (g 199 (.mul (.n 248) (.n 49) (.n 244)) (by decide +kernel)) (by omega)
    (by omega)
  have a249 : σ (.n 249) = σ (.n 247) + σ (.n 248) :=
    g 200 (.add (.n 249) (.n 247) (.n 248)) (by decide +kernel)
  have m250 := good_mul (g 201 (.mul (.n 250) (.n 91) (.n 102)) (by decide +kernel)) (by omega)
    (by omega)
  have m251 := good_mul (g 202 (.mul (.n 251) (.n 250) (.n 113)) (by decide +kernel)) (by omega)
    (by omega)
  have m252 := good_mul (g 203 (.mul (.n 252) (.n 251) (.n 124)) (by decide +kernel)) (by omega)
    (by omega)
  have m253 := good_mul (g 204 (.mul (.n 253) (.n 49) (.n 249)) (by decide +kernel)) (by omega)
    (by omega)
  have a254 : σ (.n 254) = σ (.n 252) + σ (.n 253) :=
    g 205 (.add (.n 254) (.n 252) (.n 253)) (by decide +kernel)
  have e254 : σ (.n 254) =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 49)) := by
    rw [a254, m253, a249, m248, a244, m243, c242, tb_word_zero, m241, m240, m239, m247, m246, m245,
      m252, m251, m250,
      show σ (.n 91) = σ (.n 81) from cp 0 (by omega), show σ (.n 102) = σ (.n 92) from cp 1 (by omega),
      show σ (.n 113) = σ (.n 103) from cp 2 (by omega),
      show σ (.n 124) = σ (.n 114) from cp 3 (by omega),
      show σ (.n 148) = σ (.n 138) from cp 4 (by omega),
      show σ (.n 159) = σ (.n 149) from cp 5 (by omega),
      show σ (.n 170) = σ (.n 160) from cp 6 (by omega),
      show σ (.n 181) = σ (.n 171) from cp 7 (by omega),
      show σ (.n 205) = σ (.n 195) from cp 8 (by omega),
      show σ (.n 216) = σ (.n 206) from cp 9 (by omega),
      show σ (.n 227) = σ (.n 217) from cp 10 (by omega),
      show σ (.n 238) = σ (.n 228) from cp 11 (by omega)]
    have hc0 : lyCh σ 0 = [σ (.n 81), σ (.n 92), σ (.n 103), σ (.n 114)] := by rw [lyCh_eq]; rfl
    have hc1 : lyCh σ 1 = [σ (.n 138), σ (.n 149), σ (.n 160), σ (.n 171)] := by rw [lyCh_eq]; rfl
    have hc2 : lyCh σ 2 = [σ (.n 195), σ (.n 206), σ (.n 217), σ (.n 228)] := by rw [lyCh_eq]; rfl
    rw [hc0, hc1, hc2]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  -- the third block's permutation
  have hp2 : ∀ i < 4, FsPackOk σ (.n (lyEv (4 * 2 + i))) (lyEv (4 * 2 + i) + 1) dsObserve :=
    fun i hi => hpk (4 * 2 + i) (by omega)
  have hcan2 : AllCanonical ((lyRate 2 ++ lyCap 182).map σ) := by
    rw [List.map_append, hB1]
    intro c hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact lyRate_canonical (fun i hi => hcells (4 * 2 + i) (by omega)) c hc'
    · exact tb_capOf_canonical _ c hc'
  obtain ⟨k207, -⟩ := keccak_good (g 207 (.keccak (lyRate 2 ++ lyCap 182) (lyOuts 255) false false)
    (by decide +kernel)) hcan2
  obtain ⟨P2, B2⟩ := ly_perm_block hp2 k207
  rw [hB1] at P2 B2
  set Q := Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩ with hQ
  -- the first coordinate
  have hco2 := challengeT_good (good_slice hG 208 (challengeT (.n 255) (.n 256) 268)
    (by decide +kernel) (by decide +kernel))
    (by rw [P2 1 (by omega)]; exact cellsOfState_canonical _ _ _)
  have e274 : σ (.n 274) = challengeOf Q := challengeT_value hco2 (P2 0 (by omega)) (P2 1 (by omega))
  -- the second
  have hz : (([.n 26, .n 26, .n 26, .n 26, .n 26, .n 27, .n 28, .n 29] ++ lyCap 255 : List V).map σ) =
      rateOf [] ++ capOf Q := by
    rw [List.map_append, B2, rateOf_eq_cells [] (by simp)]
    simp only [List.map_cons, List.map_nil, c26, c27, c28, c29]
    rfl
  have hcan3 : AllCanonical (rateOf [] ++ capOf Q) := by
    intro c hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact rateOf_canonical (by simp) c hc'
    · exact tb_capOf_canonical _ c hc'
  obtain ⟨k216, P3, B3⟩ := lyc_keccak (g 216 (.keccak ([.n 26, .n 26, .n 26, .n 26, .n 26, .n 27,
    .n 28, .n 29] ++ lyCap 255) (lyOuts 275) false false) (by decide +kernel))
    (by rw [hz]; exact hcan3)
  rw [hz] at P3 B3
  have hco3 := challengeT_good (good_slice hG 217 (challengeT (.n 275) (.n 276) 288)
    (by decide +kernel) (by decide +kernel))
    (by rw [P3 1 (by omega)]; exact cellsOfState_canonical _ _ _)
  have e294 : σ (.n 294) = challengeOf (permOf (rateOf [] ++ capOf Q)) :=
    challengeT_value hco3 (P3 0 (by omega)) (P3 1 (by omega))
  refine ⟨?_, e274, e294, ?_⟩
  · unfold lyR5
    repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [keccakA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      exact ⟨m239, m240, m241, c242, m243, a244, m245, m246, m247, m248, a249, m250, m251, m252,
        m253, a254, by rw [hcheck, ← e254, e_add_self], k207⟩
    · exact (holds_challengeT _ _ _ _ _).mpr ⟨hco2, trivial⟩
    · simp only [keccakA, Stmt.HoldsList, Stmt.Holds, and_true]; exact k216
    · exact (holds_challengeT _ _ _ _ _).mpr ⟨hco3, trivial⟩
  · rw [← B3]
    simp [lyCap]

/-- A side's new value on its equations: its four children's multilinear value at the two new
coordinates, stored at `off`. -/
theorem lyc_val (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {t b off : ℕ} (n : ℕ)
    (heq : tbStmtsEqb (lyVal t b off) ((lyPre.drop n).take (lyVal t b off).length) = true)
    (ht : t < 3) (hb : 294 < b) (cp : ∀ i < 12, σ (.n (lyEv i + 10)) = σ (.n (lyEv i)))
    (hl : LoadHolds rd (σ (.n 15)) off (multilinearEval (lyCh σ t) [σ (.n 274), σ (.n 294)])) :
    Stmt.HoldsList C rd σ (lyVal t b off) True kret := by
  have gb := good_slice hG n (lyVal t b off) heq (by simp [lyVal, notIteB])
  have he : ∀ i < 4, lyEv (4 * t + i) + 10 < b := by
    intro i hi; unfold lyEv; split_ifs <;> omega
  have a0 : σ (.n b) = σ (.n (lyEv (4 * t + 0) + 10)) + σ (.n (lyEv (4 * t + 1) + 10)) :=
    gb (.atom (.add (.n b) _ _)) (by simp [lyVal])
  have m1 := good_mulS (gb (.atom (.mul (.n (b + 1)) (.n 274) (.n b))) (by simp [lyVal]))
    (by omega) (by omega)
  have a2 : σ (.n (b + 2)) = σ (.n (lyEv (4 * t + 0) + 10)) + σ (.n (b + 1)) :=
    gb (.atom (.add (.n (b + 2)) _ _)) (by simp [lyVal])
  have a3 : σ (.n (b + 3)) = σ (.n (lyEv (4 * t + 2) + 10)) + σ (.n (lyEv (4 * t + 3) + 10)) :=
    gb (.atom (.add (.n (b + 3)) _ _)) (by simp [lyVal])
  have m4 := good_mulS (gb (.atom (.mul (.n (b + 4)) (.n 274) (.n (b + 3)))) (by simp [lyVal]))
    (by omega) (by omega)
  have a5 : σ (.n (b + 5)) = σ (.n (lyEv (4 * t + 2) + 10)) + σ (.n (b + 4)) :=
    gb (.atom (.add (.n (b + 5)) _ _)) (by simp [lyVal])
  have a6 : σ (.n (b + 6)) = σ (.n (b + 2)) + σ (.n (b + 5)) :=
    gb (.atom (.add (.n (b + 6)) _ _)) (by simp [lyVal])
  have m7 := good_mulS (gb (.atom (.mul (.n (b + 7)) (.n 294) (.n (b + 6)))) (by simp [lyVal]))
    (by omega) (by omega)
  have a8 : σ (.n (b + 8)) = σ (.n (b + 2)) + σ (.n (b + 7)) :=
    gb (.atom (.add (.n (b + 8)) _ _)) (by simp [lyVal])
  have e8 : σ (.n (b + 8)) = multilinearEval (lyCh σ t) [σ (.n 274), σ (.n 294)] := by
    rw [a8, m7, a6, a5, m4, a3, a2, m1, a0, cp (4 * t + 0) (by omega), cp (4 * t + 1) (by omega),
      cp (4 * t + 2) (by omega), cp (4 * t + 3) (by omega), lyCh_eq]
    simp only [multilinearEval, List.foldl, foldPairs, List.headD]
    ring_nf
  simp only [lyVal, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
  exact ⟨a0, m1, a2, a3, m4, a5, a6, m7, a8, by rw [e8]; exact hl⟩

/-- **The next slot and the next iteration**: the stores of the slot `34` words on, and the call
at `x·g` below the bound. -/
theorem lyc_stores (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s)
    (cp : ∀ i < 12, σ (.n (lyEv i + 10)) = σ (.n (lyEv i)))
    (s40 : LoadHolds rd (σ (.n 50)) 40 (σ (.n 274)))
    (s41 : LoadHolds rd (σ (.n 50)) 41 (σ (.n 294)))
    (s34 : ∀ k < 5, LoadHolds rd (σ (.n 15)) (34 + k) (σ (.n (283 + k))))
    (s47 : ∀ k < 4, LoadHolds rd (σ (.n 15)) (47 + k) 0)
    (s39 : LoadHolds rd (σ (.n 15)) 39 (σ (.n 79) * gen ^ 12))
    (sv : ∀ t < 3, LoadHolds rd (σ (.n 15)) (40 + t)
      (multilinearEval (lyCh σ t) [σ (.n 274), σ (.n 294)]))
    (s43 : LoadHolds rd (σ (.n 15)) 43 (σ (.n 50) * gen ^ 40))
    (s44 : LoadHolds rd (σ (.n 15)) 44 (σ (.n 51) * σ (.n 9) * gen))
    (s45 : LoadHolds rd (σ (.n 15)) 45 (σ (.n 61) * (1 + σ (.n 62) * (1 + gen))))
    (s46 : LoadHolds rd (σ (.n 15)) 46 (1 + σ (.n 62)))
    (hK : IsInK (σ (.n 0) * gen + σ (.n 1)))
    (hcall : σ (.n 0) * gen + σ (.n 1) ≠ 0 →
      C "__loop6" [σ (.n 0) * gen, σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] []) :
    Stmt.HoldsList C rd σ lyR6 True kret := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have gz := good_slice hG 232 ((List.range 4).map fun k ↦ [Stmt.atom (.const (.n (295 + k))
    (word 0 0 0)), .atom (.load (.n (295 + k)) (.n 15) (47 + k))]).flatten (by decide +kernel)
    (by decide +kernel)
  have c299 : σ (.n 299) = word 4096 0 0 := g 240 (.const (.n 299) (word 4096 0 0))
    (by decide +kernel)
  have m300 := good_mul (g 241 (.mul (.n 300) (.n 79) (.n 299)) (by decide +kernel)) (by omega)
    (by omega)
  have c328 : σ (.n 328) = word 1099511627776 0 0 :=
    g 273 (.const (.n 328) (word 1099511627776 0 0)) (by decide +kernel)
  have m329 := good_mul (g 274 (.mul (.n 329) (.n 50) (.n 328)) (by decide +kernel)) (by omega)
    (by omega)
  have m330 := good_mul (g 276 (.mul (.n 330) (.n 51) (.n 9)) (by decide +kernel)) (by omega)
    (by omega)
  have c331 : σ (.n 331) = word 2 0 0 := g 277 (.const (.n 331) (word 2 0 0)) (by decide +kernel)
  have m332 := good_mul (g 278 (.mul (.n 332) (.n 330) (.n 331)) (by decide +kernel)) (by omega)
    (by omega)
  have c333 : σ (.n 333) = word 1 0 0 := g 280 (.const (.n 333) (word 1 0 0)) (by decide +kernel)
  have c334 : σ (.n 334) = word 3 0 0 := g 281 (.const (.n 334) (word 3 0 0)) (by decide +kernel)
  have m335 := good_mul (g 282 (.mul (.n 335) (.n 62) (.n 334)) (by decide +kernel)) (by omega)
    (by omega)
  have a336 : σ (.n 336) = σ (.n 333) + σ (.n 335) :=
    g 283 (.add (.n 336) (.n 333) (.n 335)) (by decide +kernel)
  have m337 := good_mul (g 284 (.mul (.n 337) (.n 61) (.n 336)) (by decide +kernel)) (by omega)
    (by omega)
  have c338 : σ (.n 338) = word 1 0 0 := g 286 (.const (.n 338) (word 1 0 0)) (by decide +kernel)
  have a339 : σ (.n 339) = σ (.n 338) + σ (.n 62) :=
    g 287 (.add (.n 339) (.n 338) (.n 62)) (by decide +kernel)
  have c340 : σ (.n 340) = word 2 0 0 := g 289 (.const (.n 340) (word 2 0 0)) (by decide +kernel)
  have m341 := good_mul (g 290 (.mul (.n 341) (.n 0) (.n 340)) (by decide +kernel)) (by omega)
    (by omega)
  have a342 : σ (.n 342) = σ (.n 341) + σ (.n 1) :=
    g 291 (.add (.n 342) (.n 341) (.n 1)) (by decide +kernel)
  have c343 : σ (.n 343) = word 2 0 0 := g 292 (.const (.n 343) (word 2 0 0)) (by decide +kernel)
  have m344 := good_mul (g 293 (.mul (.n 344) (.n 0) (.n 343)) (by decide +kernel)) (by omega)
    (by omega)
  have w4096 : word 4096 0 0 = gen ^ 12 := by
    rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, tb_word_two_pow (by norm_num)]
  have w40 : word 1099511627776 0 0 = gen ^ 40 := by
    rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)]
  unfold lyR6
  repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨s40, s41⟩
  · exact (tb_holdsList_mapAtoms 5 _).mpr fun k hk => s34 k hk
  · refine (tb_holdsList_flatten_range 4 _ fun _ => rfl).mpr fun k hk => ?_
    have c : σ (.n (295 + k)) = word 0 0 0 :=
      gz (.atom (.const (.n (295 + k)) (word 0 0 0))) (List.mem_flatten.mpr ⟨_,
        List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, List.mem_cons_self⟩)
    rw [tb_word_zero] at c
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨by rw [c, tb_word_zero], by rw [c]; exact s47 k hk⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨c299, m300, by rw [m300, c299, w4096]; exact s39⟩
  · exact lyc_val hG 243 (by decide +kernel) (by omega) (by omega) cp (sv 0 (by omega))
  · exact lyc_val hG 253 (by decide +kernel) (by omega) (by omega) cp (sv 1 (by omega))
  · exact lyc_val hG 263 (by decide +kernel) (by omega) (by omega) cp (sv 2 (by omega))
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil]
    rw [tb_word_one] at c333 c338
    rw [tb_word_gen] at c331 c340 c343
    rw [tb_word_three] at c334
    refine ⟨c328, m329, by rw [m329, c328, w40]; exact s43, m330, by rw [c331, tb_word_gen], m332,
      by rw [m332, m330, c331]; exact s44, by rw [c333, tb_word_one], by rw [c334, tb_word_three],
      m335, a336, m337, by rw [m337, a336, m335, c334, c333]; exact s45, by rw [c338, tb_word_one],
      a339, by rw [a339, c338]; exact s46, by rw [c340, tb_word_gen], m341, a342,
      by rw [c343, tb_word_gen], m344, by rw [a342, m341, c340]; exact hK, fun hne => ?_⟩
    rw [m344, c343]
    exact hcall (by rw [a342, m341, c340] at hne; exact hne)

end Eval

end
end LeanVM.Guest.B1.Tables
