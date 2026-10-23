/-
  LeanVM.Guest.B1.Bits.Log2Placed

  `verify_log2_ceil` and `log2_ceil_in_the_exponent`, placed and bounded: complete at every frame
  pointer on every memory defined below `2^κ` holding the caller's words, by a tree of at most
  their frames and buffers.
-/

module

public import LeanVM.Guest.B1.Bits.Log2Low
public import LeanVM.Guest.B1.Tables.Base
public import LeanVM.Guest.Budget.Bounded

/-!
# `verify_log2_ceil` and `log2_ceil_in_the_exponent`, placed

* `vlc_completeAtB`: `verify_log2_ceil` at the floor `fl` is a leaf with one `HeapBuf` of `35`
  words, the prefix sums `W mod 2^j` (`psWords`); on the bits of `W` (`bitsL`) and the exponent
  tables (`log2Lin`) it returns `[g^L, g^W]`, `L = max fl (log2Ceil W)`, within `fs f + 35` words.
  Its walk (`vl_walk`) takes the minimality check's branches as the valuation says.
* `lce_completeAtB`: `log2_ceil_in_the_exponent` allocates the `34` bits of `N` (`allocDyn`), then
  calls `verify_log2_ceil` on them: on `g^N` and the exponent tables it returns `g^L`, within
  `fs f + 34 + (fs callee + 35)` words.
* `log2_completeAtB_L0`, `…_L15` (and their `CompleteAtD` / `CompleteAtDTB` forms): the two
  deployed specializations.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## The layouts -/

/-- The exponent tables at `lpE`, `sqE` (B1-a's `ExpTables`, as words). -/
def log2Lin (lpE sqE : ℕ) : Main.Layout :=
  [(lpE, (List.range 34).map fun j ↦ eOfNat (2 ^ j)), (sqE, Tables.gSquaresList)]

/-- The bits of `N`, low first. -/
def bitWords (N : ℕ) : List E := (List.range 34).map fun j ↦ bitE (N.testBit j)

/-- The prefix sums `N mod 2^j`, `j ≤ 34`. -/
def psWords (N : ℕ) : List E := (List.range 35).map fun j ↦ eOfNat (N % 2 ^ j)

theorem memL_single {rd : Reader} {b : ℕ} {w : List E} (h : MemL rd [(b, w)]) :
    ReadsAt rd (ofK (Parameters.gpow b)) w := h _ (List.mem_singleton_self _)

theorem expTables_of_memL {rd : Reader} {lpE sqE : ℕ} (h : MemL rd (log2Lin lpE sqE)) :
    ExpTables rd (ofK (Parameters.gpow lpE)) (ofK (Parameters.gpow sqE)) := by
  have h1 := h _ (List.mem_cons_self ..)
  have h2 := h _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  intro j hj
  have hj' : j < 34 := hj
  refine ⟨?_, ?_⟩
  · have := h1 j (by simpa using hj')
    simpa using this
  · have := h2 j (by simpa [Tables.gSquaresList] using hj')
    simpa [Tables.gSquaresList] using this

theorem limb_ofK_gpow_mul (b off : ℕ) :
    (ofK (Parameters.gpow b)).limb 0 * Parameters.gpow off = Parameters.gpow (b + off) := by
  rw [limb_ofK]; simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]; exact gpow_add' b off

theorem limb_ofK_gpow_gen (b L : ℕ) :
    (ofK (Parameters.gpow b) * gen ^ L).limb 0 * Parameters.gpow 0 = Parameters.gpow (b + L) := by
  rw [gen_pow_eq_ofK, ← ofK_mul, limb_ofK]
  simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]
  rw [gpow_add', gpow_add', Nat.add_zero]

/-! ## `verify_log2_ceil`'s walk -/

/-- The statements before the bits' checks end. -/
def vlHead : List Stmt :=
  [.atom (.hint (.alloc (.n 3) 35)), .atom (.const (.n 4) (word 0 0 0)),
    .atom (.load (.n 4) (.n 3) 0)] ++ ((List.range 34).map vlBlk).flatten

/-- The tail's straight statements. -/
def vlTailPre (fl : ℕ) : List Stmt := (vlTail fl).take 21

/-- The minimality branch's statements before its own branch. -/
def vlMinA : List Stmt :=
  [.atom (.const (.n 432) (word 1 0 0)), .atom (.add (.n 433) (.n 409) (.n 432))]

/-- The returns' copies. -/
def vlCp : List Stmt := [.atom (.copy (.n 449) (.n 409)), .atom (.copy (.n 450) (.n 405))]

theorem vlBody_split (fl : ℕ) : vlBody fl = (vlHead ++ vlTailPre fl) ++
    (.ite (.n 431) [] vlMin :: (vlCp ++ [.ret [.n 449, .n 450]])) := by
  unfold vlBody vlHead vlTailPre
  simp only [List.append_assoc]
  rfl

theorem vlMin_split : vlMin = vlMinA ++ [.ite (.n 433) [] vlMinIn] := rfl

theorem vlHead_straight : vlHead.all Main.Stmt.straight = true := by decide +kernel

theorem vlPre_straight (fl : ℕ) : (vlHead ++ vlTailPre fl).all Main.Stmt.straight = true := by
  rw [List.all_append, vlHead_straight]; rfl

/-- The events of `verify_log2_ceil`'s walk under `σ`. -/
noncomputable def vlEvs (fl : ℕ) (σ : Val) : List Ev :=
  (vlHead ++ vlTailPre fl).flatMap (Main.slEvs σ) ++
    (.inK (.n 431) :: (if σ (.n 431) = 0 then [] else vlMinA.flatMap (Main.slEvs σ) ++
      (.inK (.n 433) :: (if σ (.n 433) = 0 then [] else vlMinIn.flatMap (Main.slEvs σ))))) ++
    vlCp.flatMap (Main.slEvs σ)

theorem vl_walk (fl : ℕ) (σ : Val) :
    walk σ (vlBody fl) = .ret (vlEvs fl σ) [.n 449, .n 450] := by
  rw [vlBody_split, walk_pre_straight σ _ _ (vlPre_straight fl), walk,
    Main.walk_straight σ [.n 449, .n 450] vlCp rfl]
  by_cases h1 : σ (.n 431) = 0
  · simp only [walk1, h1, ↓reduceIte, walk, Out.pre, Out.seq, vlEvs, List.nil_append,
      List.append_nil, List.append_assoc, List.cons_append]
  · rw [vlMin_split]
    by_cases h2 : σ (.n 433) = 0
    · simp only [walk1, h1, h2, ↓reduceIte, walk_pre_straight σ _ vlMinA rfl, walk, Out.pre,
        Out.seq, vlEvs, List.nil_append, List.append_nil, List.append_assoc, List.cons_append]
    · simp only [walk1, h1, h2, ↓reduceIte, walk_pre_straight σ _ vlMinA rfl,
        walk_straight_fall σ vlMinIn rfl, walk, Out.pre, Out.seq, vlEvs, List.nil_append,
        List.append_nil, List.append_assoc, List.cons_append]

/-- What a load of `vlHead` reads: a bit, a square, or a prefix sum. -/
def vlLoadOk (q : V × ℕ) : Bool :=
  (q.1 == .n 0 && decide (q.2 < 34)) || (q.1 == .n 2 && decide (q.2 < 34)) ||
    (q.1 == .n 3 && decide (q.2 ≤ 34))

theorem vlHead_loads : (vlHead.filterMap Stmt.loadS).all vlLoadOk = true := by decide +kernel

theorem vlHead_alloc : vlHead.filterMap Main.Stmt.allocSz = [(.n 3, .inl 35)] := by decide +kernel

theorem vlHead_addr : vlHead.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem vlHead_call : vlHead.filterMap Main.Stmt.callS = [] := by decide +kernel

theorem allocDsts_app (a b : List Ev) : allocDsts (a ++ b) = allocDsts a ++ allocDsts b :=
  List.filterMap_append
theorem allocs_app (σ : Val) (a b : List Ev) : allocs σ (a ++ b) = allocs σ a ++ allocs σ b :=
  List.filterMap_append
theorem addrs_app (a b : List Ev) : addrs (a ++ b) = addrs a ++ addrs b := List.filterMap_append
theorem calls_app (a b : List Ev) : calls (a ++ b) = calls a ++ calls b := List.filterMap_append
theorem loadAddrs_app (σ : Val) (a b : List Ev) :
    loadAddrs σ (a ++ b) = loadAddrs σ a ++ loadAddrs σ b := List.filterMap_append
theorem allocDsts_inK (c : V) (es : List Ev) : allocDsts (.inK c :: es) = allocDsts es := rfl
theorem allocs_inK (σ : Val) (c : V) (es : List Ev) : allocs σ (.inK c :: es) = allocs σ es := rfl
theorem addrs_inK (c : V) (es : List Ev) : addrs (.inK c :: es) = addrs es := rfl
theorem calls_inK (c : V) (es : List Ev) : calls (.inK c :: es) = calls es := rfl
theorem loadAddrs_inK (σ : Val) (c : V) (es : List Ev) :
    loadAddrs σ (.inK c :: es) = loadAddrs σ es := rfl

/-- The parts of a straight block with no buffer, run or call. -/
theorem plain_parts (σ : Val) {pre : List Stmt} (hs : pre.all Main.Stmt.straight = true)
    (ha : pre.filterMap Main.Stmt.allocSz = []) (hd : pre.filterMap Main.Stmt.addrS = [])
    (hc : pre.filterMap Main.Stmt.callS = []) :
    allocDsts (pre.flatMap (Main.slEvs σ)) = [] ∧ allocs σ (pre.flatMap (Main.slEvs σ)) = [] ∧
      addrs (pre.flatMap (Main.slEvs σ)) = [] ∧ calls (pre.flatMap (Main.slEvs σ)) = [] := by
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ pre hs
  rw [i1, i2, i3, i4, ha, hd, hc]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem vlEvs_parts (fl : ℕ) (σ : Val) :
    allocDsts (vlEvs fl σ) = [.n 3] ∧ allocs σ (vlEvs fl σ) = [35] ∧ addrs (vlEvs fl σ) = [] ∧
      calls (vlEvs fl σ) = [] := by
  obtain ⟨a1, a2, a3, a4⟩ := Main.straight_parts σ _ (vlPre_straight fl)
  have ht1 : (vlTailPre fl).filterMap Main.Stmt.allocSz = [] := rfl
  have ht2 : (vlTailPre fl).filterMap Main.Stmt.addrS = [] := rfl
  have ht3 : (vlTailPre fl).filterMap Main.Stmt.callS = [] := rfl
  rw [List.filterMap_append, vlHead_alloc, ht1] at a1 a2
  rw [List.filterMap_append, vlHead_addr, ht2] at a3
  rw [List.filterMap_append, vlHead_call, ht3] at a4
  obtain ⟨b1, b2, b3, b4⟩ := plain_parts σ (pre := vlMinA) rfl rfl rfl rfl
  obtain ⟨c1, c2, c3, c4⟩ := plain_parts σ (pre := vlMinIn) rfl rfl rfl rfl
  obtain ⟨d1, d2, d3, d4⟩ := plain_parts σ (pre := vlCp) rfl rfl rfl rfl
  unfold vlEvs
  by_cases h1 : σ (.n 431) = 0
  · simp only [h1, ↓reduceIte, allocDsts_app, allocs_app, addrs_app, calls_app, allocDsts_inK,
      allocs_inK, addrs_inK, calls_inK, a1, a2, a3, a4, d1, d2, d3, d4]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · by_cases h2 : σ (.n 433) = 0
    · simp only [h1, h2, ↓reduceIte, allocDsts_app, allocs_app, addrs_app, calls_app,
        allocDsts_inK, allocs_inK, addrs_inK, calls_inK, a1, a2, a3, a4, b1, b2, b3, b4, d1, d2,
        d3, d4]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · simp only [h1, h2, ↓reduceIte, allocDsts_app, allocs_app, addrs_app, calls_app,
        allocDsts_inK, allocs_inK, addrs_inK, calls_inK, a1, a2, a3, a4, b1, b2, b3, b4, c1, c2,
        c3, c4, d1, d2, d3, d4]
      exact ⟨rfl, rfl, rfl, rfl⟩

end
end LeanVM.Guest.B1
