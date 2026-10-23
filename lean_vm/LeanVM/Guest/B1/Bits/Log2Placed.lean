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

/-! ## `verify_log2_ceil`, placed -/

theorem vlTail_loads (fl : ℕ) : (vlTailPre fl).filterMap Stmt.loadS = [(.n 420, 0), (.n 425, 0)] :=
  rfl

theorem regionL_single {b i : ℕ} {w : List E} (h1 : b ≤ i) (h2 : i < b + w.length) :
    RegionL [(b, w)] i := ⟨(b, w), List.mem_singleton_self _, h1, h2⟩

theorem regionL_app_left {L L' : Main.Layout} {i : ℕ} (h : RegionL L i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_left _ hq, h1, h2⟩

theorem regionL_app_right {L L' : Main.Layout} {i : ℕ} (h : RegionL L' i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_right _ hq, h1, h2⟩

/-- **`verify_log2_ceil` at the floor `fl`, placed**: on the bits of `N` at `bitsE` and the exponent
tables, it returns `[g^L, g^N]`, `L = max fl (log2Ceil N)`, its prefix sums in its one buffer,
within its frame and `35` words. -/
theorem vlc_completeAtB (fl : ℕ) (hfl : fl < 34) {name : String} {fn : Fn}
    (hf : coreProgram.find? name = some fn) (hp : fn.params = [.n 0, .n 1, .n 2])
    (hb : fn.body = vlBody fl) (hl : coreProgram.loop name = false) (κ : ℕ) (hκ6 : 6 ≤ κ)
    (bitsE lpE sqE N : ℕ) (hN : N < 2 ^ 34) (hL : max fl (log2Ceil N) < 34) :
    CompleteAtB fs cert κ name ([(bitsE, bitWords N)] ++ log2Lin lpE sqE)
      [ofK (Parameters.gpow bitsE), ofK (Parameters.gpow lpE), ofK (Parameters.gpow sqE)]
      (Returns [gen ^ max fl (log2Ceil N), gen ^ N]) (fs name + 35) := by
  have h := completeAt_leafB (fs := fs) (cert := cert) hf hl κ
    ([(bitsE, bitWords N)] ++ log2Lin lpE sqE)
    [ofK (Parameters.gpow bitsE), ofK (Parameters.gpow lpE), ofK (Parameters.gpow sqE)]
    [gen ^ max fl (log2Ceil N), gen ^ N] [35] (fun _ => [psWords N])
    (fun _ => List.Forall₂.cons (by simp [psWords]) List.Forall₂.nil) ?_
  · exact h
  intro fp rd hlow hown hLin
  have hps0 : ReadsAt rd (ofK (Parameters.gpow (fp + fs name))) (psWords N) := memL_single hown
  have hps : ∀ j ≤ 34, LoadHolds rd (ofK (Parameters.gpow (fp + fs name))) j (eOfNat (N % 2 ^ j)) :=
    fun j hj => by
      have := hps0 j (by simp [psWords]; omega)
      simpa [psWords] using this
  obtain ⟨hbL, hlin⟩ := Main.memL_append.mp hLin
  have hbits0 := memL_single hbL
  have hbits : ∀ j < 34, LoadHolds rd (ofK (Parameters.gpow bitsE)) j (bitE (N.testBit j)) :=
    fun j hj => by
      have := hbits0 j (by simp [bitWords]; omega)
      simpa [bitWords] using this
  obtain ⟨τ, e0, e1, e2, e3, e409, hh⟩ := vl_holds_low fl hfl hκ6 hlow hN hbits hL hps
    (expTables_of_memL hlin) (coreProgram.Rel rd)
  have hh' : Stmt.HoldsList (coreProgram.Rel rd) rd τ fn.body False
      (fun rs => rs = [gen ^ max fl (log2Ceil N), gen ^ N]) := by rw [hb]; exact hh
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh'
  rw [hb, vl_walk] at hsat
  obtain ⟨p1, p2, p3, p4⟩ := vlEvs_parts fl τ
  have hev : ∀ a, Ev.atom a ∈ vlEvs fl τ → a.Holds rd τ := fun a ha => (hsat.1 _ ha).1
  refine ⟨τ, vlEvs fl τ, [.n 449, .n 450], by rw [hp]; simp [e0, e1, e2], by rw [hb, vl_walk],
    hsat.2, fun e he => (hsat.1 e he).1, p4, p3, p2, by rw [p1]; simp [bases, e3], ?_⟩
  -- the loads
  have hpre : ∀ a, Stmt.atom a ∈ vlHead ++ vlTailPre fl → Ev.atom a ∈ vlEvs fl τ := fun a ha =>
    List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨_, ha, by simp [Main.slEvs]⟩))
  have m420 : τ (.n 420) = τ (.n 3) * τ (.n 409) :=
    hev (.mul (.n 420) (.n 3) (.n 409)) (hpre _ (List.mem_append_right _ (by simp [vlTailPre, vlTail])))
  have m425 : τ (.n 425) = τ (.n 1) * τ (.n 409) :=
    hev (.mul (.n 425) (.n 1) (.n 409)) (hpre _ (List.mem_append_right _ (by simp [vlTailPre, vlTail])))
  intro A hA
  set L := max fl (log2Ceil N) with hLdef
  set b := fp + fs name
  have hown : ∀ off ≤ 34, RegionL (bufL b [35] [psWords N]) (b + off) := fun off ho =>
    regionL_single (by omega) (by simp [psWords]; omega)
  have hlp : ∀ off < 34, RegionL ([(bitsE, bitWords N)] ++ log2Lin lpE sqE) (lpE + off) :=
    fun off ho => regionL_app_right ⟨_, List.mem_cons_self .., by omega, by simp; omega⟩
  -- the straight part
  unfold vlEvs at hA
  rw [loadAddrs_app, loadAddrs_app, loadAddrs_inK, List.mem_append, List.mem_append] at hA
  rcases hA with (hA | hA) | hA
  · rw [loadAddrs_straight τ _ (vlPre_straight fl), List.filterMap_append, vlTail_loads,
      List.map_append, List.mem_append] at hA
    rcases hA with hA | hA
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      have hok := List.all_eq_true.mp vlHead_loads q hq
      obtain ⟨p, off⟩ := q
      simp only [vlLoadOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        at hok
      rcases hok with (⟨rfl, ho⟩ | ⟨rfl, ho⟩) | ⟨rfl, ho⟩
      · refine ⟨bitsE + off, by rw [e0]; exact limb_ofK_gpow_mul _ _, Or.inr ?_⟩
        exact regionL_app_left (regionL_single (by omega) (by simp [bitWords]; omega))
      · refine ⟨sqE + off, by rw [e2]; exact limb_ofK_gpow_mul _ _, Or.inr ?_⟩
        exact regionL_app_right ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by omega,
          by simp [Tables.gSquaresList]; omega⟩
      · exact ⟨b + off, by rw [e3]; exact limb_ofK_gpow_mul _ _, Or.inl (hown off ho)⟩
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact ⟨b + L, by rw [m420, e3, e409]; exact limb_ofK_gpow_gen _ _, Or.inl (hown L (by omega))⟩
      · exact ⟨lpE + L, by rw [m425, e1, e409]; exact limb_ofK_gpow_gen _ _,
          Or.inr (hlp L (by omega))⟩
  · by_cases h1 : τ (.n 431) = 0
    · simp only [h1, ↓reduceIte, loadAddrs, List.filterMap_nil, List.not_mem_nil] at hA
    · simp only [h1, ↓reduceIte] at hA
      rw [loadAddrs_app, loadAddrs_inK, List.mem_append] at hA
      rcases hA with hA | hA
      · rw [loadAddrs_straight τ vlMinA rfl] at hA; simp [vlMinA, Stmt.loadS] at hA
      by_cases h2 : τ (.n 433) = 0
      · simp only [h2, ↓reduceIte, loadAddrs, List.filterMap_nil, List.not_mem_nil] at hA
      simp only [h2, ↓reduceIte] at hA
      rw [loadAddrs_straight τ vlMinIn rfl] at hA
      have hin : ∀ a, Stmt.atom a ∈ vlMinIn → Ev.atom a ∈ vlEvs fl τ := fun a ha => by
        unfold vlEvs
        simp only [h1, h2, ↓reduceIte]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_cons_of_mem _
            (List.mem_flatMap.mpr ⟨_, ha, by simp [Main.slEvs]⟩)))))
      have hA' : ∀ a, Stmt.atom a ∈ vlMinA → Ev.atom a ∈ vlEvs fl τ := fun a ha => by
        unfold vlEvs
        simp only [h1, ↓reduceIte]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, ha, by simp [Main.slEvs]⟩))))
      have m432 : τ (.n 432) = word 1 0 0 := hev (.const (.n 432) (word 1 0 0)) (hA' _ (by simp [vlMinA]))
      have m433 : τ (.n 433) = τ (.n 409) + τ (.n 432) := hev (.add (.n 433) (.n 409) (.n 432)) (hA' _ (by simp [vlMinA]))
      have m434 : τ (.n 434) = invGenWord := hev (.const (.n 434) invGenWord) (hin _ (by simp [vlMinIn]))
      have m435 : τ (.n 435) = τ (.n 409) * τ (.n 434) := hev (.mul (.n 435) (.n 409) (.n 434)) (hin _ (by simp [vlMinIn]))
      have m436 : τ (.n 436) = τ (.n 3) * τ (.n 435) := hev (.mul (.n 436) (.n 3) (.n 435)) (hin _ (by simp [vlMinIn]))
      have m438 : τ (.n 438) = invGenWord := hev (.const (.n 438) invGenWord) (hin _ (by simp [vlMinIn]))
      have m439 : τ (.n 439) = τ (.n 409) * τ (.n 438) := hev (.mul (.n 439) (.n 409) (.n 438)) (hin _ (by simp [vlMinIn]))
      have m440 : τ (.n 440) = τ (.n 1) * τ (.n 439) := hev (.mul (.n 440) (.n 1) (.n 439)) (hin _ (by simp [vlMinIn]))
      have hL0 : L ≠ 0 := fun he => by
        rw [m433, m432, word_one, e409, he, pow_zero] at h2
        exact h2 (e_add_self _)
      obtain ⟨L', hL'⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      have hinv : τ (.n 409) * invGenWord = gen ^ L' := by rw [e409, hL', gen_pow_mul_invGen]
      simp only [Stmt.loadS, vlMinIn, List.filterMap_cons, List.filterMap_nil, List.map_cons,
        List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact ⟨b + L', by rw [m436, m435, m434, hinv, e3]; exact limb_ofK_gpow_gen _ _,
          Or.inl (hown L' (by omega))⟩
      · exact ⟨lpE + L', by rw [m440, m439, m438, hinv, e1]; exact limb_ofK_gpow_gen _ _,
          Or.inr (hlp L' (by omega))⟩
  · rw [loadAddrs_straight τ vlCp rfl] at hA; simp [vlCp, Stmt.loadS] at hA

/-! ## `log2_ceil_in_the_exponent`, placed -/

/-- `log2_ceil_in_the_exponent`'s statements before its `ret`. -/
def lcPre (callee : String) : List Stmt :=
  [.atom (.const (.n 3) (word (2 ^ 34) 0 0)), .atom (.hint (.allocDyn (.n 4) (.n 3))),
    .atom (.hint (.bitsExp (.n 0) 34 (.heap (.n 4) 0 34))),
    .call callee [.n 4, .n 1, .n 2] [.n 5, .n 6], .atom (.assertEq (.n 6) (.n 0)),
    .atom (.copy (.n 7) (.n 5))]

theorem lcBody_split (callee : String) : lcBody callee = lcPre callee ++ [.ret [.n 7]] := rfl

theorem regionL_app {L L' : Main.Layout} {i : ℕ} (h : RegionL (L ++ L') i) :
    RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

/-- **`log2_ceil_in_the_exponent` at the floor `fl`, placed** (`callee` its `verify_log2_ceil`): on
`g^N` and the exponent tables it returns `g^L`, `L = max fl (log2Ceil N)`, the bits of `N` in its
one buffer, within its frame, `34` words and the callee's tree. -/
theorem lce_completeAtB (fl : ℕ) (hfl : fl < 34) {name callee : String} {fn cfn : Fn}
    (hf : coreProgram.find? name = some fn) (hp : fn.params = [.n 0, .n 1, .n 2])
    (hb : fn.body = lcBody callee) (hl : coreProgram.loop name = false)
    (hcf : coreProgram.find? callee = some cfn) (hcp : cfn.params = [.n 0, .n 1, .n 2])
    (hcb : cfn.body = vlBody fl) (hcl : coreProgram.loop callee = false) (κ : ℕ) (hκ6 : 6 ≤ κ)
    (N lpE sqE : ℕ) (hN : N < 2 ^ 34) (hL : max fl (log2Ceil N) < 34) :
    CompleteAtB fs cert κ name (log2Lin lpE sqE)
      [gen ^ N, ofK (Parameters.gpow lpE), ofK (Parameters.gpow sqE)]
      (Returns [gen ^ max fl (log2Ceil N)]) (fs name + 34 + (fs callee + 35)) := by
  intro fp
  set L := max fl (log2Ceil N) with hLdef
  set b := fp + fs name with hbdef
  let kid : Kid := ⟨callee, true,
    [ofK (Parameters.gpow b), ofK (Parameters.gpow lpE), ofK (Parameters.gpow sqE)],
    [(b, bitWords N)] ++ log2Lin lpE sqE, Returns [gen ^ L, gen ^ N]⟩
  have hown34 : List.Forall₂ (fun c s => c.length ≤ s) [bitWords N] [34] :=
    List.Forall₂.cons (by simp [bitWords]) List.Forall₂.nil
  obtain ⟨Nk, Lk, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromIn_of_kidsB (fs := fs) (cert := cert) κ
    (fun _ => fs callee + 35) [kid] (fun k hk _ => by
      rw [List.mem_singleton] at hk
      subst hk
      exact vlc_completeAtB fl hfl hcf hcp hcb hcl κ hκ6 b lpE sqE N hN hL) (b + 34)
  have hNb' : Nk ≤ fs callee + 35 := by simpa [kidsBound, kid] using hNb
  have hwb : Within (bufL b [34] [bitWords N]) b 34 := by
    simpa using bufL_within b [34] [bitWords N] hown34
  refine ⟨fs name + 34 + Nk, bufL b [34] [bitWords N] ++ Lk, [gen ^ L], [], ⟨rfl, rfl⟩, ?_, ?_,
    by omega, fun rd hlow hL' => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨hwb.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  · simpa using disj_append (bufL_disj b [34] [bitWords N] hown34) hD hwb hW le_rfl
  simp only [List.nil_append] at hL'
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL'
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  -- the valuation
  set σ : Val := setl (Val.ofArgs [gen ^ N, ofK (Parameters.gpow lpE), ofK (Parameters.gpow sqE)]) 3
    [word (2 ^ 34) 0 0, ofK (Parameters.gpow b), gen ^ L, gen ^ N, gen ^ L] with hσ
  have s0 : σ (.n 0) = gen ^ N := by simp only [hσ]; b1_look
  have s1 : σ (.n 1) = ofK (Parameters.gpow lpE) := by simp only [hσ]; b1_look
  have s2 : σ (.n 2) = ofK (Parameters.gpow sqE) := by simp only [hσ]; b1_look
  have s3 : σ (.n 3) = word (2 ^ 34) 0 0 := by simp only [hσ]; b1_look
  have s4 : σ (.n 4) = ofK (Parameters.gpow b) := by simp only [hσ]; b1_look
  have s5 : σ (.n 5) = gen ^ L := by simp only [hσ]; b1_look
  have s6 : σ (.n 6) = gen ^ N := by simp only [hσ]; b1_look
  have s7 : σ (.n 7) = gen ^ L := by simp only [hσ]; b1_look
  set es := (lcPre callee).flatMap (Main.slEvs σ) with hes
  have hw : walk σ fn.body = .ret es [.n 7] := by
    rw [hb, lcBody_split, Main.walk_straight σ _ _ rfl]
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ (lcPre callee) rfl
  have ha1 : (lcPre callee).filterMap Main.Stmt.allocSz = [(.n 4, .inr (.n 3))] := rfl
  have ha3 : (lcPre callee).filterMap Main.Stmt.addrS = [] := rfl
  have ha4 : (lcPre callee).filterMap Main.Stmt.callS =
      [(none, callee, [.n 4, .n 1, .n 2], [.n 5, .n 6])] := rfl
  rw [ha1] at i1 i2
  rw [ha3] at i3
  rw [ha4] at i4
  have hal : allocs σ es = [34] := by
    rw [i2]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, s3, word_two_pow (show 34 < 64 by norm_num)]
    rw [logG_gen_pow (by norm_num)]
  have hcalls : calls es = [⟨callee, [.n 4, .n 1, .n 2], [.n 5, .n 6], true⟩] := by
    rw [i4]; rfl
  obtain ⟨o, rfl⟩ : ∃ o, outs = [o] := by
    match outs, ho.length with
    | [o], _ => exact ⟨o, rfl⟩
  obtain ⟨hok, -⟩ := ho
  obtain ⟨ho1, -⟩ := hok rfl
  have hown' : ∀ i, RegionL (bufL b [34] [bitWords N]) i →
      ownData cert fp (fp + fs name) name (allocs σ es) es i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ hown34 i hi)
  have hk := hK rd σ (calls es) (fun i => RegionL (log2Lin lpE sqE) i ∨
      ownData cert fp (fp + fs name) name (allocs σ es) es i) (fun _ => False)
    (by
      rw [hcalls]
      refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
      · simp [s4, s1, s2, kid]
      · simp only [List.map_cons, List.map_nil, s5, s6]; exact ho1.symm)
    hlow hLk
    (memL_lins fun k hk => by
      rw [List.mem_singleton] at hk
      subst hk
      exact Main.memL_append.mpr ⟨hB, hLin⟩)
    (regionsOk_of fun k hk _ i hi => by
      rw [List.mem_singleton] at hk
      subst hk
      rcases regionL_app hi with hi | hi
      · exact Or.inl (Or.inr (hown' i hi))
      · exact Or.inl (Or.inl hi))
  have hb' : b + 34 = fp + fs name + (allocs σ es).sum := by rw [hal]; simp [hbdef]
  rw [hb'] at hk
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL (log2Lin lpE sqE))
    (D := RegionL []) (Dk := fun i => False ∨ outRegion [kid] [o] i) (N := Nk) (fp := fp)
    (args := [gen ^ N, ofK (Parameters.gpow lpE), ofK (Parameters.gpow sqE)]) (rets := [gen ^ L])
    coreProgram_wf hf (Or.inl hl) (by rw [hp]; simp [s0, s1, s2]) hw (by simp [s7])
    (fun e he => by
      simp only [hes, lcPre, List.flatMap_cons, List.flatMap_nil, Main.slEvs, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · show σ (.n 3) = _; exact s3
      · trivial
      · trivial
      · trivial
      · show σ (.n 6) + σ (.n 0) = 0; rw [s6, s0]; exact e_add_self _
      · show σ (.n 7) = σ (.n 5); rw [s7, s5])
    (by rw [hal, i1]; simp [bases, s4, hbdef]) (by rw [i3]; simp) hk
    (fun A hA => by
      rw [hes, loadAddrs_straight σ _ rfl] at hA
      simp [lcPre, Stmt.loadS] at hA)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  rw [hal] at h
  simpa using h

end
end LeanVM.Guest.B1
