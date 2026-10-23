/-
  LeanVM.Guest.B1.Gkr.Loop7In

  `__loop7` loads from any region holding, at each iteration, its layer slot, its row, its round
  records and the words at the records' cursors.
-/

module

public import LeanVM.Guest.B1.Gkr.Layer
public import LeanVM.Guest.B1.Tables.Kids.Gkr

/-!
# `__loop7`, loading from a region

`__loop7`'s body is straight but for two branches of straight statements, each ending in a call of
the rounds (`gkr_rounds__L2` at an odd layer index, `gkr_rounds__L1` at an odd depth): it walks
its statements in turn, a branch's when taken (`ly_walk`).

* `Ly7In`: what iteration `j` reads, in `R`: the slot of `L = 2j + sh` (`51` words, through the
  next slot's stores), its row (`L + 42` words), position, `half` and `parity`; the records from
  `rounds·pos` (`L + 5173` words), record `r`'s cursor `cj·g^(4r)`, the `4L + 12` words from `cj`.
* `loop7_relIn`: with those at every `j < m`, iteration `j < m` of `__loop7` loads from `R`, by
  the depth of its derivation; its rounds by `loop29_relIn` and `gkr_rounds_relIn`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## The walk -/

/-- A block of straight statements walks each, falling through. -/
theorem walk_straight_fall (σ : Val) {z : List Stmt} (h : z.all Main.Stmt.straight = true) :
    walk σ z = .fall (z.flatMap (Main.slEvs σ)) := by
  have e := walk_pre_straight σ [] z h
  rw [List.append_nil] at e
  rw [e, walk, Out.pre, List.append_nil]

/-- A branch between blocks of straight statements: its condition, then the block taken. -/
theorem walk1_ite_straight (σ : Val) (c : V) {z n : List Stmt}
    (hz : z.all Main.Stmt.straight = true) (hn : n.all Main.Stmt.straight = true) :
    walk1 σ (.ite c z n) = .fall (.inK c :: (if σ c = 0 then z else n).flatMap (Main.slEvs σ)) := by
  rw [walk1]
  by_cases hc : σ c = 0
  · simp only [hc, ↓reduceIte, walk_straight_fall σ hz, Out.pre, List.singleton_append]
  · simp only [hc, ↓reduceIte, walk_straight_fall σ hn, Out.pre, List.singleton_append]

/-- `__loop7`'s statements through `__loop29`. -/
def lyA : List Stmt := lyBody.take 57

/-- `__loop7`'s statements after the rounds, before its `ret`. -/
def lyB : List Stmt := lyPre.drop 60

/-- The rounds at an odd layer index. -/
def ly62 : List Stmt :=
  [.atom (.mul (.n 66) (.n 61) (.n 61)), .atom (.mul (.n 67) (.n 66) (.n 66)),
    .atom (.mul (.n 68) (.n 52) (.n 67)), .atom (.mul (.n 69) (.n 50) (.n 67)),
    .call "gkr_rounds__L2" [.n 68, .n 69] []]

/-- The round at an odd depth. -/
def ly70 : List Stmt :=
  [.atom (.mul (.n 71) (.n 52) (.n 6)), .atom (.mul (.n 72) (.n 50) (.n 6)),
    .call "gkr_rounds__L1" [.n 71, .n 72] []]

theorem lyBody_split : lyBody = lyA ++ (.ite (.n 62) [] ly62 :: .atom (.add (.n 70) (.n 9) (.n 6)) ::
    .ite (.n 70) [] ly70 :: (lyB ++ [.ret []])) := tbStmtsEqb_sound (by decide +kernel)

theorem lyA_straight : lyA.all Main.Stmt.straight = true := by decide +kernel
theorem lyB_straight : lyB.all Main.Stmt.straight = true := by decide +kernel
theorem ly62_straight : ly62.all Main.Stmt.straight = true := by decide +kernel
theorem ly70_straight : ly70.all Main.Stmt.straight = true := by decide +kernel

theorem lyA_calls : lyA.filterMap Main.Stmt.callS =
    [(some (.n 64), "__loop29", [.n 65, .n 61, .n 52, .n 50], [])] := by decide +kernel

theorem lyB_calls : lyB.filterMap Main.Stmt.callS =
    [(some (.n 342), "__loop7", [.n 344, .n 1, .n 2, .n 3, .n 4, .n 5], [])] := by decide +kernel

theorem lyA_loads : lyA.all (loadsViaB [(7, 1), (15, 51), (52, 5173)]) = true := by decide +kernel

theorem lyB_loads : lyB.all (loadsViaB [(15, 51), (50, 42), (73, 5173), (79, 12)]) = true := by
  decide +kernel

/-- The events of a branch's block taken or not. -/
noncomputable def lyBr (σ : Val) (c : V) (z : List Stmt) : List Ev :=
  .inK c :: (if σ c = 0 then [] else z).flatMap (Main.slEvs σ)

/-- **`__loop7`'s walk**: its statements in turn, a branch's when taken. -/
theorem ly_walk (σ : Val) : walk σ lyBody = .ret (lyA.flatMap (Main.slEvs σ) ++ lyBr σ (.n 62) ly62 ++
    (.atom (.add (.n 70) (.n 9) (.n 6)) :: lyBr σ (.n 70) ly70) ++ lyB.flatMap (Main.slEvs σ)) [] := by
  rw [lyBody_split, walk_pre_straight σ _ lyA lyA_straight, walk, walk, walk,
    walk1_ite_straight σ _ rfl ly62_straight, walk1_ite_straight σ _ rfl ly70_straight,
    Main.walk1_straight σ (.atom _) rfl, Main.walk_straight σ [] lyB lyB_straight]
  simp only [Out.seq, Out.pre, lyBr, Main.slEvs, List.append_assoc, List.cons_append,
    List.nil_append]

/-- A branch's block without loads loads nothing. -/
theorem loadAddrs_lyBr {σ : Val} {c : V} {z : List Stmt} (hs : z.all Main.Stmt.straight = true)
    (hl : z.filterMap Stmt.loadS = []) : loadAddrs σ (lyBr σ c z) = [] := by
  show loadAddrs σ ((if σ c = 0 then [] else z).flatMap (Main.slEvs σ)) = []
  by_cases hc : σ c = 0
  · simp only [hc, ↓reduceIte, List.flatMap_nil, loadAddrs, List.filterMap_nil]
  · simp only [hc, ↓reduceIte]
    rw [B1.loadAddrs_straight σ z hs, hl]; rfl

/-- A branch's frames: its block's, when taken. -/
theorem calls_lyBr {σ : Val} {c : V} {z : List Stmt} (hs : z.all Main.Stmt.straight = true) :
    calls (lyBr σ c z) = if σ c = 0 then [] else (z.filterMap Main.Stmt.callS).map (Main.mkCall σ) := by
  show calls ((if σ c = 0 then [] else z).flatMap (Main.slEvs σ)) = _
  by_cases hc : σ c = 0
  · simp only [hc, ↓reduceIte, List.flatMap_nil, calls, List.filterMap_nil]
  · simp only [hc, ↓reduceIte]
    exact (Main.straight_parts σ z hs).2.2.2

/-! ## The iterations -/

/-- **What iteration `j` reads, in `R`**: the slot of `L = 2j + sh` through the next slot's stores,
its row, position, `half` and `parity`; the round records from `rounds·pos`, record `r`'s cursor
`cj·g^(4r)`, and the words from `cj` the rounds and the children read. -/
def Ly7In (rd : Reader) (R : ℕ → Prop) (layers rounds : E) (sh j : ℕ) : Prop :=
  ∃ row pos cj : E,
    PtrIn R (layers * gen ^ (17 * (2 * j + sh))) 51 ∧
    LoadHolds rd layers (17 * (2 * j + sh) + 9) row ∧
    LoadHolds rd layers (17 * (2 * j + sh) + 10) pos ∧
    LoadHolds rd layers (17 * (2 * j + sh) + 11) (gen ^ (j / 2)) ∧
    LoadHolds rd layers (17 * (2 * j + sh) + 12) (bitE (j % 2 = 1)) ∧
    PtrIn R row (2 * j + sh + 42) ∧ PtrIn R (rounds * pos) (2 * j + sh + 5173) ∧
    PtrIn R cj (4 * (2 * j + sh) + 12) ∧
    ∀ r ≤ 2 * j + sh, LoadHolds rd (rounds * pos * gen ^ r) 4310 (cj * gen ^ (4 * r))

theorem tb_lName_gkr_rounds : lName "gkr_rounds" 1 = "gkr_rounds__L1" ∧
    lName "gkr_rounds" 2 = "gkr_rounds__L2" := ⟨rfl, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **`__loop7` loads from `R`**, every iteration `j < m`, its slots, rows, records and cursors
in `R` (`Ly7In`) and `depth_shift[g_bus_mu]` at `dsh·gmu`, holding `g^sh`. -/
theorem loop7_relIn {rd : Reader} {R : ℕ → Prop} {dsh gmu layers rounds : E} {sh m : ℕ}
    (hsh : LoadHolds rd (dsh * gmu) 0 (gen ^ sh)) (hshR : PtrIn R (dsh * gmu) 1)
    (hit : ∀ j < m, Ly7In rd R layers rounds sh j) :
    ∀ d j, j < m →
      coreProgram.relN rd d "__loop7" [gen ^ j, gen ^ m, dsh, gmu, layers, rounds] [] →
      coreProgram.RelIn rd R "__loop7" [gen ^ j, gen ^ m, dsh, gmu, layers, rounds] [] := by
  intro d
  induction d with
  | zero => intro j _ h; exact h.elim
  | succ d ih =>
    intro j hj h
    obtain ⟨fn, hf, hsem⟩ := h
    obtain ⟨fn', hf', hpm, hb⟩ := lyFound
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    obtain ⟨row, pos, cj, hRL, hrow, hpos, hhalf, hpar, hRrow, hRrec, hRcur, hcur⟩ := hit j hj
    set L := 2 * j + sh with hL
    refine relIn_of_sem hf hsem fun σ hpar' hhl es vs hw ↦ ?_
    rw [hpm] at hpar'
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar'
    obtain ⟨p0, p1, p2, p3, p4, p5⟩ := hpar'
    rw [hb, ly_walk] at hw
    injection hw with hes _
    subst hes
    rw [hb, lyBody_eq, holdsList_append, holdsList_noRet _ lyPre_noRet] at hhl
    have hP := hhl.1
    have hnr := lyPre_noRet
    have a := fun n a heq ↦ tb_holds_atom hnr hP n a heq
    have m6 := a 0 (.mul (.n 6) (.n 0) (.n 0)) (by decide +kernel)
    have m7 := a 1 (.mul (.n 7) (.n 2) (.n 3)) (by decide +kernel)
    have l8 := a 2 (.load (.n 8) (.n 7) 0) (by decide +kernel)
    have m9 := a 3 (.mul (.n 9) (.n 6) (.n 8)) (by decide +kernel)
    have m10 := a 4 (.mul (.n 10) (.n 9) (.n 9)) (by decide +kernel)
    have m11 := a 5 (.mul (.n 11) (.n 10) (.n 10)) (by decide +kernel)
    have m12 := a 6 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel)
    have m13 := a 7 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel)
    have m14 := a 8 (.mul (.n 14) (.n 13) (.n 9)) (by decide +kernel)
    have m15 := a 9 (.mul (.n 15) (.n 4) (.n 14)) (by decide +kernel)
    have l50 := a 33 (.load (.n 50) (.n 15) 9) (by decide +kernel)
    have l51 := a 34 (.load (.n 51) (.n 15) 10) (by decide +kernel)
    have m52 := a 35 (.mul (.n 52) (.n 5) (.n 51)) (by decide +kernel)
    have l61 := a 51 (.load (.n 61) (.n 15) 11) (by decide +kernel)
    have l62 := a 52 (.load (.n 62) (.n 15) 12) (by decide +kernel)
    have c63 := a 53 (.const (.n 63) (word 1 0 0)) (by decide +kernel)
    have a64 := a 54 (.add (.n 64) (.n 63) (.n 61)) (by decide +kernel)
    have c65 := a 55 (.const (.n 65) (word 1 0 0)) (by decide +kernel)
    have a70 := a 58 (.add (.n 70) (.n 9) (.n 6)) (by decide +kernel)
    have m73 := a 60 (.mul (.n 73) (.n 52) (.n 9)) (by decide +kernel)
    have l79 := a 66 (.load (.n 79) (.n 73) 4310) (by decide +kernel)
    have c340 := a 289 (.const (.n 340) (word 2 0 0)) (by decide +kernel)
    have m341 := a 290 (.mul (.n 341) (.n 0) (.n 340)) (by decide +kernel)
    have a342 := a 291 (.add (.n 342) (.n 341) (.n 1)) (by decide +kernel)
    have c343 := a 292 (.const (.n 343) (word 2 0 0)) (by decide +kernel)
    have m344 := a 293 (.mul (.n 344) (.n 0) (.n 343)) (by decide +kernel)
    simp only [Atom.Holds] at m6 m7 l8 m9 m10 m11 m12 m13 m14 m15 l50 l51 m52 l61 l62
    simp only [Atom.Holds] at c63 a64 c65 a70 m73 l79 c340 m341 a342 c343 m344
    rw [tb_word_one] at c63 c65
    rw [tb_word_gen] at c340 c343
    rw [m7, p2, p3] at l8
    have e8 := tb_loadHolds_unique l8 hsh
    have e6 : σ (.n 6) = gen ^ (2 * j) := by rw [m6, p0, ← pow_add]; ring_nf
    have e9 : σ (.n 9) = gen ^ L := by rw [m9, e6, e8, hL, pow_add]
    have e15 : σ (.n 15) = layers * gen ^ (17 * L) := by
      rw [m15, m14, m13, m12, m11, m10, e9, p4, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      ring_nf
    have ld : ∀ k w, LoadHolds rd (σ (.n 15)) k w → LoadHolds rd layers (17 * L + k) w := by
      intro k w h; rwa [e15, tb_loadHolds_mul_gen_pow] at h
    have e50 := tb_loadHolds_unique (ld _ _ l50) hrow
    have e51 := tb_loadHolds_unique (ld _ _ l51) hpos
    have e61 := tb_loadHolds_unique (ld _ _ l61) hhalf
    have e62 := tb_loadHolds_unique (ld _ _ l62) hpar
    have e52 : σ (.n 52) = rounds * pos := by rw [m52, p5, e51]
    have e73 : σ (.n 73) = rounds * pos * gen ^ L := by rw [m73, e52, e9]
    rw [e73] at l79
    have e79 := tb_loadHolds_unique l79 (hcur L le_rfl)
    -- a record's cursor
    have hcurIn : ∀ r B, 4 * r + B ≤ 4 * L + 12 → r ≤ L → ∀ c,
        LoadHolds rd (rounds * pos * gen ^ r) 4310 c → PtrIn R c B := by
      intro r B hB hr c hc
      rw [tb_loadHolds_unique hc (hcur r hr)]
      exact ptrIn_mul (ptrIn_mono hRcur hB)
    refine ⟨fun A hA ↦ ?_, fun c hc ht ↦ ?_⟩
    · -- the loads
      rw [loadAddrs_append, loadAddrs_append, loadAddrs_append,
        loadAddrs_lyBr ly62_straight (by decide +kernel),
        show loadAddrs σ (.atom (.add (.n 70) (.n 9) (.n 6)) :: lyBr σ (.n 70) ly70) =
          loadAddrs σ (lyBr σ (.n 70) ly70) from rfl,
        loadAddrs_lyBr ly70_straight (by decide +kernel), B1.loadAddrs_straight σ lyA lyA_straight,
        B1.loadAddrs_straight σ lyB lyB_straight] at hA
      simp only [List.append_nil, List.mem_append, List.mem_map] at hA
      rcases hA with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · refine loads_via lyA_loads (fun pb hpb ↦ ?_) q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
        rcases hpb with rfl | rfl | rfl
        · rw [m7, p2, p3]; exact hshR
        · rw [e15]; exact hRL
        · rw [e52]; exact ptrIn_mono hRrec (by omega)
      · refine loads_via lyB_loads (fun pb hpb ↦ ?_) q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
        rcases hpb with rfl | rfl | rfl | rfl
        · rw [e15]; exact hRL
        · rw [e50]; exact ptrIn_mono hRrow (by omega)
        · rw [e73]; exact ptrIn_mul hRrec
        · rw [e79]; exact ptrIn_mul hRcur
    · -- the calls
      rw [calls_append, calls_append, calls_append, calls_lyBr ly62_straight,
        show calls (.atom (.add (.n 70) (.n 9) (.n 6)) :: lyBr σ (.n 70) ly70) =
          calls (lyBr σ (.n 70) ly70) from rfl,
        calls_lyBr ly70_straight, (Main.straight_parts σ lyA lyA_straight).2.2.2,
        (Main.straight_parts σ lyB lyB_straight).2.2.2, lyA_calls, lyB_calls] at hc
      simp only [List.mem_append] at hc
      rcases hc with ((hc | hc) | hc) | hc
      · -- `__loop29`
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
        have hci := tb_holds_callIf hnr hP 56 (.n 64) "__loop29" [.n 65, .n 61, .n 52, .n 50]
          (by decide +kernel)
        have hrel := hci.2 ht
        have hK : 0 < j / 2 := by
          rcases Nat.eq_zero_or_pos (j / 2) with h0 | h0
          · exfalso; apply ht
            rw [a64, c63, e61, h0, pow_zero, e_add_self]
          · exact h0
        simp only [List.map_cons, List.map_nil, c65, e61, e52, e50] at hrel ⊢
        rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at hrel ⊢
        exact loop29_relIn (ptrIn_mono hRrec (by omega)) (ptrIn_mono hRrow (by omega))
          (fun k hk c hc ↦ hcurIn (4 * k) 16 (by omega) (by omega) c hc) d 0 hK hrel
      · -- `gkr_rounds__L2`
        split at hc
        · simp at hc
        rename_i h62
        rw [show ly62.filterMap Main.Stmt.callS = [(none, "gkr_rounds__L2", [.n 68, .n 69], [])] by
          decide +kernel] at hc
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        have hodd : j % 2 = 1 := by
          by_contra hne
          apply h62
          rw [e62]; simp [bitE, hne]
        have hi := tb_holds_slice hnr hP 57 [.ite (.n 62) [] ly62] (by decide +kernel)
        have hbr := hi.2.2 h62
        simp only [Stmt.HoldsList, Stmt.Holds, ly62, Atom.Holds, List.map_cons, List.map_nil,
          and_true] at hbr
        obtain ⟨m66, m67, m68, m69, hrel⟩ := hbr
        have e67 : σ (.n 67) = gen ^ (4 * (j / 2)) := by
          rw [m67, m66, e61, ← pow_add, ← pow_add]; ring_nf
        simp only [Main.mkCall, List.map_cons, List.map_nil]
        rw [m68, m69, e67, e52, e50] at hrel ⊢
        rw [← tb_lName_gkr_rounds.2] at hrel ⊢
        exact gkr_rounds_relIn (Or.inr rfl) (ptrIn_mul (ptrIn_mono hRrec (by omega)))
          (ptrIn_mul (ptrIn_mono hRrow (by omega)))
          (hcurIn (4 * (j / 2)) (4 * 2) (by omega) (by omega)) ⟨d, hrel⟩
      · -- `gkr_rounds__L1`
        split at hc
        · simp at hc
        rename_i h70
        rw [show ly70.filterMap Main.Stmt.callS = [(none, "gkr_rounds__L1", [.n 71, .n 72], [])] by
          decide +kernel] at hc
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        have hsh1 : 1 ≤ sh := by
          by_contra h0
          apply h70
          rw [a70, e9, e6, show L = 2 * j by omega, e_add_self]
        have hi := tb_holds_slice hnr hP 59 [.ite (.n 70) [] ly70] (by decide +kernel)
        have hbr := hi.2.2 h70
        simp only [Stmt.HoldsList, Stmt.Holds, ly70, Atom.Holds, List.map_cons, List.map_nil,
          and_true] at hbr
        obtain ⟨m71, m72, hrel⟩ := hbr
        simp only [Main.mkCall, List.map_cons, List.map_nil]
        rw [m71, m72, e6, e52, e50] at hrel ⊢
        rw [← tb_lName_gkr_rounds.1] at hrel ⊢
        exact gkr_rounds_relIn (Or.inl rfl) (ptrIn_mul (ptrIn_mono hRrec (by omega)))
          (ptrIn_mul (ptrIn_mono hRrow (by omega)))
          (hcurIn (2 * j) (4 * 1) (by omega) (by omega)) ⟨d, hrel⟩
      · -- the next iteration
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
        have hci := tb_holds_callIf hnr hP 294 (.n 342) "__loop7"
          [.n 344, .n 1, .n 2, .n 3, .n 4, .n 5] (by decide +kernel)
        have hrel := hci.2 ht
        have e344 : σ (.n 344) = gen ^ (j + 1) := by rw [m344, c343, p0, pow_succ]
        have e342 : σ (.n 342) = gen ^ (j + 1) + gen ^ m := by
          rw [a342, m341, c340, p0, p1, pow_succ]
        have hj1 : j + 1 < m := by
          rcases Nat.lt_or_ge (j + 1) m with h' | h'
          · exact h'
          · exfalso
            apply ht
            rw [e342, show j + 1 = m by omega, e_add_eq_zero_iff]
        simp only [List.map_cons, List.map_nil, e344, p1, p2, p3, p4, p5] at hrel ⊢
        exact ih (j + 1) hj1 hrel

end
end LeanVM.Guest.B1.Tables
