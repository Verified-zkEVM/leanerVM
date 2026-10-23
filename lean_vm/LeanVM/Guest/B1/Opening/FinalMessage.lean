/-
  LeanVM.Guest.B1.Opening.FinalMessage

  B1 for `opening_final_message`: one generic argument over the message's length `4m`.
-/

module

public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run

/-!
# `opening_final_message` (G:1132-1150, TRIAGE #37)

Its body at `n = 4m` words (`ofmBody m`): the capacity copied into `9 .. 13`, the waiting `w0`,
`w1` packed (`fsPackT` from `14`, `23`); message word `i` read, packed and stored
(`ofmNext i (msgV i)`, `msgV i = 12 + 53·((i+2)/4) + 10·((i+2)%4)`), the queue permuted after
every fourth waiting scalar (`ofmFirst`, `ofmBlock j` for block `j + 1`, its outputs at
`52 + 53 j`); the last two words, the nonce at `F + 20` (`F = 12 + 53 m`, packed with the tag
`dsPowNonce`), the zero run, the final permutation into `F + 32`, the returns.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Message word `i`: read, packed (cells `b + 7`, `b + 9`) and stored at `out[i]`. -/
def ofmNext (i b : ℕ) : List Stmt := fsNextT (.n 7) i b ++ [.atom (.load (.n b) (.n 8) i)]

/-- The rate cells of a block of four words from `b`. -/
def ofmRate (b : ℕ) : List V := [.n (b + 7), .n (b + 9), .n (b + 17), .n (b + 19), .n (b + 27),
  .n (b + 29), .n (b + 37), .n (b + 39)]

/-- The capacity cells of a permutation's outputs at `o`. -/
def capIns (o : ℕ) : List V := [.n (o + 8), .n (o + 9), .n (o + 10), .n (o + 11), .n (o + 12)]

/-- Thirteen consecutive values. -/
def ofmRun (b : ℕ) : List V := (List.range 13).map fun i ↦ .n (b + i)

/-- Block `j + 1` (`j + 1 < m`): words `4j + 2 .. 4j + 5`, then the permutation. -/
def ofmBlock (j : ℕ) : List Stmt :=
  ofmNext (4 * j + 2) (65 + 53 * j) ++ ofmNext (4 * j + 3) (75 + 53 * j) ++
    ofmNext (4 * j + 4) (85 + 53 * j) ++ ofmNext (4 * j + 5) (95 + 53 * j) ++
    [keccakA (ofmRate (65 + 53 * j) ++ capIns (52 + 53 * j)) (ofmRun (105 + 53 * j))]

/-- The expansion of `opening_final_message` at `4m` words, `m ≥ 1`. -/
def ofmBody (m : ℕ) : List Stmt :=
  [.atom (.copy (.n 9) (.n 0)), .atom (.copy (.n 10) (.n 1)), .atom (.copy (.n 11) (.n 2)),
    .atom (.copy (.n 12) (.n 3)), .atom (.copy (.n 13) (.n 4))] ++
  fsPackT (.n 5) 14 dsObserve ++ fsPackT (.n 6) 23 dsObserve ++
  ofmNext 0 32 ++ ofmNext 1 42 ++
  [keccakA [.n 20, .n 22, .n 29, .n 31, .n 39, .n 41, .n 49, .n 51, .n 9, .n 10, .n 11, .n 12,
    .n 13] (ofmRun 52)] ++
  ((List.range (m - 1)).map ofmBlock).flatten ++
  ofmNext (4 * m - 2) (12 + 53 * m) ++ ofmNext (4 * m - 1) (22 + 53 * m) ++
  [.atom (.load (.n (32 + 53 * m)) (.n 7) (4 * m))] ++
  fsPackT (.n (32 + 53 * m)) (33 + 53 * m) dsPowNonce ++
  [.atom (.const (.n (42 + 53 * m)) (word 0 0 0)), .atom (.const (.n (43 + 53 * m)) (word 0 0 0)),
    keccakA ([.n (19 + 53 * m), .n (21 + 53 * m), .n (29 + 53 * m), .n (31 + 53 * m),
      .n (39 + 53 * m), .n (41 + 53 * m), .n (42 + 53 * m), .n (43 + 53 * m)] ++ capIns (53 * m - 1))
      (ofmRun (44 + 53 * m)),
    .atom (.copy (.n (57 + 53 * m)) (.n (44 + 53 * m))),
    .atom (.copy (.n (58 + 53 * m)) (.n (52 + 53 * m))),
    .atom (.copy (.n (59 + 53 * m)) (.n (53 + 53 * m))),
    .atom (.copy (.n (60 + 53 * m)) (.n (54 + 53 * m))),
    .atom (.copy (.n (61 + 53 * m)) (.n (55 + 53 * m))),
    .atom (.copy (.n (62 + 53 * m)) (.n (56 + 53 * m))),
    .atom (.const (.n (63 + 53 * m)) (word (2 ^ (4 * m)) 0 0)),
    .atom (.mul (.n (64 + 53 * m)) (.n 7) (.n (63 + 53 * m))),
    .atom (.const (.n (65 + 53 * m)) (word 2 0 0)),
    .atom (.mul (.n (66 + 53 * m)) (.n (64 + 53 * m)) (.n (65 + 53 * m))),
    .atom (.copy (.n (67 + 53 * m)) (.n (32 + 53 * m))),
    .ret [.n (57 + 53 * m), .n (58 + 53 * m), .n (59 + 53 * m), .n (60 + 53 * m),
      .n (61 + 53 * m), .n (62 + 53 * m), .n (66 + 53 * m), .n (67 + 53 * m)]]

/-! ## The sponge of the message -/

theorem absorbAll_append' (s : Fs) (xs ys : List E) (t : ℕ) :
    s.absorbAll (xs ++ ys) t = (s.absorbAll xs t).absorbAll ys t := by
  simp [Fs.absorbAll, List.foldl_append]

/-- Four words onto two waiting: the queue fills, permutes, and two wait again. -/
theorem absorbAll_four (c : List E) (a b : E × ℕ) (x0 x1 x2 x3 : E) :
    (⟨c, [a, b]⟩ : Fs).absorbAll [x0, x1, x2, x3] dsObserve =
      ⟨capOf (⟨c, [a, b, (x0, dsObserve), (x1, dsObserve)]⟩ : Fs).perm,
        [(x2, dsObserve), (x3, dsObserve)]⟩ := by
  simp [Fs.absorbAll, Fs.absorb, rateScalars]

/-- The states the message's permutations write. -/
def ofmQ (cap : List E) (w0 w1 : E) (ms : ℕ → E) : ℕ → KState
  | 0 => (⟨cap, [(w0, dsObserve), (w1, dsObserve), (ms 0, dsObserve), (ms 1, dsObserve)]⟩ : Fs).perm
  | j + 1 => (⟨capOf (ofmQ cap w0 w1 ms j), [(ms (4 * j + 2), dsObserve), (ms (4 * j + 3), dsObserve),
      (ms (4 * j + 4), dsObserve), (ms (4 * j + 5), dsObserve)]⟩ : Fs).perm

theorem ofm_absorb (cap : List E) (w0 w1 : E) (ms : ℕ → E) :
    ∀ m, (⟨cap, [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).absorbAll
        ((List.range (4 * (m + 1))).map ms) dsObserve =
      ⟨capOf (ofmQ cap w0 w1 ms m), [(ms (4 * m + 2), dsObserve), (ms (4 * m + 3), dsObserve)]⟩
  | 0 => by
    rw [show (List.range (4 * (0 + 1))).map ms = [ms 0, ms 1, ms 2, ms 3] by simp [List.range_succ],
      absorbAll_four]
    rfl
  | m + 1 => by
    rw [show 4 * (m + 1 + 1) = 4 * (m + 1) + 4 by ring, List.range_add, List.map_append,
      absorbAll_append', ofm_absorb cap w0 w1 ms m]
    rw [show (List.map (fun x ↦ 4 * (m + 1) + x) (List.range 4)).map ms =
      [ms (4 * m + 4), ms (4 * m + 5), ms (4 * m + 6), ms (4 * m + 7)] by
        simp [List.range_succ]; ring_nf; simp,
      absorbAll_four]
    simp only [ofmQ]
    rw [show 4 * (m + 1) + 2 = 4 * m + 6 by ring, show 4 * (m + 1) + 3 = 4 * m + 7 by ring]

/-- Where message word `i` sits. -/
def msgV (i : ℕ) : ℕ := 12 + 53 * ((i + 2) / 4) + 10 * ((i + 2) % 4)

theorem msgV_block (j t : ℕ) (ht : t < 4) : msgV (4 * j + 2 + t) = 65 + 53 * j + 10 * t := by
  unfold msgV
  rw [show (4 * j + 2 + t + 2) / 4 = j + 1 by omega, show (4 * j + 2 + t + 2) % 4 = t by omega]
  ring

/-- What `ofmNext` asks. -/
theorem holds_ofmNext (i b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (ofmNext i b) next kret ↔
      (LoadHolds rd (σ (.n 7)) i (σ (.n b)) ∧ FsPackOk σ (.n b) (b + 1) dsObserve ∧
        LoadHolds rd (σ (.n 8)) i (σ (.n b))) ∧ next := by
  rw [ofmNext, holdsList_append, holds_fsNextT]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  tauto

/-- What block `j + 1` asks. -/
theorem holds_ofmBlock (j : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (ofmBlock j) True kret ↔
      (∀ t < 4, LoadHolds rd (σ (.n 7)) (4 * j + 2 + t) (σ (.n (65 + 53 * j + 10 * t))) ∧
        FsPackOk σ (.n (65 + 53 * j + 10 * t)) (65 + 53 * j + 10 * t + 1) dsObserve ∧
        LoadHolds rd (σ (.n 8)) (4 * j + 2 + t) (σ (.n (65 + 53 * j + 10 * t)))) ∧
      (Atom.keccak (ofmRate (65 + 53 * j) ++ capIns (52 + 53 * j)) (ofmRun (105 + 53 * j))
        false false).Holds rd σ := by
  simp only [ofmBlock, holdsList_append, holds_ofmNext, keccakA, Stmt.HoldsList, Stmt.Holds,
    and_true]
  constructor
  · rintro ⟨h0, h1, h2, h3, hk⟩
    refine ⟨fun t ht => ?_, hk⟩
    interval_cases t
    · simpa using h0
    · simpa [show 4 * j + 2 + 1 = 4 * j + 3 by ring, show 65 + 53 * j + 10 * 1 = 75 + 53 * j by ring]
        using h1
    · simpa [show 4 * j + 2 + 2 = 4 * j + 4 by ring, show 65 + 53 * j + 10 * 2 = 85 + 53 * j by ring]
        using h2
    · simpa [show 4 * j + 2 + 3 = 4 * j + 5 by ring, show 65 + 53 * j + 10 * 3 = 95 + 53 * j by ring]
        using h3
  · rintro ⟨h, hk⟩
    refine ⟨by simpa using h 0 (by omega), ?_, ?_, ?_, hk⟩
    · simpa [show 4 * j + 2 + 1 = 4 * j + 3 by ring, show 65 + 53 * j + 10 * 1 = 75 + 53 * j by ring]
        using h 1 (by omega)
    · simpa [show 4 * j + 2 + 2 = 4 * j + 4 by ring, show 65 + 53 * j + 10 * 2 = 85 + 53 * j by ring]
        using h 2 (by omega)
    · simpa [show 4 * j + 2 + 3 = 4 * j + 5 by ring, show 65 + 53 * j + 10 * 3 = 95 + 53 * j by ring]
        using h 3 (by omega)

/-- A `KECCAK` atom writing thirteen consecutive values. -/
theorem keccak_ofmRun {ins : List V} {b : ℕ}
    (h : (Atom.keccak ins (ofmRun b) false false).Holds rd σ) :
    AllCanonical (ins.map σ) ∧
      ∀ c : Fin 13, σ (.n (b + c.val)) = cellsOfState (permOf (ins.map σ)) false c := by
  obtain ⟨-, -, hcan, hout⟩ := keccakA_perm h
  refine ⟨hcan, fun c => ?_⟩
  have := outs_eq hout c (by simp [ofmRun])
  simpa [ofmRun] using this

/-- The nine parameters. -/
abbrev ofmParams : List V := [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8]

/-- Four packed waiting scalars and a capacity are a sponge's permutation input. -/
theorem perm_four {x0 x1 x2 x3 c0 c1 c2 c3 c4 : E} {a0 a1 a2 a3 b0 b1 b2 b3 : E} {cap : List E}
    (h0 : (a0, b0) = Keccak.scalarCells x0 dsObserve) (h1 : (a1, b1) = Keccak.scalarCells x1 dsObserve)
    (h2 : (a2, b2) = Keccak.scalarCells x2 dsObserve) (h3 : (a3, b3) = Keccak.scalarCells x3 dsObserve)
    (hc : cap = [c0, c1, c2, c3, c4]) :
    permOf [a0, b0, a1, b1, a2, b2, a3, b3, c0, c1, c2, c3, c4] =
      (⟨cap, [(x0, dsObserve), (x1, dsObserve), (x2, dsObserve), (x3, dsObserve)]⟩ : Fs).perm := by
  rw [perm_eq_cells _ (by simp)]
  subst hc
  simp only [pendCells, List.flatMap_cons, List.flatMap_nil, ← h0, ← h1, ← h2, ← h3]
  rfl

/-- **`opening_final_message` at `4m` words is sound.** -/
theorem ofm_sound {name : String} {f : Fn} (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 8)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = ofmParams)
    (hbody : f.body = ofmBody m) (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) : MeaningOpeningFinalMessage (4 * m) rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, ofmBody] at h
  simp only [holdsList_append, holdsList_range_flatten (m - 1) ofmBlock (fun _ => rfl),
    holds_ofmBlock, holds_ofmNext, holds_fsPackT, keccakA, Stmt.HoldsList, Stmt.Holds,
    List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, h9, h10, h11, h12, h13, hp0, hp1, ⟨l0, q0, s0⟩, ⟨l1, q1, s1⟩, hK0, hblocks,
    ⟨lf0, qf0, sf0⟩, ⟨lf1, qf1, sf1⟩, lN, hpN, z42, z43, hKF, c57, c58, c59, c60, c61, c62, k63,
    m64, k65, m66, c67, hret⟩ := h
  subst hp
  have h9 : σ (.n 9) = σ (.n 0) := h9
  have h10 : σ (.n 10) = σ (.n 1) := h10
  have h11 : σ (.n 11) = σ (.n 2) := h11
  have h12 : σ (.n 12) = σ (.n 3) := h12
  have h13 : σ (.n 13) = σ (.n 4) := h13
  have z42 : σ (.n (42 + 53 * m)) = 0 := by rw [← word_zero]; exact z42
  have z43 : σ (.n (43 + 53 * m)) = 0 := by rw [← word_zero]; exact z43
  have lN : LoadHolds rd (σ (.n 7)) (4 * m) (σ (.n (32 + 53 * m))) := lN
  set cap := [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] with hcap
  let ms : ℕ → E := fun i ↦ σ (.n (msgV i))
  have hms : ∀ j t, t < 4 → ms (4 * j + 2 + t) = σ (.n (65 + 53 * j + 10 * t)) := fun j t ht ↦ by
    show σ (.n (msgV _)) = _
    rw [msgV_block j t ht]
  set Q := ofmQ cap (σ (.n 5)) (σ (.n 6)) ms with hQ
  obtain ⟨hcan0, hout0⟩ := keccak_ofmRun hK0
  have hQ0 : ∀ c : Fin 13, σ (.n (52 + c.val)) = cellsOfState (Q 0) false c := by
    intro c
    rw [hout0 c]
    refine congrArg (fun S ↦ cellsOfState S false c) ?_
    have e20 : (σ (.n 20), σ (.n 22)) = Keccak.scalarCells (σ (.n 5)) dsObserve :=
      fsPackT_cells hp0 (hcan0 (σ (.n 20)) (by simp))
    have e29 : (σ (.n 29), σ (.n 31)) = Keccak.scalarCells (σ (.n 6)) dsObserve :=
      fsPackT_cells hp1 (hcan0 (σ (.n 29)) (by simp))
    have e39 : (σ (.n 39), σ (.n 41)) = Keccak.scalarCells (ms 0) dsObserve :=
      fsPackT_cells q0 (hcan0 (σ (.n 39)) (by simp))
    have e49 : (σ (.n 49), σ (.n 51)) = Keccak.scalarCells (ms 1) dsObserve :=
      fsPackT_cells q1 (hcan0 (σ (.n 49)) (by simp))
    simp only [List.map_cons, List.map_nil, h9, h10, h11, h12, h13]
    exact perm_four e20 e29 e39 e49 hcap
  have hQs : ∀ j, j < m → ∀ c : Fin 13, σ (.n (52 + 53 * j + c.val)) = cellsOfState (Q j) false c := by
    intro j
    induction j with
    | zero => intro _ c; simpa using hQ0 c
    | succ j ih =>
      intro hj c
      obtain ⟨hb, hK⟩ := hblocks j (by omega)
      obtain ⟨hcan, hout⟩ := keccak_ofmRun hK
      rw [show 52 + 53 * (j + 1) + c.val = 105 + 53 * j + c.val by ring, hout c]
      refine congrArg (fun S ↦ cellsOfState S false c) ?_
      have ep : ∀ t, t < 4 → (σ (.n (65 + 53 * j + 10 * t + 7)), σ (.n (65 + 53 * j + 10 * t + 9))) =
          Keccak.scalarCells (ms (4 * j + 2 + t)) dsObserve := fun t ht ↦ by
        rw [hms j t ht]
        exact fsPackT_cells (hb t ht).2.1 (hcan _ (by
          interval_cases t <;> simp [ofmRate, capIns]))
      have e0 := ep 0 (by omega)
      have e1 := ep 1 (by omega)
      have e2 := ep 2 (by omega)
      have e3 := ep 3 (by omega)
      simp only [Nat.add_zero, Nat.mul_zero, Nat.mul_one] at e0 e1 e2 e3
      have i8 : σ (.n (52 + 53 * j + 8)) = cellsOfState (Q j) false 8 := ih (by omega) 8
      have i9 : σ (.n (52 + 53 * j + 9)) = cellsOfState (Q j) false 9 := ih (by omega) 9
      have i10 : σ (.n (52 + 53 * j + 10)) = cellsOfState (Q j) false 10 := ih (by omega) 10
      have i11 : σ (.n (52 + 53 * j + 11)) = cellsOfState (Q j) false 11 := ih (by omega) 11
      have i12 : σ (.n (52 + 53 * j + 12)) = cellsOfState (Q j) false 12 := ih (by omega) 12
      simp only [ofmRate, capIns, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
        i8, i9, i10, i11, i12]
      rw [hQ, ofmQ, ← hQ]
      rw [show 4 * j + 3 = 4 * j + 2 + 1 by ring, show 4 * j + 4 = 4 * j + 2 + 2 by ring,
        show 4 * j + 5 = 4 * j + 2 + 3 by ring]
      refine perm_four e0 ?_ ?_ ?_ rfl
      · rw [← e1]
      · rw [← e2]
      · rw [← e3]
  -- the final permutation
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hmsF0 : ms (4 * (m' + 1) - 2) = σ (.n (12 + 53 * (m' + 1))) := by
    rw [show 4 * (m' + 1) - 2 = 4 * m' + 2 + 0 by omega, hms m' 0 (by omega)]
    congr 2; ring
  have hmsF1 : ms (4 * (m' + 1) - 1) = σ (.n (22 + 53 * (m' + 1))) := by
    rw [show 4 * (m' + 1) - 1 = 4 * m' + 2 + 1 by omega, hms m' 1 (by omega)]
    congr 2; ring
  set nonce := σ (.n (32 + 53 * (m' + 1)))
  let msl := (List.range (4 * (m' + 1))).map ms
  have hs : ((⟨cap, [(σ (.n 5), dsObserve), (σ (.n 6), dsObserve)]⟩ : Fs).absorbAll msl
      dsObserve).absorb nonce dsPowNonce =
      ⟨capOf (Q m'), [(ms (4 * m' + 2), dsObserve), (ms (4 * m' + 3), dsObserve),
        (nonce, dsPowNonce)]⟩ := by
    simp only [msl]
    rw [ofm_absorb]
    simp [Fs.absorb, rateScalars]
    try rfl
  obtain ⟨hcanF, houtF⟩ := keccak_ofmRun hKF
  have eF0 : (σ (.n (19 + 53 * (m' + 1))), σ (.n (21 + 53 * (m' + 1)))) =
      Keccak.scalarCells (ms (4 * m' + 2)) dsObserve := by
    rw [show 4 * m' + 2 = 4 * (m' + 1) - 2 by omega, hmsF0]
    have hc : IsCanonical128 (σ (.n (12 + 53 * (m' + 1) + 1 + 6))) := by
      rw [show 12 + 53 * (m' + 1) + 1 + 6 = 19 + 53 * (m' + 1) by ring]; exact hcanF _ (by simp)
    have := fsPackT_cells qf0 hc
    rwa [show 12 + 53 * (m' + 1) + 1 + 6 = 19 + 53 * (m' + 1) by ring,
      show 12 + 53 * (m' + 1) + 1 + 8 = 21 + 53 * (m' + 1) by ring] at this
  have eF1 : (σ (.n (29 + 53 * (m' + 1))), σ (.n (31 + 53 * (m' + 1)))) =
      Keccak.scalarCells (ms (4 * m' + 3)) dsObserve := by
    rw [show 4 * m' + 3 = 4 * (m' + 1) - 1 by omega, hmsF1]
    have hc : IsCanonical128 (σ (.n (22 + 53 * (m' + 1) + 1 + 6))) := by
      rw [show 22 + 53 * (m' + 1) + 1 + 6 = 29 + 53 * (m' + 1) by ring]; exact hcanF _ (by simp)
    have := fsPackT_cells qf1 hc
    rwa [show 22 + 53 * (m' + 1) + 1 + 6 = 29 + 53 * (m' + 1) by ring,
      show 22 + 53 * (m' + 1) + 1 + 8 = 31 + 53 * (m' + 1) by ring] at this
  have eFN : (σ (.n (39 + 53 * (m' + 1))), σ (.n (41 + 53 * (m' + 1)))) =
      Keccak.scalarCells nonce dsPowNonce := by
    have hc : IsCanonical128 (σ (.n (33 + 53 * (m' + 1) + 6))) := by
      rw [show 33 + 53 * (m' + 1) + 6 = 39 + 53 * (m' + 1) by ring]; exact hcanF _ (by simp)
    have := fsPackT_cells hpN hc
    rwa [show 33 + 53 * (m' + 1) + 6 = 39 + 53 * (m' + 1) by ring,
      show 33 + 53 * (m' + 1) + 8 = 41 + 53 * (m' + 1) by ring] at this
  have hSF : permOf ((([.n (19 + 53 * (m' + 1)), .n (21 + 53 * (m' + 1)), .n (29 + 53 * (m' + 1)),
      .n (31 + 53 * (m' + 1)), .n (39 + 53 * (m' + 1)), .n (41 + 53 * (m' + 1)),
      .n (42 + 53 * (m' + 1)), .n (43 + 53 * (m' + 1))] : List V) ++ capIns (53 * (m' + 1) - 1)).map σ) =
      (((⟨cap, [(σ (.n 5), dsObserve), (σ (.n 6), dsObserve)]⟩ : Fs).absorbAll msl
        dsObserve).absorb nonce dsPowNonce).perm := by
    rw [hs, perm_eq_cells _ (by simp)]
    have i8 : σ (.n (53 * (m' + 1) - 1 + 8)) = cellsOfState (Q m') false 8 := by
      rw [show 53 * (m' + 1) - 1 + 8 = 52 + 53 * m' + 8 by omega]; exact hQs m' (by omega) 8
    have i9 : σ (.n (53 * (m' + 1) - 1 + 9)) = cellsOfState (Q m') false 9 := by
      rw [show 53 * (m' + 1) - 1 + 9 = 52 + 53 * m' + 9 by omega]; exact hQs m' (by omega) 9
    have i10 : σ (.n (53 * (m' + 1) - 1 + 10)) = cellsOfState (Q m') false 10 := by
      rw [show 53 * (m' + 1) - 1 + 10 = 52 + 53 * m' + 10 by omega]; exact hQs m' (by omega) 10
    have i11 : σ (.n (53 * (m' + 1) - 1 + 11)) = cellsOfState (Q m') false 11 := by
      rw [show 53 * (m' + 1) - 1 + 11 = 52 + 53 * m' + 11 by omega]; exact hQs m' (by omega) 11
    have i12 : σ (.n (53 * (m' + 1) - 1 + 12)) = cellsOfState (Q m') false 12 := by
      rw [show 53 * (m' + 1) - 1 + 12 = 52 + 53 * m' + 12 by omega]; exact hQs m' (by omega) 12
    simp only [capIns, List.cons_append, List.nil_append, List.map_cons, List.map_nil, i8, i9, i10,
      i11, i12, z42, z43, pendCells, List.flatMap_cons, List.flatMap_nil, ← eF0, ← eF1, ← eFN]
    rfl
  have oF : ∀ c : Fin 13, σ (.n (44 + 53 * (m' + 1) + c.val)) =
      cellsOfState (((⟨cap, [(σ (.n 5), dsObserve), (σ (.n 6), dsObserve)]⟩ : Fs).absorbAll msl
        dsObserve).absorb nonce dsPowNonce).perm false c := fun c ↦ by rw [houtF c, hSF]
  -- the loads
  have hall : ∀ k, k < 4 * (m' + 1) → LoadHolds rd (σ (.n 7)) k (ms k) ∧
      LoadHolds rd (σ (.n 8)) k (ms k) := by
    intro k hk
    by_cases k0 : k = 0
    · subst k0; exact ⟨l0, s0⟩
    by_cases k1 : k = 1
    · subst k1; exact ⟨l1, s1⟩
    by_cases kf0 : k = 4 * (m' + 1) - 2
    · subst kf0; rw [hmsF0]; exact ⟨lf0, sf0⟩
    by_cases kf1 : k = 4 * (m' + 1) - 1
    · subst kf1; rw [hmsF1]; exact ⟨lf1, sf1⟩
    obtain ⟨j, t, ht, rfl⟩ : ∃ j t, t < 4 ∧ k = 4 * j + 2 + t :=
      ⟨(k - 2) / 4, (k - 2) % 4, by omega, by omega⟩
    have hj : j < m' + 1 - 1 := by omega
    obtain ⟨hb, -⟩ := hblocks j hj
    rw [hms j t ht]
    exact ⟨(hb t ht).1, (hb t ht).2.2⟩
  refine ⟨?_, msl, nonce, by simp [msl], ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · rw [← h9]; exact hcan0 _ (by simp)
    · rw [← h10]; exact hcan0 _ (by simp)
    · rw [← h11]; exact hcan0 _ (by simp)
    · rw [← h12]; exact hcan0 _ (by simp)
    · rw [← h13]; exact hcan0 _ (by simp)
  · intro k hk
    simp only [msl, List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil] at hk
    by_cases hkn : k < 4 * (m' + 1)
    · rw [List.getElem_append_left (by simpa [msl] using hkn)]
      simpa [msl] using (hall k hkn).1
    · rw [List.getElem_append_right (by simp [msl]; omega)]
      have : k = 4 * (m' + 1) := by omega
      subst this
      simpa [msl] using lN
  · intro k hk
    simp only [msl, List.length_map, List.length_range] at hk
    simpa [msl] using (hall k hk).2
  · have c57 : σ (.n (57 + 53 * (m' + 1))) = σ (.n (44 + 53 * (m' + 1))) := c57
    have c58 : σ (.n (58 + 53 * (m' + 1))) = σ (.n (52 + 53 * (m' + 1))) := c58
    have c59 : σ (.n (59 + 53 * (m' + 1))) = σ (.n (53 + 53 * (m' + 1))) := c59
    have c60 : σ (.n (60 + 53 * (m' + 1))) = σ (.n (54 + 53 * (m' + 1))) := c60
    have c61 : σ (.n (61 + 53 * (m' + 1))) = σ (.n (55 + 53 * (m' + 1))) := c61
    have c62 : σ (.n (62 + 53 * (m' + 1))) = σ (.n (56 + 53 * (m' + 1))) := c62
    have k63 : σ (.n (63 + 53 * (m' + 1))) = word (2 ^ (4 * (m' + 1))) 0 0 := k63
    have m64 : σ (.n (64 + 53 * (m' + 1))) = σ (.n 7) * σ (.n (63 + 53 * (m' + 1))) := m64
    have k65 : σ (.n (65 + 53 * (m' + 1))) = word 2 0 0 := k65
    have m66 : σ (.n (66 + 53 * (m' + 1))) =
      σ (.n (64 + 53 * (m' + 1))) * σ (.n (65 + 53 * (m' + 1))) := m66
    have c67 : σ (.n (67 + 53 * (m' + 1))) = σ (.n (32 + 53 * (m' + 1))) := c67
    have o0 := oF 0
    have o8 := oF 8
    have o9 := oF 9
    have o10 := oF 10
    have o11 := oF 11
    have o12 := oF 12
    simp only [Fin.isValue, Fin.val_zero, Nat.add_zero] at o0
    rw [show 44 + 53 * (m' + 1) + (8 : Fin 13).val = 52 + 53 * (m' + 1) by simp; ring] at o8
    rw [show 44 + 53 * (m' + 1) + (9 : Fin 13).val = 53 + 53 * (m' + 1) by simp; ring] at o9
    rw [show 44 + 53 * (m' + 1) + (10 : Fin 13).val = 54 + 53 * (m' + 1) by simp; ring] at o10
    rw [show 44 + 53 * (m' + 1) + (11 : Fin 13).val = 55 + 53 * (m' + 1) by simp; ring] at o11
    rw [show 44 + 53 * (m' + 1) + (12 : Fin 13).val = 56 + 53 * (m' + 1) by simp; ring] at o12
    rw [← hret, c57, c58, c59, c60, c61, c62, m66, m64, k63, k65, c67, o0, o8, o9, o10, o11, o12,
      word_two_pow (by omega), word_gen, mul_assoc, ← pow_succ]
    rfl


set_option maxRecDepth 100000 in
theorem core458_body : Fn.body Data.core458 = ofmBody 1 := stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem core477_body : Fn.body Data.core477 = ofmBody 2 := stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem core423_body : Fn.body Data.core423 = ofmBody 4 := stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem core440_body : Fn.body Data.core440 = ofmBody 8 := stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
