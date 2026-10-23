/-
  LeanVM.Guest.B1.Sumcheck.Batch

  B1 for `batch_sumcheck`: the claim-batching sumcheck, one generic argument over the rounds.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Meaning
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run

/-!
# `batch_sumcheck` (G:1007-1022, TRIAGE #32)

Its body at `n` rounds (`bsBody n`): the capacity copied into `8 .. 12`; round `0` (`bsRound0`):
`g(1)`, `g(∞)` read at `msgs[0]`, `msgs[1]` and packed (`fsNextT` from `13`, `23`), the pad run
`33 .. 37`, the permutation into `38 .. 50`, its challenge (at `57`) stored at `point[0]`, the fold
(`58 .. 64`); round `j + 1` (`bsRound j`): the same from `65 + 47 j`, its permutation into
`85 + 47 j`, reading the zero run `34 .. 37`; the final capacity and claim copied and returned.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Thirteen consecutive values. -/
def bsRun13 (b : ℕ) : List V := (List.range 13).map fun i ↦ .n (b + i)

/-- The fold of round `r` whose permutation writes from `o`, its claim `c`, its words at `b`,
`b + 10`. -/
def bsFold (o c b : ℕ) (r : ℕ) : List Stmt :=
  [.atom (.load (.n (o + 19)) (.n 7) r),
    .atom (.add (.n (o + 20)) (.n c) (.n b)), .atom (.add (.n (o + 21)) (.n (o + 20)) (.n b)),
    .atom (.add (.n (o + 22)) (.n (o + 21)) (.n (b + 10))),
    .atom (.mul (.n (o + 23)) (.n (b + 10)) (.n (o + 19))),
    .atom (.add (.n (o + 24)) (.n (o + 23)) (.n (o + 22))),
    .atom (.mul (.n (o + 25)) (.n (o + 24)) (.n (o + 19))),
    .atom (.add (.n (o + 26)) (.n (o + 25)) (.n (o + 20)))]

/-- Round `0`. -/
def bsRound0 : List Stmt :=
  fsNextT (.n 5) 0 13 ++ fsNextT (.n 5) 1 23 ++
  [.atom (.const (.n 33) (word 1 0 0)), .atom (.const (.n 34) (word 0 0 0)),
    .atom (.const (.n 35) (word 0 0 0)), .atom (.const (.n 36) (word 0 0 0)),
    .atom (.const (.n 37) (word 0 0 0)),
    keccakA [.n 20, .n 22, .n 30, .n 32, .n 34, .n 35, .n 36, .n 37, .n 8, .n 9, .n 10, .n 11, .n 12]
      (bsRun13 38)] ++
  challengeT (.n 38) (.n 39) 51 ++ bsFold 38 6 13 0

/-- Round `j + 1`. -/
def bsRound (j : ℕ) : List Stmt :=
  fsNextT (.n 5) (2 * j + 2) (65 + 47 * j) ++ fsNextT (.n 5) (2 * j + 3) (75 + 47 * j) ++
  [keccakA [.n (72 + 47 * j), .n (74 + 47 * j), .n (82 + 47 * j), .n (84 + 47 * j), .n 34, .n 35,
      .n 36, .n 37, .n (46 + 47 * j), .n (47 + 47 * j), .n (48 + 47 * j), .n (49 + 47 * j),
      .n (50 + 47 * j)] (bsRun13 (85 + 47 * j))] ++
  challengeT (.n (85 + 47 * j)) (.n (86 + 47 * j)) (98 + 47 * j) ++
  bsFold (85 + 47 * j) (64 + 47 * j) (65 + 47 * j) (j + 1)

/-- The expansion of `batch_sumcheck` at `n ≥ 1` rounds. -/
def bsBody (n : ℕ) : List Stmt :=
  [.atom (.copy (.n 8) (.n 0)), .atom (.copy (.n 9) (.n 1)), .atom (.copy (.n 10) (.n 2)),
    .atom (.copy (.n 11) (.n 3)), .atom (.copy (.n 12) (.n 4))] ++
  bsRound0 ++ ((List.range (n - 1)).map bsRound).flatten ++
  [.atom (.copy (.n (18 + 47 * n)) (.n (38 + 47 * (n - 1) + 8))),
    .atom (.copy (.n (19 + 47 * n)) (.n (38 + 47 * (n - 1) + 9))),
    .atom (.copy (.n (20 + 47 * n)) (.n (38 + 47 * (n - 1) + 10))),
    .atom (.copy (.n (21 + 47 * n)) (.n (38 + 47 * (n - 1) + 11))),
    .atom (.copy (.n (22 + 47 * n)) (.n (38 + 47 * (n - 1) + 12))),
    .atom (.copy (.n (23 + 47 * n)) (.n (38 + 47 * (n - 1) + 26))),
    .ret [.n (18 + 47 * n), .n (19 + 47 * n), .n (20 + 47 * n), .n (21 + 47 * n), .n (22 + 47 * n),
      .n (23 + 47 * n)]]

/-! ## The rounds as a sequence -/

/-- The claim and the sponge after the first `j` rounds of `bsRun` on the words `g`. -/
def bsSt (g : ℕ → E × E) (claim : E) (s : Fs) : ℕ → E × Fs
  | 0 => (claim, s)
  | j + 1 =>
    let st := bsSt g claim s j
    let r := ((st.2.absorb (g j).1 dsObserve).absorb (g j).2 dsObserve).squeeze
    let g0 := st.1 + (g j).1
    (((g j).2 * r.1 + (g0 + (g j).1 + (g j).2)) * r.1 + g0, r.2)

/-- Round `j`'s permutation. -/
def bsP (g : ℕ → E × E) (claim : E) (s : Fs) (j : ℕ) : KState :=
  (((bsSt g claim s j).2.absorb (g j).1 dsObserve).absorb (g j).2 dsObserve).perm

theorem bsSt_succ_shift (g : ℕ → E × E) (claim : E) (s : Fs) :
    ∀ j, bsSt g claim s (j + 1) =
      bsSt (fun i ↦ g (i + 1)) (bsSt g claim s 1).1 (bsSt g claim s 1).2 j
  | 0 => rfl
  | j + 1 => by
    rw [bsSt, bsSt_succ_shift g claim s j]
    rfl

theorem range_succ_map {α : Type} (f : ℕ → α) (n : ℕ) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map fun i ↦ f (i + 1) := by
  simp [List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- Round `j`'s challenge. -/
def bsChal (g : ℕ → E × E) (claim : E) (s : Fs) (j : ℕ) : E :=
  (((bsSt g claim s j).2.absorb (g j).1 dsObserve).absorb (g j).2 dsObserve).squeeze.1

theorem bsChal_shift (g : ℕ → E × E) (claim : E) (s : Fs) (j : ℕ) :
    bsChal g claim s (j + 1) =
      bsChal (fun i ↦ g (i + 1)) (bsSt g claim s 1).1 (bsSt g claim s 1).2 j := by
  rw [bsChal, bsChal, bsSt_succ_shift g claim s j]

theorem bsRun_cons1 (g : ℕ → E × E) (L : List (E × E)) (claim : E) (s : Fs) :
    (bsRun (g 0 :: L) claim s).1.1 =
      bsChal g claim s 0 :: (bsRun L (bsSt g claim s 1).1 (bsSt g claim s 1).2).1.1 := rfl

theorem bsRun_cons2 (g : ℕ → E × E) (L : List (E × E)) (claim : E) (s : Fs) :
    (bsRun (g 0 :: L) claim s).1.2 = (bsRun L (bsSt g claim s 1).1 (bsSt g claim s 1).2).1.2 := rfl

theorem bsRun_cons3 (g : ℕ → E × E) (L : List (E × E)) (claim : E) (s : Fs) :
    (bsRun (g 0 :: L) claim s).2 = (bsRun L (bsSt g claim s 1).1 (bsSt g claim s 1).2).2 := rfl

theorem bsRun_range1 : ∀ (n : ℕ) (g : ℕ → E × E) (claim : E) (s : Fs),
    (bsRun ((List.range n).map g) claim s).1.1 = (List.range n).map (bsChal g claim s)
  | 0, _, _, _ => rfl
  | n + 1, g, claim, s => by
    rw [range_succ_map, bsRun_cons1, bsRun_range1 n, range_succ_map]
    exact congrArg (List.cons (bsChal g claim s 0))
      (List.map_congr_left fun i _ ↦ (bsChal_shift g claim s i).symm)

theorem bsRun_range2 : ∀ (n : ℕ) (g : ℕ → E × E) (claim : E) (s : Fs),
    (bsRun ((List.range n).map g) claim s).1.2 = (bsSt g claim s n).1
  | 0, _, _, _ => rfl
  | n + 1, g, claim, s => by
    rw [range_succ_map, bsRun_cons2, bsRun_range2 n, bsSt_succ_shift g claim s n]

theorem bsRun_range3 : ∀ (n : ℕ) (g : ℕ → E × E) (claim : E) (s : Fs),
    (bsRun ((List.range n).map g) claim s).2 = (bsSt g claim s n).2
  | 0, _, _, _ => rfl
  | n + 1, g, claim, s => by
    rw [range_succ_map, bsRun_cons3, bsRun_range3 n, bsSt_succ_shift g claim s n]

theorem absorb2 (cap : List E) (a b : E) :
    ((⟨cap, []⟩ : Fs).absorb a dsObserve).absorb b dsObserve = ⟨cap, [(a, dsObserve), (b, dsObserve)]⟩ := by
  simp [Fs.absorb, rateScalars]

theorem bsSt_empty (g : ℕ → E × E) (claim : E) (cap : List E) :
    ∀ j, (bsSt g claim ⟨cap, []⟩ j).2 = ⟨(bsSt g claim ⟨cap, []⟩ j).2.cap, []⟩
  | 0 => rfl
  | _ + 1 => rfl

theorem bsSt_cap_succ (g : ℕ → E × E) (claim : E) (cap : List E) (j : ℕ) :
    (bsSt g claim ⟨cap, []⟩ (j + 1)).2.cap = capOf (bsP g claim ⟨cap, []⟩ j) := rfl

/-- Round `j`'s permutation, its cells written out. -/
theorem bsP_eq (g : ℕ → E × E) (claim : E) (cap : List E) (j : ℕ) :
    bsP g claim ⟨cap, []⟩ j = permOf (pendCells [((g j).1, dsObserve), ((g j).2, dsObserve)] ++
      [0, 0, 0, 0] ++ (bsSt g claim ⟨cap, []⟩ j).2.cap) := by
  rw [bsP, bsSt_empty, absorb2, perm_eq_cells _ (by simp)]
  rfl

/-! ## Soundness -/

/-- What a round's fold asks. -/
def BsFoldOk (rd : Reader) (σ : Val) (o c b r : ℕ) : Prop :=
  LoadHolds rd (σ (.n 7)) r (σ (.n (o + 19))) ∧ σ (.n (o + 20)) = σ (.n c) + σ (.n b) ∧
    σ (.n (o + 21)) = σ (.n (o + 20)) + σ (.n b) ∧
    σ (.n (o + 22)) = σ (.n (o + 21)) + σ (.n (b + 10)) ∧
    σ (.n (o + 23)) = σ (.n (b + 10)) * σ (.n (o + 19)) ∧
    σ (.n (o + 24)) = σ (.n (o + 23)) + σ (.n (o + 22)) ∧
    σ (.n (o + 25)) = σ (.n (o + 24)) * σ (.n (o + 19)) ∧
    σ (.n (o + 26)) = σ (.n (o + 25)) + σ (.n (o + 20))

theorem holds_bsFold (o c b r : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (bsFold o c b r) next kret ↔ BsFoldOk rd σ o c b r ∧ next := by
  simp only [bsFold, BsFoldOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_assoc]

/-- The fold's value. -/
theorem bsFold_value {o c b r : ℕ} (h : BsFoldOk rd σ o c b r) :
    σ (.n (o + 26)) = (σ (.n (b + 10)) * σ (.n (o + 19)) + (σ (.n c) + σ (.n b) + σ (.n b) +
      σ (.n (b + 10)))) * σ (.n (o + 19)) + (σ (.n c) + σ (.n b)) := by
  obtain ⟨-, h20, h21, h22, h23, h24, h25, h26⟩ := h
  rw [h26, h25, h24, h23, h22, h21, h20]

/-- What round `j + 1` asks. -/
theorem holds_bsRound (j : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (bsRound j) True kret ↔
      (LoadHolds rd (σ (.n 5)) (2 * j + 2) (σ (.n (65 + 47 * j))) ∧
        FsPackOk σ (.n (65 + 47 * j)) (65 + 47 * j + 1) dsObserve) ∧
      (LoadHolds rd (σ (.n 5)) (2 * j + 3) (σ (.n (75 + 47 * j))) ∧
        FsPackOk σ (.n (75 + 47 * j)) (75 + 47 * j + 1) dsObserve) ∧
      (Atom.keccak [.n (72 + 47 * j), .n (74 + 47 * j), .n (82 + 47 * j), .n (84 + 47 * j), .n 34,
        .n 35, .n 36, .n 37, .n (46 + 47 * j), .n (47 + 47 * j), .n (48 + 47 * j),
        .n (49 + 47 * j), .n (50 + 47 * j)] (bsRun13 (85 + 47 * j)) false false).Holds rd σ ∧
      ChallengeOk σ (.n (85 + 47 * j)) (.n (86 + 47 * j)) (98 + 47 * j) ∧
      BsFoldOk rd σ (85 + 47 * j) (64 + 47 * j) (65 + 47 * j) (j + 1) := by
  simp only [bsRound, keccakA, holdsList_append, holds_fsNextT, holds_challengeT, holds_bsFold,
    Stmt.HoldsList, Stmt.Holds, and_true]

theorem keccak_bsRun13 {ins : List V} {b : ℕ}
    (h : (Atom.keccak ins (bsRun13 b) false false).Holds rd σ) :
    AllCanonical (ins.map σ) ∧
      ∀ c : Fin 13, σ (.n (b + c.val)) = cellsOfState (permOf (ins.map σ)) false c := by
  obtain ⟨-, -, hcan, hout⟩ := keccakA_perm h
  refine ⟨hcan, fun c => ?_⟩
  have := outs_eq hout c (by simp [bsRun13])
  simpa [bsRun13] using this

theorem flatMap_pairs (g : ℕ → E × E) :
    ∀ n, ((List.range n).map g).flatMap (fun p ↦ [p.1, p.2]) =
      (List.range (2 * n)).map fun k ↦ if k % 2 = 0 then (g (k / 2)).1 else (g (k / 2)).2
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatMap_append, flatMap_pairs g n,
      show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_append, List.append_assoc, List.cons_append, List.nil_append]
    congr 2
    · simp only [show 2 * n % 2 = 0 by omega, show 2 * n / 2 = n by omega, ↓reduceIte]
    · simp only [show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega,
        one_ne_zero, ↓reduceIte]

/-- The eight parameters. -/
abbrev bsParams : List V := [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]

/-- Where round `j`'s words sit. -/
def bsG : ℕ → ℕ
  | 0 => 13
  | j + 1 => 65 + 47 * j

/-- Where the claim round `j` starts from sits. -/
def bsC : ℕ → ℕ
  | 0 => 6
  | j + 1 => 64 + 47 * j

theorem bs_sound {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = bsParams)
    (hbody : f.body = bsBody n) (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) : MeaningBatchSumcheck n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, bsBody, bsRound0] at h
  simp only [holdsList_append, holdsList_range_flatten (n - 1) bsRound (fun _ => rfl),
    holds_bsRound, holds_fsNextT, holds_challengeT, holds_bsFold, keccakA, Stmt.HoldsList,
    Stmt.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, h8, h9, h10, h11, h12, ⟨l0, p0⟩, ⟨l1, p1⟩, -, z34, z35, z36, z37, hK0, hch0, hf0,
    hrounds, c0, c1, c2, c3, c4, c5, hret⟩ := h
  subst hp
  have idx : ∀ a b, a = b → σ (.n a) = σ (.n b) := fun a b h ↦ by rw [h]
  have h8 : σ (.n 8) = σ (.n 0) := h8
  have h9 : σ (.n 9) = σ (.n 1) := h9
  have h10 : σ (.n 10) = σ (.n 2) := h10
  have h11 : σ (.n 11) = σ (.n 3) := h11
  have h12 : σ (.n 12) = σ (.n 4) := h12
  have z34 : σ (.n 34) = 0 := by rw [← word_zero]; exact z34
  have z35 : σ (.n 35) = 0 := by rw [← word_zero]; exact z35
  have z36 : σ (.n 36) = 0 := by rw [← word_zero]; exact z36
  have z37 : σ (.n 37) = 0 := by rw [← word_zero]; exact z37
  set g : ℕ → E × E := fun j ↦ (σ (.n (bsG j)), σ (.n (bsG j + 10))) with hg
  set cap0 := [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] with hcap0
  set St := bsSt g (σ (.n 6)) ⟨cap0, []⟩ with hSt
  set P := bsP g (σ (.n 6)) ⟨cap0, []⟩ with hP
  -- round j's facts
  have hR : ∀ j, j < n → (∀ c : Fin 13, σ (.n (38 + 47 * j + c.val)) = cellsOfState (P j) false c) →
      σ (.n (38 + 47 * j + 19)) = challengeOf (P j) ∧
        BsFoldOk rd σ (38 + 47 * j) (bsC j) (bsG j) j := by
    intro j hj hB
    cases j with
    | zero =>
      exact ⟨challengeT_value hch0 (hB 0) (hB 1), hf0⟩
    | succ i =>
      obtain ⟨-, -, -, hch, hf⟩ := hrounds i (by omega)
      have e : 38 + 47 * (i + 1) = 85 + 47 * i := by ring
      rw [e] at hB ⊢
      have b0 : σ (.n (85 + 47 * i)) = cellsOfState (P (i + 1)) false 0 := hB 0
      have b1 : σ (.n (86 + 47 * i)) = cellsOfState (P (i + 1)) false 1 :=
        (idx _ (85 + 47 * i + (1 : Fin 13).val) (by simp; ring)).trans (hB 1)
      refine ⟨(idx _ (98 + 47 * i + 6) (by ring)).trans (challengeT_value hch b0 b1), hf⟩
  have hAB : ∀ j, j < n → σ (.n (bsC j)) = (St j).1 ∧
      ∀ c : Fin 13, σ (.n (38 + 47 * j + c.val)) = cellsOfState (P j) false c := by
    intro j
    induction j with
    | zero =>
      intro hj
      refine ⟨rfl, fun c ↦ ?_⟩
      obtain ⟨hcan, hout⟩ := keccak_bsRun13 hK0
      rw [show 38 + 47 * 0 + c.val = 38 + c.val by ring, hout c]
      refine congrArg (fun S ↦ cellsOfState S false c) ?_
      have e20 : (σ (.n 20), σ (.n 22)) = Keccak.scalarCells (σ (.n 13)) dsObserve :=
        fsPackT_cells p0 (hcan (σ (.n 20)) (by simp))
      have e30 : (σ (.n 30), σ (.n 32)) = Keccak.scalarCells (σ (.n 23)) dsObserve :=
        fsPackT_cells p1 (hcan (σ (.n 30)) (by simp))
      rw [hP, bsP_eq]
      simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
        hg, bsG, ← e20, ← e30, z34, z35, z36, z37, h8, h9, h10, h11, h12]
      rfl
    | succ j ih =>
      intro hj
      obtain ⟨hA, hB⟩ := ih (by omega)
      obtain ⟨hr, hf⟩ := hR j (by omega) hB
      refine ⟨?_, fun c ↦ ?_⟩
      · rw [idx (bsC (j + 1)) (38 + 47 * j + 26) (by simp only [bsC]; ring), bsFold_value hf, hr, hA]
        rfl
      · obtain ⟨⟨-, q0⟩, ⟨-, q1⟩, hK, -, -⟩ := hrounds j (by omega)
        obtain ⟨hcan, hout⟩ := keccak_bsRun13 hK
        rw [idx _ (85 + 47 * j + c.val) (by ring), hout c]
        refine congrArg (fun S ↦ cellsOfState S false c) ?_
        have ea : (σ (.n (72 + 47 * j)), σ (.n (74 + 47 * j))) =
            Keccak.scalarCells (σ (.n (65 + 47 * j))) dsObserve := by
          have hc : IsCanonical128 (σ (.n (65 + 47 * j + 1 + 6))) := by
            rw [idx _ (72 + 47 * j) (by ring)]; exact hcan _ (by simp)
          have := fsPackT_cells q0 hc
          rwa [idx (65 + 47 * j + 1 + 6) (72 + 47 * j) (by ring),
            idx (65 + 47 * j + 1 + 8) (74 + 47 * j) (by ring)] at this
        have eb : (σ (.n (82 + 47 * j)), σ (.n (84 + 47 * j))) =
            Keccak.scalarCells (σ (.n (75 + 47 * j))) dsObserve := by
          have hc : IsCanonical128 (σ (.n (75 + 47 * j + 1 + 6))) := by
            rw [idx _ (82 + 47 * j) (by ring)]; exact hcan _ (by simp)
          have := fsPackT_cells q1 hc
          rwa [idx (75 + 47 * j + 1 + 6) (82 + 47 * j) (by ring),
            idx (75 + 47 * j + 1 + 8) (84 + 47 * j) (by ring)] at this
        have i8 : σ (.n (46 + 47 * j)) = cellsOfState (P j) false 8 :=
          (idx _ (38 + 47 * j + (8 : Fin 13).val) (by simp; ring)).trans (hB 8)
        have i9 : σ (.n (47 + 47 * j)) = cellsOfState (P j) false 9 :=
          (idx _ (38 + 47 * j + (9 : Fin 13).val) (by simp; ring)).trans (hB 9)
        have i10 : σ (.n (48 + 47 * j)) = cellsOfState (P j) false 10 :=
          (idx _ (38 + 47 * j + (10 : Fin 13).val) (by simp; ring)).trans (hB 10)
        have i11 : σ (.n (49 + 47 * j)) = cellsOfState (P j) false 11 :=
          (idx _ (38 + 47 * j + (11 : Fin 13).val) (by simp; ring)).trans (hB 11)
        have i12 : σ (.n (50 + 47 * j)) = cellsOfState (P j) false 12 :=
          (idx _ (38 + 47 * j + (12 : Fin 13).val) (by simp; ring)).trans (hB 12)
        have gb : g (j + 1) = (σ (.n (65 + 47 * j)), σ (.n (75 + 47 * j))) := by
          simp only [hg, bsG]
          rw [idx (65 + 47 * j + 10) (75 + 47 * j) (by ring)]
        rw [hP, bsP_eq, bsSt_cap_succ, ← hP, gb]
        simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          ← ea, ← eb, z34, z35, z36, z37, i8, i9, i10, i11, i12]
        rfl
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hAm, hBm⟩ := hAB m (by omega)
  obtain ⟨hrm, hfm⟩ := hR m (by omega) hBm
  have hAn : σ (.n (bsC (m + 1))) = (St (m + 1)).1 := by
    rw [idx (bsC (m + 1)) (38 + 47 * m + 26) (by simp only [bsC]; ring), bsFold_value hfm, hrm,
      hAm]
    rfl
  obtain ⟨hcan0, -⟩ := keccak_bsRun13 hK0
  refine ⟨?_, (List.range (m + 1)).map g, by simp, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rw [← h8]; exact hcan0 _ (by simp)
    · rw [← h9]; exact hcan0 _ (by simp)
    · rw [← h10]; exact hcan0 _ (by simp)
    · rw [← h11]; exact hcan0 _ (by simp)
    · rw [← h12]; exact hcan0 _ (by simp)
  · rw [flatMap_pairs]
    intro k hk
    simp only [List.length_map, List.length_range] at hk
    simp only [List.getElem_map, List.getElem_range]
    obtain ⟨j, e, he, rfl⟩ : ∃ j e : ℕ, e < 2 ∧ k = 2 * j + e := ⟨k / 2, k % 2, by omega, by omega⟩
    have hj : j < m + 1 := by omega
    interval_cases e
    · simp only [show (2 * j + 0) % 2 = 0 by omega, show (2 * j + 0) / 2 = j by omega, ↓reduceIte]
      cases j with
      | zero => exact l0
      | succ i =>
        obtain ⟨⟨l, -⟩, -, -⟩ := hrounds i (by omega)
        simpa [hg, bsG, show 2 * (i + 1) + 0 = 2 * i + 2 by ring] using l
    · simp only [show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega,
        one_ne_zero, ↓reduceIte]
      cases j with
      | zero => exact l1
      | succ i =>
        obtain ⟨-, ⟨l, -⟩, -, -⟩ := hrounds i (by omega)
        rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring]
        simp only [hg, bsG]
        rw [idx (65 + 47 * i + 10) (75 + 47 * i) (by ring)]
        exact l
  · simp only
    refine ⟨?_, ?_⟩
    · rw [bsRun_range1]
      intro k hk
      simp only [List.length_map, List.length_range] at hk
      simp only [List.getElem_map, List.getElem_range]
      obtain ⟨-, hB⟩ := hAB k hk
      obtain ⟨hr, hf⟩ := hR k hk hB
      have := hf.1
      rw [hr] at this
      exact this
    · rw [bsRun_range2, bsRun_range3, ← hAn, bsSt_cap_succ, ← hP, ← hret]
      have c0' : σ (.n (18 + 47 * (m + 1))) = cellsOfState (P m) false 8 := by
        rw [show σ (.n (18 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 8)) from c0]
        exact (idx _ (38 + 47 * m + (8 : Fin 13).val) (by simp)).trans (hBm 8)
      have c1' : σ (.n (19 + 47 * (m + 1))) = cellsOfState (P m) false 9 := by
        rw [show σ (.n (19 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 9)) from c1]
        exact (idx _ (38 + 47 * m + (9 : Fin 13).val) (by simp)).trans (hBm 9)
      have c2' : σ (.n (20 + 47 * (m + 1))) = cellsOfState (P m) false 10 := by
        rw [show σ (.n (20 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 10)) from c2]
        exact (idx _ (38 + 47 * m + (10 : Fin 13).val) (by simp)).trans (hBm 10)
      have c3' : σ (.n (21 + 47 * (m + 1))) = cellsOfState (P m) false 11 := by
        rw [show σ (.n (21 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 11)) from c3]
        exact (idx _ (38 + 47 * m + (11 : Fin 13).val) (by simp)).trans (hBm 11)
      have c4' : σ (.n (22 + 47 * (m + 1))) = cellsOfState (P m) false 12 := by
        rw [show σ (.n (22 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 12)) from c4]
        exact (idx _ (38 + 47 * m + (12 : Fin 13).val) (by simp)).trans (hBm 12)
      have c5' : σ (.n (23 + 47 * (m + 1))) = σ (.n (bsC (m + 1))) := by
        rw [show σ (.n (23 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 26)) from c5]
        exact idx _ _ (by simp only [bsC]; omega)
      rw [c0', c1', c2', c3', c4', c5']
      rfl


set_option maxRecDepth 100000 in
theorem core396_body : Fn.body Data.core396 = bsBody 23 := stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
