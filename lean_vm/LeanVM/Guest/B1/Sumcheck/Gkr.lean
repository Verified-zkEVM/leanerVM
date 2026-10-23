/-
  LeanVM.Guest.B1.Sumcheck.Gkr

  B1 for `gkr_rounds`: equality-mode sumcheck rounds between GKR round records.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Meaning
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run

/-!
# `gkr_rounds` (G:982-1004, TRIAGE #31)

Its body at `n` rounds (`gkBody n`): the record's capacity, cursor and claim loaded into `2 .. 8`;
round `q` (`gkRound q`, from `9 + 74 q`): four stream words read and packed, the permutation of
the four waiting with the previous capacity into `49 + 74 q`, its challenge (at `68 + 74 q`), the
previous coordinate `pt[q]`, the derived `c0`, the challenge stored at `pt[42 + q]`, the claim at
the challenge (at `82 + 74 q`); the next record's capacity, cursor and claim stored.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Thirteen consecutive values. -/
def gkRun13 (b : ℕ) : List V := (List.range 13).map fun i ↦ .n (b + i)

/-- Where round `q` reads the previous capacity. -/
def gkCapPrev : ℕ → ℕ
  | 0 => 2
  | q + 1 => 57 + 74 * q

/-- Round `q`. -/
def gkRound (q : ℕ) : List Stmt :=
  fsNextT (.n 7) (4 * q) (9 + 74 * q) ++ fsNextT (.n 7) (4 * q + 1) (19 + 74 * q) ++
  fsNextT (.n 7) (4 * q + 2) (29 + 74 * q) ++ fsNextT (.n 7) (4 * q + 3) (39 + 74 * q) ++
  [keccakA [.n (16 + 74 * q), .n (18 + 74 * q), .n (26 + 74 * q), .n (28 + 74 * q),
      .n (36 + 74 * q), .n (38 + 74 * q), .n (46 + 74 * q), .n (48 + 74 * q),
      .n (gkCapPrev q), .n (gkCapPrev q + 1), .n (gkCapPrev q + 2), .n (gkCapPrev q + 3),
      .n (gkCapPrev q + 4)] (gkRun13 (49 + 74 * q))] ++
  challengeT (.n (49 + 74 * q)) (.n (50 + 74 * q)) (62 + 74 * q) ++
  [.atom (.load (.n (69 + 74 * q)) (.n 1) q),
    .atom (.add (.n (70 + 74 * q)) (.n (9 + 74 * q)) (.n (19 + 74 * q))),
    .atom (.add (.n (71 + 74 * q)) (.n (70 + 74 * q)) (.n (29 + 74 * q))),
    .atom (.add (.n (72 + 74 * q)) (.n (71 + 74 * q)) (.n (39 + 74 * q))),
    .atom (.mul (.n (73 + 74 * q)) (.n (69 + 74 * q)) (.n (72 + 74 * q))),
    .atom (.add (.n (74 + 74 * q)) (.n (8 + 74 * q)) (.n (73 + 74 * q))),
    .atom (.load (.n (68 + 74 * q)) (.n 1) (42 + q)),
    .atom (.mul (.n (75 + 74 * q)) (.n (68 + 74 * q)) (.n (39 + 74 * q))),
    .atom (.add (.n (76 + 74 * q)) (.n (29 + 74 * q)) (.n (75 + 74 * q))),
    .atom (.mul (.n (77 + 74 * q)) (.n (68 + 74 * q)) (.n (76 + 74 * q))),
    .atom (.add (.n (78 + 74 * q)) (.n (19 + 74 * q)) (.n (77 + 74 * q))),
    .atom (.mul (.n (79 + 74 * q)) (.n (68 + 74 * q)) (.n (78 + 74 * q))),
    .atom (.add (.n (80 + 74 * q)) (.n (9 + 74 * q)) (.n (79 + 74 * q))),
    .atom (.mul (.n (81 + 74 * q)) (.n (68 + 74 * q)) (.n (80 + 74 * q))),
    .atom (.add (.n (82 + 74 * q)) (.n (74 + 74 * q)) (.n (81 + 74 * q)))]

/-- The expansion of `gkr_rounds` at `n ≥ 1` rounds. -/
def gkBody (n : ℕ) : List Stmt :=
  [.atom (.load (.n 2) (.n 0) 0), .atom (.load (.n 3) (.n 0) 862), .atom (.load (.n 4) (.n 0) 1724),
    .atom (.load (.n 5) (.n 0) 2586), .atom (.load (.n 6) (.n 0) 3448),
    .atom (.load (.n 7) (.n 0) 4310), .atom (.load (.n 8) (.n 0) 5172)] ++
  ((List.range n).map gkRound).flatten ++
  [.atom (.load (.n (57 + 74 * (n - 1))) (.n 0) n),
    .atom (.load (.n (58 + 74 * (n - 1))) (.n 0) (n + 862)),
    .atom (.load (.n (59 + 74 * (n - 1))) (.n 0) (n + 1724)),
    .atom (.load (.n (60 + 74 * (n - 1))) (.n 0) (n + 2586)),
    .atom (.load (.n (61 + 74 * (n - 1))) (.n 0) (n + 3448)),
    .atom (.const (.n (9 + 74 * n)) (word (2 ^ (4 * n)) 0 0)),
    .atom (.mul (.n (10 + 74 * n)) (.n 7) (.n (9 + 74 * n))),
    .atom (.load (.n (10 + 74 * n)) (.n 0) (n + 4310)),
    .atom (.load (.n (82 + 74 * (n - 1))) (.n 0) (n + 5172)),
    .ret []]

/-! ## The rounds as a sequence -/

/-- The claim and the sponge after the first `q` rounds of `gkrRun`, round `q` on the words
`Cf q` and the coordinate `ef q`. -/
def gkSt (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (s : Fs) : ℕ → E × Fs
  | 0 => (claim, s)
  | q + 1 =>
    let st := gkSt Cf ef claim s q
    let r := (st.2.absorbAll (Cf q) dsObserve).squeeze
    (polyEval ((st.1 + ef q * sumE (Cf q)) :: Cf q) r.1, r.2)

/-- Round `q`'s permutation. -/
def gkP (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (s : Fs) (q : ℕ) : KState :=
  ((gkSt Cf ef claim s q).2.absorbAll (Cf q) dsObserve).perm

theorem gkSt_shift (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (s : Fs) :
    ∀ q, gkSt Cf ef claim s (q + 1) =
      gkSt (fun i ↦ Cf (i + 1)) (fun i ↦ ef (i + 1)) (gkSt Cf ef claim s 1).1
        (gkSt Cf ef claim s 1).2 q
  | 0 => rfl
  | q + 1 => by
    rw [gkSt, gkSt_shift Cf ef claim s q]
    rfl

theorem gk_range_succ_map {α : Type} (f : ℕ → α) (n : ℕ) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map fun i ↦ f (i + 1) := by
  simp [List.range_succ_eq_map, List.map_map, Function.comp_def]

theorem gkrRun_cons (Cf : ℕ → List E) (ef : ℕ → E) (L : List (List E)) (M : List E) (claim : E)
    (s : Fs) :
    gkrRun (Cf 0 :: L) (ef 0 :: M) claim s =
      (((s.absorbAll (Cf 0) dsObserve).squeeze.1 ::
        (gkrRun L M (gkSt Cf ef claim s 1).1 (gkSt Cf ef claim s 1).2).1,
        (gkrRun L M (gkSt Cf ef claim s 1).1 (gkSt Cf ef claim s 1).2).2)) := rfl

theorem gkrRun_range1 : ∀ (n : ℕ) (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (s : Fs),
    (gkrRun ((List.range n).map Cf) ((List.range n).map ef) claim s).1 =
      (List.range n).map fun q ↦ challengeOf (gkP Cf ef claim s q)
  | 0, _, _, _, _ => rfl
  | n + 1, Cf, ef, claim, s => by
    rw [gk_range_succ_map Cf, gk_range_succ_map ef, gkrRun_cons, gkrRun_range1 n,
      gk_range_succ_map]
    refine congrArg (List.cons _) (List.map_congr_left fun i _ ↦ ?_)
    simp only [gkP]
    rw [gkSt_shift Cf ef claim s i]

theorem gkrRun_range2 : ∀ (n : ℕ) (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (s : Fs),
    (gkrRun ((List.range n).map Cf) ((List.range n).map ef) claim s).2 = gkSt Cf ef claim s n
  | 0, _, _, _, _ => rfl
  | n + 1, Cf, ef, claim, s => by
    rw [gk_range_succ_map Cf, gk_range_succ_map ef, gkrRun_cons, gkrRun_range2 n,
      gkSt_shift Cf ef claim s n]

theorem gkSt_empty (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (cap : List E) :
    ∀ q, (gkSt Cf ef claim ⟨cap, []⟩ q).2 = ⟨(gkSt Cf ef claim ⟨cap, []⟩ q).2.cap, []⟩
  | 0 => rfl
  | _ + 1 => rfl

/-- Round `q`'s permutation, its cells written out, on four words. -/
theorem gkP_eq (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (cap : List E) (q : ℕ) {a b c d : E}
    (hC : Cf q = [a, b, c, d]) :
    gkP Cf ef claim ⟨cap, []⟩ q = permOf (pendCells [(a, dsObserve), (b, dsObserve), (c, dsObserve),
      (d, dsObserve)] ++ (gkSt Cf ef claim ⟨cap, []⟩ q).2.cap) := by
  rw [gkP, gkSt_empty, hC, absorbAll_short _ _ _ (by simp), perm_eq_cells _ (by simp)]
  simp

/-- The guest's Horner form of a round polynomial. -/
theorem gk_eval (claim e c1 c2 c3 c4 r : E) :
    claim + e * (c1 + c2 + c3 + c4) + r * (c1 + r * (c2 + r * (c3 + r * c4))) =
      polyEval ((claim + e * sumE [c1, c2, c3, c4]) :: [c1, c2, c3, c4]) r := by
  simp only [polyEval, List.foldr, sumE, List.foldl, zero_add, zero_mul]
  ring

/-! ## Soundness -/

/-- What the arithmetic of round `q` asks. -/
def GkFoldOk (rd : Reader) (σ : Val) (q : ℕ) : Prop :=
  LoadHolds rd (σ (.n 1)) q (σ (.n (69 + 74 * q))) ∧
    σ (.n (70 + 74 * q)) = σ (.n (9 + 74 * q)) + σ (.n (19 + 74 * q)) ∧
    σ (.n (71 + 74 * q)) = σ (.n (70 + 74 * q)) + σ (.n (29 + 74 * q)) ∧
    σ (.n (72 + 74 * q)) = σ (.n (71 + 74 * q)) + σ (.n (39 + 74 * q)) ∧
    σ (.n (73 + 74 * q)) = σ (.n (69 + 74 * q)) * σ (.n (72 + 74 * q)) ∧
    σ (.n (74 + 74 * q)) = σ (.n (8 + 74 * q)) + σ (.n (73 + 74 * q)) ∧
    LoadHolds rd (σ (.n 1)) (42 + q) (σ (.n (68 + 74 * q))) ∧
    σ (.n (75 + 74 * q)) = σ (.n (68 + 74 * q)) * σ (.n (39 + 74 * q)) ∧
    σ (.n (76 + 74 * q)) = σ (.n (29 + 74 * q)) + σ (.n (75 + 74 * q)) ∧
    σ (.n (77 + 74 * q)) = σ (.n (68 + 74 * q)) * σ (.n (76 + 74 * q)) ∧
    σ (.n (78 + 74 * q)) = σ (.n (19 + 74 * q)) + σ (.n (77 + 74 * q)) ∧
    σ (.n (79 + 74 * q)) = σ (.n (68 + 74 * q)) * σ (.n (78 + 74 * q)) ∧
    σ (.n (80 + 74 * q)) = σ (.n (9 + 74 * q)) + σ (.n (79 + 74 * q)) ∧
    σ (.n (81 + 74 * q)) = σ (.n (68 + 74 * q)) * σ (.n (80 + 74 * q)) ∧
    σ (.n (82 + 74 * q)) = σ (.n (74 + 74 * q)) + σ (.n (81 + 74 * q))

/-- What round `q` asks. -/
theorem holds_gkRound (q : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gkRound q) True kret ↔
      (∀ t < 4, LoadHolds rd (σ (.n 7)) (4 * q + t) (σ (.n (9 + 74 * q + 10 * t))) ∧
        FsPackOk σ (.n (9 + 74 * q + 10 * t)) (9 + 74 * q + 10 * t + 1) dsObserve) ∧
      (Atom.keccak [.n (16 + 74 * q), .n (18 + 74 * q), .n (26 + 74 * q), .n (28 + 74 * q),
        .n (36 + 74 * q), .n (38 + 74 * q), .n (46 + 74 * q), .n (48 + 74 * q),
        .n (gkCapPrev q), .n (gkCapPrev q + 1), .n (gkCapPrev q + 2), .n (gkCapPrev q + 3),
        .n (gkCapPrev q + 4)] (gkRun13 (49 + 74 * q)) false false).Holds rd σ ∧
      ChallengeOk σ (.n (49 + 74 * q)) (.n (50 + 74 * q)) (62 + 74 * q) ∧ GkFoldOk rd σ q := by
  simp only [gkRound, keccakA, holdsList_append, holds_fsNextT, holds_challengeT, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, GkFoldOk, and_true]
  constructor
  · rintro ⟨h0, h1, h2, h3, hk, hc, hf⟩
    refine ⟨fun t ht ↦ ?_, hk, hc, hf⟩
    interval_cases t
    · simpa using h0
    · simpa [show 4 * q + 1 = 4 * q + 1 by rfl, show 9 + 74 * q + 10 * 1 = 19 + 74 * q by ring]
        using h1
    · simpa [show 9 + 74 * q + 10 * 2 = 29 + 74 * q by ring] using h2
    · simpa [show 9 + 74 * q + 10 * 3 = 39 + 74 * q by ring] using h3
  · rintro ⟨h, hk, hc, hf⟩
    refine ⟨by simpa using h 0 (by omega), ?_, ?_, ?_, hk, hc, hf⟩
    · simpa [show 9 + 74 * q + 10 * 1 = 19 + 74 * q by ring] using h 1 (by omega)
    · simpa [show 9 + 74 * q + 10 * 2 = 29 + 74 * q by ring] using h 2 (by omega)
    · simpa [show 9 + 74 * q + 10 * 3 = 39 + 74 * q by ring] using h 3 (by omega)

theorem keccak_gkRun13 {ins : List V} {b : ℕ}
    (h : (Atom.keccak ins (gkRun13 b) false false).Holds rd σ) :
    AllCanonical (ins.map σ) ∧
      ∀ c : Fin 13, σ (.n (b + c.val)) = cellsOfState (permOf (ins.map σ)) false c := by
  obtain ⟨-, -, hcan, hout⟩ := keccakA_perm h
  refine ⟨hcan, fun c => ?_⟩
  have := outs_eq hout c (by simp [gkRun13])
  simpa [gkRun13] using this

theorem readsAt_flatten4 {p : E} (Cf : ℕ → List E) (h4 : ∀ q, (Cf q).length = 4) :
    ∀ n, (∀ q < n, ∀ t < 4, LoadHolds rd p (4 * q + t) ((Cf q).getD t 0)) →
      ReadsAt rd p ((List.range n).map Cf).flatten
  | 0, _ => readsAt_nil rd p
  | n + 1, h => by
    intro k hk
    have hlen : ((List.range n).map Cf).flatten.length = 4 * n := by
      clear hk h
      induction n with
      | zero => rfl
      | succ n ih => simp [List.range_succ, h4, ih]; ring
    simp only [List.range_succ, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil] at hk ⊢
    rw [List.getElem_append]
    split_ifs with hkn
    · exact readsAt_flatten4 Cf h4 n (fun q hq t ht ↦ h q (by omega) t ht) k hkn
    · have hk' : k < 4 * n + 4 := by simpa [hlen, h4] using hk
      rw [hlen] at hkn
      have := h n (by omega) (k - 4 * n) (by omega)
      rw [show 4 * n + (k - 4 * n) = k by omega] at this
      convert this using 1
      simp [List.getD_eq_getElem?_getD, hlen, List.getElem?_eq_getElem (show k - 4 * n < (Cf n).length by rw [h4]; omega)]

/-- The two parameters. -/
abbrev gkParams : List V := [.n 0, .n 1]

theorem gk_sound {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n) (hn2 : n ≤ 2)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = gkParams)
    (hbody : f.body = gkBody n) (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) : MeaningGkrRounds n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, gkBody] at h
  simp only [holdsList_append, holdsList_range_flatten n gkRound (fun _ => rfl), holds_gkRound,
    Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, l2, l3, l4, l5, l6, l7, l8, hrounds, s0, s1, s2, s3, s4, k, m, sc, sl, hret⟩ := h
  subst hp
  have idx : ∀ a b, a = b → σ (.n a) = σ (.n b) := fun a b h ↦ by rw [h]
  set Cf : ℕ → List E := fun q ↦ [σ (.n (9 + 74 * q)), σ (.n (19 + 74 * q)), σ (.n (29 + 74 * q)),
    σ (.n (39 + 74 * q))] with hCf
  set ef : ℕ → E := fun q ↦ σ (.n (69 + 74 * q)) with hef
  set cap := [σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] with hcap
  set St := gkSt Cf ef (σ (.n 8)) ⟨cap, []⟩ with hSt
  set P := gkP Cf ef (σ (.n 8)) ⟨cap, []⟩ with hP
  have cells : ∀ q, q < n → ∀ t < 4,
      (σ (.n (9 + 74 * q + 10 * t + 7)), σ (.n (9 + 74 * q + 10 * t + 9))) =
        Keccak.scalarCells (σ (.n (9 + 74 * q + 10 * t))) dsObserve ∧
      LoadHolds rd (σ (.n 7)) (4 * q + t) (σ (.n (9 + 74 * q + 10 * t))) := by
    intro q hq t ht
    obtain ⟨hn, hk, -, -⟩ := hrounds q hq
    obtain ⟨hcan, -⟩ := keccak_gkRun13 hk
    obtain ⟨hl, hpk⟩ := hn t ht
    refine ⟨fsPackT_cells hpk (hcan _ ?_), hl⟩
    interval_cases t <;> simp <;> ring_nf <;> simp
  have hAB : ∀ q, q < n → σ (.n (8 + 74 * q)) = (St q).1 ∧
      ∀ c : Fin 13, σ (.n (49 + 74 * q + c.val)) = cellsOfState (P q) false c := by
    intro q
    induction q with
    | zero =>
      intro hq
      refine ⟨rfl, fun c ↦ ?_⟩
      obtain ⟨-, hk, -, -⟩ := hrounds 0 hq
      obtain ⟨-, hout⟩ := keccak_gkRun13 hk
      rw [hout c]
      refine congrArg (fun S ↦ cellsOfState S false c) ?_
      rw [hP, gkP_eq Cf ef _ cap 0 rfl]
      have e0 := (cells 0 hq 0 (by omega)).1
      have e1 := (cells 0 hq 1 (by omega)).1
      have e2 := (cells 0 hq 2 (by omega)).1
      have e3 := (cells 0 hq 3 (by omega)).1
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at e0 e1 e2 e3
      simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
        gkCapPrev, ← e0, ← e1, ← e2, ← e3]
      rfl
    | succ q ih =>
      intro hq
      obtain ⟨hA, hB⟩ := ih (by omega)
      obtain ⟨-, -, hch, hf⟩ := hrounds q (by omega)
      have b0 : σ (.n (49 + 74 * q)) = cellsOfState (P q) false 0 := hB 0
      have b1 : σ (.n (50 + 74 * q)) = cellsOfState (P q) false 1 :=
        (idx _ (49 + 74 * q + (1 : Fin 13).val) (by simp; ring)).trans (hB 1)
      have hr : σ (.n (68 + 74 * q)) = challengeOf (P q) :=
        (idx _ (62 + 74 * q + 6) (by ring)).trans (challengeT_value hch b0 b1)
      obtain ⟨-, f70, f71, f72, f73, f74, -, f75, f76, f77, f78, f79, f80, f81, f82⟩ := hf
      refine ⟨?_, fun c ↦ ?_⟩
      · rw [idx _ (82 + 74 * q) (by ring), f82, f81, f80, f79, f78, f77, f76, f75, f74, f73, f72,
          f71, f70, hA, hr]
        show _ = polyEval (((St q).1 + ef q * sumE (Cf q)) :: Cf q) (challengeOf (P q))
        rw [← gk_eval]
      · obtain ⟨-, hk, -, -⟩ := hrounds (q + 1) hq
        obtain ⟨-, hout⟩ := keccak_gkRun13 hk
        rw [hout c]
        refine congrArg (fun S ↦ cellsOfState S false c) ?_
        rw [hP, gkP_eq Cf ef _ cap (q + 1) rfl]
        have e0 := (cells (q + 1) hq 0 (by omega)).1
        have e1 := (cells (q + 1) hq 1 (by omega)).1
        have e2 := (cells (q + 1) hq 2 (by omega)).1
        have e3 := (cells (q + 1) hq 3 (by omega)).1
        rw [idx (9 + 74 * (q + 1) + 10 * 0) (9 + 74 * (q + 1)) (by ring)] at e0
        rw [idx (9 + 74 * (q + 1) + 10 * 1) (19 + 74 * (q + 1)) (by ring)] at e1
        rw [idx (9 + 74 * (q + 1) + 10 * 2) (29 + 74 * (q + 1)) (by ring)] at e2
        rw [idx (9 + 74 * (q + 1) + 10 * 3) (39 + 74 * (q + 1)) (by ring)] at e3
        have i8 : σ (.n (49 + 74 * q + 8)) = cellsOfState (P q) false 8 := hB 8
        have i9 : σ (.n (49 + 74 * q + 9)) = cellsOfState (P q) false 9 := hB 9
        have i10 : σ (.n (49 + 74 * q + 10)) = cellsOfState (P q) false 10 := hB 10
        have i11 : σ (.n (49 + 74 * q + 11)) = cellsOfState (P q) false 11 := hB 11
        have i12 : σ (.n (49 + 74 * q + 12)) = cellsOfState (P q) false 12 := hB 12
        simp only [gkCapPrev, List.map_cons, List.map_nil]
        rw [idx (16 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 0 + 7 by ring),
          idx (18 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 0 + 9 by ring),
          idx (26 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 1 + 7 by ring),
          idx (28 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 1 + 9 by ring),
          idx (36 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 2 + 7 by ring),
          idx (38 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 2 + 9 by ring),
          idx (46 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 3 + 7 by ring),
          idx (48 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 3 + 9 by ring)]
        rw [idx (57 + 74 * q) _ (show _ = 49 + 74 * q + 8 by ring), i8,
          idx (57 + 74 * q + 1) _ (show _ = 49 + 74 * q + 9 by ring), i9,
          idx (57 + 74 * q + 2) _ (show _ = 49 + 74 * q + 10 by ring), i10,
          idx (57 + 74 * q + 3) _ (show _ = 49 + 74 * q + 11 by ring), i11,
          idx (57 + 74 * q + 4) _ (show _ = 49 + 74 * q + 12 by ring), i12]
        simp only [pendCells, List.flatMap_cons, List.flatMap_nil, ← e0, ← e1, ← e2, ← e3]
        rfl
  have hR : ∀ q, q < n → σ (.n (68 + 74 * q)) = challengeOf (P q) ∧ GkFoldOk rd σ q := by
    intro q hq
    obtain ⟨-, hB⟩ := hAB q hq
    obtain ⟨-, -, hch, hf⟩ := hrounds q hq
    have b0 : σ (.n (49 + 74 * q)) = cellsOfState (P q) false 0 := hB 0
    have b1 : σ (.n (50 + 74 * q)) = cellsOfState (P q) false 1 :=
      (idx _ (49 + 74 * q + (1 : Fin 13).val) (by simp; ring)).trans (hB 1)
    exact ⟨(idx _ (62 + 74 * q + 6) (by ring)).trans (challengeT_value hch b0 b1), hf⟩
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
  have hAn : σ (.n (82 + 74 * m')) = (St (m' + 1)).1 := by
    obtain ⟨hA, -⟩ := hAB m' (by omega)
    obtain ⟨hr, hf⟩ := hR m' (by omega)
    obtain ⟨-, f70, f71, f72, f73, f74, -, f75, f76, f77, f78, f79, f80, f81, f82⟩ := hf
    rw [f82, f81, f80, f79, f78, f77, f76, f75, f74, f73, f72, f71, f70, hA, hr]
    show _ = polyEval (((St m').1 + ef m' * sumE (Cf m')) :: Cf m') (challengeOf (P m'))
    rw [← gk_eval]
  obtain ⟨-, hBm⟩ := hAB m' (by omega)
  refine ⟨hret.symm, cap, σ (.n 7), σ (.n 8), (List.range (m' + 1)).map Cf,
    (List.range (m' + 1)).map ef, ⟨rfl, fun j hj ↦ ?_⟩, ?_, l7, l8, by simp, ?_, ?_, by simp, ?_, ?_⟩
  · simp only [hcap, List.length_cons, List.length_nil] at hj
    interval_cases j
    · exact l2
    · exact l3
    · exact l4
    · exact l5
    · exact l6
  · obtain ⟨-, hk, -, -⟩ := hrounds 0 (by omega)
    obtain ⟨hcan, -⟩ := keccak_gkRun13 hk
    intro x hx
    simp only [hcap, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact hcan _ (by simp [gkCapPrev])
  · intro c hc
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hc
    rfl
  · refine readsAt_flatten4 Cf (fun _ ↦ rfl) (m' + 1) fun q hq t ht ↦ ?_
    have := (cells q hq t ht).2
    interval_cases t
    · simpa [hCf] using this
    · simpa [hCf, show 9 + 74 * q + 10 * 1 = 19 + 74 * q by ring] using this
    · simpa [hCf, show 9 + 74 * q + 10 * 2 = 29 + 74 * q by ring] using this
    · simpa [hCf, show 9 + 74 * q + 10 * 3 = 39 + 74 * q by ring] using this
  · intro q hq
    simp only [List.length_map, List.length_range] at hq
    simp only [List.getElem_map, List.getElem_range, hef]
    exact (hR q hq).2.1
  · simp only
    rw [gkrRun_range1, gkrRun_range2]
    refine ⟨fun q hq ↦ ?_, ⟨rfl, fun j hj ↦ ?_⟩, ?_, ?_⟩
    · simp only [List.length_map, List.length_range] at hq
      simp only [List.getElem_map, List.getElem_range]
      obtain ⟨hr, -, -, -, -, -, -, hst, -⟩ := hR q hq
      rw [loadHolds_mul_gen_pow, ← hr]
      exact hst
    · simp only [gkSt, Fs.squeeze, capOf, List.length_cons, List.length_nil] at hj
      have st : ∀ i (hi : i < 5), LoadHolds rd (σ (.n 0)) (m' + 1 + i * 862)
          (cellsOfState (P m') false ⟨8 + i, by omega⟩) := by
        intro i hi
        have e := hBm ⟨8 + i, by omega⟩
        rw [← e, idx (49 + 74 * m' + (8 + i)) (57 + 74 * (m' + 1 - 1) + i) (by simp; ring)]
        interval_cases i
        · exact s0
        · rw [idx (57 + 74 * (m' + 1 - 1) + 1) (58 + 74 * (m' + 1 - 1)) (by ring), show m' + 1 + 1 * 862 = m' + 1 + 862 by ring]
          exact s1
        · rw [idx (57 + 74 * (m' + 1 - 1) + 2) (59 + 74 * (m' + 1 - 1)) (by ring), show m' + 1 + 2 * 862 = m' + 1 + 1724 by ring]
          exact s2
        · rw [idx (57 + 74 * (m' + 1 - 1) + 3) (60 + 74 * (m' + 1 - 1)) (by ring), show m' + 1 + 3 * 862 = m' + 1 + 2586 by ring]
          exact s3
        · rw [idx (57 + 74 * (m' + 1 - 1) + 4) (61 + 74 * (m' + 1 - 1)) (by ring), show m' + 1 + 4 * 862 = m' + 1 + 3448 by ring]
          exact s4
      interval_cases j
      · exact st 0 (by omega)
      · exact st 1 (by omega)
      · exact st 2 (by omega)
      · exact st 3 (by omega)
      · exact st 4 (by omega)
    · have k : σ (.n (9 + 74 * (m' + 1))) = word (2 ^ (4 * (m' + 1))) 0 0 := k
      have m : σ (.n (10 + 74 * (m' + 1))) = σ (.n 7) * σ (.n (9 + 74 * (m' + 1))) := m
      have sc : LoadHolds rd (σ (.n 0)) (m' + 1 + 4310) (σ (.n (10 + 74 * (m' + 1)))) := sc
      rw [m, k, word_two_pow (by omega)] at sc
      exact sc
    · have sl : LoadHolds rd (σ (.n 0)) (m' + 1 + 5172) (σ (.n (82 + 74 * (m' + 1 - 1)))) := sl
      rw [show m' + 1 - 1 = m' by omega, hAn] at sl
      exact sl

set_option maxRecDepth 100000 in
theorem core401_body : Fn.body Data.core401 = gkBody 1 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem core400_body : Fn.body Data.core400 = gkBody 2 := stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
