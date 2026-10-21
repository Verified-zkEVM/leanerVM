/-
  LeanVM.Guest.B1.Comp.Tables.FlockLoopsC

  `verify_flock`'s honest memory and its two loops over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.FlockRunC
public import LeanVM.Guest.B1.Comp.Tables.CompletesB
public import LeanVM.Guest.B1.Comp.Digest.Common
public import LeanVM.Guest.B1.Tables.FlockComplete

/-!
# `verify_flock`'s memory and loops over a completeness model

`FlMemC M`: `FlMem` at a hash model's total hash (`flET`, `sqCvT`, `scStT`, …): what the honest
memory holds for the run on the state `cv` and the words `xs`. `loop81_stepC`, `loop82_stepC`:
one iteration of `__loop81`, `__loop82` under a completeness model's semantics, backward (the
converse of `loop81_stepM`, `loop82_stepM` at the model's answers). `loop81_completeC`,
`loop82_completeC` (`loop81_complete`, `loop82_complete`): the loops hold over the honest memory
when the run's hashes are answered (`FlAns`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

/-! ## One iteration of each loop, backward -/

/-- **`__loop81`, one iteration, backward, over a completeness model** (`loop81_step`'s converse
at the model's answers). -/
theorem loop81_stepC {CM : CompModel} (rd : Reader) (N pts zr x : E)
    (hb : L81BodyM CM.hm rd pts zr x) (hK : IsInK (x * gen + N))
    (hcall : x * gen + N ≠ 0 →
      coreProgram.RelB CM.sem rd "__loop81" (x * gen :: [N, pts, zr]) []) :
    ∃ fn, coreProgram.find? "__loop81" = some fn ∧
      fn.SemB CM.sem (coreProgram.RelB CM.sem rd) rd (x :: [N, pts, zr]) [] := by
  obtain ⟨cv, l6, l7, hq, l21, l13, l14⟩ := hb
  set d := sqCvT CM.hm cv
  refine ⟨Data.core140, find_loop81, ?_⟩
  rw [Fn.SemB, show Fn.params Data.core140 = [.n 0, .n 1, .n 2, .n 3] from rfl, core140_body,
    l81Body]
  refine ⟨setl (Val.ofArgs [x, N, pts, zr]) 4 [x * x, pts * (x * x), (digestScalars cv).1,
    (digestScalars cv).2, sqValsD d 0, sqValsD d 1, sqValsD d 2, sqValsD d 3, sqValsD d 4,
    sqValsD d 5, sqValsD d 6, sqValsD d 7, sqValsD d 8, sqValsD d 9, sqValsD d 10, sqValsD d 11,
    sqValsD d 12, sqValsD d 13, zr * x, gen, x * gen, x * gen + N, gen, x * gen], ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    b1_look
  · rw [holdsListB_append, holdsListB_append]
    simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, and_true,
      word_gen]
    refine ⟨?_, ?_, ?_, ?_, holdsB_squeezeT_comp _ _ _ ⟨⟨cv, d, ?_, hq, fun k hk => ?_⟩, ?_⟩⟩
    all_goals (try b1_look)
    · exact l6
    · exact l7
    · interval_cases k <;> b1_look
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try b1_look)
    · exact l21
    · exact l13
    · exact l14
    · exact hK
    · exact hcall

set_option maxHeartbeats 1000000 in
/-- **`__loop82`, one iteration, backward, over a completeness model** (`loop82_step`'s converse
at the model's answers). -/
theorem loop82_stepC {CM : CompModel} (rd : Reader) (N rnd zr chis x : E)
    (hb : L82BodyM CM.hm rd rnd zr chis x) (hK : IsInK (x * gen + N))
    (hcall : x * gen + N ≠ 0 →
      coreProgram.RelB CM.sem rd "__loop82" (x * gen :: [N, rnd, zr, chis]) []) :
    ∃ fn, coreProgram.find? "__loop82" = some fn ∧
      fn.SemB CM.sem (coreProgram.RelB CM.sem rd) rd (x :: [N, rnd, zr, chis]) [] := by
  obtain ⟨cv, cur, claim, e, g1, g2, l8, l9, l12, l43, l11, l13, l28, ⟨o1, o2, o3⟩, l60, l52, l53,
    l63, l67⟩ := hb
  set cv2 := obsCvT CM.hm cv g1
  set cv3 := obsCvT CM.hm cv2 g2
  set d := sqCvT CM.hm cv3
  have hst := (show scStepT CM.hm e (g1, g2) (claim, cv) = (challengeOf d,
    claim + e * (g1 + g2) + challengeOf d * (g1 + challengeOf d * g2), d) from rfl)
  rw [hst] at l60 l52 l53 l67
  refine ⟨Data.core141, find_loop82, ?_⟩
  rw [Fn.SemB, show Fn.params Data.core141 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
    core141_body, l82Body]
  refine ⟨setl (Val.ofArgs [x, N, rnd, zr, chis]) 5 ([x * x, x * x * (x * x),
    rnd * (x * x * (x * x)),
    (digestScalars cv).1, (digestScalars cv).2, zr * x, e, cur, g1] ++
    ((List.range 14).map fun k => fsValsD g1 cv2 1 k) ++ [g2] ++
    ((List.range 14).map fun k => fsValsD g2 cv3 1 k) ++
    [claim, g1 + g2, e * (g1 + g2), claim + e * (g1 + g2)] ++
    ((List.range 14).map fun k => sqValsD d k) ++
    [chis * x, gen ^ 2, cur * gen ^ 2, challengeOf d * g2,
      g1 + challengeOf d * g2,
      challengeOf d * (g1 + challengeOf d * g2),
      claim + e * (g1 + g2) + challengeOf d * (g1 + challengeOf d * g2),
      gen, x * gen, x * gen + N, gen, x * gen]), ?_, ?_⟩
  · simp only [List.cons_append, List.map_cons, List.range_succ, List.range_zero, List.map_nil,
      List.nil_append]
    b1_look
  · simp only [List.cons_append, List.map_cons, List.range_succ, List.range_zero, List.map_nil,
      List.nil_append]
    simp only [holdsListB_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
      List.map_nil, and_true, word_gen, word_four']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try b1_look)
    · exact l8
    · exact l9
    · exact l11
    · exact l12
    · refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨?_, cv, cv2, ?_, ?_, fun k hk1 hk2 => ?_⟩, ?_⟩
      · b1_look; exact l13
      · b1_look
      · b1_look; exact o1
      · interval_cases k <;> b1_look
      refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨?_, cv2, cv3, ?_, ?_, fun k hk1 hk2 => ?_⟩, ?_⟩
      · b1_look; exact l28
      · b1_look; rfl
      · b1_look; exact o2
      · interval_cases k <;> b1_look
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals (try b1_look)
      · exact l43
      refine holdsB_squeezeT_comp _ _ _ ⟨⟨cv3, d, ?_, o3, fun k hk => ?_⟩, ?_⟩
      · b1_look; rfl
      · interval_cases k <;> b1_look
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try b1_look)
      all_goals (try rfl)
      · exact l60
      · exact l52
      · exact l53
      · exact l63
      · exact l67
      · exact hK
      · exact hcall

/-! ## The honest memory -/

/-- The zerocheck's state after `j` rounds at the total hash (`flScAt`). -/
abbrev flScAtT (M : HashModel) (τ : ℕ) (cv : Digest) (xs : List E) (j : ℕ) : E × Digest :=
  scStT M (flET M τ cv) (flG xs) (flSt0T M τ cv xs) j

/-- **The honest memory of `verify_flock` at a hash model's total hash** (`FlMem`), for the run
on the state `cv` and the words `xs`. -/
structure FlMemC (M : HashModel) (rd : Reader) (τ : ℕ) (cv : Digest) (xs : List E)
    (cur zchis lrs zpart p11 p24 p40 p2220 : E) : Prop where
  words : ∀ k < flLen τ, LoadHolds rd cur k (xs.getD k 0)
  zr : ∀ j < τ + 8, LoadHolds rd p11 (6 + j) (flET M τ cv j)
  pts : ∀ t ≤ τ + 1, LoadHolds rd p24 (26 + 2 * t) (digestScalars ((sqCvT M)^[t] cv)).1 ∧
    LoadHolds rd p24 (27 + 2 * t) (digestScalars ((sqCvT M)^[t] cv)).2
  p1 : ∀ i < 64, LoadHolds rd p40 i (xs.getD i 0)
  rnd : ∀ j, 7 ≤ j → j ≤ τ + 8 →
    LoadHolds rd p2220 (4 * j) (digestScalars (flScAtT M τ cv xs j).2).1 ∧
    LoadHolds rd p2220 (4 * j + 1) (digestScalars (flScAtT M τ cv xs j).2).2 ∧
    LoadHolds rd p2220 (4 * j + 2) (cur * gen ^ (64 + 2 * j)) ∧
    LoadHolds rd p2220 (4 * j + 3) (flScAtT M τ cv xs j).1
  chis : ∀ j < τ + 8, LoadHolds rd zchis j (scChT M (flET M τ cv) (flG xs) (flSt0T M τ cv xs) j)
  rcs : ∀ j < 8, LoadHolds rd lrs j (lcChT M (flG' τ xs) (flSt0'T M τ cv xs) j)
  sl : ∀ i < 64, LoadHolds rd zpart i (xs.getD (82 + 2 * (τ + 8) + i) 0)

theorem flET_sampled (M : HashModel) (τ : ℕ) (cv : Digest) {t : ℕ} (ht : t ≤ τ) :
    flET M τ cv (7 + t) = challengeOf (sqCvT M ((sqCvT M)^[t] cv)) := by
  simp only [flET, flSamT]
  rw [show 7 + t = fixedChallenges.length + t by rw [fixedChallenges_length], getD_append_ge,
    Digest.getD_map_range _ (by omega)]

/-! ## The loops -/

section
variable {CM : CompModel} {rd : Reader} {τ : ℕ} {cv : Digest} {xs : List E}
  {cur zchis lrs zpart p11 p24 p40 p2220 : E}

/-- **`__loop81` holds over a completeness model** on the honest memory (`loop81_complete`), the
sampled coordinates' squeezes answered. -/
theorem loop81_completeC (hτ : τ < 29)
    (hM : FlMemC CM.hm rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220)
    (hA : FlAns CM.hm τ cv xs) :
    coreProgram.RelB CM.sem rd "__loop81" [gen ^ 13, gen ^ (τ + 14), p24, p11] [] := by
  refine Digest.loopB_bwd (B := L81BodyM CM.hm rd p24 p11)
    (fun x hb hK hcall => loop81_stepC rd _ _ _ x hb hK hcall) (k := 13) (m := τ + 14) (by omega)
    rfl fun j h1 h2 => ?_
  obtain ⟨t, rfl⟩ : ∃ t, j = 13 + t := ⟨j - 13, by omega⟩
  obtain ⟨a0, a1⟩ := hM.pts t (by omega)
  obtain ⟨b0, b1⟩ := hM.pts (t + 1) (by omega)
  have hz := hM.zr (7 + t) (by omega)
  rw [flET_sampled CM.hm τ cv (by omega)] at hz
  rw [Function.iterate_succ_apply'] at b0 b1
  unfold L81BodyM; rw [gen_pow_sq]
  exact ⟨(sqCvT CM.hm)^[t] cv, lh_back a0 (by omega), lh_back a1 (by omega),
    by rw [← Function.iterate_succ_apply' (sqCvT CM.hm)]; exact hA.sam t (by omega),
    lh_back hz (by omega), lh_back b0 (by omega), lh_back b1 (by omega)⟩

/-- **`__loop82` holds over a completeness model** on the honest memory (`loop82_complete`), the
zerocheck's sampled rounds answered. -/
theorem loop82_completeC (hτ : τ < 29)
    (hM : FlMemC CM.hm rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220)
    (hA : FlAns CM.hm τ cv xs) :
    coreProgram.RelB CM.sem rd "__loop82" [gen ^ 7, gen ^ (τ + 8), p2220, p11, zchis] [] := by
  refine Digest.loopB_bwd (B := L82BodyM CM.hm rd p2220 p11 zchis)
    (fun x hb hK hcall => loop82_stepC rd _ _ _ _ x hb hK hcall) (k := 7) (m := τ + 8) (by omega)
    rfl fun j h1 h2 => ?_
  obtain ⟨r0, r1, r2, r3⟩ := hM.rnd j h1 (by omega)
  obtain ⟨n0, n1, n2, n3⟩ := hM.rnd (j + 1) (by omega) (by omega)
  unfold L82BodyM; rw [gen_pow_quad]
  refine ⟨(flScAtT CM.hm τ cv xs j).2, cur * gen ^ (64 + 2 * j), (flScAtT CM.hm τ cv xs j).1,
    flET CM.hm τ cv j, (flG xs j).1, (flG xs j).2, lh_back r0 (by omega), lh_back r1 (by omega),
    lh_back r2 (by omega), lh_back r3 (by omega), lh_back (hM.zr j (by omega)) (by omega),
    lh_back (hM.words _ (by unfold flLen; omega)) (by omega),
    lh_back (hM.words _ (by unfold flLen; omega)) (by omega), hA.sc j (by omega),
    lh_back (hM.chis j (by omega)) (by omega), lh_back n0 (by omega), lh_back n1 (by omega), ?_,
    lh_back n3 (by omega)⟩
  rw [mul_assoc, ← pow_add]
  exact lh_back n2 (by omega)

end

end
end LeanVM.Guest.B1
