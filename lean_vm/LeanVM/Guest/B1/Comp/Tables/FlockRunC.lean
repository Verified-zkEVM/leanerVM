/-
  LeanVM.Guest.B1.Comp.Tables.FlockRunC

  `verifyFlock`'s answered run read backward over a hash model: the honest values of the words
  at the model's total hash, and every hash of the run answered.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.RunInv
public import LeanVM.Guest.B1.Tables.FlockRun

/-!
# `verifyFlock` over a hash model, backward

`FlockRun.lean`'s honest run on words `W` over a hash model `M`, at the model's total hash
(`obsCvT`, `sqCvT`, `scStT`, `lcStT`): `flCvST`, `flET`, `flZT`, `flSt0T`, `flScT`, `flCv5T`,
`flAlphaT`, `flSt0'T`, `flLcT`, `flChiT`, `flRcT`, `flTermT` are `flCvS`, `flE`, …, `flTerm`
(`flZT_deployed`, …, at `CompModel.deployed`). `FlAns M τ cv W`: every hash of the run on `W`
is answered.

`flock_invC` (`flock_inv` over `M`): an answered accepting run with `flockEv` names its words,
challenges, slices and final state at the total hash, the terminal check holds, and every hash
of the run is answered.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.E2E.Complete

@[expose] public section

/-! ## The honest run at the total hash -/

section
variable (M : HashModel) (τ : ℕ) (cv0 : Digest) (W : List E)

/-- The sampled coordinates (`(sqAll (τ + 1) cv0).1`). -/
def flSamT : List E := (List.range (τ + 1)).map fun t => challengeOf (sqCvT M ((sqCvT M)^[t] cv0))

/-- The state after the sampled coordinates (`flCvS`). -/
def flCvST : Digest := (sqCvT M)^[τ + 1] cv0

/-- The zerocheck's equality factors (`flE`). -/
def flET : ℕ → E := fun j => (fixedChallenges ++ flSamT M τ cv0).getD j 0

/-- The state after round 1's words. -/
def flCvPT : Digest := obsAllT M (flCvST M τ cv0) (flP W)

/-- The skip challenge (`flZ`). -/
def flZT : E := challengeOf (sqCvT M (flCvPT M τ cv0 W))

/-- The zerocheck's start (`flSt0`). -/
def flSt0T : E × Digest :=
  (lagrangeInterpolate 128 (List.replicate 64 0 ++ flP W) (flZT M τ cv0 W),
    sqCvT M (flCvPT M τ cv0 W))

/-- The zerocheck's end (`flSc`). -/
def flScT : E × Digest := scStT M (flET M τ cv0) (flG W) (flSt0T M τ cv0 W) (τ + 8)

/-- The state after the first final evaluation. -/
def flCv4T : Digest := obsCvT M (flScT M τ cv0 W).2 (flA τ W)

/-- The state after both (`flCv5`). -/
def flCv5T : Digest := obsCvT M (flCv4T M τ cv0 W) (flB τ W)

/-- The lincheck's `alpha` (`flAlpha`). -/
def flAlphaT : E := challengeOf (sqCvT M (flCv5T M τ cv0 W))

/-- The lincheck's start (`flSt0'`). -/
def flSt0'T : E × Digest :=
  (flA τ W + flAlphaT M τ cv0 W * flB τ W +
    flAlphaT M τ cv0 W ^ 2 * ((flScT M τ cv0 W).1 + flA τ W * flB τ W) + flAlphaT M τ cv0 W ^ 3,
    sqCvT M (flCv5T M τ cv0 W))

/-- The lincheck's end (`flLc`). -/
def flLcT : E × Digest := lcStT M (flG' τ W) (flSt0'T M τ cv0 W) 8

/-- The zerocheck's point (`flChi`). -/
def flChiT : List E := (List.range (τ + 8)).map (scChT M (flET M τ cv0) (flG W) (flSt0T M τ cv0 W))

/-- The lincheck's challenges (`flRc`). -/
def flRcT : List E := (List.range 8).map (lcChT M (flG' τ W) (flSt0'T M τ cv0 W))

/-- The terminal check at the matrices' value `mv` (`flTerm`). -/
@[reducible] def flTermT (mv : E) : Prop :=
  mv + flAlphaT M τ cv0 W ^ 2 * eqEval ((flChiT M τ cv0 W).take 8) (flRcT M τ cv0 W).reverse *
      dot (lagrangeWeights 64 (flZT M τ cv0 W)) (flS τ W) +
    flAlphaT M τ cv0 W ^ 3 * (lincheckColumnWeights (flRcT M τ cv0 W).reverse (flS τ W)).getD 512 0 =
      (flLcT M τ cv0 W).1

/-- **Every hash of the run on `W` is answered**: the sampled coordinates' squeezes, round 1's
absorbs, the skip challenge, the zerocheck's rounds, the final evaluations, `alpha`, the
lincheck's rounds and the slices. -/
structure FlAns : Prop where
  sam : ∀ t < τ + 1, sqCvM M ((sqCvT M)^[t] cv0) = some ((sqCvT M)^[t + 1] cv0)
  p1 : ObsAns M (flCvST M τ cv0) (flP W)
  z : sqCvM M (flCvPT M τ cv0 W) = some (sqCvT M (flCvPT M τ cv0 W))
  sc : ∀ j < τ + 8, RoundOk M (flG W j) (scStT M (flET M τ cv0) (flG W) (flSt0T M τ cv0 W) j).2
  a : obsCvM M (flScT M τ cv0 W).2 (flA τ W) = some (flCv4T M τ cv0 W)
  b : obsCvM M (flCv4T M τ cv0 W) (flB τ W) = some (flCv5T M τ cv0 W)
  α : sqCvM M (flCv5T M τ cv0 W) = some (sqCvT M (flCv5T M τ cv0 W))
  lc : ∀ j < 8, RoundOk M (flG' τ W j) (lcStT M (flG' τ W) (flSt0'T M τ cv0 W) j).2
  s : ObsAns M (flLcT M τ cv0 W).2 (flS τ W)

end

/-! ## Congruence of the sumchecks -/

section
variable {M : HashModel}

theorem scStT_congr {e e' : ℕ → E} {g g' : ℕ → E × E} (s0 : E × Digest) {n : ℕ}
    (he : ∀ i < n, e i = e' i) (hg : ∀ i < n, g i = g' i) :
    ∀ j ≤ n, scStT M e g s0 j = scStT M e' g' s0 j
  | 0, _ => rfl
  | j + 1, hj => by
    rw [scStT, scStT, scStT_congr s0 he hg j (by omega), he j (by omega), hg j (by omega)]

theorem scChT_congr {e e' : ℕ → E} {g g' : ℕ → E × E} (s0 : E × Digest) {n : ℕ}
    (he : ∀ i < n, e i = e' i) (hg : ∀ i < n, g i = g' i) {j : ℕ} (hj : j < n) :
    scChT M e g s0 j = scChT M e' g' s0 j := by
  rw [scChT, scChT, scStT_congr s0 he hg j (by omega), he j hj, hg j hj]

theorem lcStT_congr {g g' : ℕ → E × E} (s0 : E × Digest) {n : ℕ} (hg : ∀ i < n, g i = g' i) :
    ∀ j ≤ n, lcStT M g s0 j = lcStT M g' s0 j
  | 0, _ => rfl
  | j + 1, hj => by rw [lcStT, lcStT, lcStT_congr s0 hg j (by omega), hg j (by omega)]

theorem lcChT_congr {g g' : ℕ → E × E} (s0 : E × Digest) {n : ℕ} (hg : ∀ i < n, g i = g' i)
    {j : ℕ} (hj : j < n) : lcChT M g s0 j = lcChT M g' s0 j := by
  rw [lcChT, lcChT, lcStT_congr s0 hg j (by omega), hg j hj]

end

/-! ## The words in phases -/

/-- The words of the run's phases concatenated: round 1's, the zerocheck's rounds', the final
evaluations, the lincheck's rounds' and the slices. -/
theorem flW_facts (τ : ℕ) {p ws ws2 s : List E} {a b : E} (hp : p.length = 64)
    (hw : ws.length = 2 * (τ + 8)) (hw2 : ws2.length = 2 * 8) (hs : s.length = 64) :
    (p ++ ws ++ [a, b] ++ ws2 ++ s).length = flLen τ ∧ flP (p ++ ws ++ [a, b] ++ ws2 ++ s) = p ∧
      (∀ j < τ + 8, flG (p ++ ws ++ [a, b] ++ ws2 ++ s) j = pairAt ws j) ∧
      flA τ (p ++ ws ++ [a, b] ++ ws2 ++ s) = a ∧ flB τ (p ++ ws ++ [a, b] ++ ws2 ++ s) = b ∧
      (∀ j < 8, flG' τ (p ++ ws ++ [a, b] ++ ws2 ++ s) j = pairAt ws2 j) ∧
      flS τ (p ++ ws ++ [a, b] ++ ws2 ++ s) = s := by
  have e : p ++ ws ++ [a, b] ++ ws2 ++ s = p ++ (ws ++ (a :: b :: (ws2 ++ s))) := by simp
  rw [e]
  have gp : ∀ k, (p ++ (ws ++ (a :: b :: (ws2 ++ s)))).getD (64 + k) 0 =
      (ws ++ (a :: b :: (ws2 ++ s))).getD k 0 := fun k => by
    rw [List.getD_append_right _ _ _ _ (by omega), hp, Nat.add_sub_cancel_left]
  have gw : ∀ k, (ws ++ (a :: b :: (ws2 ++ s))).getD (2 * (τ + 8) + k) 0 =
      (a :: b :: (ws2 ++ s)).getD k 0 := fun k => by
    rw [List.getD_append_right _ _ _ _ (by omega), hw, Nat.add_sub_cancel_left]
  have g1 : ∀ k < 2 * (τ + 8), (p ++ (ws ++ (a :: b :: (ws2 ++ s)))).getD (64 + k) 0 =
      ws.getD k 0 := fun k hk => by
    rw [gp, List.getD_append _ _ _ _ (by omega)]
  have g2 : ∀ k < 2 * 8, (p ++ (ws ++ (a :: b :: (ws2 ++ s)))).getD (64 + (2 * (τ + 8) + (k + 2)))
      0 = ws2.getD k 0 := fun k hk => by
    rw [gp, gw, List.getD_cons_succ, List.getD_cons_succ, List.getD_append _ _ _ _ (by omega)]
  refine ⟨by simp [hp, hw, hw2, hs, flLen]; omega, ?_, fun j hj => ?_, ?_, ?_, fun j hj => ?_, ?_⟩
  · rw [flP, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  · simp only [flG, pairAt]
    rw [show 65 + 2 * j = 64 + (2 * j + 1) by omega, g1 _ (by omega), g1 _ (by omega)]
  · rw [flA, show 64 + 2 * (τ + 8) = 64 + (2 * (τ + 8) + 0) by omega, gp, gw]; rfl
  · rw [flB, show 65 + 2 * (τ + 8) = 64 + (2 * (τ + 8) + 1) by omega, gp, gw]; rfl
  · simp only [flG', pairAt]
    rw [show 66 + 2 * (τ + 8) + 2 * j = 64 + (2 * (τ + 8) + (2 * j + 2)) by omega,
      show 67 + 2 * (τ + 8) + 2 * j = 64 + (2 * (τ + 8) + (2 * j + 1 + 2)) by omega,
      g2 _ (by omega), g2 _ (by omega)]
  · rw [flS, show 82 + 2 * (τ + 8) = p.length + (ws.length + (2 + ws2.length)) by omega,
      ← List.drop_drop, List.drop_left, ← List.drop_drop, List.drop_left, ← List.drop_drop,
      show (a :: b :: (ws2 ++ s)).drop 2 = ws2 ++ s from rfl, List.drop_left,
      List.take_of_length_le (by omega)]

/-! ## The answered run, backward -/

set_option maxHeartbeats 1600000 in
/-- **An answered accepting run with `flockEv` names its words and arguments** (`flock_inv` over a
hash model): the words have the run's length, the challenges, the slices and the final state are
the honest ones at the total hash, the terminal check holds at `mv`, and every hash of the run is
answered. -/
theorem flock_invC {M : HashModel} {τ : ℕ} {cv0 cv' : Digest} {xs : List E} {alpha zSkip mv : E}
    {chi rcs s : List E}
    (h : RunsToM M (verifyFlock (flockEv alpha zSkip (chi.take 8) rcs.reverse s mv) (14 + τ)) cv0 xs
      (rcs.reverse ++ chi.drop 8, s) cv') :
    xs.length = flLen τ ∧ zSkip = flZT M τ cv0 xs ∧ alpha = flAlphaT M τ cv0 xs ∧
      chi = flChiT M τ cv0 xs ∧ rcs = flRcT M τ cv0 xs ∧ s = flS τ xs ∧ flTermT M τ cv0 xs mv ∧
      cv' = obsAllT M (flLcT M τ cv0 xs).2 (flS τ xs) ∧ FlAns M τ cv0 xs := by
  classical
  have hsamp : 14 + τ - flockKSkip - fixedChallenges.length = τ + 1 := by
    rw [Verifier.flockKSkip_eq, fixedChallenges_length]; omega
  simp only [verifyFlock, verifyFlockZerocheck, verifyFlockLincheck, Prog.bind_eq, Prog.pure_eq,
    Prog.bind_assoc, Prog.ret_bind, hsamp, Verifier.flockNumLincheckRounds_eq,
    show kBits = 64 from rfl, show blake2sConstantColumn = 512 from rfl,
    show 2 * 64 = 128 from rfl] at h
  obtain ⟨cs, c1, hcs, h⟩ := RunsToM.sampleN_inv h
  obtain ⟨hsam, rfl, rfl⟩ := sqAllM_T hcs
  obtain ⟨p, zs1, c2, rfl, hpl, hc2, h⟩ := h.readN_inv
  obtain ⟨rfl, hP1⟩ := obsAllM_T hc2
  obtain ⟨c3, hc3, h⟩ := h.sampleE_inv
  obtain rfl := (sqCvT_eq hc3).symm
  obtain ⟨ws, zs2, rfl, hwl, hok, h⟩ := RunsToM.sumcheck_eq_inv _ h
  obtain ⟨a, zs3, c4, rfl, hc4, h⟩ := h.readE_inv
  obtain rfl := (obsCvT_eq hc4).symm
  obtain ⟨b, zs4, c5, rfl, hc5, h⟩ := h.readE_inv
  obtain rfl := (obsCvT_eq hc5).symm
  obtain ⟨c6, hc6, h⟩ := h.sampleE_inv
  obtain rfl := (sqCvT_eq hc6).symm
  obtain ⟨ws2, zs5, rfl, hwl2, hok2, h⟩ := RunsToM.sumcheck_plain_inv _ h
  obtain ⟨s', zs6, c7, rfl, hsl, hc7, h⟩ := h.readN_inv
  obtain ⟨rfl, hS⟩ := obsAllM_T hc7
  simp only [flockEv, Prog.bind_assoc, Prog.ret_bind] at h
  obtain ⟨⟨hA1, hA2, hA3, hA4, rfl⟩, h⟩ := h.require_inv
  obtain ⟨hT, h⟩ := h.require_inv
  obtain ⟨rfl, hout, rfl⟩ := h.ret_inv
  clear * - hsam hpl hP1 hc3 hwl hok hc4 hc5 hc6 hwl2 hok2 hsl hS hc7 hA1 hA2 hA3 hA4 hT hout
  have hcsl : (fixedChallenges ++ flSamT M τ cv0).length = τ + 8 := by
    simp [fixedChallenges_length, flSamT]; omega
  have hsamE : List.map (fun t => challengeOf (sqCvT M ((sqCvT M)^[t] cv0))) (List.range (τ + 1)) =
    flSamT M τ cv0 := rfl
  simp only [hsamE] at *
  simp only [hcsl] at *
  obtain ⟨hlen, hfP, hfG, hfA, hfB, hfG', hfS⟩ :=
    flW_facts τ (a := a) (b := b) (ws2 := ws2) (s := s') hpl hwl hwl2 hsl
  simp only [List.nil_append, List.append_nil, List.cons_append, List.append_assoc] at hlen hfP hfG hfA hfB hfG' hfS ⊢
  set W := p ++ (ws ++ (a :: b :: (ws2 ++ s'))) with hW
  have hE : ∀ i < τ + 8, (fun x => (fixedChallenges ++ flSamT M τ cv0).getD x 0) i =
      flET M τ cv0 i := fun i _ => rfl
  have h0 : (lagrangeInterpolate 128 (List.replicate 64 0 ++ p)
      (challengeOf (sqCvT M (obsAllT M ((sqCvT M)^[τ + 1] cv0) p))),
        sqCvT M (obsAllT M ((sqCvT M)^[τ + 1] cv0) p)) = flSt0T M τ cv0 W := by
    simp only [flSt0T, flZT, flCvPT, flCvST, hfP]
  have hSc : ∀ j ≤ τ + 8, scStT M (fun x => (fixedChallenges ++ flSamT M τ cv0).getD x 0)
      (pairAt ws) (flSt0T M τ cv0 W) j = scStT M (flET M τ cv0) (flG W) (flSt0T M τ cv0 W) j :=
    scStT_congr _ hE fun i hi => (hfG i hi).symm
  have hSc8 := hSc (τ + 8) le_rfl
  have hCh : (List.range (τ + 8)).map (scChT M (fun x => (fixedChallenges ++ flSamT M τ cv0).getD x 0)
      (pairAt ws) (flSt0T M τ cv0 W)) = flChiT M τ cv0 W :=
    List.map_congr_left fun j hj => scChT_congr _ hE (fun i hi => (hfG i hi).symm)
      (List.mem_range.mp hj)
  have hscE : scStT M (flET M τ cv0) (flG W) (flSt0T M τ cv0 W) (τ + 8) = flScT M τ cv0 W := rfl
  simp only [h0] at hok hc4 hc5 hc6 hok2 hS hc7 hA1 hA3 hA4 hT hout
  simp only [hSc8, hCh, hscE] at hc4 hc5 hc6 hok2 hS hc7 hA1 hA3 hA4 hT hout
  have hs0' : (a + challengeOf (sqCvT M (obsCvT M (obsCvT M (flScT M τ cv0 W).2 a) b)) * b +
      challengeOf (sqCvT M (obsCvT M (obsCvT M (flScT M τ cv0 W).2 a) b)) ^ 2 *
        ((flScT M τ cv0 W).1 + a * b) +
      challengeOf (sqCvT M (obsCvT M (obsCvT M (flScT M τ cv0 W).2 a) b)) ^ 3,
      sqCvT M (obsCvT M (obsCvT M (flScT M τ cv0 W).2 a) b)) = flSt0'T M τ cv0 W := by
    simp only [flSt0'T, flAlphaT, flCv5T, flCv4T, hfA, hfB]
  simp only [hs0'] at hok2 hS hc7 hA4 hT hout
  have hLc : ∀ j ≤ 8, lcStT M (pairAt ws2) (flSt0'T M τ cv0 W) j =
      lcStT M (flG' τ W) (flSt0'T M τ cv0 W) j := lcStT_congr _ fun i hi => (hfG' i hi).symm
  have hLc8 := hLc 8 le_rfl
  have hRc : (List.range 8).map (lcChT M (pairAt ws2) (flSt0'T M τ cv0 W)) = flRcT M τ cv0 W :=
    List.map_congr_left fun j hj => lcChT_congr _ (fun i hi => (hfG' i hi).symm)
      (List.mem_range.mp hj)
  simp only [hLc8, hRc] at hS hc7 hA4 hT hout
  have hα : challengeOf (sqCvT M (obsCvT M (obsCvT M (flScT M τ cv0 W).2 a) b)) =
      flAlphaT M τ cv0 W := by simp only [flAlphaT, flCv5T, flCv4T, hfA, hfB]
  have hz : challengeOf (sqCvT M (obsAllT M ((sqCvT M)^[τ + 1] cv0) p)) = flZT M τ cv0 W := by
    simp only [flZT, flCvPT, flCvST, hfP]
  simp only [hα, hz] at hT hA1 hA2
  rw [← hfS] at hT hS
  simp only [Prod.mk.injEq] at hout
  obtain ⟨ho1, ho2⟩ := hout
  have hrc : rcs = flRcT M τ cv0 W := (List.reverse_injective hA4).symm
  have hchi : chi = flChiT M τ cv0 W := by
    rw [← List.take_append_drop 8 chi, ← List.take_append_drop 8 (flChiT M τ cv0 W), ← hA3]
    rw [hrc] at ho1
    exact congrArg _ (List.append_cancel_left ho1)
  refine ⟨hlen, hA2.symm, hA1.symm, hchi, hrc, hfS.symm, hT, ?_, ?_⟩
  · simp only [h0, hSc8, hscE, hs0', hLc8, hfS]
    rfl
  refine ⟨hsam, ?_, ?_, fun j hj => ?_, ?_, ?_, ?_, fun j hj => ?_, hS⟩
  · rw [flCvST, hfP]; exact hP1
  · rw [flCvPT, flCvST, hfP]; exact hc3
  · have := hok j (by omega)
    rw [hfG j hj, ← hSc j (by omega)]
    exact this
  · rw [flCv4T, hfA]; exact hc4
  · rw [flCv5T, flCv4T, hfA, hfB]; exact hc5
  · rw [flCv5T, flCv4T, hfA, hfB]; exact hc6
  · have := hok2 j hj
    rw [hfG' j hj, ← hLc j (by omega)]
    exact this

end
end LeanVM.Guest.B1
