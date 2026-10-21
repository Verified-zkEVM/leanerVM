/-
  LeanVM.Guest.B1.Tables.FlockSpecM

  `verifyFlock` over a hash model, phase by phase: the sumchecks round by round over the model's
  total hash, each round's hashes answered, and the whole run.
-/

module

public import LeanVM.Guest.B1.Tables.FlockSpec
public import LeanVM.Guest.B1.Tables.FlockLoopsM
public import LeanVM.Guest.B1.VerifySub.RunM

/-!
# `verifyFlock` over a hash model, phase by phase

`FlockSpec.lean` over a hash model `M`: `scStT`, `scChT`, `lcStT`, `lcChT` are `scSt`, `scCh`,
`lcSt`, `lcCh` over the model's total hash (`scStepT`, `lcStepT`); when every round's hashes are
answered (`RoundOk`) the sumchecks run over the model round by round (`runs_sumcheck_eqM`,
`runs_sumcheck_plainM`). `sqAllM_iter`: squeezes answered at every iterate of `sqCvT`.
`runs_verifyFlockM` assembles `verifyFlock ev (14 + τ)` over the model from its phases.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-! ## The sumchecks round by round over the total hash -/

/-- The equality-mode sumcheck's claim and chain after `j` rounds, over the model's total hash
(`scSt`). -/
def scStT (M : HashModel) (e : ℕ → E) (g : ℕ → E × E) (s0 : E × Digest) : ℕ → E × Digest
  | 0 => s0
  | j + 1 => (scStepT M (e j) (g j) (scStT M e g s0 j)).2

/-- Its challenge at round `j` (`scCh`). -/
def scChT (M : HashModel) (e : ℕ → E) (g : ℕ → E × E) (s0 : E × Digest) (j : ℕ) : E :=
  (scStepT M (e j) (g j) (scStT M e g s0 j)).1

/-- The plain-mode sumcheck's claim and chain after `j` rounds, over the model's total hash
(`lcSt`). -/
def lcStT (M : HashModel) (g : ℕ → E × E) (s0 : E × Digest) : ℕ → E × Digest
  | 0 => s0
  | j + 1 => (lcStepT M (g j) (lcStT M g s0 j)).2

/-- Its challenge at round `j` (`lcCh`). -/
def lcChT (M : HashModel) (g : ℕ → E × E) (s0 : E × Digest) (j : ℕ) : E :=
  (lcStepT M (g j) (lcStT M g s0 j)).1

variable {M : HashModel}

/-- Two words absorbed, both answered at the total hash. -/
theorem obsAllM_two {cv : Digest} {g1 g2 : E} (h1 : obsCvM M cv g1 = some (obsCvT M cv g1))
    (h2 : obsCvM M (obsCvT M cv g1) g2 = some (obsCvT M (obsCvT M cv g1) g2)) :
    obsAllM M cv [g1, g2] = some (obsCvT M (obsCvT M cv g1) g2) := by
  simp [obsAllM, h1, h2]

/-- An equality-mode round's words read over the model (`runs_roundEq`). -/
theorem runs_roundEqM (c e g1 g2 : E) (cv : Digest) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) (h1 : obsCvM M cv g1 = some (obsCvT M cv g1))
    (h2 : obsCvM M (obsCvT M cv g1) g2 = some (obsCvT M (obsCvT M cv g1) g2)) :
    RunsM M (sumcheckRoundPoly 3 c (some e)) ⟨cv, g1 :: g2 :: rest, os, roots⟩
      [c + e * sumE [g1, g2], g1, g2] ⟨obsCvT M (obsCvT M cv g1) g2, rest, os, roots⟩ := by
  simp only [sumcheckRoundPoly, Prog.bind_eq, Prog.pure_eq]
  exact RunsM.bind (RunsToM.runs (runsToM_readN (obsAllM_two h1 h2)) rest os roots) (RunsM.ret _ _)

/-- A plain-mode round's words read over the model (`runs_roundPlain`). -/
theorem runs_roundPlainM (c c0 c2 : E) (cv : Digest) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) (h1 : obsCvM M cv c0 = some (obsCvT M cv c0))
    (h2 : obsCvM M (obsCvT M cv c0) c2 = some (obsCvT M (obsCvT M cv c0) c2)) :
    RunsM M (sumcheckRoundPoly 3 c none) ⟨cv, c0 :: c2 :: rest, os, roots⟩
      [c0, c + sumE [c2], c2] ⟨obsCvT M (obsCvT M cv c0) c2, rest, os, roots⟩ := by
  simp only [sumcheckRoundPoly, Prog.bind_eq, Prog.pure_eq]
  exact RunsM.bind (RunsToM.runs (runsToM_readE h1) _ os roots)
    (RunsM.bind (RunsToM.runs (runsToM_readN (xs := [c2]) (by simp [obsAllM, h2])) rest os roots)
      (RunsM.ret _ _))

/-- **The equality-mode sumcheck over the model**, every round's hashes answered, runs round by
round (`runs_sumcheck_eq`). -/
theorem runs_sumcheck_eqM (e : ℕ → E) (g : ℕ → E × E) (s0 : E × Digest) :
    ∀ n k (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
      (∀ j < n, RoundOk M (g (k + j)) (scStT M e g s0 (k + j)).2) →
      RunsM M (sumcheck (scStT M e g s0 k).1 3 ((List.range n).map fun j => some (e (k + j))))
        ⟨(scStT M e g s0 k).2, roundWords g n k ++ rest, os, roots⟩
        ((List.range n).map fun j => scChT M e g s0 (k + j), (scStT M e g s0 (k + n)).1)
        ⟨(scStT M e g s0 (k + n)).2, rest, os, roots⟩
  | 0, k, rest, os, roots, _ => by
    simp only [List.range_zero, List.map_nil, Nat.add_zero, roundWords, List.flatten_nil,
      List.nil_append, sumcheck]
    exact RunsM.ret _ _
  | n + 1, k, rest, os, roots, hok => by
    have ih := runs_sumcheck_eqM e g s0 n (k + 1) rest os roots fun j hj => by
      have := hok (j + 1) (by omega)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    obtain ⟨o1, o2, o3⟩ := hok 0 (by omega)
    rw [Nat.add_zero] at o1 o2 o3
    have hp : polyEval [(scStT M e g s0 k).1 + e k * sumE [(g k).1, (g k).2], (g k).1, (g k).2]
        (scChT M e g s0 k) = (scStT M e g s0 (k + 1)).1 := by
      simp only [polyEval, sumE, scChT, scStT, scStepT, List.foldr, List.foldl]
      ring
    rw [show (List.range (n + 1)).map (fun j => some (e (k + j))) = some (e k) ::
        (List.range n).map (fun j => some (e (k + 1 + j))) from
        map_range_succ_shift (fun j => some (e j)) n k,
      show (List.range (n + 1)).map (fun j => scChT M e g s0 (k + j)) = scChT M e g s0 k ::
        (List.range n).map (fun j => scChT M e g s0 (k + 1 + j)) from
        map_range_succ_shift (scChT M e g s0) n k, roundWords_succ,
      show k + (n + 1) = k + 1 + n by omega, sumcheck,
      Prog.bind_eq]
    refine RunsM.bind (runs_roundEqM _ _ _ _ _ _ os roots o1 o2) ?_
    simp only [Prog.bind_eq]
    refine RunsM.bind (RunsToM.runs (runsToM_sampleE o3) _ os roots) ?_
    rw [show challengeOf (sqCvT M (obsCvT M (obsCvT M (scStT M e g s0 k).2 (g k).1) (g k).2)) =
      scChT M e g s0 k from rfl, hp]
    refine RunsM.bind ih ?_
    exact RunsM.ret _ _

/-- **The plain-mode sumcheck over the model**, every round's hashes answered, runs round by
round (`runs_sumcheck_plain`). -/
theorem runs_sumcheck_plainM (g : ℕ → E × E) (s0 : E × Digest) :
    ∀ n k (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
      (∀ j < n, RoundOk M (g (k + j)) (lcStT M g s0 (k + j)).2) →
      RunsM M (sumcheck (lcStT M g s0 k).1 3 ((List.range n).map fun _ => none))
        ⟨(lcStT M g s0 k).2, roundWords g n k ++ rest, os, roots⟩
        ((List.range n).map fun j => lcChT M g s0 (k + j), (lcStT M g s0 (k + n)).1)
        ⟨(lcStT M g s0 (k + n)).2, rest, os, roots⟩
  | 0, k, rest, os, roots, _ => by
    simp only [List.range_zero, List.map_nil, Nat.add_zero, roundWords, List.flatten_nil,
      List.nil_append, sumcheck]
    exact RunsM.ret _ _
  | n + 1, k, rest, os, roots, hok => by
    have ih := runs_sumcheck_plainM g s0 n (k + 1) rest os roots fun j hj => by
      have := hok (j + 1) (by omega)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    obtain ⟨o1, o2, o3⟩ := hok 0 (by omega)
    rw [Nat.add_zero] at o1 o2 o3
    have hp : polyEval [(g k).1, (lcStT M g s0 k).1 + sumE [(g k).2], (g k).2] (lcChT M g s0 k) =
        (lcStT M g s0 (k + 1)).1 := by
      simp only [polyEval, sumE, lcChT, lcStT, lcStepT, List.foldr, List.foldl]
      ring
    rw [show (List.range (n + 1)).map (fun _ => (none : Option E)) = none ::
        (List.range n).map (fun _ => none) from map_range_succ_shift (fun _ => none) n k,
      show (List.range (n + 1)).map (fun j => lcChT M g s0 (k + j)) = lcChT M g s0 k ::
        (List.range n).map (fun j => lcChT M g s0 (k + 1 + j)) from
        map_range_succ_shift (lcChT M g s0) n k, roundWords_succ,
      show k + (n + 1) = k + 1 + n by omega, sumcheck, Prog.bind_eq]
    refine RunsM.bind (runs_roundPlainM _ _ _ _ _ os roots o1 o2) ?_
    simp only [Prog.bind_eq]
    refine RunsM.bind (RunsToM.runs (runsToM_sampleE o3) _ os roots) ?_
    rw [show challengeOf (sqCvT M (obsCvT M (obsCvT M (lcStT M g s0 k).2 (g k).1) (g k).2)) =
      lcChT M g s0 k from rfl, hp]
    refine RunsM.bind ih ?_
    exact RunsM.ret _ _

/-! ## The sampled coordinates over the total hash -/

/-- **Squeezes answered at every iterate** of the total `sqCvT`: `sqAllM` is the iterate's
challenges and state (`sqAll_eq`). -/
theorem sqAllM_iter : ∀ (n : ℕ) (cv : Digest),
    (∀ t < n, sqCvM M ((sqCvT M)^[t] cv) = some ((sqCvT M)^[t + 1] cv)) →
    sqAllM M n cv =
      some ((List.range n).map fun t => challengeOf (sqCvT M ((sqCvT M)^[t] cv)), (sqCvT M)^[n] cv)
  | 0, _, _ => rfl
  | n + 1, cv, h => by
    have h0 : sqCvM M cv = some (sqCvT M cv) := h 0 (by omega)
    have ih := sqAllM_iter n (sqCvT M cv) fun t ht => by
      have := h (t + 1) (by omega)
      simp only [Function.iterate_succ_apply] at this
      exact this
    rw [sqAllM, h0, Option.bind_some, ih, Option.map_some, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp only [Function.iterate_zero_apply, Function.iterate_succ_apply, Function.comp_def]

/-! ## The whole run -/

/-- `n` words read over the model (`runs_readN`). -/
theorem runs_readNM {cv cv' : Digest} (xs rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) {n : ℕ} (hn : xs.length = n) (h : obsAllM M cv xs = some cv') :
    RunsM M (Prog.readN n) ⟨cv, xs ++ rest, os, roots⟩ xs ⟨cv', rest, os, roots⟩ := by
  subst hn; exact RunsToM.runs (runsToM_readN h) rest os roots

/-- **`verifyFlock ev (14 + τ)` over the model from its phases** (`runs_verifyFlock`): the
`τ + 1` sampled coordinates `sam`, round 1's 64 words `p`, the skip challenge, the
equality-mode sumcheck over the fixed then sampled coordinates, the final evaluations `a`, `b`,
the lincheck's `alpha`, its plain-mode sumcheck, the 64 slices `s`, and the terminal identity
with the matrices' value `mv` that `ev` takes over the model; every hash answered. -/
theorem runs_verifyFlockM (ev : Evaluations) (τ : ℕ) (cv0 : Digest) (sam : List E)
    (cvS : Digest) (hsam : sqAllM M (τ + 1) cv0 = some (sam, cvS)) (p : List E)
    (hp : p.length = 64) (cvP : Digest) (hP : obsAllM M cvS p = some cvP) (cz : Digest)
    (hz : sqCvM M cvP = some cz) (ys chi : List E) (running : E) (cv4 : Digest)
    (hsc : ∀ (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
      RunsM M (sumcheck (lagrangeInterpolate 128 (List.replicate 64 0 ++ p) (challengeOf cz)) 3
          ((fixedChallenges ++ sam).map some))
        ⟨cz, ys ++ rest, os, roots⟩ (chi, running) ⟨cv4, rest, os, roots⟩)
    (a b : E) (ca cb cα : Digest) (ha : obsCvM M cv4 a = some ca) (hb : obsCvM M ca b = some cb)
    (hα : sqCvM M cb = some cα) (zs rc : List E) (rLc : E) (cv7 : Digest)
    (hlc : ∀ (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
      RunsM M (sumcheck (a + challengeOf cα * b + challengeOf cα ^ 2 * (running + a * b) +
          challengeOf cα ^ 3) 3 (List.replicate 8 none))
        ⟨cα, zs ++ rest, os, roots⟩ (rc, rLc) ⟨cv7, rest, os, roots⟩)
    (s : List E) (hs : s.length = 64) (cv8 : Digest) (hS : obsAllM M cv7 s = some cv8) (mv : E)
    (hmv : MatricesAtM M ev (challengeOf cα) (challengeOf cz) (chi.take 8) rc.reverse s mv)
    (hterm : mv + challengeOf cα ^ 2 * eqEval (chi.take 8) rc.reverse *
        dot (lagrangeWeights 64 (challengeOf cz)) s +
        challengeOf cα ^ 3 * (lincheckColumnWeights rc.reverse s).getD 512 0 = rLc) :
    RunsToM M (verifyFlock ev (14 + τ)) cv0 (p ++ ys ++ [a, b] ++ zs ++ s)
      (rc.reverse ++ chi.drop 8, s) cv8 := by
  intro rest os roots
  have hsamp : 14 + τ - flockKSkip - fixedChallenges.length = τ + 1 := by
    rw [flockKSkip_eq, fixedChallenges_length]; omega
  show RunsM M _ _ _ _
  simp only [verifyFlock, verifyFlockZerocheck, verifyFlockLincheck, Prog.bind_eq, Prog.pure_eq,
    Prog.bind_assoc, Prog.ret_bind, hsamp, flockNumLincheckRounds_eq, List.append_assoc,
    List.cons_append, List.nil_append]
  refine RunsM.bind (RunsToM.runs (runsToM_sampleN hsam) _ os roots) ?_
  refine RunsM.bind (runs_readNM p _ os roots (by rw [hp]; rfl) hP) ?_
  refine RunsM.bind (RunsToM.runs (runsToM_sampleE hz) _ os roots) ?_
  refine RunsM.bind (hsc _ os roots) ?_
  refine RunsM.bind (RunsToM.runs (runsToM_readE ha) _ os roots) ?_
  refine RunsM.bind (RunsToM.runs (runsToM_readE hb) _ os roots) ?_
  refine RunsM.bind (RunsToM.runs (runsToM_sampleE hα) _ os roots) ?_
  refine RunsM.bind (hlc _ os roots) ?_
  refine RunsM.bind (runs_readNM s _ os roots (by rw [hs]; rfl) hS) ?_
  refine RunsM.bind (hmv _) ?_
  rw [require_pos (by simpa [blake2sConstantColumn, kBits] using hterm)]
  exact RunsM.ret _ _

end
end LeanVM.Guest.B1
