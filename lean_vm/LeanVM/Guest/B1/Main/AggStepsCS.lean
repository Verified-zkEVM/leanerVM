/-
  LeanVM.Guest.B1.Main.AggStepsCS

  `AggStepsC.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Main.AggStepsC
public import LeanVM.Guest.B1.BasicS
public import LeanVM.Guest.B1.Main.CalleesWM

/-!
# `AggStepsC.lean` under any `BLAKE2S` semantics

Each definition and lemma of `AggStepsC.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem}

variable {rd : Reader}

/-- **A `mul_range` loop, backward**: its helper holds from `g^0` to `N = g^m`, `0 < m`, once
the iteration at each `g^j`, `j < m`, holds at every depth given the next one. -/
theorem loopS_complete {f : String} {ps : List E} {N : E} {m : ℕ} {B : ℕ → Prop}
    (hm0 : 0 < m) (hN : N = gen ^ m) (hB : ∀ j < m, B j)
    (hstep : ∀ d j, B j → IsInK (gen ^ j * gen + N) →
      (gen ^ j * gen + N ≠ 0 → coreProgram.relNB S rd d f (gen ^ j * gen :: ps) []) →
      coreProgram.relNB S rd (d + 1) f (gen ^ j :: ps) []) :
    coreProgram.RelB S rd f (1 :: ps) [] := by
  have hK : ∀ j, IsInK (gen ^ j * gen + N) := fun j => by
    rw [hN]
    exact isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
  have key : ∀ t j, j + t + 1 = m → coreProgram.relNB S rd (t + 1) f (gen ^ j :: ps) [] := by
    intro t
    induction t with
    | zero =>
      intro j hj
      refine hstep 0 j (hB j (by omega)) (hK j) fun hne => absurd ?_ hne
      rw [gen_pow_add_eq_zero_iff, hN]; congr 1; omega
    | succ t ih =>
      intro j hj
      refine hstep (t + 1) j (hB j (by omega)) (hK j) fun _ => ?_
      rw [gen_pow_mul_gen]
      exact ih (j + 1) (by omega)
  refine ⟨m, ?_⟩
  have := key (m - 1) 0 (by omega)
  rwa [pow_zero, show m - 1 + 1 = m by omega] at this

/-! ## `__loop97` -/

/-- **`__loop97` at `x = g^c`, backward**: the row's words give the iteration. -/
theorem loop97S_back {N frow crow bcp wsum lam : E} (d c : ℕ) (fp cp : E) (r f g : List E)
    (w lf lc : E) (hrl : r.length = 22) (hfl : f.length = 22) (hgl : g.length = 22)
    (hf : LoadHolds rd frow c fp) (hc : LoadHolds rd crow c cp) (hR : ReadsAt rd bcp r)
    (hF : ReadsAt rd fp f) (hG : ReadsAt rd cp g) (hw : LoadHolds rd wsum c w)
    (hlf : LoadHolds rd lam (2 * c) lf) (hlc : LoadHolds rd lam (2 * c + 1) lc)
    (hn : LoadHolds rd wsum (c + 1) (w + lf * eqEval f r + lc * eqEval g r))
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 →
      coreProgram.relNB S rd d "__loop97" [gen ^ c * gen, N, frow, crow, bcp, wsum, lam] []) :
    coreProgram.relNB S rd (d + 1) "__loop97" [gen ^ c, N, frow, crow, bcp, wsum, lam] [] := by
  set x := gen ^ c with hx
  have e2 : lam * (x * x) = lam * gen ^ (2 * c) := by rw [hx]; ring
  have ef : frow * x = frow * gen ^ c := rfl
  have ec : crow * x = crow * gen ^ c := rfl
  have ew : wsum * x = wsum * gen ^ c := rfl
  have eF : eqEval (f.take 22) (r.take 22) = eqEval f r := by
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  have eG : eqEval (g.take 22) (r.take 22) = eqEval g r := by
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  rw [relNS_succ_iff find_loop97]
  refine ⟨setl (setb (setl (Val.ofArgs [x, N, frow, crow, bcp, wsum, lam]) 7
      [frow * x, fp, crow * x, cp, r.getD 0 0, 1, f.getD 0 0, 1 + f.getD 0 0,
        1 + f.getD 0 0 + r.getD 0 0, 1, g.getD 0 0, 1 + g.getD 0 0, 1 + g.getD 0 0 + r.getD 0 0])
      20 21 11 (l97V r f g)) 251
    [x * x, wsum * x, w, lam * (x * x), lf, lf * eqEval f r, w + lf * eqEval f r, lam * (x * x), lc,
      lc * eqEval g r, w + lf * eqEval f r + lc * eqEval g r, wsum * x, gen, x * gen, x * gen + N,
      gen, x * gen],
    by simp only [show Fn.params Data.core569 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] from rfl,
      List.map_cons, List.map_nil]; b1_lookb, ?_⟩
  rw [core569_body, l97Body, holdsListB_append, holdsListB_append,
    holdsListB_flatten_range 21 (fun k => l97Coord (k + 1)) (fun _ => rfl)]
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen,
    word_one]
  b1_lookb
  rw [setb_lit (by omega) (by omega), setb_lit (by omega) (by omega)]
  simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, l97V, Nat.reduceAdd, eF, eG, ef, ec, ew,
    e2, loadHolds_mul_gen_pow, Nat.add_zero, true_and, and_true]
  refine ⟨hf, hc, readsAt_getD' hR (by omega), readsAt_getD' hF (by omega),
    readsAt_getD' hG (by omega), fun k hk => ?_, hw, hlf, hlc, hn, hK, hnext⟩
  simp only [l97Coord, Nat.add_sub_cancel, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, word_one,
    Nat.add_eq_right]
  rcases k with _ | k
  · simp only [↓reduceIte]
    b1_lookb
    simp only [l97V, Nat.reduceAdd, true_and, and_true]
    refine ⟨readsAt_getD' hR (by omega), readsAt_getD' hF (by omega), ?_,
      readsAt_getD' hG (by omega), ?_⟩ <;>
      (rw [eqEval_take_succ' _ _ 1 (by omega) (by omega), eqEval_take_one _ _ (by omega) (by omega)])
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, show 20 + 11 * (k + 1) - 6 = 20 + 11 * k + 5 by omega,
      show 20 + 11 * (k + 1) - 1 = 20 + 11 * k + 10 by omega]
    b1_lookb
    simp only [l97V, true_and, and_true]
    refine ⟨readsAt_getD' hR (by omega), readsAt_getD' hF (by omega), ?_,
      readsAt_getD' hG (by omega), ?_⟩ <;>
      (rw [show k + 1 + 2 = k + 2 + 1 by omega, eqEval_take_succ' _ _ (k + 2) (by omega) (by omega)])

/-! ## `__loop95` -/

end
end LeanVM.Guest.B1.Main
