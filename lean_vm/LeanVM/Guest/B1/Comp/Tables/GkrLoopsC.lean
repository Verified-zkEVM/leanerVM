/-
  LeanVM.Guest.B1.Comp.Tables.GkrLoopsC

  `verify_bus_gkr`'s two inner loops over a completeness model, backward: a layer's sumcheck
  rounds (`__loop101`) and the pair iterations (`__loop10`).
-/

module

public import LeanVM.Guest.B1.Comp.Tables.GkrInvC
public import LeanVM.Guest.B1.Comp.Tables.CompletesB
public import LeanVM.Guest.B1.Comp.FiatShamir
public import LeanVM.Guest.B1.Comp.Digest.Common
public import LeanVM.Guest.B1.Tables.GkrLoopsM

/-!
# `verify_bus_gkr`'s inner loops over a completeness model

`GkrComplete.lean`, `GkrComplete10.lean` and `GkrPair.lean` under a completeness model's
semantics, at the model's total hash:

* `loop101_stepC`, `loop101_completeC`: a layer's rounds, each round's `sumcheck_round5` the
  model's (`sumcheck_round5_comp`) on its answered run (`GkrRoundM CM.hm`);
* `l10ValsT`: `l10Vals` at the total hash (`sqValsT`, `gkrFsvT`, `l10cvT`); `loop10_stepC`: one
  pair iteration from the memory's honest words, its Fiat-Shamir blocks the model's answers;
  `L10IterC`, `loop10_completeC`, `pair_iterC`: the iterations' facts from a pair step's
  answered run (`PairOkM`), and the loop.

`__loop11` is free of `BLAKE2S` (`relB_loop11`): its deployed completeness carries over.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete LeanVM.Guest.B1.Sig

@[expose] public section

/-! ## `__loop101` -/

/-- **`__loop101`, one round, backward, over a completeness model** (`loop101_back`): the
round's `sumcheck_round5` the model's on its answered run. -/
theorem loop101_stepC {CM : CompModel} {rd : Reader} {N rounds pos prow nrow x : E}
    (hb : GkrRoundM CM.hm rd rounds pos prow nrow x) (hK : IsInK (x * gen + N))
    (hnext : x * gen + N ≠ 0 →
      coreProgram.RelB CM.sem rd "__loop101" [x * gen, N, rounds, pos, prow, nrow] []) :
    ∃ fn, coreProgram.find? "__loop101" = some fn ∧
      fn.SemB CM.sem (coreProgram.RelB CM.sem rd) rd [x, N, rounds, pos, prow, nrow] [] := by
  obtain ⟨cv, cur, claim, e, ws, claim', rk, cv', h0, h1, h2, h3, he, hwl, hws, hrun, hrk, h4, h5,
    h6, h7⟩ := hb
  obtain ⟨c1, c2, c3, c4, rfl⟩ := list_four ws hwl
  have hsc : coreProgram.RelB CM.sem rd "sumcheck_round5"
      [(digestScalars cv).1, (digestScalars cv).2, cur, claim, e]
      [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ 4, claim', rk] :=
    sumcheck_round5_comp rd _ _ ⟨cv, c1, c2, c3, c4, claim', rk, cv', rfl, hws, hrun, rfl⟩
  have e9 : rounds * (pos * x * (pos * x) * (pos * x * (pos * x))) = rounds * (pos * x) ^ 4 := by
    ring
  refine ⟨Data.core574, find_loop101, setl (Val.ofArgs [x, N, rounds, pos, prow, nrow]) 6
    [pos * x, pos * x * (pos * x),
    pos * x * (pos * x) * (pos * x * (pos * x)), rounds * (pos * x * (pos * x) * (pos * x * (pos * x))),
    (digestScalars cv).1, (digestScalars cv).2, cur, claim, prow * x, e, (digestScalars cv').1,
    (digestScalars cv').2, cur * gen ^ 4, claim', rk, nrow * x, gen, x * gen, x * gen + N, gen,
    x * gen], by
      simp only [show Fn.params Data.core574 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
        List.map_cons, List.map_nil]; b1_look, ?_⟩
  simp only [show Fn.body Data.core574 = Data.core574.body from rfl, Data.core574.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [true_and, and_true, e9]
  exact ⟨h0, h1, h2, h3, he, hsc, hrk, h4, h5, h6, h7, hK, hnext⟩

/-- **`__loop101` over a completeness model** (`loop101_complete`): `m` rounds of the layer's
sumcheck from the honest round states, each round's run answered. -/
theorem loop101_completeC {CM : CompModel} {rd : Reader} {rounds pos prow nrow : E} {m : ℕ}
    (hm0 : 0 < m) (hB : ∀ j < m, GkrRoundM CM.hm rd rounds pos prow nrow (gen ^ j)) :
    coreProgram.RelB CM.sem rd "__loop101" [1, gen ^ m, rounds, pos, prow, nrow] [] := by
  have := Digest.loopB_bwd (S := CM.sem) (B := GkrRoundM CM.hm rd rounds pos prow nrow)
    (fun x hb hK hcall => loop101_stepC hb hK hcall) (k := 0) (m := m) hm0 rfl
    (fun j _ hj => hB j hj)
  rwa [pow_zero] at this

/-! ## `__loop10` -/

/-- `sqVals` at the total hash: the squeeze's values, its output `sqCvT M cv`. -/
def sqValsT (M : HashModel) (cv : Digest) (k : ℕ) : E := sqValsD (sqCvT M cv) k

/-- `gkrFsv` at the total hash: an `fs_next` block's values from its first, the word read. -/
def gkrFsvT (M : HashModel) (x : E) (cv : Digest) : ℕ → E
  | 0 => x
  | k + 1 => fsValsD x (obsCvT M cv x) 1 k

/-- The honest values `6 ..` of one iteration of `__loop10` at the total hash (`l10Vals`). -/
noncomputable def l10ValsT (M : HashModel) (x N dsb gmu layers rounds shE : E) (cv : Digest) (cur v0 v1 v2 row pos : E)
    (cvT : Digest) (curT claimT : E) (es : ℕ → E) : List E :=
  [x * x,
    dsb * gmu,
    shE,
    (x * x) * shE,
    ((x * x) * shE) * ((x * x) * shE),
    (((x * x) * shE) * ((x * x) * shE)) * (((x * x) * shE) * ((x * x) * shE)),
    ((((x * x) * shE) * ((x * x) * shE)) * (((x * x) * shE) * ((x * x) * shE))) * ((((x * x) * shE) * ((x * x) * shE)) * (((x * x) * shE) * ((x * x) * shE))),
    layers * (((((x * x) * shE) * ((x * x) * shE)) * (((x * x) * shE) * ((x * x) * shE))) * ((((x * x) * shE) * ((x * x) * shE)) * (((x * x) * shE) * ((x * x) * shE)))),
    (digestScalars cv).1,
    (digestScalars cv).2,
    (sqValsT M cv 0),
    (sqValsT M cv 1),
    (sqValsT M cv 2),
    (sqValsT M cv 3),
    (sqValsT M cv 4),
    (sqValsT M cv 5),
    (sqValsT M cv 6),
    (sqValsT M cv 7),
    (sqValsT M cv 8),
    (sqValsT M cv 9),
    (sqValsT M cv 10),
    (sqValsT M cv 11),
    (sqValsT M cv 12),
    (sqValsT M cv 13),
    row,
    pos,
    pos * pos,
    (pos * pos) * (pos * pos),
    rounds * ((pos * pos) * (pos * pos)),
    cur,
    v0,
    v1,
    v2,
    ((sqValsT M cv 13)) * v2,
    v1 + (((sqValsT M cv 13)) * v2),
    ((sqValsT M cv 13)) * (v1 + (((sqValsT M cv 13)) * v2)),
    v0 + (((sqValsT M cv 13)) * (v1 + (((sqValsT M cv 13)) * v2))),
    word 1 0 0,
    (word 1 0 0) + ((x * x) * shE),
    word 1 0 0,
    word 1099511627776 0 0,
    row * (word 1099511627776 0 0),
    pos * ((x * x) * shE),
    (pos * ((x * x) * shE)) * (pos * ((x * x) * shE)),
    ((pos * ((x * x) * shE)) * (pos * ((x * x) * shE))) * ((pos * ((x * x) * shE)) * (pos * ((x * x) * shE))),
    rounds * (((pos * ((x * x) * shE)) * (pos * ((x * x) * shE))) * ((pos * ((x * x) * shE)) * (pos * ((x * x) * shE)))),
    (digestScalars cvT).1,
    (digestScalars cvT).2,
    curT,
    claimT,
    (es 0),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 1),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 2),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 3),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 4),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 5),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 6),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 7),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 8),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 9),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 10),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 11),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 12),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 13),
    (gkrFsvT M (es 0) (l10cvT M cvT es 0) 14),
    (es 0),
    (es 1),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 1),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 2),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 3),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 4),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 5),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 6),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 7),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 8),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 9),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 10),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 11),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 12),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 13),
    (gkrFsvT M (es 1) (l10cvT M cvT es 1) 14),
    (es 1),
    (es 2),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 1),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 2),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 3),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 4),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 5),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 6),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 7),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 8),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 9),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 10),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 11),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 12),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 13),
    (gkrFsvT M (es 2) (l10cvT M cvT es 2) 14),
    (es 2),
    (es 3),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 1),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 2),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 3),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 4),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 5),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 6),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 7),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 8),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 9),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 10),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 11),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 12),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 13),
    (gkrFsvT M (es 3) (l10cvT M cvT es 3) 14),
    (es 3),
    (es 4),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 1),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 2),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 3),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 4),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 5),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 6),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 7),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 8),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 9),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 10),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 11),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 12),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 13),
    (gkrFsvT M (es 4) (l10cvT M cvT es 4) 14),
    (es 4),
    (es 5),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 1),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 2),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 3),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 4),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 5),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 6),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 7),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 8),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 9),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 10),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 11),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 12),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 13),
    (gkrFsvT M (es 5) (l10cvT M cvT es 5) 14),
    (es 5),
    (es 6),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 1),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 2),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 3),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 4),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 5),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 6),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 7),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 8),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 9),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 10),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 11),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 12),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 13),
    (gkrFsvT M (es 6) (l10cvT M cvT es 6) 14),
    (es 6),
    (es 7),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 1),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 2),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 3),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 4),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 5),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 6),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 7),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 8),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 9),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 10),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 11),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 12),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 13),
    (gkrFsvT M (es 7) (l10cvT M cvT es 7) 14),
    (es 7),
    (es 8),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 1),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 2),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 3),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 4),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 5),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 6),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 7),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 8),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 9),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 10),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 11),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 12),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 13),
    (gkrFsvT M (es 8) (l10cvT M cvT es 8) 14),
    (es 8),
    (es 9),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 1),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 2),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 3),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 4),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 5),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 6),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 7),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 8),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 9),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 10),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 11),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 12),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 13),
    (gkrFsvT M (es 9) (l10cvT M cvT es 9) 14),
    (es 9),
    (es 10),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 1),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 2),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 3),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 4),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 5),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 6),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 7),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 8),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 9),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 10),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 11),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 12),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 13),
    (gkrFsvT M (es 10) (l10cvT M cvT es 10) 14),
    (es 10),
    (es 11),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 1),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 2),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 3),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 4),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 5),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 6),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 7),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 8),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 9),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 10),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 11),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 12),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 13),
    (gkrFsvT M (es 11) (l10cvT M cvT es 11) 14),
    (es 11),
    ((es 8)) * ((es 9)),
    (((es 8)) * ((es 9))) * ((es 10)),
    ((((es 8)) * ((es 9))) * ((es 10))) * ((es 11)),
    word 0 0 0,
    ((sqValsT M cv 13)) * (word 0 0 0),
    (((((es 8)) * ((es 9))) * ((es 10))) * ((es 11))) + (((sqValsT M cv 13)) * (word 0 0 0)),
    ((es 4)) * ((es 5)),
    (((es 4)) * ((es 5))) * ((es 6)),
    ((((es 4)) * ((es 5))) * ((es 6))) * ((es 7)),
    ((sqValsT M cv 13)) * ((((((es 8)) * ((es 9))) * ((es 10))) * ((es 11))) + (((sqValsT M cv 13)) * (word 0 0 0))),
    (((((es 4)) * ((es 5))) * ((es 6))) * ((es 7))) + (((sqValsT M cv 13)) * ((((((es 8)) * ((es 9))) * ((es 10))) * ((es 11))) + (((sqValsT M cv 13)) * (word 0 0 0)))),
    ((es 0)) * ((es 1)),
    (((es 0)) * ((es 1))) * ((es 2)),
    ((((es 0)) * ((es 1))) * ((es 2))) * ((es 3)),
    ((sqValsT M cv 13)) * ((((((es 4)) * ((es 5))) * ((es 6))) * ((es 7))) + (((sqValsT M cv 13)) * ((((((es 8)) * ((es 9))) * ((es 10))) * ((es 11))) + (((sqValsT M cv 13)) * (word 0 0 0))))),
    (((((es 0)) * ((es 1))) * ((es 2))) * ((es 3))) + (((sqValsT M cv 13)) * ((((((es 4)) * ((es 5))) * ((es 6))) * ((es 7))) + (((sqValsT M cv 13)) * ((((((es 8)) * ((es 9))) * ((es 10))) * ((es 11))) + (((sqValsT M cv 13)) * (word 0 0 0)))))),
    (sqValsT M (l10cvT M cvT es 12) 0),
    (sqValsT M (l10cvT M cvT es 12) 1),
    (sqValsT M (l10cvT M cvT es 12) 2),
    (sqValsT M (l10cvT M cvT es 12) 3),
    (sqValsT M (l10cvT M cvT es 12) 4),
    (sqValsT M (l10cvT M cvT es 12) 5),
    (sqValsT M (l10cvT M cvT es 12) 6),
    (sqValsT M (l10cvT M cvT es 12) 7),
    (sqValsT M (l10cvT M cvT es 12) 8),
    (sqValsT M (l10cvT M cvT es 12) 9),
    (sqValsT M (l10cvT M cvT es 12) 10),
    (sqValsT M (l10cvT M cvT es 12) 11),
    (sqValsT M (l10cvT M cvT es 12) 12),
    (sqValsT M (l10cvT M cvT es 12) 13),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 0),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 1),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 2),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 3),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 4),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 5),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 6),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 7),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 8),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 9),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 10),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 11),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 12),
    (sqValsT M (sqCvT M (l10cvT M cvT es 12)) 13),
    word 4096 0 0,
    curT * (word 4096 0 0),
    ((es 0)) + ((es 1)),
    ((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 0)) + ((es 1))),
    ((es 0)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 0)) + ((es 1)))),
    ((es 2)) + ((es 3)),
    ((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 2)) + ((es 3))),
    ((es 2)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 2)) + ((es 3)))),
    (((es 0)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 0)) + ((es 1))))) + (((es 2)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 2)) + ((es 3))))),
    ((sqValsT M (sqCvT M (l10cvT M cvT es 12)) 13)) * ((((es 0)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 0)) + ((es 1))))) + (((es 2)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 2)) + ((es 3)))))),
    (((es 0)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 0)) + ((es 1))))) + (((sqValsT M (sqCvT M (l10cvT M cvT es 12)) 13)) * ((((es 0)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 0)) + ((es 1))))) + (((es 2)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 2)) + ((es 3))))))),
    ((es 4)) + ((es 5)),
    ((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 4)) + ((es 5))),
    ((es 4)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 4)) + ((es 5)))),
    ((es 6)) + ((es 7)),
    ((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 6)) + ((es 7))),
    ((es 6)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 6)) + ((es 7)))),
    (((es 4)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 4)) + ((es 5))))) + (((es 6)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 6)) + ((es 7))))),
    ((sqValsT M (sqCvT M (l10cvT M cvT es 12)) 13)) * ((((es 4)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 4)) + ((es 5))))) + (((es 6)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 6)) + ((es 7)))))),
    (((es 4)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 4)) + ((es 5))))) + (((sqValsT M (sqCvT M (l10cvT M cvT es 12)) 13)) * ((((es 4)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 4)) + ((es 5))))) + (((es 6)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 6)) + ((es 7))))))),
    ((es 8)) + ((es 9)),
    ((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 8)) + ((es 9))),
    ((es 8)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 8)) + ((es 9)))),
    ((es 10)) + ((es 11)),
    ((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 10)) + ((es 11))),
    ((es 10)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 10)) + ((es 11)))),
    (((es 8)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 8)) + ((es 9))))) + (((es 10)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 10)) + ((es 11))))),
    ((sqValsT M (sqCvT M (l10cvT M cvT es 12)) 13)) * ((((es 8)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 8)) + ((es 9))))) + (((es 10)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 10)) + ((es 11)))))),
    (((es 8)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 8)) + ((es 9))))) + (((sqValsT M (sqCvT M (l10cvT M cvT es 12)) 13)) * ((((es 8)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 8)) + ((es 9))))) + (((es 10)) + (((sqValsT M (l10cvT M cvT es 12) 13)) * (((es 10)) + ((es 11))))))),
    word 1099511627776 0 0,
    row * (word 1099511627776 0 0),
    pos * ((x * x) * shE),
    word 2 0 0,
    (pos * ((x * x) * shE)) * (word 2 0 0),
    word 2 0 0,
    x * (word 2 0 0),
    (x * (word 2 0 0)) + N,
    word 2 0 0,
    x * (word 2 0 0)]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`__loop10`, one iteration, backward, over a completeness model** (`loop10_back`): from the
memory's honest words at the total hash, the iteration's hashes answered, and the callees. -/
theorem loop10_stepC {CM : CompModel} {rd : Reader} {x N dsb gmu layers rounds shE : E} {cv cvT : Digest}
    {cur v0 v1 v2 row pos curT claimT : E} {es : ℕ → E}
    (hds : LoadHolds rd (dsb * gmu) 0 shE)
    (hl0 : LoadHolds rd (layers * (x * x * shE) ^ 8) 0 (digestScalars cv).1)
    (hl1 : LoadHolds rd (layers * (x * x * shE) ^ 8) 1 (digestScalars cv).2)
    (hl2 : LoadHolds rd (layers * (x * x * shE) ^ 8) 2 cur)
    (hl3 : LoadHolds rd (layers * (x * x * shE) ^ 8) 3 v0)
    (hl4 : LoadHolds rd (layers * (x * x * shE) ^ 8) 4 v1)
    (hl5 : LoadHolds rd (layers * (x * x * shE) ^ 8) 5 v2)
    (hl6 : LoadHolds rd (layers * (x * x * shE) ^ 8) 6 row)
    (hl7 : LoadHolds rd (layers * (x * x * shE) ^ 8) 7 pos)
    (hh0 : LoadHolds rd (rounds * pos ^ 4) 0 (digestScalars (sqCvT CM.hm cv)).1)
    (hh1 : LoadHolds rd (rounds * pos ^ 4) 1 (digestScalars (sqCvT CM.hm cv)).2)
    (hh2 : LoadHolds rd (rounds * pos ^ 4) 2 cur)
    (hh3 : LoadHolds rd (rounds * pos ^ 4) 3 (v0 + challengeOf (sqCvT CM.hm cv) * (v1 + challengeOf (sqCvT CM.hm cv) * v2)))
    (ht0 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 0 (digestScalars cvT).1)
    (ht1 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 1 (digestScalars cvT).2)
    (ht2 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 2 curT)
    (ht3 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 3 claimT)
    (hr0 : LoadHolds rd (row) 40 (challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12))))
    (hr1 : LoadHolds rd (row) 41 (challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))))
    (hn16 : LoadHolds rd (layers * (x * x * shE) ^ 8) 16 (digestScalars (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))).1)
    (hn17 : LoadHolds rd (layers * (x * x * shE) ^ 8) 17 (digestScalars (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))).2)
    (hn18 : LoadHolds rd (layers * (x * x * shE) ^ 8) 18 (curT * gen ^ 12))
    (hn19 : LoadHolds rd (layers * (x * x * shE) ^ 8) 19 ((((es 0)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 0)) + ((es 1))))) + (((challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12))))) * ((((es 0)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 0)) + ((es 1))))) + (((es 2)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 2)) + ((es 3)))))))))
    (hn20 : LoadHolds rd (layers * (x * x * shE) ^ 8) 20 ((((es 4)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 4)) + ((es 5))))) + (((challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12))))) * ((((es 4)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 4)) + ((es 5))))) + (((es 6)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 6)) + ((es 7)))))))))
    (hn21 : LoadHolds rd (layers * (x * x * shE) ^ 8) 21 ((((es 8)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 8)) + ((es 9))))) + (((challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12))))) * ((((es 8)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 8)) + ((es 9))))) + (((es 10)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 10)) + ((es 11)))))))))
    (hn22 : LoadHolds rd (layers * (x * x * shE) ^ 8) 22 (row * gen ^ 40))
    (hn23 : LoadHolds rd (layers * (x * x * shE) ^ 8) 23 (pos * (x * x * shE) * gen))
    (hK1 : IsInK (1 + (x * x * shE)))
    (h101 : 1 + (x * x * shE) ≠ 0 →
      coreProgram.RelB CM.sem rd "__loop101" [1, (x * x * shE), rounds, pos, row, row * gen ^ 40] [])
    (hc : ∀ i < 12, LoadHolds rd curT i (es i))
    (hcheck : claimT = es 0 * es 1 * es 2 * es 3 + challengeOf (sqCvT CM.hm cv) * (es 4 * es 5 * es 6 * es 7 + challengeOf (sqCvT CM.hm cv) * (es 8 * es 9 * es 10 * es 11)))
    (hK : IsInK (x * gen + N))
    (hnext : x * gen + N ≠ 0 → coreProgram.RelB CM.sem rd "__loop10" [x * gen, N, dsb, gmu, layers, rounds] [])
    (hq0 : sqCvM CM.hm cv = some (sqCvT CM.hm cv)) (hA : L10Ans CM.hm cvT es 12)
    (hq1 : sqCvM CM.hm (l10cvT CM.hm cvT es 12) = some (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))
    (hq2 : sqCvM CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12)) =
      some (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) :
    ∃ fn, coreProgram.find? "__loop10" = some fn ∧
      fn.SemB CM.sem (coreProgram.RelB CM.sem rd) rd [x, N, dsb, gmu, layers, rounds] [] := by
  refine ⟨Data.core40, find_loop10, ?_⟩
  set σ := setl (Val.ofArgs [x, N, dsb, gmu, layers, rounds]) 6 (l10ValsT CM.hm x N dsb gmu layers rounds shE cv cur v0 v1 v2 row pos
    cvT curT claimT es) with hσ
  refine ⟨σ, rfl, ?_⟩
  have e13 : σ (.n 13) = layers * (x * x * shE) ^ 8 := by show layers * _ = _; ring
  have e34 : σ (.n 34) = rounds * pos ^ 4 := by show rounds * _ = _; ring
  have e51 : σ (.n 51) = rounds * (pos * (x * x * shE)) ^ 4 := by show rounds * _ = _; ring
  have e44 : σ (.n 44) = 1 + (x * x * shE) := by show word 1 0 0 + _ = _; rw [word_one]
  have e45 : σ (.n 45) = 1 := word_one
  have e47 : σ (.n 47) = row * gen ^ 40 := by show row * word 1099511627776 0 0 = _; rw [word_g40]
  have e328 : σ (.n 328) = x * gen + N := by show x * word 2 0 0 + N = _; rw [word_gen]
  have e330 : σ (.n 330) = x * gen := by show x * word 2 0 0 = _; rw [word_gen]
  rw [core40_body, holdsListB_append, l10Pre_split]
  simp only [holdsListB_append, l10F]
  simp only [l10A0, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  refine ⟨rfl, rfl, hds, rfl, rfl, rfl, rfl, rfl, (by rw [e13]; exact hl0), (by rw [e13]; exact hl1), ?_⟩
  refine holdsB_squeezeT_comp _ _ _ ⟨⟨cv, sqCvT CM.hm cv, rfl, hq0, fun k hk => by interval_cases k <;> rfl⟩, ?_⟩
  simp only [l10A1, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  refine ⟨(by rw [e13]; exact hl6), (by rw [e13]; exact hl7), rfl, rfl, rfl, (by rw [e34]; exact hh0), (by rw [e34]; exact hh1), (by rw [e13]; exact hl2), (by rw [e34]; exact hh2), (by rw [e13]; exact hl3), (by rw [e13]; exact hl4), (by rw [e13]; exact hl5), rfl, rfl, rfl, rfl, (by rw [e34]; exact hh3), rfl, rfl, rfl, rfl, rfl, (by rw [e44]; exact hK1), (fun h => by rw [e44] at h; simp only [List.map_cons, List.map_nil]; rw [e45, e47]; exact h101 h), rfl, rfl, rfl, rfl, (by rw [e51]; exact ht0), (by rw [e51]; exact ht1), (by rw [e51]; exact ht2), (by rw [e51]; exact ht3), ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hc 0 (by norm_num), l10cvT CM.hm cvT es 0, l10cvT CM.hm cvT es (0 + 1), rfl, hA 0 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hc 1 (by norm_num), l10cvT CM.hm cvT es 1, l10cvT CM.hm cvT es (1 + 1), rfl, hA 1 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hc 2 (by norm_num), l10cvT CM.hm cvT es 2, l10cvT CM.hm cvT es (2 + 1), rfl, hA 2 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hc 3 (by norm_num), l10cvT CM.hm cvT es 3, l10cvT CM.hm cvT es (3 + 1), rfl, hA 3 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hc 4 (by norm_num), l10cvT CM.hm cvT es 4, l10cvT CM.hm cvT es (4 + 1), rfl, hA 4 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hc 5 (by norm_num), l10cvT CM.hm cvT es 5, l10cvT CM.hm cvT es (5 + 1), rfl, hA 5 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hc 6 (by norm_num), l10cvT CM.hm cvT es 6, l10cvT CM.hm cvT es (6 + 1), rfl, hA 6 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hc 7 (by norm_num), l10cvT CM.hm cvT es 7, l10cvT CM.hm cvT es (7 + 1), rfl, hA 7 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hc 8 (by norm_num), l10cvT CM.hm cvT es 8, l10cvT CM.hm cvT es (8 + 1), rfl, hA 8 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hc 9 (by norm_num), l10cvT CM.hm cvT es 9, l10cvT CM.hm cvT es (9 + 1), rfl, hA 9 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hc 10 (by norm_num), l10cvT CM.hm cvT es 10, l10cvT CM.hm cvT es (10 + 1), rfl, hA 10 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hc 11 (by norm_num), l10cvT CM.hm cvT es 11, l10cvT CM.hm cvT es (11 + 1), rfl, hA 11 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  simp only [l10A2, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by rw [show σ (.n 263) = claimT from by show (((((es 0)) * ((es 1))) * ((es 2))) * ((es 3))) + (((sqValsT CM.hm cv 13)) * ((((((es 4)) * ((es 5))) * ((es 6))) * ((es 7))) + (((sqValsT CM.hm cv 13)) * ((((((es 8)) * ((es 9))) * ((es 10))) * ((es 11))) + (((sqValsT CM.hm cv 13)) * (word 0 0 0)))))) = claimT; rw [hcheck]; simp only [sqValsT, sqValsD, word_zero]; ring]; exact e_add_self _), ?_⟩
  refine holdsB_squeezeT_comp _ _ _ ⟨⟨l10cvT CM.hm cvT es 12, sqCvT CM.hm (l10cvT CM.hm cvT es 12), rfl, hq1, fun k hk => by interval_cases k <;> rfl⟩, ?_⟩
  refine holdsB_squeezeT_comp _ _ _ ⟨⟨sqCvT CM.hm (l10cvT CM.hm cvT es 12), sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12)), rfl, hq2, fun k hk => by interval_cases k <;> rfl⟩, ?_⟩
  simp only [l10A3, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  refine ⟨hr0, hr1, (by rw [e13]; exact hn16), (by rw [e13]; exact hn17), rfl, rfl, (by rw [e13]; rw [show σ (.n 293) = curT * gen ^ 12 from by show curT * word 4096 0 0 = _; rw [word_g12]]; exact hn18), rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by rw [e13]; exact hn19), rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by rw [e13]; exact hn20), rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by rw [e13]; exact hn21), rfl, rfl, (by rw [e13]; rw [show σ (.n 322) = row * gen ^ 40 from by show row * word 1099511627776 0 0 = _; rw [word_g40]]; exact hn22), rfl, rfl, rfl, (by rw [e13]; rw [show σ (.n 325) = pos * (x * x * shE) * gen from by show pos * ((x * x) * shE) * word 2 0 0 = _; rw [word_gen]]; exact hn23), rfl, rfl, rfl, rfl, rfl, (by rw [e328]; exact hK), (fun h => by rw [e328] at h; simp only [List.map_cons, List.map_nil]; rw [e330]; exact hnext h), ?_⟩
  rfl


/-- The memory, callee and answered facts one iteration of `__loop10` needs, at `x`, over a
completeness model (`L10Iter`). -/
structure L10IterC (CM : CompModel) (rd : Reader) (N dsb gmu layers rounds x shE : E) (cv cvT : Digest)
    (cur v0 v1 v2 row pos curT claimT : E) (es : ℕ → E) : Prop where
  hds : LoadHolds rd (dsb * gmu) 0 shE
  hl0 : LoadHolds rd (layers * (x * x * shE) ^ 8) 0 (digestScalars cv).1
  hl1 : LoadHolds rd (layers * (x * x * shE) ^ 8) 1 (digestScalars cv).2
  hl2 : LoadHolds rd (layers * (x * x * shE) ^ 8) 2 cur
  hl3 : LoadHolds rd (layers * (x * x * shE) ^ 8) 3 v0
  hl4 : LoadHolds rd (layers * (x * x * shE) ^ 8) 4 v1
  hl5 : LoadHolds rd (layers * (x * x * shE) ^ 8) 5 v2
  hl6 : LoadHolds rd (layers * (x * x * shE) ^ 8) 6 row
  hl7 : LoadHolds rd (layers * (x * x * shE) ^ 8) 7 pos
  hh0 : LoadHolds rd (rounds * pos ^ 4) 0 (digestScalars (sqCvT CM.hm cv)).1
  hh1 : LoadHolds rd (rounds * pos ^ 4) 1 (digestScalars (sqCvT CM.hm cv)).2
  hh2 : LoadHolds rd (rounds * pos ^ 4) 2 cur
  hh3 : LoadHolds rd (rounds * pos ^ 4) 3 (v0 + challengeOf (sqCvT CM.hm cv) * (v1 + challengeOf (sqCvT CM.hm cv) * v2))
  ht0 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 0 (digestScalars cvT).1
  ht1 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 1 (digestScalars cvT).2
  ht2 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 2 curT
  ht3 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 3 claimT
  hr0 : LoadHolds rd (row) 40 (challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))
  hr1 : LoadHolds rd (row) 41 (challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12))))
  hn16 : LoadHolds rd (layers * (x * x * shE) ^ 8) 16 (digestScalars (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))).1
  hn17 : LoadHolds rd (layers * (x * x * shE) ^ 8) 17 (digestScalars (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))).2
  hn18 : LoadHolds rd (layers * (x * x * shE) ^ 8) 18 (curT * gen ^ 12)
  hn19 : LoadHolds rd (layers * (x * x * shE) ^ 8) 19 ((((es 0)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 0)) + ((es 1))))) + (((challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12))))) * ((((es 0)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 0)) + ((es 1))))) + (((es 2)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 2)) + ((es 3))))))))
  hn20 : LoadHolds rd (layers * (x * x * shE) ^ 8) 20 ((((es 4)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 4)) + ((es 5))))) + (((challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12))))) * ((((es 4)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 4)) + ((es 5))))) + (((es 6)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 6)) + ((es 7))))))))
  hn21 : LoadHolds rd (layers * (x * x * shE) ^ 8) 21 ((((es 8)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 8)) + ((es 9))))) + (((challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12))))) * ((((es 8)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 8)) + ((es 9))))) + (((es 10)) + (((challengeOf (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))) * (((es 10)) + ((es 11))))))))
  hn22 : LoadHolds rd (layers * (x * x * shE) ^ 8) 22 (row * gen ^ 40)
  hn23 : LoadHolds rd (layers * (x * x * shE) ^ 8) 23 (pos * (x * x * shE) * gen)
  hK1 : IsInK (1 + (x * x * shE))
  h101 : 1 + (x * x * shE) ≠ 0 → coreProgram.RelB CM.sem rd "__loop101" [1, (x * x * shE), rounds, pos, row, row * gen ^ 40] []
  hc : ∀ i < 12, LoadHolds rd curT i (es i)
  hcheck : claimT = es 0 * es 1 * es 2 * es 3 + challengeOf (sqCvT CM.hm cv) * (es 4 * es 5 * es 6 * es 7 +
    challengeOf (sqCvT CM.hm cv) * (es 8 * es 9 * es 10 * es 11))
  hq0 : sqCvM CM.hm cv = some (sqCvT CM.hm cv)
  hA : L10Ans CM.hm cvT es 12
  hq1 : sqCvM CM.hm (l10cvT CM.hm cvT es 12) = some (sqCvT CM.hm (l10cvT CM.hm cvT es 12))
  hq2 : sqCvM CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12)) =
    some (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm cvT es 12)))

/-- **`__loop10` over a completeness model** (`loop10_complete`): the `m` pair iterations from
their honest facts. -/
theorem loop10_completeC {CM : CompModel} {rd : Reader} {dsb gmu layers rounds : E} {m : ℕ}
    (hm0 : 0 < m)
    (hB : ∀ j < m, ∃ (shE : E) (cv cvT : Digest) (cur v0 v1 v2 row pos curT claimT : E)
      (es : ℕ → E), L10IterC CM rd (gen ^ m) dsb gmu layers rounds (gen ^ j) shE cv cvT cur v0 v1
        v2 row pos curT claimT es) :
    coreProgram.RelB CM.sem rd "__loop10" [1, gen ^ m, dsb, gmu, layers, rounds] [] := by
  have := Digest.loopB_bwd (S := CM.sem) (B := fun x => ∃ (shE : E) (cv cvT : Digest)
      (cur v0 v1 v2 row pos curT claimT : E) (es : ℕ → E), L10IterC CM rd (gen ^ m) dsb gmu layers
        rounds x shE cv cvT cur v0 v1 v2 row pos curT claimT es)
    (fun x hb hK hcall => by
      obtain ⟨shE, cv, cvT, cur, v0, v1, v2, row, pos, curT, claimT, es, it⟩ := hb
      exact loop10_stepC it.hds it.hl0 it.hl1 it.hl2 it.hl3 it.hl4 it.hl5 it.hl6 it.hl7 it.hh0
        it.hh1 it.hh2 it.hh3 it.ht0 it.ht1 it.ht2 it.ht3 it.hr0 it.hr1 it.hn16 it.hn17 it.hn18
        it.hn19 it.hn20 it.hn21 it.hn22 it.hn23 it.hK1 it.h101 it.hc it.hcheck hK hcall it.hq0 it.hA
        it.hq1 it.hq2)
    (k := 0) (m := m) hm0 rfl (fun j _ hj => hB j hj)
  rwa [pow_zero] at this

/-- **A pair step's iteration facts over a completeness model** (`pair_iter`): on a memory holding the layer `L = 2j + sh`, its row, the
round states, the next row and the next layer, `__loop10`'s iteration at `g^j` holds its facts. -/
theorem pair_iterC {CM : CompModel} {rd : Reader} {cv : Digest} {s : GkrState} {cur : E} {L : ℕ} (cl : ℕ → E)
    (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch es : ℕ → E) {v0 v1 v2 : E}
    (hvals : s.values = [v0, v1, v2])
    (hc0 : cl 0 = polyEval s.values (challengeOf (sqCvT CM.hm cv))) (hcv0 : cvr 0 = sqCvT CM.hm cv)
    (hr : ∀ r < L, (wsr r).length = 4 ∧ RunsToM CM.hm (roundPoly 5 (cl r) (some (s.point.getD r 0))) (cvr r)
      (wsr r) (cl (r + 1), ch r) (cvr (r + 1)))
    (hfin : cl L = es 0 * es 1 * es 2 * es 3 + challengeOf (sqCvT CM.hm cv) * (es 4 * es 5 * es 6 * es 7 +
      challengeOf (sqCvT CM.hm cv) * (es 8 * es 9 * es 10 * es 11)))
    {N dsb gmu layers rounds row : E} {j sh posE : ℕ} (hLj : L = 2 * j + sh)
    (hds : LoadHolds rd (dsb * gmu) 0 (gen ^ sh))
    (hlay : ∀ k < 8, LoadHolds rd layers (8 * L + k)
      ([(digestScalars cv).1, (digestScalars cv).2, cur, v0, v1, v2, row, gen ^ posE].getD k 0))
    (hrow : ∀ r < L, LoadHolds rd row r (s.point.getD r 0))
    (hrnd : ∀ r ≤ L, ∀ k < 4, LoadHolds rd rounds (4 * (posE + r) + k)
      ([(digestScalars (cvr r)).1, (digestScalars (cvr r)).2, cur * gen ^ (4 * r), cl r].getD k 0))
    (hnr : ∀ r < L, LoadHolds rd row (42 + r) (ch r))
    (hnr0 : LoadHolds rd row 40 (challengeOf (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12))))
    (hnr1 : LoadHolds rd row 41 (challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12)))))
    (hnext : ∀ k < 8, LoadHolds rd layers (8 * L + 16 + k)
      ([(digestScalars (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12)))).1,
        (digestScalars (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12)))).2, cur * gen ^ (4 * L) * gen ^ 12,
        l10Next es 0 (challengeOf (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12)))
          (challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12)))),
        l10Next es 4 (challengeOf (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12)))
          (challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12)))),
        l10Next es 8 (challengeOf (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12)))
          (challengeOf (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12)))),
        row * gen ^ 40, gen ^ (posE + L + 1)].getD k 0))
    (hys : ReadsAt rd cur ((List.range L).flatMap wsr ++ (List.range 12).map es))
    (hq0 : sqCvM CM.hm cv = some (sqCvT CM.hm cv)) (hA : L10Ans CM.hm (cvr L) es 12)
    (hq1 : sqCvM CM.hm (l10cvT CM.hm (cvr L) es 12) = some (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12)))
    (hq2 : sqCvM CM.hm (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12)) =
      some (sqCvT CM.hm (sqCvT CM.hm (l10cvT CM.hm (cvr L) es 12)))) :
    L10IterC CM rd N dsb gmu layers rounds (gen ^ j) (gen ^ sh) cv (cvr L) cur v0 v1 v2 row (gen ^ posE)
      (cur * gen ^ (4 * L)) (cl L) es := by
  have hXL : gen ^ j * gen ^ j * gen ^ sh = gen ^ L := by rw [hLj, ← pow_add, ← pow_add]; ring_nf
  have pL : layers * (gen ^ j * gen ^ j * gen ^ sh) ^ 8 = layers * gen ^ (8 * L) := by
    rw [hXL, ← pow_mul]; ring_nf
  have pH : rounds * (gen ^ posE) ^ 4 = rounds * gen ^ (4 * (posE + 0)) := by rw [← pow_mul]; ring_nf
  have pT : rounds * (gen ^ posE * (gen ^ j * gen ^ j * gen ^ sh)) ^ 4 = rounds * gen ^ (4 * (posE + L)) := by
    rw [hXL, ← pow_add, ← pow_mul]; ring_nf
  have hwl : ∀ r < L, (wsr r).length = 4 := fun r h => (hr r h).1
  obtain ⟨hws, hes⟩ := readsAt_flatMap_range hwl hys
  have lay := fun k (hk : k < 8) => (loadHolds_gen_pow_mul (p := layers) (j := 8 * L) (k := k)).mpr (hlay k hk)
  have nxt := fun k (hk : k < 8) => (loadHolds_gen_pow_mul (p := layers) (j := 8 * L) (k := 16 + k)).mpr
    (by rw [← Nat.add_assoc]; exact hnext k hk)
  have rnd := fun r (hr' : r ≤ L) k (hk : k < 4) =>
    (loadHolds_gen_pow_mul (p := rounds) (j := 4 * (posE + r)) (k := k)).mpr (hrnd r hr' k hk)
  have rH := fun k (hk : k < 4) => by
    have := rnd 0 (Nat.zero_le _) k hk; rw [← pH] at this; exact this
  have rT := fun k (hk : k < 4) => by
    have := rnd L le_rfl k hk; rw [← pT] at this; exact this
  have lay' := fun k (hk : k < 8) => by have := lay k hk; rw [← pL] at this; exact this
  have nxt' := fun k (hk : k < 8) => by have := nxt k hk; rw [← pL] at this; exact this
  have e23 : gen ^ posE * (gen ^ j * gen ^ j * gen ^ sh) * gen = gen ^ (posE + L + 1) := by
    rw [hXL, ← pow_add, ← pow_succ]
  have hpe : cl 0 = v0 + challengeOf (sqCvT CM.hm cv) * (v1 + challengeOf (sqCvT CM.hm cv) * v2) := by
    rw [hc0, hvals, polyEval_three]
  refine
    { hds := hds, hl0 := lay' 0 (by norm_num), hl1 := lay' 1 (by norm_num), hl2 := lay' 2 (by norm_num),
      hl3 := lay' 3 (by norm_num), hl4 := lay' 4 (by norm_num), hl5 := lay' 5 (by norm_num),
      hl6 := lay' 6 (by norm_num), hl7 := lay' 7 (by norm_num),
      hh0 := by have := rH 0 (by norm_num); rw [hcv0] at this; exact this,
      hh1 := by have := rH 1 (by norm_num); rw [hcv0] at this; exact this,
      hh2 := by have := rH 2 (by norm_num); simpa using this,
      hh3 := by have := rH 3 (by norm_num); rw [hpe] at this; exact this,
      ht0 := rT 0 (by norm_num), ht1 := rT 1 (by norm_num), ht2 := rT 2 (by norm_num),
      ht3 := rT 3 (by norm_num), hr0 := hnr0, hr1 := hnr1,
      hn16 := nxt' 0 (by norm_num), hn17 := nxt' 1 (by norm_num), hn18 := nxt' 2 (by norm_num),
      hn19 := nxt' 3 (by norm_num), hn20 := nxt' 4 (by norm_num), hn21 := nxt' 5 (by norm_num),
      hn22 := nxt' 6 (by norm_num), hn23 := by rw [e23]; exact nxt' 7 (by norm_num),
      hK1 := isInK_add (by simpa using gen_pow_isInK 0) (by rw [hXL]; exact gen_pow_isInK L),
      h101 := fun hne => ?_, hc := fun i hi => ?_, hcheck := hfin, hq0 := hq0, hA := hA,
      hq1 := hq1, hq2 := hq2 }
  · rw [hXL] at hne ⊢
    rcases Nat.eq_zero_or_pos L with h0 | hpos
    · exact absurd (by rw [h0, pow_zero]; exact e_add_self 1) hne
    refine loop101_completeC hpos fun r hr' => ?_
    have pR : rounds * (gen ^ posE * gen ^ r) ^ 4 = rounds * gen ^ (4 * (posE + r)) := by
      rw [← pow_add, ← pow_mul]; ring_nf
    have r0 := fun k (hk : k < 4) => by
      have := rnd r (by omega) k hk; rw [← pR] at this; exact this
    have r1 := fun k (hk : k < 4) => by
      have := hrnd (r + 1) (by omega) k hk
      rw [show 4 * (posE + (r + 1)) + k = 4 * (posE + r) + (4 + k) by ring] at this
      exact (loadHolds_gen_pow_mul (p := rounds) (j := 4 * (posE + r)) (k := 4 + k)).mpr this
    have r1' := fun k (hk : k < 4) => by have := r1 k hk; rw [← pR] at this; exact this
    refine ⟨cvr r, cur * gen ^ (4 * r), cl r, s.point.getD r 0, wsr r, cl (r + 1), ch r, cvr (r + 1),
      r0 0 (by norm_num), r0 1 (by norm_num), r0 2 (by norm_num), r0 3 (by norm_num), ?_, (hr r hr').1,
      hws r hr', (hr r hr').2, ?_, r1' 0 (by norm_num), r1' 1 (by norm_num), ?_, r1' 3 (by norm_num)⟩
    · exact (loadHolds_gen_pow_mul (p := row) (j := r) (k := 0)).mpr (by simpa using hrow r hr')
    · refine (loadHolds_gen_pow_mul (p := row * gen ^ 40) (j := r) (k := 2)).mpr ?_
      refine (loadHolds_gen_pow_mul (p := row) (j := 40) (k := r + 2)).mpr ?_
      rw [show 40 + (r + 2) = 42 + r by omega]; exact hnr r hr'
    · have := r1' 2 (by norm_num)
      rw [show cur * gen ^ (4 * (r + 1)) = cur * gen ^ (4 * r) * gen ^ 4 by ring] at this
      exact this
  · have := hes i (by simp; omega)
    simpa using this

end
end LeanVM.Guest.B1.VerifySub
