/-
  LeanVM.Guest.B1.Comp.Tables.GkrBodyC

  `verify_bus_gkr`'s body over a completeness model, backward: its honest values at the total
  hash and every statement holding under the model's semantics.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.GkrLoopsC
public import LeanVM.Guest.B1.Tables.GkrCompleteBody

/-!
# `verify_bus_gkr`'s body over a completeness model

`GkrCompleteBody.lean` under a completeness model's semantics: `vbgValsT`, `vbgσT` are `vbgVals`,
`vbgσ` at the total hash; `vbg_holdsC`: on a memory holding the words the body loads (`VbgOddC`
for the odd layer), the body's hashes answered, every statement holds under the model's semantics,
for any relation the two loops hold of; its Fiat-Shamir blocks are the model's answers
(`holdsB_fsNextT_comp`, `holdsB_squeezeT_comp`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

/-- `cv0`: the state after the two roots, at the total hash (`vbgCv0`). -/
abbrev vbgCv0T (M : HashModel) (cv : Digest) (x0 cnt : E) : Digest := obsCvT M (obsCvT M cv x0) cnt

/-- The honest values `5 ..` of `verify_bus_gkr`'s body at the total hash (`vbgVals`). -/
noncomputable def vbgValsT (M : HashModel) (fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 : E)
    (cv cvF : Digest) (oes : ℕ → E) : List E :=
  let cv0 := vbgCv0T M cv x0 cnt
  [word 4 0 0,
    gmu * (word 4 0 0),
    (gmu * (word 4 0 0)) * (gmu * (word 4 0 0)),
    ((gmu * (word 4 0 0)) * (gmu * (word 4 0 0))) * ((gmu * (word 4 0 0)) * (gmu * (word 4 0 0))),
    (((gmu * (word 4 0 0)) * (gmu * (word 4 0 0))) * ((gmu * (word 4 0 0)) * (gmu * (word 4 0 0)))) * (((gmu * (word 4 0 0)) * (gmu * (word 4 0 0))) * ((gmu * (word 4 0 0)) * (gmu * (word 4 0 0)))),
    layers,
    rounds,
    pts,
    word 4294967296 0 0,
    rcy,
    rct1,
    rct2,
    fs0,
    fs1,
    x0,
    (gkrFsvT M x0 cv 1),
    (gkrFsvT M x0 cv 2),
    (gkrFsvT M x0 cv 3),
    (gkrFsvT M x0 cv 4),
    (gkrFsvT M x0 cv 5),
    (gkrFsvT M x0 cv 6),
    (gkrFsvT M x0 cv 7),
    (gkrFsvT M x0 cv 8),
    (gkrFsvT M x0 cv 9),
    (gkrFsvT M x0 cv 10),
    (gkrFsvT M x0 cv 11),
    (gkrFsvT M x0 cv 12),
    (gkrFsvT M x0 cv 13),
    (gkrFsvT M x0 cv 14),
    cnt,
    (gkrFsvT M cnt (obsCvT M cv x0) 1),
    (gkrFsvT M cnt (obsCvT M cv x0) 2),
    (gkrFsvT M cnt (obsCvT M cv x0) 3),
    (gkrFsvT M cnt (obsCvT M cv x0) 4),
    (gkrFsvT M cnt (obsCvT M cv x0) 5),
    (gkrFsvT M cnt (obsCvT M cv x0) 6),
    (gkrFsvT M cnt (obsCvT M cv x0) 7),
    (gkrFsvT M cnt (obsCvT M cv x0) 8),
    (gkrFsvT M cnt (obsCvT M cv x0) 9),
    (gkrFsvT M cnt (obsCvT M cv x0) 10),
    (gkrFsvT M cnt (obsCvT M cv x0) 11),
    (gkrFsvT M cnt (obsCvT M cv x0) 12),
    (gkrFsvT M cnt (obsCvT M cv x0) 13),
    (gkrFsvT M cnt (obsCvT M cv x0) 14),
    word 0 0 0,
    cnt + (word 0 0 0),
    cinv,
    1,
    word 4 0 0,
    cur * (word 4 0 0),
    word 1 0 0,
    pb,
    dsb,
    word 1 0 0,
    word 1 0 0,
    word 1 0 0,
    word 2 0 0,
    word 2 0 0,
    word 1 0 0,
    word 2 0 0,
    word 2 0 0,
    word 4 0 0,
    word 1 0 0,
    word 4 0 0,
    word 2 0 0,
    word 8 0 0,
    word 1 0 0,
    word 8 0 0,
    word 2 0 0,
    word 16 0 0,
    word 1 0 0,
    word 16 0 0,
    word 2 0 0,
    word 32 0 0,
    word 1 0 0,
    word 32 0 0,
    word 2 0 0,
    word 64 0 0,
    word 1 0 0,
    word 64 0 0,
    word 2 0 0,
    word 128 0 0,
    word 1 0 0,
    word 128 0 0,
    word 2 0 0,
    word 256 0 0,
    word 1 0 0,
    word 256 0 0,
    word 2 0 0,
    word 512 0 0,
    word 1 0 0,
    word 512 0 0,
    word 2 0 0,
    word 1024 0 0,
    word 1 0 0,
    word 1024 0 0,
    word 2 0 0,
    word 2048 0 0,
    word 1 0 0,
    word 2048 0 0,
    word 2 0 0,
    word 4096 0 0,
    word 1 0 0,
    word 4096 0 0,
    word 2 0 0,
    word 8192 0 0,
    word 1 0 0,
    word 8192 0 0,
    word 2 0 0,
    word 16384 0 0,
    word 1 0 0,
    word 16384 0 0,
    word 2 0 0,
    word 32768 0 0,
    word 1 0 0,
    word 32768 0 0,
    word 2 0 0,
    word 65536 0 0,
    word 1 0 0,
    dsb * gmu,
    shE,
    word 1 0 0,
    shE + (word 1 0 0),
    (digestScalars cv0).1,
    (digestScalars cv0).2,
    (sqValsT M cv0 0),
    (sqValsT M cv0 1),
    (sqValsT M cv0 2),
    (sqValsT M cv0 3),
    (sqValsT M cv0 4),
    (sqValsT M cv0 5),
    (sqValsT M cv0 6),
    (sqValsT M cv0 7),
    (sqValsT M cv0 8),
    (sqValsT M cv0 9),
    (sqValsT M cv0 10),
    (sqValsT M cv0 11),
    (sqValsT M cv0 12),
    (sqValsT M cv0 13),
    (cur * word 4 0 0),
    x0,
    x0,
    cnt,
    ((sqValsT M cv0 13)) * cnt,
    x0 + (((sqValsT M cv0 13)) * cnt),
    ((sqValsT M cv0 13)) * (x0 + (((sqValsT M cv0 13)) * cnt)),
    x0 + (((sqValsT M cv0 13)) * (x0 + (((sqValsT M cv0 13)) * cnt))),
    pts,
    word 1099511627776 0 0,
    pts * (word 1099511627776 0 0),
    (oes 0),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 1),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 2),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 3),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 4),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 5),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 6),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 7),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 8),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 9),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 10),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 11),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 12),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 13),
    (gkrFsvT M (oes 0) (l10cvT M (sqCvT M cv0) oes 0) 14),
    (oes 0),
    (oes 1),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 1),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 2),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 3),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 4),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 5),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 6),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 7),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 8),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 9),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 10),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 11),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 12),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 13),
    (gkrFsvT M (oes 1) (l10cvT M (sqCvT M cv0) oes 1) 14),
    (oes 1),
    (oes 2),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 1),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 2),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 3),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 4),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 5),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 6),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 7),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 8),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 9),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 10),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 11),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 12),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 13),
    (gkrFsvT M (oes 2) (l10cvT M (sqCvT M cv0) oes 2) 14),
    (oes 2),
    (oes 3),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 1),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 2),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 3),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 4),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 5),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 6),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 7),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 8),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 9),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 10),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 11),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 12),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 13),
    (gkrFsvT M (oes 3) (l10cvT M (sqCvT M cv0) oes 3) 14),
    (oes 3),
    (oes 4),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 1),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 2),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 3),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 4),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 5),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 6),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 7),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 8),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 9),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 10),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 11),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 12),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 13),
    (gkrFsvT M (oes 4) (l10cvT M (sqCvT M cv0) oes 4) 14),
    (oes 4),
    (oes 5),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 1),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 2),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 3),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 4),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 5),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 6),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 7),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 8),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 9),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 10),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 11),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 12),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 13),
    (gkrFsvT M (oes 5) (l10cvT M (sqCvT M cv0) oes 5) 14),
    (oes 5),
    ((oes 4)) * ((oes 5)),
    word 0 0 0,
    ((sqValsT M cv0 13)) * (word 0 0 0),
    (((oes 4)) * ((oes 5))) + (((sqValsT M cv0 13)) * (word 0 0 0)),
    ((oes 2)) * ((oes 3)),
    ((sqValsT M cv0 13)) * ((((oes 4)) * ((oes 5))) + (((sqValsT M cv0 13)) * (word 0 0 0))),
    (((oes 2)) * ((oes 3))) + (((sqValsT M cv0 13)) * ((((oes 4)) * ((oes 5))) + (((sqValsT M cv0 13)) * (word 0 0 0)))),
    ((oes 0)) * ((oes 1)),
    ((sqValsT M cv0 13)) * ((((oes 2)) * ((oes 3))) + (((sqValsT M cv0 13)) * ((((oes 4)) * ((oes 5))) + (((sqValsT M cv0 13)) * (word 0 0 0))))),
    (((oes 0)) * ((oes 1))) + (((sqValsT M cv0 13)) * ((((oes 2)) * ((oes 3))) + (((sqValsT M cv0 13)) * ((((oes 4)) * ((oes 5))) + (((sqValsT M cv0 13)) * (word 0 0 0)))))),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 0),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 1),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 2),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 3),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 4),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 5),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 6),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 7),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 8),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 9),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 10),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 11),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 12),
    (sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 13),
    word 64 0 0,
    ((cur * word 4 0 0)) * (word 64 0 0),
    ((oes 0)) + ((oes 1)),
    ((sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 13)) * (((oes 0)) + ((oes 1))),
    ((oes 0)) + (((sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 13)) * (((oes 0)) + ((oes 1)))),
    ((oes 2)) + ((oes 3)),
    ((sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 13)) * (((oes 2)) + ((oes 3))),
    ((oes 2)) + (((sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 13)) * (((oes 2)) + ((oes 3)))),
    ((oes 4)) + ((oes 5)),
    ((sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 13)) * (((oes 4)) + ((oes 5))),
    ((oes 4)) + (((sqValsT M (l10cvT M (sqCvT M cv0) oes 6) 13)) * (((oes 4)) + ((oes 5)))),
    word 2 0 0,
    word 1 0 0,
    pb * gmu,
    npair,
    (word 1 0 0) + npair,
    word 1 0 0,
    pb * gmu,
    npair,
    gmu * gmu,
    (gmu * gmu) * (gmu * gmu),
    ((gmu * gmu) * (gmu * gmu)) * ((gmu * gmu) * (gmu * gmu)),
    layers * (((gmu * gmu) * (gmu * gmu)) * ((gmu * gmu) * (gmu * gmu))),
    (digestScalars cvF).1,
    (digestScalars cvF).2,
    curF,
    rowF,
    word 1 0 0,
    (word 1 0 0) + gmu,
    word 1 0 0,
    (digestScalars cvF).1,
    (digestScalars cvF).2,
    curF,
    vF0,
    vF1,
    vF2]

theorem gkrFsvT_obs1 (M : HashModel) (x : E) (cv : Digest) :
    gkrFsvT M x cv 13 = (digestScalars (obsCvT M cv x)).1 := rfl

theorem gkrFsvT_obs2 (M : HashModel) (x : E) (cv : Digest) :
    gkrFsvT M x cv 14 = (digestScalars (obsCvT M cv x)).2 := rfl

/-- The odd layer's words at the total hash, its hashes answered (`VbgOdd`): its six children,
its check, the next row's challenge, the layer `1` slots. -/
structure VbgOddC (CM : CompModel) (rd : Reader) (layers pts cur : E) (cv : Digest) (x0 cnt : E) (oes : ℕ → E) : Prop where
  hc : ∀ i < 6, LoadHolds rd (cur * word 4 0 0) i (oes i)
  chk : x0 + (challengeOf (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt))) * (x0 + (challengeOf (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt))) * cnt) =
    oes 0 * oes 1 + (challengeOf (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt))) * (oes 2 * oes 3 + (challengeOf (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt))) * (oes 4 * oes 5))
  hrow : LoadHolds rd (pts * word 1099511627776 0 0) 0 (challengeOf (sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 6)))
  hq0 : sqCvM CM.hm (vbgCv0T CM.hm cv x0 cnt) = some (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt))
  hA : L10Ans CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 6
  hq1 : sqCvM CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 6) =
    some (sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 6))
  hl1 : ∀ k < 8, LoadHolds rd layers (8 + k) ([(digestScalars (sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 6))).1, (digestScalars (sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 6))).2, cur * word 4 0 0 * word 64 0 0, oes 0 + (challengeOf (sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 6))) * (oes 0 + oes 1), oes 2 + (challengeOf (sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 6))) * (oes 2 + oes 3), oes 4 + (challengeOf (sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 6))) * (oes 4 + oes 5), pts * word 1099511627776 0 0, word 2 0 0].getD k 0)

/-- The honest valuation of `verify_bus_gkr`'s body at the total hash (`vbgσ`). -/
noncomputable def vbgσT (M : HashModel) (zeta fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 : E)
    (cv cvF : Digest) (oes : ℕ → E) : Val :=
  setl (Val.ofArgs [fs0, fs1, cur, gmu, zeta]) 5 (vbgValsT M fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 cv cvF oes)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vbg_P1C {CM : CompModel} {C : CallRel} {rd : Reader} {fs0 fs1 cur gmu zeta layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt
    shE npair curF rowF vF0 vF1 vF2 : E} {cv cvF : Digest} {oes : ℕ → E} {next : Prop} {kret : List E → Prop}
    (hne : (cnt + word 0 0 0) * cinv = 1)
    (hl0 : ∀ k < 8, LoadHolds rd layers k ([(digestScalars (vbgCv0T CM.hm cv x0 cnt)).1,
      (digestScalars (vbgCv0T CM.hm cv x0 cnt)).2, cur * word 4 0 0, x0, x0, cnt, pts, word 1 0 0].getD k 0))
    (hpb : ∀ k < 33, LoadHolds rd pb k (vbgPb.getD k 0))
    (hdt : ∀ k < 33, LoadHolds rd dsb k (vbgDs.getD k 0))
    (hsh : LoadHolds rd (dsb * gmu) 0 shE) (hn : next) :
    Stmt.HoldsListB CM.sem C rd (vbgσT CM.hm zeta fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 cv cvF oes) vbgP1 next kret := by
  set σ := vbgσT CM.hm zeta fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 cv cvF oes with hσ
  simp only [vbgP1, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  refine ⟨rfl, rfl, trivial, ⟨hne.symm, rfl⟩, (by rw [show σ (.n 47) = (digestScalars (vbgCv0T CM.hm cv x0 cnt)).1 from gkrFsvT_obs1 _ _ _]; exact hl0 0 (by norm_num)), (by rw [show σ (.n 48) = (digestScalars (vbgCv0T CM.hm cv x0 cnt)).2 from gkrFsvT_obs2 _ _ _]; exact hl0 1 (by norm_num)), rfl, rfl, (by have h := hl0 2 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 3 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 4 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 5 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 6 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, (by have h := hl0 7 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), trivial, trivial, rfl, (by have h := hpb 0 (by norm_num); simp only [List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 0 (by norm_num); simp only [List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 1 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 1 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 2 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 2 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 3 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 3 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 4 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 4 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 5 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 5 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 6 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 6 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 7 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 7 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 8 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 8 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 9 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 9 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 10 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 10 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 11 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 11 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 12 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 12 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 13 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 13 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 14 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 14 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 15 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 15 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 16 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 16 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 17 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 17 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 18 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 18 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 19 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 19 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 20 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 20 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 21 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 21 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 22 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 22 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 23 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 23 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 24 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 24 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 25 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 25 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 26 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 26 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 27 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 27 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 28 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 28 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 29 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 29 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 30 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 30 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 31 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 31 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 32 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 32 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, hsh, rfl, rfl, ?_⟩
  exact hn

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`verify_bus_gkr`'s body holds over a completeness model** (`vbg_holds`) at its honest
values at the total hash, on a memory holding the words it loads, the body's hashes answered, for
any relation its two loops hold of. -/
theorem vbg_holdsC {CM : CompModel} {C : CallRel} {rd : Reader} {fs0 fs1 cur gmu zeta layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt
    shE npair curF rowF vF0 vF1 vF2 : E} {cv cvF : Digest} {oes : ℕ → E}
    (hfs : (fs0, fs1) = digestScalars cv)
    (hrc1 : LoadHolds rd gmu 0 rct1) (hrc2 : LoadHolds rd rcy 0 rct2) (hrck : word 4294967296 0 0 = gmu * rcy)
    (hx0 : LoadHolds rd cur 0 x0) (hcnt : LoadHolds rd cur 1 cnt) (hne : (cnt + word 0 0 0) * cinv = 1)
    (hax0 : obsCvM CM.hm cv x0 = some (obsCvT CM.hm cv x0))
    (hacnt : obsCvM CM.hm (obsCvT CM.hm cv x0) cnt = some (vbgCv0T CM.hm cv x0 cnt))
    (hl0 : ∀ k < 8, LoadHolds rd layers k ([(digestScalars (vbgCv0T CM.hm cv x0 cnt)).1,
      (digestScalars (vbgCv0T CM.hm cv x0 cnt)).2, cur * word 4 0 0, x0, x0, cnt, pts, word 1 0 0].getD k 0))
    (hpb : ∀ k < 33, LoadHolds rd pb k (vbgPb.getD k 0))
    (hdt : ∀ k < 33, LoadHolds rd dsb k (vbgDs.getD k 0))
    (hsh : LoadHolds rd (dsb * gmu) 0 shE) (hK127 : IsInK (shE + word 1 0 0))
    (hodd : shE + word 1 0 0 ≠ 0 → VbgOddC CM rd layers pts cur cv x0 cnt oes)
    (hnp : LoadHolds rd (pb * gmu) 0 npair) (hK290 : IsInK (word 1 0 0 + npair))
    (h10 : word 1 0 0 + npair ≠ 0 → C "__loop10" [word 1 0 0, npair, dsb, gmu, layers, rounds] [])
    (hlF : ∀ k < 7, LoadHolds rd (layers * gmu ^ 8) k ([(digestScalars cvF).1, (digestScalars cvF).2, curF,
      vF0, vF1, vF2, rowF].getD k 0))
    (hK303 : IsInK (word 1 0 0 + gmu))
    (h11 : word 1 0 0 + gmu ≠ 0 → C "__loop11" [word 1 0 0, gmu, zeta, rowF] []) :
    Stmt.HoldsListB CM.sem C rd (setl (Val.ofArgs [fs0, fs1, cur, gmu, zeta]) 5 (vbgValsT CM.hm fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 cv cvF oes)) (Fn.body Data.core10) False
      (fun rs => rs = [(digestScalars cvF).1, (digestScalars cvF).2, curF, vF0, vF1, vF2]) := by
  set σ := setl (Val.ofArgs [fs0, fs1, cur, gmu, zeta]) 5 (vbgValsT CM.hm fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 cv cvF oes) with hσ
  have e297 : σ (.n 297) = layers * gmu ^ 8 := by show layers * _ = _; ring
  have hQ : Stmt.HoldsListB CM.sem C rd σ (vbgQ ++ [.ret [.n 305, .n 306, .n 307, .n 308, .n 309, .n 310]]) False
      (fun rs => rs = [(digestScalars cvF).1, (digestScalars cvF).2, curF, vF0, vF1, vF2]) := by
    rw [holdsListB_append]
    simp only [vbgQ, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
    refine ⟨rfl, rfl, hnp, rfl, rfl, rfl, hnp, hK290, (fun h => by simp only [List.map_cons, List.map_nil]; exact h10 h), rfl, rfl, rfl, rfl, (by rw [e297]; have h := hlF 0 (by norm_num); simp only [List.getD_cons_zero] at h; exact h), (by rw [e297]; have h := hlF 1 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by rw [e297]; have h := hlF 2 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by rw [e297]; have h := hlF 6 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, rfl, hK303, (fun h => by simp only [List.map_cons, List.map_nil]; exact h11 h), rfl, rfl, rfl, (by rw [e297]; have h := hlF 3 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by rw [e297]; have h := hlF 4 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by rw [e297]; have h := hlF 5 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), ?_⟩
    rfl
  rw [vbg_body]
  simp only [holdsListB_append]
  simp only [vbgP0, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  refine ⟨rfl, rfl, rfl, rfl, rfl, trivial, trivial, trivial, rfl, ⟨hrc1, hrck, hrc2⟩, rfl, rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hx0, cv, obsCvT CM.hm cv x0, hfs, hax0, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hcnt, obsCvT CM.hm cv x0, vbgCv0T CM.hm cv x0 cnt, rfl, hacnt, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine vbg_P1C (zeta := zeta) hne hl0 hpb hdt hsh ?_
  refine ⟨hK127, fun _ => hQ, fun hne' => ?_⟩
  have OD := hodd hne'
  simp only [holdsListB_append, vbgOF]
  simp only [vbgO0, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  refine ⟨(by rw [show σ (.n 128) = (digestScalars (vbgCv0T CM.hm cv x0 cnt)).1 from gkrFsvT_obs1 _ _ _]; exact hl0 0 (by norm_num)), (by rw [show σ (.n 129) = (digestScalars (vbgCv0T CM.hm cv x0 cnt)).2 from gkrFsvT_obs2 _ _ _]; exact hl0 1 (by norm_num)), ?_⟩
  refine holdsB_squeezeT_comp _ _ _ ⟨⟨vbgCv0T CM.hm cv x0 cnt, sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt), rfl, OD.hq0, fun k hk => by interval_cases k <;> rfl⟩, ?_⟩
  simp only [vbgO1, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  refine ⟨(by have h := hl0 2 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 3 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 4 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 5 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, rfl, rfl, (by have h := hl0 6 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨OD.hc 0 (by norm_num), l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 0, l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes (0 + 1), rfl, OD.hA 0 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨OD.hc 1 (by norm_num), l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 1, l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes (1 + 1), rfl, OD.hA 1 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨OD.hc 2 (by norm_num), l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 2, l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes (2 + 1), rfl, OD.hA 2 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨OD.hc 3 (by norm_num), l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 3, l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes (3 + 1), rfl, OD.hA 3 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨OD.hc 4 (by norm_num), l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 4, l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes (4 + 1), rfl, OD.hA 4 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨OD.hc 5 (by norm_num), l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 5, l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes (5 + 1), rfl, OD.hA 5 (by norm_num), fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  simp only [vbgO2, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by rw [show σ (.n 260) = σ (.n 151) from by show (((oes 0)) * ((oes 1))) + (((sqValsT CM.hm (vbgCv0T CM.hm cv x0 cnt) 13)) * ((((oes 2)) * ((oes 3))) + (((sqValsT CM.hm (vbgCv0T CM.hm cv x0 cnt) 13)) * ((((oes 4)) * ((oes 5))) + (((sqValsT CM.hm (vbgCv0T CM.hm cv x0 cnt) 13)) * (word 0 0 0)))))) = x0 + (((sqValsT CM.hm (vbgCv0T CM.hm cv x0 cnt) 13)) * (x0 + (((sqValsT CM.hm (vbgCv0T CM.hm cv x0 cnt) 13)) * cnt))); simp only [sqValsT, sqValsD]; rw [OD.chk]; simp only [word_zero]; ring]; exact e_add_self _), ?_⟩
  refine holdsB_squeezeT_comp _ _ _ ⟨⟨l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 6, sqCvT CM.hm (l10cvT CM.hm (sqCvT CM.hm (vbgCv0T CM.hm cv x0 cnt)) oes 6), rfl, OD.hq1, fun k hk => by interval_cases k <;> rfl⟩, ?_⟩
  simp only [vbgO3, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  refine ⟨OD.hrow, (by have h := OD.hl1 0 (by norm_num); simp only [List.getD_cons_zero] at h; exact h), (by have h := OD.hl1 1 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, (by have h := OD.hl1 2 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, rfl, (by have h := OD.hl1 3 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, rfl, (by have h := OD.hl1 4 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, rfl, (by have h := OD.hl1 5 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := OD.hl1 6 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, (by have h := OD.hl1 7 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), ?_⟩
  exact hQ

end
end LeanVM.Guest.B1.VerifySub
