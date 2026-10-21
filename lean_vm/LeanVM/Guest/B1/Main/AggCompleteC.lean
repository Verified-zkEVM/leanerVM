/-
  LeanVM.Guest.B1.Main.AggCompleteC

  B1 for `aggregate_claims`, completeness, under a semantics `S` over an answered hash `Ha`: for
  every pointer of its `HeapBuf`s and every memory holding the honest words there, the batching's
  claim from the guest's baked start is stored.
-/

module

public import LeanVM.Guest.B1.Main.AggStepsCC
public import LeanVM.Guest.B1.Main.AggLoop99CS
public import LeanVM.Guest.B1.Main.AggEqtreeCS
public import LeanVM.Guest.B1.Main.AggSoundM

/-!
# `aggregate_claims`, completely, over an answered hash

`AggComplete.lean` under `S : BlakeSem` over the answered hash `Ha`. The batching's run is
`batchWith Ha aggSeedD` from the guest's baked start (`aggSeedD`, the cells `AGG_SEED`), its
values over the total hash `Ht` (`agCv1H`, `agCvAH`, `agLBH`, `agRbH`, `agLMH`, `agRmH`), every
step of its chain answered by `Ha` (`AggAns`, from `batchWith_steps`). `AggMemH` is `AggMem` at
these values. Each loop iteration's rows are `FsRowsC S Ha`'s, the two sumchecks
`BsRowsC S Ha`'s: `aggregateC_claims_complete`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-! ## The batching's run over `Ht` -/

section Run

variable (Ht : List UInt8 → Digest)

/-- The state after absorbing the count, from the baked start. -/
noncomputable def agCv1H (cs : List ChildClaims) : Digest := obsCvH Ht aggSeedD (ofK (Parameters.gpow cs.length))

/-- The state after absorbing every child. -/
noncomputable def agCvAH (cs : List ChildClaims) : Digest := obsAllH Ht (agCv1H Ht cs) (cs.flatMap childCells)

/-- The bytecode lambdas. -/
noncomputable def agLBH (cs : List ChildClaims) : List (E × E) := (sq2H Ht cs.length (agCvAH Ht cs)).1

/-- The bytecode sumcheck's run. -/
noncomputable def agRbH (cs : List ChildClaims) (h : BatchHints) : (List E × E) × Digest :=
  (batchRoundsWith (m := Id) Ht (sumE (List.zipWith bcTerm cs (agLBH Ht cs))) h.bytecodeRounds).run
    (sqIt2H Ht (agCvAH Ht cs) cs.length)

/-- The matrix lambdas. -/
noncomputable def agLMH (cs : List ChildClaims) (h : BatchHints) : List (E × E × E) :=
  (sq3H Ht cs.length (agRbH Ht cs h).2).1

/-- The matrix sumcheck's run. -/
noncomputable def agRmH (cs : List ChildClaims) (h : BatchHints) : (List E × E) × Digest :=
  (batchRoundsWith (m := Id) Ht (sumE (List.zipWith mtTerm cs (agLMH Ht cs h))) h.matrixRounds).run
    (sqIt3H Ht (agRbH Ht cs h).2 cs.length)

/-- **The honest words at the `HeapBuf`s** over `Ht` (`AggMem`). -/
structure AggMemH (rd : Reader) (P : AggPtrs) (fresh carried : E) (cs : List ChildClaims)
    (h : BatchHints) : Prop where
  msgB : ∀ r < 22, LoadHolds rd P.msgB (2 * r) (h.bytecodeRounds.getD r (0, 0)).1 ∧
    LoadHolds rd P.msgB (2 * r + 1) (h.bytecodeRounds.getD r (0, 0)).2
  msgM : ∀ r < 28, LoadHolds rd P.msgM (2 * r) (h.matrixRounds.getD r (0, 0)).1 ∧
    LoadHolds rd P.msgM (2 * r + 1) (h.matrixRounds.getD r (0, 0)).2
  rows : ∀ c < cs.length, LoadHolds rd P.frow c (fresh * gen ^ (106 * c)) ∧
    LoadHolds rd P.crow c (carried * gen ^ (53 * c))
  absb : ∀ c ≤ cs.length,
    LoadHolds rd P.absb (2 * c)
      (digestScalars (obsAllH Ht (agCv1H Ht cs) ((cs.take c).flatMap childCells))).1 ∧
    LoadHolds rd P.absb (2 * c + 1)
      (digestScalars (obsAllH Ht (agCv1H Ht cs) ((cs.take c).flatMap childCells))).2
  lamB : ∀ c < cs.length, LoadHolds rd P.lamB (2 * c) ((agLBH Ht cs).getD c (0, 0)).1 ∧
    LoadHolds rd P.lamB (2 * c + 1) ((agLBH Ht cs).getD c (0, 0)).2
  bcc : ∀ c ≤ cs.length,
    LoadHolds rd P.bcc (3 * c) (digestScalars (sqIt2H Ht (agCvAH Ht cs) c)).1 ∧
    LoadHolds rd P.bcc (3 * c + 1) (digestScalars (sqIt2H Ht (agCvAH Ht cs) c)).2 ∧
    LoadHolds rd P.bcc (3 * c + 2) (sumE (List.zipWith bcTerm (cs.take c) ((agLBH Ht cs).take c)))
  rs : ReadsAt rd P.rs (agRbH Ht cs h).1.1
  wB : ∀ c ≤ cs.length, LoadHolds rd P.wB c
    (sumE (List.zipWith (bcWeight (agRbH Ht cs h).1.1) (cs.take c) ((agLBH Ht cs).take c)))
  lamM : ∀ c < cs.length, LoadHolds rd P.lamM (3 * c) ((agLMH Ht cs h).getD c (0, 0, 0)).1 ∧
    LoadHolds rd P.lamM (3 * c + 1) ((agLMH Ht cs h).getD c (0, 0, 0)).2.1 ∧
    LoadHolds rd P.lamM (3 * c + 2) ((agLMH Ht cs h).getD c (0, 0, 0)).2.2
  mcc : ∀ c ≤ cs.length,
    LoadHolds rd P.mcc (3 * c) (digestScalars (sqIt3H Ht (agRbH Ht cs h).2 c)).1 ∧
    LoadHolds rd P.mcc (3 * c + 1) (digestScalars (sqIt3H Ht (agRbH Ht cs h).2 c)).2 ∧
    LoadHolds rd P.mcc (3 * c + 2) (sumE (List.zipWith mtTerm (cs.take c) ((agLMH Ht cs h).take c)))
  rM : ReadsAt rd P.rM (agRmH Ht cs h).1.1
  eqR : ∀ t < 6, ∀ i < 2 ^ (t + 1),
    LoadHolds rd P.eqR (2 ^ (t + 1) - 2 + i) (etK ((agRmH Ht cs h).1.1.take 6) (t + 1) i)
  eqC : ∀ t < 6, ∀ i < 2 ^ (t + 1),
    LoadHolds rd P.eqC (2 ^ (t + 1) - 2 + i) (etK (((agRmH Ht cs h).1.1.drop 14).take 6) (t + 1) i)
  wsum : ∀ c ≤ cs.length,
    LoadHolds rd P.wsum (2 * c)
      (sumE (List.zipWith (mtWeightA (agRmH Ht cs h).1.1) (cs.take c) ((agLMH Ht cs h).take c))) ∧
    LoadHolds rd P.wsum (2 * c + 1)
      (sumE (List.zipWith (mtWeightB (agRmH Ht cs h).1.1) (cs.take c) ((agLMH Ht cs h).take c)))

theorem getD_lBH (cs : List ChildClaims) {c : ℕ} (hc : c < cs.length) :
    (agLBH Ht cs).getD c (0, 0) = (challengeOf (sqCvH Ht (sqIt2H Ht (agCvAH Ht cs) c)),
      challengeOf (sqCvH Ht (sqCvH Ht (sqIt2H Ht (agCvAH Ht cs) c)))) := by
  obtain ⟨-, h2, h3⟩ := sq2H_spec Ht cs.length (agCvAH Ht cs)
  rw [agLBH, List.getD_eq_getElem _ _ (by rw [h2]; exact hc), h3 c (by rw [h2]; exact hc)]

theorem getD_lMH (cs : List ChildClaims) (h : BatchHints) {c : ℕ} (hc : c < cs.length) :
    (agLMH Ht cs h).getD c (0, 0, 0) = (challengeOf (sqCvH Ht (sqIt3H Ht (agRbH Ht cs h).2 c)),
      challengeOf (sqCvH Ht (sqCvH Ht (sqIt3H Ht (agRbH Ht cs h).2 c))),
      challengeOf (sqCvH Ht (sqCvH Ht (sqCvH Ht (sqIt3H Ht (agRbH Ht cs h).2 c))))) := by
  obtain ⟨-, h2, h3⟩ := sq3H_spec Ht cs.length (agRbH Ht cs h).2
  rw [agLMH, List.getD_eq_getElem _ _ (by rw [h2]; exact hc), h3 c (by rw [h2]; exact hc)]

theorem length_lBH (cs : List ChildClaims) : (agLBH Ht cs).length = cs.length :=
  (sq2H_spec Ht cs.length (agCvAH Ht cs)).2.1

theorem length_lMH (cs : List ChildClaims) (h : BatchHints) : (agLMH Ht cs h).length = cs.length :=
  (sq3H_spec Ht cs.length (agRbH Ht cs h).2).2.1

/-- **The batching over `Ht`, on the run's parts** (`batch_eq`). -/
theorem batchH_eq (cs : List ChildClaims) (h : BatchHints) :
    Id.run (batchWith (m := Id) Ht aggSeedD cs h) =
      if (agRbH Ht cs h).1.2 = h.bytecodeValue *
            sumE (List.zipWith (bcWeight (agRbH Ht cs h).1.1) cs (agLBH Ht cs)) ∧
          (agRmH Ht cs h).1.2 = h.matrixA *
            sumE (List.zipWith (mtWeightA (agRmH Ht cs h).1.1) cs (agLMH Ht cs h)) +
            h.matrixB * sumE (List.zipWith (mtWeightB (agRmH Ht cs h).1.1) cs (agLMH Ht cs h)) then
        some ⟨(agRbH Ht cs h).1.1, h.bytecodeValue, (agRmH Ht cs h).1.1, h.matrixA, h.matrixB⟩
      else none := by
  rw [batchWithH_spec]
  simp only [(sq2H_spec _ _ _).1, (sq3H_spec _ _ _).1]
  rfl

/-- The batching's points are its rounds' challenges (`batch_lengths` over `Ht`). -/
theorem batchH_lengths {cs : List ChildClaims} {h : BatchHints} {d : DeferredClaim}
    (hb : Id.run (batchWith (m := Id) Ht aggSeedD cs h) = some d) :
    d.bytecodePoint.length = h.bytecodeRounds.length ∧ d.matrixPoint.length = h.matrixRounds.length := by
  rw [batchH_eq] at hb
  split_ifs at hb
  injection hb with hd
  subst hd
  exact ⟨batchRoundsWithH_length Ht _ _ _, batchRoundsWithH_length Ht _ _ _⟩

end Run

/-! ## The answers -/

/-- **The batching's chain answered by `Ha`** at its values over `Ht`: the count's absorb, the
children's absorbs, the lambdas' squeezes, the two sumchecks' runs (`batchWith_steps` from
`aggSeedD`). -/
structure AggAns (Ha : List UInt8 → Option Digest) (Ht : List UInt8 → Digest) (cs : List ChildClaims)
    (h : BatchHints) : Prop where
  cv1 : Ha (digestBytes aggSeedD ++ blockOf (ofK (Parameters.gpow cs.length)) 1) = some (agCv1H Ht cs)
  obs : ObsAns Ha Ht (agCv1H Ht cs) (cs.flatMap childCells)
  sq2 : Sq2Ans Ha Ht cs.length (agCvAH Ht cs)
  runB : (batchRoundsWith (m := Option) Ha (sumE (List.zipWith bcTerm cs (agLBH Ht cs)))
    h.bytecodeRounds).run (sqIt2H Ht (agCvAH Ht cs) cs.length) = some (agRbH Ht cs h)
  sq3 : Sq3Ans Ha Ht cs.length (agRbH Ht cs h).2
  runM : (batchRoundsWith (m := Option) Ha (sumE (List.zipWith mtTerm cs (agLMH Ht cs h)))
    h.matrixRounds).run (sqIt3H Ht (agRbH Ht cs h).2 cs.length) = some (agRmH Ht cs h)

/-- **The batching from the baked start over `Ha` is answered** at the values over `Ht`, and closes
on the same claim over `Ht`. -/
theorem aggAns_of {Ha : List UInt8 → Option Digest} {Ht : List UInt8 → Digest}
    (hag : ∀ x d, Ha x = some d → d = Ht x) {cs : List ChildClaims} {h : BatchHints}
    {d : DeferredClaim} (hb : batchWith (m := Option) Ha aggSeedD cs h = some (some d)) :
    AggAns Ha Ht cs h ∧ Id.run (batchWith (m := Id) Ht aggSeedD cs h) = some d := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := batchWith_steps (Ht := Ht) hag hb
  have eB : agRbH Ht cs h = (batchRoundsWith (m := Id) Ht (sumE (List.zipWith bcTerm cs (agLBH Ht cs)))
      h.bytecodeRounds).run (sq2H Ht cs.length (agCvAH Ht cs)).2 := by
    rw [agRbH, (sq2H_spec Ht _ _).1]
  have eM : agRmH Ht cs h = (batchRoundsWith (m := Id) Ht (sumE (List.zipWith mtTerm cs (agLMH Ht cs h)))
      h.matrixRounds).run (sq3H Ht cs.length (agRbH Ht cs h).2).2 := by
    rw [agRmH, (sq3H_spec Ht _ _).1]
  have eL : agLMH Ht cs h = (sq3H Ht cs.length ((batchRoundsWith (m := Id) Ht
      (sumE (List.zipWith bcTerm cs (agLBH Ht cs))) h.bytecodeRounds).run
        (sq2H Ht cs.length (agCvAH Ht cs)).2).2).1 := by
    rw [agLMH, eB]
  refine ⟨⟨h1, h2, h3, ?_, ?_, ?_⟩, (batchWith_ans hag aggSeedD cs h _ hb).symm⟩
  · rw [← (sq2H_spec Ht _ _).1, eB]; exact h4
  · rw [eB]; exact h5
  · rw [← (sq3H_spec Ht _ _).1, eM, eL, eB]; exact h6

/-- The children's absorbs from child `j`'s state. -/
theorem obsAns_child {Ha : List UInt8 → Option Digest} {Ht : List UInt8 → Digest} {cv : Digest}
    {cs : List ChildClaims} (h : ObsAns Ha Ht cv (cs.flatMap childCells)) {j : ℕ}
    (hj : j < cs.length) :
    ObsAns Ha Ht (obsAllH Ht cv ((cs.take j).flatMap childCells)) (childCells cs[j]) := by
  have e : cs.flatMap childCells = (cs.take j).flatMap childCells ++
      (childCells cs[j] ++ (cs.drop (j + 1)).flatMap childCells) := by
    rw [← List.flatMap_cons, ← List.flatMap_append, ← List.drop_eq_getElem_cons hj,
      List.take_append_drop]
  rw [e, obsAns_append, obsAns_append] at h
  exact h.2.1

/-! ## The loops -/

section Loops

variable {S : BlakeSem} {Ha : List UInt8 → Option Digest} {Ht : List UInt8 → Digest} {rd : Reader}
  {cs : List ChildClaims} {h : BatchHints} {pis fresh carried : E} {P : AggPtrs}

theorem readsAt_of_getDC {p : E} {xs ys : List E} (h : ReadsAt rd p xs) (hl : ys.length ≤ xs.length)
    (he : ∀ k < ys.length, xs.getD k 0 = ys.getD k 0) : ReadsAt rd p ys := fun k hk => by
  rw [← List.getD_eq_getElem _ 0 hk, ← he k hk]; exact readsAt_getD' h (by omega)

theorem agC_loop95 (hF : FsRowsC S Ha) (hA : AggAns Ha Ht cs h) (hn0 : 0 < cs.length)
    (hC : ChildClaimsAt rd pis fresh carried cs) (hM : AggMemH Ht rd P fresh carried cs h) :
    coreProgram.RelB S rd "__loop95" [1, gen ^ cs.length, P.absb, pis, fresh, P.frow, carried, P.crow]
      [] := by
  refine loopS_complete (B := fun j => j < cs.length) hn0 rfl (fun j hj => hj)
    fun d j hj hK hnext => ?_
  obtain ⟨g0, g1, gsh, gfr, gb, gm, gcr⟩ := hC j hj
  obtain ⟨a0, a1⟩ := hM.absb j hj.le
  obtain ⟨o0, o1⟩ := hM.absb (j + 1) hj
  obtain ⟨wf, wc⟩ := hM.rows j hj
  have htk : (cs.take (j + 1)).flatMap childCells =
      (cs.take j).flatMap childCells ++ childCells cs[j] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
      List.flatMap_append, List.flatMap_singleton]
  have hob : obsAllH Ht (agCv1H Ht cs) ((cs.take (j + 1)).flatMap childCells) =
      obsAllH Ht (obsAllH Ht (agCv1H Ht cs) ((cs.take j).flatMap childCells))
        ((digestScalars cs[j].publicInput).1 :: (digestScalars cs[j].publicInput).2 ::
          (fixedCells cs[j].fresh ++ cs[j].carried.cells)) := by
    rw [htk, obsAllH, obsAllH, obsAllH, List.foldl_append]
    rfl
  rw [hob, show 2 * (j + 1) = 2 * j + 2 by ring] at o0
  rw [hob, show 2 * (j + 1) + 1 = 2 * j + 3 by ring] at o1
  have hans := obsAns_child hA.obs hj
  rw [show childCells cs[j] = (digestScalars cs[j].publicInput).1 :: (digestScalars cs[j].publicInput).2 ::
    (fixedCells cs[j].fresh ++ cs[j].carried.cells) by simp [childCells]] at hans
  exact loop95C_back hF d j _ _ _ _ _ (fixedCells_getD gsh).1 (deferCells_getD gb gm).1 hans a0 a1 g0 g1
    gfr gcr wf wc o0 o1 hK hnext

theorem agC_loop96 (hF : FsRowsC S Ha) (hA : AggAns Ha Ht cs h) (hn0 : 0 < cs.length)
    (hC : ChildClaimsAt rd pis fresh carried cs) (hM : AggMemH Ht rd P fresh carried cs h) :
    coreProgram.RelB S rd "__loop96" [1, gen ^ cs.length, P.bcc, P.lamB, P.frow, P.crow] [] := by
  refine loopS_complete (B := fun j => j < cs.length) hn0 rfl (fun j hj => hj)
    fun d j hj hK hnext => ?_
  obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC j hj
  obtain ⟨b0, b1, b2⟩ := hM.bcc j hj.le
  obtain ⟨n0, n1, n2⟩ := hM.bcc (j + 1) hj
  obtain ⟨l0, l1⟩ := hM.lamB j hj
  obtain ⟨wf, wc⟩ := hM.rows j hj
  have hfv := readsAt_getD' gfr (k := 22) (by rw [(fixedCells_getD gsh).1]; omega)
  have hcv := readsAt_getD' gcr (k := 22) (by rw [(deferCells_getD gb gm).1]; omega)
  rw [(fixedCells_getD gsh).2.2.1] at hfv
  rw [(deferCells_getD gb gm).2.2.1] at hcv
  rw [getD_lBH Ht cs hj] at l0 l1
  rw [sqIt2H_succ Ht, show 3 * (j + 1) = 3 * j + 3 by ring] at n0
  rw [sqIt2H_succ Ht, show 3 * (j + 1) + 1 = 3 * j + 4 by ring] at n1
  rw [show 3 * (j + 1) + 2 = 3 * j + 5 by ring,
    sumE_take_succ' _ _ _ _ (0, 0) hj (by rw [length_lBH]; exact hj), getD_lBH Ht cs hj, bcTerm,
    ← add_assoc] at n2
  obtain ⟨q0, q1⟩ := sq2Ans_get hA.sq2 j hj
  exact loop96C_back hF d j _ _ _ _ _ _ q0 q1 b0 b1 l0 l1 n0 n1 wf wc b2 hfv hcv n2 hK hnext

theorem agC_loop98 (hF : FsRowsC S Ha) (hA : AggAns Ha Ht cs h) (hn0 : 0 < cs.length)
    (hC : ChildClaimsAt rd pis fresh carried cs) (hM : AggMemH Ht rd P fresh carried cs h) :
    coreProgram.RelB S rd "__loop98" [1, gen ^ cs.length, P.mcc, P.lamM, P.frow, P.crow] [] := by
  refine loopS_complete (B := fun j => j < cs.length) hn0 rfl (fun j hj => hj)
    fun d j hj hK hnext => ?_
  obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC j hj
  obtain ⟨b0, b1, b2⟩ := hM.mcc j hj.le
  obtain ⟨n0, n1, n2⟩ := hM.mcc (j + 1) hj
  obtain ⟨l0, l1, l2⟩ := hM.lamM j hj
  obtain ⟨wf, wc⟩ := hM.rows j hj
  have hfv := readsAt_getD' gfr (k := 105) (by rw [(fixedCells_getD gsh).1]; omega)
  have hca := readsAt_getD' gcr (k := 51) (by rw [(deferCells_getD gb gm).1]; omega)
  have hcb := readsAt_getD' gcr (k := 52) (by rw [(deferCells_getD gb gm).1]; omega)
  rw [(fixedCells_getD gsh).2.2.2.2.2.2.2.2] at hfv
  rw [(deferCells_getD gb gm).2.2.2.2.1] at hca
  rw [(deferCells_getD gb gm).2.2.2.2.2] at hcb
  rw [getD_lMH Ht cs h hj] at l0 l1 l2
  rw [sqIt3H_succ Ht, show 3 * (j + 1) = 3 * j + 3 by ring] at n0
  rw [sqIt3H_succ Ht, show 3 * (j + 1) + 1 = 3 * j + 4 by ring] at n1
  rw [show 3 * (j + 1) + 2 = 3 * j + 5 by ring,
    sumE_take_succ' _ _ _ _ (0, 0, 0) hj (by rw [length_lMH]; exact hj), getD_lMH Ht cs h hj, mtTerm,
    ← add_assoc, ← add_assoc] at n2
  obtain ⟨q0, q1, q2⟩ := sq3Ans_get hA.sq3 j hj
  exact loop98C_back hF d j _ _ _ _ _ _ _ q0 q1 q2 b0 b1 l0 l1 l2 n0 n1 wf wc b2 hfv hca hcb n2 hK hnext

theorem agC_loop97 (hn0 : 0 < cs.length) (hbr : h.bytecodeRounds.length = 22)
    (hC : ChildClaimsAt rd pis fresh carried cs) (hM : AggMemH Ht rd P fresh carried cs h) :
    coreProgram.RelB S rd "__loop97" [1, gen ^ cs.length, P.frow, P.crow, P.rs, P.wB, P.lamB] [] := by
  have hrl : (agRbH Ht cs h).1.1.length = 22 := by rw [agRbH, batchRoundsWithH_length, hbr]
  refine loopS_complete (B := fun j => j < cs.length) hn0 rfl (fun j hj => hj)
    fun d j hj hK hnext => ?_
  obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC j hj
  obtain ⟨wf, wc⟩ := hM.rows j hj
  obtain ⟨l0, l1⟩ := hM.lamB j hj
  have hw := hM.wB j hj.le
  have hn := hM.wB (j + 1) hj
  rw [sumE_take_succ' _ _ _ _ (0, 0) hj (by rw [length_lBH]; exact hj), bcWeight, ← add_assoc] at hn
  refine loop97S_back d j _ _ _ cs[j].fresh.bytecodePoint cs[j].carried.bytecodePoint _ _ _ hrl gsh.1
    gb wf wc hM.rs ?_ ?_ hw l0 l1 hn hK hnext
  · exact readsAt_of_getDC gfr (by rw [(fixedCells_getD gsh).1, gsh.1]; omega)
      fun k hk => (fixedCells_getD gsh).2.1 k (by rw [gsh.1] at hk; exact hk)
  · exact readsAt_of_getDC gcr (by rw [(deferCells_getD gb gm).1, gb]; omega)
      fun k hk => (deferCells_getD gb gm).2.1 k (by rw [gb] at hk; exact hk)

theorem agC_loop99 (hn0 : 0 < cs.length) (hmr : h.matrixRounds.length = 28)
    (hC : ChildClaimsAt rd pis fresh carried cs) (hM : AggMemH Ht rd P fresh carried cs h) :
    coreProgram.RelB S rd "__loop99"
      [1, gen ^ cs.length, P.frow, P.eqR, P.rM, P.eqC, P.crow, P.lamM, P.wsum] [] := by
  have hrl : (agRmH Ht cs h).1.1.length = 28 := by rw [agRmH, batchRoundsWithH_length, hmr]
  refine loopS_complete (B := fun j => j < cs.length) hn0 rfl (fun j hj => hj)
    fun d j hj hK hnext => ?_
  obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC j hj
  obtain ⟨wf, wc⟩ := hM.rows j hj
  obtain ⟨l0, l1, l2⟩ := hM.lamM j hj
  obtain ⟨w0, w1⟩ := hM.wsum j hj.le
  obtain ⟨n0, n1⟩ := hM.wsum (j + 1) hj
  rw [sumE_take_succ' _ _ _ _ (0, 0, 0) hj (by rw [length_lMH]; exact hj), mtWeightA, ← add_assoc,
    show 2 * (j + 1) = 2 * j + 2 by ring, ← l99U_eq gsh hrl, ← carProd_eq gb gm hrl] at n0
  rw [sumE_take_succ' _ _ _ _ (0, 0, 0) hj (by rw [length_lMH]; exact hj), mtWeightB, ← add_assoc,
    show 2 * (j + 1) + 1 = 2 * j + 3 by ring, ← l99U_eq gsh hrl, ← carProd_eq gb gm hrl,
    ← (fixedCells_getD gsh).2.2.2.1] at n1
  refine loop99S_back d j _ _ _ _ _ _ _ _ _ _ _ _ (fixedCells_getD gsh).1 (deferCells_getD gb gm).1
    hrl wf wc gfr gcr hM.rM (fun i hi => ?_) (fun i hi => ?_) l0 l1 l2 w0 w1 n0 n1 hK hnext
  · have := hM.eqR 5 (by omega) i (by norm_num; omega)
    rwa [etK, List.take_take, min_self, show 2 ^ (5 + 1) - 2 + i = 62 + i by norm_num] at this
  · have := hM.eqC 5 (by omega) i (by norm_num; omega)
    rwa [etK, List.take_take, min_self, show 2 ^ (5 + 1) - 2 + i = 62 + i by norm_num] at this

/-! ## The body -/

variable (Ht) in
/-- **`aggregate_claims`' honest valuation** over `Ht`: its pointers, the hints, the transcript's seed and
first absorb, the run's values, the two `eqtree`s, the final check, the stored points. -/
noncomputable def agValH (cs : List ChildClaims) (h : BatchHints) (P : AggPtrs) (pis fresh carried dp : E) : Val :=
  let gn := gen ^ cs.length
  let cvA := agCvAH Ht cs
  let rb := agRbH Ht cs h
  let rm := agRmH Ht cs h
  let s1 := sumE (List.zipWith (mtWeightA rm.1.1) cs (agLMH Ht cs h))
  let s2 := sumE (List.zipWith (mtWeightB rm.1.1) cs (agLMH Ht cs h))
  setv (setv (setl (setEt (setl (setEt (setl (setv (setl
    (Val.ofArgs [gn, pis, fresh, carried, dp]) 5
      [P.msgB, P.msgM, h.bytecodeValue, h.matrixA, h.matrixB, P.frow, P.crow,
        word 13601591990776631179 14393745058652752134 0, word 10115303172019694088 4136606974476857268 0])
    14 14 (fsValsD gn (agCv1H Ht cs) 1)) 28
    [gen, gn * gen, gn * gen * (gn * gen), P.absb, 1, 1 + gn, 1, gn * gn, P.absb * (gn * gn), gn * gn,
      P.lamB, gen, gn * gen, gn * gen * (gn * gen), gn * gen * (gn * gen) * (gn * gen), P.bcc,
      (digestScalars cvA).1, (digestScalars cvA).2, 0, 1, 1 + gn, 1, gn * gn, gn * gn * gn,
      P.bcc * (gn * gn * gn), (digestScalars (sqIt2H Ht cvA cs.length)).1,
      (digestScalars (sqIt2H Ht cvA cs.length)).2, sumE (List.zipWith bcTerm cs (agLBH Ht cs)), P.rs,
      (digestScalars rb.2).1, (digestScalars rb.2).2, rb.1.2, (digestScalars rb.2).1,
      (digestScalars rb.2).2, gen, gn * gen, P.wB, 0, 1, 1 + gn, 1, P.wB * gn,
      sumE (List.zipWith (bcWeight rb.1.1) cs (agLBH Ht cs)),
      h.bytecodeValue * sumE (List.zipWith (bcWeight rb.1.1) cs (agLBH Ht cs)), gn * gn, gn * gn * gn,
      P.lamM, gen, gn * gen, gn * gen * (gn * gen), gn * gen * (gn * gen) * (gn * gen), P.mcc, 0, 1,
      1 + gn, 1, gn * gn, gn * gn * gn, P.mcc * (gn * gn * gn),
      (digestScalars (sqIt3H Ht rb.2 cs.length)).1, (digestScalars (sqIt3H Ht rb.2 cs.length)).2,
      sumE (List.zipWith mtTerm cs (agLMH Ht cs h)), P.rM, (digestScalars rm.2).1, (digestScalars rm.2).2,
      rm.1.2, (digestScalars rm.2).1, (digestScalars rm.2).2, P.eqR])
    97 (rm.1.1.take 6)) 301 [P.eqC]) 302 ((rm.1.1.drop 14).take 6)) 506
    [gen, gn * gen, gn * gen * (gn * gen), P.wsum, 0, 0, 1, 1 + gn, 1, gn * gn, P.wsum * (gn * gn), s1,
      h.matrixA * s1, s2, h.matrixB * s2, h.matrixA * s1 + h.matrixB * s2])
    522 22 fun k => rb.1.1.getD k 0) 544 28 fun k => rm.1.1.getD k 0

/-- `aggregate_claims`' body on its honest valuation. -/
theorem agBodyC_holds (hF : FsRowsC S Ha) (hBs : BsRowsC S Ha) {cs : List ChildClaims} {h : BatchHints}
    {d : DeferredClaim} (hA : AggAns Ha Ht cs h) (hne : cs ≠ [])
    (hb : Id.run (batchWith (m := Id) Ht aggSeedD cs h) = some d)
    (hbr : h.bytecodeRounds.length = 22) (hmr : h.matrixRounds.length = 28)
    {pis fresh carried dp : E} (hC : ChildClaimsAt rd pis fresh carried cs)
    (hd : ReadsAt rd dp d.cells) (P : AggPtrs) (hM : AggMemH Ht rd P fresh carried cs h) :
    Stmt.HoldsListB S (coreProgram.RelB S rd) rd (agValH Ht cs h P pis fresh carried dp) agBody False
      (fun rs => rs = []) := by
  have hn0 : 0 < cs.length := List.length_pos_iff.mpr hne
  rw [batchH_eq] at hb
  split_ifs at hb with hck
  obtain ⟨hck1, hck2⟩ := hck
  cases hb
  rw [agBody]
  simp only [holdsListB_append]
  rw [holdsListB_noRet (fsCompressT (.n 12) (.n 13) (.n 0) 14 1) rfl,
    holdsListB_noRet (eqtreeT (.n 90) 0 (.n 96) 97) (noRetList_eqtreeT ..),
    holdsListB_noRet (eqtreeT (.n 90) 14 (.n 301) 302) (noRetList_eqtreeT ..),
    holdsListB_noRet agStores noRetList_agStores]
  simp only [agP1, agP2, agP3, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil,
    word_gen, word_one, word_zero]
  have hrb : (agRbH Ht cs h).1.1.length = 22 := by rw [agRbH, batchRoundsWithH_length, hbr]
  have hrm : (agRmH Ht cs h).1.1.length = 28 := by rw [agRmH, batchRoundsWithH_length, hmr]
  have hK : IsInK (1 + gen ^ cs.length) := isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK _)
  have tB : (agLBH Ht cs).take cs.length = agLBH Ht cs := by rw [← length_lBH Ht cs, List.take_length]
  have tM : (agLMH Ht cs h).take cs.length = agLMH Ht cs h := by rw [← length_lMH Ht cs h, List.take_length]
  obtain ⟨b0, b1, b2⟩ := hM.bcc 0 (Nat.zero_le _)
  obtain ⟨bn0, bn1, bn2⟩ := hM.bcc cs.length le_rfl
  obtain ⟨m0, m1, m2⟩ := hM.mcc 0 (Nat.zero_le _)
  obtain ⟨mn0, mn1, mn2⟩ := hM.mcc cs.length le_rfl
  obtain ⟨w0, w1⟩ := hM.wsum 0 (Nat.zero_le _)
  obtain ⟨wn0, wn1⟩ := hM.wsum cs.length le_rfl
  obtain ⟨a0, a1⟩ := hM.absb 0 (Nat.zero_le _)
  obtain ⟨an0, an1⟩ := hM.absb cs.length le_rfl
  have v0 := hM.wB 0 (Nat.zero_le _)
  have vn := hM.wB cs.length le_rfl
  simp only [List.take_zero, List.flatMap_nil, List.zipWith_nil_left, List.take_length, tB, tM]
    at b2 m2 w0 w1 a0 a1 an0 an1 v0 bn2 mn2 wn0 wn1 vn
  simp only [agValH]
  ag_look
  simp only [true_and, and_true]
  refine ⟨hF.fsCompress _ _ _ _ (by decide) ⟨⟨aggSeedD, agCv1H Ht cs, by ag_look; exact aggSeed_cells,
      by ag_look; rw [gen_pow_eq_ofK]; exact hA.cv1, fun k h1 h2 => by ag_look⟩, trivial⟩, ?_, ?_, hK,
    fun _ => agC_loop95 hF hA hn0 hC hM, ?_, b0, ?_, b1, by simpa [sumE] using b2, hK,
    fun _ => agC_loop96 hF hA hn0 hC hM, ?_, ?_, ?_, ?_, by simpa [sumE] using v0, hK,
    fun _ => agC_loop97 hn0 hbr hC hM, ?_, e_add_eq_zero_iff.mpr hck1, m0, m1,
    by simpa [sumE] using m2, hK, fun _ => agC_loop98 hF hA hn0 hC hM, ?_, ?_, ?_, ?_, ?_, ?_,
    by simpa [sumE] using w0, by simpa [sumE] using w1, hK, fun _ => agC_loop99 hn0 hmr hC hM, ?_, ?_,
    e_add_eq_zero_iff.mpr hck2, ?_⟩
  · simpa [obsAllH, fsValsD] using a0
  · simpa [obsAllH, fsValsD] using a1
  · exact loadHolds_of_mul0 (by ring) an0
  · exact loadHolds_of_mul (by ring) an1
  · exact loadHolds_of_mul0 (by ring) bn0
  · exact loadHolds_of_mul (by ring) bn1
  · exact loadHolds_of_mul (by ring) bn2
  · exact hBs.bs22 rd _ _ ⟨_, h.bytecodeRounds, _, _, _, rfl, hbr,
      fun r hr => by
        have := hM.msgB r (by rwa [hbr] at hr)
        rwa [List.getD_eq_getElem _ _ hr] at this, hA.runB, hM.rs, rfl⟩
  · exact loadHolds_of_mul0 rfl vn
  · exact loadHolds_of_mul0 (by ring) mn0
  · exact loadHolds_of_mul (by ring) mn1
  · exact loadHolds_of_mul (by ring) mn2
  · exact hBs.bs28 rd _ _ ⟨_, h.matrixRounds, _, _, _, rfl, hmr,
      fun r hr => by
        have := hM.msgM r (by rwa [hmr] at hr)
        rwa [List.getD_eq_getElem _ _ hr] at this, hA.runM, hM.rM, rfl⟩
  · refine eqtreeS_complete (.n 90) (.n 96) 0 97 _ ((agRmH Ht cs h).1.1.take 6) (by simp [hrm])
      (etVals_congr (fun i h1 h2 => by ag_look; rfl) (setEt_vals _ _ _)) (fun t ht => ?_)
      (fun t ht i hi => by ag_look; exact hM.eqR t ht i hi)
    ag_look
    rw [getD_take _ ht]
    exact readsAt_getD' hM.rM (by omega)
  · refine eqtreeS_complete (.n 90) (.n 301) 14 302 _ (((agRmH Ht cs h).1.1.drop 14).take 6)
      (by simp [hrm]) (etVals_congr (fun i h1 h2 => by ag_look; rfl) (setEt_vals _ _ _)) (fun t ht => ?_)
      (fun t ht i hi => by ag_look; exact hM.eqC t ht i hi)
    ag_look
    rw [getD_take _ ht, getD_drop]
    exact readsAt_getD' hM.rM (by omega)
  · exact loadHolds_of_mul0 (by ring) wn0
  · exact loadHolds_of_mul (by ring) wn1
  · obtain ⟨dl, d1, d2, d3, d4, d5⟩ := deferCells_getD
      (d := ⟨(agRbH Ht cs h).1.1, h.bytecodeValue, (agRmH Ht cs h).1.1, h.matrixA, h.matrixB⟩) hrb hrm
    have hdk : ∀ k < 53, LoadHolds rd dp k
        (DeferredClaim.cells ⟨(agRbH Ht cs h).1.1, h.bytecodeValue, (agRmH Ht cs h).1.1, h.matrixA,
          h.matrixB⟩ |>.getD k 0) := fun k hk => readsAt_getD' hd (by rw [dl]; exact hk)
    rw [agStores]
    simp only [holdsListB_append]
    rw [holdsListB_flatten_range 22 (fun k => [Stmt.atom (.load (.n (522 + k)) (.n 56) k),
        .atom (.load (.n (522 + k)) (.n 4) k)]) (fun _ => rfl),
      holdsListB_flatten_range 28 (fun k => [Stmt.atom (.load (.n (544 + k)) (.n 90) k),
        .atom (.load (.n (544 + k)) (.n 4) (23 + k))]) (fun _ => rfl)]
    simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
    refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, ?_, ?_⟩
    · ag_look
      refine ⟨readsAt_getD' hM.rs (by omega), ?_⟩
      have := hdk k (by omega)
      rwa [d1 k hk] at this
    · ag_look
      have := hdk 22 (by omega)
      rwa [d2] at this
    · ag_look
      refine ⟨readsAt_getD' hM.rM (by omega), ?_⟩
      have := hdk (23 + k) (by omega)
      rwa [d3 k hk] at this
    · ag_look
      have := hdk 51 (by omega)
      rwa [d4] at this
    · ag_look
      have := hdk 52 (by omega)
      rwa [d5] at this

/-- **`aggregate_claims`, completely** (G:3319-3486; TRIAGE #77): for nonempty claims `cs` at the
buffers (`ChildClaimsAt`), hints `h` of `22` and `28` rounds whose batching closes
on `d`, stored at `defer_stmt`, every choice of the `HeapBuf` pointers `P` and every memory
holding the honest words there (`AggMemH`), `aggregate_claims` holds. -/
theorem aggregateC_claims_complete (hF : FsRowsC S Ha) (hBs : BsRowsC S Ha) {cs : List ChildClaims}
    {h : BatchHints} {d : DeferredClaim} (hA : AggAns Ha Ht cs h) (hne : cs ≠ [])
    (hb : Id.run (batchWith (m := Id) Ht aggSeedD cs h) = some d)
    (hbr : h.bytecodeRounds.length = 22) (hmr : h.matrixRounds.length = 28)
    {pis fresh carried dp : E} (hC : ChildClaimsAt rd pis fresh carried cs)
    (hd : ReadsAt rd dp d.cells) (P : AggPtrs) (hM : AggMemH Ht rd P fresh carried cs h) :
    coreProgram.RelB S rd "aggregate_claims" [gen ^ cs.length, pis, fresh, carried, dp] [] := by
  rw [relB_iff_sem find_aggregate_claims]
  refine ⟨agValH Ht cs h P pis fresh carried dp, by
    simp only [show Fn.params Data.core29 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, List.map_cons,
      List.map_nil, agValH]; ag_look, ?_⟩
  rw [core29_body]
  exact agBodyC_holds hF hBs hA hne hb hbr hmr hC hd P hM

end Loops

end
end LeanVM.Guest.B1.Main
