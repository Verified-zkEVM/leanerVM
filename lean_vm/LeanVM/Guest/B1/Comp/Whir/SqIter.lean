/-
  LeanVM.Guest.B1.Comp.Whir.SqIter

  One iteration of `open_stacked`'s squeeze loop at its honest valuation over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.OsBody
public import LeanVM.Guest.B1.Whir.SqIter
public import LeanVM.Guest.B1.Whir.StackedLoopsM

/-!
# One squeeze over a completeness model (TRIAGE #36)

`Whir/SqIter.lean` over a `CompModel` and a total hash `Ht`: `sqIterValW` is `sqIterVal` with the
squeeze's values over `Ht`; `sqIter_holdsC` is `sqIter_holds` under `CM.sem`, the model answering the
squeeze of the state `cv` (`sqCvM CM.hm cv`, what `ansRun_sampleQueries` gives step by step);
`sqIterVal_ptrsW` is `sqIterVal_ptrs` at it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.E2E.Complete

@[expose] public section

variable {C : CallRel} {rd : Reader} {CM : CompModel} {Ht : Bytes → Digest}

/-- **The squeeze loop's body's valuation at `x`**, from the state `cv` at `sqz·x²`. -/
def sqIterValW (Ht : Bytes → Digest) (lv : OsLvl) (x N sqz qpos qbp : E) (cv : Digest) : Val :=
  let q := x ^ osDigitsVal 1 (osPowDigits (192 / lv.depth))
  setl (Val.ofArgs [x, N, sqz, qpos, qbp]) 5
    ([x * x, sqz * (x * x), (digestScalars cv).1, (digestScalars cv).2, (digestScalars cv).1,
      (digestScalars cv).2] ++ (List.range 14).map (sqValsW Ht cv) ++ [sqValsW Ht cv 5, sqValsW Ht cv 6] ++
      osPowVals x (osPowDigits (192 / lv.depth)) x ++ sqPtrVals lv.posOff qpos q ++
      sqPtrVals lv.posOff qbp q ++ [gen, x * gen, x * gen + N, gen, x * gen])


/-- **One squeeze's body holds** at `sqIterValW Ht`, on a memory holding the state `cv` and the next
state at `sqz·x²`, the decode call and the tail's call holding. -/
theorem sqIter_holdsC {lv : OsLvl} (hpo : lv.posOff < 2 ^ 128)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth) {x N sqz qpos qbp : E}
    {cv : Digest}
    (l0 : LoadHolds rd (sqz * (x * x)) 0 (digestScalars cv).1)
    (l1 : LoadHolds rd (sqz * (x * x)) 1 (digestScalars cv).2)
    (l2 : LoadHolds rd (sqz * (x * x)) 2 (digestScalars (sqCvW Ht cv)).1)
    (l3 : LoadHolds rd (sqz * (x * x)) 3 (digestScalars (sqCvW Ht cv)).2)
    (asq : sqCvM CM.hm cv = some (sqCvW Ht cv))
    (hdec : C lv.decode [challengeOf (sqCvW Ht cv), qpos * gen ^ lv.posOff * x ^ (192 / lv.depth),
      qbp * gen ^ lv.posOff * x ^ (192 / lv.depth)] [])
    (hK : IsInK (x * gen + N)) (hcall : x * gen + N ≠ 0 → C lv.sqLoop [x * gen, N, sqz, qpos, qbp] []) :
    Stmt.HoldsListB CM.sem C rd (sqIterValW Ht lv x N sqz qpos qbp cv) (sqLoopOf lv) False (fun rs => rs = []) := by
  set q := x ^ osDigitsVal 1 (osPowDigits (192 / lv.depth)) with hq
  set pv := osPowVals x (osPowDigits (192 / lv.depth)) x
  set P1 := sqPtrVals lv.posOff qpos q
  set P2 := sqPtrVals lv.posOff qbp q
  set A : List E := [x * x, sqz * (x * x), (digestScalars cv).1, (digestScalars cv).2,
      (digestScalars cv).1, (digestScalars cv).2] with hA
  set S : List E := (List.range 14).map (sqValsW Ht cv) with hS
  set B : List E := [sqValsW Ht cv 5, sqValsW Ht cv 6] with hB
  set T : List E := [gen, x * gen, x * gen + N, gen, x * gen] with hT
  set vals : List E := A ++ (S ++ (B ++ (pv ++ (P1 ++ (P2 ++ T))))) with hvals
  set σ := sqIterValW Ht lv x N sqz qpos qbp cv with hσ
  have hσ' : σ = setl (Val.ofArgs [x, N, sqz, qpos, qbp]) 5 vals := by
    rw [hσ, sqIterValW]; simp only [vals, A, S, B, T, P1, P2, pv, q, List.append_assoc]
  have larg : ∀ i < 5, σ (.n i) = [x, N, sqz, qpos, qbp].getD i 0 := fun i hi => by
    rw [hσ']; simp only [setl]; rw [set_n_lt (by omega)]; rfl
  have lv' : ∀ off < vals.length, σ (.n (5 + off)) = vals.getD off 0 := fun off ho => by
    rw [hσ']; simp only [setl]; rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have hlen1 : ∀ v, (sqPtrVals lv.posOff v q).length = (sqPtrVals lv.posOff 0 0).length := by
    intro v; unfold sqPtrVals; split <;> simp
  have lA : A.length = 6 := rfl
  have lS : S.length = 14 := by simp [S]
  have lB : B.length = 2 := rfl
  have lT : T.length = 5 := rfl
  have skip : ∀ (l l' : List E) (n : ℕ), (l ++ l').getD (l.length + n) 0 = l'.getD n 0 := fun l l' n => by
    rw [oq_getD_app_ge (by omega), Nat.add_sub_cancel_left]
  have hvl : vals.length = 22 + pv.length + P1.length + P2.length + 5 := by
    simp only [vals, List.length_append, lA, lS, lB, lT]; omega
  have gA : ∀ t < 6, σ (.n (5 + t)) = A.getD t 0 := fun t ht => by
    rw [lv' t (by omega), hvals, oq_getD_app_lt (by omega)]
  have gS : ∀ t < 14, σ (.n (11 + t)) = sqValsW Ht cv t := fun t ht => by
    rw [show 11 + t = 5 + (A.length + t) by rw [lA]; ring, lv' _ (by omega), hvals, skip,
      oq_getD_app_lt (by omega)]
    simp [S, List.getD_eq_getElem?_getD, ht]
  have gB : σ (.n 25) = sqValsW Ht cv 5 ∧ σ (.n 26) = sqValsW Ht cv 6 := by
    refine ⟨?_, ?_⟩
    · rw [show 25 = 5 + (A.length + (S.length + 0)) by rw [lA, lS], lv' _ (by omega), hvals, skip, skip]; rfl
    · rw [show 26 = 5 + (A.length + (S.length + 1)) by rw [lA, lS], lv' _ (by omega), hvals, skip, skip]; rfl
  have gP : ∀ t < pv.length, σ (.n (27 + t)) = pv.getD t 0 := fun t ht => by
    rw [show 27 + t = 5 + (A.length + (S.length + (B.length + t))) by rw [lA, lS, lB]; ring, lv' _ (by omega),
      hvals, skip, skip, skip, oq_getD_app_lt (by omega)]
  have hk : sqK lv = 27 + pv.length := sqK_eq lv x x
  have gP1 : ∀ t < P1.length, σ (.n (sqK lv + t)) = P1.getD t 0 := fun t ht => by
    rw [hk, show 27 + pv.length + t = 5 + (A.length + (S.length + (B.length + (pv.length + t)))) by
      rw [lA, lS, lB]; ring, lv' _ (by omega), hvals, skip, skip, skip, skip, oq_getD_app_lt (by omega)]
  have hp1 := sqPtr_index lv.posOff (sqPw lv).2 3 (sqK lv)
  have gP2 : ∀ t < P2.length, σ (.n ((sqP1 lv).2.2 + t)) = P2.getD t 0 := fun t ht => by
    rw [show (sqP1 lv).2.2 = sqK lv + P1.length by rw [sqP1, hp1.2, hlen1], hk,
      show 27 + pv.length + P1.length + t = 5 + (A.length + (S.length + (B.length + (pv.length + (P1.length + t)))))
        by rw [lA, lS, lB]; ring, lv' _ (by omega), hvals, skip, skip, skip, skip, skip, oq_getD_app_lt (by omega)]
  have hp2 := sqPtr_index lv.posOff (sqPw lv).2 4 (sqP1 lv).2.2
  have hE : sqE lv = sqK lv + P1.length + P2.length := by
    rw [sqE, sqP2, hp2.2, sqP1, hp1.2, hlen1, hlen1]
  have gT : ∀ t < 5, σ (.n (sqE lv + t)) = T.getD t 0 := fun t ht => by
    rw [hE, hk, show 27 + pv.length + P1.length + P2.length + t =
      5 + (A.length + (S.length + (B.length + (pv.length + (P1.length + (P2.length + t)))))) by
        rw [lA, lS, lB]; ring, lv' _ (by omega), hvals, skip, skip, skip, skip, skip, skip]
  have a0 : σ (.n 0) = x := larg 0 (by omega)
  have a1 : σ (.n 1) = N := larg 1 (by omega)
  have a2 : σ (.n 2) = sqz := larg 2 (by omega)
  have a3 : σ (.n 3) = qpos := larg 3 (by omega)
  have a4 : σ (.n 4) = qbp := larg 4 (by omega)
  -- the power
  have hpw : Stmt.HoldsList C rd σ (sqPw lv).1 True (fun rs => rs = []) := by
    refine osPowSteps_complete 0 _ 0 27 x a0 fun j hj => ?_
    rw [a0]; exact gP j (by rw [a0] at hj; exact hj)
  have hqv : σ (.n (sqPw lv).2) = q := by
    have := osPowSteps_sound (C := C) (rd := rd) (σ := σ) 0 _ 0 27 1 (by rw [pow_one, a0]) hpw
    rw [show (sqPw lv).2 = (osPowSteps 0 (osPowDigits (192 / lv.depth)) 0 27).2 from rfl, this, a0]
  rw [sqLoopOf_eq]
  simp only [holdsListB_append]
  refine (holdsListB_noRet _ rfl _ _).mpr ⟨?_, ?_⟩
  · have e0 := gA 0 (by omega); have e1 := gA 1 (by omega); have e2 := gA 2 (by omega)
    have e3 := gA 3 (by omega); have e4 := gA 4 (by omega); have e5 := gA 5 (by omega)
    simp only [hA, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd] at e0 e1 e2 e3 e4 e5
    simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
    refine ⟨by rw [e0, a0], by rw [e1, a2, e0], by rw [e1, e2]; exact l0, by rw [e1, e3]; exact l1,
      by rw [e4, e2], by rw [e5, e3]⟩
  refine (holdsListB_noRet _ (by simp [squeezeT, squeezeStateT, challengeT, Stmt.noRetList, Stmt.noRet]) _ _).mpr
    ⟨?_, ?_⟩
  · have e4 := gA 4 (by omega); have e5 := gA 5 (by omega)
    simp only [hA, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd] at e4 e5
    exact holdsB_squeezeT_comp _ _ _ ⟨⟨cv, sqCvW Ht cv, by rw [e4, e5], asq,
      fun t ht => by rw [gS t ht, sqValsW_eq Ht cv ht]⟩, trivial⟩
  refine (holdsListB_noRet _ rfl _ _).mpr ⟨?_, ?_⟩
  · have e1 := gA 1 (by omega)
    simp only [hA, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd] at e1
    have s5 := gS 5 (by omega); have s6 := gS 6 (by omega)
    simp only [Nat.reduceAdd] at s5 s6
    simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
    refine ⟨by rw [gB.1, s5], by rw [gB.2, s6], by rw [e1, gB.1]; exact l2, by rw [e1, gB.2]; exact l3⟩
  refine (holdsListB_noRet _ (osPowSteps_noRet _ _ _ _) _ _).mpr
    ⟨(holdsListB_iff_of_noBlake (osPowSteps_noBlake _ _ _ _) _ _).mpr hpw, ?_⟩
  have hpv1 : σ (.n (sqP1 lv).2.1) = qpos * gen ^ lv.posOff * x ^ (192 / lv.depth) := by
    have := sqPtr_sound (C := C) (rd := rd) (σ := σ) hpo (sqPtr_complete (kret := fun rs => rs = [])
      (posOff := lv.posOff) (q := (sqPw lv).2) (base := 3) (k := sqK lv) fun j hj => by rw [a3, hqv]; exact gP1 j (by rw [a3, hqv] at hj; exact hj))
    rw [sqP1, this, a3, hqv, hq, hdig]
  have hpv2 : σ (.n (sqP2 lv).2.1) = qbp * gen ^ lv.posOff * x ^ (192 / lv.depth) := by
    have := sqPtr_sound (C := C) (rd := rd) (σ := σ) hpo (sqPtr_complete (kret := fun rs => rs = [])
      (posOff := lv.posOff) (q := (sqPw lv).2) (base := 4) (k := (sqP1 lv).2.2) fun j hj => by rw [a4, hqv]; exact gP2 j (by rw [a4, hqv] at hj; exact hj))
    rw [sqP2, this, a4, hqv, hq, hdig]
  refine (holdsListB_noRet _ (sqPtr_noRet _ _ _ _) _ _).mpr
    ⟨(holdsListB_iff_of_noBlake (sqPtr_noBlake _ _ _ _) _ _).mpr (sqPtr_complete fun j hj => ?_), ?_⟩
  · rw [a3, hqv]; exact gP1 j (by rw [a3, hqv] at hj; exact hj)
  refine (holdsListB_noRet _ (sqPtr_noRet _ _ _ _) _ _).mpr
    ⟨(holdsListB_iff_of_noBlake (sqPtr_noBlake _ _ _ _) _ _).mpr (sqPtr_complete fun j hj => ?_), ?_⟩
  · rw [a4, hqv]; exact gP2 j (by rw [a4, hqv] at hj; exact hj)
  have t0 := gT 0 (by omega); have t1 := gT 1 (by omega); have t2 := gT 2 (by omega)
  have t3 := gT 3 (by omega); have t4 := gT 4 (by omega)
  simp only [hT, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at t0 t1 t2 t3 t4
  have s13 := gS 13 (by omega)
  simp only [Nat.reduceAdd] at s13
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen]
  refine ⟨?_, t0, by rw [t1, a0, t0], by rw [t2, t1, a1], t3, by rw [t4, a0, t3], by rw [t2]; exact hK,
    fun h => ?_, trivial⟩
  · rw [s13, hpv1, hpv2]; exact hdec
  · rw [t4, a1, a2, a3, a4]
    exact hcall (by rwa [t2] at h)

/-- **The pointers and arguments of one squeeze** at `sqIterValW Ht`: the row, the challenge, the
positions' and bit runs' pointers, the tail's condition and argument. -/
theorem sqIterVal_ptrsW {lv : OsLvl} (hpo : lv.posOff < 2 ^ 128)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth) (x N sqz qpos qbp : E)
    (cv : Digest) :
    (∀ i < 5, sqIterValW Ht lv x N sqz qpos qbp cv (.n i) = [x, N, sqz, qpos, qbp].getD i 0) ∧
      sqIterValW Ht lv x N sqz qpos qbp cv (.n 6) = sqz * (x * x) ∧
      sqIterValW Ht lv x N sqz qpos qbp cv (.n 24) = challengeOf (sqCvW Ht cv) ∧
      sqIterValW Ht lv x N sqz qpos qbp cv (.n (sqP1 lv).2.1) = qpos * gen ^ lv.posOff * x ^ (192 / lv.depth) ∧
      sqIterValW Ht lv x N sqz qpos qbp cv (.n (sqP2 lv).2.1) = qbp * gen ^ lv.posOff * x ^ (192 / lv.depth) ∧
      sqIterValW Ht lv x N sqz qpos qbp cv (.n (sqE lv + 2)) = x * gen + N ∧
      sqIterValW Ht lv x N sqz qpos qbp cv (.n (sqE lv + 4)) = x * gen := by
  set q := x ^ osDigitsVal 1 (osPowDigits (192 / lv.depth)) with hq
  set pv := osPowVals x (osPowDigits (192 / lv.depth)) x
  set P1 := sqPtrVals lv.posOff qpos q
  set P2 := sqPtrVals lv.posOff qbp q
  set A : List E := [x * x, sqz * (x * x), (digestScalars cv).1, (digestScalars cv).2,
      (digestScalars cv).1, (digestScalars cv).2] with hA
  set S : List E := (List.range 14).map (sqValsW Ht cv) with hS
  set B : List E := [sqValsW Ht cv 5, sqValsW Ht cv 6] with hB
  set T : List E := [gen, x * gen, x * gen + N, gen, x * gen] with hT
  set vals : List E := A ++ (S ++ (B ++ (pv ++ (P1 ++ (P2 ++ T))))) with hvals
  set σ := sqIterValW Ht lv x N sqz qpos qbp cv with hσ
  have hσ' : σ = setl (Val.ofArgs [x, N, sqz, qpos, qbp]) 5 vals := by
    rw [hσ, sqIterValW]; simp only [vals, A, S, B, T, P1, P2, pv, q, List.append_assoc]
  have larg : ∀ i < 5, σ (.n i) = [x, N, sqz, qpos, qbp].getD i 0 := fun i hi => by
    rw [hσ']; simp only [setl]; rw [set_n_lt (by omega)]; rfl
  have lv' : ∀ off < vals.length, σ (.n (5 + off)) = vals.getD off 0 := fun off ho => by
    rw [hσ']; simp only [setl]; rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have hlen1 : ∀ v, (sqPtrVals lv.posOff v q).length = (sqPtrVals lv.posOff 0 0).length := by
    intro v; unfold sqPtrVals; split <;> simp
  have lA : A.length = 6 := rfl
  have lS : S.length = 14 := by simp [S]
  have lB : B.length = 2 := rfl
  have lT : T.length = 5 := rfl
  have skip : ∀ (l l' : List E) (n : ℕ), (l ++ l').getD (l.length + n) 0 = l'.getD n 0 := fun l l' n => by
    rw [oq_getD_app_ge (by omega), Nat.add_sub_cancel_left]
  have hvl : vals.length = 22 + pv.length + P1.length + P2.length + 5 := by
    simp only [vals, List.length_append, lA, lS, lB, lT]; omega
  have gA : ∀ t < 6, σ (.n (5 + t)) = A.getD t 0 := fun t ht => by
    rw [lv' t (by omega), hvals, oq_getD_app_lt (by omega)]
  have gS : ∀ t < 14, σ (.n (11 + t)) = sqValsW Ht cv t := fun t ht => by
    rw [show 11 + t = 5 + (A.length + t) by rw [lA]; ring, lv' _ (by omega), hvals, skip,
      oq_getD_app_lt (by omega)]
    simp [S, List.getD_eq_getElem?_getD, ht]
  have gB : σ (.n 25) = sqValsW Ht cv 5 ∧ σ (.n 26) = sqValsW Ht cv 6 := by
    refine ⟨?_, ?_⟩
    · rw [show 25 = 5 + (A.length + (S.length + 0)) by rw [lA, lS], lv' _ (by omega), hvals, skip, skip]; rfl
    · rw [show 26 = 5 + (A.length + (S.length + 1)) by rw [lA, lS], lv' _ (by omega), hvals, skip, skip]; rfl
  have gP : ∀ t < pv.length, σ (.n (27 + t)) = pv.getD t 0 := fun t ht => by
    rw [show 27 + t = 5 + (A.length + (S.length + (B.length + t))) by rw [lA, lS, lB]; ring, lv' _ (by omega),
      hvals, skip, skip, skip, oq_getD_app_lt (by omega)]
  have hk : sqK lv = 27 + pv.length := sqK_eq lv x x
  have gP1 : ∀ t < P1.length, σ (.n (sqK lv + t)) = P1.getD t 0 := fun t ht => by
    rw [hk, show 27 + pv.length + t = 5 + (A.length + (S.length + (B.length + (pv.length + t)))) by
      rw [lA, lS, lB]; ring, lv' _ (by omega), hvals, skip, skip, skip, skip, oq_getD_app_lt (by omega)]
  have hp1 := sqPtr_index lv.posOff (sqPw lv).2 3 (sqK lv)
  have gP2 : ∀ t < P2.length, σ (.n ((sqP1 lv).2.2 + t)) = P2.getD t 0 := fun t ht => by
    rw [show (sqP1 lv).2.2 = sqK lv + P1.length by rw [sqP1, hp1.2, hlen1], hk,
      show 27 + pv.length + P1.length + t = 5 + (A.length + (S.length + (B.length + (pv.length + (P1.length + t)))))
        by rw [lA, lS, lB]; ring, lv' _ (by omega), hvals, skip, skip, skip, skip, skip, oq_getD_app_lt (by omega)]
  have hp2 := sqPtr_index lv.posOff (sqPw lv).2 4 (sqP1 lv).2.2
  have hE : sqE lv = sqK lv + P1.length + P2.length := by
    rw [sqE, sqP2, hp2.2, sqP1, hp1.2, hlen1, hlen1]
  have gT : ∀ t < 5, σ (.n (sqE lv + t)) = T.getD t 0 := fun t ht => by
    rw [hE, hk, show 27 + pv.length + P1.length + P2.length + t =
      5 + (A.length + (S.length + (B.length + (pv.length + (P1.length + (P2.length + t)))))) by
        rw [lA, lS, lB]; ring, lv' _ (by omega), hvals, skip, skip, skip, skip, skip, skip]
  have a0 : σ (.n 0) = x := larg 0 (by omega)
  have a1 : σ (.n 1) = N := larg 1 (by omega)
  have a2 : σ (.n 2) = sqz := larg 2 (by omega)
  have a3 : σ (.n 3) = qpos := larg 3 (by omega)
  have a4 : σ (.n 4) = qbp := larg 4 (by omega)
  have hpw : Stmt.HoldsList (fun _ _ _ => True) (fun _ => none) σ (sqPw lv).1 True (fun rs => rs = []) := by
    refine osPowSteps_complete 0 _ 0 27 x (larg 0 (by omega)) fun j hj => ?_
    rw [larg 0 (by omega)]; exact gP j (by rw [larg 0 (by omega)] at hj; exact hj)
  have hqv : σ (.n (sqPw lv).2) = q := by
    have := osPowSteps_sound (C := fun _ _ _ => True) (rd := fun _ => none) (σ := σ) 0 _ 0 27 1
      (by rw [pow_one, larg 0 (by omega)]) hpw
    rw [show (sqPw lv).2 = (osPowSteps 0 (osPowDigits (192 / lv.depth)) 0 27).2 from rfl, this, a0]
  have a3 : σ (.n 3) = qpos := larg 3 (by omega)
  have a4 : σ (.n 4) = qbp := larg 4 (by omega)
  have e1 := gA 1 (by omega)
  simp only [hA, List.getD_cons_zero, List.getD_cons_succ] at e1
  have s13 := gS 13 (by omega)
  have t2 := gT 2 (by omega); have t4 := gT 4 (by omega)
  simp only [hT, List.getD_cons_zero, List.getD_cons_succ] at t2 t4
  refine ⟨larg, e1, s13, ?_, ?_, t2, t4⟩
  · have := sqPtr_sound (C := fun _ _ _ => True) (rd := fun _ => none) (σ := σ) hpo (sqPtr_complete (kret := fun rs => rs = [])
      (posOff := lv.posOff) (q := (sqPw lv).2) (base := 3) (k := sqK lv) fun j hj => by rw [a3, hqv]; exact gP1 j (by rw [a3, hqv] at hj; exact hj))
    rw [sqP1, this, a3, hqv, hq, hdig]
  · have := sqPtr_sound (C := fun _ _ _ => True) (rd := fun _ => none) (σ := σ) hpo (sqPtr_complete (kret := fun rs => rs = [])
      (posOff := lv.posOff) (q := (sqPw lv).2) (base := 4) (k := (sqP1 lv).2.2) fun j hj => by rw [a4, hqv]; exact gP2 j (by rw [a4, hqv] at hj; exact hj))
    rw [sqP2, this, a4, hqv, hq, hdig]


end
end LeanVM.Guest.B1
