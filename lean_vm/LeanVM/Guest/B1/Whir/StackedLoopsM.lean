/-
  LeanVM.Guest.B1.Whir.StackedLoopsM

  `open_stacked`'s two loop helpers under a hash model: the squeezes that decode a level's query
  positions, answered by the model, and the residual loop, free of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B1.Whir.StackedLoops
public import LeanVM.Guest.B1.Whir.StackedBlocksM

/-!
# The loops of `open_stacked` under a hash model (TRIAGE #36)

* The squeeze loop (`SqBodyM`, `sqLoop_stepM`, `osSqueezes_soundM`): each iteration squeezes the
  state at `sqz[2j], sqz[2j+1]` into the model's answered digest, decoding its challenge; the
  squeezes are `sqAllM` from the state, the batching challenge one more answered squeeze.
* The residual loop has no `BLAKE2S` row and calls only itself (`resLoop_freeOn`), so its
  relation under any semantics is its deployed one (`resLoop_relB`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel} {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The residual loop -/

theorem resLoopBody_freeIn (posOff row cols qo : ℕ) (vals : List ℕ) (loop : String) :
    Stmt.freeInList [loop] (resLoopBody posOff row cols qo vals loop) = true := by
  unfold resLoopBody
  rw [freeInList_append, freeInList_append,
    freeInList_flatten_range _ _ _ (fun _ => rfl)]
  simp [Stmt.freeInList, Stmt.freeIn]

/-- The residual loop is free of `BLAKE2S` and calls only itself. -/
theorem resLoop_freeOn {posOff row cols qo : ℕ} {vals : List ℕ} {loop : String} {fn : Fn}
    (hfind : coreProgram.find? loop = some fn) (hb : fn.body = resLoopBody posOff row cols qo vals loop) :
    coreProgram.FreeOn [loop] = true :=
  freeOn_self hfind (by rw [hb]; exact resLoopBody_freeIn _ _ _ _ _ _)

/-- **The residual loop under any semantics** is its deployed relation. -/
theorem resLoop_relB {S : BlakeSem} {posOff row cols qo : ℕ} {vals : List ℕ} {loop : String} {fn : Fn}
    (hfind : coreProgram.find? loop = some fn) (hb : fn.body = resLoopBody posOff row cols qo vals loop)
    (args rets : List E) :
    coreProgram.RelB S rd loop args rets ↔ coreProgram.Rel rd loop args rets :=
  relB_iff_rel_of_freeOn (resLoop_freeOn hfind hb) (List.mem_singleton_self _) args rets

/-! ## The squeeze loop -/

theorem osPowSteps_noBlake (x : ℕ) : ∀ ds acc k, Stmt.noBlakeList (osPowSteps x ds acc k).1 = true
  | [], _, _ => rfl
  | d :: ds, acc, k => by
    unfold osPowSteps
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact osPowSteps_noBlake x ds k (k + 1)
    · simp only [↓reduceIte]
      exact osPowSteps_noBlake x ds (k + 1) (k + 2)

theorem sqPtr_noBlake (posOff q base k : ℕ) : Stmt.noBlakeList (sqPtr posOff q base k).1 = true := by
  unfold sqPtr; split <;> rfl

/-- One squeeze of the loop at `x` under a hash model: the state at `sqz·x²` squeezed into the
model's answered digest, stored in its next two words, and its challenge decoded at
`g^posOff·x^(192/depth)`. -/
def SqBodyM (M : HashModel) (rd : Reader) (depth posOff : ℕ) (sqz qpos qbp x : E) : Prop :=
  ∃ cv d, LoadHolds rd (sqz * (x * x)) 0 (digestScalars cv).1 ∧
    LoadHolds rd (sqz * (x * x)) 1 (digestScalars cv).2 ∧ sqCvM M cv = some d ∧
    LoadHolds rd (sqz * (x * x)) 2 (digestScalars d).1 ∧
    LoadHolds rd (sqz * (x * x)) 3 (digestScalars d).2 ∧
    MeaningDecodeQueryBits depth rd [challengeOf d,
      qpos * gen ^ posOff * x ^ (192 / depth), qbp * gen ^ posOff * x ^ (192 / depth)] []

theorem sqLoop_stepM {lv : OsLvl} {fn : Fn} (hfind : coreProgram.find? lv.sqLoop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) (hb : fn.body = sqLoopOf lv)
    (hdec : ∀ a r, coreProgram.RelB M.sem rd lv.decode a r → MeaningDecodeQueryBits lv.depth rd a r)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth)
    (hpo : lv.posOff < 2 ^ 128) {d : ℕ} {x N sqz qpos qbp : E}
    (h : coreProgram.relNB M.sem rd (d + 1) lv.sqLoop [x, N, sqz, qpos, qbp] []) :
    SqBodyM M rd lv.depth lv.posOff sqz qpos qbp x ∧ IsInK (x * gen + N) ∧
      (x * gen + N ≠ 0 → coreProgram.relNB M.sem rd d lv.sqLoop [x * gen, N, sqz, qpos, qbp] []) := by
  rw [relNB_succ_iff hfind, hp, hb, sqLoopOf, sqLoopBody] at h
  obtain ⟨σ, hpar, h⟩ := h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hpar
  simp only [holdsListB_append] at h
  obtain ⟨hA, h⟩ := holdsListB_split_free rfl rfl h
  obtain ⟨hS, h⟩ := holdsListB_true_of (by rfl) h
  obtain ⟨hB, h⟩ := holdsListB_split_free rfl rfl h
  obtain ⟨hP, h⟩ := holdsListB_split_free (osPowSteps_noBlake _ _ _ _) (osPowSteps_noRet _ _ _ _) h
  obtain ⟨h1, h⟩ := holdsListB_split_free (sqPtr_noBlake _ _ _ _) (sqPtr_noRet _ _ _ _) h
  obtain ⟨h2, h⟩ := holdsListB_split_free (sqPtr_noBlake _ _ _ _) (sqPtr_noRet _ _ _ _) h
  rw [holdsListB_iff_of_noBlake rfl] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hA hB h
  obtain ⟨a5, a6, l7, l8, a9, a10⟩ := hA
  obtain ⟨b25, b26, l25, l26⟩ := hB
  obtain ⟨hcall, e0, e1, e2, e3, e4, hK, hrec, -⟩ := h
  obtain ⟨⟨cv, dd, hcv, hdd, hv⟩, -⟩ := holdsB_squeezeT _ _ _ hS
  have hq := osPowSteps_sound 0 _ 0 27 1 (by rw [pow_one]) hP
  rw [hdig] at hq
  have hp1 := sqPtr_sound hpo h1
  have hp2 := sqPtr_sound hpo h2
  rw [hq] at hp1 hp2
  have hrow : σ (.n 6) = σ (.n 2) * (σ (.n 0) * σ (.n 0)) := by rw [a6, a5]
  have f16 : σ (.n (11 + 5)) = sqValsD dd 5 := hv 5 (by omega)
  have f17 : σ (.n (11 + 6)) = sqValsD dd 6 := hv 6 (by omega)
  have f24 : σ (.n (11 + 13)) = sqValsD dd 13 := hv 13 (by omega)
  simp only [Nat.reduceAdd] at f16 f17 f24
  rw [a9, a10] at hcv
  have c1 : σ (.n 7) = (digestScalars cv).1 := congrArg Prod.fst hcv
  have c2 : σ (.n 8) = (digestScalars cv).2 := congrArg Prod.snd hcv
  rw [e2, e1, e0, word_gen] at hK hrec
  refine ⟨⟨cv, dd, ?_, ?_, hdd, ?_, ?_, ?_⟩, hK, fun hne => ?_⟩
  · rw [← hrow, ← c1]; exact l7
  · rw [← hrow, ← c2]; exact l8
  · rw [← hrow]; convert l25 using 1; rw [b25, f16]; rfl
  · rw [← hrow]; convert l26 using 1; rw [b26, f17]; rfl
  · have := hdec _ _ (relNB_le_rel coreProgram d _ _ _ hcall)
    simp only [List.map_cons, List.map_nil] at this
    rwa [f24, hp1, hp2] at this
  · have := hrec hne
    simp only [List.map_cons, List.map_nil, e4, e3, word_gen] at this
    exact this

theorem sqBodyM_at {depth posOff : ℕ} {sqz qpos qbp : E} {j : ℕ}
    (h : SqBodyM M rd depth posOff sqz qpos qbp (gen ^ j)) :
    ∃ cv d, LoadHolds rd sqz (2 * j) (digestScalars cv).1 ∧
      LoadHolds rd sqz (2 * j + 1) (digestScalars cv).2 ∧ sqCvM M cv = some d ∧
      LoadHolds rd sqz (2 * j + 2) (digestScalars d).1 ∧
      LoadHolds rd sqz (2 * j + 3) (digestScalars d).2 ∧
      MeaningDecodeQueryBits depth rd [challengeOf d,
        qpos * gen ^ (posOff + j * (192 / depth)), qbp * gen ^ (posOff + j * (192 / depth))] [] := by
  obtain ⟨cv, d, l0, l1, hd, l2, l3, hdec⟩ := h
  rw [os_gen_pow_sq, loadHolds_mul_gen_pow] at l0 l1 l2 l3
  rw [← pow_mul, mul_assoc, mul_assoc, ← pow_add] at hdec
  rw [Nat.add_zero] at l0
  exact ⟨cv, d, l0, l1, hd, l2, l3, hdec⟩

private theorem getD_append_lt' {l l' : List E} {n : ℕ} (h : n < l.length) : (l ++ l').getD n 0 = l.getD n 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- **The query positions' squeezes under a hash model** (G:1144-1157): `nsq` answered squeezes
from the chain state `cv` (`sqAllM`, challenges `cs`), the `j`-th challenge decoded at
`posOff + j·(192/depth)`, then the batching challenge, one more answered squeeze, at the returned
`OsSt.k - 1`. -/
theorem osSqueezes_soundM {lv : OsLvl} {fn : Fn} (hfind : coreProgram.find? lv.sqLoop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) (hb : fn.body = sqLoopOf lv)
    (hdec : ∀ a r, coreProgram.RelB M.sem rd lv.decode a r → MeaningDecodeQueryBits lv.depth rd a r)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth)
    (hpo : lv.posOff < 2 ^ 128) {maxSq nsq qpos qbp : ℕ} (hnsq : nsq < 2 ^ 62) {cur : E} {s : OsSt}
    {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs) {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
      (osSqueezes maxSq nsq qpos qbp lv.sqLoop s).1 True kret) :
    ∃ (cs : List E) (cvq dl : Digest), sqAllM M nsq cv = some (cs, cvq) ∧ sqCvM M cvq = some dl ∧
      OsCur rd σ cur (osSqueezes maxSq nsq qpos qbp lv.sqLoop s).2 dl xs ∧
      σ (.n ((osSqueezes maxSq nsq qpos qbp lv.sqLoop s).2.k - 1)) = challengeOf dl ∧
      (∀ j < nsq, MeaningDecodeQueryBits lv.depth rd [cs.getD j 0,
        σ (.n qpos) * gen ^ (lv.posOff + j * (192 / lv.depth)),
        σ (.n qbp) * gen ^ (lv.posOff + j * (192 / lv.depth))] []) ∧
      (osSqueezes maxSq nsq qpos qbp lv.sqLoop s).2.co = s.co := by
  unfold osSqueezes at h ⊢
  simp only at h ⊢
  rw [holdsListB_append] at h
  obtain ⟨hpre, hsq⟩ := holdsListB_split_free rfl (by simp [osHeap, Stmt.noRetList, Stmt.noRet]) h
  clear h
  simp only [osHeap, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil, and_true, word_one] at hpre
  obtain ⟨-, -, l0, l1, e2, e3, e4, e5, e6, -, hrun, e7, e8, l9, l10⟩ := hpre
  rw [e4, e3, e2, os_gw_eq (by omega)] at hrun
  rw [e5, e6, os_gw_eq (by omega)] at hrun
  obtain ⟨m, hm, hN, hB⟩ := guarded_loopB_sound (P := coreProgram) (f := lv.sqLoop)
    (ps := [gen ^ nsq, σ (.n (s.k + 1)), σ (.n qpos), σ (.n qbp)])
    (B := SqBodyM M rd lv.depth lv.posOff (σ (.n (s.k + 1))) (σ (.n qpos)) (σ (.n qbp)))
    (fun d x hx => sqLoop_stepM hfind hp hb hdec hdig hpo hx) hrun
  have hmn : m = nsq := gen_pow_inj hm (by omega) hN.symm
  subst hmn
  set sqz := σ (.n (s.k + 1))
  have hchain : ∀ j ≤ m, ∃ cs d, sqAllM M j cv = some (cs, d) ∧ cs.length = j ∧
      LoadHolds rd sqz (2 * j) (digestScalars d).1 ∧ LoadHolds rd sqz (2 * j + 1) (digestScalars d).2 ∧
      ∀ i < j, MeaningDecodeQueryBits lv.depth rd [cs.getD i 0,
        σ (.n qpos) * gen ^ (lv.posOff + i * (192 / lv.depth)),
        σ (.n qbp) * gen ^ (lv.posOff + i * (192 / lv.depth))] [] := by
    intro j hj
    induction j with
    | zero =>
      refine ⟨[], cv, rfl, rfl, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      · rw [show (digestScalars cv).1 = σ (.n s.f0) from (congrArg Prod.fst hat.fs).symm]
        exact l0
      · rw [show (digestScalars cv).2 = σ (.n s.f1) from (congrArg Prod.snd hat.fs).symm]
        exact l1
    | succ j ih =>
      obtain ⟨cs, d, hcs, hlen, i0, i1, hprev⟩ := ih (by omega)
      obtain ⟨cvj, dj, b0, b1, hdj, b2, b3, hdec'⟩ := sqBodyM_at (hB j (by omega))
      obtain rfl : cvj = d := digestScalars_injective (Prod.ext (loadHolds_unique b0 i0)
        (loadHolds_unique b1 i1))
      refine ⟨cs ++ [challengeOf dj], dj, ?_, by simp [hlen], ?_, ?_, fun i hi => ?_⟩
      · rw [sqAllM_succ, hcs, Option.bind_some, hdj, Option.map_some]
      · rw [show 2 * (j + 1) = 2 * j + 2 by ring]; exact b2
      · rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring]; exact b3
      · rcases Nat.lt_or_ge i j with hij | hij
        · rw [getD_append_lt' (by omega)]; exact hprev i hij
        · obtain rfl : i = j := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
          exact hdec'
  obtain ⟨cs, cvq, hcs, -, c0, c1, hdecs⟩ := hchain m le_rfl
  rw [e8, e7, os_gw_eq (by omega), loadHolds_mul_gen_pow] at l9 l10
  have h9 := loadHolds_unique l9 (by simpa using c0)
  have h10 := loadHolds_unique l10 c1
  obtain ⟨⟨cv', dl, hcv', hdl, hv⟩, -⟩ := holdsB_squeezeT _ _ _ hsq
  obtain rfl : cv' = cvq := digestScalars_injective (by rw [← hcv', h9, h10])
  refine ⟨cs, cv', dl, hcs, hdl, ⟨?_, hat.reads, hat.cursor⟩, ?_, hdecs, trivial⟩
  · show (σ (.n (s.k + 16)), σ (.n (s.k + 17))) = _
    rw [show s.k + 16 = s.k + 11 + 5 by ring, show s.k + 17 = s.k + 11 + 6 by ring,
      hv 5 (by omega), hv 6 (by omega)]
    rfl
  · show σ (.n (s.k + 25 - 1)) = _
    rw [show s.k + 25 - 1 = s.k + 11 + 13 by omega, hv 13 (by omega)]
    rfl

end
end LeanVM.Guest.B1
