/-
  LeanVM.Guest.B1.Main.AggSoundM

  B1 for `aggregate_claims` over a hash model: the claim it stores is `Node.batchWith`'s over the
  model's hash, from the chain state of the guest's baked `AGG_SEED` cells (`AggSound.lean` over a
  `HashModel`).
-/

module

public import LeanVM.Guest.B1.Main.AggStepsM
public import LeanVM.Guest.B1.Main.BatchSpecM
public import LeanVM.Guest.B1.Main.AggSound
public import LeanVM.Guest.B1.Main.Decode
public import LeanVM.Guest.B1.Main.LoopsW

/-!
# `aggregate_claims`, soundly, over a hash model

`aggregate_claims_sound_wM` is `aggregate_claims_sound_w` over a hash model `M`: its body under
`M.sem` batches (`batchWith M.H aggSeedD`) with the hints of its valuation (`aggHints`), every
hash of the transcript, the lambdas and the two sumchecks answered by the model.

* **The start (pattern D).** The transcript starts from the chain state the guest bakes, the cells
  `AGG_SEED_0`, `AGG_SEED_1`, as a digest: `aggSeedD`. Nothing is hashed to get it; at the deployed
  model it is the label's hash (`aggSeedD_eq`, from the `decide` fact `aggSeed_eq`), the start of
  the deployed `batch` (`batchWith_some`).
* **The chain (pattern C).** Each state is the answer of the step before: the transcript row
  `c` the answered `obsAllM` of the first `c` children's cells, the lambdas the answered
  squeezes `sq2M`, `sq3M` (`BatchSpecM.lean`), the rounds `batchRoundsWith M.H` as
  `batch_sumcheck` over the model gives them (`MeaningBatchSumcheckM`, the callee's meaning over
  the model, `BatchSumcheckM` its soundness, a hypothesis here: the B1 root's
  `batch_sumcheck_L22_model`, `batch_sumcheck_L28_model`).
* The weights (`__loop97`, `__loop99`, the two `eqtree`s) and the stores hash nothing: their
  deployed facts hold under every semantics.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-! ## The start -/

/-- **The batching's start, as the guest bakes it**: the cells `AGG_SEED_0`, `AGG_SEED_1`, as a
digest (D5). -/
noncomputable def aggSeedD : Digest :=
  digestAt (word 13601591990776631179 14393745058652752134 0)
    (word 10115303172019694088 4136606974476857268 0)

/-- At the deployed hash the baked start is the label's hash (`aggSeed_eq`). -/
theorem aggSeedD_eq : aggSeedD = blake2sBytes batchLabel := digestAt_eq aggSeed_eq

/-- The baked cells are the start's. -/
theorem aggSeed_cells : (word 13601591990776631179 14393745058652752134 0,
    word 10115303172019694088 4136606974476857268 0) = digestScalars aggSeedD := by
  rw [aggSeedD_eq]; exact aggSeed_eq

/-! ## `batch_sumcheck` over a model -/

/-- **`batch_sumcheck(n)` over a hash model** (`MeaningBatchSumcheck`, every hash answered): the
rounds are `Node.batchRoundsWith` over the model's hash, answered. -/
def MeaningBatchSumcheckM (M : HashModel) (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [s0, s1, msgs, running, point], rets =>
      ∃ cv rounds rs final cv', (s0, s1) = digestScalars cv ∧ rounds.length = n ∧
        (∀ r (hr : r < rounds.length),
          LoadHolds rd msgs (2 * r) rounds[r].1 ∧ LoadHolds rd msgs (2 * r + 1) rounds[r].2) ∧
        (Node.batchRoundsWith (m := Option) M.H running rounds).run cv = some ((rs, final), cv') ∧
        ReadsAt rd point rs ∧
        rets = [(digestScalars cv').1, (digestScalars cv').2, final]
  | _, _ => False

/-- At the deployed model it is `MeaningBatchSumcheck`. -/
theorem meaningBatchSumcheckM_deployed (n : ℕ) (rd : Reader) (args rets : List E) :
    MeaningBatchSumcheckM HashModel.deployed n rd args rets ↔ MeaningBatchSumcheck n rd args rets := by
  match args, rets with
  | [s0, s1, msgs, running, point], rets =>
    have hH : HashModel.deployed.H = someBlake := rfl
    simp only [MeaningBatchSumcheckM, MeaningBatchSumcheck, hH, batchRoundsWith_some,
      Option.some.injEq]
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ | [_, _, _, _], _
  | _ :: _ :: _ :: _ :: _ :: _ :: _, _ => exact Iff.rfl

/-- **`batch_sumcheck`'s two specializations are sound over the model** on the memory `rd` (the
B1 root's `batch_sumcheck_L22_model`, `batch_sumcheck_L28_model`). -/
def BatchSumcheckM (M : HashModel) (rd : Reader) : Prop :=
  (∀ args rets, coreProgram.RelB M.sem rd "batch_sumcheck__L22" args rets →
    MeaningBatchSumcheckM M 22 rd args rets) ∧
  (∀ args rets, coreProgram.RelB M.sem rd "batch_sumcheck__L28" args rets →
    MeaningBatchSumcheckM M 28 rd args rets)

/-- At the deployed model the hypothesis is the deployed lemmas'. -/
theorem batchSumcheckM_deployed (rd : Reader) : BatchSumcheckM HashModel.deployed rd :=
  ⟨fun args rets h => (meaningBatchSumcheckM_deployed 22 rd args rets).mpr
      ((batch_sumcheck_L22_iff rd args rets).mp (by rw [← relB_deployed]; exact h)),
    fun args rets h => (meaningBatchSumcheckM_deployed 28 rd args rets).mpr
      ((batch_sumcheck_L28_iff rd args rets).mp (by rw [← relB_deployed]; exact h))⟩

/-! ## Sums -/

theorem sumE_zipWith_snoc {α β : Type} (g : α → β → E) (cs : List α) (l : List β) (x : β)
    (c : ℕ) (hc : c < cs.length) (hl : l.length = c) :
    sumE (List.zipWith g (cs.take (c + 1)) (l ++ [x])) =
      sumE (List.zipWith g (cs.take c) l) + g cs[c] x := by
  rw [List.take_add_one, List.getElem?_eq_getElem hc, Option.toList_some,
    List.zipWith_append (by simp; omega), List.zipWith_cons_cons, List.zipWith_nil_left,
    sumE_append_one]

theorem getD_snoc_lt {α : Type} {l : List α} {x d : α} {c' : ℕ} (h : c' < l.length) :
    (l ++ [x]).getD c' d = l.getD c' d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h,
    List.getElem_append_left h]

theorem getD_snoc_eq {α : Type} {l : List α} {x d : α} : (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
  simp

/-! ## The body -/

variable {M : HashModel} {rd : Reader}

/-- **`aggregate_claims`, soundly, over a hash model, on a valuation** (`aggregate_claims_sound_w`):
its body under `M.sem` on `σ` batches over the model from the baked start `aggSeedD` with the
hints of `σ` (`aggHints`), given `batch_sumcheck`'s soundness over the model. -/
theorem aggregate_claims_sound_wM (hbsM : BatchSumcheckM M rd) {σ : Val} {args rets : List E}
    (hp : (Fn.params Data.core29).map σ = args)
    (h : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ (Fn.body Data.core29) False
      (fun rs => rs = rets)) : MeaningAggWM M aggSeedD rd args rets (aggHints rd σ) := by
  rw [show Fn.params Data.core29 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl] at hp
  rw [core29_body, agBody] at h
  simp only [holdsListB_append] at h
  rw [holdsListB_noRet (fsCompressT (.n 12) (.n 13) (.n 0) 14 1) rfl,
    holdsListB_noRet (eqtreeT (.n 90) 0 (.n 96) 97) (noRetList_eqtreeT ..),
    holdsListB_noRet (eqtreeT (.n 90) 14 (.n 301) 302) (noRetList_eqtreeT ..),
    holdsListB_noRet agStores noRetList_agStores] at h
  generalize hFs : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
    (fsCompressT (.n 12) (.n 13) (.n 0) 14 1) True (fun rs => rs = rets) = Fs at h
  generalize hE1 : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
    (eqtreeT (.n 90) 0 (.n 96) 97) True (fun rs => rs = rets) = E1 at h
  generalize hE2 : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
    (eqtreeT (.n 90) 14 (.n 301) 302) True (fun rs => rs = rets) = E2 at h
  generalize hSt : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ agStores True
    (fun rs => rs = rets) = St at h
  simp only [agP1, agP2, agP3, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil,
    word_gen, word_one, word_zero] at h
  obtain ⟨-, -, -, -, -, -, -, -, c12, c13, hfs,
    c28, h29, h30, -, l26, l27, c32, h33, c34, -, hl95,
    h35, h36, h37, -, c39, h40, h41, h42, -, l44a, l44b, l45a, l45b, c46, l46, c47, h48, c49, -, hl96,
    h50, h51, h52, l53, l54, l55, -, hbs22, h60, h61, c62, h63, -, c65, l65, c66, h67, c68, -, hl97,
    h69, l70, h71, he59, h72, h73, -, c75, h76, h77, h78, -, l60, l61, c80, l80, c81, h82, c83, -, hl98,
    h84, h85, h86, l87, l88, l89, -, hbs28, h94, h95, -,
    hE1', -, hE2', c506, h507, h508, -, c510, l510, c511, l511, c512, h513, c514, -, hl99,
    h515, h516, l517, h518, l519, h520, h521, he93, hSt', hret⟩ := h
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), by rw [← hp]; rfl, hret.symm,
    fun cs hne hlen hng hCC => ?_⟩
  have hn0 : 0 < cs.length := List.length_pos_iff.mpr hne
  -- the claims at the buffers
  have hC : ∀ c (hc : c < cs.length),
      LoadHolds rd (σ (.n 1)) (2 * c) (digestScalars cs[c].publicInput).1 ∧
      LoadHolds rd (σ (.n 1)) (2 * c + 1) (digestScalars cs[c].publicInput).2 ∧
      FreshShaped cs[c].fresh ∧ ReadsAt rd (σ (.n 2) * gen ^ (106 * c)) (fixedCells cs[c].fresh) ∧
      cs[c].carried.bytecodePoint.length = 22 ∧ cs[c].carried.matrixPoint.length = 28 ∧
      ReadsAt rd (σ (.n 3) * gen ^ (53 * c)) cs[c].carried.cells := hCC
  -- the transcript's start
  have hseed0 : (σ (.n 12), σ (.n 13)) = digestScalars aggSeedD := by
    rw [c12, c13]; exact aggSeed_cells
  obtain ⟨cv0, cv1, hcv0, hd1, efs⟩ := (holdsB_fsCompressT _ _ _ _ (by decide : 1 < 256)
    (hFs ▸ hfs)).1
  obtain rfl := digestScalars_injective (hcv0.symm.trans hseed0)
  have hcv1 : (σ (.n 26), σ (.n 27)) = digestScalars cv1 := by
    rw [show 26 = 14 + 12 from rfl, show 27 = 14 + 13 from rfl, efs 12 (by omega) (by omega),
      efs 13 (by omega) (by omega)]
    rfl
  have h1 : obsCvM M aggSeedD (ofK (Parameters.gpow cs.length)) = some cv1 := by
    rw [← gen_pow_eq_ofK, ← hng]; exact hd1
  -- the transcript, child by child
  have r95 := loop_soundC (C := coreProgram.RelB M.sem rd) (f := "__loop95")
    (ps := [σ (.n 0), σ (.n 31), σ (.n 1), σ (.n 2), σ (.n 10), σ (.n 3), σ (.n 11)])
    (m := cs.length) (N := σ (.n 0)) (by unfold ordG; omega) hng (fun x hx => loop95_stepM x hx)
    (by rw [h33, c32, c34] at hl95; exact hl95)
  have hAbs : ∀ c ≤ cs.length, ∃ d, obsAllM M cv1 ((cs.take c).flatMap childCells) = some d ∧
      LoadHolds rd (σ (.n 31)) (2 * c) (digestScalars d).1 ∧
      LoadHolds rd (σ (.n 31)) (2 * c + 1) (digestScalars d).2 ∧
      ∀ c' < c, LoadHolds rd (σ (.n 10)) c' (σ (.n 2) * gen ^ (106 * c')) ∧
        LoadHolds rd (σ (.n 11)) c' (σ (.n 3) * gen ^ (53 * c')) := by
    intro c hc
    induction c with
    | zero =>
      refine ⟨cv1, rfl, ?_, ?_, fun _ h => absurd h (by omega)⟩
      · rw [show σ (.n 26) = _ from congrArg Prod.fst hcv1] at l26; simpa using l26
      · rw [show σ (.n 27) = _ from congrArg Prod.snd hcv1] at l27; simpa using l27
    | succ c ih =>
      obtain ⟨d, hd, a0, a1, arows⟩ := ih (by omega)
      obtain ⟨s0, s1, q0, q1, hall⟩ := r95 c (by omega) c rfl
      obtain ⟨p0, p1, fs, cs', w0, w1, hfl, hfr, hcl, hcr, wf, wc, d', hd', o0, o1⟩ :=
        hall _ (Prod.ext (loadHolds_unique q0 a0) (loadHolds_unique q1 a1))
      obtain ⟨g0, g1, gsh, gfr, gb, gm, gcr⟩ := hC c (by omega)
      have e0 := loadHolds_unique w0 g0
      have e1 := loadHolds_unique w1 g1
      have efs : fs = fixedCells cs[c].fresh := readsAt_unique hfr gfr (by rw [hfl, (fixedCells_getD gsh).1])
      have ecs : cs' = cs[c].carried.cells := readsAt_unique hcr gcr (by rw [hcl, (deferCells_getD gb gm).1])
      have htk : (cs.take (c + 1)).flatMap childCells =
          (cs.take c).flatMap childCells ++ p0 :: p1 :: (fs ++ cs') := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
          List.flatMap_append, List.flatMap_singleton, e0, e1, efs, ecs]
        simp [childCells]
      refine ⟨d', by rw [htk, obsAllM_append, hd, Option.bind_some, hd'],
        by rw [show 2 * (c + 1) = 2 * c + 2 by ring]; exact o0,
        by rw [show 2 * (c + 1) + 1 = 2 * c + 3 by ring]; exact o1, fun c' hc' => ?_⟩
      rcases Nat.lt_or_ge c' c with h' | h'
      · exact arows c' h'
      · rw [show c' = c by omega]; exact ⟨wf, wc⟩
  obtain ⟨cvA, hAbsA, a0, a1, hRows⟩ := hAbs cs.length le_rfl
  rw [List.take_length] at hAbsA
  -- the bytecode lambdas
  have e35 : σ (.n 35) = gen ^ (2 * cs.length) := by rw [h35, hng]; ring
  rw [h36, e35, loadHolds_mul_gen_pow, Nat.add_zero] at l44a
  rw [h36, e35, loadHolds_mul_gen_pow] at l45a
  rw [← loadHolds_unique a0 l44a] at l44b
  rw [← loadHolds_unique a1 l45a] at l45b
  rw [c46] at l46
  have r96 := loop_soundC (C := coreProgram.RelB M.sem rd) (f := "__loop96")
    (ps := [σ (.n 0), σ (.n 43), σ (.n 38), σ (.n 10), σ (.n 11)])
    (m := cs.length) (N := σ (.n 0)) (by unfold ordG; omega) hng (fun x hx => loop96_stepM x hx)
    (by rw [h48, c47, c49] at hl96; exact hl96)
  have hBC : ∀ c ≤ cs.length, ∃ (l : List (E × E)) (d : Digest), sq2M M c cvA = some (l, d) ∧
      l.length = c ∧
      LoadHolds rd (σ (.n 43)) (3 * c) (digestScalars d).1 ∧
      LoadHolds rd (σ (.n 43)) (3 * c + 1) (digestScalars d).2 ∧
      LoadHolds rd (σ (.n 43)) (3 * c + 2) (sumE (List.zipWith (fun c l ↦
        l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) (cs.take c) l)) ∧
      ∀ c' < c, LoadHolds rd (σ (.n 38)) (2 * c') (l.getD c' (0, 0)).1 ∧
        LoadHolds rd (σ (.n 38)) (2 * c' + 1) (l.getD c' (0, 0)).2 := by
    intro c hc
    induction c with
    | zero => exact ⟨[], cvA, rfl, rfl, l44b, l45b, by simpa [sumE] using l46,
        fun _ h => absurd h (by omega)⟩
    | succ c ih =>
      obtain ⟨l, d, hl, hll, b0, b1, b2, blam⟩ := ih (by omega)
      obtain ⟨s0, s1, q0, q1, hall⟩ := r96 c (by omega) c rfl
      obtain ⟨a, b, ha, hb, wl0, wl1, ws0, ws1, fp, cp, acc, fv, cv', wfp, wcp, wacc, wfv, wcv,
        wnew⟩ := hall _ (Prod.ext (loadHolds_unique q0 b0) (loadHolds_unique q1 b1))
      obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC c (by omega)
      obtain ⟨wr, wc'⟩ := hRows c (by omega)
      have efp := loadHolds_unique wfp wr
      have ecp := loadHolds_unique wcp wc'
      subst efp ecp
      have efv := loadHolds_unique wfv (readsAt_getD gfr (by rw [(fixedCells_getD gsh).1]; omega))
      have ecv := loadHolds_unique wcv (readsAt_getD gcr (by rw [(deferCells_getD gb gm).1]; omega))
      rw [(fixedCells_getD gsh).2.2.1] at efv
      rw [(deferCells_getD gb gm).2.2.1] at ecv
      have eacc := loadHolds_unique wacc b2
      refine ⟨l ++ [(challengeOf a, challengeOf b)], b, ?_, by simp [hll], ?_, ?_, ?_,
        fun c' hc' => ?_⟩
      · rw [sq2M_succ, hl, Option.bind_some, ha, Option.bind_some, hb]; rfl
      · rw [show 3 * (c + 1) = 3 * c + 3 by ring]; exact ws0
      · rw [show 3 * (c + 1) + 1 = 3 * c + 4 by ring]; exact ws1
      · rw [show 3 * (c + 1) + 2 = 3 * c + 5 by ring, sumE_zipWith_snoc _ _ _ _ _ (by omega) hll,
          ← eacc, ← efv, ← ecv, ← add_assoc]
        exact wnew
      · rcases Nat.lt_or_ge c' c with h' | h'
        · rw [getD_snoc_lt (by omega)]; exact blam c' h'
        · obtain rfl : c' = c := by omega
          rw [← hll, getD_snoc_eq, hll]; exact ⟨wl0, wl1⟩
  obtain ⟨lB, cvB', hSq2, hlB, b0, b1, b2, hLB⟩ := hBC cs.length le_rfl
  rw [List.take_length] at b2
  -- the bytecode sumcheck
  have e51 : σ (.n 51) = gen ^ (3 * cs.length) := by rw [h51, h50, hng]; ring
  rw [h52, e51, loadHolds_mul_gen_pow, Nat.add_zero] at l53
  rw [h52, e51, loadHolds_mul_gen_pow] at l54 l55
  have hbs := hbsM.1 _ _ hbs22
  obtain ⟨cvB, rounds, rs, final, cvC, hcvB, hrl, hmsg, hrun, hrs, hrets⟩ := hbs
  rw [← loadHolds_unique b0 l53, ← loadHolds_unique b1 l54] at hcvB
  have ecvB : cvB = cvB' := (digestScalars_injective hcvB).symm
  subst ecvB
  rw [← loadHolds_unique b2 l55] at hrun
  simp only [List.cons.injEq, and_true] at hrets
  obtain ⟨r57, r58, r59⟩ := hrets
  have hrsl : rs.length = 22 := by
    rw [batchRoundsWith_length _ _ _ _ _ _ hrun, hrl]
  -- the bytecode weight
  rw [c65] at l65
  have r97 := loop_soundC (C := coreProgram.RelB M.sem rd) (f := "__loop97")
    (ps := [σ (.n 0), σ (.n 10), σ (.n 11), σ (.n 56), σ (.n 64), σ (.n 38)])
    (m := cs.length) (N := σ (.n 0)) (by unfold ordG; omega) hng (fun x hx => loop97_stepB x hx)
    (by rw [h67, c66, c68] at hl97; exact hl97)
  have hW : ∀ c ≤ cs.length, LoadHolds rd (σ (.n 64)) c (sumE (List.zipWith (fun c l ↦
      l.1 * eqEval c.fresh.bytecodePoint rs + l.2 * eqEval c.carried.bytecodePoint rs)
      (cs.take c) (lB.take c))) := by
    intro c hc
    induction c with
    | zero => simpa [sumE] using l65
    | succ c ih =>
      obtain ⟨fp, cp, wfp, wcp, r, f, g, hrl', hfl, hgl, hr, hf, hg, w, lf, lc, ww, wlf, wlc, wnew⟩ :=
        r97 c (by omega) c rfl
      obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC c (by omega)
      obtain ⟨wr, wc'⟩ := hRows c (by omega)
      have efp := loadHolds_unique wfp wr
      have ecp := loadHolds_unique wcp wc'
      subst efp ecp
      have er : r = rs := readsAt_unique hr hrs (by rw [hrl', hrsl])
      have ef : f = cs[c].fresh.bytecodePoint := readsAt_eq_of_getD hf gfr hfl gsh.1
        (by rw [(fixedCells_getD gsh).1]; omega) (fixedCells_getD gsh).2.1
      have eg : g = cs[c].carried.bytecodePoint := readsAt_eq_of_getD hg gcr hgl gb
        (by rw [(deferCells_getD gb gm).1]; omega) (deferCells_getD gb gm).2.1
      obtain ⟨l0, l1⟩ := hLB c (by omega)
      rw [loadHolds_unique wlf l0, loadHolds_unique wlc l1, loadHolds_unique ww (ih (by omega)),
        er, ef, eg] at wnew
      rw [sumE_zipWith_take_succ _ _ _ _ (by omega) (by omega), ← List.getD_eq_getElem _ (0, 0)
        (by omega), ← add_assoc]
      exact wnew
  have hWn := hW cs.length le_rfl
  rw [List.take_length, show lB.take cs.length = lB by rw [← hlB, List.take_length]] at hWn
  rw [h69, hng, loadHolds_mul_gen_pow, Nat.add_zero] at l70
  have hbcF : final = σ (.n 7) * sumE (List.zipWith (fun c l ↦
      l.1 * eqEval c.fresh.bytecodePoint rs + l.2 * eqEval c.carried.bytecodePoint rs) cs lB) := by
    rw [← r59, e_add_eq_zero_iff.mp he59, h71, loadHolds_unique l70 hWn]
  -- the matrix lambdas
  rw [h60, r57] at l60
  rw [h61, r58] at l61
  rw [c80] at l80
  have r98 := loop_soundC (C := coreProgram.RelB M.sem rd) (f := "__loop98")
    (ps := [σ (.n 0), σ (.n 79), σ (.n 74), σ (.n 10), σ (.n 11)])
    (m := cs.length) (N := σ (.n 0)) (by unfold ordG; omega) hng (fun x hx => loop98_stepM x hx)
    (by rw [h82, c81, c83] at hl98; exact hl98)
  have hMC : ∀ c ≤ cs.length, ∃ (l : List (E × E × E)) (d : Digest), sq3M M c cvC = some (l, d) ∧
      l.length = c ∧
      LoadHolds rd (σ (.n 79)) (3 * c) (digestScalars d).1 ∧
      LoadHolds rd (σ (.n 79)) (3 * c + 1) (digestScalars d).2 ∧
      LoadHolds rd (σ (.n 79)) (3 * c + 2) (sumE (List.zipWith (fun c l ↦
        l.1 * c.fresh.matrixValue + l.2.1 * c.carried.matrixA + l.2.2 * c.carried.matrixB)
        (cs.take c) l)) ∧
      ∀ c' < c, LoadHolds rd (σ (.n 74)) (3 * c') (l.getD c' (0, 0, 0)).1 ∧
        LoadHolds rd (σ (.n 74)) (3 * c' + 1) (l.getD c' (0, 0, 0)).2.1 ∧
        LoadHolds rd (σ (.n 74)) (3 * c' + 2) (l.getD c' (0, 0, 0)).2.2 := by
    intro c hc
    induction c with
    | zero => exact ⟨[], cvC, rfl, rfl, l60, l61, by simpa [sumE] using l80,
        fun _ h => absurd h (by omega)⟩
    | succ c ih =>
      obtain ⟨l, d, hl, hll, b0, b1, b2, blam⟩ := ih (by omega)
      obtain ⟨s0, s1, q0, q1, hall⟩ := r98 c (by omega) c rfl
      obtain ⟨a, b, e, ha, hb, he, wl0, wl1, wl2, ws0, ws1, fp, cp, acc, fv, ca, cb, wfp, wcp, wacc,
        wfv, wca, wcb, wnew⟩ := hall _ (Prod.ext (loadHolds_unique q0 b0) (loadHolds_unique q1 b1))
      obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC c (by omega)
      obtain ⟨wr, wc'⟩ := hRows c (by omega)
      have efp := loadHolds_unique wfp wr
      have ecp := loadHolds_unique wcp wc'
      subst efp ecp
      have efv := loadHolds_unique wfv (readsAt_getD gfr (by rw [(fixedCells_getD gsh).1]; omega))
      have eca := loadHolds_unique wca (readsAt_getD gcr (by rw [(deferCells_getD gb gm).1]; omega))
      have ecb := loadHolds_unique wcb (readsAt_getD gcr (by rw [(deferCells_getD gb gm).1]; omega))
      rw [(fixedCells_getD gsh).2.2.2.2.2.2.2.2] at efv
      rw [(deferCells_getD gb gm).2.2.2.2.1] at eca
      rw [(deferCells_getD gb gm).2.2.2.2.2] at ecb
      have eacc := loadHolds_unique wacc b2
      refine ⟨l ++ [(challengeOf a, challengeOf b, challengeOf e)], e, ?_, by simp [hll], ?_, ?_,
        ?_, fun c' hc' => ?_⟩
      · rw [sq3M_succ, hl, Option.bind_some, ha, Option.bind_some, hb, Option.bind_some, he]; rfl
      · rw [show 3 * (c + 1) = 3 * c + 3 by ring]; exact ws0
      · rw [show 3 * (c + 1) + 1 = 3 * c + 4 by ring]; exact ws1
      · rw [show 3 * (c + 1) + 2 = 3 * c + 5 by ring, sumE_zipWith_snoc _ _ _ _ _ (by omega) hll,
          ← eacc, ← efv, ← eca, ← ecb, ← add_assoc, ← add_assoc]
        exact wnew
      · rcases Nat.lt_or_ge c' c with h' | h'
        · rw [getD_snoc_lt (by omega)]; exact blam c' h'
        · obtain rfl : c' = c := by omega
          rw [← hll, getD_snoc_eq, hll]; exact ⟨wl0, wl1, wl2⟩
  obtain ⟨lM, cvD', hCm, hlM, m0, m1, m2, hLM⟩ := hMC cs.length le_rfl
  rw [List.take_length] at m2
  -- the matrix sumcheck
  have e85 : σ (.n 85) = gen ^ (3 * cs.length) := by rw [h85, h84, hng]; ring
  rw [h86, e85, loadHolds_mul_gen_pow, Nat.add_zero] at l87
  rw [h86, e85, loadHolds_mul_gen_pow] at l88 l89
  have hbsMt := hbsM.2 _ _ hbs28
  obtain ⟨cvD, roundsM, rM, finalM, cvE, hcvD, hrlM, hmsgM, hrunM, hrM, hretsM⟩ := hbsMt
  rw [← loadHolds_unique m0 l87, ← loadHolds_unique m1 l88] at hcvD
  have ecvD : cvD = cvD' := (digestScalars_injective hcvD).symm
  subst ecvD
  rw [← loadHolds_unique m2 l89] at hrunM
  simp only [List.cons.injEq, and_true] at hretsM
  obtain ⟨-, -, r93⟩ := hretsM
  have hrMl : rM.length = 28 := by
    rw [batchRoundsWith_length _ _ _ _ _ _ hrunM, hrlM]
  -- the two `eqtree`s: the equality kernels of the matrix point's row and column halves
  obtain ⟨hR1, hK1⟩ := eqtree_sound (.n 90) (.n 96) 0 97 _
    ((holdsListB_noCall (by decide +kernel) _ _).mp (hE1 ▸ hE1'))
  obtain ⟨hR2, hK2⟩ := eqtree_sound (.n 90) (.n 301) 14 302 _
    ((holdsListB_noCall (by decide +kernel) _ _).mp (hE2 ▸ hE2'))
  have eR1 : etRs σ 97 = rM.take 6 := by
    apply List.ext_getElem (by rw [length_etRs, List.length_take, hrMl]; rfl)
    intro t h1 h2
    rw [length_etRs] at h1
    have a := hR1 t h1
    rw [Nat.zero_add, List.getD_eq_getElem _ _ (by rw [length_etRs]; exact h1)] at a
    rw [loadHolds_unique a (hrM t (by omega)), List.getElem_take]
  have eR2 : etRs σ 302 = (rM.drop 14).take 6 := by
    apply List.ext_getElem (by rw [length_etRs, List.length_take, List.length_drop, hrMl]; rfl)
    intro t h1 h2
    rw [length_etRs] at h1
    have a := hR2 t h1
    rw [List.getD_eq_getElem _ _ (by rw [length_etRs]; exact h1)] at a
    rw [loadHolds_unique a (hrM (14 + t) (by omega)), List.getElem_take, List.getElem_drop]
  have cEqR : ∀ i < 64, cellAt rd (σ (.n 96)) (62 + i) = (eqKernel (rM.take 6)).getD i 0 :=
    fun i hi => by rw [← eR1]; exact cellAt_of_load (hK1 i hi)
  have cEqC : ∀ i < 64, cellAt rd (σ (.n 301)) (62 + i) = (eqKernel ((rM.drop 14).take 6)).getD i 0 :=
    fun i hi => by rw [← eR2]; exact cellAt_of_load (hK2 i hi)
  have cMp : ∀ k < 28, cellAt rd (σ (.n 90)) k = rM.getD k 0 := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact cellAt_of_load (hrM k (by omega))
  -- the matrix weights, child by child
  rw [c510] at l510
  rw [c511] at l511
  have r99 := loop_soundC (C := coreProgram.RelB M.sem rd) (f := "__loop99")
    (ps := [σ (.n 0), σ (.n 10), σ (.n 96), σ (.n 90), σ (.n 301), σ (.n 11), σ (.n 74), σ (.n 509)])
    (m := cs.length) (N := σ (.n 0)) (by unfold ordG; omega) hng (fun x hx => loop99_stepB x hx)
    (by rw [h513, c512, c514] at hl99; exact hl99)
  have hWS : ∀ c ≤ cs.length,
      LoadHolds rd (σ (.n 509)) (2 * c) (sumE (List.zipWith (fun c l ↦
        l.1 * freshWeight c.fresh rM + l.2.1 * eqEval c.carried.matrixPoint rM)
        (cs.take c) (lM.take c))) ∧
      LoadHolds rd (σ (.n 509)) (2 * c + 1) (sumE (List.zipWith (fun c l ↦
        l.1 * c.fresh.alpha * freshWeight c.fresh rM + l.2.2 * eqEval c.carried.matrixPoint rM)
        (cs.take c) (lM.take c))) := by
    intro c hc
    induction c with
    | zero => exact ⟨by simpa [sumE] using l510, by simpa [sumE] using l511⟩
    | succ c ih =>
      obtain ⟨w0, w1⟩ := ih (by omega)
      obtain ⟨fp, cp, wfp, wcp, wn0, wn1⟩ := r99 c (by omega) c rfl
      obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC c (by omega)
      obtain ⟨wr, wc'⟩ := hRows c (by omega)
      have efp := loadHolds_unique wfp wr
      have ecp := loadHolds_unique wcp wc'
      subst efp ecp
      have cF : ∀ k < 106, cellAt rd (σ (.n 2) * gen ^ (106 * c)) k =
          (fixedCells cs[c].fresh).getD k 0 :=
        fun k hk => cellAt_of_load (readsAt_getD gfr (by rw [(fixedCells_getD gsh).1]; exact hk))
      have cC : ∀ k < 53, cellAt rd (σ (.n 3) * gen ^ (53 * c)) k = cs[c].carried.cells.getD k 0 :=
        fun k hk => cellAt_of_load (readsAt_getD gcr (by rw [(deferCells_getD gb gm).1]; exact hk))
      have hP : ∏ k ∈ Finset.range 28, (1 + cellAt rd (σ (.n 3) * gen ^ (53 * c)) (23 + k) +
          cellAt rd (σ (.n 90)) k) = eqEval cs[c].carried.matrixPoint rM := by
        rw [eqEval_prod _ _ 28 gm hrMl]
        exact Finset.prod_congr rfl fun k hk => by
          have := Finset.mem_range.mp hk
          rw [cC (23 + k) (by omega), (deferCells_getD gb gm).2.2.2.1 k this, cMp k this]
      have hU := guestU_congr (cF 24 (by omega)) (fun k hk => cF (25 + k) (by omega))
        (fun j hj => cF (33 + j) (by omega)) (fun i hi => cF (41 + i) (by omega)) cEqR cEqC cMp
      rw [guestU_eq gsh hrMl] at hU
      obtain ⟨l0, l1, l2⟩ := hLM c (by omega)
      rw [hU, hP, cellAt_of_load w0, cellAt_of_load l0, cellAt_of_load l1] at wn0
      rw [hU, hP, cellAt_of_load w1, cellAt_of_load l0, cellAt_of_load l2, cF 23 (by omega),
        (fixedCells_getD gsh).2.2.2.1] at wn1
      refine ⟨?_, ?_⟩
      · rw [show 2 * (c + 1) = 2 * c + 2 by ring, sumE_zipWith_take_succ _ _ _ _ (by omega)
          (by omega), ← List.getD_eq_getElem _ (0, 0, 0) (by omega), ← add_assoc]
        exact wn0
      · rw [show 2 * (c + 1) + 1 = 2 * c + 3 by ring, sumE_zipWith_take_succ _ _ _ _ (by omega)
          (by omega), ← List.getD_eq_getElem _ (0, 0, 0) (by omega), ← add_assoc]
        exact wn1
  obtain ⟨n0, n1⟩ := hWS cs.length le_rfl
  rw [List.take_length, show lM.take cs.length = lM by rw [← hlM, List.take_length]] at n0 n1
  -- the final check
  have e515 : σ (.n 515) = gen ^ (2 * cs.length) := by rw [h515, hng]; ring
  rw [h516, e515, loadHolds_mul_gen_pow, Nat.add_zero] at l517
  rw [h516, e515, loadHolds_mul_gen_pow] at l519
  have hmF : finalM = σ (.n 8) * sumE (List.zipWith (fun c l ↦
        l.1 * freshWeight c.fresh rM + l.2.1 * eqEval c.carried.matrixPoint rM) cs lM) +
      σ (.n 9) * sumE (List.zipWith (fun c l ↦
        l.1 * c.fresh.alpha * freshWeight c.fresh rM + l.2.2 * eqEval c.carried.matrixPoint rM)
        cs lM) := by
    rw [← r93, e_add_eq_zero_iff.mp he93, h521, h518, h520, loadHolds_unique l517 n0,
      loadHolds_unique l519 n1]
  -- the stores
  have hSt2 := hSt ▸ hSt'
  rw [agStores] at hSt2
  simp only [holdsListB_append] at hSt2
  rw [holdsListB_range_flatten 22 (fun k => [Stmt.atom (.load (.n (522 + k)) (.n 56) k),
      .atom (.load (.n (522 + k)) (.n 4) k)]) (fun _ => rfl),
    holdsListB_range_flatten 28 (fun k => [Stmt.atom (.load (.n (544 + k)) (.n 90) k),
      .atom (.load (.n (544 + k)) (.n 4) (23 + k))]) (fun _ => rfl)] at hSt2
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB] at hSt2
  obtain ⟨hA, l7, hB, l8, l9, -⟩ := hSt2
  have hD : ReadsAt rd (σ (.n 4)) (⟨rs, σ (.n 7), rM, σ (.n 8), σ (.n 9)⟩ : DeferredClaim).cells := by
    obtain ⟨dl, d1, d2, d3, d4, d5⟩ :=
      deferCells_getD (d := ⟨rs, σ (.n 7), rM, σ (.n 8), σ (.n 9)⟩) hrsl hrMl
    intro k hk
    rw [← List.getD_eq_getElem _ 0 hk]
    rw [dl] at hk
    rcases Nat.lt_or_ge k 22 with h1 | h1
    · obtain ⟨a, b, -⟩ := hA k h1
      rw [d1 k h1]
      show LoadHolds rd _ k (rs.getD k 0)
      rw [List.getD_eq_getElem _ _ (by omega), ← loadHolds_unique a (hrs k (by omega))]
      exact b
    rcases Nat.lt_or_ge k 23 with h2 | h2
    · rw [show k = 22 by omega, d2]; exact l7
    rcases Nat.lt_or_ge k 51 with h3 | h3
    · obtain ⟨a, b, -⟩ := hB (k - 23) (by omega)
      rw [show k = 23 + (k - 23) by omega, d3 _ (by omega)]
      show LoadHolds rd _ _ (rM.getD (k - 23) 0)
      rw [List.getD_eq_getElem _ _ (by omega), ← loadHolds_unique a (hrM (k - 23) (by omega))]
      exact b
    rcases Nat.lt_or_ge k 52 with h4 | h4
    · rw [show k = 51 by omega, d4]; exact l8
    · rw [show k = 52 by omega, d5]; exact l9
  -- the batching
  have eH : aggHints rd σ = ⟨rounds, roundsM, σ (.n 7), σ (.n 8), σ (.n 9)⟩ := by
    rw [aggHints, rounds_of_msgs hrl hmsg, rounds_of_msgs hrlM hmsgM]
  refine ⟨⟨rs, σ (.n 7), rM, σ (.n 8), σ (.n 9)⟩, ?_, hrsl, hrMl, hD⟩
  rw [eH]
  exact batchWith_of h1 hAbsA hSq2 hrun hCm hrunM hbcF hmF

end
end LeanVM.Guest.B1.Main
