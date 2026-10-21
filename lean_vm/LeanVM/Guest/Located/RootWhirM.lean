/-
  LeanVM.Guest.Located.RootWhirM

  The B1 root's and the Whir group's fields of `GuestHypsM`: `batch_sumcheck` and the located
  calls of `open_stacked` over a hash model, at the decoded openings.
-/

module

public import LeanVM.Guest.Located.InterfaceM
public import LeanVM.Guest.B1.Whir.StackedM

/-!
# `batch_sumcheck` and `open_stacked`, located, over a hash model

* `batchSumcheckM_model`: `Main.BatchSumcheckM` (`GuestHypsM.batch_sumcheck`), from
  `batch_sumcheck_L22_model`, `batch_sumcheck_L28_model` (`MeaningBatchSumcheckM` is
  `MeaningBatchSumcheckWith`, `meaningBatchSumcheckM_iff`).
* `openStacked_model`: `SoundOpenWCM … (wOLB M.sem fr L)` (`GuestHypsM.open_stacked`), `wOL_spec`
  (`Located/VerifySub.lean`) over the model's semantics: the decoders under `M.sem` (`wlLB`,
  `wqDecB`, `wqLB`, `wOLB`) read the frames whose bodies the Whir lemmas over the model take
  (`oqFrame_soundM`, `oqOpeningOf_okM`, `opening_queries_frame_wM`, `open_stacked_frame_wCM`), and
  the configurations' callees are their model forms (`osCalleesM_…`).
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Value LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub

@[expose] public section

/-! ## `batch_sumcheck` -/

/-- `Main.MeaningBatchSumcheckM` is the B1 root's `MeaningBatchSumcheckWith`. -/
theorem meaningBatchSumcheckM_iff (M : HashModel) (n : ℕ) (rd : Reader) (args rets : List E) :
    Main.MeaningBatchSumcheckM M n rd args rets ↔ MeaningBatchSumcheckWith M n rd args rets := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, l⟩⟩⟩⟩⟩⟩ <;>
    simp only [Main.MeaningBatchSumcheckM, MeaningBatchSumcheckWith]

/-- **`GuestHypsM.batch_sumcheck`**: `batch_sumcheck__L22`, `__L28` are sound over the model. -/
theorem batchSumcheckM_model (M : HashModel) : ∀ rd, Main.MemOk rd → Main.BatchSumcheckM M rd :=
  fun rd _ => ⟨fun args rets h => (meaningBatchSumcheckM_iff M 22 rd args rets).mpr
      (batch_sumcheck_L22_model rd args rets h),
    fun args rets h => (meaningBatchSumcheckM_iff M 28 rd args rets).mpr
      (batch_sumcheck_L28_model rd args rets h)⟩

/-! ## The loop helper of `opening_queries` -/

/-- The empty opening, the decoders' default. -/
local instance : Inhabited Opening := ⟨⟨[], []⟩⟩

variable {M : HashModel} {fr : String → List E → Option ℕ}

/-- The loop's iteration outcome over a hash model at `y` (`oqIterB`). -/
def oqIterBM (M : HashModel) (base I pd cd : ℕ) (rd : Reader) (y : E) (ps : List E) (o : Opening) : Prop :=
  ∀ j, y = gen ^ j → ∀ q, q < 2 ^ (pd + cd) →
    (∀ dbp, LoadHolds rd (ps.getD 4 0) j dbp → BitsAt rd dbp q (pd + cd)) →
    QueryOkM M base I (pd + cd) cd rd (ps.getD 1 0) (ps.getD 2 0) (ps.getD 3 0) (ps.getD 4 0)
      (ps.getD 5 0) (ps.getD 6 0) j q o

theorem wlLB_spec {κ : ℕ} {L : MemImage κ} {name loop : String} {base I blocks pd cd : ℕ}
    (spec : OqSpec name loop base I blocks pd cd) :
    ∀ a, RLB M.sem coreProgram L certByName loop a [] →
      OqLoopOutM M base I pd cd L.read a (wlLB M.sem fr L base I blocks pd cd loop a []) := by
  intro a h
  obtain ⟨lf, hlf, hlp, hlb⟩ := spec.loopFn
  have hstep : ∀ C : CallRel, CallRel.Le C (RLB M.sem coreProgram L certByName) →
      ∀ (σ : Val) (args rets : List E), lf.params.map σ = args →
      Stmt.HoldsListB M.sem C L.read σ lf.body False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧
        oqIterBM M base I pd cd L.read x ps (oqOpeningOf base I blocks pd cd L.read σ) ∧
        (x * gen ≠ ps.getD 0 0 → C loop (x * gen :: ps) []) := by
    intro C _ σ args rets hp hb
    rw [hlp] at hp
    rw [hlb] at hb
    obtain ⟨hx, -, hcall, hk⟩ := oqFrame_soundM spec.shape hb
    simp only [List.map_cons, List.map_nil] at hp
    subst hp
    refine ⟨σ (.n 0), [σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)], rfl,
      hk.symm, fun j hj q hq hb' => oqOpeningOf_okM spec.shape hq hj hb' hx, fun hne => ?_⟩
    exact hcall fun h0 => hne (e_add_eq_zero_iff.mp h0)
  obtain ⟨a0, -, hp, -⟩ := rl_frameB hlf h
  obtain ⟨x, ps, rfl, -, hl⟩ := loopDecB_spec hlf hstep h
  rw [hlp] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨-, rfl⟩ := hp
  obtain ⟨hlen, hW, hfirst, hall⟩ := hl
  unfold wlLB
  generalize loopDecB M.sem fr L loop (fun ps => ps.getD 0 0)
    (oqOpeningOf base I blocks pd cd L.read) _ [] = os at hlen hW hfirst hall ⊢
  intro k hk
  have hWg : ∀ t, x * gen ^ t = gen ^ (k + t) := fun t => by rw [hk, pow_add]
  refine ⟨k + os.length, by omega, by simp only [List.getD_cons_zero] at hW; rw [hW, hWg], ?_,
    by omega, ?_⟩
  · intro j h1 h2
    obtain ⟨t, rfl⟩ : ∃ t, j = k + t := ⟨j - k, by omega⟩
    rw [← hWg]
    have := hfirst t (by omega) (by omega)
    simpa only [List.getD_cons_zero] using this
  · intro j h1 h2 q hq hb
    obtain ⟨t, rfl⟩ : ∃ t, j = k + t := ⟨j - k, by omega⟩
    have hj : t < os.length := by omega
    rw [Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hj]
    exact hall t hj (k + t) (hWg t) q hq hb

/-! ## `opening_queries` -/

/-- `opening_queries`' outcome over a hash model at the call's words (`QueriesTest`). -/
def QueriesTestM (M : HashModel) (rd : Reader) (base I depth cd : ℕ) (args rets : List E)
    (os : List Opening) : Prop :=
  ∀ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E), args = [cap, flags, qw, qbp, rew, gen ^ n] →
    n < ordG → QueryBits rd qbp n depth pos →
    ∃ qsc, MeaningOpeningQueriesWM M base I depth cd n pos rd qsc args rets os

theorem wqDecB_spec {κ : ℕ} {L : MemImage κ} {name loop : String} {base I blocks pd cd : ℕ}
    (spec : OqSpec name loop base I blocks pd cd) :
    SoundQueriesWCM M (RLB M.sem coreProgram L certByName) L.read name base I (pd + cd) cd
      (wqDecB M.sem fr L name loop base I blocks pd cd) := by
  intro n pos cap flags qw qbp rew rets hn hpre hcall
  obtain ⟨f, hf, hfp, hfb⟩ := spec.fn
  have key : QueriesTestM M L.read base I (pd + cd) cd [cap, flags, qw, qbp, rew, gen ^ n] rets
      (wqDecB M.sem fr L name loop base I blocks pd cd [cap, flags, qw, qbp, rew, gen ^ n] rets) := by
    unfold wqDecB
    refine frameDecB_spec hf hcall fun a hp hb => ?_
    rw [hfp] at hp
    rw [hfb] at hb
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
    obtain ⟨e0, e1, e2, e3, e4, e5, -⟩ := hp
    intro n' pos' cap' flags' qw' qbp' rew' hargs hn' hpre'
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, hg⟩ := hargs
    obtain rfl := gen_pow_inj hn' hn hg.symm
    have hm := opening_queries_frame_wM (wlLB_spec (fr := fr) spec) hn (by rw [e5]) (by rw [e3]; exact hpre) hb
    rw [e0, e1, e2, e3, e4, e5] at hm
    exact ⟨_, hm.of_pos hpre hpre'⟩
  exact key n pos cap flags qw qbp rew rfl hn hpre

theorem wqLB_spec {κ : ℕ} {L : MemImage κ} {j : ℕ} (hj : j < 28) :
    OsQueriesWCM M (RLB M.sem coreProgram L certByName) L.read (osCfgs.getD j default)
      (wqLB M.sem fr L (osCfgs.getD j default)) := by
  intro i hi
  have hok := osCfgs_lvOk j hj i hi
  unfold lvOk at hok
  rcases hq : oqLookup ((osCfgs.getD j default).lv i).queriesFn with _ | ⟨loop, base, I, blocks, pd, cd⟩
  · rw [hq] at hok; cases hok
  · rw [hq] at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hb, hI⟩, hd⟩, hc⟩ := hok
    have hw : wqLB M.sem fr L (osCfgs.getD j default) i =
        wqDecB M.sem fr L ((osCfgs.getD j default).lv i).queriesFn loop base I blocks pd cd := by
      funext a r
      simp only [wqLB, hq]
    rw [hw, ← hb, ← hI, ← hd, ← hc]
    exact wqDecB_spec (oqLookup_spec hq)

/-! ## `open_stacked` -/

/-- **The `open_stacked` specialization `j` over a hash model**: its function, the facts of its
configuration, its callees' meanings over every model (`OsInst` with `OsCalleesM`). -/
structure OsInstM (j : ℕ) : Prop where
  fn : ∃ fn : Fn, coreProgram.find? (openNames.getD j "") = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] ∧ fn.body = osBody (osCfgs.getD j default)
  ok : OsCfgOk (osCfgs.getD j default) (22 + j % 7) (j / 7 + 1)
    ((deriveConfig (22 + j % 7) (j / 7 + 1)).getD [])
  cal : ∀ M rd, OsCalleesM M rd (osCfgs.getD j default)

set_option maxRecDepth 100000 in
theorem os_instM : ∀ j < 28, OsInstM j := by
  intro j hj
  interval_cases j
  exacts [
    ⟨⟨_, os_find_0, rfl, os_body_0⟩, osCfgOk_0, osCalleesM_0⟩,
    ⟨⟨_, os_find_1, rfl, os_body_1⟩, osCfgOk_1, osCalleesM_1⟩,
    ⟨⟨_, os_find_2, rfl, os_body_2⟩, osCfgOk_2, osCalleesM_2⟩,
    ⟨⟨_, os_find_3, rfl, os_body_3⟩, osCfgOk_3, osCalleesM_3⟩,
    ⟨⟨_, os_find_4, rfl, os_body_4⟩, osCfgOk_4, osCalleesM_4⟩,
    ⟨⟨_, os_find_5, rfl, os_body_5⟩, osCfgOk_5, osCalleesM_5⟩,
    ⟨⟨_, os_find_6, rfl, os_body_6⟩, osCfgOk_6, osCalleesM_6⟩,
    ⟨⟨_, os_find_7, rfl, os_body_7⟩, osCfgOk_7, osCalleesM_7⟩,
    ⟨⟨_, os_find_8, rfl, os_body_8⟩, osCfgOk_8, osCalleesM_8⟩,
    ⟨⟨_, os_find_9, rfl, os_body_9⟩, osCfgOk_9, osCalleesM_9⟩,
    ⟨⟨_, os_find_10, rfl, os_body_10⟩, osCfgOk_10, osCalleesM_10⟩,
    ⟨⟨_, os_find_11, rfl, os_body_11⟩, osCfgOk_11, osCalleesM_11⟩,
    ⟨⟨_, os_find_12, rfl, os_body_12⟩, osCfgOk_12, osCalleesM_12⟩,
    ⟨⟨_, os_find_13, rfl, os_body_13⟩, osCfgOk_13, osCalleesM_13⟩,
    ⟨⟨_, os_find_14, rfl, os_body_14⟩, osCfgOk_14, osCalleesM_14⟩,
    ⟨⟨_, os_find_15, rfl, os_body_15⟩, osCfgOk_15, osCalleesM_15⟩,
    ⟨⟨_, os_find_16, rfl, os_body_16⟩, osCfgOk_16, osCalleesM_16⟩,
    ⟨⟨_, os_find_17, rfl, os_body_17⟩, osCfgOk_17, osCalleesM_17⟩,
    ⟨⟨_, os_find_18, rfl, os_body_18⟩, osCfgOk_18, osCalleesM_18⟩,
    ⟨⟨_, os_find_19, rfl, os_body_19⟩, osCfgOk_19, osCalleesM_19⟩,
    ⟨⟨_, os_find_20, rfl, os_body_20⟩, osCfgOk_20, osCalleesM_20⟩,
    ⟨⟨_, os_find_21, rfl, os_body_21⟩, osCfgOk_21, osCalleesM_21⟩,
    ⟨⟨_, os_find_22, rfl, os_body_22⟩, osCfgOk_22, osCalleesM_22⟩,
    ⟨⟨_, os_find_23, rfl, os_body_23⟩, osCfgOk_23, osCalleesM_23⟩,
    ⟨⟨_, os_find_24, rfl, os_body_24⟩, osCfgOk_24, osCalleesM_24⟩,
    ⟨⟨_, os_find_25, rfl, os_body_25⟩, osCfgOk_25, osCalleesM_25⟩,
    ⟨⟨_, os_find_26, rfl, os_body_26⟩, osCfgOk_26, osCalleesM_26⟩,
    ⟨⟨_, os_find_27, rfl, os_body_27⟩, osCfgOk_27, osCalleesM_27⟩]

/-- `open_stacked`'s outcome over a hash model at the call's words (`OpenTest`). -/
def OpenTestM (M : HashModel) (rd : Reader) (name : String) (args rets : List E) (os : List Opening) :
    Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 → name = openName μ r →
    ∀ (root : Digest) fs0 fs1 target root0 root1 cur, (root0, root1) = digestScalars root →
      args = [fs0, fs1, target, root0, root1, cur] → OpenOutWM M rd μ r root fs0 fs1 target cur rets os

/-- **`GuestHypsM.open_stacked`: a located call of `open_stacked` under the model's semantics
holds its outcome over the model at the openings decoded at any named frames `fr`** (`wOL_spec`
over a hash model). -/
theorem openStacked_model (M : HashModel) (fr : String → List E → Option ℕ) {κ : ℕ} (L : MemImage κ) (_ : 16 ≤ κ) (_ : κ ≤ 32) :
    SoundOpenWCM M L.read (RLB M.sem coreProgram L certByName) (wOLB M.sem fr L) := by
  intro μ r h1 h2 h3 h4 root fs0 fs1 target root0 root1 cur rets hroot hcall
  have hj : μ - 22 + 7 * (r - 1) < 28 := by omega
  obtain ⟨⟨fn, hfind, hpar, hbody⟩, hok, hcal⟩ := os_instM _ hj
  have hname : openName μ r = openNames.getD (μ - 22 + 7 * (r - 1)) "" := rfl
  have hcfg : osCfgOf (openName μ r) = osCfgs.getD (μ - 22 + 7 * (r - 1)) default := by
    rw [osCfgOf, hname, openNames_idxOf _ hj]
  rw [show 22 + (μ - 22 + 7 * (r - 1)) % 7 = μ by omega,
    show (μ - 22 + 7 * (r - 1)) / 7 + 1 = r by omega] at hok
  rw [← hname] at hfind
  have key : OpenTestM M L.read (openName μ r) [fs0, fs1, target, root0, root1, cur] rets
      (wOLB M.sem fr L (openName μ r) [fs0, fs1, target, root0, root1, cur] rets) := by
    unfold wOLB
    refine frameDecB_spec hfind hcall fun a hp hb => ?_
    rw [hpar] at hp
    simp only [List.map_cons, List.map_nil] at hp
    intro μ' r' g1 g2 g3 g4 hn' root' fs0' fs1' target' root0' root1' cur' hroot' hargs
    obtain ⟨rfl, rfl⟩ := openName_inj h1 h2 h3 h4 g1 g2 g3 g4 hn'
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
    rw [hroot] at hroot'
    obtain rfl := digestScalars_injective hroot'
    rw [hcfg]
    exact open_stacked_frame_wCM (relLB_le_rel coreProgram) hok (hcal M L.read) (wqLB_spec hj) hroot hp
      hbody hb
  exact key μ r h1 h2 h3 h4 rfl root fs0 fs1 target root0 root1 cur hroot rfl

end
end LeanVM.Guest.Located
