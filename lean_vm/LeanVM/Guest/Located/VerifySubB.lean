/-
  LeanVM.Guest.Located.VerifySubB

  The child proof `verify_sub` checks, decoded from the memory under any semantics of `BLAKE2S`,
  and accepted over a hash model (`Located/VerifySub.lean` over `S` and a `HashModel`).
-/

module

public import LeanVM.Guest.Located.DaB
public import LeanVM.Guest.Located.VerifySub
public import LeanVM.Guest.B1.VerifySub.SoundWM

/-!
# The child proof, located, under any semantics

`Located/VerifySub.lean`'s decoders with the frames under `S` at the named frames `fr`
(`frameDecB S fr`, `loopDecB S fr`, decision E2E-5): `wlLB`, `wqDecB`, `wqLB`, `wOLB` (the stacked
openings) and `wVsLB` (the child proof), each the deployed one at `blakeDeployed` with no frame
named (`wOLB_deployed`, `wVsLB_deployed`). At the deployed semantics the stacked openings hold
`open_stacked`'s outcome at every `fr` (`wOLB_spec_deployed`: `wOL_spec`'s proof at the decoded
frames, each holding its callee's code).

`vsWit_outM`: a located call of `verify_sub` under the model's semantics accepts the decoded proof
over the model (`verifyDeferredWith M.H … = some true`), by `verify_sub_sound_wCM`, given the
hashing callees' soundness over the model: GKR, the tables and Flock (`SoundGkrM`,
`SoundTablesM`, `SoundFlockM`, the Tables group's), and `open_stacked` at the decoded openings
(`SoundOpenWCM … (wOLB M.sem fr L)`, the B1 root's: the deployed `wOL_spec` over the model, from the
model forms of `oqFrame_sound`, `oqOpeningOf_ok`, `opening_queries_frame_w` and
`open_stacked_frame_wC`). The hash-free callees (placement, kappas, the terminal) are the deployed
lemmas.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Value LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The empty opening, the decoders' default. -/
local instance : Inhabited Opening := ⟨⟨[], []⟩⟩

variable (S : BlakeSem) (fr : String → List E → Option ℕ)

/-- The loop's openings, decoded under `S` (`wlL`). -/
noncomputable def wlLB {κ : ℕ} (L : MemImage κ) (base I blocks pd cd : ℕ) (loop : String) :
    List E → List E → List Opening :=
  loopDecB S fr L loop (fun ps => ps.getD 0 0) (oqOpeningOf base I blocks pd cd L.read)

/-- A specialization of `opening_queries`' openings, decoded under `S` (`wqDec`). -/
noncomputable def wqDecB {κ : ℕ} (L : MemImage κ) (name loop : String) (base I blocks pd cd : ℕ)
    (args rets : List E) : List Opening :=
  frameDecB S fr L name (fun σ => oqQueriesOs (wlLB S fr L base I blocks pd cd loop) σ) args rets

/-- Level `i`'s `opening_queries` openings, decoded under `S` (`wqL`). -/
noncomputable def wqLB {κ : ℕ} (L : MemImage κ) (cfg : OsCfg) (i : ℕ) (args rets : List E) :
    List Opening :=
  match oqLookup (cfg.lv i).queriesFn with
  | some (loop, base, I, blocks, pd, cd) =>
      wqDecB S fr L (cfg.lv i).queriesFn loop base I blocks pd cd args rets
  | none => []

/-- **`open_stacked`'s openings, decoded under `S`** (`wOL`). -/
noncomputable def wOLB {κ : ℕ} (L : MemImage κ) (name : String) (args rets : List E) :
    List Opening :=
  frameDecB S fr L name (fun σ => osOsOf (osCfgOf name) σ (wqLB S fr L (osCfgOf name))) args rets

/-- **`verify_sub`'s child proof, decoded under `S`** (`wVsL`). -/
noncomputable def wVsLB {κ : ℕ} (L : MemImage κ) (args rets : List E) : Proof :=
  frameDecB S fr L "verify_sub" (fun σ => vsProofOf End.bytecode L.read σ (wOLB S fr L)) args rets

variable {S fr}

/-! ## At the deployed semantics -/

theorem wOLB_deployed {κ : ℕ} (L : MemImage κ) : wOLB blakeDeployed (fun _ _ ↦ none) L = wOL L := by
  have hl : wlLB blakeDeployed (fun _ _ ↦ none) L = wlL L := by
    funext base I blocks pd cd loop
    simp only [wlLB, wlL, loopDecB_deployed]
  have hq : wqDecB blakeDeployed (fun _ _ ↦ none) L = wqDec L := by
    funext name loop base I blocks pd cd args rets
    simp only [wqDecB, wqDec, frameDecB_deployed, hl]
  have hqL : wqLB blakeDeployed (fun _ _ ↦ none) L = wqL L := by
    funext cfg i args rets
    unfold wqLB wqL
    rw [hq]
    split <;> rename_i h <;> rw [h]
  funext name args rets
  simp only [wOLB, wOL, frameDecB_deployed, hqL]

theorem wVsLB_deployed {κ : ℕ} (L : MemImage κ) : wVsLB blakeDeployed (fun _ _ ↦ none) L = wVsL L := by
  funext args rets
  simp only [wVsLB, wVsL, frameDecB_deployed, wOLB_deployed]

/-! ## At the deployed semantics, at any named frames

`wOL_spec`'s proof (`Located/VerifySub.lean`) at the frames `fr` names: it uses only that every
decoded frame holds its callee's code (`frameDecB_spec_deployed`, `loopDecB_spec_deployed`). -/

section Deployed

variable {fr : String → List E → Option ℕ}

/-- The loop of `opening_queries`, at the named frames (`wlL_spec`). -/
theorem wlLB_spec_deployed {κ : ℕ} {L : MemImage κ} {name loop : String} {base I blocks pd cd : ℕ}
    (spec : OqSpec name loop base I blocks pd cd) :
    ∀ a, RL coreProgram L certByName loop a [] →
      OqLoopOut base I pd cd L.read a (wlLB blakeDeployed fr L base I blocks pd cd loop a []) := by
  intro a h
  obtain ⟨lf, hlf, hlp, hlb⟩ := spec.loopFn
  have hstep : ∀ C : CallRel, CallRel.Le C (RL coreProgram L certByName) →
      ∀ (σ : Val) (args rets : List E), lf.params.map σ = args →
      Stmt.HoldsList C L.read σ lf.body False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧
        oqIterB base I pd cd L.read x ps (oqOpeningOf base I blocks pd cd L.read σ) ∧
        (x * gen ≠ ps.getD 0 0 → C loop (x * gen :: ps) []) := by
    intro C _ σ args rets hp hb
    rw [hlp] at hp
    rw [hlb] at hb
    obtain ⟨hx, -, hcall, hk⟩ := oqFrame_sound spec.shape hb
    simp only [List.map_cons, List.map_nil] at hp
    subst hp
    refine ⟨σ (.n 0), [σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)], rfl,
      hk.symm, fun j hj q hq hb' => oqOpeningOf_ok spec.shape hq hj hb' hx, fun hne => ?_⟩
    exact hcall fun h0 => hne (e_add_eq_zero_iff.mp h0)
  obtain ⟨a0, -, hp, -⟩ := rl_frame hlf h
  obtain ⟨x, ps, rfl, -, hl⟩ := loopDecB_spec_deployed hlf hstep h
  rw [hlp] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨-, rfl⟩ := hp
  obtain ⟨hlen, hW, hfirst, hall⟩ := hl
  unfold wlLB
  generalize loopDecB blakeDeployed fr L loop (fun ps => ps.getD 0 0)
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

/-- A specialization of `opening_queries`, at the named frames (`wqDec_spec`). -/
theorem wqDecB_spec_deployed {κ : ℕ} {L : MemImage κ} {name loop : String} {base I blocks pd cd : ℕ}
    (spec : OqSpec name loop base I blocks pd cd) :
    SoundQueriesWC (RL coreProgram L certByName) L.read name base I (pd + cd) cd
      (wqDecB blakeDeployed fr L name loop base I blocks pd cd) := by
  intro n pos cap flags qw qbp rew rets hn hpre hcall
  obtain ⟨f, hf, hfp, hfb⟩ := spec.fn
  have key : QueriesTest L.read base I (pd + cd) cd [cap, flags, qw, qbp, rew, gen ^ n] rets
      (wqDecB blakeDeployed fr L name loop base I blocks pd cd [cap, flags, qw, qbp, rew, gen ^ n]
        rets) := by
    unfold wqDecB
    refine frameDecB_spec_deployed hf hcall fun a hp hb => ?_
    rw [hfp] at hp
    rw [hfb] at hb
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
    obtain ⟨e0, e1, e2, e3, e4, e5, -⟩ := hp
    intro n' pos' cap' flags' qw' qbp' rew' hargs hn' hpre'
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, hg⟩ := hargs
    obtain rfl := gen_pow_inj hn' hn hg.symm
    have hm := opening_queries_frame_w (wlLB_spec_deployed (fr := fr) spec) hn (by rw [e5])
      (by rw [e3]; exact hpre) hb
    rw [e0, e1, e2, e3, e4, e5] at hm
    exact ⟨_, hm.of_pos hpre hpre'⟩
  exact key n pos cap flags qw qbp rew rfl hn hpre

/-- The levels' `opening_queries`, at the named frames (`wqL_spec`). -/
theorem wqLB_spec_deployed {κ : ℕ} {L : MemImage κ} {j : ℕ} (hj : j < 28) :
    OsQueriesWC (RL coreProgram L certByName) L.read (osCfgs.getD j default)
      (wqLB blakeDeployed fr L (osCfgs.getD j default)) := by
  intro i hi
  have hok := osCfgs_lvOk j hj i hi
  unfold lvOk at hok
  unfold wqLB
  rcases heq : oqLookup ((osCfgs.getD j default).lv i).queriesFn with _ | ⟨loop, base, I, blocks, pd, cd⟩
  · rw [heq] at hok
    cases hok
  · rw [heq] at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hb, hI⟩, hd⟩, hc⟩ := hok
    rw [← hb, ← hI, ← hd, ← hc]
    exact wqDecB_spec_deployed (fr := fr) (oqLookup_spec heq)

/-- **A located call of `open_stacked` holds its outcome at the openings decoded at the named
frames** (`wOL_spec`, at the deployed semantics and any `fr`). -/
theorem wOLB_spec_deployed {κ : ℕ} (L : MemImage κ) :
    SoundOpenWC L.read (RL coreProgram L certByName) (wOLB blakeDeployed fr L) := by
  intro μ r h1 h2 h3 h4 root fs0 fs1 target root0 root1 cur rets hroot hcall
  have hj : μ - 22 + 7 * (r - 1) < 28 := by omega
  obtain ⟨⟨fn, hfind, hpar, hbody⟩, hok, hcal⟩ := os_inst _ hj
  have hname : openName μ r = openNames.getD (μ - 22 + 7 * (r - 1)) "" := rfl
  have hcfg : osCfgOf (openName μ r) = osCfgs.getD (μ - 22 + 7 * (r - 1)) default := by
    rw [osCfgOf, hname, openNames_idxOf _ hj]
  rw [show 22 + (μ - 22 + 7 * (r - 1)) % 7 = μ by omega,
    show (μ - 22 + 7 * (r - 1)) / 7 + 1 = r by omega] at hok
  rw [← hname] at hfind
  have key : OpenTest L.read (openName μ r) [fs0, fs1, target, root0, root1, cur] rets
      (wOLB blakeDeployed fr L (openName μ r) [fs0, fs1, target, root0, root1, cur] rets) := by
    unfold wOLB
    refine frameDecB_spec_deployed hfind hcall fun a hp hb => ?_
    rw [hpar] at hp
    simp only [List.map_cons, List.map_nil] at hp
    intro μ' r' g1 g2 g3 g4 hn' root' fs0' fs1' target' root0' root1' cur' hroot' hargs
    obtain ⟨rfl, rfl⟩ := openName_inj h1 h2 h3 h4 g1 g2 g3 g4 hn'
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
    rw [hroot] at hroot'
    obtain rfl := digestScalars_injective hroot'
    rw [hcfg]
    exact open_stacked_frame_wC (relL_le_rel coreProgram) hok (hcal L.read) (wqLB_spec_deployed (fr := fr) hj)
      hroot hp hbody hb
  exact key μ r h1 h2 h3 h4 rfl root fs0 fs1 target root0 root1 cur hroot rfl

end Deployed

/-! ## Over a hash model -/

variable {M : HashModel}

set_option maxRecDepth 100000 in
/-- **A located call of `verify_sub` under the model's semantics accepts the decoded proof over the
model** (`vsWit_out`): on a memory of `2^κ` words, `6 ≤ κ ≤ 32`, over the exponent tables, given
the hashing callees' soundness over the model (GKR, the tables with the terminal's context, Flock,
and `open_stacked` at the decoded openings), the cells are a public input and an IV, and the
deferring verifier accepts `wVsLB M.sem fr L args []` for them over the model with claims of the
guest's shape at `defer_out`. -/
theorem vsWit_outM {κ : ℕ} {L : MemImage κ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ)
    (hgkr : SoundGkrM M L.read) (htab : SoundTablesM M End.bytecode TCtx L.read)
    (hfl : SoundFlockM M L.read)
    (hop : SoundOpenWCM M L.read (RLB M.sem coreProgram L certByName) (wOLB M.sem fr L))
    {pi0 pi1 s0 s1 glp gsq out : E} (ht : ExpTables L.read glp gsq)
    (h : RLB M.sem coreProgram L certByName "verify_sub" [pi0, pi1, s0, s1, glp, gsq, out] []) :
    ∃ (pi iv : Digest) (fresh : FixedClaims), (pi0, pi1) = digestScalars pi ∧
      (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧ ReadsAt L.read out (Node.fixedCells fresh) ∧
      verifyDeferredWith M.H End.bytecode iv pi fresh
        (wVsLB M.sem fr L [pi0, pi1, s0, s1, glp, gsq, out] []) = some true := by
  have key : ∃ (pi iv : Digest) (fresh : FixedClaims), (pi0, pi1) = digestScalars pi ∧
      (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧ ReadsAt L.read out (Node.fixedCells fresh) ∧
      verifyDeferredWith M.H End.bytecode iv pi fresh
        (wVsLB M.sem fr L [pi0, pi1, s0, s1, glp, gsq, out] []) = some true := by
    unfold wVsLB
    refine frameDecB_spec (t := fun π => ∃ (pi iv : Digest) (fresh : FixedClaims),
      (pi0, pi1) = digestScalars pi ∧ (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧
      ReadsAt L.read out (Node.fixedCells fresh) ∧
      verifyDeferredWith M.H End.bytecode iv pi fresh π = some true) find_verify_sub h
      fun a hp hb => ?_
    rw [core15_params] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, -⟩ := hp
    rw [core15_body, holdsListB_append, holdsListB_noRet _ vsPre_noRet] at hb
    have hvC : VsHoldsCB M.sem (RLB M.sem coreProgram L certByName) L.read (valAt L "verify_sub" a) :=
      hb.1
    have ht' : ExpTables L.read (valAt L "verify_sub" a (.n 4)) (valAt L "verify_sub" a (.n 5)) := by
      rw [e4, e5]; exact ht
    obtain ⟨hpi, hseed, hsh, hout, hacc⟩ := verify_sub_sound_wCM hκ hκ6 L (relLB_le_rel coreProgram)
      End.bytecode_length hgkr htab hfl (soundPlace hκ L) (hypKappa _) hop
      (check_opening_terminal_sound _) hvC ht'
    refine ⟨_, _, _, ?_, ?_, hsh, ?_, hacc⟩
    · rw [← e0, ← e1]; exact hpi
    · rw [← e2, ← e3]; exact hseed
    · rw [← e6]; exact hout
  exact key

end
end LeanVM.Guest.Located
