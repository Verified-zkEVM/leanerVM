/-
  LeanVM.Guest.Located.VerifySub

  The child proof `verify_sub` checks, decoded from the memory: the frames of `open_stacked`,
  `opening_queries` and its loop, found by a scan, give the openings; `verify_sub`'s own frame the
  stream.
-/

module

public import LeanVM.Guest.Located.Da
public import LeanVM.Guest.B1.VerifySub.SoundW
public import LeanVM.Guest.B1.Whir.Stacked
public import LeanVM.Guest.B1.Whir.QueriesSpec
public import LeanVM.Guest.B1.Tables.VerifyTablesSound
public import LeanVM.Guest.B1.Tables.Gkr
public import LeanVM.Guest.B1.Tables.Flock
public import LeanVM.Guest.B1.Tables.Kappas
public import LeanVM.Guest.B1.Tables.Terminal
public import LeanVM.Guest.End

/-!
# The child proof, located

`verify_sub_sound_wC` states `verify_sub`'s child proof as `vsProofOf bytecode rd σ wO`: the
words of its `stream` buffer and the openings `open_stacked`'s witness function `wO` gives. Here
every witness function is a decoder of the memory `L` (`frameDec`, `loopDec` of
`Located/Da.lean`), each a scan along the static call graph:

* the loop helper of `opening_queries` (`wlL`), iteration by iteration: iteration `j` is the
  first frame whose opening `oqOpeningOf` passes the query's outcome at `x·g^j` (`oqIterB`);
* `opening_queries` (`wqL`), at each level of a configuration: the first frame whose openings
  `oqQueriesOs (wlL …)` have the meaning at the call's words (`QueriesTest`);
* `open_stacked__L{j}` (`wOL`): the first frame whose openings `osOsOf cfg σ (wqL …)` have
  `OpenOutW` at the call's words (`OpenTest`);
* `verify_sub` (`wVsL`): the first frame whose child proof `vsProofOf` the deferring verifier
  accepts for the call's words (`VsTest`).

The tests are decided classically: each scan is definite, no witness is chosen. `vsWit_out`: a
located call of `verify_sub` holds `Callees.verify_sub`'s claim at the decoded proof
`wVsL L args []`, for the guest's bytecode.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Value LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub

@[expose] public section

/-! ## The specializations -/

/-- `opening_queries`' 50 specializations: name, loop helper, `base, I, blocks, pd, cd`. -/
def oqTable : List (String × String × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [("opening_queries__L0_L16_L6_L14_L5", "__loop435", 0, 16, 6, 9, 5),
    ("opening_queries__L0_L16_L6_L15_L5", "__loop434", 0, 16, 6, 10, 5),
    ("opening_queries__L0_L16_L6_L16_L4", "__loop460", 0, 16, 6, 12, 4),
    ("opening_queries__L0_L16_L6_L16_L5", "__loop438", 0, 16, 6, 11, 5),
    ("opening_queries__L0_L16_L6_L16_L6", "__loop432", 0, 16, 6, 10, 6),
    ("opening_queries__L0_L16_L6_L17_L4", "__loop462", 0, 16, 6, 13, 4),
    ("opening_queries__L0_L16_L6_L17_L5", "__loop441", 0, 16, 6, 12, 5),
    ("opening_queries__L0_L16_L6_L17_L6", "__loop437", 0, 16, 6, 11, 6),
    ("opening_queries__L0_L16_L6_L18_L4", "__loop455", 0, 16, 6, 14, 4),
    ("opening_queries__L0_L16_L6_L18_L5", "__loop444", 0, 16, 6, 13, 5),
    ("opening_queries__L0_L16_L6_L18_L6", "__loop440", 0, 16, 6, 12, 6),
    ("opening_queries__L0_L16_L6_L19_L4", "__loop465", 0, 16, 6, 15, 4),
    ("opening_queries__L0_L16_L6_L19_L5", "__loop447", 0, 16, 6, 14, 5),
    ("opening_queries__L0_L16_L6_L19_L6", "__loop443", 0, 16, 6, 13, 6),
    ("opening_queries__L0_L16_L6_L20_L4", "__loop469", 0, 16, 6, 16, 4),
    ("opening_queries__L0_L16_L6_L20_L5", "__loop450", 0, 16, 6, 15, 5),
    ("opening_queries__L0_L16_L6_L20_L6", "__loop446", 0, 16, 6, 14, 6),
    ("opening_queries__L0_L16_L6_L21_L4", "__loop473", 0, 16, 6, 17, 4),
    ("opening_queries__L0_L16_L6_L21_L5", "__loop453", 0, 16, 6, 16, 5),
    ("opening_queries__L0_L16_L6_L21_L6", "__loop449", 0, 16, 6, 15, 6),
    ("opening_queries__L0_L16_L6_L22_L4", "__loop483", 0, 16, 6, 18, 4),
    ("opening_queries__L0_L16_L6_L22_L5", "__loop468", 0, 16, 6, 17, 5),
    ("opening_queries__L0_L16_L6_L22_L6", "__loop452", 0, 16, 6, 16, 6),
    ("opening_queries__L0_L16_L6_L23_L5", "__loop472", 0, 16, 6, 18, 5),
    ("opening_queries__L0_L16_L6_L23_L6", "__loop467", 0, 16, 6, 17, 6),
    ("opening_queries__L0_L16_L6_L24_L5", "__loop480", 0, 16, 6, 19, 5),
    ("opening_queries__L0_L16_L6_L24_L6", "__loop471", 0, 16, 6, 18, 6),
    ("opening_queries__L0_L16_L6_L25_L5", "__loop482", 0, 16, 6, 20, 5),
    ("opening_queries__L1_L64_L8_L17_L8", "__loop430", 1, 64, 8, 9, 8),
    ("opening_queries__L1_L64_L8_L18_L7", "__loop457", 1, 64, 8, 11, 7),
    ("opening_queries__L1_L64_L8_L18_L8", "__loop436", 1, 64, 8, 10, 8),
    ("opening_queries__L1_L64_L8_L19_L7", "__loop458", 1, 64, 8, 12, 7),
    ("opening_queries__L1_L64_L8_L19_L8", "__loop439", 1, 64, 8, 11, 8),
    ("opening_queries__L1_L64_L8_L20_L6", "__loop474", 1, 64, 8, 14, 6),
    ("opening_queries__L1_L64_L8_L20_L7", "__loop459", 1, 64, 8, 13, 7),
    ("opening_queries__L1_L64_L8_L20_L8", "__loop442", 1, 64, 8, 12, 8),
    ("opening_queries__L1_L64_L8_L21_L6", "__loop475", 1, 64, 8, 15, 6),
    ("opening_queries__L1_L64_L8_L21_L7", "__loop461", 1, 64, 8, 14, 7),
    ("opening_queries__L1_L64_L8_L21_L8", "__loop445", 1, 64, 8, 13, 8),
    ("opening_queries__L1_L64_L8_L22_L6", "__loop476", 1, 64, 8, 16, 6),
    ("opening_queries__L1_L64_L8_L22_L7", "__loop463", 1, 64, 8, 15, 7),
    ("opening_queries__L1_L64_L8_L22_L8", "__loop448", 1, 64, 8, 14, 8),
    ("opening_queries__L1_L64_L8_L23_L6", "__loop477", 1, 64, 8, 17, 6),
    ("opening_queries__L1_L64_L8_L23_L7", "__loop464", 1, 64, 8, 16, 7),
    ("opening_queries__L1_L64_L8_L23_L8", "__loop451", 1, 64, 8, 15, 8),
    ("opening_queries__L1_L64_L8_L24_L6", "__loop478", 1, 64, 8, 18, 6),
    ("opening_queries__L1_L64_L8_L24_L7", "__loop466", 1, 64, 8, 17, 7),
    ("opening_queries__L1_L64_L8_L25_L6", "__loop479", 1, 64, 8, 19, 6),
    ("opening_queries__L1_L64_L8_L25_L7", "__loop470", 1, 64, 8, 18, 7),
    ("opening_queries__L1_L64_L8_L26_L6", "__loop481", 1, 64, 8, 20, 6)]

/-- The loop helper and the shape of the specialization `name`. -/
def oqLookup (name : String) : Option (String × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (oqTable.find? fun e => e.1 == name).map (·.2)

set_option maxRecDepth 100000 in
theorem oqTable_spec : ∀ e ∈ oqTable,
    OqSpec e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 := by
  intro e he
  simp only [oqTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [oqSpec_L0_L16_L6_L14_L5, oqSpec_L0_L16_L6_L15_L5, oqSpec_L0_L16_L6_L16_L4, oqSpec_L0_L16_L6_L16_L5, oqSpec_L0_L16_L6_L16_L6, oqSpec_L0_L16_L6_L17_L4, oqSpec_L0_L16_L6_L17_L5, oqSpec_L0_L16_L6_L17_L6, oqSpec_L0_L16_L6_L18_L4, oqSpec_L0_L16_L6_L18_L5, oqSpec_L0_L16_L6_L18_L6, oqSpec_L0_L16_L6_L19_L4, oqSpec_L0_L16_L6_L19_L5, oqSpec_L0_L16_L6_L19_L6, oqSpec_L0_L16_L6_L20_L4, oqSpec_L0_L16_L6_L20_L5, oqSpec_L0_L16_L6_L20_L6, oqSpec_L0_L16_L6_L21_L4, oqSpec_L0_L16_L6_L21_L5, oqSpec_L0_L16_L6_L21_L6, oqSpec_L0_L16_L6_L22_L4, oqSpec_L0_L16_L6_L22_L5, oqSpec_L0_L16_L6_L22_L6, oqSpec_L0_L16_L6_L23_L5, oqSpec_L0_L16_L6_L23_L6, oqSpec_L0_L16_L6_L24_L5, oqSpec_L0_L16_L6_L24_L6, oqSpec_L0_L16_L6_L25_L5, oqSpec_L1_L64_L8_L17_L8, oqSpec_L1_L64_L8_L18_L7, oqSpec_L1_L64_L8_L18_L8, oqSpec_L1_L64_L8_L19_L7, oqSpec_L1_L64_L8_L19_L8, oqSpec_L1_L64_L8_L20_L6, oqSpec_L1_L64_L8_L20_L7, oqSpec_L1_L64_L8_L20_L8, oqSpec_L1_L64_L8_L21_L6, oqSpec_L1_L64_L8_L21_L7, oqSpec_L1_L64_L8_L21_L8, oqSpec_L1_L64_L8_L22_L6, oqSpec_L1_L64_L8_L22_L7, oqSpec_L1_L64_L8_L22_L8, oqSpec_L1_L64_L8_L23_L6, oqSpec_L1_L64_L8_L23_L7, oqSpec_L1_L64_L8_L23_L8, oqSpec_L1_L64_L8_L24_L6, oqSpec_L1_L64_L8_L24_L7, oqSpec_L1_L64_L8_L25_L6, oqSpec_L1_L64_L8_L25_L7, oqSpec_L1_L64_L8_L26_L6]

theorem oqLookup_spec {name loop : String} {base I blocks pd cd : ℕ}
    (h : oqLookup name = some (loop, base, I, blocks, pd, cd)) : OqSpec name loop base I blocks pd cd := by
  unfold oqLookup at h
  rcases hf : oqTable.find? (fun e => e.1 == name) with _ | e
  · rw [hf] at h; cases h
  · rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hn : e.1 = name := by simpa using List.find?_some hf
    have := oqTable_spec e (List.mem_of_find?_eq_some hf)
    rw [h, hn] at this
    exact this

/-- Level `i`'s `opening_queries` is a specialization at the level's shape. -/
def lvOk (i : ℕ) (lv : OsLvl) : Bool :=
  match oqLookup lv.queriesFn with
  | some (_, base, I, _, pd, cd) => base == (if i = 0 then 1 else 0) && I == 2 ^ lv.folds &&
      pd + cd == lv.depth && cd == lv.capDepth
  | none => false

/-- `open_stacked`'s 28 configurations, in dispatch order. -/
def osCfgs : List OsCfg := [osCfg0, osCfg1, osCfg2, osCfg3, osCfg4, osCfg5, osCfg6, osCfg7, osCfg8, osCfg9, osCfg10, osCfg11, osCfg12, osCfg13, osCfg14, osCfg15, osCfg16, osCfg17, osCfg18, osCfg19, osCfg20, osCfg21, osCfg22, osCfg23, osCfg24, osCfg25, osCfg26, osCfg27]

set_option maxRecDepth 100000 in
theorem osCfgs_lvOk : ∀ j < 28, ∀ i < (osCfgs.getD j default).levels.length,
    lvOk i ((osCfgs.getD j default).lv i) = true := by
  decide +kernel

/-- The configuration of the `open_stacked` specialization `name`. -/
def osCfgOf (name : String) : OsCfg := osCfgs.getD (openNames.idxOf name) default

theorem openNames_idxOf : ∀ j < 28, openNames.idxOf (openNames.getD j "") = j := by decide

/-- **The `open_stacked` specialization `j`**: its function, the facts of its configuration
against the ladder of its candidate, its callees' meanings. -/
structure OsInst (j : ℕ) : Prop where
  fn : ∃ fn : Fn, coreProgram.find? (openNames.getD j "") = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] ∧ fn.body = osBody (osCfgs.getD j default)
  ok : OsCfgOk (osCfgs.getD j default) (22 + j % 7) (j / 7 + 1)
    ((deriveConfig (22 + j % 7) (j / 7 + 1)).getD [])
  cal : ∀ rd, OsCallees rd (osCfgs.getD j default)

set_option maxRecDepth 100000 in
theorem os_inst : ∀ j < 28, OsInst j := by
  intro j hj
  interval_cases j
  exacts [⟨⟨_, os_find_0, rfl, os_body_0⟩, osCfgOk_0, osCallees_0⟩,
    ⟨⟨_, os_find_1, rfl, os_body_1⟩, osCfgOk_1, osCallees_1⟩,
    ⟨⟨_, os_find_2, rfl, os_body_2⟩, osCfgOk_2, osCallees_2⟩,
    ⟨⟨_, os_find_3, rfl, os_body_3⟩, osCfgOk_3, osCallees_3⟩,
    ⟨⟨_, os_find_4, rfl, os_body_4⟩, osCfgOk_4, osCallees_4⟩,
    ⟨⟨_, os_find_5, rfl, os_body_5⟩, osCfgOk_5, osCallees_5⟩,
    ⟨⟨_, os_find_6, rfl, os_body_6⟩, osCfgOk_6, osCallees_6⟩,
    ⟨⟨_, os_find_7, rfl, os_body_7⟩, osCfgOk_7, osCallees_7⟩,
    ⟨⟨_, os_find_8, rfl, os_body_8⟩, osCfgOk_8, osCallees_8⟩,
    ⟨⟨_, os_find_9, rfl, os_body_9⟩, osCfgOk_9, osCallees_9⟩,
    ⟨⟨_, os_find_10, rfl, os_body_10⟩, osCfgOk_10, osCallees_10⟩,
    ⟨⟨_, os_find_11, rfl, os_body_11⟩, osCfgOk_11, osCallees_11⟩,
    ⟨⟨_, os_find_12, rfl, os_body_12⟩, osCfgOk_12, osCallees_12⟩,
    ⟨⟨_, os_find_13, rfl, os_body_13⟩, osCfgOk_13, osCallees_13⟩,
    ⟨⟨_, os_find_14, rfl, os_body_14⟩, osCfgOk_14, osCallees_14⟩,
    ⟨⟨_, os_find_15, rfl, os_body_15⟩, osCfgOk_15, osCallees_15⟩,
    ⟨⟨_, os_find_16, rfl, os_body_16⟩, osCfgOk_16, osCallees_16⟩,
    ⟨⟨_, os_find_17, rfl, os_body_17⟩, osCfgOk_17, osCallees_17⟩,
    ⟨⟨_, os_find_18, rfl, os_body_18⟩, osCfgOk_18, osCallees_18⟩,
    ⟨⟨_, os_find_19, rfl, os_body_19⟩, osCfgOk_19, osCallees_19⟩,
    ⟨⟨_, os_find_20, rfl, os_body_20⟩, osCfgOk_20, osCallees_20⟩,
    ⟨⟨_, os_find_21, rfl, os_body_21⟩, osCfgOk_21, osCallees_21⟩,
    ⟨⟨_, os_find_22, rfl, os_body_22⟩, osCfgOk_22, osCallees_22⟩,
    ⟨⟨_, os_find_23, rfl, os_body_23⟩, osCfgOk_23, osCallees_23⟩,
    ⟨⟨_, os_find_24, rfl, os_body_24⟩, osCfgOk_24, osCallees_24⟩,
    ⟨⟨_, os_find_25, rfl, os_body_25⟩, osCfgOk_25, osCallees_25⟩,
    ⟨⟨_, os_find_26, rfl, os_body_26⟩, osCfgOk_26, osCallees_26⟩,
    ⟨⟨_, os_find_27, rfl, os_body_27⟩, osCfgOk_27, osCallees_27⟩]

/-! ## The loop helper of `opening_queries` -/

/-- The empty opening, the decoders' default. -/
local instance : Inhabited Opening := ⟨⟨[], []⟩⟩

/-- The loop's iteration outcome at `y`, its other words `ps = [N, rew, qsc, qw, qbp, flags, cap]`:
at `y = g^j`, query `j`'s opening at every position whose bits are at `qbp[j]`. -/
def oqIterB (base I pd cd : ℕ) (rd : Reader) (y : E) (ps : List E) (o : Opening) : Prop :=
  ∀ j, y = gen ^ j → ∀ q, q < 2 ^ (pd + cd) →
    (∀ dbp, LoadHolds rd (ps.getD 4 0) j dbp → BitsAt rd dbp q (pd + cd)) →
    QueryOkO base I (pd + cd) cd rd (ps.getD 1 0) (ps.getD 2 0) (ps.getD 3 0) (ps.getD 4 0)
      (ps.getD 5 0) (ps.getD 6 0) j q o

/-- **The loop's openings, decoded**: iteration `j`'s opening, `oqOpeningOf` of the first frame of
the loop whose opening passes the iteration's outcome at `x·g^j`. -/
noncomputable def wlL {κ : ℕ} (L : MemImage κ) (base I blocks pd cd : ℕ) (loop : String) :
    List E → List E → List Opening :=
  loopDec L loop (fun ps => ps.getD 0 0) (oqIterB base I pd cd L.read)
    (oqOpeningOf base I blocks pd cd L.read)

theorem wlL_spec {κ : ℕ} {L : MemImage κ} {name loop : String} {base I blocks pd cd : ℕ}
    (spec : OqSpec name loop base I blocks pd cd) :
    ∀ a, RL coreProgram L certByName loop a [] →
      OqLoopOut base I pd cd L.read a (wlL L base I blocks pd cd loop a []) := by
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
  obtain ⟨x, ps, rfl, -, hl⟩ := loopDec_spec hlf hstep h
  rw [hlp] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨-, rfl⟩ := hp
  obtain ⟨hlen, hW, hfirst, hall⟩ := hl
  unfold wlL
  generalize loopDec L loop (fun ps => ps.getD 0 0) (oqIterB base I pd cd L.read)
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

/-- `opening_queries`' outcome at the call's words `args`, `rets`, the openings `os`: for every
count `n` and positions `pos` the words allow, the meaning. -/
def QueriesTest (rd : Reader) (base I depth cd : ℕ) (args rets : List E) (os : List Opening) : Prop :=
  ∀ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E), args = [cap, flags, qw, qbp, rew, gen ^ n] →
    n < ordG → QueryBits rd qbp n depth pos →
    ∃ qsc, MeaningOpeningQueriesW base I depth cd n pos rd qsc args rets os

/-- **A specialization of `opening_queries`' openings, decoded**: those of its first frame whose
openings, its loop's decoded, have the meaning at the call's words. -/
noncomputable def wqDec {κ : ℕ} (L : MemImage κ) (name loop : String) (base I blocks pd cd : ℕ)
    (args rets : List E) : List Opening :=
  frameDec L name (fun σ => oqQueriesOs (wlL L base I blocks pd cd loop) σ)
    (QueriesTest L.read base I (pd + cd) cd args rets)

theorem wqDec_spec {κ : ℕ} {L : MemImage κ} {name loop : String} {base I blocks pd cd : ℕ}
    (spec : OqSpec name loop base I blocks pd cd) :
    SoundQueriesWC (RL coreProgram L certByName) L.read name base I (pd + cd) cd
      (wqDec L name loop base I blocks pd cd) := by
  intro n pos cap flags qw qbp rew rets hn hpre hcall
  obtain ⟨f, hf, hfp, hfb⟩ := spec.fn
  obtain ⟨a, ha, hp, hb⟩ := rl_frame hf hcall
  rw [hfp] at hp
  rw [hfb] at hb
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨e0, e1, e2, e3, e4, e5, -⟩ := hp
  have key : QueriesTest L.read base I (pd + cd) cd [cap, flags, qw, qbp, rew, gen ^ n] rets
      (wqDec L name loop base I blocks pd cd [cap, flags, qw, qbp, rew, gen ^ n] rets) := by
    unfold wqDec
    refine frameDec_spec ha fun n' pos' cap' flags' qw' qbp' rew' hargs hn' hpre' => ?_
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, hg⟩ := hargs
    obtain rfl := gen_pow_inj hn' hn hg.symm
    have hm := opening_queries_frame_w (wlL_spec spec) hn (by rw [e5]) (by rw [e3]; exact hpre) hb
    rw [e0, e1, e2, e3, e4, e5] at hm
    exact ⟨_, hm.of_pos hpre hpre'⟩
  exact key n pos cap flags qw qbp rew rfl hn hpre

/-- **Level `i`'s `opening_queries` openings, decoded**, at the specialization its name gives. -/
noncomputable def wqL {κ : ℕ} (L : MemImage κ) (cfg : OsCfg) (i : ℕ) (args rets : List E) :
    List Opening :=
  match oqLookup (cfg.lv i).queriesFn with
  | some (loop, base, I, blocks, pd, cd) =>
      wqDec L (cfg.lv i).queriesFn loop base I blocks pd cd args rets
  | none => []

theorem wqL_spec {κ : ℕ} {L : MemImage κ} {j : ℕ} (hj : j < 28) :
    OsQueriesWC (RL coreProgram L certByName) L.read (osCfgs.getD j default)
      (wqL L (osCfgs.getD j default)) := by
  intro i hi
  have hok := osCfgs_lvOk j hj i hi
  unfold lvOk at hok
  unfold wqL
  split at hok
  · rename_i loop base I blocks pd cd heq
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hb, hI⟩, hd⟩, hc⟩ := hok
    rw [← hb, ← hI, ← hd, ← hc]
    exact wqDec_spec (oqLookup_spec heq)
  · cases hok

/-! ## `open_stacked` -/

/-- `open_stacked`'s outcome at the call's words `args`, `rets`, the openings `os`, for the
specialization `name`. -/
def OpenTest (rd : Reader) (name : String) (args rets : List E) (os : List Opening) : Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 → name = openName μ r →
    ∀ (root : Digest) fs0 fs1 target root0 root1 cur, (root0, root1) = digestScalars root →
      args = [fs0, fs1, target, root0, root1, cur] → OpenOutW rd μ r root fs0 fs1 target cur rets os

/-- **`open_stacked`'s openings, decoded**: those of the first frame of the specialization
`name` whose openings, its levels' `opening_queries` decoded, have `OpenOutW` at the call's
words. -/
noncomputable def wOL {κ : ℕ} (L : MemImage κ) (name : String) (args rets : List E) : List Opening :=
  frameDec L name (fun σ => osOsOf (osCfgOf name) σ (wqL L (osCfgOf name)))
    (OpenTest L.read name args rets)

/-- **A located call of `open_stacked` holds its outcome at the decoded openings.** -/
theorem wOL_spec {κ : ℕ} (L : MemImage κ) :
    SoundOpenWC L.read (RL coreProgram L certByName) (wOL L) := by
  intro μ r h1 h2 h3 h4 root fs0 fs1 target root0 root1 cur rets hroot hcall
  have hj : μ - 22 + 7 * (r - 1) < 28 := by omega
  obtain ⟨⟨fn, hfind, hpar, hbody⟩, hok, hcal⟩ := os_inst _ hj
  have hname : openName μ r = openNames.getD (μ - 22 + 7 * (r - 1)) "" := rfl
  have hcfg : osCfgOf (openName μ r) = osCfgs.getD (μ - 22 + 7 * (r - 1)) default := by
    rw [osCfgOf, hname, openNames_idxOf _ hj]
  rw [show 22 + (μ - 22 + 7 * (r - 1)) % 7 = μ by omega,
    show (μ - 22 + 7 * (r - 1)) / 7 + 1 = r by omega] at hok
  rw [← hname] at hfind
  obtain ⟨a, ha, hp, hb⟩ := rl_frame hfind hcall
  rw [hpar] at hp
  simp only [List.map_cons, List.map_nil] at hp
  have key : OpenTest L.read (openName μ r) [fs0, fs1, target, root0, root1, cur] rets
      (wOL L (openName μ r) [fs0, fs1, target, root0, root1, cur] rets) := by
    unfold wOL
    refine frameDec_spec ha fun μ' r' g1 g2 g3 g4 hn' root' fs0' fs1' target' root0' root1' cur'
      hroot' hargs => ?_
    obtain ⟨rfl, rfl⟩ := openName_inj h1 h2 h3 h4 g1 g2 g3 g4 hn'
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
    rw [hroot] at hroot'
    obtain rfl := digestScalars_injective hroot'
    rw [hcfg]
    exact open_stacked_frame_wC (relL_le_rel coreProgram) hok (hcal L.read) (wqL_spec hj) hroot hp
      hbody hb
  exact key μ r h1 h2 h3 h4 rfl root fs0 fs1 target root0 root1 cur hroot rfl

/-! ## `verify_sub` -/

/-- `Callees.verify_sub`'s claim at the call's words `args` and the proof `π`, for `bytecode`. -/
def VsTest (bytecode : List K) (rd : Reader) (args : List E) (π : Proof) : Prop :=
  ∃ (pi iv : Digest) (fresh : FixedClaims), (args.getD 0 0, args.getD 1 0) = digestScalars pi ∧
    (args.getD 2 0, args.getD 3 0) = digestScalars iv ∧ FreshShaped fresh ∧
    ReadsAt rd (args.getD 6 0) (Node.fixedCells fresh) ∧ verifyDeferred bytecode iv pi fresh π = true

/-- The empty proof, the decoder's default. -/
local instance : Inhabited Proof := ⟨⟨[], []⟩⟩

/-- **`verify_sub`'s child proof, decoded**: `vsProofOf` of its first frame whose proof, the
openings decoded, the deferring verifier accepts for the call's words, for the guest's bytecode. -/
noncomputable def wVsL {κ : ℕ} (L : MemImage κ) (args _rets : List E) : Proof :=
  frameDec L "verify_sub" (fun σ => vsProofOf End.bytecode L.read σ (wOL L))
    (VsTest End.bytecode L.read args)

set_option maxRecDepth 100000 in
/-- **A located call of `verify_sub` holds its claim at the decoded proof**: on a memory of
`2^κ` words, `6 ≤ κ ≤ 32`, over the exponent tables, the cells are a public input and an IV, and
the deferring verifier accepts `wVsL L args []` for them with claims of the guest's shape at
`defer_out`, for the guest's bytecode. -/
theorem vsWit_out {κ : ℕ} {L : MemImage κ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ)
    {pi0 pi1 s0 s1 glp gsq out : E} (ht : ExpTables L.read glp gsq)
    (h : RL coreProgram L certByName "verify_sub" [pi0, pi1, s0, s1, glp, gsq, out] []) :
    ∃ (pi iv : Digest) (fresh : FixedClaims), (pi0, pi1) = digestScalars pi ∧
      (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧ ReadsAt L.read out (Node.fixedCells fresh) ∧
      verifyDeferred End.bytecode iv pi fresh (wVsL L [pi0, pi1, s0, s1, glp, gsq, out] []) = true := by
  obtain ⟨a, ha, hp, hb⟩ := rl_frame find_verify_sub h
  rw [core15_params] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, -⟩ := hp
  rw [core15_body, holdsList_append, holdsList_noRet _ vsPre_noRet] at hb
  have hvC : VsHoldsC (RL coreProgram L certByName) L.read (valAt L "verify_sub" a) := hb.1
  have ht' : ExpTables L.read (valAt L "verify_sub" a (.n 4)) (valAt L "verify_sub" a (.n 5)) := by
    rw [e4, e5]; exact ht
  obtain ⟨hpi, hseed, hsh, hout, hacc⟩ := verify_sub_sound_wC hκ hκ6 L (relL_le_rel coreProgram)
    End.bytecode_length (verify_bus_gkr_sound hκ L) (verify_tables_sound hκ L End.bytecode_length)
    (verify_flock_sound _) (soundPlace hκ L) (hypKappa _) (wOL_spec L)
    (check_opening_terminal_sound _) hvC ht'
  have key : VsTest End.bytecode L.read [pi0, pi1, s0, s1, glp, gsq, out]
      (wVsL L [pi0, pi1, s0, s1, glp, gsq, out] []) := by
    unfold wVsL
    refine frameDec_spec ha ⟨_, _, _, ?_, ?_, hsh, ?_, hacc⟩
    · simpa [e0, e1] using hpi
    · simpa [e2, e3] using hseed
    · simpa [e6] using hout
  obtain ⟨pi, iv, fresh, h1, h2, h3, h4, h5⟩ := key
  exact ⟨pi, iv, fresh, h1, h2, h3, h4, h5⟩

end
end LeanVM.Guest.Located
