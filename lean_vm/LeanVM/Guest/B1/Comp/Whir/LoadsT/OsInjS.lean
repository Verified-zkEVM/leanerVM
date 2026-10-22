/-
  LeanVM.Guest.B1.Comp.Whir.LoadsT.OsInjS

  The instance-injectivity clause of the stacked opening (`OsInj`) and the static facts its proof
  rests on, checked by kernel evaluation: the functions `open_stacked`'s other callees reach, the
  levels' `opening_queries` calls, the loop helpers' bodies.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LoadsT.OsStreamL
public import LeanVM.Guest.B1.Comp.Whir.LoadsT.OsInjZ
public import LeanVM.Guest.B2C.Defs

/-!
# `OsInj` and its static facts

`OsInj fp t`: within the call tree `t` of an `open_stacked` instance at `fp`, every instance of an
`opening_queries` specialization or of its loop helper (`osInjNames`) has an argument pointing into
`t`'s region, and two such instances of the same function on the same arguments are the same
instance (one frame pointer).

Static facts, by kernel evaluation:

* `osInjZ` (`OsInjZ.lean`): the functions the other callees reach, closed under calls;
* `OsICfg cfg`, for each of the 28 configurations (`osI_cfg`): the body's calls of `osInjNames`
  are the levels' `opening_queries` calls (`osQCalls`), its other calls call `osInjZ`;
* `osI_oqLoop`: each loop helper's body before its `ret` is straight, allocates nothing and calls
  only itself, at `x·g`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Located LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The argument of a function of `osInjNames` pointing into the opening's region: `rew_l` (the
fifth) for an `opening_queries` specialization, its query sums' buffer (the fourth) for a loop
helper. -/
def osPtrIdx (f : String) : ℕ := if f ∈ oqTable.map (·.1) then 4 else 3

/-- **Instance injectivity in the stacked opening's tree `t` at `fp`**: every instance of a
function of `osInjNames` has its argument `osPtrIdx` a pointer `g^a` into `t`'s region, and is the
only instance of its function on its arguments. -/
def OsInj (fp : ℕ) (t : Memory.Tree) : Prop :=
  fp + t.total B2C.fs ≤ 2 ^ 32 →
  ∀ (H : Inst → ℕ → E × E) (hdr : E × E), ∀ I ∈ t.insts B2C.fs coreProgram.loop H fp hdr, ∀ j,
    B2C.idxOf I.t.name = some j → I.t.name ∈ osInjNames →
    (∃ a, ((coreOf j).params.map I.t.val)[osPtrIdx I.t.name]? = some (ofK (Parameters.gpow a)) ∧ fp ≤ a ∧
      a < fp + t.total B2C.fs) ∧
    ∀ I' ∈ t.insts B2C.fs coreProgram.loop H fp hdr, I'.t.name = I.t.name →
      (coreOf j).params.map I'.t.val = (coreOf j).params.map I.t.val → I'.fp = I.fp

/-! ## The levels' `opening_queries` calls -/

/-- The state a level's queries start from. -/
def osQIn (cfg : OsCfg) (lvl : ℕ) (lv : OsLvl) (s : OsSt) : OsSt :=
  let f := osFolds osFch lv.foldsOff lv.folds s
  let m := if lvl = cfg.yrLevel then osFinal cfg.finalMsg osFmsg f.2
    else osCommit lvl lv.logCols lv.oodNext osRoots osOodz osOod f.2
  let gr := osGrind lv.grindBits m.2
  let sq := osSqueezes cfg.maxSq lv.squeezes osQpos osQbp lv.sqLoop gr.2
  { sq.2 with k := sq.2.k + lv.queries }

/-- The `opening_queries` call of the level's queries from `s`. -/
def osQCallOf (cfg : OsCfg) (lv : OsLvl) (lvl : ℕ) (s : OsSt) : Option V × String × List V × List V :=
  let k := s.k
  let p := osMat osFch lv.foldsOff (k + 2)
  let cp := osMat osCaps (4 * lv.capOff) p.2.2
  let fp := osMat osFlags lv.capOff cp.2.2
  let r := fp.2.2
  let cp2 := osMat osCaps (4 * lv.capOff) (r + 2)
  let fp2 := osMat osFlags lv.capOff cp2.2.2
  let qp := osMat osQw (lvl * cfg.maxQ) fp2.2.2
  let bp := osMat osQbp lv.posOff qp.2.2
  let g := bp.2.2
  (none, lv.queriesFn, [.n cp2.2.1, .n fp2.2.1, .n qp.2.1, .n bp.2.1, .n (k + 1), .n g], [.n (g + 1)])

/-- The levels' `opening_queries` calls from level `lvl`. -/
def osQCalls (cfg : OsCfg) : ℕ → List OsLvl → OsSt → List (Option V × String × List V × List V)
  | _, [], _ => []
  | lvl, lv :: rest, s =>
    osQCallOf cfg lv lvl (osQIn cfg lvl lv s) :: osQCalls cfg (lvl + 1) rest (osLevel cfg lvl lv s).2

/-- **A configuration's calls**: those of `osInjNames` are the levels' queries, the others call
`osInjZ`; the queries' weights fit. -/
structure OsICfg (cfg : OsCfg) : Prop where
  filt : ((osBody cfg).dropLast.filterMap Main.Stmt.callS).filter (fun c => osInjNames.contains c.2.1) =
    osQCalls cfg 0 cfg.levels (osHead cfg).2
  cal : ((osBody cfg).dropLast.filterMap Main.Stmt.callS).all
    (fun c => osInjZ.contains c.2.1 || osInjNames.contains c.2.1) = true
  mq : 0 < cfg.maxQ ∧ cfg.levels.length * cfg.maxQ < 2 ^ 32

set_option maxRecDepth 100000 in
theorem osI_cfg0 : OsICfg osCfg0 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg1 : OsICfg osCfg1 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg2 : OsICfg osCfg2 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg3 : OsICfg osCfg3 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg4 : OsICfg osCfg4 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg5 : OsICfg osCfg5 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg6 : OsICfg osCfg6 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg7 : OsICfg osCfg7 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg8 : OsICfg osCfg8 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg9 : OsICfg osCfg9 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg10 : OsICfg osCfg10 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg11 : OsICfg osCfg11 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg12 : OsICfg osCfg12 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg13 : OsICfg osCfg13 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg14 : OsICfg osCfg14 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg15 : OsICfg osCfg15 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg16 : OsICfg osCfg16 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg17 : OsICfg osCfg17 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg18 : OsICfg osCfg18 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg19 : OsICfg osCfg19 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg20 : OsICfg osCfg20 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg21 : OsICfg osCfg21 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg22 : OsICfg osCfg22 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg23 : OsICfg osCfg23 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg24 : OsICfg osCfg24 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg25 : OsICfg osCfg25 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg26 : OsICfg osCfg26 := ⟨by decide +kernel, by decide +kernel, by decide⟩

set_option maxRecDepth 100000 in
theorem osI_cfg27 : OsICfg osCfg27 := ⟨by decide +kernel, by decide +kernel, by decide⟩

/-- **The 28 configurations' calls.** -/
theorem osI_cfg (j : ℕ) (hj : j < 28) : OsICfg (osCfgs.getD j default) := by
  interval_cases j
  exacts [osI_cfg0, osI_cfg1, osI_cfg2, osI_cfg3, osI_cfg4, osI_cfg5, osI_cfg6, osI_cfg7, osI_cfg8,
    osI_cfg9, osI_cfg10, osI_cfg11, osI_cfg12, osI_cfg13, osI_cfg14, osI_cfg15, osI_cfg16, osI_cfg17,
    osI_cfg18, osI_cfg19, osI_cfg20, osI_cfg21, osI_cfg22, osI_cfg23, osI_cfg24, osI_cfg25, osI_cfg26,
    osI_cfg27]

set_option maxRecDepth 100000 in
/-- `open_stacked`'s specializations are no loop helpers. -/
theorem osI_loop : ∀ j < 28, coreProgram.loop (openNames.getD j "") = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem osI_openNames : ∀ j < 28, openNames.getD j "" ∉ osInjNames := by decide +kernel

/-! ## The specializations -/

set_option maxRecDepth 100000 in
/-- **Each loop helper's body before its `ret`**: straight, no `HeapBuf`, one call, to itself at
`x·g`. -/
theorem osI_oqLoop : ∀ e ∈ oqTable,
    (oqLoopPre e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 e.2.1).all Main.Stmt.straight = true ∧
    (oqLoopPre e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 e.2.1).filterMap Main.Stmt.allocSz = [] ∧
    (oqLoopPre e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 e.2.1).filterMap Main.Stmt.callS =
      [(some (.n (oqK7 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 + 17)), e.2.1,
        [.n (oqK7 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 + 19), .n 1, .n 2, .n 3, .n 4, .n 5,
          .n 6, .n 7], [])] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A statement found in a block by `stmtsEqb`. -/
theorem osI_mem_of_any {l : List Stmt} {x : Stmt} (h : l.any (fun s => stmtsEqb [s] [x]) = true) : x ∈ l := by
  obtain ⟨s, hs, he⟩ := List.any_eq_true.mp h
  have := stmtsEqb_sound he
  simp only [List.cons.injEq, and_true] at this
  exact this ▸ hs

set_option maxRecDepth 100000 in
/-- The tail call's argument `x·g` in each loop helper's body. -/
theorem osI_oqLoop_atoms : ∀ e ∈ oqTable,
    (oqLoopPre e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 e.2.1).any (fun s => stmtsEqb [s]
      [.atom (.const (.n (oqK7 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 + 18)) (word 2 0 0))]) = true ∧
    (oqLoopPre e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 e.2.1).any (fun s => stmtsEqb [s]
      [.atom (.mul (.n (oqK7 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 + 19)) (.n 0)
        (.n (oqK7 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 + 18)))]) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The specializations' names are no loop helpers', and a loop helper has one specialization. -/
theorem osI_oqNames : ∀ e ∈ oqTable, ∀ e' ∈ oqTable, e.1 ≠ e'.2.1 ∧ (e.2.1 = e'.2.1 → e.1 = e'.1) := by
  decide +kernel

end
end LeanVM.Guest.B1
