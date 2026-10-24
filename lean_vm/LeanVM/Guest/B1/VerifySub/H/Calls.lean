/-
  LeanVM.Guest.B1.VerifySub.H.Calls

  `verify_sub`'s frames: its thirteen calls in order, the dispatch's callee named by the candidate.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Regions

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory

@[expose] public section

/-- A call statement's frame. -/
def vcs (f : String) (args rets : List ℕ) : Option V × String × List V × List V :=
  (none, f, args.map V.n, rets.map V.n)

/-- The calls before the dispatch. -/
def vsCallsA : List (Option V × String × List V × List V) :=
  [vcs "g_power_of_word" [112] [122], vcs "g_power_of_word" [29] [130],
    vcs "log2_ceil_in_the_exponent__L0_L34" [521, 4, 5] [522],
    vcs "assert_canonical" [537] [557], vcs "assert_canonical" [547] [558],
    vcs "verify_bus_gkr" [825, 826, 827, 828, 829, 838, 522, 523] ((List.range 9).map (839 + ·)),
    vcs "verify_tables" [839, 840, 841, 842, 843, 844, 0, 1, 523, 522, 129, 28, 149, 5, 640, 836, 7,
      8, 848, 845, 846, 847] ((List.range 9).map (849 + ·)),
    vcs "verify_keccak" [849, 850, 851, 852, 853, 854, 858, 848, 862, 859, 860]
      ((List.range 8).map (863 + ·)),
    vcs "ring_switch_target" [860, 876] [1303],
    vcs "certify_placement" [141, 5] [1887, 1888, 1889],
    vcs "log2_ceil_in_the_exponent__L15_L34" [1887, 4, 5] [1890]]

/-- The dispatch's arguments and returns. -/
def vsDispArgs : List V := [.n 1312, .n 1313, .n 1314, .n 1315, .n 1316, .n 1886, .n 537, .n 547, .n 868]

/-- The calls after the dispatch. -/
def vsCallsB : List (Option V × String × List V × List V) :=
  [vcs "check_opening_terminal" [523, 848, 857, 522, 855, 130, 858, 8, 1884, 1324, 1888, 1889, 859,
    877, 1907, 1908, 1909, 1910, 1906] []]

/-- No dispatch. -/
def noDispatchB : Stmt → Bool
  | .dispatch .. => false
  | _ => true

theorem vs_split_disp : vsCPre = vsCPre.take 2097 ++
    [.dispatch (.n 1901) vsOpenNames vsDispArgs (vsRun 1906 5)] ++ vsCPre.drop 2098 := by
  have h : (vsCPre.drop 2097).take 1 = [.dispatch (.n 1901) vsOpenNames vsDispArgs (vsRun 1906 5)] :=
    (Tables.tbStmtsEqb_sound (by decide +kernel)).symm
  have e : vsCPre.drop 2097 = (vsCPre.drop 2097).take 1 ++ vsCPre.drop 2098 := by
    rw [show vsCPre.drop 2098 = (vsCPre.drop 2097).drop 1 by simp [List.drop_drop],
      List.take_append_drop]
  rw [List.append_assoc, ← h, ← e, List.take_append_drop]

theorem vs_noDisp : (vsCPre.take 2097).all noDispatchB = true ∧ (vsCPre.drop 2098).all noDispatchB = true := by
  decide +kernel

theorem vs_callsA : (vsCPre.take 2097).filterMap Stmt.callS = vsCallsA := by decide +kernel

theorem vs_callsB : (vsCPre.drop 2098).filterMap Stmt.callS = vsCallsB := by decide +kernel

theorem callSF_noDisp (σ : Val) : ∀ (l : List Stmt), l.all noDispatchB = true →
    l.filterMap (Core.Stmt.callSF σ) = l.filterMap Stmt.callS
  | [], _ => rfl
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := callSF_noDisp σ l h.2
    cases s with
    | dispatch => simp [noDispatchB] at h
    | _ => simp only [List.filterMap_cons, Core.Stmt.callSF, ih]

/-- **`verify_sub`'s frames**, the dispatch's callee named by the candidate. -/
theorem vs_calls (σ : Val) : (vsCPre.filterMap (Core.Stmt.callSF σ)).map (mkCall σ) =
    (vsCallsA ++ [(none, vsOpenNames.getD (logG (σ (.n 1901))) "", vsDispArgs, vsRun 1906 5)] ++
      vsCallsB).map (mkCall σ) := by
  rw [vs_split_disp, List.filterMap_append, List.filterMap_append,
    callSF_noDisp σ _ vs_noDisp.1, callSF_noDisp σ _ vs_noDisp.2, vs_callsA, vs_callsB]
  rfl

end
end LeanVM.Guest.B1.VerifySub
