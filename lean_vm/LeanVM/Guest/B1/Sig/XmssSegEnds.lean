/-
  LeanVM.Guest.B1.Sig.XmssSegEnds

  The ends and roots of the two layers of leanXMSS's check in `__loop2`, evaluated.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegT

/-!
# The layers' ends

`sLayer0_snd`, `sLayer1_snd`: the bottom layer ends at `107749` with its root at `74076`, the top
layer at `211051` with its root at `181713` (by kernel evaluation).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem sLayer0_snd : (sLayer 0 88 (.n 0)).2 = (107749, .n 74076) := by decide +kernel

set_option maxRecDepth 100000 in
theorem sLayer1_snd : (sLayer 1 107749 (.n 74076)).2 = (211051, .n 181713) := by decide +kernel

theorem sWin1_0 : (sWin1 0 88).2 = (107749, 74076) := by
  have h := sLayer0_snd
  simp only [sLayer] at h
  simp only [Prod.mk.injEq, V.mk.injEq, true_and] at h
  exact Prod.ext h.1 h.2

theorem sWin1_1 : (sWin1 1 107749).2 = (211051, 181713) := by
  have h := sLayer1_snd
  simp only [sLayer] at h
  simp only [Prod.mk.injEq, V.mk.injEq, true_and] at h
  exact Prod.ext h.1 h.2

end
end LeanVM.Guest.B1.Sig
