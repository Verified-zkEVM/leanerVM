/-
  LeanVM.Guest.B1.Whir.StackedM

  `open_stacked` is sound at every candidate under a hash model: `SoundOpenM`.
-/

module

public import LeanVM.Guest.B1.Whir.StackedInstM0
public import LeanVM.Guest.B1.Whir.StackedInstM1
public import LeanVM.Guest.B1.Whir.StackedInstM2
public import LeanVM.Guest.B1.Whir.StackedInstM3

/-!
# `open_stacked` (TRIAGE #36) under a hash model: `SoundOpenM`

At every candidate `22 ≤ μ ≤ 28`, `1 ≤ r ≤ 4`, the specialization `openName μ r` is
`open_stacked__L{(μ - 22) + 7·(r - 1)}`, sound under the model by `open_stacked_L…_model`. At
`HashModel.deployed` this is `soundOpen` (`VerifySub.soundOpenM_deployed`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- **`open_stacked` is sound under a hash model** at every candidate (`SoundOpenM`). -/
theorem soundOpenM (M : HashModel) (rd : Reader) : SoundOpenM M rd := by
  intro μ r h1 h2 h3 h4 root fs0 fs1 target root0 root1 cur rets hroot h
  interval_cases μ <;> interval_cases r
  · exact open_stacked_L0_model hroot h
  · exact open_stacked_L7_model hroot h
  · exact open_stacked_L14_model hroot h
  · exact open_stacked_L21_model hroot h
  · exact open_stacked_L1_model hroot h
  · exact open_stacked_L8_model hroot h
  · exact open_stacked_L15_model hroot h
  · exact open_stacked_L22_model hroot h
  · exact open_stacked_L2_model hroot h
  · exact open_stacked_L9_model hroot h
  · exact open_stacked_L16_model hroot h
  · exact open_stacked_L23_model hroot h
  · exact open_stacked_L3_model hroot h
  · exact open_stacked_L10_model hroot h
  · exact open_stacked_L17_model hroot h
  · exact open_stacked_L24_model hroot h
  · exact open_stacked_L4_model hroot h
  · exact open_stacked_L11_model hroot h
  · exact open_stacked_L18_model hroot h
  · exact open_stacked_L25_model hroot h
  · exact open_stacked_L5_model hroot h
  · exact open_stacked_L12_model hroot h
  · exact open_stacked_L19_model hroot h
  · exact open_stacked_L26_model hroot h
  · exact open_stacked_L6_model hroot h
  · exact open_stacked_L13_model hroot h
  · exact open_stacked_L20_model hroot h
  · exact open_stacked_L27_model hroot h

end
end LeanVM.Guest.B1
