/-
  LeanVM.Guest.WalkOs0

  The cut obligations (`CutsKnown`) of `open_stacked__L0` to `open_stacked__L6`
  (`os_cutsKnown`, `WalkOsOk0.lean`'s checks).
-/

module

public import LeanVM.Guest.WalkOs
public import LeanVM.Guest.WalkOsOk0

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem walk_304 : CutsKnown 304 :=
  os_cutsKnown (m := 0) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_0 osOk_304

set_option maxRecDepth 100000 in
theorem walk_305 : CutsKnown 305 :=
  os_cutsKnown (m := 1) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_1 osOk_305

set_option maxRecDepth 100000 in
theorem walk_306 : CutsKnown 306 :=
  os_cutsKnown (m := 2) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_2 osOk_306

set_option maxRecDepth 100000 in
theorem walk_307 : CutsKnown 307 :=
  os_cutsKnown (m := 3) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_3 osOk_307

set_option maxRecDepth 100000 in
theorem walk_308 : CutsKnown 308 :=
  os_cutsKnown (m := 4) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_4 osOk_308

set_option maxRecDepth 100000 in
theorem walk_309 : CutsKnown 309 :=
  os_cutsKnown (m := 5) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_5 osOk_309

set_option maxRecDepth 100000 in
theorem walk_310 : CutsKnown 310 :=
  os_cutsKnown (m := 6) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_6 osOk_310

end
end LeanVM.Guest.End
