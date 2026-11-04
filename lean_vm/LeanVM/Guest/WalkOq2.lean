/-
  LeanVM.Guest.WalkOq2

  The cut obligations (`CutsKnown`) of a quarter of `opening_queries`' specializations and loops,
  from their templates (`B1/Opening/QueriesBody2.lean`), the generic forms (`WalkKnown.lean`) and
  their certificates' checks (`WalkOqOk2.lean`).
-/

module

public import LeanVM.Guest.WalkKnown
public import LeanVM.Guest.WalkOqOk2
public import LeanVM.Guest.B1.Opening.QueriesBody2

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

set_option maxRecDepth 100000 in
theorem walk_456 : CutsKnown 456 :=
  main_cutsKnown (j := 456) oqBody_433 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_456

set_option maxRecDepth 100000 in
theorem walk_475 : CutsKnown 475 :=
  main_cutsKnown (j := 475) oqBody_452 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_475

set_option maxRecDepth 100000 in
theorem walk_478 : CutsKnown 478 :=
  main_cutsKnown (j := 478) oqBody_455 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_478

set_option maxRecDepth 100000 in
theorem walk_510 : CutsKnown 510 :=
  main_cutsKnown (j := 510) oqBody_487 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_510

set_option maxRecDepth 100000 in
theorem walk_540 : CutsKnown 540 :=
  main_cutsKnown (j := 540) oqBody_517 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_540

set_option maxRecDepth 100000 in
theorem walk_542 : CutsKnown 542 :=
  main_cutsKnown (j := 542) oqBody_519 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_542

set_option maxRecDepth 100000 in
theorem walk_574 : CutsKnown 574 :=
  main_cutsKnown (j := 574) oqBody_551 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_574

set_option maxRecDepth 100000 in
theorem walk_579 : CutsKnown 579 :=
  main_cutsKnown (j := 579) oqBody_556 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_579

set_option maxRecDepth 100000 in
theorem walk_609 : CutsKnown 609 :=
  main_cutsKnown (j := 609) oqBody_586 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_609

set_option maxRecDepth 100000 in
theorem walk_628 : CutsKnown 628 :=
  main_cutsKnown (j := 628) oqBody_605 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_628

set_option maxRecDepth 100000 in
theorem walk_666 : CutsKnown 666 :=
  main_cutsKnown (j := 666) oqBody_643 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_666

set_option maxRecDepth 100000 in
theorem walk_688 : CutsKnown 688 :=
  main_cutsKnown (j := 688) oqBody_665 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_688

set_option maxRecDepth 100000 in
theorem walk_701 : CutsKnown 701 :=
  main_cutsKnown (j := 701) oqBody_678 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_701

set_option maxRecDepth 100000 in
theorem walk_778 : CutsKnown 778 :=
  main_cutsKnown (j := 778) oqBody_755 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_778

set_option maxRecDepth 100000 in
theorem walk_856 : CutsKnown 856 :=
  loop1_cutsKnown (j := 856) oqBody_835 (by decide) (by decide) (by decide) walkOk_856

set_option maxRecDepth 100000 in
theorem walk_864 : CutsKnown 864 :=
  loop0_cutsKnown (j := 864) oqBody_840 (by decide) (by decide) (by decide) walkOk_864

set_option maxRecDepth 100000 in
theorem walk_866 : CutsKnown 866 :=
  loop0_cutsKnown (j := 866) oqBody_841 (by decide) (by decide) (by decide) walkOk_866

set_option maxRecDepth 100000 in
theorem walk_874 : CutsKnown 874 :=
  loop1_cutsKnown (j := 874) oqBody_847 (by decide) (by decide) (by decide) walkOk_874

set_option maxRecDepth 100000 in
theorem walk_888 : CutsKnown 888 :=
  loop0_cutsKnown (j := 888) oqBody_856 (by decide) (by decide) (by decide) walkOk_888

set_option maxRecDepth 100000 in
theorem walk_890 : CutsKnown 890 :=
  loop0_cutsKnown (j := 890) oqBody_857 (by decide) (by decide) (by decide) walkOk_890

set_option maxRecDepth 100000 in
theorem walk_898 : CutsKnown 898 :=
  loop1_cutsKnown (j := 898) oqBody_861 (by decide) (by decide) (by decide) walkOk_898

set_option maxRecDepth 100000 in
theorem walk_900 : CutsKnown 900 :=
  loop0_cutsKnown (j := 900) oqBody_862 (by decide) (by decide) (by decide) walkOk_900

set_option maxRecDepth 100000 in
theorem walk_908 : CutsKnown 908 :=
  loop1_cutsKnown (j := 908) oqBody_866 (by decide) (by decide) (by decide) walkOk_908

set_option maxRecDepth 100000 in
theorem walk_918 : CutsKnown 918 :=
  loop0_cutsKnown (j := 918) oqBody_872 (by decide) (by decide) (by decide) walkOk_918

set_option maxRecDepth 100000 in
theorem walk_922 : CutsKnown 922 :=
  loop1_cutsKnown (j := 922) oqBody_876 (by decide) (by decide) (by decide) walkOk_922

set_option maxRecDepth 100000 in
theorem walk_924 : CutsKnown 924 :=
  loop1_cutsKnown (j := 924) oqBody_878 (by decide) (by decide) (by decide) walkOk_924

set_option maxRecDepth 100000 in
theorem walk_928 : CutsKnown 928 :=
  loop0_cutsKnown (j := 928) oqBody_881 (by decide) (by decide) (by decide) walkOk_928

set_option maxRecDepth 100000 in
theorem walk_943 : CutsKnown 943 :=
  loop1_cutsKnown (j := 943) oqBody_892 (by decide) (by decide) (by decide) walkOk_943

end
end LeanVM.Guest.End
