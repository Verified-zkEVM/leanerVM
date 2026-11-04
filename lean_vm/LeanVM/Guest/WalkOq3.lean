/-
  LeanVM.Guest.WalkOq3

  The cut obligations (`CutsKnown`) of a quarter of `opening_queries`' specializations and loops,
  from their templates (`B1/Opening/QueriesBody3.lean`), the generic forms (`WalkKnown.lean`) and
  their certificates' checks (`WalkOqOk3.lean`).
-/

module

public import LeanVM.Guest.WalkKnown
public import LeanVM.Guest.WalkOqOk3
public import LeanVM.Guest.B1.Opening.QueriesBody3

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

theorem walk_459 : CutsKnown 459 :=
  main_cutsKnown (j := 459) oqBody_436 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_459

theorem walk_462 : CutsKnown 462 :=
  main_cutsKnown (j := 462) oqBody_439 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_462

theorem walk_491 : CutsKnown 491 :=
  main_cutsKnown (j := 491) oqBody_468 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_491

theorem walk_524 : CutsKnown 524 :=
  main_cutsKnown (j := 524) oqBody_501 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_524

theorem walk_526 : CutsKnown 526 :=
  main_cutsKnown (j := 526) oqBody_503 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_526

theorem walk_528 : CutsKnown 528 :=
  main_cutsKnown (j := 528) oqBody_505 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_528

theorem walk_565 : CutsKnown 565 :=
  main_cutsKnown (j := 565) oqBody_542 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_565

theorem walk_614 : CutsKnown 614 :=
  main_cutsKnown (j := 614) oqBody_591 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_614

theorem walk_637 : CutsKnown 637 :=
  main_cutsKnown (j := 637) oqBody_614 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_637

theorem walk_699 : CutsKnown 699 :=
  main_cutsKnown (j := 699) oqBody_676 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_699

theorem walk_703 : CutsKnown 703 :=
  main_cutsKnown (j := 703) oqBody_680 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_703

theorem walk_733 : CutsKnown 733 :=
  main_cutsKnown (j := 733) oqBody_710 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_733

theorem walk_755 : CutsKnown 755 :=
  main_cutsKnown (j := 755) oqBody_732 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_755

theorem walk_780 : CutsKnown 780 :=
  main_cutsKnown (j := 780) oqBody_757 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_780

theorem walk_858 : CutsKnown 858 :=
  loop0_cutsKnown (j := 858) oqBody_836 (by decide) (by decide) (by decide) walkOk_858

theorem walk_860 : CutsKnown 860 :=
  loop0_cutsKnown (j := 860) oqBody_837 (by decide) (by decide) (by decide) walkOk_860

theorem walk_868 : CutsKnown 868 :=
  loop1_cutsKnown (j := 868) oqBody_843 (by decide) (by decide) (by decide) walkOk_868

theorem walk_880 : CutsKnown 880 :=
  loop1_cutsKnown (j := 880) oqBody_851 (by decide) (by decide) (by decide) walkOk_880

theorem walk_882 : CutsKnown 882 :=
  loop0_cutsKnown (j := 882) oqBody_852 (by decide) (by decide) (by decide) walkOk_882

theorem walk_884 : CutsKnown 884 :=
  loop0_cutsKnown (j := 884) oqBody_853 (by decide) (by decide) (by decide) walkOk_884

theorem walk_896 : CutsKnown 896 :=
  loop1_cutsKnown (j := 896) oqBody_860 (by decide) (by decide) (by decide) walkOk_896

theorem walk_910 : CutsKnown 910 :=
  loop0_cutsKnown (j := 910) oqBody_867 (by decide) (by decide) (by decide) walkOk_910

theorem walk_919 : CutsKnown 919 :=
  loop1_cutsKnown (j := 919) oqBody_873 (by decide) (by decide) (by decide) walkOk_919

theorem walk_926 : CutsKnown 926 :=
  loop1_cutsKnown (j := 926) oqBody_880 (by decide) (by decide) (by decide) walkOk_926

theorem walk_930 : CutsKnown 930 :=
  loop0_cutsKnown (j := 930) oqBody_882 (by decide) (by decide) (by decide) walkOk_930

theorem walk_935 : CutsKnown 935 :=
  loop1_cutsKnown (j := 935) oqBody_886 (by decide) (by decide) (by decide) walkOk_935

theorem walk_937 : CutsKnown 937 :=
  loop1_cutsKnown (j := 937) oqBody_888 (by decide) (by decide) (by decide) walkOk_937

theorem walk_945 : CutsKnown 945 :=
  loop0_cutsKnown (j := 945) oqBody_893 (by decide) (by decide) (by decide) walkOk_945

end
end LeanVM.Guest.End
