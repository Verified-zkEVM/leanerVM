/-
  LeanVM.Guest.WalkOq0

  The cut obligations (`CutsKnown`) of a quarter of `opening_queries`' specializations and loops,
  from their templates (`B1/Opening/QueriesBody0.lean`), the generic forms (`WalkKnown.lean`) and
  their certificates' checks (`WalkOqOk0.lean`).
-/

module

public import LeanVM.Guest.WalkKnown
public import LeanVM.Guest.WalkOqOk0
public import LeanVM.Guest.B1.Opening.QueriesBody0

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

theorem walk_436 : CutsKnown 436 :=
  main_cutsKnown (j := 436) oqBody_413 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_436

theorem walk_441 : CutsKnown 441 :=
  main_cutsKnown (j := 441) oqBody_418 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_441

theorem walk_448 : CutsKnown 448 :=
  main_cutsKnown (j := 448) oqBody_425 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_448

theorem walk_472 : CutsKnown 472 :=
  main_cutsKnown (j := 472) oqBody_449 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_472

theorem walk_512 : CutsKnown 512 :=
  main_cutsKnown (j := 512) oqBody_489 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_512

theorem walk_514 : CutsKnown 514 :=
  main_cutsKnown (j := 514) oqBody_491 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_514

theorem walk_547 : CutsKnown 547 :=
  main_cutsKnown (j := 547) oqBody_524 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_547

theorem walk_598 : CutsKnown 598 :=
  main_cutsKnown (j := 598) oqBody_575 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_598

theorem walk_621 : CutsKnown 621 :=
  main_cutsKnown (j := 621) oqBody_598 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_621

theorem walk_623 : CutsKnown 623 :=
  main_cutsKnown (j := 623) oqBody_600 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_623

theorem walk_646 : CutsKnown 646 :=
  main_cutsKnown (j := 646) oqBody_623 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_646

theorem walk_677 : CutsKnown 677 :=
  main_cutsKnown (j := 677) oqBody_654 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_677

theorem walk_724 : CutsKnown 724 :=
  main_cutsKnown (j := 724) oqBody_701 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_724

theorem walk_784 : CutsKnown 784 :=
  main_cutsKnown (j := 784) oqBody_761 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_784

theorem walk_848 : CutsKnown 848 :=
  loop1_cutsKnown (j := 848) oqBody_827 (by decide) (by decide) (by decide) walkOk_848

theorem walk_850 : CutsKnown 850 :=
  loop0_cutsKnown (j := 850) oqBody_829 (by decide) (by decide) (by decide) walkOk_850

theorem walk_854 : CutsKnown 854 :=
  loop0_cutsKnown (j := 854) oqBody_833 (by decide) (by decide) (by decide) walkOk_854

theorem walk_862 : CutsKnown 862 :=
  loop1_cutsKnown (j := 862) oqBody_839 (by decide) (by decide) (by decide) walkOk_862

theorem walk_876 : CutsKnown 876 :=
  loop0_cutsKnown (j := 876) oqBody_848 (by decide) (by decide) (by decide) walkOk_876

theorem walk_878 : CutsKnown 878 :=
  loop0_cutsKnown (j := 878) oqBody_849 (by decide) (by decide) (by decide) walkOk_878

theorem walk_892 : CutsKnown 892 :=
  loop0_cutsKnown (j := 892) oqBody_858 (by decide) (by decide) (by decide) walkOk_892

theorem walk_906 : CutsKnown 906 :=
  loop1_cutsKnown (j := 906) oqBody_865 (by decide) (by decide) (by decide) walkOk_906

theorem walk_912 : CutsKnown 912 :=
  loop1_cutsKnown (j := 912) oqBody_869 (by decide) (by decide) (by decide) walkOk_912

theorem walk_914 : CutsKnown 914 :=
  loop0_cutsKnown (j := 914) oqBody_870 (by decide) (by decide) (by decide) walkOk_914

theorem walk_920 : CutsKnown 920 :=
  loop1_cutsKnown (j := 920) oqBody_874 (by decide) (by decide) (by decide) walkOk_920

theorem walk_923 : CutsKnown 923 :=
  loop1_cutsKnown (j := 923) oqBody_877 (by decide) (by decide) (by decide) walkOk_923

theorem walk_934 : CutsKnown 934 :=
  loop1_cutsKnown (j := 934) oqBody_885 (by decide) (by decide) (by decide) walkOk_934

theorem walk_947 : CutsKnown 947 :=
  loop0_cutsKnown (j := 947) oqBody_894 (by decide) (by decide) (by decide) walkOk_947

end
end LeanVM.Guest.End
