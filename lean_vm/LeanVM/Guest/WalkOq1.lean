/-
  LeanVM.Guest.WalkOq1

  The cut obligations (`CutsKnown`) of a quarter of `opening_queries`' specializations and loops,
  from their templates (`B1/Opening/QueriesBody1.lean`), the generic forms (`WalkKnown.lean`) and
  their certificates' checks (`WalkOqOk1.lean`).
-/

module

public import LeanVM.Guest.WalkKnown
public import LeanVM.Guest.WalkOqOk1
public import LeanVM.Guest.B1.Opening.QueriesBody1

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

theorem walk_445 : CutsKnown 445 :=
  main_cutsKnown (j := 445) oqBody_422 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_445

theorem walk_494 : CutsKnown 494 :=
  main_cutsKnown (j := 494) oqBody_471 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_494

theorem walk_497 : CutsKnown 497 :=
  main_cutsKnown (j := 497) oqBody_474 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_497

theorem walk_538 : CutsKnown 538 :=
  main_cutsKnown (j := 538) oqBody_515 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_538

theorem walk_556 : CutsKnown 556 :=
  main_cutsKnown (j := 556) oqBody_533 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_556

theorem walk_586 : CutsKnown 586 :=
  main_cutsKnown (j := 586) oqBody_563 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_586

theorem walk_591 : CutsKnown 591 :=
  main_cutsKnown (j := 591) oqBody_568 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_591

theorem walk_625 : CutsKnown 625 :=
  main_cutsKnown (j := 625) oqBody_602 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_625

theorem walk_655 : CutsKnown 655 :=
  main_cutsKnown (j := 655) oqBody_632 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_655

theorem walk_706 : CutsKnown 706 :=
  main_cutsKnown (j := 706) oqBody_683 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_706

theorem walk_715 : CutsKnown 715 :=
  main_cutsKnown (j := 715) oqBody_692 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_715

theorem walk_744 : CutsKnown 744 :=
  main_cutsKnown (j := 744) oqBody_721 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_744

theorem walk_766 : CutsKnown 766 :=
  main_cutsKnown (j := 766) oqBody_743 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_766

theorem walk_768 : CutsKnown 768 :=
  main_cutsKnown (j := 768) oqBody_745 (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_768

theorem walk_852 : CutsKnown 852 :=
  loop0_cutsKnown (j := 852) oqBody_831 (by decide) (by decide) (by decide) walkOk_852

theorem walk_870 : CutsKnown 870 :=
  loop0_cutsKnown (j := 870) oqBody_844 (by decide) (by decide) (by decide) walkOk_870

theorem walk_872 : CutsKnown 872 :=
  loop0_cutsKnown (j := 872) oqBody_845 (by decide) (by decide) (by decide) walkOk_872

theorem walk_886 : CutsKnown 886 :=
  loop1_cutsKnown (j := 886) oqBody_855 (by decide) (by decide) (by decide) walkOk_886

theorem walk_894 : CutsKnown 894 :=
  loop1_cutsKnown (j := 894) oqBody_859 (by decide) (by decide) (by decide) walkOk_894

theorem walk_902 : CutsKnown 902 :=
  loop1_cutsKnown (j := 902) oqBody_863 (by decide) (by decide) (by decide) walkOk_902

theorem walk_904 : CutsKnown 904 :=
  loop0_cutsKnown (j := 904) oqBody_864 (by decide) (by decide) (by decide) walkOk_904

theorem walk_916 : CutsKnown 916 :=
  loop0_cutsKnown (j := 916) oqBody_871 (by decide) (by decide) (by decide) walkOk_916

theorem walk_921 : CutsKnown 921 :=
  loop1_cutsKnown (j := 921) oqBody_875 (by decide) (by decide) (by decide) walkOk_921

theorem walk_932 : CutsKnown 932 :=
  loop0_cutsKnown (j := 932) oqBody_883 (by decide) (by decide) (by decide) walkOk_932

theorem walk_933 : CutsKnown 933 :=
  loop1_cutsKnown (j := 933) oqBody_884 (by decide) (by decide) (by decide) walkOk_933

theorem walk_936 : CutsKnown 936 :=
  loop1_cutsKnown (j := 936) oqBody_887 (by decide) (by decide) (by decide) walkOk_936

theorem walk_939 : CutsKnown 939 :=
  loop1_cutsKnown (j := 939) oqBody_889 (by decide) (by decide) (by decide) walkOk_939

theorem walk_941 : CutsKnown 941 :=
  loop0_cutsKnown (j := 941) oqBody_890 (by decide) (by decide) (by decide) walkOk_941

end
end LeanVM.Guest.End
