/-
  LeanVM.Guest.B1.Tables.VtC.BGlueGen

  `verify_tables`' bus sides between the selectors and the stream reads, slice by slice
  (generated: scripts/b1c-vt/genbglue.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BGlue
public import LeanVM.Guest.B1.Tables.Vt.SelFw

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}

set_option maxRecDepth 100000 in
theorem vtB_glue_769 (hl : args.length = 20)  :
    ∀ s ∈ (vtPre.drop 769).take 3, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  exact vt_blockR hl 769 3 [] (by decide +kernel) (fun _ h ↦ absurd h (by simp))

set_option maxRecDepth 100000 in
theorem vtB_glue_784 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i))  :
    ∀ s ∈ (vtPre.drop 784).take 10, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 784 10 [
    .atom (.load (.n 797) (.n 13) 0),
    .atom (.load (.n 798) (.n 13) 1),
    .atom (.load (.n 800) (.n 13) 2)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact (vt_readAt hl 784 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 785 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 787 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_807 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) 
    (h810 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.dispatch (.n 29) vtImNames [.n 8] [.n 824]))
    (h811 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 824) (.n 781) 1))) :
    ∀ s ∈ (vtPre.drop 807).take 10, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 807 10 [
    .atom (.load (.n 821) (.n 13) 0),
    .dispatch (.n 29) vtImNames [.n 8] [.n 824],
    .atom (.load (.n 824) (.n 781) 1),
    .atom (.load (.n 825) (.n 13) 1),
    .atom (.load (.n 828) (.n 13) 2)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact (vt_readAt hl 807 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact h810
  · exact h811
  · exact (vt_readAt hl 812 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 815 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_826 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) 
    (h826 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 830) (.n 15) 0))) :
    ∀ s ∈ (vtPre.drop 826).take 4, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 826 4 [
    .atom (.load (.n 830) (.n 15) 0),
    .atom (.load (.n 840) (.n 13) 3)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact h826
  · exact (vt_readAt hl 827 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_839 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) 
    (h839 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 843) (.n 15) 1))) :
    ∀ s ∈ (vtPre.drop 839).take 4, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 839 4 [
    .atom (.load (.n 843) (.n 15) 1),
    .atom (.load (.n 853) (.n 13) 4)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact h839
  · exact (vt_readAt hl 840 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_852 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) 
    (h852 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 856) (.n 15) 2))) :
    ∀ s ∈ (vtPre.drop 852).take 12, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 852 12 [
    .atom (.load (.n 856) (.n 15) 2),
    .atom (.load (.n 866) (.n 13) 5)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact h852
  · exact (vt_readAt hl 853 (by decide +kernel) (by decide +kernel) (hw 5 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_877 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) 
    (h880 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.dispatch (.n 876) vtImNames [.n 8] [.n 894]))
    (h881 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 894) (.n 781) 2))) :
    ∀ s ∈ (vtPre.drop 877).take 58, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 877 58 [
    .atom (.load (.n 891) (.n 13) 0),
    .dispatch (.n 876) vtImNames [.n 8] [.n 894],
    .atom (.load (.n 894) (.n 781) 2),
    .atom (.load (.n 895) (.n 13) 1),
    .atom (.load (.n 898) (.n 13) 2),
    .atom (.load (.n 900) (.n 13) 3),
    .atom (.load (.n 904) (.n 13) 4),
    .atom (.load (.n 908) (.n 13) 5),
    .atom (.load (.n 912) (.n 13) 6),
    .atom (.load (.n 916) (.n 13) 7),
    .atom (.load (.n 920) (.n 13) 8),
    .atom (.load (.n 924) (.n 13) 9),
    .atom (.load (.n 928) (.n 13) 10),
    .atom (.load (.n 932) (.n 13) 11),
    .atom (.load (.n 936) (.n 13) 12),
    .atom (.load (.n 940) (.n 13) 13)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (vt_readAt hl 877 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact h880
  · exact h881
  · exact (vt_readAt hl 882 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 885 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 887 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 891 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 895 (by decide +kernel) (by decide +kernel) (hw 5 (by norm_num))).2
  · exact (vt_readAt hl 899 (by decide +kernel) (by decide +kernel) (hw 6 (by norm_num))).2
  · exact (vt_readAt hl 903 (by decide +kernel) (by decide +kernel) (hw 7 (by norm_num))).2
  · exact (vt_readAt hl 907 (by decide +kernel) (by decide +kernel) (hw 8 (by norm_num))).2
  · exact (vt_readAt hl 911 (by decide +kernel) (by decide +kernel) (hw 9 (by norm_num))).2
  · exact (vt_readAt hl 915 (by decide +kernel) (by decide +kernel) (hw 10 (by norm_num))).2
  · exact (vt_readAt hl 919 (by decide +kernel) (by decide +kernel) (hw 11 (by norm_num))).2
  · exact (vt_readAt hl 923 (by decide +kernel) (by decide +kernel) (hw 12 (by norm_num))).2
  · exact (vt_readAt hl 927 (by decide +kernel) (by decide +kernel) (hw 13 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_1425 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) {Q : ℕ → E}
    (hidx : ∀ i < 3, LoadHolds rd (vtσ rd wo args (.n 781)) i (Q i))  :
    ∀ s ∈ (vtPre.drop 1425).take 448, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 1425 448 [
    .atom (.load (.n 1387) (.n 13) 0),
    .atom (.load (.n 1390) (.n 13) 0),
    .atom (.load (.n 1394) (.n 13) 3),
    .atom (.load (.n 1398) (.n 13) 0),
    .atom (.load (.n 1404) (.n 13) 0),
    .atom (.load (.n 1410) (.n 13) 0),
    .atom (.load (.n 1417) (.n 13) 0),
    .atom (.load (.n 1420) (.n 13) 0),
    .atom (.load (.n 1424) (.n 13) 3),
    .atom (.load (.n 1430) (.n 13) 0),
    .atom (.load (.n 1436) (.n 13) 0),
    .atom (.load (.n 1442) (.n 13) 0),
    .atom (.load (.n 1450) (.n 13) 0),
    .atom (.load (.n 1453) (.n 13) 0),
    .atom (.load (.n 1457) (.n 13) 3),
    .atom (.load (.n 1463) (.n 13) 0),
    .atom (.load (.n 1471) (.n 13) 0),
    .atom (.load (.n 1474) (.n 13) 0),
    .atom (.load (.n 1478) (.n 13) 3),
    .atom (.load (.n 1484) (.n 13) 0),
    .atom (.load (.n 1490) (.n 13) 0),
    .atom (.load (.n 1496) (.n 13) 0),
    .atom (.load (.n 1504) (.n 13) 0),
    .atom (.load (.n 1507) (.n 13) 0),
    .atom (.load (.n 1511) (.n 13) 3),
    .atom (.load (.n 1517) (.n 13) 0),
    .atom (.load (.n 1523) (.n 13) 0),
    .atom (.load (.n 1529) (.n 13) 0),
    .atom (.load (.n 1537) (.n 13) 0),
    .atom (.load (.n 1540) (.n 13) 0),
    .atom (.load (.n 1544) (.n 13) 3),
    .atom (.load (.n 1550) (.n 13) 0),
    .atom (.load (.n 1556) (.n 13) 0),
    .atom (.load (.n 1562) (.n 13) 0),
    .atom (.load (.n 1568) (.n 13) 0),
    .atom (.load (.n 1574) (.n 13) 0),
    .atom (.load (.n 1580) (.n 13) 0),
    .atom (.load (.n 1586) (.n 13) 0),
    .atom (.load (.n 1592) (.n 13) 0),
    .atom (.load (.n 1598) (.n 13) 0),
    .atom (.load (.n 1604) (.n 13) 0),
    .atom (.load (.n 1610) (.n 13) 0),
    .atom (.load (.n 1616) (.n 13) 0),
    .atom (.load (.n 1622) (.n 13) 0),
    .atom (.load (.n 1628) (.n 13) 0),
    .atom (.load (.n 1632) (.n 13) 3),
    .atom (.load (.n 1636) (.n 13) 4),
    .atom (.load (.n 1642) (.n 13) 0),
    .atom (.load (.n 1646) (.n 13) 3),
    .atom (.load (.n 1650) (.n 13) 4),
    .atom (.load (.n 1656) (.n 13) 0),
    .atom (.load (.n 1660) (.n 13) 3),
    .atom (.load (.n 1664) (.n 13) 4),
    .atom (.load (.n 1670) (.n 13) 0),
    .atom (.load (.n 1674) (.n 13) 3),
    .atom (.load (.n 1678) (.n 13) 4),
    .atom (.load (.n 1684) (.n 13) 0),
    .atom (.load (.n 1688) (.n 13) 3),
    .atom (.load (.n 1692) (.n 13) 4),
    .atom (.load (.n 1698) (.n 13) 0),
    .atom (.load (.n 1702) (.n 13) 3),
    .atom (.load (.n 1706) (.n 13) 4),
    .atom (.load (.n 1712) (.n 13) 0),
    .atom (.load (.n 1716) (.n 13) 3),
    .atom (.load (.n 1720) (.n 13) 4),
    .atom (.load (.n 1726) (.n 13) 0),
    .atom (.load (.n 1730) (.n 13) 3),
    .atom (.load (.n 1734) (.n 13) 4),
    .atom (.load (.n 1740) (.n 13) 0),
    .atom (.load (.n 1744) (.n 13) 3),
    .atom (.load (.n 1750) (.n 13) 0),
    .atom (.load (.n 1754) (.n 13) 3),
    .atom (.load (.n 1758) (.n 13) 4),
    .atom (.load (.n 1764) (.n 13) 0),
    .atom (.load (.n 1768) (.n 13) 3),
    .atom (.load (.n 1772) (.n 13) 4),
    .atom (.load (.n 1778) (.n 13) 0),
    .atom (.load (.n 1782) (.n 13) 3),
    .atom (.load (.n 1786) (.n 13) 4),
    .atom (.load (.n 1792) (.n 13) 0),
    .atom (.load (.n 1796) (.n 13) 3),
    .atom (.load (.n 1800) (.n 13) 4),
    .atom (.load (.n 1814) (.n 13) 0),
    .atom (.load (.n 1815) (.n 13) 1),
    .atom (.load (.n 1819) (.n 13) 2),
    .atom (.load (.n 1828) (.n 13) 0),
    .atom (.load (.n 1831) (.n 781) 1),
    .atom (.load (.n 1832) (.n 13) 1)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (vt_readAt hl 1425 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1428 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1432 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1436 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1442 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1448 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1455 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1458 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1462 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1468 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1474 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1480 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1488 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1491 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1495 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1501 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1509 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1512 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1516 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1522 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1528 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1534 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1542 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1545 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1549 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1555 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1561 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1567 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1575 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1578 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1582 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1588 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1594 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1600 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1606 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1612 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1618 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1624 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1630 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1636 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1642 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1648 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1654 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1660 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1666 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1670 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1674 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1680 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1684 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1688 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1694 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1698 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1702 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1708 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1712 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1716 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1722 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1726 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1730 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1736 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1740 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1744 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1750 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1754 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1758 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1764 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1768 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1772 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1778 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1782 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1788 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1792 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1796 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1802 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1806 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1810 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1816 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1820 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1824 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1830 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1834 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1838 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1852 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1853 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 1857 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 1866 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1869 (by decide +kernel) (by decide +kernel) (hidx 1 (by norm_num))).2
  · exact (vt_readAt hl 1870 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_1882 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) {P : ℕ → E}
    (hpool : ∀ i < 5, LoadHolds rd (vtσ rd wo args (.n 15)) i (P i)) {Q : ℕ → E}
    (hidx : ∀ i < 3, LoadHolds rd (vtσ rd wo args (.n 781)) i (Q i)) 
    (h1882 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 1835) (.n 15) 3)))
    (h1915 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.keccak [.n 837, .n 839, .n 850, .n 852, .n 863, .n 865, .n 1842, .n 1844, .n 20, .n 21, .n 22, .n 23, .n 24] [.n 1877, .n 1878, .n 1879, .n 1880, .n 1881, .n 1882, .n 1883, .n 1884, .n 1885, .n 1886, .n 1887, .n 1888, .n 1889] false false))) :
    ∀ s ∈ (vtPre.drop 1882).take 34, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 1882 34 [
    .atom (.load (.n 1835) (.n 15) 3),
    .atom (.load (.n 1845) (.n 13) 2),
    .atom (.load (.n 1848) (.n 15) 0),
    .atom (.load (.n 1849) (.n 13) 3),
    .atom (.load (.n 1852) (.n 15) 1),
    .atom (.load (.n 1853) (.n 13) 4),
    .atom (.load (.n 1856) (.n 15) 2),
    .atom (.load (.n 1857) (.n 13) 5),
    .atom (.load (.n 1870) (.n 13) 0),
    .atom (.load (.n 1873) (.n 781) 2),
    .atom (.load (.n 1874) (.n 13) 1),
    .atom (.keccak [.n 837, .n 839, .n 850, .n 852, .n 863, .n 865, .n 1842, .n 1844, .n 20, .n 21, .n 22, .n 23, .n 24] [.n 1877, .n 1878, .n 1879, .n 1880, .n 1881, .n 1882, .n 1883, .n 1884, .n 1885, .n 1886, .n 1887, .n 1888, .n 1889] false false)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1882
  · exact (vt_readAt hl 1883 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 1886 (by decide +kernel) (by decide +kernel) (hpool 0 (by norm_num))).2
  · exact (vt_readAt hl 1887 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1890 (by decide +kernel) (by decide +kernel) (hpool 1 (by norm_num))).2
  · exact (vt_readAt hl 1891 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1894 (by decide +kernel) (by decide +kernel) (hpool 2 (by norm_num))).2
  · exact (vt_readAt hl 1895 (by decide +kernel) (by decide +kernel) (hw 5 (by norm_num))).2
  · exact (vt_readAt hl 1908 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1911 (by decide +kernel) (by decide +kernel) (hidx 2 (by norm_num))).2
  · exact (vt_readAt hl 1912 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact h1915

set_option maxRecDepth 100000 in
theorem vtB_glue_1925 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) 
    (h1925 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 1890) (.n 15) 4))) :
    ∀ s ∈ (vtPre.drop 1925).take 159, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 1925 159 [
    .atom (.load (.n 1890) (.n 15) 4),
    .atom (.load (.n 1900) (.n 13) 2),
    .atom (.load (.n 1903) (.n 13) 3),
    .atom (.load (.n 1907) (.n 13) 4),
    .atom (.load (.n 1911) (.n 13) 5),
    .atom (.load (.n 1915) (.n 13) 6),
    .atom (.load (.n 1919) (.n 13) 7),
    .atom (.load (.n 1923) (.n 13) 8),
    .atom (.load (.n 1927) (.n 13) 9),
    .atom (.load (.n 1931) (.n 13) 10),
    .atom (.load (.n 1935) (.n 13) 11),
    .atom (.load (.n 1939) (.n 13) 12),
    .atom (.load (.n 1943) (.n 13) 13)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1925
  · exact (vt_readAt hl 1926 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 1929 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1933 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1937 (by decide +kernel) (by decide +kernel) (hw 5 (by norm_num))).2
  · exact (vt_readAt hl 1941 (by decide +kernel) (by decide +kernel) (hw 6 (by norm_num))).2
  · exact (vt_readAt hl 1945 (by decide +kernel) (by decide +kernel) (hw 7 (by norm_num))).2
  · exact (vt_readAt hl 1949 (by decide +kernel) (by decide +kernel) (hw 8 (by norm_num))).2
  · exact (vt_readAt hl 1953 (by decide +kernel) (by decide +kernel) (hw 9 (by norm_num))).2
  · exact (vt_readAt hl 1957 (by decide +kernel) (by decide +kernel) (hw 10 (by norm_num))).2
  · exact (vt_readAt hl 1961 (by decide +kernel) (by decide +kernel) (hw 11 (by norm_num))).2
  · exact (vt_readAt hl 1965 (by decide +kernel) (by decide +kernel) (hw 12 (by norm_num))).2
  · exact (vt_readAt hl 1969 (by decide +kernel) (by decide +kernel) (hw 13 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_2517 (hl : args.length = 20)  :
    ∀ s ∈ (vtPre.drop 2517).take 56, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  exact vt_blockR hl 2517 56 [] (by decide +kernel) (fun _ h ↦ absurd h (by simp))

end

end
end LeanVM.Guest.B1.Tables
