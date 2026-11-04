module

/-!
# `sp_wots`' positions, as literal tables

The cells `sp_wots` (`Data.core19`) hints its chains' starts at, precomputed from its template
(`B1/Sig/SpWotsT.lean`, `spGroupsT`, `spLast`) and checked equal to it by kernel evaluation
(`Fast/SpWotsTablesCheck.lean`): its codeword groups' selector cells (each group's digit hint, its
base), and the chains' starts from a selector (the first group's, the other groups', the last
chain's), as the shared reader of a codeword reads them (`cwCell`, `Fast/Wots.lean`).
-/

namespace LeanVM.Guest.Fast

@[expose] public section

/-- The codeword groups' selector cells: `21` groups of three digits, then the last chain's. -/
def spSel : List Nat := [
    13, 1278, 2474, 3670, 4866, 6062, 7258, 8454, 9650, 10846, 12042, 13238, 14434, 15630, 16826,
    18022, 19218, 20414, 21610, 22806, 24002, 25198]

/-- The first group's chain starts from its selector: row `r`, arm `k`. -/
def spFirst : List (List Nat) := [
  [12, 162, 191, 48, 239, 268, 294, 48, 336, 362, 385, 48, 421, 443, 462, 48, 490, 519, 545, 48,
    587, 613, 636, 48, 672, 695, 715, 48, 745, 764, 780, 48, 802, 828, 851, 48, 887, 910, 930, 48,
    960, 980, 997, 48, 1021, 1037, 1050, 48, 1066, 1088, 1107, 48, 1135, 1154, 1170, 48, 1192,
    1208, 1221, 48, 1237, 1249, 1258, 48],
  [61, 169, 195, 217, 249, 275, 298, 317, 346, 369, 389, 405, 97, 97, 97, 97, 500, 526, 549, 568,
    597, 620, 640, 656, 682, 702, 719, 732, 97, 97, 97, 97, 812, 835, 855, 871, 897, 917, 934, 947,
    970, 987, 1001, 1011, 97, 97, 97, 97, 1076, 1095, 1111, 1123, 1145, 1161, 1174, 1183, 1202,
    1215, 1225, 1231, 97, 97, 97, 97],
  [110, 179, 205, 227, 256, 282, 305, 324, 350, 373, 393, 409, 431, 450, 466, 478, 510, 536, 559,
    578, 604, 627, 647, 663, 686, 706, 723, 736, 755, 771, 784, 793, 822, 845, 865, 881, 904, 924,
    941, 954, 974, 991, 1005, 1015, 1031, 1044, 1054, 1060, 146, 146, 146, 146, 146, 146, 146, 146,
    146, 146, 146, 146, 146, 146, 146, 146]]

/-- The other groups' chain starts from their selector: row `r`, arm `k`. -/
def spRest : List (List Nat) := [
  [6, 155, 183, 42, 229, 257, 282, 42, 322, 347, 369, 42, 403, 424, 442, 42, 468, 496, 521, 42,
    561, 586, 608, 42, 642, 664, 683, 42, 711, 729, 744, 42, 764, 789, 811, 42, 845, 867, 886, 42,
    914, 933, 949, 42, 971, 986, 998, 42, 1012, 1033, 1051, 42, 1077, 1095, 1110, 42, 1130, 1145,
    1157, 42, 1171, 1182, 1190, 42],
  [55, 162, 187, 208, 239, 264, 286, 304, 332, 354, 373, 388, 91, 91, 91, 91, 478, 503, 525, 543,
    571, 593, 612, 627, 652, 671, 687, 699, 91, 91, 91, 91, 774, 796, 815, 830, 855, 874, 890, 902,
    924, 940, 953, 962, 91, 91, 91, 91, 1022, 1040, 1055, 1066, 1087, 1102, 1114, 1122, 1140, 1152,
    1161, 1166, 91, 91, 91, 91],
  [104, 172, 197, 218, 246, 271, 293, 311, 336, 358, 377, 392, 413, 431, 446, 457, 488, 513, 535,
    553, 578, 600, 619, 634, 656, 675, 691, 703, 721, 736, 748, 756, 784, 806, 825, 840, 862, 881,
    897, 909, 928, 944, 957, 966, 981, 993, 1002, 1007, 140, 140, 140, 140, 140, 140, 140, 140,
    140, 140, 140, 140, 140, 140, 140, 140]]

/-- The last chain's start from its selector, arm `k`. -/
def spLast : List (List Nat) := [
  [6, 57, 65, 42]]

/-- Group `p`'s table of starts from its selector: the first group's, the other groups', the last
chain's. -/
def spTabOf (p : Nat) : List (List Nat) := if p = 0 then spFirst else if p < 21 then spRest else spLast

end
end LeanVM.Guest.Fast
