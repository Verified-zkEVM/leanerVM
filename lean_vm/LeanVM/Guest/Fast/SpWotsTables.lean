module

/-!
# `sp_wots`' positions, as literal tables

The cells `sp_wots` (`Data.core19`) hints its chains' starts at, precomputed from its template
(`B1/Sig/SpWotsT.lean`, `spGroupsT`, `spLast`) in the guest's numbering (`spRen`) and checked
equal to it by kernel evaluation
(`Fast/SpWotsTablesCheck.lean`): its codeword groups' selector cells (each group's digit hint, its
base), and the chains' starts from a selector (the first group's, the other groups', the last
chain's), as the shared reader of a codeword reads them (`cwCell`, `Fast/Wots.lean`).
-/

namespace LeanVM.Guest.Fast

@[expose] public section

/-- The codeword groups' selector cells: `21` groups of three digits, then the last chain's. -/
def spSel : List Nat := [
    16, 1249, 2445, 3641, 4837, 6033, 7229, 8425, 9621, 10817, 12013,
    13209, 14405, 15601, 16797, 17993, 19189, 20385, 21581, 22777, 23973, 25169]

/-- The first group's chain starts from its selector: row `r`, arm `k`. -/
def spFirst : List (List Nat) := [
  [12, 160, 189, 46, 237, 264, 290, 46, 332, 356, 379, 46, 415, 435, 454, 46, 482, 509, 535, 46,
    577, 601, 624, 46, 660, 681, 701, 46, 731, 748, 764, 46, 786, 810, 833, 46, 869, 890, 910, 46,
    940, 958, 975, 46, 999, 1013, 1026, 46, 1042, 1062, 1081, 46, 1109, 1126, 1142, 46, 1164,
    1178, 1191, 46, 1207, 1217, 1226, 46],
  [59, 167, 193, 215, 245, 271, 294, 313, 340, 363, 383, 399, 95, 95, 95, 95, 490, 516, 539, 558,
    585, 608, 628, 644, 668, 688, 705, 718, 95, 95, 95, 95, 794, 817, 837, 853, 877, 897, 914,
    927, 948, 965, 979, 989, 95, 95, 95, 95, 1050, 1069, 1085, 1097, 1117, 1133, 1146, 1155, 1172,
    1185, 1195, 1201, 95, 95, 95, 95],
  [108, 177, 203, 225, 252, 278, 301, 320, 344, 367, 387, 403, 423, 442, 458, 470, 500, 526, 549,
    568, 592, 615, 635, 651, 672, 692, 709, 722, 739, 755, 768, 777, 804, 827, 847, 863, 884, 904,
    921, 934, 952, 969, 983, 993, 1007, 1020, 1030, 1036, 144, 144, 144, 144, 144, 144, 144, 144,
    144, 144, 144, 144, 144, 144, 144, 144]]

/-- The other groups' chain starts from their selectors: row `r`, arm `k`. -/
def spRest : List (List Nat) := [
  [6, 155, 183, 42, 229, 257, 282, 42, 322, 347, 369, 42, 403, 424, 442, 42, 468, 496, 521, 42,
    561, 586, 608, 42, 642, 664, 683, 42, 711, 729, 744, 42, 764, 789, 811, 42, 845, 867, 886, 42,
    914, 933, 949, 42, 971, 986, 998, 42, 1012, 1033, 1051, 42, 1077, 1095, 1110, 42, 1130, 1145,
    1157, 42, 1171, 1182, 1190, 42],
  [55, 162, 187, 208, 239, 264, 286, 304, 332, 354, 373, 388, 91, 91, 91, 91, 478, 503, 525, 543,
    571, 593, 612, 627, 652, 671, 687, 699, 91, 91, 91, 91, 774, 796, 815, 830, 855, 874, 890,
    902, 924, 940, 953, 962, 91, 91, 91, 91, 1022, 1040, 1055, 1066, 1087, 1102, 1114, 1122, 1140,
    1152, 1161, 1166, 91, 91, 91, 91],
  [104, 172, 197, 218, 246, 271, 293, 311, 336, 358, 377, 392, 413, 431, 446, 457, 488, 513, 535,
    553, 578, 600, 619, 634, 656, 675, 691, 703, 721, 736, 748, 756, 784, 806, 825, 840, 862, 881,
    897, 909, 928, 944, 957, 966, 981, 993, 1002, 1007, 140, 140, 140, 140, 140, 140, 140, 140,
    140, 140, 140, 140, 140, 140, 140, 140]]

/-- The last chain's start from its selector: arm `k`. -/
def spLast : List (List Nat) := [
  [6, 57, 65, 42]]

/-- Group `p`'s table of starts from its selector: the first group's, the other groups', the last
chain's. -/
def spTabOf (p : Nat) : List (List Nat) := if p = 0 then spFirst else if p < 21 then spRest else spLast

end
end LeanVM.Guest.Fast
