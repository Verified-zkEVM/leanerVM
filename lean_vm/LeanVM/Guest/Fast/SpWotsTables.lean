module

/-!
# `sp_wots`' positions, as literal tables

The cells `sp_wots` (`Data.core20`) hints its chains' starts at, precomputed from its template
(`B1/Sig/SpWotsT.lean`, `spGroupsT`, `spLast`) and checked equal to it by kernel evaluation
(`Fast/SpWotsTablesCheck.lean`): its codeword groups' selector cells (each group's digit hint, its
base), and the chains' starts from a selector (the first group's, the other groups', the last
chain's), as the shared reader of a codeword reads them (`cwCell`, `Fast/Wots.lean`).
-/

namespace LeanVM.Guest.Fast

@[expose] public section

/-- The codeword groups' selector cells: `21` groups of three digits, then the last chain's. -/
def spSel : List Nat := [
    13, 1587, 3097, 4607, 6117, 7627, 9137, 10647, 12157, 13667, 15177, 16687, 18197, 19707, 21217,
    22727, 24237, 25747, 27257, 28767, 30277, 31787]

/-- The first group's chain starts from its selector: row `r`, arm `k`. -/
def spFirst : List (List Nat) := [
  [6, 161, 195, 47, 253, 287, 318, 47, 370, 401, 429, 47, 475, 502, 526, 47, 564, 598, 629, 47,
    681, 712, 740, 47, 786, 814, 839, 47, 879, 903, 924, 47, 956, 987, 1015, 47, 1061, 1089,
    1114, 47, 1154, 1179, 1201, 47, 1235, 1256, 1274, 47, 1300, 1327, 1351, 47, 1389, 1413,
    1434, 47, 1466, 1487, 1505, 47, 1531, 1548, 1562, 47],
  [60, 173, 204, 226, 268, 299, 327, 346, 385, 413, 438, 454, 96, 96, 96, 96, 579, 610, 638, 657,
    696, 724, 749, 765, 801, 826, 848, 861, 96, 96, 96, 96, 971, 999, 1024, 1040, 1076, 1101,
    1123, 1136, 1169, 1191, 1210, 1220, 96, 96, 96, 96, 1315, 1339, 1360, 1372, 1404, 1425,
    1443, 1452, 1481, 1499, 1514, 1520, 96, 96, 96, 96],
  [109, 183, 214, 241, 275, 306, 334, 358, 389, 417, 442, 463, 490, 514, 535, 547, 589, 620, 648,
    672, 703, 731, 756, 777, 805, 830, 852, 870, 894, 915, 933, 942, 981, 1009, 1034, 1055,
    1083, 1108, 1130, 1148, 1173, 1195, 1214, 1229, 1250, 1268, 1283, 1289, 145, 145, 145, 145,
    145, 145, 145, 145, 145, 145, 145, 145, 145, 145, 145, 145]]

/-- The other groups' chain starts from their selector: row `r`, arm `k`. -/
def spRest : List (List Nat) := [
  [5, 159, 192, 46, 248, 281, 311, 46, 361, 391, 418, 46, 462, 488, 511, 46, 547, 580, 610, 46,
    660, 690, 717, 46, 761, 788, 812, 46, 850, 873, 893, 46, 923, 953, 980, 46, 1024, 1051,
    1075, 46, 1113, 1137, 1158, 46, 1190, 1210, 1227, 46, 1251, 1277, 1300, 46, 1336, 1359,
    1379, 46, 1409, 1429, 1446, 46, 1470, 1486, 1499, 46],
  [59, 171, 201, 222, 263, 293, 320, 338, 376, 403, 427, 442, 95, 95, 95, 95, 562, 592, 619, 637,
    675, 702, 726, 741, 776, 800, 821, 833, 95, 95, 95, 95, 938, 965, 989, 1004, 1039, 1063,
    1084, 1096, 1128, 1149, 1167, 1176, 95, 95, 95, 95, 1266, 1289, 1309, 1320, 1351, 1371,
    1388, 1396, 1424, 1441, 1455, 1460, 95, 95, 95, 95],
  [108, 181, 211, 237, 270, 300, 327, 350, 380, 407, 431, 451, 477, 500, 520, 531, 572, 602, 629,
    652, 682, 709, 733, 753, 780, 804, 825, 842, 865, 885, 902, 910, 948, 975, 999, 1019, 1046,
    1070, 1091, 1108, 1132, 1153, 1171, 1185, 1205, 1222, 1236, 1241, 144, 144, 144, 144, 144,
    144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144]]

/-- The last chain's start from its selector, arm `k`. -/
def spLast : List (List Nat) := [
  [5, 61, 74, 46]]

/-- Group `p`'s table of starts from its selector: the first group's, the other groups', the last
chain's. -/
def spTabOf (p : Nat) : List (List Nat) := if p = 0 then spFirst else if p < 21 then spRest else spLast

end
end LeanVM.Guest.Fast
