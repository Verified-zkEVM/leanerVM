/-
  LeanVM.Guest.B1.KeccakGkr.LayerT

  `keccak_layer`'s four specializations as one template (`layerT first odd`), section by section.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Prod
public import LeanVM.Guest.B1.KeccakGkr.LayerRmfe
public import LeanVM.Guest.B1.KeccakGkr.EqFrame

/-!
# `keccak_layer` as a template

The specializations `keccak_layer__L{first}_L{odd}` (G:2478-2723) compile to one statement list up
to the product's table (`prodTab first`), the waiting cells of the squeeze after it, the
first layer's weight section, and a shift `d = 4·odd` of the values after the pack rounds' call
(`odd = 1` adds a `keccak_round` call and its four values). Sections:

* `headT`: the carried capacity (and, first, the waiting word's cells) copied, the claim's sixteen
  instance weights read (`KC_MU`);
* `prodT` (`Prod`): the product's 47 coefficients read and absorbed, and their projection;
* `checkT`: the projection plus `ι·κ` against the claim's value;
* `sqT`: the squeeze of `s`; `rmfeBlockT` (`LayerRmfe`): the instance weights at `s`;
* `hornerT`: the product at `s`;
* `packSetupT`: the pack rounds' first record, the loop, and with `odd` the last round;
* `lastT`, `localRoundsT`, `tReadsT`: the last record read, the eleven position rounds, `t`;
* `eqfT` (`EqFrame`): the lane weights of the local point;
* `weightT`: the claim's weights at the local point (first: `lanesEqT`; later: `shiftsT` and
  `formT`, `keccak_shifts_eq` and `keccak_form`);
* `tailT`: the final check, the squeeze of `β`, and the next claim's record.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Helpers -/

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem holdsList_map_atoms (n : ℕ) (A : ℕ → Atom) : ∀ (next : Prop) (kret : List E → Prop),
    Stmt.HoldsList C rd σ ((List.range n).map fun i ↦ .atom (A i)) next kret ↔
      (∀ i < n, (A i).Holds rd σ) ∧ next := by
  induction n with
  | zero => intro next kret; simp [Stmt.HoldsList]
  | succ n ih =>
    intro next kret
    rw [List.range_succ, List.map_append, holdsList_append, ih]
    simp only [List.map_cons, List.map_nil, Stmt.HoldsList, Stmt.Holds]
    constructor
    · rintro ⟨h, h', hn⟩
      refine ⟨fun i hi ↦ ?_, hn⟩
      rcases Nat.lt_or_ge i n with hin | hin
      · exact h i hin
      · obtain rfl : i = n := by omega
        exact h'
    · rintro ⟨h, hn⟩
      exact ⟨fun i hi ↦ h i (by omega), h n (by omega), hn⟩

theorem eq_of_add_eq_zero' {a b : E} (h : a + b = 0) : a = b := by
  have := congrArg (· + b) h
  simpa [add_assoc, e_add_self] using this

/-! ## The product's tables -/

/-- The product section's table, first = 1. -/
def prodTab1 : List PPos := [
    ⟨37, none, 38, [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 13], 47, 58, none, 58⟩,
    ⟨59, none, 60, [1, 3, 5, 7, 10, 13], 69, 74, some 58, 75⟩,
    ⟨76, none, 77, [1, 3, 5, 7, 10, 13], 86, 91, some 75, 92⟩,
    ⟨93, some ([19, 20, 44, 46, 66, 68, 83, 85, 14, 15, 16, 17, 18], 94), 107, [1, 2, 4, 7, 10, 13], 116, 121, some 92, 122⟩,
    ⟨123, none, 124, [1, 4, 5, 7, 8, 10, 11, 13, 14], 133, 141, some 122, 142⟩,
    ⟨143, none, 144, [1, 2, 3, 4, 6, 9, 12], 153, 159, some 142, 160⟩,
    ⟨161, none, 162, [1, 2, 11, 14], 171, 174, some 160, 175⟩,
    ⟨176, some ([113, 115, 130, 132, 150, 152, 168, 170, 102, 103, 104, 105, 106], 177), 190, [1, 2, 3, 4, 5, 8, 9, 10, 12, 13, 14], 199, 209, some 175, 210⟩,
    ⟨211, none, 212, [1, 3, 5, 6, 7, 10, 11, 12], 221, 228, some 210, 229⟩,
    ⟨230, none, 231, [1, 3, 5, 7, 8, 9, 11, 14], 240, 247, some 229, 248⟩,
    ⟨249, none, 250, [1, 2, 4, 6, 8, 9, 10, 11, 12, 13], 259, 268, some 248, 269⟩,
    ⟨270, some ([196, 198, 218, 220, 237, 239, 256, 258, 185, 186, 187, 188, 189], 271), 284, [1, 4, 5, 6, 7, 9, 13, 14], 293, 300, some 269, 301⟩,
    ⟨302, none, 303, [1, 2, 3, 4, 7, 11, 12], 312, 318, some 301, 319⟩,
    ⟨320, none, 321, [1, 2, 7, 8, 9, 10, 11], 330, 336, some 319, 337⟩,
    ⟨338, none, 339, [1, 2, 3, 4, 5, 6, 8, 9], 348, 355, some 337, 356⟩,
    ⟨357, some ([290, 292, 309, 311, 327, 329, 345, 347, 279, 280, 281, 282, 283], 358), 371, [1, 3, 5, 6, 7, 8, 14], 380, 386, some 356, 387⟩,
    ⟨388, none, 389, [1, 3, 5, 6, 8, 12, 13, 14], 398, 405, some 387, 406⟩,
    ⟨407, none, 408, [1, 2, 4, 6, 7, 8, 11, 12, 14], 417, 425, some 406, 426⟩,
    ⟨427, none, 428, [1, 4, 5, 6, 9, 10, 11, 12, 13], 437, 445, some 426, 446⟩,
    ⟨447, some ([377, 379, 395, 397, 414, 416, 434, 436, 366, 367, 368, 369, 370], 448), 461, [1, 2, 3, 4, 9, 11, 13, 14], 470, 477, some 446, 478⟩,
    ⟨479, none, 480, [1, 2, 9, 10, 11, 12, 14], 489, 495, some 478, 496⟩,
    ⟨497, none, 498, [1, 2, 3, 4, 5, 8, 9, 11, 12, 13, 14], 507, 517, some 496, 518⟩,
    ⟨519, none, 520, [1, 3, 5, 6, 7, 8, 9, 10, 12, 14], 529, 538, some 518, 539⟩,
    ⟨540, some ([467, 469, 486, 488, 504, 506, 526, 528, 456, 457, 458, 459, 460], 541), 554, [1, 3, 5, 6, 10, 12, 13, 14], 563, 570, some 539, 571⟩,
    ⟨572, none, 573, [1, 2, 4, 8, 10, 11, 12], 582, 588, some 571, 589⟩,
    ⟨590, none, 591, [1, 4, 5, 6, 7, 8, 9, 11], 600, 607, some 589, 608⟩,
    ⟨609, none, 610, [1, 2, 3, 4, 6, 8, 9, 10, 14], 619, 627, some 608, 628⟩,
    ⟨629, some ([560, 562, 579, 581, 597, 599, 616, 618, 549, 550, 551, 552, 553], 630), 643, [1, 2, 6, 7, 10, 11, 12, 13], 652, 659, some 628, 660⟩,
    ⟨661, none, 662, [1, 2, 3, 4, 5, 7, 8, 9, 13], 671, 679, some 660, 680⟩,
    ⟨681, none, 682, [1, 3, 5, 6, 13, 14], 691, 696, some 680, 697⟩,
    ⟨698, none, 699, [1, 3, 5, 8, 11, 12, 14], 708, 714, some 697, 715⟩,
    ⟨716, some ([649, 651, 668, 670, 688, 690, 705, 707, 638, 639, 640, 641, 642], 717), 730, [1, 2, 4, 6, 7, 9, 10, 12, 13], 739, 747, some 715, 748⟩,
    ⟨749, none, 750, [1, 4, 5, 7, 10, 13], 759, 764, some 748, 765⟩,
    ⟨766, none, 767, [1, 2, 3, 4, 7, 10, 13], 776, 782, some 765, 783⟩,
    ⟨784, none, 785, [1, 2, 7, 10, 13], 794, 798, some 783, 799⟩,
    ⟨800, some ([736, 738, 756, 758, 773, 775, 791, 793, 725, 726, 727, 728, 729], 801), 814, [1, 2, 3, 4, 5, 7, 8, 10, 11, 13, 14], 823, 833, some 799, 834⟩,
    ⟨835, none, 836, [1, 3, 5, 6, 9, 12], 845, 850, some 834, 851⟩,
    ⟨852, none, 853, [1, 3, 5, 11, 14], 862, 866, some 851, 867⟩,
    ⟨868, none, 869, [1, 2, 4, 8, 9, 10, 12, 13, 14], 878, 886, some 867, 887⟩,
    ⟨888, some ([820, 822, 842, 844, 859, 861, 875, 877, 809, 810, 811, 812, 813], 889), 902, [1, 4, 5, 6, 7, 10, 11, 12], 911, 918, some 887, 919⟩,
    ⟨920, none, 921, [1, 2, 3, 4, 7, 8, 9, 11, 14], 930, 938, some 919, 939⟩,
    ⟨940, none, 941, [1, 2, 6, 8, 9, 10, 11, 12, 13], 950, 958, some 939, 959⟩,
    ⟨960, none, 961, [1, 2, 3, 4, 5, 6, 7, 9, 13, 14], 970, 979, some 959, 980⟩,
    ⟨981, some ([908, 910, 927, 929, 947, 949, 967, 969, 897, 898, 899, 900, 901], 982), 995, [1, 3, 5, 7, 11, 12], 1004, 1009, some 980, 1010⟩,
    ⟨1011, none, 1012, [1, 3, 5, 7, 8, 9, 10, 11], 1021, 1028, some 1010, 1029⟩,
    ⟨1030, none, 1031, [1, 2, 4, 6, 8, 9], 1040, 1045, some 1029, 1046⟩,
    ⟨1047, none, 1048, [1, 4, 5, 6, 7, 8, 14, 15], 1057, 1064, some 1046, 1065⟩]


/-- The product section's table, first = 0. -/
def prodTab0 : List PPos := [
    ⟨35, none, 36, [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 13], 45, 56, none, 56⟩,
    ⟨57, none, 58, [1, 3, 5, 7, 10, 13], 67, 72, some 56, 73⟩,
    ⟨74, none, 75, [1, 3, 5, 7, 10, 13], 84, 89, some 73, 90⟩,
    ⟨91, none, 92, [1, 2, 4, 7, 10, 13], 101, 106, some 90, 107⟩,
    ⟨108, some ([42, 44, 64, 66, 81, 83, 98, 100, 14, 15, 16, 17, 18], 109), 122, [1, 4, 5, 7, 8, 10, 11, 13, 14], 131, 139, some 107, 140⟩,
    ⟨141, none, 142, [1, 2, 3, 4, 6, 9, 12], 151, 157, some 140, 158⟩,
    ⟨159, none, 160, [1, 2, 11, 14], 169, 172, some 158, 173⟩,
    ⟨174, none, 175, [1, 2, 3, 4, 5, 8, 9, 10, 12, 13, 14], 184, 194, some 173, 195⟩,
    ⟨196, some ([128, 130, 148, 150, 166, 168, 181, 183, 117, 118, 119, 120, 121], 197), 210, [1, 3, 5, 6, 7, 10, 11, 12], 219, 226, some 195, 227⟩,
    ⟨228, none, 229, [1, 3, 5, 7, 8, 9, 11, 14], 238, 245, some 227, 246⟩,
    ⟨247, none, 248, [1, 2, 4, 6, 8, 9, 10, 11, 12, 13], 257, 266, some 246, 267⟩,
    ⟨268, none, 269, [1, 4, 5, 6, 7, 9, 13, 14], 278, 285, some 267, 286⟩,
    ⟨287, some ([216, 218, 235, 237, 254, 256, 275, 277, 205, 206, 207, 208, 209], 288), 301, [1, 2, 3, 4, 7, 11, 12], 310, 316, some 286, 317⟩,
    ⟨318, none, 319, [1, 2, 7, 8, 9, 10, 11], 328, 334, some 317, 335⟩,
    ⟨336, none, 337, [1, 2, 3, 4, 5, 6, 8, 9], 346, 353, some 335, 354⟩,
    ⟨355, none, 356, [1, 3, 5, 6, 7, 8, 14], 365, 371, some 354, 372⟩,
    ⟨373, some ([307, 309, 325, 327, 343, 345, 362, 364, 296, 297, 298, 299, 300], 374), 387, [1, 3, 5, 6, 8, 12, 13, 14], 396, 403, some 372, 404⟩,
    ⟨405, none, 406, [1, 2, 4, 6, 7, 8, 11, 12, 14], 415, 423, some 404, 424⟩,
    ⟨425, none, 426, [1, 4, 5, 6, 9, 10, 11, 12, 13], 435, 443, some 424, 444⟩,
    ⟨445, none, 446, [1, 2, 3, 4, 9, 11, 13, 14], 455, 462, some 444, 463⟩,
    ⟨464, some ([393, 395, 412, 414, 432, 434, 452, 454, 382, 383, 384, 385, 386], 465), 478, [1, 2, 9, 10, 11, 12, 14], 487, 493, some 463, 494⟩,
    ⟨495, none, 496, [1, 2, 3, 4, 5, 8, 9, 11, 12, 13, 14], 505, 515, some 494, 516⟩,
    ⟨517, none, 518, [1, 3, 5, 6, 7, 8, 9, 10, 12, 14], 527, 536, some 516, 537⟩,
    ⟨538, none, 539, [1, 3, 5, 6, 10, 12, 13, 14], 548, 555, some 537, 556⟩,
    ⟨557, some ([484, 486, 502, 504, 524, 526, 545, 547, 473, 474, 475, 476, 477], 558), 571, [1, 2, 4, 8, 10, 11, 12], 580, 586, some 556, 587⟩,
    ⟨588, none, 589, [1, 4, 5, 6, 7, 8, 9, 11], 598, 605, some 587, 606⟩,
    ⟨607, none, 608, [1, 2, 3, 4, 6, 8, 9, 10, 14], 617, 625, some 606, 626⟩,
    ⟨627, none, 628, [1, 2, 6, 7, 10, 11, 12, 13], 637, 644, some 626, 645⟩,
    ⟨646, some ([577, 579, 595, 597, 614, 616, 634, 636, 566, 567, 568, 569, 570], 647), 660, [1, 2, 3, 4, 5, 7, 8, 9, 13], 669, 677, some 645, 678⟩,
    ⟨679, none, 680, [1, 3, 5, 6, 13, 14], 689, 694, some 678, 695⟩,
    ⟨696, none, 697, [1, 3, 5, 8, 11, 12, 14], 706, 712, some 695, 713⟩,
    ⟨714, none, 715, [1, 2, 4, 6, 7, 9, 10, 12, 13], 724, 732, some 713, 733⟩,
    ⟨734, some ([666, 668, 686, 688, 703, 705, 721, 723, 655, 656, 657, 658, 659], 735), 748, [1, 4, 5, 7, 10, 13], 757, 762, some 733, 763⟩,
    ⟨764, none, 765, [1, 2, 3, 4, 7, 10, 13], 774, 780, some 763, 781⟩,
    ⟨782, none, 783, [1, 2, 7, 10, 13], 792, 796, some 781, 797⟩,
    ⟨798, none, 799, [1, 2, 3, 4, 5, 7, 8, 10, 11, 13, 14], 808, 818, some 797, 819⟩,
    ⟨820, some ([754, 756, 771, 773, 789, 791, 805, 807, 743, 744, 745, 746, 747], 821), 834, [1, 3, 5, 6, 9, 12], 843, 848, some 819, 849⟩,
    ⟨850, none, 851, [1, 3, 5, 11, 14], 860, 864, some 849, 865⟩,
    ⟨866, none, 867, [1, 2, 4, 8, 9, 10, 12, 13, 14], 876, 884, some 865, 885⟩,
    ⟨886, none, 887, [1, 4, 5, 6, 7, 10, 11, 12], 896, 903, some 885, 904⟩,
    ⟨905, some ([840, 842, 857, 859, 873, 875, 893, 895, 829, 830, 831, 832, 833], 906), 919, [1, 2, 3, 4, 7, 8, 9, 11, 14], 928, 936, some 904, 937⟩,
    ⟨938, none, 939, [1, 2, 6, 8, 9, 10, 11, 12, 13], 948, 956, some 937, 957⟩,
    ⟨958, none, 959, [1, 2, 3, 4, 5, 6, 7, 9, 13, 14], 968, 977, some 957, 978⟩,
    ⟨979, none, 980, [1, 3, 5, 7, 11, 12], 989, 994, some 978, 995⟩,
    ⟨996, some ([925, 927, 945, 947, 965, 967, 986, 988, 914, 915, 916, 917, 918], 997), 1010, [1, 3, 5, 7, 8, 9, 10, 11], 1019, 1026, some 995, 1027⟩,
    ⟨1028, none, 1029, [1, 2, 4, 6, 8, 9], 1038, 1043, some 1027, 1044⟩,
    ⟨1045, none, 1046, [1, 4, 5, 6, 7, 8, 14, 15], 1055, 1062, some 1044, 1063⟩]


/-- The product's table of a specialization. -/
def prodTab : ℕ → List PPos
  | 1 => prodTab1
  | _ => prodTab0

/-- The last running sum of the projection. -/
def accL (first : ℕ) : ℕ := if first = 1 then 1065 else 1063

/-! ## Head, check, squeeze, Horner -/

/-- The capacity (and the waiting cells) copied, the instance weights read. -/
def headT (first : ℕ) : List Stmt :=
  (List.range (5 + 2 * first)).map (fun i ↦ .atom (.copy (.n (14 + i)) (.n i))) ++
    (List.range 16).map fun i ↦ .atom (.load (.n (19 + 2 * first + i)) (.n 11) (6 + i))

/-- The projection plus `ι·κ` against the claim's value. -/
def checkT (a : ℕ) : List Stmt :=
  [.atom (.load (.n (a + 1)) (.n 11) 1), .atom (.mul (.n (a + 2)) (.n 13) (.n (a + 1))),
    .atom (.add (.n (a + 3)) (.n a) (.n (a + 2))), .atom (.load (.n (a + 4)) (.n 11) 0),
    .atom (.assertEq (.n (a + 3)) (.n (a + 4)))]

/-- The cells the squeeze of `s` reads. -/
def sqIns : ℕ → List V
  | 1 => [.n 1001, .n 1003, .n 1018, .n 1020, .n 1037, .n 1039, .n 1054, .n 1056,
      .n 990, .n 991, .n 992, .n 993, .n 994]
  | _ => [.n 1016, .n 1018, .n 1035, .n 1037, .n 1052, .n 1054, .n 1068, .n 1069,
      .n 1005, .n 1006, .n 1007, .n 1008, .n 1009]

/-- The squeeze of `s` (`1089`). -/
def sqT (first : ℕ) : List Stmt :=
  (if first = 1 then [] else
    [.atom (.const (.n 1068) (word 0 0 0)), .atom (.const (.n 1069) (word 0 0 0))]) ++
  [keccakA (sqIns first) ((List.range 13).map fun k ↦ .n (1070 + k))] ++
  challengeT (.n 1070) (.n 1071) 1083

/-- The product at `s`, Horner from the top coefficient `a 46`, from the value `b`. -/
def hornerT (a : ℕ → ℕ) (s b : ℕ) : List Stmt :=
  ((List.range 46).map fun j ↦
    [.atom (.mul (.n (b + 2 * j)) (.n (if j = 0 then a 46 else b + 2 * j - 1)) (.n s)),
      .atom (.add (.n (b + 2 * j + 1)) (.n (b + 2 * j)) (.n (a (45 - j))))]).flatten

/-! ## The pack rounds and the local rounds -/

/-- The pack rounds' first record, the loop, and with `odd` the last round. -/
def packSetupT (first odd : ℕ) : List Stmt :=
  [.atom (.load (.n 1308) (.n 11) 2), .atom (.hint (.allocDyn (.n 1309) (.n 8))),
    .atom (.hint (.alloc (.n 1310) 128)),
    .atom (.load (.n 1078) (.n 1310) 0), .atom (.load (.n 1079) (.n 1310) 16),
    .atom (.load (.n 1080) (.n 1310) 32), .atom (.load (.n 1081) (.n 1310) 48),
    .atom (.load (.n 1082) (.n 1310) 64),
    .atom (.const (.n 1311) (word 140737488355328 0 0)), .atom (.mul (.n 1312) (.n 7) (.n 1311)),
    .atom (.load (.n 1312) (.n 1310) 80), .atom (.load (.n 1307) (.n 1310) 96),
    .atom (.const (.n 1313) (word 1 0 0)), .atom (.load (.n 1313) (.n 1310) 112),
    .atom (.const (.n 1314) (word 1 0 0)), .atom (.add (.n 1315) (.n 1314) (.n 9)),
    .atom (.const (.n 1316) (word 1 0 0)),
    .callIf (.n 1315) (packLoopName first odd) [.n 1316, .n 9, .n 1310, .n 1308, .n 1309]] ++
  if odd = 1 then
    [.atom (.mul (.n 1317) (.n 9) (.n 9)), .atom (.mul (.n 1318) (.n 1310) (.n 9)),
      .atom (.mul (.n 1319) (.n 1308) (.n 1317)), .atom (.mul (.n 1320) (.n 1309) (.n 1317)),
      .call "keccak_round" [.n 1318, .n 1319, .n 1320] []]
  else []

/-- The capacity cells from `b`. -/
def cap5 (b : ℕ) : List V := [.n b, .n (b + 1), .n (b + 2), .n (b + 3), .n (b + 4)]

/-- The last record read, the local point allocated. -/
def lastT (d : ℕ) : List Stmt :=
  [.atom (.mul (.n (d + 1317)) (.n 1310) (.n 10))] ++
    (List.range 5).map (fun j ↦ .atom (.load (.n (d + 1318 + j)) (.n (d + 1317)) (16 * j))) ++
    [.atom (.load (.n (d + 1323)) (.n (d + 1317)) 80), .atom (.load (.n (d + 1324)) (.n (d + 1317)) 96),
      .atom (.hint (.alloc (.n (d + 1325)) 11))]

/-- `t`'s three words. -/
def tReadsT (d : ℕ) : List Stmt :=
  fsNextT (.n (d + 1323)) 33 (d + 1986) ++ fsNextT (.n (d + 1323)) 34 (d + 1996) ++
    fsNextT (.n (d + 1323)) 35 (d + 2006)

/-- The lane weights of the local point (`f_lanes[LANE_OFF + i]`). -/
def laneW (d i : ℕ) : ℕ := eqfVal (d + 2016) 5 25 4 i

/-! ## The first claim's weight -/

/-- `Σ_lane f_lanes[lane]·lanes[lane]`, times `Π_t (1 + local_t (1 + g^(2^t)))`, from `B`. -/
def lanesEqT (lp loc : V) (f : ℕ → ℕ) (B : ℕ) : List Stmt :=
  [.atom (.load (.n B) lp 0), .atom (.mul (.n (B + 1)) (.n (f 0)) (.n B))] ++
  ((List.range 24).map fun i ↦
    [.atom (.load (.n (B + 2 + 3 * i)) lp (i + 1)),
      .atom (.mul (.n (B + 3 + 3 * i)) (.n (f (i + 1))) (.n (B + 2 + 3 * i))),
      .atom (.add (.n (B + 4 + 3 * i)) (.n (B + 1 + 3 * i))
        (.n (B + 3 + 3 * i)))]).flatten ++
  ((List.range 6).map fun t ↦
    [.atom (.const (.n (B + 74 + 6 * t)) (word 1 0 0)),
      .atom (.load (.n (B + 75 + 6 * t)) loc t),
      .atom (.const (.n (B + 76 + 6 * t)) (word (2 ^ (2 ^ t) + 1) 0 0)),
      .atom (.mul (.n (B + 77 + 6 * t)) (.n (B + 75 + 6 * t)) (.n (B + 76 + 6 * t))),
      .atom (.add (.n (B + 78 + 6 * t)) (.n (B + 74 + 6 * t)) (.n (B + 77 + 6 * t))),
      .atom (.mul (.n (B + 79 + 6 * t)) (.n (B + 73 + 6 * t)) (.n (B + 78 + 6 * t)))]).flatten

/-! ## A later claim's weight: `keccak_shifts_eq` -/

/-- Bit `t` of the two points from `B`: `a_t`, `b_t`, `a_t b_t`, `a_t + b_t`, `1`, then the
weights `e_t = 1 + a_t + b_t`, `u_t = a_t + a_t b_t`, `v_t = b_t + a_t b_t`. -/
def bitT (aP bP : V) (t B : ℕ) : List Stmt :=
  [.atom (.load (.n B) aP t), .atom (.load (.n (B + 1)) bP t),
    .atom (.mul (.n (B + 2)) (.n B) (.n (B + 1))), .atom (.add (.n (B + 3)) (.n B) (.n (B + 1))),
    .atom (.const (.n (B + 4)) (word 1 0 0)), .atom (.add (.n (B + 5)) (.n (B + 4)) (.n (B + 3))),
    .atom (.add (.n (B + 6)) (.n B) (.n (B + 2))), .atom (.add (.n (B + 7)) (.n (B + 1)) (.n (B + 2)))]

/-- `carry_step(c0, c1, n0, n1, e, u, v, t)` from `B`. -/
def carryT (c0 c1 : ℕ → ℕ) (e u v : ℕ) (t B : ℕ) : List Stmt :=
  [.atom (.mul (.n B) (.n (c0 0)) (.n e)), .atom (.mul (.n (B + 1)) (.n (c0 0)) (.n u)),
    .atom (.mul (.n (B + 2)) (.n (c0 0)) (.n v))] ++
  ((List.range (2 ^ t - 1)).map fun i ↦
    [.atom (.mul (.n (B + 3 + 8 * i)) (.n (c0 (i + 1))) (.n e)),
      .atom (.mul (.n (B + 4 + 8 * i)) (.n (c1 (i + 1))) (.n u)),
      .atom (.add (.n (B + 5 + 8 * i)) (.n (B + 3 + 8 * i)) (.n (B + 4 + 8 * i))),
      .atom (.mul (.n (B + 6 + 8 * i)) (.n (c1 (i + 1))) (.n v)),
      .atom (.mul (.n (B + 7 + 8 * i)) (.n (c0 (i + 1))) (.n u)),
      .atom (.mul (.n (B + 8 + 8 * i)) (.n (c0 (i + 1))) (.n v)),
      .atom (.mul (.n (B + 9 + 8 * i)) (.n (c1 (i + 1))) (.n e)),
      .atom (.add (.n (B + 10 + 8 * i)) (.n (B + 8 + 8 * i)) (.n (B + 9 + 8 * i)))]).flatten

/-- Where `carryT` writes `n0[q]`. -/
def carryN0 (t B q : ℕ) : ℕ :=
  if q = 0 then B else if q = 2 ^ t then B + 1 else if q < 2 ^ t then B + 5 + 8 * (q - 1)
  else B + 7 + 8 * (q - 2 ^ t - 1)

/-- Where `carryT` writes `n1[q]` (`q ≠ 0`). -/
def carryN1 (t B q : ℕ) : ℕ :=
  if q = 2 ^ t then B + 2 else if q < 2 ^ t then B + 6 + 8 * (q - 1)
  else B + 10 + 8 * (q - 2 ^ t - 1)

/-- `carry_wrap(c0, c1, out, e, s, t)` from `B`. -/
def carryWrapT (c0 c1 : ℕ → ℕ) (e s : ℕ) (t B : ℕ) : List Stmt :=
  [.atom (.mul (.n B) (.n (c0 0)) (.n e)), .atom (.mul (.n (B + 1)) (.n (c0 0)) (.n s))] ++
  ((List.range (2 ^ t - 1)).map fun i ↦
    [.atom (.mul (.n (B + 2 + 6 * i)) (.n (c0 (i + 1))) (.n e)),
      .atom (.mul (.n (B + 3 + 6 * i)) (.n (c1 (i + 1))) (.n s)),
      .atom (.add (.n (B + 4 + 6 * i)) (.n (B + 2 + 6 * i)) (.n (B + 3 + 6 * i))),
      .atom (.mul (.n (B + 5 + 6 * i)) (.n (c0 (i + 1))) (.n s)),
      .atom (.mul (.n (B + 6 + 6 * i)) (.n (c1 (i + 1))) (.n e)),
      .atom (.add (.n (B + 7 + 6 * i)) (.n (B + 5 + 6 * i)) (.n (B + 6 + 6 * i)))]).flatten

/-- Where `carryWrapT` writes `out[q]`. -/
def wrapOut (t B q : ℕ) : ℕ :=
  if q = 0 then B else if q = 2 ^ t then B + 1 else if q < 2 ^ t then B + 4 + 6 * (q - 1)
  else B + 7 + 6 * (q - 2 ^ t - 1)

/-- The shifts `keccak_form` uses: `ρ` and `ρ + 1`, ascending (`KECCAK_SHIFT_USED`). -/
def shiftUsed : List ℕ :=
  ((List.range 64).filter fun r ↦ keccakRho.contains r || keccakRho.contains ((r + 63) % 64))

/-- `shifts[r]` for the used `r` from `b`: `low0[r % 8]·high[r / 8]`, plus
`low1[r % 8]·high[r / 8 + 1]` unless `r % 8 = 0`. -/
def shOutT (low0 low1 high : ℕ → ℕ) : List ℕ → ℕ → List Stmt
  | [], _ => []
  | r :: rs, b =>
      if r % 8 = 0 then
        .atom (.mul (.n b) (.n (low0 0)) (.n (high (r / 8)))) :: shOutT low0 low1 high rs (b + 1)
      else
        [.atom (.mul (.n b) (.n (low0 (r % 8))) (.n (high (r / 8)))),
          .atom (.mul (.n (b + 1)) (.n (low1 (r % 8))) (.n (high ((r / 8 + 1) % 8)))),
          .atom (.add (.n (b + 2)) (.n b) (.n (b + 1)))] ++ shOutT low0 low1 high rs (b + 3)

/-- Where `shOutT` writes `shifts[r]`. -/
def shOutV : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | r :: rs, b, q =>
      if r % 8 = 0 then (if q = r then b else shOutV rs (b + 1) q)
      else (if q = r then b + 2 else shOutV rs (b + 3) q)

/-- The bit weights' values from `B0`. -/
def bitEv (B0 t : ℕ) : ℕ := B0 + 8 * t + 5
def bitUv (B0 t : ℕ) : ℕ := B0 + 8 * t + 6
def bitVv (B0 t : ℕ) : ℕ := B0 + 8 * t + 7
def bitSv (B0 t : ℕ) : ℕ := B0 + 8 * t + 3

/-- `keccak_shifts_eq(a, b, shifts)` from `B0`: the six bits, the low carries (bits `1`, `2` on
bit `0`), the high ones (bit `4` on bit `3`, bit `5` wrapping), the used shifts. -/
def shiftsT (aP bP : V) (B0 : ℕ) : List Stmt :=
  ((List.range 6).map fun t ↦ bitT aP bP t (B0 + 8 * t)).flatten ++
  carryT (fun p ↦ if p = 0 then bitEv B0 0 else bitUv B0 0) (fun _ ↦ bitVv B0 0)
    (bitEv B0 1) (bitUv B0 1) (bitVv B0 1) 1 (B0 + 48) ++
  carryT (carryN0 1 (B0 + 48)) (carryN1 1 (B0 + 48)) (bitEv B0 2) (bitUv B0 2) (bitVv B0 2) 2
    (B0 + 59) ++
  carryT (fun p ↦ if p = 0 then bitEv B0 3 else bitUv B0 3) (fun _ ↦ bitVv B0 3)
    (bitEv B0 4) (bitUv B0 4) (bitVv B0 4) 1 (B0 + 86) ++
  carryWrapT (carryN0 1 (B0 + 86)) (carryN1 1 (B0 + 86)) (bitEv B0 5) (bitSv B0 5) 2 (B0 + 97) ++
  shOutT (carryN0 2 (B0 + 59)) (carryN1 2 (B0 + 59)) (wrapOut 2 (B0 + 97)) shiftUsed (B0 + 117)

/-- Where `shiftsT` writes `shifts[r]`. -/
def shiftsV (B0 r : ℕ) : ℕ := shOutV shiftUsed (B0 + 117) r

/-- The value after `shiftsT`. -/
def shiftsEnd (B0 : ℕ) : ℕ := B0 + 227

/-! ## A later claim's weight: `keccak_form` -/

/-- An addition onto a running sum (none: the first term, no statement). -/
def addOpt (o : Option ℕ) (v b : ℕ) : List Stmt × ℕ × ℕ :=
  match o with
  | none => ([], b, v)
  | some t => ([.atom (.add (.n b) (.n t) (.n v))], b + 1, b)

/-- The running sums of `keccak_form`: the total, a column's sums and its `f` sum. -/
structure FAcc where
  tot : Option ℕ
  acc : Option ℕ
  accn : Option ℕ
  facc : Option ℕ

/-- Lane `lane` from `b`: its weight read, `moved`, `f·moved` onto the total, `moved` and the
next shift's product onto the column, `f` onto the column's. -/
def formEnt (lp : V) (sh f : ℕ → ℕ) (lane b : ℕ) (st : FAcc) : List Stmt × ℕ × FAcc :=
  let r1 := addOpt st.tot (b + 2) (b + 3)
  let r2 := addOpt st.acc (b + 1) r1.2.1
  let r3 := addOpt st.accn r2.2.1 (r2.2.1 + 1)
  let r4 := addOpt st.facc (f lane) r3.2.1
  ([.atom (.load (.n b) lp (keccakPi lane)),
    .atom (.mul (.n (b + 1)) (.n b) (.n (sh (keccakRho.getD lane 0)))),
    .atom (.mul (.n (b + 2)) (.n (f lane)) (.n (b + 1)))] ++ r1.1 ++ r2.1 ++
    [.atom (.mul (.n r2.2.1) (.n b) (.n (sh ((keccakRho.getD lane 0 + 1) % 64))))] ++ r3.1 ++ r4.1,
    r4.2.1, ⟨some r1.2.2, some r2.2.2, some r3.2.2, some r4.2.2⟩)

/-- The lanes `x + 5y` of a column, `y ∈ ys`. -/
def formEnts (lp : V) (sh f : ℕ → ℕ) (x : ℕ) : List ℕ → ℕ → FAcc → List Stmt × ℕ × FAcc
  | [], b, st => ([], b, st)
  | y :: ys, b, st =>
      let e := formEnt lp sh f (x + 5 * y) b st
      let r := formEnts lp sh f x ys e.2.1 e.2.2
      (e.1 ++ r.1, r.2.1, r.2.2)

/-- The columns `x ∈ xs`: each one's lanes, then its sums copied (`column`, `column_next`,
`f_column`). Returns the statements, the next value, the total and the copies. -/
def formCols (lp : V) (sh f : ℕ → ℕ) : List ℕ → ℕ → Option ℕ →
    List Stmt × ℕ × Option ℕ × List (ℕ × ℕ × ℕ)
  | [], b, tot => ([], b, tot, [])
  | x :: xs, b, tot =>
      let e := formEnts lp sh f x [0, 1, 2, 3, 4] b ⟨tot, none, none, none⟩
      let b1 := e.2.1
      let r := formCols lp sh f xs (b1 + 3) e.2.2.tot
      (e.1 ++ [.atom (.copy (.n b1) (.n (e.2.2.acc.getD 0))),
          .atom (.copy (.n (b1 + 1)) (.n (e.2.2.accn.getD 0))),
          .atom (.copy (.n (b1 + 2)) (.n (e.2.2.facc.getD 0)))] ++ r.1,
        r.2.1, r.2.2.1, (b1, b1 + 1, b1 + 2) :: r.2.2.2)

/-- The final loop: `total += f_column[x]·(column[x + 1] + column_next[x - 1])`. -/
def formFin (cols : List (ℕ × ℕ × ℕ)) : List ℕ → ℕ → ℕ → List Stmt × ℕ × ℕ
  | [], b, tot => ([], b, tot)
  | x :: xs, b, tot =>
      let r := formFin cols xs (b + 3) (b + 2)
      ([.atom (.add (.n b) (.n (cols.getD ((x + 1) % 5) default).1)
          (.n (cols.getD ((x + 4) % 5) default).2.1)),
        .atom (.mul (.n (b + 1)) (.n (cols.getD x default).2.2) (.n b)),
        .atom (.add (.n (b + 2)) (.n tot) (.n (b + 1)))] ++ r.1, r.2.1, r.2.2)

/-- `keccak_form(lanes, shifts, f_lanes, LANE_OFF)` from `B`: the statements, the next value and
the total's value. -/
def formAll (lp : V) (sh f : ℕ → ℕ) (B : ℕ) : List Stmt × ℕ × ℕ :=
  let c := formCols lp sh f [0, 1, 2, 3, 4] B none
  let r := formFin c.2.2.2 [0, 1, 2, 3, 4] c.2.1 (c.2.2.1.getD 0)
  (c.1 ++ r.1, r.2.1, r.2.2)

/-! ## The weight section and the tail -/

/-- The weight section. -/
def weightT (first d : ℕ) : List Stmt :=
  if first = 1 then
    .atom (.load (.n (d + 2085)) (.n 11) 3) ::
      lanesEqT (.n (d + 2085)) (.n (d + 1325)) (laneW d) (d + 2086)
  else
    [.atom (.load (.n (d + 2085)) (.n 11) 3), .atom (.load (.n (d + 2086)) (.n 11) 4)] ++
      shiftsT (.n (d + 2086)) (.n (d + 1325)) (d + 2087) ++
      (formAll (.n (d + 2085)) (shiftsV (d + 2087)) (laneW d) (shiftsEnd (d + 2087))).1

/-- The weight's value. -/
def weightVal (first d : ℕ) : ℕ :=
  if first = 1 then d + 2195 else (formAll (.n (d + 2085)) (shiftsV (d + 2087)) (laneW d)
    (shiftsEnd (d + 2087))).2.2

/-- The value after the weight section. -/
def weightEnd (first d : ℕ) : ℕ :=
  if first = 1 then d + 2196 else (formAll (.n (d + 2085)) (shiftsV (d + 2087)) (laneW d)
    (shiftsEnd (d + 2087))).2.1

/-- The next claim's lanes: `f[x] + β (f[x - 1] + β f[x - 2])` in each row, from `B`. -/
def lanesOutT (beta : ℕ) (f : ℕ → ℕ) (lp B : ℕ) : List Stmt :=
  ((List.range 25).map fun i ↦
    [.atom (.mul (.n (B + 4 * i)) (.n beta) (.n (f ((i % 5 + 3) % 5 + 5 * (i / 5))))),
      .atom (.add (.n (B + 4 * i + 1)) (.n (f ((i % 5 + 4) % 5 + 5 * (i / 5)))) (.n (B + 4 * i))),
      .atom (.mul (.n (B + 4 * i + 2)) (.n beta) (.n (B + 4 * i + 1))),
      .atom (.add (.n (B + 4 * i + 3)) (.n (f i)) (.n (B + 4 * i + 2))),
      .atom (.load (.n (B + 4 * i + 3)) (.n lp) i)]).flatten

/-- The final check, the squeeze of `β`, the next claim's record, the return; `W` the first value,
`wv` the weight's. -/
def tailT (d W wv : ℕ) : List Stmt :=
  [.atom (.copy (.n W) (.n wv)), .atom (.load (.n (W + 1)) (.n (d + 1317)) 112),
    .atom (.mul (.n (W + 2)) (.n (W + 1)) (.n W)),
    .atom (.mul (.n (W + 3)) (.n 1215) (.n (d + 1986))),
    .atom (.add (.n (W + 4)) (.n 1215) (.n (d + 1996))),
    .atom (.mul (.n (W + 5)) (.n (W + 4)) (.n (d + 2006))),
    .atom (.add (.n (W + 6)) (.n (W + 3)) (.n (W + 5))),
    .atom (.mul (.n (W + 7)) (.n (W + 2)) (.n (W + 6))),
    .atom (.assertEq (.n (W + 7)) (.n (d + 1985))),
    .atom (.const (.n (W + 8)) (word 0 0 0)), .atom (.const (.n (W + 9)) (word 0 0 0)),
    keccakA ([.n (d + 1993), .n (d + 1995), .n (d + 2003), .n (d + 2005), .n (d + 2013),
      .n (d + 2015), .n (W + 8), .n (W + 9)] ++ cap5 (d + 1966))
      ((List.range 13).map fun k ↦ .n (W + 10 + k))] ++
  challengeT (.n (W + 10)) (.n (W + 11)) (W + 23) ++
  [.atom (.mul (.n (W + 30)) (.n (W + 29)) (.n (d + 2006))),
    .atom (.add (.n (W + 31)) (.n (d + 1996)) (.n (W + 30))),
    .atom (.mul (.n (W + 32)) (.n (W + 29)) (.n (W + 31))),
    .atom (.add (.n (W + 33)) (.n (d + 1986)) (.n (W + 32))),
    .atom (.load (.n (W + 33)) (.n 12) 0), .atom (.load (.n 1309) (.n 12) 2),
    .atom (.load (.n (d + 1325)) (.n 12) 4), .atom (.hint (.alloc (.n (W + 34)) 25))] ++
  lanesOutT (W + 29) (laneW d) (W + 34) (W + 35) ++
  [.atom (.load (.n (W + 34)) (.n 12) 3)] ++
  eqfT (.n (d + 1325)) 0 6 64 (W + 135) ++
  [.atom (.hint (.alloc (.n (W + 278)) 64))] ++
  (List.range 64).map (fun z ↦ .atom (.load (.n (eqfVal (W + 135) 6 64 5 z)) (.n (W + 278)) z)) ++
  [.atom (.load (.n (W + 278)) (.n 12) 5)] ++
  (List.range 5).map (fun j ↦ .atom (.copy (.n (W + 279 + j)) (.n (W + 18 + j)))) ++
  [.atom (.const (.n (W + 284)) (word 68719476736 0 0)),
    .atom (.mul (.n (W + 285)) (.n (d + 1323)) (.n (W + 284))),
    .atom (.copy (.n (W + 286)) (.n (W + 285))),
    .ret [.n (W + 279), .n (W + 280), .n (W + 281), .n (W + 282), .n (W + 283), .n (W + 286)]]

/-! ## The template -/

/-- **`keccak_layer__L{first}_L{odd}`'s body.** -/
def layerT (first odd : ℕ) : List Stmt :=
  headT first ++ prodT (.n 7) (19 + 2 * first) (prodTab first) ++ checkT (accL first) ++
    sqT first ++ rmfeBlockT ++ hornerT (fun k ↦ ((prodTab first).getD k default).a) 1089 1216 ++
    packSetupT first odd ++ lastT (4 * odd) ++
    localRoundsT (.n (4 * odd + 1323)) (.n (4 * odd + 1325)) (.n (4 * odd + 1324))
      (cap5 (4 * odd + 1318)) (4 * odd + 1326) 11 ++
    tReadsT (4 * odd) ++ eqfT (.n (4 * odd + 1325)) 6 5 25 (4 * odd + 2016) ++
    weightT first (4 * odd) ++
    tailT (4 * odd) (weightEnd first (4 * odd)) (weightVal first (4 * odd))

end
end LeanVM.Guest.B1.VerifySub
