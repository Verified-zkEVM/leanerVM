/-
  LeanVM.Guest.B1.Tables.Vt.SelBlocks

  `verify_tables`' table blocks' selectors on the push and the count side, through each table's
  shared nibble tables (`block_selector_tab`).
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SelMath

/-!
# The table blocks' selectors (G:2045-2061)

A table block `b` of table `t` (`vtSelT`): its `block_kappa` cell below `g^34`, its offset's bits
hinted, the `block_selector_tab` arm `μ - τ_t` on the bits shifted by `τ_t` and the table's shared
tables, the returned `g`-power asserted to be the block's `block_off_g`, and the running
`selector_sum`. `vtPushSel`, `vtCountSel` list the push side's blocks `3 .. 53` and the count
side's `108 .. 152`: block, first statement, first value, table, the previous running sum.
`vt_selblock`: the block's eq weight is `eqAbove ⟨τ_t, offset⟩` at the bus point.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `block_selector_tab`'s 34 arms. -/
def vtBstNames : List String := (List.range 34).map (lName "block_selector_tab")

/-- `2^34`'s word: the offset bits' buffer, `g^34` words. -/
abbrev vtW34 : E := word 17179869184 0 0

/-- The eq weight's value of a block from `w`, table `t`. -/
def vtSelE (w t : ℕ) : ℕ := if t = 0 then w + 10 else w + 14

/-- A table block's running sum and copy. -/
def vtSelTail (w t : ℕ) : Option ℕ → List Stmt
  | none => [.atom (.copy (.n (vtSelE w t + 3)) (.n (vtSelE w t)))]
  | some p => [.atom (.add (.n (vtSelE w t + 3)) (.n p) (.n (vtSelE w t))),
      .atom (.copy (.n (vtSelE w t + 4)) (.n (vtSelE w t)))]

/-- A table block's statements. -/
def vtSelT (w b t : ℕ) (prev : Option ℕ) : List Stmt :=
  [.atom (.load (.n w) (.n 12) b), .atom (.const (.n (w + 1)) vtW33),
    .atom (.rangeCheck (.n w) (.n (w + 2)) (.n (w + 3)) (.n (w + 4)) (.n (w + 1))),
    .atom (.const (.n (w + 5)) vtW34), .atom (.hint (.allocDyn (.n (w + 6)) (.n (w + 5)))),
    .atom (.load (.n (w + 7)) (.n 185) b),
    .atom (.hint (.bitsExp (.n (w + 7)) 34 (.heap (.n (w + 6)) 0 34))),
    .atom (.load (.n (w + 8)) (.n 10) (t + 1)), .atom (.mul (.n (w + 9)) (.n (w + 6)) (.n (w + 8)))] ++
  (if t = 0 then [] else
    [.atom (.const (.n (w + 10)) (word (vtShC1.getD t 0) 0 0)),
      .atom (.mul (.n (w + 11)) (.n 2769) (.n (w + 10))),
      .atom (.const (.n (w + 12)) (word (vtShC2.getD t 0) 0 0)),
      .atom (.mul (.n (w + 13)) (.n 2770) (.n (w + 12)))]) ++
  [.dispatch (.n (vtShLen t)) vtBstNames [.n (w + 9), .n (if t = 0 then 2769 else w + 11),
      .n (if t = 0 then 2770 else w + 13)] [.n (vtSelE w t), .n (vtSelE w t + 1)],
    .atom (.load (.n (vtSelE w t + 2)) (.n 185) b),
    .atom (.assertEq (.n (vtSelE w t + 1)) (.n (vtSelE w t + 2)))] ++ vtSelTail w t prev

def vtPushSel : List (ℕ × ℕ × ℕ × ℕ × Option ℕ) :=
  [(3, 2586, 3037, 0, some 2978), (4, 2600, 3052, 0, some 3050),
    (5, 2614, 3067, 0, some 3065), (6, 2628, 3082, 0, some 3080),
    (7, 2642, 3097, 0, some 3095), (8, 2656, 3112, 1, some 3110),
    (9, 2674, 3131, 1, some 3129), (10, 2692, 3150, 1, some 3148),
    (11, 2710, 3169, 1, some 3167), (12, 2728, 3188, 1, some 3186),
    (13, 2746, 3207, 2, some 3205), (14, 2764, 3226, 2, some 3224),
    (15, 2782, 3245, 2, some 3243), (16, 2800, 3264, 3, some 3262),
    (17, 2818, 3283, 3, some 3281), (18, 2836, 3302, 3, some 3300),
    (19, 2854, 3321, 3, some 3319), (20, 2872, 3340, 3, some 3338),
    (21, 2890, 3359, 4, some 3357), (22, 2908, 3378, 4, some 3376),
    (23, 2926, 3397, 4, some 3395), (24, 2944, 3416, 4, some 3414),
    (25, 2962, 3435, 4, some 3433), (26, 2980, 3454, 5, some 3452),
    (27, 2998, 3473, 5, some 3471), (28, 3016, 3492, 5, some 3490),
    (29, 3034, 3511, 5, some 3509), (30, 3052, 3530, 5, some 3528),
    (31, 3070, 3549, 5, some 3547), (32, 3088, 3568, 5, some 3566),
    (33, 3106, 3587, 5, some 3585), (34, 3124, 3606, 5, some 3604),
    (35, 3142, 3625, 5, some 3623), (36, 3160, 3644, 5, some 3642),
    (37, 3178, 3663, 5, some 3661), (38, 3196, 3682, 5, some 3680),
    (39, 3214, 3701, 5, some 3699), (40, 3232, 3720, 5, some 3718),
    (41, 3250, 3739, 5, some 3737), (42, 3268, 3758, 5, some 3756),
    (43, 3286, 3777, 5, some 3775), (44, 3304, 3796, 5, some 3794),
    (45, 3322, 3815, 5, some 3813), (46, 3340, 3834, 5, some 3832),
    (47, 3358, 3853, 5, some 3851), (48, 3376, 3872, 5, some 3870),
    (49, 3394, 3891, 5, some 3889), (50, 3412, 3910, 5, some 3908),
    (51, 3430, 3929, 5, some 3927), (52, 3448, 3948, 5, some 3946),
    (53, 3466, 3967, 5, some 3965)]

def vtCountSel : List (ℕ × ℕ × ℕ × ℕ × Option ℕ) :=
  [(108, 4305, 4925, 0, none), (109, 4318, 4939, 0, some 4935),
    (110, 4332, 4954, 0, some 4952), (111, 4346, 4969, 0, some 4967),
    (112, 4360, 4984, 1, some 4982), (113, 4378, 5003, 1, some 5001),
    (114, 4396, 5022, 1, some 5020), (115, 4414, 5041, 1, some 5039),
    (116, 4432, 5060, 2, some 5058), (117, 4450, 5079, 2, some 5077),
    (118, 4468, 5098, 3, some 5096), (119, 4486, 5117, 3, some 5115),
    (120, 4504, 5136, 3, some 5134), (121, 4522, 5155, 3, some 5153),
    (122, 4540, 5174, 4, some 5172), (123, 4558, 5193, 4, some 5191),
    (124, 4576, 5212, 4, some 5210), (125, 4594, 5231, 4, some 5229),
    (126, 4612, 5250, 5, some 5248), (127, 4630, 5269, 5, some 5267),
    (128, 4648, 5288, 5, some 5286), (129, 4666, 5307, 5, some 5305),
    (130, 4684, 5326, 5, some 5324), (131, 4702, 5345, 5, some 5343),
    (132, 4720, 5364, 5, some 5362), (133, 4738, 5383, 5, some 5381),
    (134, 4756, 5402, 5, some 5400), (135, 4774, 5421, 5, some 5419),
    (136, 4792, 5440, 5, some 5438), (137, 4810, 5459, 5, some 5457),
    (138, 4828, 5478, 5, some 5476), (139, 4846, 5497, 5, some 5495),
    (140, 4864, 5516, 5, some 5514), (141, 4882, 5535, 5, some 5533),
    (142, 4900, 5554, 5, some 5552), (143, 4918, 5573, 5, some 5571),
    (144, 4936, 5592, 5, some 5590), (145, 4954, 5611, 5, some 5609),
    (146, 4972, 5630, 5, some 5628), (147, 4990, 5649, 5, some 5647),
    (148, 5008, 5668, 5, some 5666), (149, 5026, 5687, 5, some 5685),
    (150, 5044, 5706, 5, some 5704), (151, 5062, 5725, 5, some 5723),
    (152, 5080, 5744, 5, some 5742)]

theorem vtPushSel_check : ∀ i < vtPushSel.length,
    tbStmtsEqb (vtSelT (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).1
        (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2)
      ((vtPre.drop (vtPushSel.getD i default).2.1).take
        (vtSelT (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).1
          (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2).length) = true := by
  decide +kernel

theorem vtCountSel_check : ∀ i < vtCountSel.length,
    tbStmtsEqb (vtSelT (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).1
        (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2)
      ((vtPre.drop (vtCountSel.getD i default).2.1).take
        (vtSelT (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).1
          (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2).length) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Tables
