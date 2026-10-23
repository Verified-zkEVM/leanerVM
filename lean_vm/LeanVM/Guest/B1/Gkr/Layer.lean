/-
  LeanVM.Guest.B1.Gkr.Layer

  A layer of `verify_bus_gkr`'s walk, its loop `__loop7`: one step of two levels of the
  specification's GKR walk, between two layer slots.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop29

/-!
# A layer of two levels (`__loop7`, G:1689-1777)

The template of `__loop7`'s body, from the layer slot at `layers·x_layer^17`: the combiner's
permutation over the slot's capacity and waiting cells, the first round record, the rounds
(`__loop29`, then `gkr_rounds__L2` at an odd layer index, then `gkr_rounds__L1` at an odd depth),
the twelve children read, their check, the two new coordinates squeezed, and the next slot
`34` words on.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The first value of child `i`'s read. -/
def lyEv (i : ℕ) : ℕ := if i < 4 then 81 + 11 * i else if i < 8 then 138 + 11 * (i - 4) else 195 + 11 * (i - 8)

/-- Child `i`'s read: `fs_next` at the tail cursor, its word copied. -/
def lyEvT (i : ℕ) : List Stmt :=
  tbxFsNextT (.n 79) i (lyEv i) ++ [.atom (.copy (.n (lyEv i + 10)) (.n (lyEv i)))]

/-- The rate cells of children `4m .. 4m + 3`. -/
def lyRate (m : ℕ) : List V :=
  (List.range 4).flatMap fun i ↦ [.n (lyEv (4 * m + i) + 7), .n (lyEv (4 * m + i) + 9)]

/-- A run of `13` values from `b`. -/
def lyOuts (b : ℕ) : List V := (List.range 13).map fun k ↦ .n (b + k)

/-- The capacity cells among a permutation's outputs from `b`. -/
def lyCap (b : ℕ) : List V := (List.range 5).map fun k ↦ .n (b + 8 + k)

/-- The side `t`'s new value: `lo + c1·(lo + hi)`, its values from `b`. -/
def lyVal (t b off : ℕ) : List Stmt :=
  let e := fun i ↦ lyEv (4 * t + i) + 10
  [.atom (.add (.n b) (.n (e 0)) (.n (e 1))), .atom (.mul (.n (b + 1)) (.n 274) (.n b)),
    .atom (.add (.n (b + 2)) (.n (e 0)) (.n (b + 1))),
    .atom (.add (.n (b + 3)) (.n (e 2)) (.n (e 3))), .atom (.mul (.n (b + 4)) (.n 274) (.n (b + 3))),
    .atom (.add (.n (b + 5)) (.n (e 2)) (.n (b + 4))),
    .atom (.add (.n (b + 6)) (.n (b + 2)) (.n (b + 5))), .atom (.mul (.n (b + 7)) (.n 294) (.n (b + 6))),
    .atom (.add (.n (b + 8)) (.n (b + 2)) (.n (b + 7))), .atom (.load (.n (b + 8)) (.n 15) off)]

/-- `__loop7`'s body. -/
def lyBody : List Stmt :=
  [.atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 2) (.n 3)),
    .atom (.load (.n 8) (.n 7) 0), .atom (.mul (.n 9) (.n 6) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.mul (.n 12) (.n 11) (.n 11)), .atom (.mul (.n 13) (.n 12) (.n 12)),
    .atom (.mul (.n 14) (.n 13) (.n 9)), .atom (.mul (.n 15) (.n 4) (.n 14))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (16 + k)) (.n 15) k)) ++
  (List.range 4).map (fun k ↦ .atom (.load (.n (21 + k)) (.n 15) (13 + k))) ++
  [.atom (.const (.n 25) (word 1 0 0)), .atom (.const (.n 26) (word 0 0 0)),
    .atom (.const (.n 27) (word 0 0 0)), .atom (.const (.n 28) (word 0 0 0)),
    .atom (.const (.n 29) (word 0 0 0)),
    tbxKeccakA ([.n 21, .n 22, .n 23, .n 24, .n 26, .n 27, .n 28, .n 29] ++
      (List.range 5).map fun k ↦ .n (16 + k)) (lyOuts 30)] ++
  tbxChallengeT (.n 30) (.n 31) 43 ++
  [.atom (.load (.n 50) (.n 15) 9), .atom (.load (.n 51) (.n 15) 10),
    .atom (.mul (.n 52) (.n 5) (.n 51))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (38 + k)) (.n 52) (862 * k))) ++
  [.atom (.load (.n 53) (.n 15) 5), .atom (.load (.n 53) (.n 52) 4310),
    .atom (.load (.n 54) (.n 15) 6), .atom (.load (.n 55) (.n 15) 7),
    .atom (.load (.n 56) (.n 15) 8), .atom (.mul (.n 57) (.n 49) (.n 56)),
    .atom (.add (.n 58) (.n 55) (.n 57)), .atom (.mul (.n 59) (.n 49) (.n 58)),
    .atom (.add (.n 60) (.n 54) (.n 59)), .atom (.load (.n 60) (.n 52) 5172),
    .atom (.load (.n 61) (.n 15) 11), .atom (.load (.n 62) (.n 15) 12),
    .atom (.const (.n 63) (word 1 0 0)), .atom (.add (.n 64) (.n 63) (.n 61)),
    .atom (.const (.n 65) (word 1 0 0)),
    .callIf (.n 64) "__loop29" [.n 65, .n 61, .n 52, .n 50],
    .ite (.n 62) [] [.atom (.mul (.n 66) (.n 61) (.n 61)), .atom (.mul (.n 67) (.n 66) (.n 66)),
      .atom (.mul (.n 68) (.n 52) (.n 67)), .atom (.mul (.n 69) (.n 50) (.n 67)),
      .call "gkr_rounds__L2" [.n 68, .n 69] []],
    .atom (.add (.n 70) (.n 9) (.n 6)),
    .ite (.n 70) [] [.atom (.mul (.n 71) (.n 52) (.n 6)), .atom (.mul (.n 72) (.n 50) (.n 6)),
      .call "gkr_rounds__L1" [.n 71, .n 72] []],
    .atom (.mul (.n 73) (.n 52) (.n 9))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (74 + k)) (.n 73) (862 * k))) ++
  [.atom (.load (.n 79) (.n 73) 4310), .atom (.load (.n 80) (.n 73) 5172)] ++
  ((List.range 4).map lyEvT).flatten ++
  [tbxKeccakA (lyRate 0 ++ (List.range 5).map fun k ↦ .n (74 + k)) (lyOuts 125)] ++
  ((List.range 4).map fun i ↦ lyEvT (4 + i)).flatten ++
  [tbxKeccakA (lyRate 1 ++ lyCap 125) (lyOuts 182)] ++
  ((List.range 4).map fun i ↦ lyEvT (8 + i)).flatten ++
  [.atom (.mul (.n 239) (.n 205) (.n 216)), .atom (.mul (.n 240) (.n 239) (.n 227)),
    .atom (.mul (.n 241) (.n 240) (.n 238)), .atom (.const (.n 242) (word 0 0 0)),
    .atom (.mul (.n 243) (.n 49) (.n 242)), .atom (.add (.n 244) (.n 241) (.n 243)),
    .atom (.mul (.n 245) (.n 148) (.n 159)), .atom (.mul (.n 246) (.n 245) (.n 170)),
    .atom (.mul (.n 247) (.n 246) (.n 181)), .atom (.mul (.n 248) (.n 49) (.n 244)),
    .atom (.add (.n 249) (.n 247) (.n 248)), .atom (.mul (.n 250) (.n 91) (.n 102)),
    .atom (.mul (.n 251) (.n 250) (.n 113)), .atom (.mul (.n 252) (.n 251) (.n 124)),
    .atom (.mul (.n 253) (.n 49) (.n 249)), .atom (.add (.n 254) (.n 252) (.n 253)),
    .atom (.assertEq (.n 80) (.n 254)),
    tbxKeccakA (lyRate 2 ++ lyCap 182) (lyOuts 255)] ++
  tbxChallengeT (.n 255) (.n 256) 268 ++
  [tbxKeccakA ([.n 26, .n 26, .n 26, .n 26, .n 26, .n 27, .n 28, .n 29] ++ lyCap 255) (lyOuts 275)] ++
  tbxChallengeT (.n 275) (.n 276) 288 ++
  [.atom (.load (.n 274) (.n 50) 40), .atom (.load (.n 294) (.n 50) 41)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (283 + k)) (.n 15) (34 + k))) ++
  ((List.range 4).map fun k ↦ [.atom (.const (.n (295 + k)) (word 0 0 0)),
    .atom (.load (.n (295 + k)) (.n 15) (47 + k))]).flatten ++
  [.atom (.const (.n 299) (word 4096 0 0)), .atom (.mul (.n 300) (.n 79) (.n 299)),
    .atom (.load (.n 300) (.n 15) 39)] ++
  lyVal 0 301 40 ++ lyVal 1 310 41 ++ lyVal 2 319 42 ++
  [.atom (.const (.n 328) (word 1099511627776 0 0)), .atom (.mul (.n 329) (.n 50) (.n 328)),
    .atom (.load (.n 329) (.n 15) 43), .atom (.mul (.n 330) (.n 51) (.n 9)),
    .atom (.const (.n 331) (word 2 0 0)), .atom (.mul (.n 332) (.n 330) (.n 331)),
    .atom (.load (.n 332) (.n 15) 44), .atom (.const (.n 333) (word 1 0 0)),
    .atom (.const (.n 334) (word 3 0 0)), .atom (.mul (.n 335) (.n 62) (.n 334)),
    .atom (.add (.n 336) (.n 333) (.n 335)), .atom (.mul (.n 337) (.n 61) (.n 336)),
    .atom (.load (.n 337) (.n 15) 45), .atom (.const (.n 338) (word 1 0 0)),
    .atom (.add (.n 339) (.n 338) (.n 62)), .atom (.load (.n 339) (.n 15) 46),
    .atom (.const (.n 340) (word 2 0 0)), .atom (.mul (.n 341) (.n 0) (.n 340)),
    .atom (.add (.n 342) (.n 341) (.n 1)), .atom (.const (.n 343) (word 2 0 0)),
    .atom (.mul (.n 344) (.n 0) (.n 343)),
    .callIf (.n 342) "__loop7" [.n 344, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []]

noncomputable def lyCheck : Bool :=
  match coreProgram.find? "__loop7" with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]) && tbStmtsEqb fn.body lyBody
  | none => false

theorem lyCheck_eq : lyCheck = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables
