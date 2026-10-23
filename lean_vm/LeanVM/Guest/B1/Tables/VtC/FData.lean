/-
  LeanVM.Guest.B1.Tables.VtC.FData

  The statements of the window `5259 ..< 10208` that evaluation alone does not settle, by kind:
  each evaluation's read, limb check and two stores, the permutations, and each table's `dims`
  read, weight division and two weight reads; the kernel checks that they and the reads of
  `fp_w` cover the window.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FBase
public import LeanVM.Guest.B1.Tables.Vt.EvalsT

/-!
# The window's statements, by kind

`vtAirD[t]`: table `t`'s `dims` read (position, value `τv`) and weight block (position, value
`x`): `g^n = x·τv` (a division), `cprod` read at `zc_cprod·x`, `peq` read at `zc_peq·τv`
(`vtAirT`). `vtEvTab k`: evaluation `k`'s table. `vtEvRest k`: evaluation `k`'s read at the
cursor, limb check, `claim_pool` and `claim_cplen_g` stores. `vtFR`: all of them, the
permutations and the tables' statements; `vtF_cover`: every statement of the window is settled by
evaluation (`autoB`), a read of `fp_w` (`rd14`) or one of `vtFR`. `noStoreB p`: no store goes
through the pointer `.n p`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The tables' `dims` reads and weight blocks: positions and first values. -/
def vtAirD : List (ℕ × ℕ × ℕ × ℕ) :=
  [(5259, 5938, 5683, 6383), (5690, 6390, 6155, 6888), (6163, 6896, 6402, 7151),
    (6410, 7159, 6869, 7651), (6877, 7659, 7318, 8122), (7326, 8130, 10200, 11190)]

/-- Table `t`'s `g^τ` value. -/
def vtTauV (t : ℕ) : ℕ := (vtAirD.getD t (0, 0, 0, 0)).2.1

/-- Table `t`'s weight block's first value. -/
def vtAirX (t : ℕ) : ℕ := (vtAirD.getD t (0, 0, 0, 0)).2.2.2

/-- Table `t`'s `dims` read. -/
def vtDimT (t : ℕ) : Stmt := .atom (.load (.n (vtTauV t)) (.n 10) (t + 1))

/-- Table `t`'s weight block. -/
def vtAirT (t : ℕ) : List Stmt :=
  [.atom (.mul (.n 5817) (.n (vtAirX t)) (.n (vtTauV t))),
    .atom (.mul (.n (vtAirX t + 1)) (.n 5915) (.n (vtAirX t))),
    .atom (.load (.n (vtAirX t + 2)) (.n (vtAirX t + 1)) 0),
    .atom (.mul (.n (vtAirX t + 3)) (.n 5936) (.n (vtTauV t))),
    .atom (.load (.n (vtAirX t + 4)) (.n (vtAirX t + 3)) 0)]

theorem vtAirT_check : ∀ t < 6,
    tbStmtsEqb [vtDimT t] ((vtPre.drop (vtAirD.getD t (0, 0, 0, 0)).1).take 1) = true ∧
      tbStmtsEqb (vtAirT t) ((vtPre.drop (vtAirD.getD t (0, 0, 0, 0)).2.2.1).take 5) = true := by
  decide +kernel

/-- Evaluation `k`'s table. -/
def vtEvTab (k : ℕ) : ℕ :=
  ((List.range 6).map vtTauV).idxOf (vtEvalData.getD k (0, 0, 0)).2.2

theorem vtEvTab_spec : ∀ k < 157,
    vtEvTab k < 6 ∧ vtTauV (vtEvTab k) = (vtEvalData.getD k (0, 0, 0)).2.2 := by
  decide +kernel

/-- Evaluation `k`'s statements evaluation alone does not settle. -/
def vtEvRest (k : ℕ) : List Stmt :=
  [.atom (.load (.n (vtEvB k)) (.n 5932) k),
    .atom (.assertInK (.n (vtEvB k + 3)) (.n (vtEvB k + 4))),
    .atom (.load (.n (vtEvB k)) (.n 16) (5 + k)),
    .atom (.load (.n (vtEvalData.getD k (0, 0, 0)).2.2) (.n 17) (5 + k))]

/-- A read of `fp_w`. -/
def rd14 : Stmt → Bool
  | .atom (.load _ (.n 14) _) => true
  | _ => false

/-- A kind of statement to settle: an evaluation's (`0`), a permutation (`1`), a `dims` read
(`2`), a weight block's (`3`). -/
def vtFTagT : ℕ × ℕ → List Stmt
  | (0, k) => vtEvRest k
  | (1, j) => [vtPermT j]
  | (2, t) => [vtDimT t]
  | (_, t) => (vtAirT t).filter fun s ↦ !autoB s

/-- The window's statements to settle, in order. -/
def vtFTags : List (ℕ × ℕ) := [
    (2, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (0, 4), (0, 5), (0, 6), (0, 7), (1, 1), (0, 8),
    (0, 9), (0, 10), (0, 11), (1, 2), (0, 12), (0, 13), (0, 14), (3, 0), (2, 1), (0, 15), (1, 3),
    (0, 16), (0, 17), (0, 18), (0, 19), (1, 4), (0, 20), (0, 21), (0, 22), (0, 23), (1, 5), (0, 24),
    (0, 25), (0, 26), (0, 27), (1, 6), (0, 28), (0, 29), (3, 1), (2, 2), (0, 30), (0, 31), (1, 7),
    (0, 32), (0, 33), (0, 34), (0, 35), (1, 8), (0, 36), (0, 37), (3, 2), (2, 3), (0, 38), (0, 39),
    (1, 9), (0, 40), (0, 41), (0, 42), (0, 43), (1, 10), (0, 44), (0, 45), (0, 46), (0, 47), (1,
    11), (0, 48), (0, 49), (0, 50), (0, 51), (1, 12), (0, 52), (3, 3), (2, 4), (0, 53), (0, 54), (0,
    55), (1, 13), (0, 56), (0, 57), (0, 58), (0, 59), (1, 14), (0, 60), (0, 61), (0, 62), (0, 63),
    (1, 15), (0, 64), (0, 65), (0, 66), (3, 4), (2, 5), (0, 67), (1, 16), (0, 68), (0, 69), (0, 70),
    (0, 71), (1, 17), (0, 72), (0, 73), (0, 74), (0, 75), (1, 18), (0, 76), (0, 77), (0, 78), (0,
    79), (1, 19), (0, 80), (0, 81), (0, 82), (0, 83), (1, 20), (0, 84), (0, 85), (0, 86), (0, 87),
    (1, 21), (0, 88), (0, 89), (0, 90), (0, 91), (1, 22), (0, 92), (0, 93), (0, 94), (0, 95), (1,
    23), (0, 96), (0, 97), (0, 98), (0, 99), (1, 24), (0, 100), (0, 101), (0, 102), (0, 103), (1,
    25), (0, 104), (0, 105), (0, 106), (0, 107), (1, 26), (0, 108), (0, 109), (0, 110), (0, 111),
    (1, 27), (0, 112), (0, 113), (0, 114), (0, 115), (1, 28), (0, 116), (0, 117), (0, 118), (0,
    119), (1, 29), (0, 120), (0, 121), (0, 122), (0, 123), (1, 30), (0, 124), (0, 125), (0, 126),
    (0, 127), (1, 31), (0, 128), (0, 129), (0, 130), (0, 131), (1, 32), (0, 132), (0, 133), (0,
    134), (0, 135), (1, 33), (0, 136), (0, 137), (0, 138), (0, 139), (1, 34), (0, 140), (0, 141),
    (0, 142), (0, 143), (1, 35), (0, 144), (0, 145), (0, 146), (0, 147), (1, 36), (0, 148), (0,
    149), (0, 150), (0, 151), (1, 37), (0, 152), (0, 153), (0, 154), (0, 155), (1, 38), (0, 156),
    (3, 5)]

theorem vtF_cover : tbStmtsEqb (((vtPre.drop vtFLo).take (vtFHi - vtFLo)).filter
    (fun s ↦ !(autoB s || rd14 s))) (vtFTags.flatMap vtFTagT) = true := by
  decide +kernel

theorem vtFTags_spec : ∀ q ∈ vtFTags, (q.1 = 0 ∧ q.2 < 157) ∨ (q.1 = 1 ∧ q.2 < 39) ∨
    ((q.1 = 2 ∨ q.1 = 3) ∧ q.2 < 6) := by
  decide +kernel

/-- No store goes through the pointer `.n p`. -/
def noStoreB (p : ℕ) : Bool :=
  vtSL.all fun a ↦ match a with
    | .load _ (.n q) _ => q != p
    | _ => true

theorem not_mem_vtSL {p : ℕ} (h : noStoreB p = true) (d : V) (off : ℕ) :
    Atom.load d (.n p) off ∉ vtSL := fun hm ↦ by
  have := List.all_eq_true.mp h _ hm
  simp at this

theorem vtF_noStore : noStoreB 14 = true ∧ noStoreB 5932 = true ∧
    ∀ t < 6, noStoreB (vtAirX t + 1) = true ∧ noStoreB (vtAirX t + 3) = true := by
  decide +kernel

theorem vtF_dimsRead : ∀ t < 6, Atom.load (.n (vtTauV t)) (.n 10) (t + 1) ∉ vtSL := by
  decide +kernel

theorem vtF_loadsBelow : loadsBelow [(14, 14), (5932, 157)] = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables
