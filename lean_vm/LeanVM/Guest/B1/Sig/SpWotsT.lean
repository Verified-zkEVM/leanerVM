/-
  LeanVM.Guest.B1.Sig.SpWotsT

  The body of `sp_wots` as a template, written from the guest's structure
  (`lean_ethereum.py:3600-3631` at leanVM 542b0353) with the values numbered as the renumbered
  expansion numbers them.
-/

module

public import LeanVM.Guest.B1.Sig.WotsT

/-!
# `sp_wots` as a template

`sp_wots(pp, at, encoding)` (`G:3600-3631`; `G` is `lean_ethereum.py`) has the parameters `pp = n0`,
`at = n1` (the one-time key's address: its leaf in the low lane, its layer and tree in the high one)
and `encoding = n2`; the powers `g^s` are `n(3 + s)`, `s < 10`.

Its codeword is the shared WOTS+C dispatch (`walk_group`, `G:3389-3398`, `lx = 0`): 21 groups of
three digits and the last chain's, each a hinted digit word, its range check and a `match` over its
`4^n` arms, written with the shared templates (`WotsT`, `armT`). One thing differs: no `KECCAK`
precedes the codeword, so the compiler allocates the padding run `[0x01, 0, 0, 0, 0]` where an arm
first needs it, in its first chain step, and again in every arm (an arm's constants are its own).
The templates therefore write each arm with its padding run at a virtual base `spVPad` above every
value (`spW`), and `withPad` moves it where the compiler puts it: it renames the arm's values
(`padShift`: the virtual run to the real one, every value from the real run on five up) and inserts
the run's five constants. The leaf's `keccak_cells` (`wots_leaf`, `G:3412-3415`, 66 cells, 1056
bytes) is the shared Keccak message (`kMsg`) moved the same way, its run allocated at its first
block's `KECCAK`.

* `k48At`, `spW`: the chain step, the address `at + (TW_CHAIN + i·2^32 + s·2^61)` and
  `keccak([pp, a], [v, 0], walks[o:o + 13], len=48)` (`walk`, `G:3381-3386`);
* `padRun`, `padShift`, `withPad`: the padding run where the compiler allocates it;
* `spArmT`, `spArmsT`, `spGroupT`, `spGroupsT`: an arm, a group's arms (arm `0` lays out the
  chains' slots and the group's outputs, the others write them), a group, the groups;
* `spLeafCells`, `spBody`: the leaf's cells and the body: the powers, the groups, the encoding asserted to be
  `encoding`, the digit product to be `g^128` (`SP_TARGET_SUM`), the leaf hashed at
  `at + TW_LEAF` and returned.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## The padding run where the compiler allocates it -/

/-- A virtual padding run, above every value of `sp_wots`. -/
def spVPad : Nat := 2 ^ 32

/-- The padding run `[0x01, 0, 0, 0, 0]` at `P`. -/
def padRun (P : Nat) : List Stmt :=
  (List.range 5).map fun k => cst (P + k) (word (if k = 0 then 1 else 0) 0 0)

/-- The renaming that moves the virtual run at `X` to `P` and every value from `P` on five up. -/
def padShift (X P : Nat) (v : V) : V :=
  if v.path = [] ∧ v.tag = 0 then
    .n (if X ≤ v.idx then P + (v.idx - X) else if P ≤ v.idx then v.idx + 5 else v.idx)
  else v

/-- The value a statement defines first: a constant's, the first output of a `KECCAK`. -/
def firstDef : Stmt → Nat
  | .atom (.const d _) => d.idx
  | .atom (.keccak _ (o :: _) _ _) => o.idx
  | _ => 0

open scoped Dec in
/-- A constant `2^63`: the last byte's `0x80` of a one-block message, after its padding cells. -/
def isTopConst : Stmt → Bool
  | .atom (.const _ c) => decide (c = word (2 ^ 63) 0 0)
  | _ => false

/-- A `KECCAK`. -/
def isKeccak : Stmt → Bool
  | .atom (.keccak ..) => true
  | _ => false

/-- **The padding run allocated at its first use**: the statements `L`, written with their padding
run at the virtual `X`, with the run moved before the first statement `sel` picks (none: `L`
unchanged) and the values renamed; and the values it adds (`5` or `0`). -/
def withPad (X : Nat) (sel : Stmt → Bool) (L : List Stmt) : List Stmt × Nat :=
  match L.findIdx? sel with
  | none => (L, 0)
  | some i =>
      let P := firstDef (L.getD i default)
      let L' := Stmt.renameList (padShift X P) L
      (L'.take i ++ padRun P ++ L'.drop i, 5)

/-! ## The chains -/

/-- `keccak([pp, a], [v, 0], out, len=48)` with its padding run at `pad`: its last byte's
constant at `c`, the outputs from `o`. -/
def k48At (pp : V) (pad : Nat) (a v : V) (c o : Nat) : List Stmt :=
  [cst c (word (2 ^ 63) 0 0), kecS [pp, a, v, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3),
    .n (pad + 4), .n c, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)] (runV o 13)
    false false]

/-- `sp_wots`'s chain step `s` of chain `i`: the address `at + (TW_CHAIN + i·2^32 + s·2^61)`, then
the 48-byte hash of `pp`, it and the value, its padding run virtual (`walk`, `G:3381-3386`). -/
def spW : WotsT where
  step i s v c o := cst c (word (tw 1 + i * hiMul + s * stepMul) 0 0) ::
    addS (.n (c + 1)) (.n 1) (.n c) :: k48At (.n 0) spVPad (.n (c + 1)) v (c + 2) o
  size := 3
  power s := .n (3 + s)

/-- The real slot of chain `r`'s step `s` in a group from base `B`: arm `0` lays the slots out after
its padding run. -/
def spSlot (fold : Bool) (B r s : Nat) : Nat := slotsT spW fold B r s + 5

/-- The group's running product, after arm `0`'s walks. -/
def spProd (fold : Bool) (n B : Nat) : Nat := groupStart fold B + chainStride spW * n + 5

/-- The group's running encoding. -/
def spEnc (fold : Bool) (n B : Nat) : Nat := spProd fold n B + 1

/-- Arm `k` of a group from base `b`: the shared arm with its padding run moved where the compiler
puts it; the statements and the next base. -/
def spArmT (first n : Nat) (fold : Bool) (slots : Nat → Nat → Nat) (prodIn encIn prodOut encOut : V)
    (k b : Nat) : List Stmt × Nat :=
  let a := armT spW slots first n fold prodIn encIn prodOut encOut k b
  let w := withPad spVPad isTopConst a.1
  (w.1, a.2 + w.2)

/-- Arms `k ..< k + m` of the group from `B`, from base `b`: arm `0` with the slots and outputs as
the shared template lays them out (moved by its run), the others writing the real ones; the arms
and the next base. -/
def spArmsT (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) :
    Nat → Nat → Nat → List (List Stmt) × Nat
  | 0, _, b => ([], b)
  | m + 1, k, b =>
      let a := if k = 0 then
          spArmT first n fold (slotsT spW fold B) prodIn encIn (prodT spW fold n B) (encT spW fold n B)
            0 b
        else spArmT first n fold (spSlot fold B) prodIn encIn (.n (spProd fold n B))
          (.n (spEnc fold n B)) k b
      let rest := spArmsT first n fold B prodIn encIn m (k + 1) (if k = 0 then a.2 + 2 else a.2)
      (a.1 :: rest.1, rest.2)

/-- A group of `n` digits from base `B`: the digit hint, its range check and the dispatch over the
`4^n` digit values; the statements and the next base. -/
def spGroupT (first n : Nat) (fold : Bool) (prodIn encIn : V) (B : Nat) : List Stmt × Nat :=
  let arms := spArmsT first n fold B prodIn encIn (4 ^ n) 0 (B + 5)
  (hintW "digits" [.n B] :: rangeS (.n B) (word (2 ^ (4 ^ n - 1)) 0 0) (B + 1) ++
    [.match_ (.n B) arms.1], arms.2)

/-- Groups `p ..< p + m` of three digits from base `B`, after the running product and encoding:
the statements, the next base, the chains' tips, the product and the encoding. -/
def spGroupsT : Nat → Nat → V → V → Nat → List Stmt × Nat × List V × V × V
  | 0, _, prod, enc, B => ([], B, [], prod, enc)
  | m + 1, p, prod, enc, B =>
      let fold := p == 0
      let g := spGroupT (3 * p) 3 fold prod enc B
      let rest := spGroupsT m (p + 1) (.n (spProd fold 3 B)) (.n (spEnc fold 3 B)) g.2
      (g.1 ++ rest.1, rest.2.1,
        (List.range 3).map (fun r => V.n (spSlot fold B r 2)) ++ rest.2.2.1, rest.2.2.2)

/-! ## The body -/

/-- `g^128`, the target sum in the exponent (`SP_TARGET_SUM`), as the compiler writes it. -/
def spTarget : E := word 325 0 0

/-- The codeword's groups: 21 of three digits from `n13`, then the last chain's. -/
def spGs : List Stmt × Nat × List V × V × V := spGroupsT 21 0 (.n 0) (.n 0) 13

/-- The last chain's group. -/
def spLast : List Stmt × Nat := spGroupT 63 1 false spGs.2.2.2.1 spGs.2.2.2.2 spGs.2.1

/-- The first value after the codeword's checks: `g^128` there, the leaf's address after it. -/
def spC : Nat := spLast.2

/-- The leaf's cells: `pp`, `at + TW_LEAF` and the 64 chain tips. -/
def spLeafCells : List V :=
  V.n 0 :: V.n (spC + 2) :: spGs.2.2.1 ++ [V.n (spSlot false spGs.2.1 0 2)]

/-- The leaf's `keccak_cells` (1056 bytes), its padding run allocated at its first `KECCAK`: the
statements, the next base and the output run's base. -/
def spLeafK : List Stmt × Nat × Nat :=
  let k := kMsg spVPad (spLeafCells.map KC.cell) 1056 false none (spC + 3)
  let w := withPad spVPad isKeccak k.1
  (w.1, k.2.1 + w.2, k.2.2 + w.2)

/-- The body of `sp_wots`. -/
def spBody : List Stmt :=
  (List.range 10).map (fun s => cst (3 + s) (word (2 ^ s) 0 0)) ++ spGs.1 ++ spLast.1 ++
    [.atom (.assertEq (.n (spEnc false 1 spGs.2.1)) (.n 2)), cst spC spTarget,
      .atom (.assertEq (.n (spProd false 1 spGs.2.1)) (.n spC)), cst (spC + 1) (word (tw 2) 0 0),
      addS (.n (spC + 2)) (.n 1) (.n (spC + 1))] ++ spLeafK.1 ++
    [copyS (.n spLeafK.2.1) (.n spLeafK.2.2), .ret [.n spLeafK.2.1]]

end
end LeanVM.Guest.B1.Sig
