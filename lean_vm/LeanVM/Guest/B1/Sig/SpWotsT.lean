/-
  LeanVM.Guest.B1.Sig.SpWotsT

  The body of `sp_wots` as a template, written from the guest's structure
  (`lean_ethereum.py:3816-3843` at leanVM c4f4bc92) with the values numbered as the renumbered
  expansion numbers them.
-/

module

public import LeanVM.Guest.B1.Sig.WotsT

/-!
# `sp_wots` as a template

`sp_wots(pp, at, encoding)` (`G:3816-3843`; `G` is `lean_ethereum.py`) has the parameters `pp = n0`,
`at = n1` (the one-time key's address: its leaf in the low lane, its layer and tree in the high one)
and `encoding = n2`; the powers `g^s` are `n(3 + s)`, `s < 10`.

Its codeword is the shared WOTS+C dispatch (`walk_group`, `G:3577-3584`, `lx = 0`): 21 groups of
three digits and the last chain's, each a hinted digit word, its range check, the hoisted constant
and a `match` over its `4^n` arms, written with the shared templates (`WotsT`, `groupD`). No `KECCAK`
precedes the codeword, so the compiler sets the padding run `[0x01, 0, 0, 0, 0]` above the first
group's dispatch, at `n18 ..< n23` (`spPad`), after its range check: the first group's arms are laid
out from `n18` (`spL`), five above its digit word; every chain step and the leaf read that run.

* `k48At`, `spWp`, `spW`: the chain step, the address `at + (TW_CHAIN + i·2^32 + s·2^61)` and
  `keccak([pp, a], [v, 0], walks[o:o + 13], len=48)` (`walk`, `G:3548-3573`), its run at `spPad`;
* `spL`, `spPre`, `spSlot`, `spProd`, `spEnc`, `spGroupT`, `spGroupsT`: a group's layout base, the
  run the first group sets, a chain's slots, the group's outputs, a group, the groups;
* `spLeafCells`, `spBody`: the leaf's cells and the body: the powers, the groups, the encoding asserted to be
  `encoding`, the digit product to be `g^128` (`SP_TARGET_SUM`), the leaf hashed at
  `at + TW_LEAF` (`wots_leaf`, `G:3599-3603`, 66 cells, 1056 bytes) and returned.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## The padding run -/

/-- The padding run's base: the first group sets it after its range check. -/
def spPad : Nat := 18

/-- The padding run `[0x01, 0, 0, 0, 0]` at `P`. -/
def padRun (P : Nat) : List Stmt :=
  (List.range 5).map fun k => cst (P + k) (word (if k = 0 then 1 else 0) 0 0)

/-! ## The chains -/

/-- `keccak([pp, a], [v, 0], out, len=48)` with its padding run at `pad`: its last byte's
constant at `c`, the outputs from `o`. -/
def k48At (pp : V) (pad : Nat) (a v : V) (c o : Nat) : List Stmt :=
  [cst c (word (2 ^ 63) 0 0), kecS [pp, a, v, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3),
    .n (pad + 4), .n c, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)] (runV o 13)
    false false]

/-- `sp_wots`'s chain step with its padding run at `X`: step `s` of chain `i`, the address
`at + (TW_CHAIN + i·2^32 + s·2^61)`, then the 48-byte hash of `pp`, it and the value (`walk`,
`G:3548-3573`). -/
def spWp (X : Nat) : WotsT where
  step i s v c o := cst c (word (tw 1 + i * hiMul + s * stepMul) 0 0) ::
    addS (.n (c + 1)) (.n 1) (.n c) :: k48At (.n 0) X (.n (c + 1)) v (c + 2) o
  size := 3
  power s := .n (3 + s)

/-- `sp_wots`'s chain step, its padding run at `spPad`. -/
def spW : WotsT := spWp spPad

/-! ## The groups -/

/-- A group's layout base from its digit word's cell `B`: the first group's arms lie above the
padding run, five up. -/
def spL (fold : Bool) (B : Nat) : Nat := if fold then B + 5 else B

/-- What a group sets between its range check and its hoisted constant: the first, the padding run. -/
def spPre (fold : Bool) (B : Nat) : List Stmt := if fold then padRun (B + 5) else []

/-- The slot of chain `r`'s step `s` in a group from base `B`. -/
def spSlot (fold : Bool) (B : Nat) : Nat → Nat → Nat := slotsT spW fold (spL fold B)

/-- The group's running product, after arm `0`'s walks. -/
def spProd (fold : Bool) (n B : Nat) : Nat := groupStart fold (spL fold B) + chainStride spW * n

/-- The group's running encoding. -/
def spEnc (fold : Bool) (n B : Nat) : Nat := spProd fold n B + 1

/-- A group of `n` digits, its digit word at `B`: the shared group, its arms laid out from
`spL fold B`, the first setting the padding run; the statements and the next base. -/
def spGroupT (first n : Nat) (fold : Bool) (prodIn encIn : V) (B : Nat) : List Stmt × Nat :=
  groupD spW first n fold prodIn encIn B (spPre fold B) (spL fold B)

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

/-- The leaf's `keccak_cells` (1056 bytes), its padding run at `spPad`: the statements, the next
base and the output run's base. -/
def spLeafK : List Stmt × Nat × Nat := kMsg spPad (spLeafCells.map KC.cell) 1056 false none (spC + 3)

/-- The body of `sp_wots`. -/
def spBody : List Stmt :=
  (List.range 10).map (fun s => cst (3 + s) (word (2 ^ s) 0 0)) ++ spGs.1 ++ spLast.1 ++
    [.atom (.assertEq (.n (spEnc false 1 spGs.2.1)) (.n 2)), cst spC spTarget,
      .atom (.assertEq (.n (spProd false 1 spGs.2.1)) (.n spC)), cst (spC + 1) (word (tw 2) 0 0),
      addS (.n (spC + 2)) (.n 1) (.n (spC + 1))] ++ spLeafK.1 ++
    [copyS (.n spLeafK.2.1) (.n spLeafK.2.2), .ret [.n spLeafK.2.1]]

end
end LeanVM.Guest.B1.Sig
