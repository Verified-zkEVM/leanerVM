/-
  LeanVM.Guest.B1.Sig.WotsT

  The WOTS+C codeword check and the Merkle path both signature verifiers share, as templates
  (`walk`, `walk_group`, the digit dispatch, `merkle_path`, `lean_ethereum.py:3332-3440`).
-/

module

public import LeanVM.Guest.B1.Sig.Shapes

/-!
# WOTS+C and Merkle paths, as templates

Both verifiers walk their chains with the same code (`walk`, `walk_group`) and differ only in a
chain step (`WotsT.step`): leanXMSS hashes `P`, the step's address computed once per signature, the
value and the chain index (one constant before the outputs, `size = 1`); leanSPHINCS computes the
address from the index, the chain and the step and hashes `P`, it and the value, 48 bytes (three
values before the outputs, `size = 3`).

* `walkT`: chain `i` from digit `d`: the hinted start at the base, then steps `d, …, 2`, step `s`
  writing slot `s` of the chain in `walks`; the step's constants `stride` apart (`size + 13` in the
  arm that lays out the slots, `size` elsewhere); at `d = 3` the start is hinted into the tip;
* `armT`, `armsT`, `groupT`: arm `k` of a group's dispatch (the walks at the base-4 digits of `k`,
  then the digit sum folded into the product, in the exponent, and the digits into the encoding),
  the `4^n` arms, and the group with its hint, its range check and the `match`; `fold` marks the
  first group, whose running encoding is a literal `0` set in each arm;
* `groupsT`, `codewordT`: `G` groups of three and the last chain's, the digits stored where the
  digest's first cell is, and the target sum asserted;
* `merkleT`: `merkle_path`, the children hinted, the child checked, each parent hashed.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-- A scheme's chain step and powers. -/
structure WotsT where
  /-- Step `s` of chain `i` on value `v`: its statements, its fresh values from the base, then the
  `KECCAK` writing the slot from `o`. -/
  step : Nat → Nat → V → Nat → Nat → List Stmt
  /-- The fresh values of a step before its outputs. -/
  size : Nat
  /-- The cell holding `g^s`. -/
  power : Nat → V

/-- Chain `i`'s walk from digit `d` (`walk`). -/
def walkT (W : WotsT) (i : Nat) (slot : Nat → Nat) (stride d b : Nat) : List Stmt :=
  if d = 3 then [hintW "chain_starts" [.n (slot 2)]]
  else hintW "chain_starts" [.n b] :: (List.range (3 - d)).flatMap fun j =>
    W.step i (d + j) (if j = 0 then .n b else .n (slot (d + j - 1))) (b + 1 + j * stride)
      (slot (d + j))

/-- The fresh values of a walk. -/
def walkSize (stride d : Nat) : Nat := if d = 3 then 0 else 1 + (3 - d) * stride

/-- The walks of chains `first + r`, `r ..< r + m`, at the base-4 digits of `k`, from `b`. -/
def walksT (W : WotsT) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    Nat → Nat → Nat → List Stmt × Nat
  | 0, _, b => ([], b)
  | m + 1, r, b =>
      let d := k / 4 ^ r % 4
      let rest := walksT W slots first k stride m (r + 1) (b + walkSize stride d)
      (walkT W (first + r) (slots r) stride d b ++ rest.1, rest.2)

/-- Arm `k` of a group from base `b`: the walks, then the product and the encoding folded in. -/
def armT (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k b : Nat) : List Stmt × Nat :=
  let ws := walksT W slots first k (if k = 0 then W.size + 13 else W.size) n 0
    (if fold then b + 1 else b)
  let enc0 := if fold then V.n b else encIn
  let pre := if fold then [cst b (word 0 0 0)] else []
  let prod := if fold then copyS prodOut (W.power (digitSum k n))
    else mulS prodOut prodIn (W.power (digitSum k n))
  if k = 0 then (pre ++ ws.1 ++ [prod, copyS encOut enc0], ws.2)
  else (pre ++ ws.1 ++ [prod, cst ws.2 (lit (k * 4 ^ first)), addS encOut enc0 (.n ws.2)], ws.2 + 1)

/-- Arms `k ..< k + m` from base `b`; arm `0` allocates the outputs after its walks. -/
def armsT (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : Nat → Nat → Nat → List (List Stmt) × Nat
  | 0, _, b => ([], b)
  | m + 1, k, b =>
      let a := armT W slots first n fold prodIn encIn prodOut encOut k b
      let rest := armsT W slots first n fold prodIn encIn prodOut encOut m (k + 1)
        (if k = 0 then a.2 + 2 else a.2)
      (a.1 :: rest.1, rest.2)

/-- Where arm `0` of a group from base `b` starts its first walk. -/
def groupStart (fold : Bool) (b : Nat) : Nat := b + 5 + (if fold then 1 else 0)
/-- The fresh values of a chain in arm `0`. -/
def chainStride (W : WotsT) : Nat := 1 + 3 * (W.size + 13)
/-- The slot of chain `r`'s step `s` in a group from base `b`. -/
def slotsT (W : WotsT) (fold : Bool) (b : Nat) (r s : Nat) : Nat :=
  groupStart fold b + chainStride W * r + 1 + (W.size + 13) * s + W.size
def prodT (W : WotsT) (fold : Bool) (n b : Nat) : V := .n (groupStart fold b + chainStride W * n)
def encT (W : WotsT) (fold : Bool) (n b : Nat) : V := .n (groupStart fold b + chainStride W * n + 1)

/-- A group of `n` digits from base `b`: the digit hint, its range check and the dispatch over the
`4^n` digit values. -/
def groupT (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b : Nat) :
    List Stmt × Nat :=
  let arms := armsT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b)
    (4 ^ n) 0 (b + 5)
  (hintW "digits" [.n b] :: rangeS (.n b) (word (2 ^ (4 ^ n - 1)) 0 0) (b + 1) ++
    [.match_ (.n b) arms.1], arms.2)

/-- Groups `p ..< p + m` of three digits from base `b`, after the running product and encoding:
the statements, the next base, the chains' tips, the product and the encoding. -/
def groupsT (W : WotsT) : Nat → Nat → V → V → Nat → List Stmt × Nat × List V × V × V
  | 0, _, prod, enc, b => ([], b, [], prod, enc)
  | m + 1, p, prod, enc, b =>
      let fold := p == 0
      let g := groupT W (3 * p) 3 fold prod enc b
      let rest := groupsT W m (p + 1) (prodT W fold 3 b) (encT W fold 3 b) g.2
      (g.1 ++ rest.1, rest.2.1,
        (List.range 3).map (fun r => V.n (slotsT W fold b r 2)) ++ rest.2.2.1, rest.2.2.2)

/-- The codeword of `3G + 1` chains from base `b`: `G` groups and the last chain's, the digits stored
where the digest's first cell `d0` is, and the target sum `g^T` asserted. The statements, the next
base and the chains' tips. -/
def codewordT (W : WotsT) (G : Nat) (target : E) (d0 : V) (b : Nat) : List Stmt × Nat × List V :=
  let gs := groupsT W G 0 (.n 0) (.n 0) b
  let last := groupT W (3 * G) 1 false gs.2.2.2.1 gs.2.2.2.2 gs.2.1
  let c := last.2
  (gs.1 ++ last.1 ++ [copyS d0 (encT W false 1 gs.2.1), cst c target,
    .atom (.assertEq (prodT W false 1 gs.2.1) (.n c))], c + 1,
    gs.2.2.1 ++ [V.n (slotsT W false gs.2.1 0 2)])

/-- `merkle_path` levels `l ..< l + m` from `cur`, from base `b` (`pp` the parameter, `pad` the
padding run): the hinted children, the child check, the parent's address (the node index added
unless `nodeOf l` is `none`, at a root) and its hash. The statements, the next base and the node
reached. -/
def merkleT (pad : Nat) (pp : V) (bitOf : Nat → V) (nodeOf : Nat → Option V) (addrOf : Nat → Nat) :
    Nat → Nat → V → Nat → List Stmt × Nat × V
  | 0, _, cur, b => ([], b, cur)
  | m + 1, l, cur, b =>
      let c := match nodeOf l with
        | none => b + 5
        | some _ => b + 6
      let rest := merkleT pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 14)
      ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
          addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) (bitOf l) (.n (b + 3)),
          cst (b + 4) (word (addrOf l) 0 0)] ++
        (match nodeOf l with
          | none => []
          | some nd => [addS (.n (b + 5)) (.n (b + 4)) nd]) ++
        k64 pad pp (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1) ++ rest.1, rest.2.1, rest.2.2)

end
end LeanVM.Guest.B1.Sig
