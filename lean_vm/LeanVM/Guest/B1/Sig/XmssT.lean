/-
  LeanVM.Guest.B1.Sig.XmssT

  The body of `verify_lean_xmss` as a template, written from the guest's structure
  (`lean_ethereum.py:3339-3521`) with the values numbered as the renumbered expansion numbers them.
-/

module

public import LeanVM.Guest.B1.Sig.Shapes

/-!
# `verify_lean_xmss` as a template

* `xPrologue`: `pp`, the leaf index's 32 bits pinned Boolean, the node indices `xNode l`
  (`shifts`), the powers `g^s` (`xPower s`, `s < 10`) and the chain indices `xTag i` (`i < 58`);
* `xWalk` (`walk`, `lean_ethereum.py:3377-3395`): a chain from its digit, each step a 64-byte
  `keccak` of `P`, the step's address, the value and the chain index, into its slot of `walks`;
* `xArm`, `xArms`, `xGroup` (`walk_group`, `lean_ethereum.py:3398-3406`, and the digit dispatch of
  `verify_lean_xmss`): the arm of digit values `k`, the `4^n` arms, the group with its hint and
  range check; arm `0` lays out the slots and the outputs, `fold` marks the first group, whose
  running encoding starts from a literal `0` in each arm;
* `xCodeword`: the 19 groups of three digits, the last chain's, then the digest's first cell and
  the target sum;
* `xMerkle` (`merkle_path`, `lean_ethereum.py:3428-3448`), `xLayer`, `xBody`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-- The padding run of `verify_lean_xmss`, set by the bottom layer's message digest. -/
def xPad : Nat := 206

def xNode (l : Nat) : V := .n (34 + 3 * (31 - l))
def xBit (l : Nat) : V := .n (2 + l)
def xPower (s : Nat) : V := .n (128 + s)
def xTag (i : Nat) : V := .n (138 + i)

/-- `g^106`, the leanXMSS target sum in the exponent. -/
def xTarget : E := word 118747255799808 0 0

/-- The prologue (`lean_ethereum.py:3459-3483`). -/
def xPrologue : List Stmt :=
  [loadS (.n 1) (.n 0) 1, hintW "leaf_index_bits" (runV 2 32)] ++ booleans 2 32 ++ shifts 2 32 34 ++
    (List.range 10).map (fun s => cst (128 + s) (word (2 ^ s) 0 0)) ++
    (List.range 58).map (fun i => cst (138 + i) (word i 0 0))

/-- Chain `i`'s walk from digit `d` (`walk`, leanXMSS): the hinted start at `b`, then the steps
`d + j` at the addresses `steps (d + j)`, each writing its slot from `slot (d + j)`, its constant
`stride` after the previous one (`14` in the arm that lays out the slots, `1` elsewhere). At
`d = 3` the start is hinted into the tip. -/
def xWalk (steps : Nat → V) (i : Nat) (slot : Nat → Nat) (stride d b : Nat) : List Stmt :=
  if d = 3 then [hintW "chain_starts" [.n (slot 2)]]
  else hintW "chain_starts" [.n b] :: (List.range (3 - d)).flatMap fun j =>
    k64 xPad (.n 1) (steps (d + j)) (if j = 0 then .n b else .n (slot (d + j - 1))) (xTag i)
      (b + 1 + j * stride) (slot (d + j))

/-- The fresh values of a walk. -/
def walkSize (stride d : Nat) : Nat := if d = 3 then 0 else 1 + (3 - d) * stride

/-- The walks of chains `first + r`, `r ..< r + m`, at the base-4 digits of `k`, from `b`. -/
def xWalks (steps : Nat → V) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    Nat → Nat → Nat → List Stmt × Nat
  | 0, _, b => ([], b)
  | m + 1, r, b =>
      let d := k / 4 ^ r % 4
      let rest := xWalks steps slots first k stride m (r + 1) (b + walkSize stride d)
      (xWalk steps (first + r) (slots r) stride d b ++ rest.1, rest.2)

/-- Arm `k` of a group from base `b`: the walks, then the product and the encoding folded in.
`fold` for the first group, whose running encoding is a literal `0` set in each arm. -/
def xArm (steps : Nat → V) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k b : Nat) : List Stmt × Nat :=
  let ws := xWalks steps slots first k (if k = 0 then 14 else 1) n 0 (if fold then b + 1 else b)
  let enc0 := if fold then V.n b else encIn
  let pre := if fold then [cst b (word 0 0 0)] else []
  let prod := if fold then copyS prodOut (xPower (digitSum k n))
    else mulS prodOut prodIn (xPower (digitSum k n))
  if k = 0 then (pre ++ ws.1 ++ [prod, copyS encOut enc0], ws.2)
  else (pre ++ ws.1 ++ [prod, cst ws.2 (lit (k * 4 ^ first)), addS encOut enc0 (.n ws.2)], ws.2 + 1)

/-- Arms `k ..< k + m` from base `b`; arm `0` allocates the outputs after its walks. -/
def xArms (steps : Nat → V) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : Nat → Nat → Nat → List (List Stmt) × Nat
  | 0, _, b => ([], b)
  | m + 1, k, b =>
      let a := xArm steps slots first n fold prodIn encIn prodOut encOut k b
      let rest := xArms steps slots first n fold prodIn encIn prodOut encOut m (k + 1)
        (if k = 0 then a.2 + 2 else a.2)
      (a.1 :: rest.1, rest.2)

/-- Where arm `0` of a group from base `b` starts its first walk. -/
def groupStart (fold : Bool) (b : Nat) : Nat := b + 5 + (if fold then 1 else 0)
/-- The slot of chain `r`'s step `s` in a group from base `b`. -/
def xSlots (fold : Bool) (b : Nat) (r s : Nat) : Nat := groupStart fold b + 43 * r + 2 + 14 * s
def xProd (fold : Bool) (n b : Nat) : V := .n (groupStart fold b + 43 * n)
def xEnc (fold : Bool) (n b : Nat) : V := .n (groupStart fold b + 43 * n + 1)

/-- A group of `n` digits from base `b`: the digit hint, its range check and the dispatch over the
`4^n` digit values (`lean_ethereum.py:3497-3503`). -/
def xGroup (steps : Nat → V) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b : Nat) :
    List Stmt × Nat :=
  let arms := xArms steps (xSlots fold b) first n fold prodIn encIn (xProd fold n b) (xEnc fold n b)
    (4 ^ n) 0 (b + 5)
  (hintW "digits" [.n b] :: rangeS (.n b) (word (2 ^ (4 ^ n - 1)) 0 0) (b + 1) ++
    [.match_ (.n b) arms.1], arms.2)

/-- Groups `p ..< p + m` of three digits from base `b`, after the running product and encoding:
the statements, the next base, the chains' tips, the product and the encoding. -/
def xGroups (steps : Nat → V) : Nat → Nat → V → V → Nat → List Stmt × Nat × List V × V × V
  | 0, _, prod, enc, b => ([], b, [], prod, enc)
  | m + 1, p, prod, enc, b =>
      let fold := p == 0
      let g := xGroup steps (3 * p) 3 fold prod enc b
      let rest := xGroups steps m (p + 1) (xProd fold 3 b) (xEnc fold 3 b) g.2
      (g.1 ++ rest.1, rest.2.1, (List.range 3).map (fun r => V.n (xSlots fold b r 2)) ++ rest.2.2.1,
        rest.2.2.2)

/-- The codeword of the 58 chains from base `b`: 19 groups and the last chain's, the digits stored
where the digest's first cell `d0` is, and the target sum asserted. The statements, the next base
and the chains' tips. -/
def xCodeword (steps : Nat → V) (d0 : V) (b : Nat) : List Stmt × Nat × List V :=
  let gs := xGroups steps 19 0 (.n 0) (.n 0) b
  let last := xGroup steps 57 1 false gs.2.2.2.1 gs.2.2.2.2 gs.2.1
  let c := last.2
  (gs.1 ++ last.1 ++ [copyS d0 (xEnc false 1 gs.2.1), cst c xTarget,
    .atom (.assertEq (xProd false 1 gs.2.1) (.n c))], c + 1,
    gs.2.2.1 ++ [V.n (xSlots false gs.2.1 0 2)])

/-- `merkle_path` levels `l ..< l + m` from `cur`, from base `b`: the hinted children, the child
check, the parent's address (the node index added unless `nodeOf l` is `none`, at a root) and its
hash. The statements, the next base and the node reached. -/
def xMerkle (bitOf : Nat → V) (nodeOf : Nat → Option V) (addrOf : Nat → Nat) :
    Nat → Nat → V → Nat → List Stmt × Nat × V
  | 0, _, cur, b => ([], b, cur)
  | m + 1, l, cur, b =>
      let c := match nodeOf l with
        | none => b + 5
        | some _ => b + 6
      let rest := xMerkle bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 14)
      ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
          addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) (bitOf l) (.n (b + 3)),
          cst (b + 4) (word (addrOf l) 0 0)] ++
        (match nodeOf l with
          | none => []
          | some nd => [addS (.n (b + 5)) (.n (b + 4)) nd]) ++
        k64 xPad (.n 1) (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1) ++ rest.1, rest.2.1, rest.2.2)

/-- The bottom layer's message digest from base `b`: `D = Th(P, A_msg, M | ρ)`, 80 bytes, one
block; it sets the padding run at `b + 10`. -/
def xDigest0 (b : Nat) : List Stmt :=
  [hintW "randomizer" [.n b], cst (b + 1) (word (tw 12) 0 0), addS (.n (b + 2)) (xNode 0) (.n (b + 1)),
    loadS (.n (b + 3)) (.n 0) 2, loadS (.n (b + 4)) (.n 0) 3, copyS (.n (b + 5)) (.n b),
    cst (b + 6) (word 1 0 0), cst (b + 7) (word 0 0 0), cst (b + 8) (word 0 0 0),
    cst (b + 9) (word (2 ^ 63) 0 0)] ++
  (List.range 5).map (fun k => cst (b + 10 + k) (word (if k = 0 then 1 else 0) 0 0)) ++
  [kecS [.n 1, .n (b + 2), .n (b + 3), .n (b + 4), .n (b + 5), .n (b + 6), .n (b + 7), .n (b + 8),
    .n (b + 9), .n (b + 11), .n (b + 12), .n (b + 13), .n (b + 14)] (runV (b + 15) 13) false false]

/-- The top layer's index and message digest from base `b`, over the bottom root `root`. -/
def xDigest1 (b : Nat) (root : V) : List Stmt :=
  [cst b (word lxTop 0 0), addS (.n (b + 1)) (xNode 16) (.n b), hintW "randomizer" [.n (b + 2)],
    cst (b + 3) (word (tw 12) 0 0), addS (.n (b + 4)) (.n (b + 1)) (.n (b + 3))] ++
  k64 xPad (.n 1) (.n (b + 4)) root (.n (b + 2)) (b + 5) (b + 6)

/-- The three step addresses from base `b`, at `n(b + 2s + 1)`. -/
def xStepAddrs (idx : V) (b : Nat) : List Stmt :=
  (List.range 3).flatMap fun s =>
    [cst (b + 2 * s) (word (tw 1 + s * stepMul) 0 0), addS (.n (b + 2 * s + 1)) idx (.n (b + 2 * s))]

/-- Layer `layer` from base `b`, over the bottom root `root` at the top: its statements, the next
base and its root. -/
def xLayer (layer b : Nat) (root : V) : List Stmt × Nat × V :=
  let idx : V := if layer = 0 then xNode 0 else .n (b + 1)
  let a := if layer = 0 then b + 28 else b + 19
  let d0 : V := if layer = 0 then .n (b + 15) else .n (b + 6)
  let cw := xCodeword (fun s => .n (a + 2 * s + 1)) d0 (a + 6)
  let c := cw.2.1
  let leaf := kMsg xPad ((V.n 1 :: V.n (c + 1) :: cw.2.2).map KC.cell) 960 false none (c + 2)
  let mk := xMerkle (fun l => xBit (16 * layer + l))
    (fun l => if 16 * layer + l + 1 = 32 then none else some (xNode (16 * layer + l + 1)))
    (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop) 16 0 (.n leaf.2.2) leaf.2.1
  ((if layer = 0 then xDigest0 b else xDigest1 b root) ++ xStepAddrs idx a ++ cw.1 ++
    [cst c (word (tw 2) 0 0), addS (.n (c + 1)) idx (.n c)] ++ leaf.1 ++ mk.1, mk.2.1, mk.2.2)

/-- The body of `verify_lean_xmss`. -/
def xBody : List Stmt :=
  let l0 := xLayer 0 196 (.n 0)
  let l1 := xLayer 1 l0.2.1 l0.2.2
  xPrologue ++ l0.1 ++ l1.1 ++
    [loadS (.n l1.2.1) (.n 0) 0, .atom (.assertEq l1.2.2 (.n l1.2.1)), .ret []]

end
end LeanVM.Guest.B1.Sig
