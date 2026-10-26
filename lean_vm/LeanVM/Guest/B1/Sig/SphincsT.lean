/-
  LeanVM.Guest.B1.Sig.SphincsT

  The body of `verify_sig_lean_sphincs` as a template, written from the guest's structure
  (`lean_ethereum.py:3524-3763`) with the values numbered as the renumbered expansion numbers them.
-/

module

public import LeanVM.Guest.B1.Sig.WotsT
public import Sphincs.Equations

/-!
# `verify_sig_lean_sphincs` as a template

`byte_bits` is the parameter `n1`, `P` the cell `n2` (`sPP`), the padding run `n12 … n16`, the
index `idx` the node index `sNode 0`.

* `sFromBytes` (`sp_from_bytes`, `lean_ethereum.py:3528-3544`): each byte mark range checked and read
  off `byte_bits`, the value folded high byte first;
* `sPrologue`: the message digest, its index bits pinned Boolean, the node indices (`shifts`), the
  unused bytes, the bound's start, the encoding's first two cells (`tops`), and the address
  constants of the forest keys (`tws`) and of the sub-trees (`sub_tws`);
* `fkChain`, `fkArm`, `fkArms` (`sp_forest_top`, `sp_forest_key`, `lean_ethereum.py:3548-3589`): the
  forest key of codeword entry `t`, each of its six chains walked its deficit `spCode t i` up to the
  top, the key's leaf hashed;
* `foldLevel`, `foldArm`, `foldArms` (`sp_fold`, `sp_subtree_arm`, `sp_tree_arm`,
  `lean_ethereum.py:3592-3631`): a leaf folded up its hinted path into the tree's two top nodes;
* `sSubtree`, `sCoord`: a sub-tree of a coordinate (its key and codeword hints, the forest key's
  dispatch, the fold's dispatch) and a coordinate (its leaf hint, two sub-trees, the tree leaf's
  hash, the top fold's dispatch);
* `sWots`: the one-time chain step; `sBody`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-- The padding run of `verify_sig_lean_sphincs`, set by the message digest. -/
def sPad : Nat := 12
def sPP : V := .n 2
def sNode (l : Nat) : V := .n (56 + 3 * (25 - l))
def sBit (l : Nat) : V := .n (30 + l)
/-- `tws[k]`: what a forest key's step (`4 i + s`) or leaf (`24`) address adds to the key's. -/
def sTws (k : Nat) : V := .n (165 + k)
/-- `sub_tws[k]`: what a sub-tree node's address (`2 a + l`) adds to its key's. -/
def sSubTws (k : Nat) : V := .n (190 + k)

/-- `g^255`, `g^63`, `g^15`, `g^7` and `g^123`, as the compiler writes them. -/
def g255W : E := word 9223372036854810629 0 0
def g63W : E := word (2 ^ 63) 0 0
def g15W : E := word (2 ^ 15) 0 0
def g7W : E := word (2 ^ 7) 0 0
def sTarget : E := word 15564440312192434176 0 0

/-- The guest's codeword table (`SP_CODEWORDS`) as one number: the deficit of chain `i` in entry `t`
is its base-5 digit `6 t + i` (`spCodes_eq`: the scheme's `lut`). -/
def spCodes : Nat :=
  8631839020406613191160114983723275665298640796343609222621742565094309190981918509084514383022418732463253124642455227629651883777975082883024568907441145731427037111555090928528042711228332321662590151231070707009819138490573935406199335817216339647178606289382559463376348881407249603307696882622511157087178317066805592167665301525678635103989605775071656292464966864290093026074744021371914802635913362916878522553906932163856979934779130609064178309898489883866435693027106516869960555184941499058924896278940088508773149859812774591343661980786447042749080038364026435405661916491722576723635592096859297416162130845762528155300342395214265924709984299602519263095490788250598276483913627778258603953644129970491128582377492180641768761938413751793909442289835513070071339130009914789340130716133762547879204100044759527748647839786810676582711916799692868016179380207515627096632140729308189334582518674938811562715850386140435647667304890725396252190555613943518958416709309184806640665885290560514680130513183614064364824162991141639804846956610689643127529310000

/-- The deficit of chain `i` in codeword entry `t`. -/
def spCode (t i : Nat) : Nat := spCodes / 5 ^ (6 * t + i) % 5

/-- `keccak([P, a], [v, 0], out, len=48)`: its last byte's constant at `c`, the outputs from `o`. -/
def k48 (a v : V) (c o : Nat) : List Stmt :=
  [cst c (word (2 ^ 63) 0 0), kecS [sPP, a, v, .n sPad, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3),
    .n (sPad + 4), .n c, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)] (runV o 13)
    false false]

/-! ## `sp_from_bytes` -/

/-- One byte from base `b`: its range check against `bound`, the table's address and value at
`b + 5`. -/
def sByte (mark : V) (bound : E) (b : Nat) : List Stmt :=
  rangeS mark bound b ++ [mulS (.n (b + 4)) (.n 1) mark, loadS (.n (b + 5)) (.n (b + 4)) 0]

/-- The bytes after the top one, folding `val`. -/
def sFromBytesRest : List V → Nat → V → List Stmt × Nat × V
  | [], b, val => ([], b, val)
  | m :: ms, b, val =>
      let rest := sFromBytesRest ms (b + 9) (.n (b + 8))
      (sByte m g255W b ++ [cst (b + 6) (word 256 0 0), mulS (.n (b + 7)) val (.n (b + 6)),
        addS (.n (b + 8)) (.n (b + 5)) (.n (b + 7))] ++ rest.1, rest.2.1, rest.2.2)

/-- `sp_from_bytes` of the marks `top :: rest` (high byte first) from base `b`: the statements, the
next base and the value. -/
def sFromBytes (top : V) (rest : List V) (bound : E) (b : Nat) : List Stmt × Nat × V :=
  let r := sFromBytesRest rest (b + 6) (.n (b + 5))
  (sByte top bound b ++ r.1, r.2.1, r.2.2)

/-! ## The prologue -/

/-- The forest keys' address constants: `tws[4 i + s]`, then `tws[24]`. -/
def sTwsWords : List E :=
  ((List.range 6).flatMap fun i => (List.range 4).map fun s =>
    word (tw 15 + i * 2 ^ 43 + s * stepMul) 0 0) ++ [word (tw 16) 0 0]

/-- The sub-trees' address constants `sub_tws[2 a + l]`. -/
def sSubTwsWords : List E :=
  (List.range 8).flatMap fun a => (List.range 2).map fun l =>
    word (a * 2 ^ 40 ^^^ (tw 17 + (l + 1) * 2 ^ 40 + a / 2 ^ (l + 1) * 2 ^ 42)) 0 0

/-- The prologue (`lean_ethereum.py:3634-3679`): the message digest into `n17 … n29`, the index's
bits, the node indices, the unused bytes into `n158`, the bound `n161`, `tops[0] = n162`,
`tops[1] = n164`, and the address constants. -/
def sPrologue : List Stmt :=
  [loadS sPP (.n 0) 1, hintW "sp_rand" [.n 3], cst 4 (word (tw 12) 0 0), loadS (.n 5) (.n 0) 2,
    loadS (.n 6) (.n 0) 3, copyS (.n 7) (.n 3), cst 8 (word 1 0 0), cst 9 (word 0 0 0),
    cst 10 (word 0 0 0), cst 11 (word (2 ^ 63) 0 0)] ++
  (List.range 5).map (fun k => cst (12 + k) (word (if k = 0 then 1 else 0) 0 0)) ++
  [kecS [sPP, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 13, .n 14, .n 15, .n 16]
    (runV 17 13) false false,
    .atom (.hint (.bits (.n 18) 0 26 (.stack (runV 30 26))))] ++
  booleans 30 26 ++ shifts 30 26 56 ++
  [hintW "sp_unused" [.n 132, .n 133, .n 134]] ++
  (sFromBytes (.n 134) [.n 133, .n 132] g63W 135).1 ++
  [cst 159 (word 0 (2 ^ 42) 0), mulS (.n 160) (.n 158) (.n 159), addS (.n 161) (sNode 0) (.n 160),
    copyS (.n 162) sPP, cst 163 (word (tw 4) 0 0), addS (.n 164) (sNode 0) (.n 163)] ++
  (sTwsWords.zipIdx.map fun (w, k) => cst (165 + k) w) ++
  (sSubTwsWords.zipIdx.map fun (w, k) => cst (190 + k) w)

/-! ## The forest keys -/

/-- Chain `i` of forest key `t` from base `b` (`sp_forest_top`): its hinted value, walked its deficit
up to the top at the addresses `keyAt + tws[4 i + s]`; a top of chain `i ≥ 2` copied into its cell
of `tops` (at deficit `0` the hint writes it there). The statements, the next base and the top. -/
def fkChain (t i : Nat) (keyAt : V) (b : Nat) : List Stmt × Nat × V :=
  let d := spCode t i
  if d = 0 then ([hintW "sp_forest_values" [.n b]], b + 1, .n b)
  else
    let steps := (List.range d).flatMap fun j => let c := b + 1 + 15 * j;
      addS (.n c) keyAt (sTws (4 * i + 4 - d + j)) ::
        k48 (.n c) (if j = 0 then .n b else .n (c - 13)) (c + 1) (c + 2)
    let v : V := .n (b + 15 * d - 12)
    if i < 2 then (hintW "sp_forest_values" [.n b] :: steps, b + 1 + 15 * d, v)
    else (hintW "sp_forest_values" [.n b] :: steps ++ [copyS (.n (b + 1 + 15 * d)) v],
      b + 2 + 15 * d, .n (b + 1 + 15 * d))

/-- Chains `i ..< i + m` of forest key `t` from base `b`: the statements, the next base, the tops. -/
def fkChains (t : Nat) (keyAt : V) : Nat → Nat → Nat → List Stmt × Nat × List V
  | 0, _, b => ([], b, [])
  | m + 1, i, b =>
      let c := fkChain t i keyAt b
      let rest := fkChains t keyAt m (i + 1) c.2.1
      (c.1 ++ rest.1, rest.2.1, c.2.2 :: rest.2.2)

/-- The weight of codeword entry `t` at the digest's byte `w` (`sp_forest_key`'s second return). -/
def fkWeight (t w : Nat) : E :=
  if w < 8 then word (t * 2 ^ (8 * w)) 0 0 else word 0 (t * 2 ^ (8 * (w - 8))) 0

/-- Forest key `t` for the digest's byte `w` from base `b` (`sp_forest_key`): the six chains, the
leaf hashed from `P`, `keyAt + tws[24]`, the tops of chains `0`, `1` and the run `tops`, its first
cell into `retN` and the weight into `retW`; the first arm allocates the two. -/
def fkArm (t w : Nat) (keyAt retN retW : V) (fresh : Bool) (b : Nat) : List Stmt × Nat :=
  let ch := fkChains t keyAt 6 0 b
  let B := ch.2.1
  let top := fun i => ch.2.2.getD i (.n 0)
  let rN := if fresh then V.n (B + 15) else retN
  let rW := if fresh then V.n (B + 16) else retW
  (ch.1 ++ [addS (.n B) keyAt (sTws 24), cst (B + 1) (word (2 ^ 63 + 1) 0 0),
    kecS [sPP, .n B, top 0, top 1, top 2, top 3, top 4, top 5, .n (B + 1), .n (sPad + 1),
      .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)] (runV (B + 2) 13) false false,
    copyS rN (.n (B + 2)), .atom (.const rW (fkWeight t w))], if fresh then B + 17 else B + 15)

/-- Forest keys `t ..< t + m` after the first, from base `b`. -/
def fkArmsRest (w : Nat) (keyAt retN retW : V) : Nat → Nat → Nat → List (List Stmt) × Nat
  | 0, _, b => ([], b)
  | m + 1, t, b =>
      let a := fkArm t w keyAt retN retW false b
      let rest := fkArmsRest w keyAt retN retW m (t + 1) a.2
      (a.1 :: rest.1, rest.2)

/-- The 256 forest keys of the digest's byte `w` from base `b`: the arms, the next base, the leaf's
cell and the weight's. -/
def fkArms (w : Nat) (keyAt : V) (b : Nat) : List (List Stmt) × Nat × V × V :=
  let a0 := fkArm 0 w keyAt (.n 0) (.n 0) true b
  let rest := fkArmsRest w keyAt (.n (a0.2 - 2)) (.n (a0.2 - 1)) 255 1 a0.2
  (a0.1 :: rest.1, rest.2, .n (a0.2 - 2), .n (a0.2 - 1))

/-! ## The folds -/

/-- One level of `sp_fold` from base `b`: the hinted sibling, the node's address (`at` plus a cell,
or plus a constant), the pair in the order of the index's bit. The statements, the next base and
the parent. -/
def foldLevel (atV : V) (adr : Sum V Nat) (bit : Bool) (cur : V) (b : Nat) : List Stmt × Nat × V :=
  match adr with
  | .inl a =>
      (hintW "sp_forest_nodes" [.n b] :: addS (.n (b + 1)) atV a ::
        k64 sPad sPP (.n (b + 1)) (if bit then .n b else cur) (if bit then cur else .n b) (b + 2) (b + 3),
        b + 16, .n (b + 3))
  | .inr c =>
      (hintW "sp_forest_nodes" [.n b] :: cst (b + 1) (word c 0 0) :: addS (.n (b + 2)) atV (.n (b + 1)) ::
        k64 sPad sPP (.n (b + 2)) (if bit then .n b else cur) (if bit then cur else .n b) (b + 3) (b + 4),
        b + 17, .n (b + 4))

/-- Levels `l ..< l + m` of a fold of leaf `index` from `cur`, from base `b`. -/
def foldLevels (atV : V) (adr : Nat → Sum V Nat) (index : Nat) :
    Nat → Nat → V → Nat → List Stmt × Nat × V
  | 0, _, cur, b => ([], b, cur)
  | m + 1, l, cur, b =>
      let x := foldLevel atV (adr l) (index.testBit l) cur b
      let rest := foldLevels atV adr index m (l + 1) x.2.2 x.2.1
      (x.1 ++ rest.1, rest.2.1, rest.2.2)

/-- The arm of leaf `index` of a fold of height `height` from base `b`: the levels, the node
reached into the top `outs` of the index's top bit, the other top hinted, the mark `markV` set to
`markC` and the weight `wC` into the third of `outs`; the first arm allocates the three. -/
def foldArm (atV : V) (adr : Nat → Sum V Nat) (height index : Nat) (node0 : V) (outs : V × V × V)
    (markV : V) (markC wC : E) (fresh : Bool) (b : Nat) : List Stmt × Nat :=
  let lv := foldLevels atV adr index (height - 1) 0 node0 b
  let o : V × V × V := if fresh then (.n lv.2.1, .n (lv.2.1 + 1), .n (lv.2.1 + 2)) else outs
  let h := index / 2 ^ (height - 1)
  (lv.1 ++ [copyS (if h = 0 then o.1 else o.2.1) lv.2.2,
    hintW "sp_forest_nodes" [if h = 0 then o.2.1 else o.1], .atom (.const markV markC),
    .atom (.const o.2.2 wC)], if fresh then lv.2.1 + 3 else lv.2.1)

/-- The fold's arms `index ..< index + m` after the first, from base `b`. -/
def foldArmsRest (atV : V) (adr : Nat → Nat → Sum V Nat) (height : Nat) (node0 : V)
    (outs : V × V × V) (markV : V) (markC wC : Nat → E) : Nat → Nat → Nat → List (List Stmt) × Nat
  | 0, _, b => ([], b)
  | m + 1, index, b =>
      let a := foldArm atV (adr index) height index node0 outs markV (markC index) (wC index) false b
      let rest := foldArmsRest atV adr height node0 outs markV markC wC m (index + 1) a.2
      (a.1 :: rest.1, rest.2)

/-- The `2^height` arms of a fold from base `b`: the arms, the next base and the outputs. -/
def foldArms (atV : V) (adr : Nat → Nat → Sum V Nat) (height : Nat) (node0 markV : V)
    (markC wC : Nat → E) (b : Nat) : List (List Stmt) × Nat × (V × V × V) :=
  let a0 := foldArm atV (adr 0) height 0 node0 (.n 0, .n 0, .n 0) markV (markC 0) (wC 0) true b
  let outs : V × V × V := (.n (a0.2 - 3), .n (a0.2 - 2), .n (a0.2 - 1))
  let rest := foldArmsRest atV adr height node0 outs markV markC wC (2 ^ height - 1) 1 a0.2
  (a0.1 :: rest.1, rest.2, outs)

/-- `const(a) * COORD_BASIS[k]` for a small `a`. -/
def cbMul (a k : Nat) : E := if k < 64 then word (a * 2 ^ k) 0 0 else word 0 (a * 2 ^ (k - 64)) 0

/-! ## A coordinate -/

/-- Sub-tree `j` of coordinate `c` from base `b`, at the leaf's address `leafAt`, after the running
encoding `enc` (`none` before the first) and bound: its key and codeword hints and checks, the forest
key's dispatch, the encoding updated (into the digest's first cell `n17` for the last), the fold's
dispatch and the bound updated. The statements, the next base, the encoding, the bound and the
sub-tree's two top nodes. -/
def sSubtree (c j : Nat) (leafAt : V) (enc : Option V) (bound : V) (b : Nat) :
    List Stmt × Nat × V × V × (V × V) :=
  let w := 2 * c + j
  let keyAt : V := .n (b + 11)
  let fk := fkArms w keyAt (b + 12)
  let e : List Stmt × V × Nat :=
    if w + 1 = 16 then ([addS (.n 17) (enc.getD (.n 0)) fk.2.2.2], .n 17, fk.2.1)
    else match enc with
      | none => ([], fk.2.2.2, fk.2.1)
      | some en => ([addS (.n fk.2.1) en fk.2.2.2], .n fk.2.1, fk.2.1 + 1)
  let fd := foldArms keyAt (fun a l => .inl (sSubTws (2 * a + l))) 3 fk.2.2.1 (.n (b + 1))
    (fun a => word (j * 2 ^ 39 + a * 2 ^ 40) 0 0) (fun a => cbMul a (58 + 3 * w)) e.2.2
  ([hintW "sp_keys" [.n b, .n (b + 1)]] ++ rangeS (.n b) g7W (b + 2) ++ [hintW "sp_words" [.n (b + 6)]] ++
    rangeS (.n (b + 6)) g255W (b + 7) ++ [addS keyAt leafAt (.n (b + 1)), .match_ (.n (b + 6)) fk.1] ++
    e.1 ++ [.match_ (.n b) fd.1, addS (.n fd.2.1) bound fd.2.2.2.2], fd.2.1 + 1, e.2.1, .n fd.2.1,
    (fd.2.2.1, fd.2.2.2.1))

/-- Coordinate `c` from base `b`: its leaf hint and check, the leaf's address and the tree leaf's
first two cells, the two sub-trees, the tree leaf `keccak_cells(subtops)`, the top fold's dispatch and
the bound updated (into the digest's second cell `n18` for the last). The statements, the next base,
the encoding, the bound and the coordinate's two top nodes. -/
def sCoord (c : Nat) (enc : Option V) (bound : V) (b : Nat) : List Stmt × Nat × V × V × (V × V) :=
  let leafAt : V := .n (b + 6)
  let s0 := sSubtree c 0 leafAt enc bound (b + 10)
  let s1 := sSubtree c 1 leafAt (some s0.2.2.1) s0.2.2.2.1 s0.2.1
  let f := s1.2.1
  let fd := foldArms leafAt
    (fun s l => .inr (s * 2 ^ 35 ^^^ (tw 19 + (l + 1) * (8 * hiMul) + s / 2 ^ (l + 1) * (64 * hiMul)))) 4
    (.n (f + 5)) (.n (b + 1)) (fun s => word (c * hiMul + s * 2 ^ 35) 0 0) (fun s => cbMul s (26 + 4 * c))
    (f + 18)
  let last := c + 1 = 8
  ([hintW "sp_leaves" [.n b, .n (b + 1)]] ++ rangeS (.n b) g15W (b + 2) ++
    [addS leafAt (sNode 0) (.n (b + 1)), copyS (.n (b + 7)) sPP, cst (b + 8) (word (tw 18) 0 0),
      addS (.n (b + 9)) leafAt (.n (b + 8))] ++ s0.1 ++ s1.1 ++
    [copyS (.n f) s1.2.2.2.2.1, copyS (.n (f + 1)) s1.2.2.2.2.2, cst (f + 2) (word 1 0 0),
      cst (f + 3) (word 0 0 0), cst (f + 4) (word (2 ^ 63) 0 0),
      kecS [.n (b + 7), .n (b + 9), s0.2.2.2.2.1, s0.2.2.2.2.2, .n f, .n (f + 1), .n (f + 2), .n (f + 3),
        .n (f + 4), .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)] (runV (f + 5) 13)
        false false,
      .match_ (.n b) fd.1, addS (if last then .n 18 else .n fd.2.1) s1.2.2.2.1 fd.2.2.2.2],
    if last then fd.2.1 else fd.2.1 + 1, s1.2.2.1, if last then .n 18 else .n fd.2.1,
    (fd.2.2.1, fd.2.2.2.1))

/-- Coordinates `c ..< c + m` from base `b`: the statements, the next base, the encoding, the bound
and the top nodes. -/
def sCoords : Nat → Nat → Option V → V → Nat → List Stmt × Nat × V × V × List V
  | 0, _, enc, bound, b => ([], b, enc.getD (.n 0), bound, [])
  | m + 1, c, enc, bound, b =>
      let x := sCoord c enc bound b
      let rest := sCoords m (c + 1) (some x.2.2.1) x.2.2.2.1 x.2.1
      (x.1 ++ rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1, x.2.2.2.2.1 :: x.2.2.2.2.2 :: rest.2.2.2.2)

/-! ## The one-time signature and the tree -/

/-- leanSPHINCS's chain step: the address `idx + (TW_CHAIN + i·2^32 + s·2^61)`, then
`keccak([P, a], [v, 0], walks[o:o + 13], len=48)` (`walk`, `lean_ethereum.py:3391`). -/
def sWots (power : Nat → V) : WotsT where
  step i s v c o := cst c (word (tw 1 + i * hiMul + s * stepMul) 0 0) ::
    addS (.n (c + 1)) (sNode 0) (.n c) :: k48 (.n (c + 1)) v (c + 2) o
  size := 3
  power := power

/-- The body of `verify_sig_lean_sphincs`. -/
def sBody : List Stmt :=
  let cs := sCoords 8 0 none (.n 161) 206
  let b := cs.2.1
  let fb := sFromBytes (.n (b + 3)) [.n (b + 2), .n (b + 1), .n b] g255W (b + 4)
  let tops : List V := [.n 162, .n 164] ++ cs.2.2.2.2 ++ [.n fb.2.1]
  let enc := kMsg sPad (tops.map KC.cell) 292 true none (fb.2.1 + 1)
  let pb := enc.2.1
  let cw := codewordT (sWots fun s => .n (pb + s)) 21 sTarget (.n enc.2.2) (pb + 10)
  let c := cw.2.1
  let leaf := kMsg sPad ((sPP :: V.n (c + 1) :: cw.2.2).map KC.cell) 1056 false none (c + 2)
  let mk := merkleT sPad sPP sBit (fun l => if l + 1 = 26 then none else some (sNode (l + 1)))
    (fun l => tw 3 + (l + 1) * hiMul) 26 0 (.n leaf.2.2) leaf.2.1
  sPrologue ++ cs.1 ++ [hintW "sp_counter" (runV b 4)] ++ fb.1 ++ [copyS (.n fb.2.1) fb.2.2] ++ enc.1 ++
    (List.range 10).map (fun s => cst (pb + s) (word (2 ^ s) 0 0)) ++ cw.1 ++
    [cst c (word (tw 2) 0 0), addS (.n (c + 1)) (sNode 0) (.n c)] ++ leaf.1 ++ mk.1 ++
    [loadS (.n mk.2.1) (.n 0) 0, .atom (.assertEq mk.2.2 (.n mk.2.1)), .ret []]

end
end LeanVM.Guest.B1.Sig
