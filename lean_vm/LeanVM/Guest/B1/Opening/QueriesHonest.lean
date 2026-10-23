/-
  LeanVM.Guest.B1.Opening.QueriesHonest

  The honest values of one query of `opening_queries`, by index: what the completeness direction
  builds its valuation from.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesMain

/-!
# One query's honest values

`QD` is what an honest query is made of: the shape, its first value, whether it emits the padding
run, the row's words, the weights, the position `q`, the siblings below the cap, the path's frame
address, the cap's and the flags' pointers, and the memory (for the frame run's spare cells).
`qVal d i` is the value of index `i` of the query's expansion (`oqQueryT`), piece by piece:

* the row's words `ofK`, the packs `y`, `y·r`, `r + y·r` (`qPackV`);
* the dot product: per term the assembled word (deeper), the weight, the product, the running sum
  (`qPartV`), per group the weight, the product, the running dot product (`qDotAfterV`);
* the padding run `1, 0, 0, 0, 0`;
* the leaf hash: per block the XORed inputs and the permutation's output (`qLeafO`, `qLeafI`);
* the path: the children `pathCell`, the frame address, the frame run's spare cells (the memory
  there), the step `pp·5`; per level the bit, the selected child's address, `0x80`, the pair's
  permutation (`qLevelIns`);
* the cap leaf: the products of the cap bits' factors (`qCapQ`), the flag, the cap leaf's address.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- An honest query. -/
structure QD where
  s : Oq
  b : ℕ
  emit : Bool
  pr : ℕ
  row : List K
  w : ℕ → E
  q : ℕ
  sibs : List Digest
  pp : E
  capv : E
  flagsv : E
  rd : Reader

namespace QD

variable (d : QD)

/-- The padding run's first value. -/
def prV : ℕ := oqPr d.s d.b d.emit d.pr
/-- The first value of the dot product. -/
def k1 : ℕ := oqK1 d.b d.s.R
/-- The first value of the leaf hash. -/
def kL : ℕ := oqKL d.s d.b d.emit
/-- The first hinted child. -/
def ch : ℕ := oqCh d.s d.b d.emit
/-- The cap section. -/
def Cq : ℕ := oqCq d.s d.ch
/-- The cap tail. -/
def z : ℕ := d.Cq + 5 + 6 * (d.s.cd - 2)

/-- Row word `j`. -/
def rw (j : ℕ) : E := ofK (d.row.getD j 0)

/-- The packed cell `j`. -/
def pk (j : ℕ) : E := d.rw (2 * j) + word 0 1 0 * d.rw (2 * j + 1)

/-- The row's `E` word `jw`. -/
def W (jw : ℕ) : E := rowWord d.s.base d.row jw

/-- The running sum of group `h` after its term `l`. -/
def partV (h l : ℕ) : E :=
  ((List.range (l + 1)).map fun l' ↦ d.W (d.s.lo * h + l') * d.w l').foldl (· + ·) 0

/-- The dot product after group `h`. -/
def dotAfterV (h : ℕ) : E :=
  ((List.range (h + 1)).map fun h' ↦ d.w (d.s.lo + h') * d.partV h' (d.s.lo - 1)).foldl (· + ·) 0

/-- A deeper level's word statements' values, offset `o < 3`. -/
def wordStmtV (jw o : ℕ) : E :=
  if jw % 2 = 0 then
    [word 0 0 1, word 0 0 1 * d.rw (3 * jw + 2), d.W jw].getD o 0
  else
    [word 0 1 0, word 0 1 0 * d.pk ((3 * jw + 1) / 2), d.W jw].getD o 0

/-- Term `l` of group `h`, offset `o`. -/
def termV (h l o : ℕ) : E :=
  if o < d.s.tsz then d.wordStmtV (d.s.lo * h + l) o
  else if o = d.s.tsz then d.w l
  else if o = d.s.tsz + 1 then d.W (d.s.lo * h + l) * d.w l
  else d.partV h l

/-- The group of the dot product's offset `i`. -/
def dotH (G i : ℕ) : ℕ := if i < G then 0 else (i - G) / (G + 1) + 1

/-- The offset within its group. -/
def dotR (G i : ℕ) : ℕ := if dotH G i = 0 then i else i + 1 - dotH G i * (G + 1)

/-- The term of a group's offset `r`. -/
def termL (t r : ℕ) : ℕ := if r < 2 + t then 0 else (r - (2 + t)) / (3 + t) + 1

/-- The offset within its term. -/
def termO (t r : ℕ) : ℕ := if r < 2 + t then r else (r - (2 + t)) % (3 + t)

/-- The dot product's value at offset `i`. -/
def dotV (i : ℕ) : E :=
  if dotR d.s.G i < d.s.G - 2 then
    d.termV (dotH d.s.G i) (termL d.s.tsz (dotR d.s.G i)) (termO d.s.tsz (dotR d.s.G i))
  else if dotR d.s.G i = d.s.G - 2 then d.w (d.s.lo + dotH d.s.G i)
  else if dotR d.s.G i = d.s.G - 1 then
    d.w (d.s.lo + dotH d.s.G i) * d.partV (dotH d.s.G i) (d.s.lo - 1)
  else d.dotAfterV (dotH d.s.G i)

/-- The padded message cell `m` of the leaf hash. -/
def P (m : ℕ) : E := if m < d.s.ncells then d.pk m else if m = d.s.ncells then word 1 0 0 else oqW80 d.s

/-- The leaf hash's state before block `k`, as the cells block `k - 1` writes. -/
def leafO : ℕ → Fin 13 → E
  | 0, _ => 0
  | k + 1, c => cellsOfState (keccakF (stateOfCells (fun c' ↦
      if k = 0 then (if c'.val < 9 then d.P c'.val else 0)
      else if c'.val < 9 then leafO k c' + d.P (17 * k / 2 + c'.val) else leafO k c')
      (inLayout k))) (outLayout d.s.B k) c

/-- The cells the leaf's block `k` reads. -/
def leafI (k : ℕ) (c : Fin 13) : E :=
  if k = 0 then (if c.val < 9 then d.P c.val else 0)
  else if c.val < 9 then d.leafO k c + d.P (17 * k / 2 + c.val) else d.leafO k c

/-- The leaf hash's value at offset `i`: block `0`'s outputs, then per block the XORed inputs (the
last's `0x80` constant before its cell `8`) and the outputs. -/
def leafV (i : ℕ) : E :=
  if i < 13 then d.leafO 1 (Fin.ofNat 13 i)
  else
    let k := min ((i - 13) / 22 + 1) (d.s.B - 1)
    let r := i - (13 + (k - 1) * 22)
    if k + 1 = d.s.B then
      (if r < 8 then d.leafI k (Fin.ofNat 13 r)
        else if r = 8 then oqW80 d.s
        else if r = 9 then d.leafI k 8
        else d.leafO (k + 1) (Fin.ofNat 13 (r - 10)))
    else
      (if r < 9 then d.leafI k (Fin.ofNat 13 r) else d.leafO (k + 1) (Fin.ofNat 13 (r - 9)))

/-- The leaf's digest. -/
def leaf : Digest := hashWords d.row

/-- Path cell `k`. -/
def pc (k : ℕ) : E := pathCell d.leaf d.q d.sibs k

/-- The path's prefix at offset `o < 83`: the children, the frame address, the frame run's spare
cells, `5`, the step. -/
def preV (o : ℕ) : E :=
  if o < 4 * d.s.pd then d.pc o
  else if o = 4 * d.s.pd then d.pp
  else if o < 81 then (d.rd (d.pp.limb 0 * Parameters.gpow (o - 1))).getD 0
  else if o = 81 then word 5 0 0
  else d.pp * word 5 0 0

/-- The bit of level `l`. -/
def bit (l : ℕ) : E := bitE (d.q.testBit l)

/-- The cells level `l`'s permutation reads. -/
def levelIns (l : ℕ) : List E :=
  [d.pc (4 * l), d.pc (4 * l + 1), d.pc (4 * l + 2), d.pc (4 * l + 3), word 1 0 0, word 0 0 0,
    word 0 0 0, word 0 0 0, word (2 ^ 63) 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0]

/-- Level `l`'s value at offset `o < 17`. -/
def levelV (l o : ℕ) : E :=
  if o = 0 then d.bit l
  else if o = 1 then d.bit l * (d.pp * word 5 0 0)
  else if o = 2 then d.pp + d.bit l * (d.pp * word 5 0 0)
  else if o = 3 then word (2 ^ 63) 0 0
  else cellsOfState (permOf (d.levelIns l)) false (Fin.ofNat 13 (o - 4))

/-- The product of the cap bits' factors after bit `j`. -/
def capQ : ℕ → E
  | 0 => word 1 0 0 + d.bit (d.s.pd + 1) * word (capFac.getD 0 0) 0 0
  | j + 1 => capQ j * (word 1 0 0 + d.bit (d.s.pd + 2 + j) * word (capFac.getD (j + 1) 0) 0 0)

/-- The cap head at offset `o < 5`. -/
def capHeadV (o : ℕ) : E :=
  [word 1 0 0, d.bit (d.s.pd + 1), word (capFac.getD 0 0) 0 0,
    d.bit (d.s.pd + 1) * word (capFac.getD 0 0) 0 0, d.capQ 0].getD o 0

/-- Cap bit `j ≥ 1` at offset `o < 6`. -/
def capBitV (j o : ℕ) : E :=
  [word 1 0 0, d.bit (d.s.pd + 1 + j), word (capFac.getD j 0) 0 0,
    d.bit (d.s.pd + 1 + j) * word (capFac.getD j 0) 0 0,
    word 1 0 0 + d.bit (d.s.pd + 1 + j) * word (capFac.getD j 0) 0 0, d.capQ j].getD o 0

/-- The cap tail at offset `o < 11`. -/
def capTailV (o : ℕ) : E :=
  let qv := d.capQ (d.s.cd - 2)
  [d.flagsv * qv, word 1 0 0, qv * qv, d.capv * (qv * qv), d.capv * (qv * qv) * (qv * qv),
    word 1 0 0, d.bit d.s.pd, word 5 0 0, d.bit d.s.pd * word 5 0 0,
    word 1 0 0 + d.bit d.s.pd * word 5 0 0,
    d.capv * (qv * qv) * (qv * qv) * (word 1 0 0 + d.bit d.s.pd * word 5 0 0)].getD o 0

/-- **The honest value of index `i` of the query.** -/
def val (i : ℕ) : E :=
  if i < d.b + d.s.R then d.rw (i - d.b)
  else if i < d.k1 then
    [word 0 1 0, word 0 1 0 * d.rw (2 * ((i - d.b - d.s.R) / 3) + 1),
      d.pk ((i - d.b - d.s.R) / 3)].getD ((i - d.b - d.s.R) % 3) 0
  else if i < d.k1 + d.s.D then d.dotV (i - d.k1)
  else if i < d.kL then [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0].getD
    (i - (d.k1 + d.s.D)) 0
  else if i < d.ch then d.leafV (i - d.kL)
  else if i < d.ch + 83 then d.preV (i - d.ch)
  else if i < d.Cq then d.levelV ((i - (d.ch + 83)) / 17) ((i - (d.ch + 83)) % 17)
  else if i < d.Cq + 5 then d.capHeadV (i - d.Cq)
  else if i < d.z then d.capBitV ((i - (d.Cq + 5)) / 6 + 1) ((i - (d.Cq + 5)) % 6)
  else d.capTailV (i - d.z)

end QD

namespace QD

variable (d : QD)

/-! ## The pieces' places -/

theorem k1_eq : d.k1 = d.b + d.s.R + 3 * (d.s.R / 2) := rfl
theorem kL_eq : d.kL = d.k1 + d.s.D + (if d.emit then 5 else 0) := rfl
theorem ch_eq : d.ch = d.kL + d.s.chainLen := rfl
theorem Cq_eq : d.Cq = d.ch + 83 + 17 * d.s.pd := rfl
theorem z_eq : d.z = d.Cq + 5 + 6 * (d.s.cd - 2) := rfl

theorem end_eq : oqEnd d.s d.b d.emit = d.z + 11 := by
  simp only [oqEnd, z_eq, Cq_eq, ch_eq, oqCq, oqL0, QD.kL, oqCh]; omega

theorem val_row {j : ℕ} (hj : j < d.s.R) : d.val (d.b + j) = d.rw j := by
  unfold val; simp [hj]

theorem val_pack {j t : ℕ} (hj : j < d.s.R / 2) (ht : t < 3) :
    d.val (d.b + d.s.R + 3 * j + t) =
      [word 0 1 0, word 0 1 0 * d.rw (2 * j + 1), d.pk j].getD t 0 := by
  unfold val
  have := k1_eq d
  simp only [show ¬ d.b + d.s.R + 3 * j + t < d.b + d.s.R by omega,
    show d.b + d.s.R + 3 * j + t < d.k1 by omega, ↓reduceIte,
    show (d.b + d.s.R + 3 * j + t - d.b - d.s.R) / 3 = j by omega,
    show (d.b + d.s.R + 3 * j + t - d.b - d.s.R) % 3 = t by omega]

theorem val_dot {i : ℕ} (hi : i < d.s.D) : d.val (d.k1 + i) = d.dotV i := by
  unfold val
  have := k1_eq d
  simp only [show ¬ d.k1 + i < d.b + d.s.R by omega, show ¬ d.k1 + i < d.k1 by omega,
    show d.k1 + i < d.k1 + d.s.D by omega, ↓reduceIte, Nat.add_sub_cancel_left]

theorem val_pad (he : d.emit = true) {i : ℕ} (hi : i < 5) :
    d.val (d.k1 + d.s.D + i) =
      [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0].getD i 0 := by
  unfold val
  have := k1_eq d
  have hkL : d.kL = d.k1 + d.s.D + 5 := by rw [kL_eq, he]; rfl
  simp only [show ¬ d.k1 + d.s.D + i < d.b + d.s.R by omega,
    show ¬ d.k1 + d.s.D + i < d.k1 by omega, show ¬ d.k1 + d.s.D + i < d.k1 + d.s.D by omega,
    show d.k1 + d.s.D + i < d.kL by omega, ↓reduceIte, Nat.add_sub_cancel_left]

theorem val_leaf {i : ℕ} (hi : i < d.s.chainLen) : d.val (d.kL + i) = d.leafV i := by
  unfold val
  have := k1_eq d
  have h1 := kL_eq d
  have h2 : d.k1 + d.s.D ≤ d.kL := by rw [h1]; split <;> omega
  simp only [show ¬ d.kL + i < d.b + d.s.R by omega, show ¬ d.kL + i < d.k1 by omega,
    show ¬ d.kL + i < d.k1 + d.s.D by omega, show ¬ d.kL + i < d.kL by omega,
    show d.kL + i < d.ch by rw [ch_eq]; omega, ↓reduceIte, Nat.add_sub_cancel_left]

theorem le_kL : d.k1 + d.s.D ≤ d.kL := by rw [kL_eq]; split <;> omega

theorem val_pre {o : ℕ} (ho : o < 83) : d.val (d.ch + o) = d.preV o := by
  unfold val
  have := k1_eq d
  have h2 := le_kL d
  have h3 := ch_eq d
  simp only [show ¬ d.ch + o < d.b + d.s.R by omega, show ¬ d.ch + o < d.k1 by omega,
    show ¬ d.ch + o < d.k1 + d.s.D by omega, show ¬ d.ch + o < d.kL by omega,
    show ¬ d.ch + o < d.ch by omega, show d.ch + o < d.ch + 83 by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]

theorem val_level {l o : ℕ} (hl : l < d.s.pd) (ho : o < 17) :
    d.val (d.ch + 83 + 17 * l + o) = d.levelV l o := by
  unfold val
  have := k1_eq d
  have h2 := le_kL d
  have h3 := ch_eq d
  have h4 := Cq_eq d
  simp only [show ¬ d.ch + 83 + 17 * l + o < d.b + d.s.R by omega,
    show ¬ d.ch + 83 + 17 * l + o < d.k1 by omega,
    show ¬ d.ch + 83 + 17 * l + o < d.k1 + d.s.D by omega,
    show ¬ d.ch + 83 + 17 * l + o < d.kL by omega, show ¬ d.ch + 83 + 17 * l + o < d.ch by omega,
    show ¬ d.ch + 83 + 17 * l + o < d.ch + 83 by omega,
    show d.ch + 83 + 17 * l + o < d.Cq by omega, ↓reduceIte]
  rw [show (d.ch + 83 + 17 * l + o - (d.ch + 83)) / 17 = l by omega,
    show (d.ch + 83 + 17 * l + o - (d.ch + 83)) % 17 = o by omega]

theorem val_capHead {o : ℕ} (ho : o < 5) : d.val (d.Cq + o) = d.capHeadV o := by
  unfold val
  have := k1_eq d
  have h2 := le_kL d
  have h3 := ch_eq d
  have h4 := Cq_eq d
  simp only [show ¬ d.Cq + o < d.b + d.s.R by omega, show ¬ d.Cq + o < d.k1 by omega,
    show ¬ d.Cq + o < d.k1 + d.s.D by omega, show ¬ d.Cq + o < d.kL by omega,
    show ¬ d.Cq + o < d.ch by omega, show ¬ d.Cq + o < d.ch + 83 by omega,
    show ¬ d.Cq + o < d.Cq by omega, show d.Cq + o < d.Cq + 5 by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]

theorem val_capBit {j o : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ d.s.cd - 2) (ho : o < 6) :
    d.val (d.Cq + 5 + 6 * (j - 1) + o) = d.capBitV j o := by
  unfold val
  have := k1_eq d
  have h2 := le_kL d
  have h3 := ch_eq d
  have h4 := Cq_eq d
  have h5 := z_eq d
  simp only [show ¬ d.Cq + 5 + 6 * (j - 1) + o < d.b + d.s.R by omega,
    show ¬ d.Cq + 5 + 6 * (j - 1) + o < d.k1 by omega,
    show ¬ d.Cq + 5 + 6 * (j - 1) + o < d.k1 + d.s.D by omega,
    show ¬ d.Cq + 5 + 6 * (j - 1) + o < d.kL by omega,
    show ¬ d.Cq + 5 + 6 * (j - 1) + o < d.ch by omega,
    show ¬ d.Cq + 5 + 6 * (j - 1) + o < d.ch + 83 by omega,
    show ¬ d.Cq + 5 + 6 * (j - 1) + o < d.Cq by omega,
    show ¬ d.Cq + 5 + 6 * (j - 1) + o < d.Cq + 5 by omega,
    show d.Cq + 5 + 6 * (j - 1) + o < d.z by omega, ↓reduceIte]
  rw [show (d.Cq + 5 + 6 * (j - 1) + o - (d.Cq + 5)) / 6 + 1 = j by omega,
    show (d.Cq + 5 + 6 * (j - 1) + o - (d.Cq + 5)) % 6 = o by omega]

theorem val_capTail {o : ℕ} (ho : o < 11) : d.val (d.z + o) = d.capTailV o := by
  unfold val
  have := k1_eq d
  have h2 := le_kL d
  have h3 := ch_eq d
  have h4 := Cq_eq d
  have h5 := z_eq d
  simp only [show ¬ d.z + o < d.b + d.s.R by omega, show ¬ d.z + o < d.k1 by omega,
    show ¬ d.z + o < d.k1 + d.s.D by omega, show ¬ d.z + o < d.kL by omega,
    show ¬ d.z + o < d.ch by omega, show ¬ d.z + o < d.ch + 83 by omega,
    show ¬ d.z + o < d.Cq by omega, show ¬ d.z + o < d.Cq + 5 by omega,
    show ¬ d.z + o < d.z by omega, ↓reduceIte, Nat.add_sub_cancel_left]

end QD

namespace QD

/-! ## Decoding the dot product -/

/-- The offset of group `h`. -/
def gsOff (G h : ℕ) : ℕ := if h = 0 then 0 else h * (G + 1) - 1

/-- The offset of term `l` in its group. -/
def tsOff (t l : ℕ) : ℕ := if l = 0 then 0 else (2 + t) + (l - 1) * (3 + t)

theorem dotH_eq {G h r : ℕ} (hG : 2 ≤ G) (hr : r < (if h = 0 then G else G + 1)) :
    dotH G (gsOff G h + r) = h ∧ dotR G (gsOff G h + r) = r := by
  unfold dotR dotH gsOff
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp only [↓reduceIte] at hr ⊢
    simp [hr]
  · simp only [show h ≠ 0 by omega, ↓reduceIte] at hr ⊢
    obtain ⟨a, rfl⟩ : ∃ a, h = a + 1 := ⟨h - 1, by omega⟩
    have hm : (a + 1) * (G + 1) = (G + 1) * a + (G + 1) := by ring
    rw [hm]
    have hdiv : ((G + 1) * a + (G + 1) - 1 + r - G) / (G + 1) = a := by
      rw [show (G + 1) * a + (G + 1) - 1 + r - G = (G + 1) * a + r by omega,
        Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]
    have hlt : ¬ (G + 1) * a + (G + 1) - 1 + r < G := by omega
    simp only [hlt, ↓reduceIte, hdiv, true_and]
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    omega

theorem termL_eq {t l o : ℕ} (ho : o < (if l = 0 then 2 + t else 3 + t)) :
    termL t (tsOff t l + o) = l ∧ termO t (tsOff t l + o) = o := by
  unfold termL termO tsOff
  rcases Nat.eq_zero_or_pos l with rfl | hpos
  · simp only [↓reduceIte] at ho ⊢
    simp [ho]
  · simp only [show l ≠ 0 by omega, ↓reduceIte] at ho ⊢
    obtain ⟨a, rfl⟩ : ∃ a, l = a + 1 := ⟨l - 1, by omega⟩
    have e : 2 + t + (a + 1 - 1) * (3 + t) + o - (2 + t) = (3 + t) * a + o := by
      rw [Nat.add_sub_cancel]; ring_nf; omega
    simp only [show ¬ 2 + t + (a + 1 - 1) * (3 + t) + o < 2 + t by omega, ↓reduceIte, e,
      Nat.mul_add_div (show 0 < 3 + t by omega), Nat.div_eq_of_lt ho, Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt ho, and_true]

/-- The dot product's offset of term `l`'s value `o` in group `h`. -/
theorem oqTs_eq (s : Oq) (b h l : ℕ) :
    oqTs s b h l = oqK1 b s.R + gsOff s.G h + tsOff s.tsz l := by
  simp [oqTs, oqGs, gsOff, tsOff]

theorem G_eq (s : Oq) : s.G = (2 + s.tsz) + (s.lo - 1) * (3 + s.tsz) + 2 := rfl


/-- The shape's numbers. -/
theorem shape_nums {s : Oq} (hs : s.RowShape) :
    (s.base = 1 ∧ s.I = 64 ∧ s.tsz = 0 ∧ s.lo = 8 ∧ s.G = 25 ∧ s.R = 64 ∧ s.D = 207 ∧
      s.ncells = 32 ∧ s.B = 4 ∧ s.chainLen = 80) ∨
    (s.base = 0 ∧ s.I = 16 ∧ s.tsz = 3 ∧ s.lo = 8 ∧ s.G = 49 ∧ s.R = 48 ∧ s.D = 99 ∧
      s.ncells = 24 ∧ s.B = 3 ∧ s.chainLen = 58) := by
  rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩
  · left; simp [Oq.tsz, Oq.lo, Oq.G, Oq.R, Oq.D, Oq.ncells, Oq.B, Oq.chainLen, rowLo, rate, hb, hI]
  · right; simp [Oq.tsz, Oq.lo, Oq.G, Oq.R, Oq.D, Oq.ncells, Oq.B, Oq.chainLen, rowLo, rate, hb, hI]

variable (d : QD)

theorem dotV_term (hs : d.s.RowShape) {h l o : ℕ} (hl : l < d.s.lo)
    (ho : o < (if l = 0 then 2 + d.s.tsz else 3 + d.s.tsz)) :
    d.dotV (gsOff d.s.G h + tsOff d.s.tsz l + o) = d.termV h l o := by
  have hr : tsOff d.s.tsz l + o < d.s.G - 2 := by
    unfold tsOff
    rcases shape_nums hs with ⟨-, -, ht, hlo, hG, -⟩ | ⟨-, -, ht, hlo, hG, -⟩ <;>
      simp only [ht, hlo, hG] at ho hl ⊢ <;> split <;> split at ho <;> omega
  have hG2 : 2 ≤ d.s.G := by omega
  obtain ⟨e1, e2⟩ := dotH_eq (G := d.s.G) (h := h) (r := tsOff d.s.tsz l + o) hG2
    (by split <;> omega)
  rw [Nat.add_assoc]
  unfold dotV
  rw [e1, e2]
  simp only [hr, ↓reduceIte]
  obtain ⟨f1, f2⟩ := termL_eq (t := d.s.tsz) (l := l) (o := o) ho
  rw [f1, f2]

theorem dotV_tail (hs : d.s.RowShape) {h o : ℕ} (ho : o < (if h = 0 then 2 else 3)) :
    d.dotV (gsOff d.s.G h + (d.s.G - 2 + o)) =
      [d.w (d.s.lo + h), d.w (d.s.lo + h) * d.partV h (d.s.lo - 1), d.dotAfterV h].getD o 0 := by
  have hG : 2 ≤ d.s.G := by
    rcases shape_nums hs with ⟨-, -, -, -, hG, -⟩ | ⟨-, -, -, -, hG, -⟩ <;> omega
  obtain ⟨e1, e2⟩ := dotH_eq (G := d.s.G) (h := h) (r := d.s.G - 2 + o) hG (by split at ho <;> split <;> omega)
  unfold dotV
  rw [e1, e2]
  rcases (show o = 0 ∨ o = 1 ∨ o = 2 by split at ho <;> omega) with rfl | rfl | rfl
  · simp
  · rw [show d.s.G - 2 + 1 = d.s.G - 1 by omega]
    simp only [show ¬ d.s.G - 1 < d.s.G - 2 by omega, show ¬ d.s.G - 1 = d.s.G - 2 by omega,
      ↓reduceIte]; rfl
  · rw [show d.s.G - 2 + 2 = d.s.G by omega]
    simp only [show ¬ d.s.G < d.s.G - 2 by omega, show ¬ d.s.G = d.s.G - 2 by omega,
      show ¬ d.s.G = d.s.G - 1 by omega, ↓reduceIte]; rfl

end QD

end
end LeanVM.Guest.B1
