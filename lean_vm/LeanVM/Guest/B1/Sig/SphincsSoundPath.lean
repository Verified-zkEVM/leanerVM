/-
  LeanVM.Guest.B1.Sig.SphincsSoundPath

  `sp_path` (`lean_ethereum.py:3941-3961` at leanVM 56a4109f) is sound: whatever children are
  hinted, the node a path reaches is the tree's fold of the hinted siblings; with the pieces the
  FORS trees share (`is_child`, `sp_be16`, a node's 80-byte hash).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsForsT
public import LeanVM.Guest.B1.Sig.Merkle
public import LeanVM.Guest.B1.Sig.MerkleComplete
public import LeanVM.Guest.B1.Sig.Digest80

/-!
# `sp_path`, sound

* `pFold`, `nIter`: a path folded from the bottom, and level by level;
* `a1Hi h i`: limb `1` of an address cell `A1` of height `h` and index `i < 2^16`; `sBe16_sound`,
  `a1Hi_xor`: `sp_be16` places the index, and the indices of disjoint bits add;
* `isChild_sound`: `is_child` makes the node the hinted child its bit names, the two children being
  the node and its sibling `siblingOf` in the bit's order (`mPair`);
* `kMsg_cells_sound`, `kNode_sound`: a message of whole cells hashes to their `hcell`; a node's
  80-byte hash;
* `pathAdr`, `pNodeE`, `sPathSib`: a path's node addresses (type `TREE`), its nodes, the hinted
  siblings; `sPath_sound`: `sp_path` of `height` levels from leaf bit `off`, its bits those of
  `e < 2^height` and its shifts `e`'s, reaches `pFold` of `pNodeE`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

/-! ## Folds -/

/-- A path folded from the bottom: the node at level `l + 1` is `node l` of the one at `l`. -/
def pFold (node : Nat → E → E) : Nat → E → E
  | 0, v => v
  | l + 1, v => node l (pFold node l v)

/-- A path folded level by level, from level `l`, `m` levels. -/
def nIter (node : Nat → E → E) : Nat → Nat → E → E
  | _, 0, v => v
  | l, m + 1, v => nIter node (l + 1) m (node l v)

theorem nIter_pFold (node : Nat → E → E) : ∀ (m l : Nat) (v : E),
    nIter node l m (pFold node l v) = pFold node (l + m) v
  | 0, _, _ => rfl
  | m + 1, l, v => by
      rw [nIter, show node l (pFold node l v) = pFold node (l + 1) v from rfl,
        nIter_pFold node m (l + 1), show l + 1 + m = l + (m + 1) by omega]

theorem nIter_zero (node : Nat → E → E) (m : Nat) (v : E) : nIter node 0 m v = pFold node m v := by
  have := nIter_pFold node m 0 v
  rw [Nat.zero_add] at this
  exact this

/-- `nIter` from level `l` reads the levels from `l` only. -/
theorem nIter_congr {node node' : Nat → E → E} : ∀ (m l : Nat) (v : E),
    (∀ j, l ≤ j → node j = node' j) → nIter node l m v = nIter node' l m v
  | 0, _, _, _ => rfl
  | m + 1, l, v, h => by
      rw [nIter, nIter, h l le_rfl]
      exact nIter_congr m (l + 1) _ fun j hj => h j (by omega)

/-- `nIter` from level `l`, `m` levels, reads the levels `l ..< l + m` only. -/
theorem nIter_congr_lt {node node' : Nat → E → E} : ∀ (m l : Nat) (v : E),
    (∀ j, l ≤ j → j < l + m → node j = node' j) → nIter node l m v = nIter node' l m v
  | 0, _, _, _ => rfl
  | m + 1, l, v, h => by
      rw [nIter, nIter, h l le_rfl (by omega)]
      exact nIter_congr_lt m (l + 1) _ fun j hj1 hj2 => h j (by omega) (by omega)

/-! ## Address words -/

/-- Limb `1` of an address cell `A1` (`G:487-497`): the height (or chain index) `h` at bit `24`,
the index `i`'s high byte at bit `48` and its low byte at bit `56` (FIPS 205's bytes `27`, `30`,
`31`, big endian). -/
def a1Hi (h i : Nat) : Nat := 2 ^ 24 * h + 2 ^ 48 * (i / 256) + 2 ^ 56 * (i % 256)

theorem pow_mul_xor_pow_mul (s a b : Nat) : 2 ^ s * a ^^^ 2 ^ s * b = 2 ^ s * (a ^^^ b) := by
  rw [Nat.mul_comm (2 ^ s) a, Nat.mul_comm (2 ^ s) b, Nat.mul_comm (2 ^ s), ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, Nat.shiftLeft_xor_distrib]

theorem xor_two_pow_mul {s q r : Nat} (hr : r < 2 ^ s) : r ^^^ 2 ^ s * q = 2 ^ s * q + r := by
  rw [Nat.xor_comm, two_pow_mul_xor hr]

/-- **Indices of disjoint bits**: the `A1` limb of height `z` and index `P`, XOR the index `v`. -/
theorem a1Hi_xor {z P v : Nat} (hz : z < 2 ^ 24) (hP : P < 2 ^ 16) (hv : v < 2 ^ 16) :
    a1Hi z P ^^^ a1Hi 0 v = a1Hi z (P ^^^ v) := by
  have hPv : P ^^^ v < 2 ^ 16 := Nat.xor_lt_two_pow hP hv
  have e1 : ∀ x, x < 2 ^ 16 → (2 ^ 8 * (x % 256) ^^^ x / 256) = 2 ^ 8 * (x % 256) + x / 256 :=
    fun x hx => two_pow_mul_xor (by omega)
  have eP : a1Hi z P = 2 ^ 48 * (2 ^ 8 * (P % 256) ^^^ P / 256) ^^^ 2 ^ 24 * z := by
    rw [e1 P hP, two_pow_mul_xor (by omega), a1Hi]
    ring
  have ev : a1Hi 0 v = 2 ^ 48 * (2 ^ 8 * (v % 256) ^^^ v / 256) := by
    rw [e1 v hv, a1Hi]
    ring
  have eM : (2 ^ 8 * (P % 256) ^^^ P / 256) ^^^ (2 ^ 8 * (v % 256) ^^^ v / 256) =
      2 ^ 8 * ((P ^^^ v) % 256) ^^^ (P ^^^ v) / 256 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.xor_mod_two_pow, Nat.xor_div_two_pow,
      ← pow_mul_xor_pow_mul]
    ac_rfl
  rw [eP, ev, Nat.xor_assoc, Nat.xor_comm (2 ^ 24 * z), ← Nat.xor_assoc, pow_mul_xor_pow_mul, eM,
    e1 _ hPv, two_pow_mul_xor (by omega), a1Hi]
  ring

/-- Two words without a top limb add limb by limb. -/
theorem word_add_word (a b c d : Nat) : word a b 0 + word c d 0 = word (a ^^^ c) (b ^^^ d) 0 := by
  simp only [word, ofLimbs_add, ofBits_xor, Value.ofBits_zero, add_zero]

/-- A literal past the low limb. -/
theorem lit_hi {X : Nat} (h : X < 2 ^ 64) : lit (2 ^ 64 * X) = word 0 X 0 := by
  simp only [lit, Nat.mul_mod_right, Nat.mul_div_cancel_left _ (Nat.two_pow_pos 64),
    Nat.mod_eq_of_lt h]

/-- A word times `y·2^s`. -/
theorem eOfNat_mul_word_hi' {a s : Nat} (h : 2 ^ s * a < 2 ^ 64) :
    eOfNat a * word 0 (2 ^ s) 0 = word 0 (2 ^ s * a) 0 := by
  rw [eOfNat_eq_ofLimbs]
  simp only [word]
  rw [mul_comm, ← ofK_eq_ofLimbs, ofLimbs_mul_ofK, Value.ofBits_zero, zero_mul,
    ofBits_two_pow_mul h]

variable {rd : Reader} {σ : Val}

/-- `g^8 · g^56 = g^64`, reduced: `27`. -/
theorem ofBits_g64 : K.ofBits (2 ^ 56) * K.ofBits (2 ^ 8) = K.ofBits 27 := by decide +kernel

/-- **`sp_be16`'s two-byte value**: `v · 2^120 + (v / 2^8) · (g^8 · 2^120 + 2^112)`, the part of
`v · 2^120` past limb `1` (`g^64 = 27`) cancelled, is `v`'s two bytes reversed in limb `1`. -/
theorem be16_two {v : Nat} (hv : v < 2 ^ 16) :
    eOfNat v * word 0 (2 ^ 56) 0 + eOfNat (v / 256) * word 0 (2 ^ 48 + 27) 0 =
      word 0 (a1Hi 0 v) 0 := by
  have hq : v / 256 < 2 ^ 8 := by omega
  have hl : v % 256 < 2 ^ 8 := by omega
  rw [mul_comm, mul_comm (eOfNat (v / 256))]
  simp only [word, LeanVM.Protocol.Verifier.eOfNat, ofLimbs_mul_ofK, ofLimbs_add, ofBits_zero,
    zero_mul, add_zero]
  congr 1
  have ev : K.ofBits v = K.ofBits (2 ^ 8) * K.ofBits (v / 256) + K.ofBits (v % 256) := by
    rw [ofBits_two_pow_mul (by omega), ← ofBits_xor, two_pow_mul_xor hl]
    congr 1; omega
  have e27 : K.ofBits (2 ^ 48 + 27) = K.ofBits (2 ^ 48) + K.ofBits 27 := by
    rw [← ofBits_xor]; rfl
  have ea : a1Hi 0 v = 2 ^ 48 * (v / 256) ^^^ 2 ^ 56 * (v % 256) := by
    rw [show 2 ^ 56 * (v % 256) = 2 ^ 48 * (2 ^ 8 * (v % 256)) by ring, pow_mul_xor_pow_mul,
      Nat.xor_comm, two_pow_mul_xor hq, a1Hi]
    ring
  rw [ev, e27, ea, ofBits_xor, ← ofBits_two_pow_mul (by omega), ← ofBits_two_pow_mul (by omega)]
  calc K.ofBits (2 ^ 56) * (K.ofBits (2 ^ 8) * K.ofBits (v / 256) + K.ofBits (v % 256)) +
        (K.ofBits (2 ^ 48) + K.ofBits 27) * K.ofBits (v / 256)
      = K.ofBits (2 ^ 48) * K.ofBits (v / 256) + K.ofBits (2 ^ 56) * K.ofBits (v % 256) +
          (K.ofBits 27 * K.ofBits (v / 256) + K.ofBits 27 * K.ofBits (v / 256)) := by
        rw [← ofBits_g64]; ring
    _ = _ := by rw [k_add_self, add_zero]

/-- **`sp_be16`, sound**: an `n`-bit value `v` (`n ≤ 16`), its shift by eight given when it has a
second byte, is placed as the index of an `A1`. -/
theorem sBe16_sound {val : Nat → V} {pos n x v : Nat} (hn : n ≤ 16) (hv : v < 2 ^ n)
    (h0 : σ (val pos) = eOfNat v) (h8 : 9 ≤ n → σ (val (pos + 8)) = eOfNat (v / 256))
    (h : AtomsHold rd σ (sBe16 val pos n x).1) :
    σ (sBe16 val pos n x).2.2 = word 0 (a1Hi 0 v) 0 := by
  have hv16 : v < 2 ^ 16 := lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hn)
  by_cases h2 : (n + 7) / 8 = 2
  · have q8 := h8 (by omega)
    simp only [sBe16, h2, ↓reduceIte] at h ⊢
    have c0 : σ (.n x) = lit (2 ^ 120) := h.atom (a := .const (.n x) _) (by simp [cst])
    have a1 : σ (.n (x + 1)) = σ (val pos) * σ (.n x) := h.atom (a := .mul (.n (x + 1)) _ _) (by simp [mulS])
    have c2 : σ (.n (x + 2)) = be16HiW := h.atom (a := .const (.n (x + 2)) _) (by simp [cst])
    have a3 : σ (.n (x + 3)) = σ (val (pos + 8)) * σ (.n (x + 2)) :=
      h.atom (a := .mul (.n (x + 3)) _ _) (by simp [mulS])
    have a4 : σ (.n (x + 4)) = σ (.n (x + 1)) + σ (.n (x + 3)) :=
      h.atom (a := .add (.n (x + 4)) _ _) (by simp [addS])
    have hq : v / 256 < 2 ^ 8 := by omega
    have hl : v % 256 < 2 ^ 8 := by omega
    rw [a4, a1, a3, c0, c2, h0, q8, show (2 : Nat) ^ 120 = 2 ^ 64 * 2 ^ 56 by norm_num,
      lit_hi (by norm_num), be16HiW]
    exact be16_two (v := v) hv16
  · have hv8 : v < 256 := lt_of_lt_of_le hv (by
      calc 2 ^ n ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 256 := by norm_num)
    simp only [sBe16, h2, ↓reduceIte] at h ⊢
    have c0 : σ (.n x) = lit (2 ^ 120) := h.atom (a := .const (.n x) _) (by simp [cst])
    have a1 : σ (.n (x + 1)) = σ (val pos) * σ (.n x) := h.atom (a := .mul _ _ _) (by simp [mulS])
    rw [a1, c0, h0, show (2 : Nat) ^ 120 = 2 ^ 64 * 2 ^ 56 by norm_num, lit_hi (by norm_num),
      eOfNat_mul_word_hi' (by omega), a1Hi, Nat.div_eq_of_lt hv8, Nat.mod_eq_of_lt hv8]
    ring_nf

/-! ## `is_child` -/

/-- **`is_child`, sound**: the children are the node and its sibling, in the order of the bit. -/
theorem isChild_sound {cur bit : V} {x b : Nat} (hbit : IsBit (σ bit))
    (e1 : σ (.n b) = σ cur + σ (.n x)) (e2 : σ (.n (b + 1)) = σ (.n x) + σ (.n (x + 1)))
    (e3 : σ (.n b) = σ bit * σ (.n (b + 1))) :
    (σ (.n x), σ (.n (x + 1))) = mPair (decide (σ bit = 1)) (σ cur) (siblingOf σ bit x) := by
  rcases isBit_cases hbit with h0 | h1
  · rw [h0, zero_mul, e1] at e3
    have : σ cur = σ (.n x) := e_add_eq_zero_iff.mp e3
    simp [h0, this, mPair, siblingOf]
  · rw [h1, one_mul, e1, e2] at e3
    have : σ cur = σ (.n (x + 1)) :=
      add_left_cancel (a := σ (.n x)) (by rw [add_comm (σ (.n x))]; exact e3)
    simp [h1, this, mPair, siblingOf]

/-- A bit of `e` as a cell, pinned Boolean, and its `decide`. -/
theorem bit_facts {σ : Val} {bit : V} {e z : Nat} (hb : σ bit = if e.testBit z then 1 else 0) :
    IsBit (σ bit) ∧ decide (σ bit = 1) = e.testBit z := by
  refine ⟨by rw [hb]; split <;> simp [IsBit], ?_⟩
  rw [hb]
  cases e.testBit z <;> simp

/-! ## The hashes -/

theorem flatMap_cellBytes_length : ∀ cs : List E, (cs.flatMap cellBytes).length = 16 * cs.length
  | [] => rfl
  | c :: cs => by
      simp only [List.flatMap_cons, List.length_append, length_cellBytes,
        flatMap_cellBytes_length cs, List.length_cons]
      ring

/-- **A message of whole cells** hashes to their `hcell`. -/
theorem kMsg_cells_sound {pad : Nat} (hp : PadOK σ pad) {vs : List V} {len b : Nat}
    (hlen : len = 16 * vs.length)
    (h : AtomsHold rd σ (kMsg pad (vs.map KC.cell) len false none b).1) :
    (σ (.n (kMsg pad (vs.map KC.cell) len false none b).2.2),
        σ (.n ((kMsg pad (vs.map KC.cell) len false none b).2.2 + 1))) = hcell (vs.map σ) := by
  have hm : (vs.map KC.cell).map (KC.val σ) = vs.map σ := by
    rw [List.map_map]
    rfl
  have k := kMsg_sound (cells := vs.map KC.cell) (len := len) (tailRun := false) (out := none) hp
    (fun h => by simp at h) h (by simp [hlen]) (fun j hj => by
    rw [hm, cellsBytes_eq_flatMap, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
      rw [flatMap_cellBytes_length, List.length_map]; omega)]
    rfl)
  rw [k, hm, hcell, cellsBytes_eq_flatMap, List.take_of_length_le (by
    rw [flatMap_cellBytes_length, List.length_map]; omega)]

theorem kNode_shape (pad : Nat) (pp a0 adr k0 k1 : V) (y : Nat) :
    (kNode pad pp a0 adr k0 k1 y).2.1 = y + 17 ∧ (kNode pad pp a0 adr k0 k1 y).2.2 = y + 4 := by
  constructor <;> rfl

/-- **A node's 80-byte hash** of `P`, `A0`, its address and its two children, the padding set in
the cells after `kids[1]` (`pad_tail=1`). -/
theorem kNode_sound {pad : Nat} (hp : PadOK σ pad) {pp a0 adr k0 k1 : V} {y : Nat}
    (h : AtomsHold rd σ (kNode pad pp a0 adr k0 k1 y).1) :
    (σ (.n (y + 4)), σ (.n (y + 5))) = hcell [σ pp, σ a0, σ adr, σ k0, σ k1] := by
  obtain ⟨-, q1, q2, q3, q4⟩ := hp
  have c0 : σ (.n y) = word 1 0 0 := h.atom (a := .const _ _) (by simp [kNode, cst])
  have c1 : σ (.n (y + 1)) = word 0 0 0 := h.atom (a := .const _ _) (by simp [kNode, cst])
  have c2 : σ (.n (y + 2)) = word 0 0 0 := h.atom (a := .const _ _) (by simp [kNode, cst])
  have c3 : σ (.n (y + 3)) = word (2 ^ 63) 0 0 := h.atom (a := .const _ _) (by simp [kNode, cst])
  have z0 : word 0 0 0 = 0 := by simp only [word, Value.ofBits_zero]; exact zero_eq_ofLimbs.symm
  exact kec80_sound (o := y + 4) (t2 := .n (y + 1)) (t3 := .n (y + 2)) (h.sub fun s hs => by
    simp only [List.mem_singleton] at hs; subst hs; simp [kNode]) c0 (by rw [c1, z0])
    (by rw [c2, z0]) c3 q1 q2 q3 q4

/-- **One level of a tree**: the children hinted at `x` and checked by `is_child` against `cur` and
the bit `bit`, then hashed at the address `adr` holding `A`, give the parent of `cur` and its
sibling in the bit's order. -/
theorem level_sound {pad : Nat} (hp : PadOK σ pad) {pp a0 adr cur bit : V} {x y : Nat}
    (hbit : IsBit (σ bit))
    (hc : AtomsHold rd σ (isChildS cur (.n x) (.n (x + 1)) bit (x + 2)))
    (hk : AtomsHold rd σ (kNode pad pp a0 adr (.n x) (.n (x + 1)) y).1) :
    σ (.n (y + 4)) = (hcell [σ pp, σ a0, σ adr, (mPair (decide (σ bit = 1)) (σ cur)
      (siblingOf σ bit x)).1, (mPair (decide (σ bit = 1)) (σ cur) (siblingOf σ bit x)).2]).1 := by
  have e1 : σ (.n (x + 2)) = σ cur + σ (.n x) :=
    hc.atom (a := .add (.n (x + 2)) cur (.n x)) (by simp [isChildS, addS])
  have e2 : σ (.n (x + 3)) = σ (.n x) + σ (.n (x + 1)) :=
    hc.atom (a := .add (.n (x + 3)) (.n x) (.n (x + 1))) (by simp [isChildS, addS])
  have e3 : σ (.n (x + 2)) = σ bit * σ (.n (x + 3)) :=
    hc.atom (a := .mul (.n (x + 2)) bit (.n (x + 3))) (by simp [isChildS, mulS])
  rw [← isChild_sound hbit e1 e2 e3]
  exact congrArg Prod.fst (kNode_sound hp hk)

/-! ## The paths -/

/-- The address of a path's node at height `h`, index `i`: type `TREE`, no key pair. -/
def pathAdr (h i : Nat) : E := word (2 * 2 ^ 24) (a1Hi h i) 0

/-- A path's node at height `z + 1` from the one at `z`, the leaf `e`, its siblings `sib`. -/
def pNodeE (pp a0 : E) (e : Nat) (sib : Nat → E) (z : Nat) (v : E) : E :=
  (hcell [pp, a0, pathAdr (z + 1) (e >>> (z + 1)), (mPair (e.testBit z) v (sib z)).1,
    (mPair (e.testBit z) v (sib z)).2]).1

/-- A path level's width when `m` levels follow it. -/
def pathWidth (m : Nat) : Nat := if m = 0 then 22 else if (m + 7) / 8 = 2 then 28 else 25

/-- The hinted sibling of level `j` of `sPath … m z cur x` (`0` outside its levels). -/
def sPathSib (σ : Val) (bit : Nat → V) (off : Nat) : Nat → Nat → Nat → Nat → E
  | 0, _, _, _ => 0
  | m + 1, z, x, j => if j = z then siblingOf σ (bit (off + z)) x
      else sPathSib σ bit off m (z + 1) (x + pathWidth m) j

/-- A path level's address (`G:3953-3957`) from base `x`, `m` levels after it: below the root the
index `val (off + z + 1)` (`sBe16`) plus the constant, at the root the constant alone. The
statements, the next base and the address. -/
def sPathAddr (val : Nat → V) (off z m x : Nat) : List Stmt × Nat × V :=
  if m = 0 then ([cst x (lit (pathConst (z + 1)))], x + 1, .n x)
  else
    let be := sBe16 val (off + z + 1) m x
    (be.1 ++ [cst be.2.1 (lit (pathConst (z + 1))), addS (.n (be.2.1 + 1)) be.2.2 (.n be.2.1)],
      be.2.1 + 2, .n (be.2.1 + 1))

theorem sPath_succ (pad : Nat) (pp a0 : V) (bit val : Nat → V) (off m z : Nat) (cur : V) (x : Nat) :
    sPath pad pp a0 bit val off (m + 1) z cur x =
      ([hintW "siblings" [.n x, .n (x + 1)]] ++
        isChildS cur (.n x) (.n (x + 1)) (bit (off + z)) (x + 2) ++
          (sPathAddr val off z m (x + 4)).1 ++
          (kNode pad pp a0 (sPathAddr val off z m (x + 4)).2.2 (.n x) (.n (x + 1))
            (sPathAddr val off z m (x + 4)).2.1).1 ++
          (sPath pad pp a0 bit val off m (z + 1) (.n ((sPathAddr val off z m (x + 4)).2.1 + 4))
            ((sPathAddr val off z m (x + 4)).2.1 + 17)).1,
        (sPath pad pp a0 bit val off m (z + 1) (.n ((sPathAddr val off z m (x + 4)).2.1 + 4))
            ((sPathAddr val off z m (x + 4)).2.1 + 17)).2.1,
        (sPath pad pp a0 bit val off m (z + 1) (.n ((sPathAddr val off z m (x + 4)).2.1 + 4))
            ((sPathAddr val off z m (x + 4)).2.1 + 17)).2.2) := by
  simp only [sPath, sPathAddr, (kNode_shape ..).1, (kNode_shape ..).2]

theorem sBe16_next (val : Nat → V) (pos n x : Nat) :
    (sBe16 val pos n x).2.1 = x + (if (n + 7) / 8 = 2 then 5 else 2) := by
  unfold sBe16; split <;> rfl

/-- The address part of a path level ends `pathWidth m - 17` after its base. -/
theorem sPathAddr_next (val : Nat → V) (off z m x : Nat) :
    (sPathAddr val off z m (x + 4)).2.1 = x + pathWidth m - 17 := by
  unfold sPathAddr pathWidth
  by_cases hm0 : m = 0
  · simp [hm0]
  · simp only [hm0, ↓reduceIte, sBe16_next]
    split_ifs <;> omega

/-- **A path level's address, sound**: the node at height `z + 1` on the path of `e`, `m` levels
after it (`e < 2^(z + 1 + m)`). -/
theorem sPathAddr_sound {val : Nat → V} {off e z m x : Nat} (hzm : z + 1 + m ≤ 16)
    (he : e < 2 ^ (z + 1 + m))
    (hval : ∀ j, z < j → j ≤ z + m → σ (val (off + j)) = eOfNat (e >>> j))
    (hA : AtomsHold rd σ (sPathAddr val off z m x).1) :
    σ (sPathAddr val off z m x).2.2 = pathAdr (z + 1) (e >>> (z + 1)) := by
  unfold sPathAddr at hA ⊢
  by_cases hm0 : m = 0
  · subst hm0
    simp only [↓reduceIte] at hA ⊢
    have c0 : σ (.n x) = lit (pathConst (z + 1)) := hA.atom (a := .const _ _) (by simp [cst])
    have hq : e >>> (z + 1) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (by simpa using he)
    have hlo : (2 * 2 ^ 24 + 2 ^ 88 * (z + 1)) % 2 ^ 64 = 2 * 2 ^ 24 := by omega
    have hhi : (2 * 2 ^ 24 + 2 ^ 88 * (z + 1)) / 2 ^ 64 % 2 ^ 64 = 2 ^ 24 * (z + 1) := by omega
    rw [c0, hq, pathAdr, a1Hi, pathConst, lit, hlo, hhi]
    simp only [Nat.zero_div, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  · simp only [hm0, ↓reduceIte] at hA ⊢
    have hv : e >>> (z + 1) < 2 ^ m := by
      rw [Nat.shiftRight_eq_div_pow]
      have : e < 2 ^ (z + 1) * 2 ^ m := by rw [← pow_add]; exact he
      exact Nat.div_lt_of_lt_mul this
    have hbv := sBe16_sound (rd := rd) (n := m) (x := x) (by omega) hv
      (by rw [show off + z + 1 = off + (z + 1) by omega, hval (z + 1) (by omega) (by omega)])
      (fun _ => by
        rw [show off + z + 1 + 8 = off + (z + 9) by omega, hval (z + 9) (by omega) (by omega),
          Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
          show (256 : Nat) = 2 ^ 8 from rfl, ← pow_add])
      hA.left
    have c1 : σ (.n (sBe16 val (off + z + 1) m x).2.1) = lit (pathConst (z + 1)) :=
      hA.right.atom (a := .const _ _) (by simp [cst])
    have a2 : σ (.n ((sBe16 val (off + z + 1) m x).2.1 + 1)) =
        σ (sBe16 val (off + z + 1) m x).2.2 + σ (.n (sBe16 val (off + z + 1) m x).2.1) :=
      hA.right.atom (a := .add _ _ _) (by simp [addS])
    have hv16 : e >>> (z + 1) < 2 ^ 16 :=
      lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [a2, hbv, c1, pathConst, lit, pathAdr, word_add_word]
    have hlo : (2 * 2 ^ 24 + 2 ^ 88 * (z + 1)) % 2 ^ 64 = 2 * 2 ^ 24 := by omega
    have hhi : (2 * 2 ^ 24 + 2 ^ 88 * (z + 1)) / 2 ^ 64 % 2 ^ 64 = 2 ^ 24 * (z + 1) := by omega
    rw [hlo, hhi, Nat.zero_xor, Nat.xor_comm]
    have := a1Hi_xor (z := z + 1) (P := 0) (v := e >>> (z + 1)) (by omega) (by norm_num) hv16
    rw [Nat.zero_xor] at this
    rw [← this, show a1Hi (z + 1) 0 = 2 ^ 24 * (z + 1) by simp [a1Hi]]

/-- **`sp_path`, sound**: from level `z` (base `x`), `m` levels to height `height`, the bits those
of `e < 2^height` and the shifted values `e`'s, the node reached is `nIter` of the levels, the
siblings those hinted (`sPathSib`). -/
theorem sPath_sound {pad : Nat} (hp : PadOK σ pad) {pp a0 : V} {bit val : Nat → V}
    {off e height : Nat}
    (hh : height ≤ 16) (he : e < 2 ^ height)
    (hbit : ∀ z < height, σ (bit (off + z)) = if e.testBit z then 1 else 0)
    (hval : ∀ z, z < height → σ (val (off + z)) = eOfNat (e >>> z)) :
    ∀ (m z : Nat) (cur : V) (x : Nat), z + m = height →
      AtomsHold rd σ (sPath pad pp a0 bit val off m z cur x).1 →
      σ (sPath pad pp a0 bit val off m z cur x).2.2 =
        nIter (pNodeE (σ pp) (σ a0) e (sPathSib σ bit off m z x)) z m (σ cur)
  | 0, _, _, _, _, _ => rfl
  | m + 1, z, cur, x, hm, hA => by
      rw [sPath_succ] at hA ⊢
      obtain ⟨hib, hd⟩ := bit_facts (hbit z (by omega))
      have hadr := sPathAddr_sound (off := off) (x := x + 4) (by omega)
        (by rw [show z + 1 + m = height by omega]; exact he)
        (fun j _ hj => hval j (by omega)) hA.left.left.right
      have hk := hA.left.right
      have hc : AtomsHold rd σ (isChildS cur (.n x) (.n (x + 1)) (bit (off + z)) (x + 2)) :=
        hA.left.left.left.sub fun s hs => List.mem_append_right _ hs
      have hlv := level_sound hp hib hc hk
      have hrest := sPath_sound hp hh he hbit hval m (z + 1) _ _ (by omega) hA.right
      have hfirst : σ (.n ((sPathAddr val off z m (x + 4)).2.1 + 4)) =
          pNodeE (σ pp) (σ a0) e (sPathSib σ bit off (m + 1) z x) z (σ cur) := by
        rw [hlv, hd, hadr]
        simp [pNodeE, sPathSib]
      rw [hrest, nIter, hfirst, sPathAddr_next,
        show x + pathWidth m - 17 + 17 = x + pathWidth m by unfold pathWidth; split_ifs <;> omega]
      refine nIter_congr _ _ _ fun j hj => ?_
      unfold pNodeE
      simp only [sPathSib, show j ≠ z by omega, ite_false]

end
end LeanVM.Guest.B1.Sig
