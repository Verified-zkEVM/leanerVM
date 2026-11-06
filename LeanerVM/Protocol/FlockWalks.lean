/-
  LeanerVM.Protocol.FlockWalks

  The two walks of a product-gate circuit's R1CS over `E` as compiled code runs them: on the
  words of the rows' and the columns' forms, the entries of `E` as their limbs' machine words,
  and a block of `0`s and `1`s by the parity of word-wise `and`s. The R1CS with these walks has
  the circuit's matrices.
-/

module

public import LeanerVM.Protocol.ToArkLib.Flock.CircuitFast
public import LeanerVM.Protocol.Field
public import LeanerVM.Parameters.ToCompPoly.BF64Fast
public import Batteries.Data.BitVec.Lemmas

/-!
# The walks of a circuit over `E`, on words

`ProductCircuit.toBlockR1CS` walks a block by summing `2 ^ m` entries per row, each entry's
matrix bit read through the row's gate lookup: `2 ^ 28` steps for the BLAKE2s circuit. Its forms
are dense, about `3,000` of the `2 ^ 14` positions each, so even a sparse walk over `E`, whose
addition works on three big integers, takes tens of seconds. `toBlockR1CSE` walks on words:

* the rows' forms as words (`rowTable`, built once), so that the forward walk reads the set bits
  of a form's words, highest first (`gatherWord`, by `Nat.log2` of a half word), and the
  backward walk scatters each row's entry onto the set bits of its form (`scatterFrom`), the rows
  read in order, the entries' limbs as six half-words that an array holds unboxed
  (`halvesTable`, `entryAt`);
* an entry of `E` as its three limbs' words, which `E`'s addition `xor`s (`gather`, one limb at a
  time, `gatherE`);
* a block of `0`s and `1`s, the prover's, packed into words, each row the parity of its form's
  word-wise `and` with the block (`ProductCircuit.evalW`), the bit read back as `0` or `1`
  (`rowsBool`).

`toBlockR1CSE_eq`: it is `toBlockR1CS E`, since two `BlockR1CS` with the same matrices are equal
(`BlockR1CS.ext_of`): the walks are fixed by their specifications. Nothing here transcribes a
source.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly FastBF64

@[expose] public section

namespace ProductCircuit

variable {m : ℕ}

/-! ## The set bits of a word -/

/-- The bit of a word is its number's bit. -/
private theorem getLsbD_toBitVec (w : UInt64) (b : ℕ) :
    w.toBitVec.getLsbD b = w.toNat.testBit b := rfl

/-- The index of the top set bit of a word, `Nat.log2` of a half below `2 ^ 32`, so that no big
number is built. -/
private def topBit (w : UInt64) : ℕ :=
  if w >>> 32 = 0 then Nat.log2 w.toNat else 32 + Nat.log2 (w >>> 32).toNat

/-- `topBit` is the word's `Nat.log2`. -/
private theorem topBit_eq (w : UInt64) : topBit w = Nat.log2 w.toNat := by
  have hsh : (w >>> 32).toNat = w.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_shiftRight]
    simp [Nat.shiftRight_eq_div_pow]
  unfold topBit
  split
  · rfl
  · rename_i h
    have hq : w.toNat / 2 ^ 32 ≠ 0 := fun h0 ↦ h (UInt64.toNat_inj.mp (by rw [hsh, h0]; rfl))
    have hn : w.toNat ≠ 0 := fun h0 ↦ hq (by rw [h0]; rfl)
    rw [hsh]
    symm
    rw [Nat.log2_eq_iff hn]
    have h1 := Nat.log2_self_le hq
    have h2 := Nat.lt_log2_self (n := w.toNat / 2 ^ 32)
    constructor
    · rw [pow_add, mul_comm]
      exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mp h1
    · have e : 2 ^ (32 + (w.toNat / 2 ^ 32).log2 + 1) =
          2 ^ ((w.toNat / 2 ^ 32).log2 + 1) * 2 ^ 32 := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mp h2

/-- The top bit of a nonzero word is below `64`. -/
private theorem log2_lt_64 (w : UInt64) (hn : w.toNat ≠ 0) : w.toNat.log2 < 64 :=
  (Nat.log2_lt hn).mpr w.toNat_lt

/-- The word with only bit `b` set, `b < 64`. -/
private theorem toNat_one_shiftLeft {b : ℕ} (hb : b < 64) :
    ((1 : UInt64) <<< b.toUInt64).toNat = 2 ^ b := by
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_one]
  have hb' : b.toUInt64.toNat = b := by simp; omega
  rw [hb', Nat.mod_eq_of_lt hb, Nat.one_shiftLeft,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hb)]

/-- A word with bit `b` flipped. -/
private def clearAt (w : UInt64) (b : ℕ) : UInt64 := w ^^^ ((1 : UInt64) <<< b.toUInt64)

/-- A word with its top bit cleared. -/
private abbrev clearTop (w : UInt64) : UInt64 := clearAt w (topBit w)

/-- Clearing the top bit of a nonzero word: bit `i` is the word's but at the top bit. -/
private theorem testBit_clearTop {w : UInt64} (hn : w.toNat ≠ 0) (i : ℕ) :
    (clearTop w).toNat.testBit i = (w.toNat.testBit i && decide (i ≠ w.toNat.log2)) := by
  rw [clearTop, clearAt, UInt64.toNat_xor, Nat.testBit_xor, topBit_eq,
    toNat_one_shiftLeft (log2_lt_64 w hn), Nat.testBit_two_pow]
  by_cases hi : i = w.toNat.log2
  · subst hi; simp [Nat.testBit_log2 hn]
  · have : (w.toNat.log2 = i) = False := propext ⟨fun h ↦ hi h.symm, False.elim⟩
    simp [hi, this]

/-- Clearing the top bit leaves a number below the top bit's power. -/
private theorem toNat_clearTop_lt {w : UInt64} (hn : w.toNat ≠ 0) :
    (clearTop w).toNat < 2 ^ w.toNat.log2 := by
  refine Nat.lt_pow_two_of_testBit _ fun i hi ↦ ?_
  rw [testBit_clearTop hn]
  by_cases h : i = w.toNat.log2
  · simp [h]
  · have : w.toNat < 2 ^ i := lt_of_lt_of_le Nat.lt_log2_self
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [Nat.testBit_eq_false_of_lt this]

/-- The facts a walk over the set bits of a nonzero word uses at its top bit. -/
private theorem top_facts {w : UInt64} (h : ¬ w = 0) {fuel : ℕ} (hw : w.toNat < 2 ^ (fuel + 1)) :
    w.toNat ≠ 0 ∧ w.toNat.log2 < 64 ∧ (clearTop w).toNat < 2 ^ fuel := by
  have hn : w.toNat ≠ 0 := fun h' ↦ h (UInt64.toNat_inj.mp (by simpa using h'))
  have hfuel : w.toNat.log2 < fuel + 1 := (Nat.log2_lt hn).mpr hw
  exact ⟨hn, log2_lt_64 w hn, lt_of_lt_of_le (toNat_clearTop_lt hn)
    (Nat.pow_le_pow_right (by norm_num) (by omega))⟩

/-! ## Gathering over the set bits -/

/-- `acc` `xor`ed with the words `V[base + b]` at the set bits `b` of `w`, highest first; `fuel`
bounds the steps. -/
private def gatherWord (V : Array UInt64) (base : ℕ) : ℕ → UInt64 → UInt64 → UInt64
  | 0, _, acc => acc
  | fuel + 1, w, acc =>
    if w = 0 then acc else
      let b := topBit w
      gatherWord V base fuel (clearAt w b) (acc ^^^ V.getD (base + b) 0)

/-- `gatherWord` adds the elements at the set bits of the word, as long as the fuel covers its
bits. -/
private theorem ofWord_gatherWord (V : Array UInt64) (base : ℕ) :
    ∀ (fuel : ℕ) (w acc : UInt64), w.toNat < 2 ^ fuel →
      ofWord (gatherWord V base fuel w acc) = ofWord acc +
        ∑ b ∈ Finset.range 64, if w.toNat.testBit b then ofWord (V.getD (base + b) 0) else 0
  | 0, w, acc, hw => by
    have : w.toNat = 0 := by simpa using hw
    simp [gatherWord, this]
  | fuel + 1, w, acc, hw => by
    rw [gatherWord]
    split
    · rename_i h
      subst h
      simp
    · rename_i h
      obtain ⟨hn, hlt, hc⟩ := top_facts h hw
      change ofWord (gatherWord V base fuel (clearTop w) _) = _
      rw [ofWord_gatherWord V base fuel _ _ hc, ofWord_xor, add_assoc, topBit_eq]
      congr 1
      symm
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hlt), Nat.testBit_log2 hn,
        ite_eq_left_of_eq_true _ _ (eq_self true)]
      congr 1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hlt)]
      have hz : (if (clearTop w).toNat.testBit w.toNat.log2 then
          ofWord (V.getD (base + w.toNat.log2) 0) else 0) = 0 := by
        rw [testBit_clearTop hn]; simp
      rw [hz, zero_add]
      refine Finset.sum_congr rfl fun b hb ↦ ?_
      rw [testBit_clearTop hn]
      simp [Finset.ne_of_mem_erase hb]

/-- The `xor` of the words of `V` at the set bits of the words `Lw[i], …, Lw[i + n - 1]`, onto
`acc`. -/
private def gatherAux (Lw V : Array UInt64) : ℕ → ℕ → UInt64 → UInt64
  | 0, _, acc => acc
  | n + 1, i, acc => gatherAux Lw V n (i + 1) (gatherWord V (64 * i) 64 (Lw.getD i 0) acc)

/-- The `xor` of the words of `V` at the set bits of the words `Lw`. -/
private def gather (Lw V : Array UInt64) : UInt64 := gatherAux Lw V Lw.size 0 0

/-- Bit `j` of an array of words: bit `j % 64` of word `j / 64`, `false` past the end. -/
private def wbit (Lw : Array UInt64) (j : ℕ) : Bool :=
  (Lw.getD (j / 64) 0).toBitVec.getLsbD (j % 64)

/-- The bits of word `i` are the array's bits `64 i, …, 64 i + 63`. -/
private theorem wbit_add (Lw : Array UInt64) (i : ℕ) {b : ℕ} (hb : b < 64) :
    wbit Lw (64 * i + b) = (Lw.getD i 0).toNat.testBit b := by
  rw [wbit, show (64 * i + b) / 64 = i by omega, show (64 * i + b) % 64 = b by omega,
    getLsbD_toBitVec]

private theorem ofWord_gatherAux (Lw V : Array UInt64) :
    ∀ (n i : ℕ) (acc : UInt64), ofWord (gatherAux Lw V n i acc) = ofWord acc +
      ∑ k ∈ Finset.range (64 * n), if wbit Lw (64 * i + k) then ofWord (V.getD (64 * i + k) 0)
        else 0
  | 0, i, acc => by simp [gatherAux]
  | n + 1, i, acc => by
    rw [gatherAux, ofWord_gatherAux Lw V n (i + 1),
      ofWord_gatherWord V _ 64 _ _ (UInt64.toNat_lt _), add_assoc,
      show 64 * (n + 1) = 64 + 64 * n by ring, Finset.sum_range_add]
    congr 1
    congr 1
    · refine Finset.sum_congr rfl fun b hb ↦ ?_
      rw [wbit_add Lw i (Finset.mem_range.mp hb)]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [show 64 * (i + 1) + k = 64 * i + (64 + k) by ring]

/-- `gather` sums the elements of `V` at the set bits of `Lw`. -/
private theorem ofWord_gather (Lw V : Array UInt64) :
    ofWord (gather Lw V) = ∑ j ∈ Finset.range (64 * Lw.size),
      if wbit Lw j then ofWord (V.getD j 0) else 0 := by
  rw [gather, ofWord_gatherAux]
  simp [ofWord_zero]

/-- With words that hold a form's bits, a sum over the words' set bits is the sum over the form's
positions. -/
private theorem sum_wbit {M : Type*} [AddCommMonoid M] {Lw : Array UInt64} {L : Form m}
    (hL : Rep Lw L) (f : ℕ → M) :
    ∑ j ∈ Finset.range (64 * Lw.size), (if wbit Lw j then f j else 0) =
      ∑ j : Fin (2 ^ m), if L.getLsbD j then f j else 0 := by
  rw [hL.1, Fin.sum_univ_eq_sum_range (fun j ↦ if L.getLsbD j then f j else 0) (2 ^ m)]
  have hle := two_pow_le_nWords m
  rw [show 64 * nWords m = 2 ^ m + (64 * nWords m - 2 ^ m) by omega, Finset.sum_range_add]
  have hrest : (∑ x ∈ Finset.range (64 * nWords m - 2 ^ m),
      if wbit Lw (2 ^ m + x) then f (2 ^ m + x) else 0) = 0 := by
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    rw [Finset.mem_range] at hx
    rw [wbit, hL.2 _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]
    simp
  rw [hrest, add_zero]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [wbit, hL.2 j (by omega)]

/-! ## Entries of `E` as words -/

/-- The words of the three limbs of a table's entries. -/
private def limbsOf {n : ℕ} (W : Vector E n) : Vector (Array UInt64) 3 :=
  Vector.ofFn fun l ↦ Array.ofFn fun j : Fin n ↦ toWord (W[j].limb l)

/-- The sum of a table's entries at the set bits of `Lw`, from the words of their limbs. -/
private def gatherE (Lw : Array UInt64) (V : Vector (Array UInt64) 3) : E :=
  E.ofLimbs (ofWord (gather Lw V[0])) (ofWord (gather Lw V[1])) (ofWord (gather Lw V[2]))

/-- **The gathered sum is the row's product**: with words holding a form, `gatherE` of a table's
limbs is the sum of its entries at the form's positions. -/
private theorem gatherE_eq {Lw : Array UInt64} {L : Form m} (hL : Rep Lw L) (W : Vector E (2 ^ m)) :
    gatherE Lw (limbsOf W) = ∑ j : Fin (2 ^ m), if L.getLsbD j then W[j] else 0 := by
  refine E.ext fun l ↦ ?_
  have key : ofWord (gather Lw (limbsOf W)[l]) =
      ∑ j : Fin (2 ^ m), if L.getLsbD j then W[j].limb l else 0 := by
    rw [ofWord_gather, sum_wbit hL]
    exact Finset.sum_congr rfl fun j _ ↦ by simp [limbsOf, Array.getD_eq_getD_getElem?]
  have hsum : (∑ j : Fin (2 ^ m), if L.getLsbD j then W[j] else 0).limb l =
      ∑ j : Fin (2 ^ m), if L.getLsbD j then W[j].limb l else 0 := by
    rw [limb_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by split <;> simp [limb_zero]
  rw [hsum, ← key, gatherE, limbsOf]
  fin_cases l <;> simp

/-! ## Packing bits into words -/

/-- Bits `b < n` of `g` set onto `acc`. -/
private def packWordAux (g : ℕ → Bool) : ℕ → UInt64 → UInt64
  | 0, acc => acc
  | b + 1, acc => packWordAux g b (if g b then acc ||| ((1 : UInt64) <<< b.toUInt64) else acc)

/-- The word whose bit `b < 64` is `g b`. -/
private def packWord (g : ℕ → Bool) : UInt64 := packWordAux g 64 0

private theorem testBit_packWordAux (g : ℕ → Bool) :
    ∀ (n : ℕ), n ≤ 64 → ∀ (acc : UInt64) (i : ℕ),
      (packWordAux g n acc).toNat.testBit i = (acc.toNat.testBit i || (decide (i < n) && g i))
  | 0, _, acc, i => by simp [packWordAux]
  | n + 1, hn, acc, i => by
    rw [packWordAux, testBit_packWordAux g n (by omega)]
    have hlt : ∀ i, decide (i < n + 1) = (decide (i < n) || decide (i = n)) := fun i ↦ by
      by_cases h : i < n
      · simp [h, show i < n + 1 by omega]
      · by_cases h' : i = n
        · simp [h']
        · simp [h, h', show ¬ i < n + 1 by omega]
    rw [hlt]
    split
    · rename_i hg
      rw [UInt64.toNat_or, Nat.testBit_or, toNat_one_shiftLeft (by omega), Nat.testBit_two_pow]
      by_cases hi : i = n
      · subst hi; simp [hg]
      · have : (n = i) = False := propext ⟨fun h ↦ hi h.symm, False.elim⟩
        simp [this, hi]
    · rename_i hg
      by_cases hi : i = n
      · subst hi; simp [hg]
      · simp [hi]

/-- Bit `b < 64` of `packWord g` is `g b`. -/
private theorem testBit_packWord (g : ℕ → Bool) {b : ℕ} (hb : b < 64) :
    (packWord g).toNat.testBit b = g b := by
  rw [packWord, testBit_packWordAux g 64 le_rfl]
  simp [hb]

/-- The `nw` words whose bit `j` is `g j`. -/
private def packWords (nw : ℕ) (g : ℕ → Bool) : Array UInt64 :=
  Array.ofFn fun i : Fin nw ↦ packWord fun b ↦ g (64 * i.val + b)

/-- The packed words hold the bits of `BitVec.ofFnLE f`, for `g` agreeing with `f` on the
positions and `false` past them. -/
private theorem rep_packWords {g : ℕ → Bool} {f : Fin (2 ^ m) → Bool}
    (hg : ∀ j (h : j < 2 ^ m), g j = f ⟨j, h⟩) (hg' : ∀ j, 2 ^ m ≤ j → g j = false) :
    Rep (packWords (nWords m) g) (BitVec.ofFnLE f) := by
  refine ⟨by simp [packWords], fun j hj ↦ ?_⟩
  have hi : j / 64 < nWords m := by omega
  have hw : (packWords (nWords m) g).getD (j / 64) 0 = packWord fun b ↦ g (64 * (j / 64) + b) := by
    simp [packWords, Array.getD_eq_getD_getElem?, hi]
  rw [hw, getLsbD_toBitVec, testBit_packWord _ (Nat.mod_lt _ (by norm_num)),
    show 64 * (j / 64) + j % 64 = j by omega, BitVec.getLsbD_ofFnLE]
  split
  · rename_i h; exact hg j h
  · rename_i h; exact hg' j (by omega)

/-! ## The tables of a circuit's forms -/

/-- The words of the form of the one position `k`. -/
private def varWords (k : ℕ) : Array UInt64 :=
  Array.ofFn fun i : Fin (nWords m) ↦
    if i.val = k / 64 then (1 : UInt64) <<< (k % 64).toUInt64 else 0

private theorem rep_varWords (k : Pos m) : Rep (varWords (m := m) k) (Form.var k) := by
  refine ⟨by simp [varWords], fun j hj ↦ ?_⟩
  have hi : j / 64 < nWords m := by omega
  rw [getLsbD_var]
  have hw : (varWords (m := m) k).getD (j / 64) 0 =
      if j / 64 = k.val / 64 then (1 : UInt64) <<< (k.val % 64).toUInt64 else 0 := by
    simp [varWords, Array.getD_eq_getD_getElem?, hi]
  rw [hw, getLsbD_toBitVec]
  split
  · rename_i h
    rw [toNat_one_shiftLeft (Nat.mod_lt _ (by norm_num)), Nat.testBit_two_pow]
    simp only [decide_eq_decide]
    omega
  · rename_i h
    simp only [UInt64.toNat_zero, Nat.zero_testBit, false_eq_decide_iff]
    omega

/-- The words of the zero form. -/
private def zeroWords : Array UInt64 := Array.replicate (nWords m) 0

private theorem rep_zeroWords : Rep (zeroWords (m := m)) (0 : Form m) := by
  refine ⟨by simp [zeroWords], fun j hj ↦ ?_⟩
  have hi : j / 64 < nWords m := by omega
  simp [zeroWords, Array.getD_eq_getD_getElem?, hi]

/-- The row of a position with no gate: the constant's `(1, 1)`, an input's `(z_k, 1)`, the zero
row elsewhere. -/
private def baseForm (c : ProductCircuit m) (k : Pos m) : Gate m :=
  if k = c.cpos then ⟨Form.var c.cpos, Form.var c.cpos⟩
  else if c.inputs.getLsbD k then ⟨Form.var k, Form.var c.cpos⟩
  else ⟨0, 0⟩

/-- The words of `baseForm`'s two forms. -/
private def baseRow (c : ProductCircuit m) (k : Pos m) : Array UInt64 × Array UInt64 :=
  if k = c.cpos then (varWords (m := m) c.cpos, varWords (m := m) c.cpos)
  else if c.inputs.getLsbD k then (varWords (m := m) k, varWords (m := m) c.cpos)
  else (zeroWords (m := m), zeroWords (m := m))

private theorem rep_baseRow (c : ProductCircuit m) (k : Pos m) :
    Rep (baseRow c k).1 (baseForm c k).a ∧ Rep (baseRow c k).2 (baseForm c k).b := by
  unfold baseRow baseForm
  split
  · exact ⟨rep_varWords _, rep_varWords _⟩
  · split
    · exact ⟨rep_varWords _, rep_varWords _⟩
    · exact ⟨rep_zeroWords, rep_zeroWords⟩

/-- The row of position `k` after a list of gates: its first gate's, else the base row. -/
private def rowOfList (c : ProductCircuit m) (L : List (Pos m × Gate m)) (k : Pos m) : Gate m :=
  match L.lookup k with
  | some g => g
  | none => baseForm c k

/-- The rows' words from a list of compiled gates: the first gate at a position wins. -/
private def rowsFrom (c : ProductCircuit m) (L : List (Pos m × Array UInt64 × Array UInt64)) :
    Vector (Array UInt64 × Array UInt64) (2 ^ m) :=
  L.foldr (fun g t ↦ t.set g.1.val (g.2.1, g.2.2) g.1.isLt) (Vector.ofFn (baseRow c))

private theorem rep_rowsFrom (c : ProductCircuit m) :
    ∀ (L : List (Pos m × Gate m)) (k : Pos m),
      Rep (rowsFrom c (L.map compileGate))[k].1 (rowOfList c L k).a ∧
        Rep (rowsFrom c (L.map compileGate))[k].2 (rowOfList c L k).b
  | [], k => by
    simp only [rowsFrom, List.map_nil, List.foldr_nil, Fin.getElem_fin, Vector.getElem_ofFn,
      rowOfList, List.lookup_nil]
    exact rep_baseRow c k
  | (k0, g0) :: L, k => by
    have ih := rep_rowsFrom c L k
    simp only [rowsFrom, List.map_cons, List.foldr_cons] at ih ⊢
    rw [Fin.getElem_fin, Vector.getElem_set]
    simp only [rowOfList, List.lookup_cons]
    by_cases hk : k = k0
    · subst hk
      simp only [compileGate, beq_self_eq_true, ite_true]
      exact ⟨rep_wordsOf _, rep_wordsOf _⟩
    · have h1 : (k0.val = k.val) = False := propext ⟨fun h ↦ hk (Fin.ext h.symm), False.elim⟩
      have h2 : (k == k0) = false := by simpa using hk
      simp only [compileGate, h1, ite_false, h2]
      exact ih

/-- The words of every row's two forms: the circuit compiled once, each gate's words set at its
position over the base rows. -/
@[no_expose] def rowTable (c : ProductCircuit m) : Vector (Array UInt64 × Array UInt64) (2 ^ m) :=
  rowsFrom c (compile c).gates.toList

private theorem rep_rowTable (c : ProductCircuit m) (k : Pos m) :
    Rep (rowTable c)[k].1 (c.rowOf k).a ∧ Rep (rowTable c)[k].2 (c.rowOf k).b := by
  rw [show c.rowOf k = rowOfList c c.gates.toList k from rfl, rowTable, compile]
  simp only [Array.toList_map]
  exact rep_rowsFrom c c.gates.toList k

/-! ## The walks -/

/-- Whether an entry is `0` or `1`, limb by limb. -/
private def isBoolE (x : E) : Bool :=
  isOneE x || decide (x.limb 0 = 0 ∧ x.limb 1 = 0 ∧ x.limb 2 = 0)

private theorem isBool_of_isBoolE {x : E} (h : isBoolE x = true) : BlockR1CS.IsBool x := by
  rw [isBoolE, Bool.or_eq_true, isOneE_iff, decide_eq_true_eq] at h
  rcases h with h | ⟨h0, h1, h2⟩
  · exact Or.inr h
  · refine Or.inl (E.ext fun i ↦ ?_)
    rw [limb_zero]
    fin_cases i <;> assumption

/-- `true` as `1`, `false` as `0`. -/
private def boolE (b : Bool) : E := if b then oneE else zeroE

private theorem boolE_eq (b : Bool) : boolE b = ofBool E b := by
  cases b <;> rfl

/-- The forward walk: on a block of `0`s and `1`s, each row the parity of its form's word-wise
`and` with the packed block; on any other block, each row its form's entries gathered limb by
limb. -/
@[no_expose] def walkRows (rt : Vector (Array UInt64 × Array UInt64) (2 ^ m))
    (W : CMlPolynomialEval E m) :
    CMlPolynomialEval E m × CMlPolynomialEval E m :=
  if W.all isBoolE then
    let zw := packWords (nWords m) fun j ↦ if h : j < 2 ^ m then isOneE W[j] else false
    (Vector.ofFn fun k ↦ boolE (evalW rt[k].1 zw), Vector.ofFn fun k ↦ boolE (evalW rt[k].2 zw))
  else
    let V := limbsOf W
    (Vector.ofFn fun k ↦ gatherE rt[k].1 V, Vector.ofFn fun k ↦ gatherE rt[k].2 V)

/-- A row on a block of `0`s and `1`s: the parity of the form on the packed block. -/
private theorem boolE_evalW {W : CMlPolynomialEval E m} (hW : W.all isBoolE = true)
    {Lw : Array UInt64} {L : Form m} (hL : Rep Lw L) :
    boolE (evalW Lw (packWords (nWords m) fun j ↦ if h : j < 2 ^ m then isOneE W[j] else false)) =
      ∑ j : Fin (2 ^ m), if L.getLsbD j then W[j] else 0 := by
  have hb : ∀ k : Pos m, BlockR1CS.IsBool W[k] := fun k ↦
    isBool_of_isBoolE (Vector.all_eq_true.mp hW k k.isLt)
  have hz : Rep (packWords (nWords m) fun j ↦ if h : j < 2 ^ m then isOneE W[j] else false)
      (BitVec.ofFnLE fun j : Pos m ↦ isOneE W[j]) :=
    rep_packWords (fun j h ↦ by simp [h]) (fun j h ↦ by simp [show ¬ j < 2 ^ m by omega])
  have hbits : (fun j : Pos m ↦ (BitVec.ofFnLE fun j : Pos m ↦ isOneE W[j]).getLsbD j) =
      toBools W := by
    funext j
    simp only [BitVec.getLsbD_ofFnLE, j.isLt, dite_true, toBools]
    exact Bool.eq_iff_iff.mpr (by rw [isOneE_iff, decide_eq_true_eq])
  have key := sum_liftBlock (R := E) L (toBools W)
  rw [← eq_liftBlock_toBools hb] at key
  rw [key, boolE_eq, evalW_eq_evalB hL hz, evalB_eq_eval, hbits]

private theorem walkRows_fst (c : ProductCircuit m) (W : CMlPolynomialEval E m) (k : Pos m) :
    (walkRows (rowTable c) W).1[k] = ∑ j : Pos m, if (c.rowOf k).a.getLsbD j then W[j] else 0 := by
  unfold walkRows
  split <;> simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exacts [boolE_evalW ‹_› (rep_rowTable c k).1, gatherE_eq (rep_rowTable c k).1 W]

private theorem walkRows_snd (c : ProductCircuit m) (W : CMlPolynomialEval E m) (k : Pos m) :
    (walkRows (rowTable c) W).2[k] = ∑ j : Pos m, if (c.rowOf k).b.getLsbD j then W[j] else 0 := by
  unfold walkRows
  split <;> simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exacts [boolE_evalW ‹_› (rep_rowTable c k).2, gatherE_eq (rep_rowTable c k).2 W]

/-! ## Entries of `E` as six half-words -/

/-- The word of two halves. -/
private def joinWord (lo hi : UInt32) : UInt64 := lo.toUInt64 ||| (hi.toUInt64 <<< 32)

private theorem getLsbD_joinWord (lo hi : UInt32) (i : ℕ) :
    (joinWord lo hi).toBitVec.getLsbD i =
      if i < 32 then lo.toBitVec.getLsbD i
      else decide (i < 64) && hi.toBitVec.getLsbD (i - 32) := by
  simp only [joinWord, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64,
    BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft]
  by_cases h : i < 32
  · simp [h, show i < 64 by omega]
  · by_cases h' : i < 64
    · simp [h, h', BitVec.getLsbD_of_ge lo.toBitVec i (by omega), show i - 32 < 32 by omega,
        show i - 32 < 64 by omega]
    · simp [h, h', BitVec.getLsbD_of_ge lo.toBitVec i (by omega),
        BitVec.getLsbD_of_ge hi.toBitVec (i - 32) (by omega)]

/-- The halves of a word join to the word. -/
private theorem joinWord_halves (w : UInt64) : joinWord w.toUInt32 (w >>> 32).toUInt32 = w := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_joinWord]
  simp only [UInt64.toBitVec_toUInt32, UInt64.toBitVec_shiftRight,
    BitVec.getLsbD_setWidth, BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight]
  by_cases h : i < 32
  · simp [h]
  · simp [h, hi, show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega]

/-- Joining is additive: the join of two `xor`s is the `xor` of the joins. -/
private theorem joinWord_xor (a b c d : UInt32) :
    joinWord (a ^^^ b) (c ^^^ d) = joinWord a c ^^^ joinWord b d := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [UInt64.toBitVec_xor, BitVec.getLsbD_xor, getLsbD_joinWord, getLsbD_joinWord,
    getLsbD_joinWord]
  by_cases h : i < 32
  · simp [h, UInt32.toBitVec_xor]
  · simp [h, hi, UInt32.toBitVec_xor]

/-- The entry `j` of an array of half-words: limb `l` at the halves `6 j + 2 l`, `6 j + 2 l + 1`,
low first. -/
private def entryAt (acc : Array UInt32) (j : ℕ) : E :=
  E.ofLimbs (ofWord (joinWord (acc.getD (6 * j) 0) (acc.getD (6 * j + 1) 0)))
    (ofWord (joinWord (acc.getD (6 * j + 2) 0) (acc.getD (6 * j + 3) 0)))
    (ofWord (joinWord (acc.getD (6 * j + 4) 0) (acc.getD (6 * j + 5) 0)))

/-- The six halves of an entry, in `entryAt`'s order. -/
private def halvesOf (x : E) (h : ℕ) : UInt32 :=
  let w := toWord (x.limb ⟨(h / 2) % 3, Nat.mod_lt _ (by norm_num)⟩)
  if h % 2 = 0 then w.toUInt32 else (w >>> 32).toUInt32

/-- The half-words of a table's entries, six an entry. -/
private def halvesTable {n : ℕ} (W : Vector E n) : Array UInt32 :=
  Array.ofFn fun i : Fin (6 * n) ↦ halvesOf (W.toArray.getD (i.val / 6) 0) (i.val % 6)

/-- `v` `xor`ed onto the six halves of entry `p`. -/
private def addAt (acc : Array UInt32) (p : ℕ) (v0 v1 v2 v3 v4 v5 : UInt32) : Array UInt32 :=
  (((((acc.modify (6 * p) (· ^^^ v0)).modify (6 * p + 1) (· ^^^ v1)).modify (6 * p + 2)
    (· ^^^ v2)).modify (6 * p + 3) (· ^^^ v3)).modify (6 * p + 4) (· ^^^ v4)).modify (6 * p + 5)
      (· ^^^ v5)

private theorem size_addAt (acc : Array UInt32) (p : ℕ) (v0 v1 v2 v3 v4 v5 : UInt32) :
    (addAt acc p v0 v1 v2 v3 v4 v5).size = acc.size := by
  simp [addAt]

/-- The entry of six halves. -/
private def ofHalves (v0 v1 v2 v3 v4 v5 : UInt32) : E :=
  E.ofLimbs (ofWord (joinWord v0 v1)) (ofWord (joinWord v2 v3)) (ofWord (joinWord v4 v5))

private theorem ofHalves_halvesOf (x : E) :
    ofHalves (halvesOf x 0) (halvesOf x 1) (halvesOf x 2) (halvesOf x 3) (halvesOf x 4)
      (halvesOf x 5) = x := by
  simp only [ofHalves, halvesOf, Nat.reduceMod, Nat.reduceDiv, ↓reduceIte, Nat.one_ne_zero,
    joinWord_halves, ofWord_toWord]
  exact ofLimbs_limb x

/-- An entry after `addAt`: its value plus the six halves' entry at `p`, when they fit. -/
private theorem entryAt_addAt (acc : Array UInt32) (p j : ℕ) (v0 v1 v2 v3 v4 v5 : UInt32)
    (hj : 6 * j + 5 < acc.size) :
    entryAt (addAt acc p v0 v1 v2 v3 v4 v5) j =
      entryAt acc j + if p = j then ofHalves v0 v1 v2 v3 v4 v5 else 0 := by
  have hmod : ∀ (a : Array UInt32) (q i : ℕ) (f : UInt32 → UInt32),
      (a.modify q f).getD i 0 = if q = i ∧ i < a.size then f (a.getD i 0) else a.getD i 0 := by
    intro a q i f
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
    by_cases hq : q = i
    · subst hq; by_cases hi : q < a.size <;> simp [hi]
    · simp [hq]
  by_cases hp : p = j
  · subst hp
    simp (disch := omega) only [entryAt, addAt, hmod, Array.size_modify, true_and, ↓reduceIte,
      ite_eq_left, ite_eq_right, joinWord_xor, ofWord_xor, ofHalves, add_limbs]
  · simp (disch := omega) only [entryAt, addAt, hmod, Array.size_modify, ite_eq_left, ite_eq_right,
      add_zero]

/-! ## The backward walk, scattered row by row -/

/-- The six halves `v` `xor`ed onto the entries `base + b` at the set bits `b` of `w`, highest
first; `fuel` bounds the steps. -/
private def scatterWord (base : ℕ) (v0 v1 v2 v3 v4 v5 : UInt32) :
    ℕ → UInt64 → Array UInt32 → Array UInt32
  | 0, _, acc => acc
  | fuel + 1, w, acc =>
    if w = 0 then acc else
      let b := topBit w
      scatterWord base v0 v1 v2 v3 v4 v5 fuel (clearAt w b) (addAt acc (base + b) v0 v1 v2 v3 v4 v5)

private theorem size_scatterWord (base : ℕ) (v0 v1 v2 v3 v4 v5 : UInt32) :
    ∀ (fuel : ℕ) (w : UInt64) (acc : Array UInt32),
      (scatterWord base v0 v1 v2 v3 v4 v5 fuel w acc).size = acc.size
  | 0, _, _ => rfl
  | fuel + 1, w, acc => by
    rw [scatterWord]
    split
    · rfl
    · change (scatterWord base v0 v1 v2 v3 v4 v5 fuel _ _).size = _
      rw [size_scatterWord, size_addAt]

/-- What `scatterWord` adds at an entry: the halves' entry when the entry is `base` plus a set
bit of the word. -/
private theorem entryAt_scatterWord (base : ℕ) (v0 v1 v2 v3 v4 v5 : UInt32) :
    ∀ (fuel : ℕ) (w : UInt64) (acc : Array UInt32), w.toNat < 2 ^ fuel → ∀ j,
      6 * j + 5 < acc.size →
      entryAt (scatterWord base v0 v1 v2 v3 v4 v5 fuel w acc) j = entryAt acc j +
        if base ≤ j ∧ j < base + 64 ∧ w.toNat.testBit (j - base) then
          ofHalves v0 v1 v2 v3 v4 v5 else 0
  | 0, w, acc, hw, j, _ => by
    have : w.toNat = 0 := by simpa using hw
    simp [scatterWord, this]
  | fuel + 1, w, acc, hw, j, hj => by
    rw [scatterWord]
    split
    · rename_i h
      subst h
      simp
    · rename_i h
      change entryAt (scatterWord base v0 v1 v2 v3 v4 v5 fuel (clearTop w)
        (addAt acc (base + topBit w) v0 v1 v2 v3 v4 v5)) j = _
      obtain ⟨hn, hlt, hc⟩ := top_facts h hw
      rw [entryAt_scatterWord base v0 v1 v2 v3 v4 v5 fuel _ _ hc j
        (by rw [size_addAt]; exact hj), entryAt_addAt _ _ _ _ _ _ _ _ _ hj, topBit_eq,
        testBit_clearTop hn, add_assoc]
      congr 1
      by_cases hb : base + w.toNat.log2 = j
      · subst hb
        have e1 : base + w.toNat.log2 - base = w.toNat.log2 := by omega
        rw [ite_eq_left rfl, ite_eq_right (by simp [e1]),
          ite_eq_left ⟨by omega, by omega, by rw [e1]; exact Nat.testBit_log2 hn⟩, add_zero]
      · rw [ite_eq_right hb, zero_add]
        refine if_congr ?_ rfl rfl
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1⟩,
          fun h ↦ ⟨h.1, h.2.1, h.2.2, fun h' ↦ hb (by have := h.1; omega)⟩⟩

/-- The six halves `v` `xor`ed onto the entries at the set bits of the words `Lw[i], …`. -/
private def scatterAux (Lw : Array UInt64) (v0 v1 v2 v3 v4 v5 : UInt32) :
    ℕ → ℕ → Array UInt32 → Array UInt32
  | 0, _, acc => acc
  | n + 1, i, acc => scatterAux Lw v0 v1 v2 v3 v4 v5 n (i + 1)
      (scatterWord (64 * i) v0 v1 v2 v3 v4 v5 64 (Lw.getD i 0) acc)

private theorem size_scatterAux (Lw : Array UInt64) (v0 v1 v2 v3 v4 v5 : UInt32) :
    ∀ (n i : ℕ) (acc : Array UInt32), (scatterAux Lw v0 v1 v2 v3 v4 v5 n i acc).size = acc.size
  | 0, _, _ => rfl
  | n + 1, i, acc => by rw [scatterAux, size_scatterAux, size_scatterWord]

private theorem entryAt_scatterAux (Lw : Array UInt64) (v0 v1 v2 v3 v4 v5 : UInt32) :
    ∀ (n i : ℕ) (acc : Array UInt32) (j : ℕ), 6 * j + 5 < acc.size →
      entryAt (scatterAux Lw v0 v1 v2 v3 v4 v5 n i acc) j = entryAt acc j +
        if 64 * i ≤ j ∧ j < 64 * (i + n) ∧ wbit Lw j then ofHalves v0 v1 v2 v3 v4 v5 else 0
  | 0, i, acc, j, _ => by
    simp only [scatterAux, Nat.add_zero]
    rw [ite_eq_right (fun h ↦ by omega), add_zero]
  | n + 1, i, acc, j, hj => by
    rw [scatterAux, entryAt_scatterAux Lw v0 v1 v2 v3 v4 v5 n (i + 1) _ j
      (by rw [size_scatterWord]; exact hj),
      entryAt_scatterWord _ _ _ _ _ _ _ 64 _ _ (UInt64.toNat_lt _) j hj, add_assoc]
    congr 1
    by_cases h1 : 64 * i ≤ j ∧ j < 64 * i + 64
    · have hw : wbit Lw j = (Lw.getD i 0).toNat.testBit (j - 64 * i) := by
        rw [show j = 64 * i + (j - 64 * i) by omega, wbit_add Lw i (by omega)]
        congr 1; omega
      rw [ite_eq_right (show ¬ (64 * (i + 1) ≤ j ∧ j < 64 * (i + 1 + n) ∧ wbit Lw j = true) from
        fun h ↦ by omega), add_zero]
      simp only [hw, h1, true_and, show j < 64 * (i + (n + 1)) by omega]
    · rw [ite_eq_right (fun h ↦ h1 ⟨h.1, h.2.1⟩), zero_add]
      exact if_congr ⟨fun h ↦ ⟨by omega, by omega, h.2.2⟩,
        fun h ↦ ⟨Nat.le_of_not_lt fun hlt ↦ h1 ⟨h.1, by omega⟩, by omega, h.2.2⟩⟩ rfl rfl

/-- The six halves `v` `xor`ed onto the entries at the set bits of `Lw`. -/
private def scatterRow (Lw : Array UInt64) (v0 v1 v2 v3 v4 v5 : UInt32) (acc : Array UInt32) :
    Array UInt32 :=
  scatterAux Lw v0 v1 v2 v3 v4 v5 Lw.size 0 acc

private theorem size_scatterRow (Lw : Array UInt64) (v0 v1 v2 v3 v4 v5 : UInt32)
    (acc : Array UInt32) :
    (scatterRow Lw v0 v1 v2 v3 v4 v5 acc).size = acc.size :=
  size_scatterAux _ _ _ _ _ _ _ _ _ _

/-- What a row adds at an entry: the halves' entry at its form's set bits. -/
private theorem entryAt_scatterRow (Lw : Array UInt64) (v0 v1 v2 v3 v4 v5 : UInt32)
    (acc : Array UInt32) {j : ℕ} (hj : 6 * j + 5 < acc.size) :
    entryAt (scatterRow Lw v0 v1 v2 v3 v4 v5 acc) j = entryAt acc j +
      if wbit Lw j then ofHalves v0 v1 v2 v3 v4 v5 else 0 := by
  rw [scatterRow, entryAt_scatterAux _ _ _ _ _ _ _ _ _ _ _ hj]
  congr 1
  by_cases h : j < 64 * Lw.size
  · simp [h]
  · have : wbit Lw j = false := by
      rw [wbit, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      simp
    simp [this]

/-- The rows `k, k + 1, …` scattered, each its entry's six halves at its form's set bits. -/
private def scatterFrom (rows : Array (Array UInt64)) (H : Array UInt32) :
    ℕ → ℕ → Array UInt32 → Array UInt32
  | 0, _, acc => acc
  | c + 1, k, acc => scatterFrom rows H c (k + 1)
      (scatterRow (rows.getD k #[]) (H.getD (6 * k) 0) (H.getD (6 * k + 1) 0)
        (H.getD (6 * k + 2) 0) (H.getD (6 * k + 3) 0) (H.getD (6 * k + 4) 0)
        (H.getD (6 * k + 5) 0) acc)

private theorem size_scatterFrom (rows : Array (Array UInt64)) (H : Array UInt32) :
    ∀ (c k : ℕ) (acc : Array UInt32), (scatterFrom rows H c k acc).size = acc.size
  | 0, _, _ => rfl
  | c + 1, k, acc => by rw [scatterFrom, size_scatterFrom, size_scatterRow]

private theorem entryAt_scatterFrom (rows : Array (Array UInt64)) (H : Array UInt32) :
    ∀ (c k : ℕ) (acc : Array UInt32) (j : ℕ), 6 * j + 5 < acc.size →
      entryAt (scatterFrom rows H c k acc) j = entryAt acc j +
        ∑ i ∈ Finset.range c,
          if wbit (rows.getD (k + i) #[]) j then entryAt H (k + i) else 0
  | 0, k, acc, j, _ => by simp [scatterFrom]
  | c + 1, k, acc, j, hj => by
    rw [scatterFrom, entryAt_scatterFrom rows H c (k + 1) _ j (by rw [size_scatterRow]; exact hj),
      entryAt_scatterRow _ _ _ _ _ _ _ _ hj, Finset.sum_range_succ', add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show k + 1 + i = k + (i + 1) by ring]

/-- The six halves of the entries of a table, read back. -/
private theorem entryAt_halvesTable {n : ℕ} (W : Vector E n) {k : ℕ} (hk : k < n) :
    entryAt (halvesTable W) k = W[k] := by
  have hg : ∀ h, h < 6 → (halvesTable W).getD (6 * k + h) 0 = halvesOf W[k] h := fun h hh ↦ by
    simp only [halvesTable, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      show 6 * k + h < 6 * n by omega, dite_true, Option.getD_some,
      show (6 * k + h) / 6 = k by omega, show (6 * k + h) % 6 = h by omega]
    simp [hk]
  have h0 : (halvesTable W).getD (6 * k) 0 = halvesOf W[k] 0 := by simpa using hg 0 (by norm_num)
  rw [entryAt, h0, hg 1 (by norm_num), hg 2 (by norm_num), hg 3 (by norm_num), hg 4 (by norm_num),
    hg 5 (by norm_num)]
  exact ofHalves_halvesOf W[k]

/-- The backward walk: each row's entry, as six half-words, scattered onto the columns its form
holds. -/
@[no_expose] def walkCols (rt : Vector (Array UInt64 × Array UInt64) (2 ^ m))
    (e : CMlPolynomialEval E m) :
    CMlPolynomialEval E m × CMlPolynomialEval E m :=
  let H := halvesTable e
  let z : Array UInt32 := Array.replicate (6 * 2 ^ m) 0
  let a := scatterFrom (rt.map Prod.fst).toArray H (2 ^ m) 0 z
  let b := scatterFrom (rt.map Prod.snd).toArray H (2 ^ m) 0 z
  (Vector.ofFn fun j ↦ entryAt a j, Vector.ofFn fun j ↦ entryAt b j)

/-- The entry of zeros is zero. -/
private theorem entryAt_replicate (N j : ℕ) : entryAt (Array.replicate N (0 : UInt32)) j = 0 := by
  apply E.ext
  intro l
  have hz : ∀ i, (Array.replicate N (0 : UInt32)).getD i 0 = 0 := fun i ↦ by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  simp only [entryAt, hz, limb_zero]
  fin_cases l <;> rfl

/-- The scattered entries are the sums over the rows that hold the column. -/
private theorem scatter_entry (rows : Vector (Array UInt64) (2 ^ m)) (L : Pos m → Form m)
    (hL : ∀ k, Rep rows[k] (L k)) (e : CMlPolynomialEval E m) (j : Pos m) :
    entryAt (scatterFrom rows.toArray (halvesTable e) (2 ^ m) 0
        (Array.replicate (6 * 2 ^ m) 0)) j =
      ∑ k : Pos m, if (L k).getLsbD j then e[k] else 0 := by
  rw [entryAt_scatterFrom _ _ _ _ _ _ (by simp; omega), entryAt_replicate, zero_add,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hr : rows.toArray.getD (0 + (k : ℕ)) #[] = rows[k] := by
    simp [Array.getD_eq_getD_getElem?]
  rw [hr, wbit, (hL k).2 j (lt_of_lt_of_le j.isLt (two_pow_le_nWords m)),
    show (0 + (k : ℕ)) = k by omega, entryAt_halvesTable e k.isLt]
  rfl

private theorem walkCols_fst (c : ProductCircuit m) (e : CMlPolynomialEval E m) (j : Pos m) :
    (walkCols (rowTable c) e).1[j] =
      ∑ k : Pos m, if (c.rowOf k).a.getLsbD j then e[k] else 0 := by
  simp only [walkCols, Fin.getElem_fin, Vector.getElem_ofFn]
  exact scatter_entry ((rowTable c).map Prod.fst) (fun k ↦ (c.rowOf k).a)
    (fun k ↦ by simpa using (rep_rowTable c k).1) e j

private theorem walkCols_snd (c : ProductCircuit m) (e : CMlPolynomialEval E m) (j : Pos m) :
    (walkCols (rowTable c) e).2[j] =
      ∑ k : Pos m, if (c.rowOf k).b.getLsbD j then e[k] else 0 := by
  simp only [walkCols, Fin.getElem_fin, Vector.getElem_ofFn]
  exact scatter_entry ((rowTable c).map Prod.snd) (fun k ↦ (c.rowOf k).b)
    (fun k ↦ by simpa using (rep_rowTable c k).2) e j

/-- **The circuit's R1CS over `E`, with the walks on words**: the matrices of `toBlockR1CS E`, the
rows' words built once, on the first walk. -/
def toBlockR1CSE (c : ProductCircuit m) : BlockR1CS E m :=
  let rt : Thunk (Vector (Array UInt64 × Array UInt64) (2 ^ m)) := Thunk.mk fun _ ↦ rowTable c
  { A := fun k j ↦ (c.rowOf k).a.getLsbD j
    B := fun k j ↦ (c.rowOf k).b.getLsbD j
    rows := fun W ↦ walkRows rt.get W
    cols := fun e ↦ walkCols rt.get e
    rows_fst := fun W k ↦ by exact walkRows_fst c W k
    rows_snd := fun W k ↦ by exact walkRows_snd c W k
    cols_fst := fun e j ↦ by exact walkCols_fst c e j
    cols_snd := fun e j ↦ by exact walkCols_snd c e j }

/-- **It is the circuit's R1CS**: the same matrices, so the same block R1CS. -/
theorem toBlockR1CSE_eq (c : ProductCircuit m) : c.toBlockR1CSE = c.toBlockR1CS E :=
  BlockR1CS.ext_of rfl rfl

end ProductCircuit

end
end LeanerVM.Protocol
