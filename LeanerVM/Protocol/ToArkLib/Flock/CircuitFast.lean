/-
  LeanerVM.Protocol.ToArkLib.Flock.CircuitFast

  A product-gate circuit compiled for its honest prover: each gate's forms and the block as
  arrays of 64-bit words, a form's value the parity of the word-wise `and`, a gate's bit one word
  update, and the trace on words proved to hold the bitset trace. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Flock.Circuit

/-!
# The trace of a compiled circuit

`ProductCircuit.trace` evaluates a gate's two forms on the block as bitsets of `2 ^ m` bits: an
`and` and `m` halvings each, and an `or` to set the gate's bit, every one a new number of `2 ^ m`
bits. The honest prover compiles the circuit once (`compile`: each form as its `2 ^ (m - 6)`
words, `wordsOf`, read off the number by halving it, `wordsAux_getD`) and runs it on the block's
words (`Compiled.traceW`): a form's value is the parity of the `xor` of the word-wise `and`s
(`evalW`, `evalW_eq_evalB`), a gate's bit one word updated (`setBitW`, `rep_setBitW`).
`Rep zw z` says that the words `zw` hold the bits of `z`; `rep_traceW`: the words of the compiled
trace hold `trace`'s. Nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

@[expose] public section

namespace ProductCircuit

/-! ## Words -/

/-- Bit `b` of a word, by a shift and a mask. -/
def bitOf (w : UInt64) (b : ℕ) : Bool := (w >>> b.toUInt64) &&& 1 != 0

/-- `bitOf` reads the bit. -/
theorem bitOf_eq (w : UInt64) {b : ℕ} (hb : b < 64) : bitOf w b = w.toBitVec.getLsbD b := by
  have hsh : (w >>> b.toUInt64 &&& 1).toBitVec = (w.toBitVec >>> b) &&& 1#64 := by
    rw [UInt64.toBitVec_and, UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq']
    congr 2
    simp [Nat.toUInt64, Nat.mod_eq_of_lt hb]
  have hz : ∀ x : UInt64, (x != 0) = !(decide (x.toBitVec = 0)) := fun x ↦ by
    by_cases h : x = 0
    · subst h; rfl
    · have h' : x.toBitVec ≠ 0 := fun h0 ↦ h (UInt64.toBitVec_inj.mp (by rw [h0]; rfl))
      rw [show (x != 0) = true from bne_iff_ne.mpr h, decide_eq_false h']
      rfl
  rw [bitOf, hz, hsh]
  cases hbit : w.toBitVec.getLsbD b
  · simp only [Bool.not_eq_false', decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_one]
    by_cases h0 : i = 0
    · subst h0; simp [hbit]
    · simp [h0]
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    intro h
    have := congrArg (fun x ↦ x.getLsbD 0) h
    simp [hbit] at this

/-- The parity of the bits below `n` of a word, xored onto `a`. -/
def parityAux (w : UInt64) : ℕ → Bool → Bool
  | 0, a => a
  | n + 1, a => parityAux w n (a ^^ bitOf w n)

theorem toZ_parityAux (w : UInt64) : (n : ℕ) → n ≤ 64 → (a : Bool) →
    toZ (parityAux w n a) = toZ a + ∑ b ∈ Finset.range n, toZ (w.toBitVec.getLsbD b)
  | 0, _, a => by simp [parityAux]
  | n + 1, hn, a => by
    rw [parityAux, toZ_parityAux w n (by omega), toZ_xor, bitOf_eq w (by omega),
      Finset.sum_range_succ]
    ring

/-- The parity of a word. -/
def parity (w : UInt64) : Bool := parityAux w 64 false

/-- The `xor` of the word-wise `and` of the first `n` words of two arrays. -/
def xorAnd (Lw zw : Array UInt64) : ℕ → UInt64
  | 0 => 0
  | n + 1 => xorAnd Lw zw n ^^^ (Lw.getD n 0 &&& zw.getD n 0)

theorem toZ_getLsbD_xorAnd (Lw zw : Array UInt64) (b : ℕ) : (n : ℕ) →
    toZ ((xorAnd Lw zw n).toBitVec.getLsbD b) =
      ∑ i ∈ Finset.range n,
        toZ ((Lw.getD i 0).toBitVec.getLsbD b && (zw.getD i 0).toBitVec.getLsbD b)
  | 0 => by simp [xorAnd, toZ]
  | n + 1 => by
    rw [xorAnd, UInt64.toBitVec_xor, BitVec.getLsbD_xor, toZ_xor, toZ_getLsbD_xorAnd Lw zw b n,
      UInt64.toBitVec_and, BitVec.getLsbD_and, Finset.sum_range_succ]

/-- The value of a form, given by its words, on a block given by its words: the parity of the
`xor` of the word-wise `and`. -/
def evalW (Lw zw : Array UInt64) : Bool := parity (xorAnd Lw zw Lw.size)

/-- Bit `b` of word `i` is position `64 i + b`. -/
private theorem sum_words (f : ℕ → ZMod 2) : (n : ℕ) →
    ∑ b ∈ Finset.range 64, ∑ i ∈ Finset.range n, f (64 * i + b) =
      ∑ j ∈ Finset.range (64 * n), f j
  | 0 => by simp
  | n + 1 => by
    rw [show 64 * (n + 1) = 64 * n + 64 by ring, Finset.sum_range_add, ← sum_words f n,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Finset.sum_range_succ]

/-! ## The words of a number -/

/-- The words of `x` below `64 · 2 ^ k`, appended to `acc`, by halving the number. -/
def wordsAux : (k : ℕ) → ℕ → Array UInt64 → Array UInt64
  | 0, x, acc => acc.push x.toUInt64
  | k + 1, x, acc =>
    wordsAux k (x >>> (64 * 2 ^ k)) (wordsAux k (x % 2 ^ (64 * 2 ^ k)) acc)

theorem size_wordsAux : (k x : ℕ) → (acc : Array UInt64) →
    (wordsAux k x acc).size = acc.size + 2 ^ k
  | 0, x, acc => by simp [wordsAux]
  | k + 1, x, acc => by
    rw [wordsAux, size_wordsAux, size_wordsAux, pow_succ]
    ring

/-- `wordsAux` keeps `acc` and appends the words of `x`, word `i` holding the bits
`64 i, …, 64 i + 63`. -/
theorem wordsAux_getD : (k x : ℕ) → (acc : Array UInt64) → (i : ℕ) →
    (i < acc.size → (wordsAux k x acc).getD i 0 = acc.getD i 0) ∧
      (acc.size ≤ i → i < acc.size + 2 ^ k → ∀ c < 64,
        ((wordsAux k x acc).getD i 0).toBitVec.getLsbD c = x.testBit (64 * (i - acc.size) + c))
  | 0, x, acc, i => by
    refine ⟨fun hi ↦ ?_, fun h1 h2 c hc ↦ ?_⟩
    · simp [wordsAux, Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt hi]
    · have hi : i = acc.size := by simp at h2; omega
      subst hi
      simp only [wordsAux, Array.getD_eq_getD_getElem?, Array.getElem?_push_size,
        Option.getD_some, Nat.toUInt64, UInt64.toBitVec_ofNat', BitVec.getLsbD_ofNat,
        Nat.sub_self, Nat.mul_zero, Nat.zero_add, hc, decide_true, Bool.true_and]
  | k + 1, x, acc, i => by
    have hin := wordsAux_getD k (x % 2 ^ (64 * 2 ^ k)) acc
    have hout := wordsAux_getD k (x >>> (64 * 2 ^ k)) (wordsAux k (x % 2 ^ (64 * 2 ^ k)) acc)
    rw [size_wordsAux] at hout
    rw [wordsAux]
    refine ⟨fun hi ↦ ?_, fun h1 h2 c hc ↦ ?_⟩
    · rw [(hout i).1 (Nat.lt_add_right _ hi), (hin i).1 hi]
    · by_cases hlo : i < acc.size + 2 ^ k
      · have hlt : 64 * (i - acc.size) + c < 64 * 2 ^ k := by
          have := Nat.mul_le_mul_left 64 (show i - acc.size + 1 ≤ 2 ^ k by omega)
          omega
        rw [(hout i).1 hlo, (hin i).2 h1 hlo c hc, Nat.testBit_mod_two_pow, decide_eq_true hlt,
          Bool.true_and]
      · rw [(hout i).2 (by omega) (by rw [pow_succ] at h2; omega) c hc, Nat.testBit_shiftRight]
        congr 1
        rw [show i - acc.size = 2 ^ k + (i - (acc.size + 2 ^ k)) by omega]
        ring

variable {m : ℕ}

/-- The number of words of a block of `2 ^ m` positions. -/
abbrev nWords (m : ℕ) : ℕ := 2 ^ (m - 6)

theorem two_pow_le_nWords (m : ℕ) : 2 ^ m ≤ 64 * nWords m := by
  rcases Nat.lt_or_ge m 6 with h | h
  · calc 2 ^ m ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) h.le
      _ = 64 * 1 := by norm_num
      _ ≤ 64 * nWords m := Nat.mul_le_mul_left _ Nat.one_le_two_pow
  · rw [nWords, show 64 = 2 ^ 6 by norm_num, ← pow_add, Nat.add_sub_cancel' h]

/-- The words `zw` hold the bits of `z`, every position of every word. -/
def Rep (zw : Array UInt64) (z : Form m) : Prop :=
  zw.size = nWords m ∧
    ∀ j < 64 * nWords m, (zw.getD (j / 64) 0).toBitVec.getLsbD (j % 64) = z.getLsbD j

/-- The words of a bitset. -/
def wordsOf (x : Form m) : Array UInt64 := wordsAux (m - 6) x.toNat #[]

theorem rep_wordsOf (x : Form m) : Rep (wordsOf x) x := by
  refine ⟨by rw [wordsOf, size_wordsAux]; simp, fun j hj ↦ ?_⟩
  rw [wordsOf, (wordsAux_getD (m - 6) x.toNat #[] (j / 64)).2 (Nat.zero_le _)
    (by rw [Array.size_empty, zero_add]; exact Nat.div_lt_of_lt_mul hj) (j % 64)
    (Nat.mod_lt _ (by norm_num))]
  simp only [Array.size_empty, Nat.sub_zero, Nat.div_add_mod]
  rfl

/-- The value of a form on a block, by their words. -/
theorem evalW_eq_evalB {Lw zw : Array UInt64} {L z : Form m} (hL : Rep Lw L) (hz : Rep zw z) :
    evalW Lw zw = L.evalB z := by
  apply toZ_injective
  rw [evalW, parity, toZ_parityAux _ 64 le_rfl, hL.1, evalB_eq_eval, toZ_eval, Form.evalZ]
  simp only [toZ_getLsbD_xorAnd]
  have hbits : ∀ j < 64 * nWords m,
      toZ ((Lw.getD (j / 64) 0).toBitVec.getLsbD (j % 64) &&
        (zw.getD (j / 64) 0).toBitVec.getLsbD (j % 64)) =
        if L.getLsbD j then toZ (z.getLsbD j) else 0 := fun j hj ↦ by
    rw [hL.2 j hj, hz.2 j hj]
    cases L.getLsbD j <;> cases z.getLsbD j <;> rfl
  have hsum := sum_words (fun j ↦ if L.getLsbD j then toZ (z.getLsbD j) else 0) (nWords m)
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ if L.getLsbD j then toZ (z.getLsbD j) else 0) (2 ^ m)]
  rw [show (∑ j ∈ Finset.range (2 ^ m), if L.getLsbD j then toZ (z.getLsbD j) else 0) =
      ∑ j ∈ Finset.range (64 * nWords m), if L.getLsbD j then toZ (z.getLsbD j) else 0 from ?_]
  · rw [← hsum, show toZ false = 0 from rfl, zero_add]
    refine Finset.sum_congr rfl fun b hb ↦ Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hb hi
    have hj : 64 * i + b < 64 * nWords m := by omega
    rw [← hbits _ hj, show (64 * i + b) / 64 = i by omega, show (64 * i + b) % 64 = b by omega]
  · rw [show 64 * nWords m = 2 ^ m + (64 * nWords m - 2 ^ m) by
      have := two_pow_le_nWords m; omega, Finset.sum_range_add]
    simp [BitVec.getLsbD_of_ge]

/-! ## Setting a bit -/

/-- Bit `j` of a bitset after its bit `k` is set to `b`. -/
theorem getLsbD_setBitB (w : Form m) (k : Pos m) (b : Bool) (j : ℕ) (hj : j < 2 ^ m) :
    (setBitB w k b).getLsbD j = if (k : ℕ) = j then b else w.getLsbD j := by
  unfold setBitB
  by_cases hkj : (k : ℕ) = j
  · cases b <;> simp [Form.var, BitVec.getElem_twoPow, hkj, hj]
  · have hjk : j ≠ (k : ℕ) := fun h ↦ hkj h.symm
    cases b <;> simp [Form.var, BitVec.getElem_twoPow, hkj, hjk, hj]

/-- Set bit `k` of a block given by its words to `b`: one word updated. -/
def setBitW (zw : Array UInt64) (k : ℕ) (b : Bool) : Array UInt64 :=
  zw.modify (k / 64) fun w ↦
    if b then w ||| ((1 : UInt64) <<< (k % 64).toUInt64)
    else w &&& ~~~((1 : UInt64) <<< (k % 64).toUInt64)

private theorem getLsbD_mask {s c : ℕ} (hs : s < 64) (hc : c < 64) :
    ((1 : UInt64) <<< s.toUInt64).toBitVec.getLsbD c = decide (s = c) := by
  rw [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq']
  have : (s.toUInt64.toBitVec % 64).toNat = s := by
    simp [Nat.toUInt64, Nat.mod_eq_of_lt hs, BitVec.toNat_umod]
  rw [this, BitVec.getLsbD_shiftLeft]
  simp only [UInt64.toBitVec_one, BitVec.getLsbD_one, hc, decide_true, Bool.true_and]
  by_cases h : s = c
  · subst h; simp
  · by_cases hlt : c < s
    · simp [hlt, h]
    · simp [hlt, h, show c - s ≠ 0 by omega]

/-- Setting a bit through the words sets it in the bitset they hold. -/
theorem rep_setBitW {zw : Array UInt64} {z : Form m} (hz : Rep zw z) (k : Pos m) (b : Bool) :
    Rep (setBitW zw k b) (setBitB z k b) := by
  refine ⟨by rw [setBitW, Array.size_modify, hz.1], fun j hj ↦ ?_⟩
  have hset : (setBitB z k b).getLsbD j = if (k : ℕ) = j then b else z.getLsbD j := by
    by_cases hjm : j < 2 ^ m
    · exact getLsbD_setBitB z k b j hjm
    · have hkj : (k : ℕ) ≠ j := by have := k.isLt; omega
      rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]
      simp [hkj]
  rw [hset, ← hz.2 j hj]
  simp only [setBitW, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  have hjw : j / 64 < zw.size := by rw [hz.1]; omega
  have hc : j % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hkc : (k : ℕ) % 64 < 64 := Nat.mod_lt _ (by norm_num)
  split
  · rename_i hw
    have hiff : ((k : ℕ) % 64 = j % 64) ↔ (k : ℕ) = j := by omega
    rw [Array.getElem?_eq_getElem hjw, Option.map_some, Option.getD_some, Option.getD_some]
    cases b
    · simp only [Bool.false_eq_true, ite_false, UInt64.toBitVec_and, UInt64.toBitVec_not,
        BitVec.getLsbD_and, BitVec.getLsbD_not, getLsbD_mask hkc hc, hc, decide_true,
        Bool.true_and]
      by_cases h : (k : ℕ) = j
      · simp [h]
      · simp [h, hiff.not.mpr h]
    · simp only [ite_true, UInt64.toBitVec_or, BitVec.getLsbD_or, getLsbD_mask hkc hc]
      by_cases h : (k : ℕ) = j
      · simp [h]
      · simp [h, hiff.not.mpr h]
  · rename_i hw
    have hkj : (k : ℕ) ≠ j := by omega
    simp [hkj]

/-! ## The compiled circuit -/

/-- A circuit compiled for its honest prover: the constant position, the inputs, and each gate's
position with the words of its two forms. -/
structure Compiled (m : ℕ) where
  /-- The position holding `1`. -/
  cpos : Pos m
  /-- The input positions. -/
  inputs : Form m
  /-- The gates: position, and the words of the left and the right form. -/
  gates : Array (Pos m × Array UInt64 × Array UInt64)

/-- A gate, compiled. -/
def compileGate (kg : Pos m × Gate m) : Pos m × Array UInt64 × Array UInt64 :=
  (kg.1, wordsOf kg.2.a, wordsOf kg.2.b)

/-- A circuit, compiled. -/
def compile (c : ProductCircuit m) : Compiled m :=
  ⟨c.cpos, c.inputs, c.gates.map compileGate⟩

/-- One compiled gate on the block's words: its position takes the product of its forms. -/
def stepW (zw : Array UInt64) (g : Pos m × Array UInt64 × Array UInt64) : Array UInt64 :=
  setBitW zw g.1 (evalW g.2.1 zw && evalW g.2.2 zw)

/-- The honest block of the inputs `inp`, as words: the compiled gates in order. -/
def Compiled.traceW (pc : Compiled m) (inp : Form m) : Array UInt64 :=
  pc.gates.foldl stepW (wordsOf ((pc.inputs &&& inp) ||| Form.var pc.cpos))

private theorem rep_foldl {zw : Array UInt64} {z : Form m} (hz : Rep zw z) :
    (gs : List (Pos m × Gate m)) → Rep ((gs.map compileGate).foldl stepW zw) (gs.foldl stepB z)
  | [] => hz
  | kg :: gs => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    refine rep_foldl ?_ gs
    rw [stepW, compileGate, stepB, evalW_eq_evalB (rep_wordsOf _) hz,
      evalW_eq_evalB (rep_wordsOf _) hz]
    exact rep_setBitW hz kg.1 _

/-- **The compiled trace is the trace**: the words of the compiled circuit's honest block hold
`trace`'s. -/
theorem rep_traceW (c : ProductCircuit m) (inp : Form m) :
    Rep ((compile c).traceW inp) (c.trace inp) := by
  rw [Compiled.traceW, compile, trace, ← Array.foldl_toList, Array.toList_map,
    ← Array.foldl_toList, initB]
  exact rep_foldl (rep_wordsOf _) _

end ProductCircuit

end
end LeanerVM.Protocol
