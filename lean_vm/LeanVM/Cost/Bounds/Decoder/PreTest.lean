module

public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Bounds.FieldLib
public import LeanVM.Cost.Bounds.Decoder.PreTestDefs
public import LeanVM.Cost.Decoder.PreTest

/-!
# Bound: the decoder's precondition test, compiled

The prices of `Guest.Fast.preTestAt D T rd j fp` (`Cost/Decoder/PreTest.lean`), function `j`'s
precondition at the frame `fp` from the table `T` of the functions' preconditions, the
logarithm's baby-step tables `D` given. Parametric in what the test calls:

* a memory read: the reader closure `rdVal` at most `R` (the decoder's `memReaderC`,
  `Bounds/Decoder/DecoderEnds.lean`: `123 + 42κ`);
* a logarithm's bound: `powBelowC` at most `B` at a bound `n ≤ 34` (every bound of the deployed
  table, `preTable_shape`). `powBelow_cost` gives `B = 911`: the word's lane compared with the
  lanes `2^0, …, 2^(n-1)` of `g^0, …, g^(n-1)` (`twoPowScanC`), no logarithm (the logarithm
  serves only bounds above `34`, `powBelowLogC`);
* the exponents of an entry within `W ≤ 7` bits (`FnPreWithin`): a power `g^o`, `o < 128`, read
  off the powers table `Pw` (`gpowAt_cost`, `19`; `psAt W = 6 + 535·W` by squaring, `3751` at
  `W = 7`, before the table held them).

The bounds, bottom-up: `powBelowAt_cost` (`6`), `readIs_cost` (`19`), `gpowAt_cost` (`19`),
`symValAt_cost`, `envOne_cost`,
`readPowBelow_cost`, `bndOne_cost`, `memAt_cost`, `memCell_cost`, `memOne_cost`, `wordAt_cost`
(`wordWith_cost`, by squaring, for the entry table),
`powSqE_cost` (a power in `E` by squaring, `12 + 4732·(log₂ n + 1)`), `expOne_cost`,
`expTablesAt_cost` (the exponent tables' `34` entries, the powers `gen^(2^j)` read off the table
`Pw` the caller built once: `68R + 23142`), `semOne_cost`, then

* **`fnPreTest_cost`**: an entry's test at most `fnPrePrice R B t` (`PreTestDefs.lean`);
* **`preTestAt_cost`**: function `j`'s test at most `fnPrePrice R B (T.getD j none) + 19`;
* **`preTestAt_cost_deployed`**: on the deployed table (`preTable`, its shape evaluated in
  `PreTableShape.lean`: exponents below `2^7`, at most one check of each kind, at most `99`
  bounds and memory cells, their logarithms' bounds at most `34`), at most
  `269R + 99B + 86262`. With `B = 911` (`powBelow_cost`) and the deployed reader
  (`R ≤ 1472`): `572419 ≈ 2^19.13` per call (`1543736 ≈ 2^20.56` with the powers by squaring,
  `99·402684 + 1453547 ≈ 2^25.30` with a discrete logarithm per bound);
* **`genPows_cost`**: the powers table, built once (`genPowsC`: `34` squarings for `gen^(2^j)`,
  `128` products for `g^o`), at most `117080`.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Fast LeanVM.Extraction.Fast

public section

variable (P : LeanVM.Cost.MachineProgram)

/-! ## Powers and the logarithm's bound -/

/-- A power `g^o` by squaring, `o < 2^W`: at most `psAt W`. -/
theorem powSqW_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c198.costDeps) {W o : ℕ}
    (hW : 0 < W) (hW64 : W < 64) (ho : o < 2 ^ W) :
    machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c198.costIdx [encodeValue LeanVM.Parameters.g, encodeValue o] ≤
      psAt W := by
  have h64 : 2 ^ W ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hW64.le
  have h1 := powSq_cost P hP LeanVM.Parameters.g o (by omega)
  have h2 := log2_lt_of hW ho
  unfold psAt
  omega

/-- A power in `E` by squaring (`powSqEC`): at most `12 + 4732·(log₂ n + 1)`. -/
theorem powSqE_cost (hP : Includes P powSqEC.costDeps) (a : E) (n : ℕ)
    (hn : n < 2 ^ 64) :
    machineCost P powSqEC.costIdx [encodeValue a, encodeValue n] ≤
      12 + 4732 * (Nat.log2 n + 1) := by
  have := le_of_halving (fun x : E × ℕ ↦ x.2 < 2 ^ 64) (fun x ↦ x.2)
    (fun x ↦ machineCost P powSqEC.costIdx
      [encodeValue x.1, encodeValue x.2]) 4732 12
    (fun x hx h0 ↦ by
      try dsimp only at hx h0 ⊢
      rw [powSqEC.costEq P hP, h0]
      simp)
    (fun x hx hpos ↦ by
      try dsimp only at hx hpos ⊢
      right
      refine ⟨(x.1 * x.1, x.2 / 2), by dsimp only; omega, le_refl _, ?_⟩
      rw [powSqEC.costEq P hP, limbs_of_lt hx,
        limbs_of_lt (by omega : x.2 % 2 < 2 ^ 64)]
      simp only [show x.2 ≠ 0 by omega, ↓reduceIte]
      split_ifs <;> omega)
    (a, n) hn
  simpa using this

/-- Whether a logarithm is below `n` (`powBelowAtC`): at most `6`, on word-sized numbers. -/
theorem powBelowAt_cost (hP : Includes P powBelowAtC.costDeps) (o : Option ℕ) (n : ℕ)
    (hn : n < 2 ^ 64) (ho : ∀ m, o = some m → m < 2 ^ 64) :
    machineCost P powBelowAtC.costIdx [encodeValue o, encodeValue n] ≤ 6 := by
  rw [powBelowAtC.costEq P hP]
  cases o with
  | none => dsimp only; omega
  | some m =>
    dsimp only
    rw [limbs_of_lt (ho m rfl), limbs_of_lt hn]
    simp only [max_self]
    omega

/-- The lanes' scan (`twoPowScanC`) over `m` shifts from `e`, `e + m ≤ 63`: `26` per shift and
`6`, on words. -/
theorem twoPowScan_cost (hP : Includes P twoPowScanC.costDeps) (w : ℕ) (hw : w < 2 ^ 64) :
    ∀ (m e : ℕ), e + m ≤ 63 →
      machineCost P twoPowScanC.costIdx [encodeValue w, encodeValue e, encodeValue m] ≤ 26 * m + 6
  | 0, e, _ => by rw [twoPowScanC.costEq_zero P hP]
  | m + 1, e, he => by
    have hs : 1 <<< e < 2 ^ 64 := by
      rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [twoPowScanC.costEq_succ P hP, limbs_of_lt (by omega : m + 1 < 2 ^ 64), limbs_of_lt hs,
      limbs_of_lt (by omega : e < 2 ^ 64), limbs_of_lt hw]
    have := twoPowScan_cost hP w hw m (e + 1) (by omega)
    simp only [max_self]
    split_ifs <;> omega

/-- **A logarithm's bound** (`powBelowC`) at a bound `n ≤ 34`: the word's lane compared with the
lanes `2^0, …, 2^(n-1)` of `g^0, …, g^(n-1)` (`twoPowScanC`), at most `26·n + 27 ≤ 911`; no
logarithm. -/
theorem powBelow_cost (hP : Includes P powBelowC.costDeps) (D : DiscreteLogTables) (w : E)
    (n : ℕ) (hn : n ≤ 34) :
    machineCost P powBelowC.costIdx [encodeValue D, encodeValue w, encodeValue n] ≤ 911 := by
  rw [powBelowC.costEq P hP, limbs_of_lt (by omega : n < 2 ^ 64),
    limbs_of_lt (by unfold scanBound; norm_num : scanBound < 2 ^ 64)]
  have := twoPowScan_cost P (by includes) (w.limb 0).lane.toNat (UInt64.toNat_lt _) n 0
    (by omega)
  have hs : n ≤ scanBound := hn
  simp only [hs, ↓reduceIte, max_self]
  split_ifs <;> omega

/-- Whether the word read is `x` (`readIsC`): at most `19`. -/
theorem readIs_cost (hP : Includes P readIsC.costDeps) (o : Option E) (x : E) :
    machineCost P readIsC.costIdx [encodeValue o, encodeValue x] ≤ 19 := by
  rw [readIsC.costEq P hP]
  cases o with
  | none => dsimp only; omega
  | some w => dsimp only; split_ifs <;> omega

/-- An exponent of `W ≤ 7` bits is below `128`: the powers table holds its power. -/
theorem lt_smallPowBound {W o : ℕ} (hW7 : W ≤ 7) (ho : o < 2 ^ W) : o < smallPowBound := by
  have : 2 ^ W ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hW7
  unfold smallPowBound
  omega

/-- **A power `g^o`, `o < 128`, read off the powers table** (`gpowAtC`): `19`. -/
theorem gpowAt_cost (hP : Includes P gpowAtC.costDeps) (Pw : Array E) (o : ℕ)
    (ho : o < smallPowBound) :
    machineCost P gpowAtC.costIdx [encodeValue Pw, encodeValue o] ≤ 19 := by
  have h128 : smallPowBound < 2 ^ 64 := by unfold smallPowBound; norm_num
  rw [gpowAtC.costEq P hP, limbs_of_lt (by omega : o < 2 ^ 64), limbs_of_lt h128,
    limbs_of_lt (by norm_num [LeanVM.Guest.B1.sizeBits] : LeanVM.Guest.B1.sizeBits < 2 ^ 64)]
  simp only [ho, ↓reduceIte, max_self]
  omega

/-- A known word's value (`symValAtC`), its power read off the table: at most `287`. -/
theorem symValAt_cost (hP : Includes P symValAtC.costDeps) (Pw : Array E) (fp : K) (a : Sym)
    (ha : symExp a < smallPowBound) :
    machineCost P symValAtC.costIdx [encodeValue Pw, encodeValue fp, encodeValue a] ≤ 287 := by
  rw [symValAtC.costEq P hP]
  cases a with
  | zero => dsimp only; omega
  | gp e => have := gpowAt_cost P (by includes) Pw e ha; dsimp only; omega
  | fpg e => have := gpowAt_cost P (by includes) Pw e ha; dsimp only; omega

/-- The sum of an affine price over a list. -/
theorem sum_map_affine {α : Type} (f : α → ℕ) (a b : ℕ) :
    ∀ l : List α, (l.map fun x ↦ a * f x + b).sum = a * (l.map f).sum + b * l.length
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, sum_map_affine f a b l]
    ring

/-- `List.all` (`all.c240`), the predicate's price depending on the element: its prices and `9`
per element, `3`. -/
theorem all_cost_sum (hP : Includes P Auto.List.all.c240.costDeps) {β : Type} [MachineEncoding β]
    (p : β → Bool) (pVal : MachineValue)
    (hp : ∀ a, RunsApp P pVal [encodeValue a] (encodeValue (p a))) (B : β → ℕ) :
    ∀ l : List β, (∀ a ∈ l, appCost P pVal [encodeValue a] ≤ B a) →
      machineCost P Auto.List.all.c240.costIdx [encodeValue l, pVal] ≤
        (l.map fun a ↦ B a + 9).sum + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.all.c240.costEq_nil P hP p pVal hp]; simp
  | cons a l ih =>
    intro hB
    rw [Auto.List.all.c240.costEq_cons P hP a l p pVal hp]
    have h1 := ih fun a' ha ↦ hB a' (by simp [ha])
    have h2 := hB a (by simp)
    simp only [List.map_cons, List.sum_cons]
    split_ifs <;> omega

/-- The squarings (`squaresFromC`): `2371` per squaring, `6`. -/
theorem squaresFrom_cost (hP : Includes P squaresFromC.costDeps) :
    ∀ (n : ℕ) (x : E), n < 2 ^ 64 →
      machineCost P squaresFromC.costIdx [encodeValue x, encodeValue n] ≤ 2371 * n + 6 := by
  intro n
  induction n with
  | zero => intro x _; rw [squaresFromC.costEq_zero P hP]
  | succ n ih =>
    intro x hn
    rw [squaresFromC.costEq_succ P hP, limbs_of_lt hn]
    have := ih (x * x) (by omega)
    omega

/-- The products (`powsFromC`): `281` per product, `6`. -/
theorem powsFrom_cost (hP : Includes P powsFromC.costDeps) :
    ∀ (n : ℕ) (y : K), n < 2 ^ 64 →
      machineCost P powsFromC.costIdx [encodeValue y, encodeValue n] ≤ 281 * n + 6 := by
  intro n
  induction n with
  | zero => intro y _; rw [powsFromC.costEq_zero P hP]
  | succ n ih =>
    intro y hn
    rw [powsFromC.costEq_succ P hP, limbs_of_lt hn]
    have := ih (y * LeanVM.Parameters.g) (by omega)
    omega

/-- **The powers table** (`genPowsC`: `gen^(2^j)` for `j < 34` by squarings, `g^o` for `o < 128`
by products), built once: at most `117080`. -/
theorem genPows_cost (hP : Includes P genPowsC.costDeps) :
    machineCost P genPowsC.costIdx [] ≤ 117080 := by
  rw [genPowsC.costEq P hP, List.length_append, length_squaresFrom]
  have hs : LeanVM.Guest.B1.sizeBits = 34 := rfl
  have hp : smallPowBound = 128 := rfl
  have h1 := squaresFrom_cost P (by includes) LeanVM.Guest.B1.sizeBits LeanVM.Protocol.Verifier.gen
    (by norm_num [hs])
  have h2 := powsFrom_cost P (by includes) smallPowBound 1 (by norm_num [hp])
  have h3 := append_cost P (by includes)
    (squaresFrom LeanVM.Protocol.Verifier.gen LeanVM.Guest.B1.sizeBits) (powsFrom 1 smallPowBound)
  have h4 : (powsFrom 1 smallPowBound).length = 128 := by
    rw [hp]; exact length_powsFrom 128 1
  rw [length_squaresFrom] at h3
  rw [hs, hp] at *
  omega

/-! ## The checks, one by one -/

section Checks

variable (D : DiscreteLogTables) (rd : Reader) (rdVal : MachineValue)
  (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
  (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)
  (B : ℕ) (hB : ∀ (w : E) (n : ℕ), n ≤ 34 →
    machineCost P powBelowC.costIdx [encodeValue D, encodeValue w, encodeValue n] ≤ B)
  {W : ℕ} (hW : 0 < W) (hW64 : W < 64)

include hrd

include hR in
/-- An entry-environment check (`envOneC`): a power off the table, a read, the known word's value
and `269`: `R + 594`. -/
theorem envOne_cost (hP : Includes P envOneC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (p : ℕ × Sym) (h1 : p.1 < 2 ^ W) (h2 : symExp p.2 < 2 ^ W) :
    machineCost P envOneC.costIdx [encodeValue Pw, rdVal, encodeValue fp, encodeValue p] ≤
      R + 594 := by
  rw [envOneC.costEq P hP Pw rd rdVal hrd]
  have := gpowAt_cost P (by includes) Pw p.1 (lt_smallPowBound hW7 h1)
  have := hR (fp * gpowAt Pw p.1)
  have := symValAt_cost P (by includes) Pw fp p.2 (lt_smallPowBound hW7 h2)
  have := readIs_cost P (by includes) (rd (fp * gpowAt Pw p.1)) (symValAt Pw fp p.2)
  omega

omit hrd in
include hB in
/-- A read's logarithm's bound (`readPowBelowC`): `B + 6`. -/
theorem readPowBelow_cost (hP : Includes P readPowBelowC.costDeps) (o : Option E) (n : ℕ)
    (hn : n ≤ 34) :
    machineCost P readPowBelowC.costIdx [encodeValue D, encodeValue o, encodeValue n] ≤ B + 6 := by
  rw [readPowBelowC.costEq P hP]
  cases o with
  | none => dsimp only; omega
  | some w => have := hB w n hn; dsimp only; omega

include hR hB in
/-- A bound on a frame cell (`bndOneC`): a power off the table, a read, a logarithm's bound and
`273`: `R + B + 292`. -/
theorem bndOne_cost (hP : Includes P bndOneC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (p : ℕ × ℕ) (h1 : p.1 < 2 ^ W) (h2 : p.2 ≤ 34) :
    machineCost P bndOneC.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp,
      encodeValue p] ≤ R + B + 292 := by
  rw [bndOneC.costEq P hP D Pw rd rdVal hrd]
  have := gpowAt_cost P (by includes) Pw p.1 (lt_smallPowBound hW7 h1)
  have := hR (fp * gpowAt Pw p.1)
  have := readPowBelow_cost P D B hB (by includes) (rd (fp * gpowAt Pw p.1)) p.2 h2
  omega

include hR hB in
/-- A memory bound at one cell (`memAtC`): a power off the table, a read, a logarithm's bound and
`282`: `R + B + 301`. -/
theorem memAt_cost (hP : Includes P memAtC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (n c : ℕ)
    (p : E) (hn : n ≤ 34) (hc : c < 2 ^ W) :
    machineCost P memAtC.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue n,
      encodeValue c, encodeValue p] ≤ R + B + 301 := by
  rw [memAtC.costEq P hP D Pw rd rdVal hrd]
  have := gpowAt_cost P (by includes) Pw c (lt_smallPowBound hW7 hc)
  have := hR (p.limb 0 * gpowAt Pw c)
  have := readPowBelow_cost P D B hB (by includes) (rd (p.limb 0 * gpowAt Pw c)) n hn
  split_ifs <;> omega

include hR hB in
/-- A memory bound at one cell of the address in a frame cell (`memCellC`): two powers off the
table, two reads, a logarithm's bound: `2R + B + 590`. -/
theorem memCell_cost (hP : Includes P memCellC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (o n c : ℕ) (ho : o < 2 ^ W) (hn : n ≤ 34) (hc : c < 2 ^ W) :
    machineCost P memCellC.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp,
      encodeValue o, encodeValue n, encodeValue c] ≤ 2 * R + B + 590 := by
  rw [memCellC.costEq P hP D Pw rd rdVal hrd]
  have := gpowAt_cost P (by includes) Pw o (lt_smallPowBound hW7 ho)
  have := hR (fp * gpowAt Pw o)
  generalize rd (fp * gpowAt Pw o) = r
  cases r with
  | none => dsimp only; omega
  | some p =>
    have := memAt_cost P D rd rdVal hrd R hR B hB (by includes) Pw hW7 n c p hn hc
    dsimp only; omega

include hR hB in
/-- A memory bound (`memOneC`): per cell `2R + B + 624`, and `31`. -/
theorem memOne_cost (hP : Includes P memOneC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (m : ℕ × ℕ × ℕ) (h1 : m.1 < 2 ^ W) (h2 : m.2.1 ≤ 2 ^ W) (h3 : m.2.2 ≤ 34) :
    machineCost P memOneC.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp,
      encodeValue m] ≤ (2 * R + B + 624) * m.2.1 + 31 := by
  have h64 : 2 ^ W ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hW7
  rw [memOneC.costEq P hP D Pw rd rdVal hrd]
  have hr := rangeLoop_cost P (by includes) m.2.1 [] (by omega)
  have ha := all_cost P (by includes) _
    (.closure memOneC.lam0.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp,
      encodeValue m.2.2, encodeValue m.1])
    (fun c ↦ RunsApp.of_spec (memOneC.lam0.costSpec P (by includes) D Pw rd rdVal hrd fp m.2.2
      m.1 c))
    (2 * R + B + 598) (List.range m.2.1) (fun c hc ↦ by
      have hc' := List.mem_range.mp hc
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [memOneC.lam0.costEq P (by includes) D Pw rd rdVal hrd]
      have := memCell_cost P D rd rdVal hrd R hR B hB (by includes) Pw hW7 fp m.1 m.2.2 c
        h1 h3 (by omega)
      omega)
  rw [List.length_range] at ha
  nlinarith

include hR hW hW64 in
/-- A frame cell's word (`wordWithC`): a power, a read and `271`. -/
theorem wordWith_cost (hP : Includes P wordWithC.costDeps) (fp : K)
    (o : ℕ) (ho : o < 2 ^ W) :
    machineCost P wordWithC.costIdx
      [rdVal, encodeValue fp, encodeValue o] ≤ psAt W + R + 271 := by
  rw [wordWithC.costEq P hP rd rdVal hrd]
  have := powSqW_cost P (by includes) hW hW64 ho
  have := hR (fp * gpow o)
  generalize rd (fp * gpow o) = r
  cases r <;> dsimp only <;> omega

include hR in
/-- A frame cell's word (`wordAtC`), its power read off the table: `R + 289`. -/
theorem wordAt_cost (hP : Includes P wordAtC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (o : ℕ) (ho : o < 2 ^ W) :
    machineCost P wordAtC.costIdx [encodeValue Pw, rdVal, encodeValue fp, encodeValue o] ≤
      R + 289 := by
  rw [wordAtC.costEq P hP Pw rd rdVal hrd]
  have := gpowAt_cost P (by includes) Pw o (lt_smallPowBound hW7 ho)
  have := hR (fp * gpowAt Pw o)
  generalize rd (fp * gpowAt Pw o) = r
  cases r <;> dsimp only <;> omega

include hR in
/-- An entry of the exponent tables (`expOneC`), `j < 34`, the powers `g^j` and `gen^(2^j)` read
off the table `Pw`: two reads, at most `2R + 647`. -/
theorem expOne_cost (hP : Includes P expOneC.costDeps) (Pw : Array E) (p q : E) (j : ℕ)
    (hj : j < 34) :
    machineCost P expOneC.costIdx [encodeValue Pw, rdVal, encodeValue p, encodeValue q,
      encodeValue j] ≤ 2 * R + 647 := by
  rw [expOneC.costEq P hP Pw rd rdVal hrd, limbs_shift (by omega),
    limbs_of_lt (by omega : j < 2 ^ 64)]
  have h1 := gpowAt_cost P (by includes) Pw j (by unfold smallPowBound; omega)
  have h2 := hR (p.limb 0 * gpowAt Pw j)
  have h3 := hR (q.limb 0 * gpowAt Pw j)
  have h4 := readIs_cost P (by includes) (rd (p.limb 0 * gpowAt Pw j))
    (LeanVM.Protocol.Verifier.eOfNat (2 ^ j))
  have h5 := readIs_cost P (by includes) (rd (q.limb 0 * gpowAt Pw j)) (Pw.getD j 0)
  split_ifs <;> omega

include hR in
/-- The exponent tables at two words (`expTablesAtC`): `34` entries, at most `68R + 23142`. -/
theorem expTablesAt_cost (hP : Includes P expTablesAtC.costDeps) (Pw : Array E) (p q : E) :
    machineCost P expTablesAtC.costIdx [encodeValue Pw, rdVal, encodeValue p, encodeValue q] ≤
      68 * R + 23142 := by
  rw [expTablesAtC.costEq P hP Pw rd rdVal hrd]
  have hs : LeanVM.Guest.B1.sizeBits = 34 := rfl
  have hr := rangeLoop_cost P (by includes) LeanVM.Guest.B1.sizeBits [] (by rw [hs]; norm_num)
  have ha := all_cost P (by includes) _
    (.closure expTablesAtC.lam0.costIdx [encodeValue Pw, rdVal, encodeValue p, encodeValue q])
    (fun j ↦ RunsApp.of_spec (expTablesAtC.lam0.costSpec P (by includes) Pw rd rdVal hrd p q j))
    (2 * R + 654) (List.range LeanVM.Guest.B1.sizeBits) (fun j hj ↦ by
      have hj' := List.mem_range.mp hj
      rw [hs] at hj'
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [expTablesAtC.lam0.costEq P (by includes) Pw rd rdVal hrd]
      have := expOne_cost P rd rdVal hrd R hR (by includes) Pw p q j hj'
      omega)
  simp only [hs, List.length_range] at hr ha ⊢
  omega

include hR in
/-- A semantic pair (`semOneC`): two frame cells' words and the exponent tables at them: at most
`70R + 23735`. -/
theorem semOne_cost (hP : Includes P semOneC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (p : ℕ × ℕ) (h1 : p.1 < 2 ^ W) (h2 : p.2 < 2 ^ W) :
    machineCost P semOneC.costIdx [encodeValue Pw, rdVal, encodeValue fp, encodeValue p] ≤
      70 * R + 23735 := by
  rw [semOneC.costEq P hP Pw rd rdVal hrd]
  have := wordAt_cost P rd rdVal hrd R hR (by includes) Pw hW7 fp p.1 h1
  have := wordAt_cost P rd rdVal hrd R hR (by includes) Pw hW7 fp p.2 h2
  have := expTablesAt_cost P rd rdVal hrd R hR (by includes) Pw
    (wordAt Pw rd fp p.1) (wordAt Pw rd fp p.2)
  omega

/-! ## An entry, and function `j` -/

include hR hB in
/-- **An entry's test** (`fnPreTestC`), its exponents within `W ≤ 7` bits: at most
`fnPrePrice R B t`. -/
theorem fnPreTest_cost (hP : Includes P fnPreTestC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (t : Option FnPre) (ht : ∀ s, t = some s → FnPreWithin W s) :
    machineCost P fnPreTestC.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp,
      encodeValue t] ≤ fnPrePrice R B t := by
  rw [fnPreTestC.costEq P hP D Pw rd rdVal hrd]
  cases t with
  | none => dsimp only; simp [fnPrePrice]
  | some s =>
    obtain ⟨he, hpre, hm, hsem⟩ := ht s rfl
    dsimp only
    have h1 := all_cost P (by includes) _
      (.closure fnPreTestC.lam0.costIdx [encodeValue Pw, rdVal, encodeValue fp])
      (fun p ↦ RunsApp.of_spec (fnPreTestC.lam0.costSpec P (by includes) Pw rd rdVal hrd fp p))
      (R + 599) s.env (fun p hp ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [fnPreTestC.lam0.costEq P (by includes) Pw rd rdVal hrd]
        have := envOne_cost P rd rdVal hrd R hR (by includes) Pw hW7 fp p (he p hp).1
          (he p hp).2
        omega)
    have h2 := all_cost P (by includes) _
      (.closure fnPreTestC.lam1.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp])
      (fun p ↦ RunsApp.of_spec (fnPreTestC.lam1.costSpec P (by includes) D Pw rd rdVal hrd fp p))
      (R + B + 298) s.pre (fun p hp ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [fnPreTestC.lam1.costEq P (by includes) D Pw rd rdVal hrd]
        have := bndOne_cost P D rd rdVal hrd R hR B hB (by includes) Pw hW7 fp p
          (hpre p hp).1 (hpre p hp).2
        omega)
    have h3 := all_cost_sum P (by includes) _
      (.closure fnPreTestC.lam2.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp])
      (fun m ↦ RunsApp.of_spec (fnPreTestC.lam2.costSpec P (by includes) D Pw rd rdVal hrd fp m))
      (fun m ↦ (2 * R + B + 624) * m.2.1 + 37) s.mem (fun m hm' ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [fnPreTestC.lam2.costEq P (by includes) D Pw rd rdVal hrd]
        have := memOne_cost P D rd rdVal hrd R hR B hB (by includes) Pw hW7 fp m
          (hm m hm').1 (hm m hm').2.1 (hm m hm').2.2
        omega)
    have h4 := all_cost P (by includes) _
      (.closure fnPreTestC.lam3.costIdx [encodeValue Pw, rdVal, encodeValue fp])
      (fun p ↦ RunsApp.of_spec (fnPreTestC.lam3.costSpec P (by includes) Pw rd rdVal hrd fp p))
      (70 * R + 23742) s.sem (fun p hp ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [fnPreTestC.lam3.costEq P (by includes) Pw rd rdVal hrd]
        have := semOne_cost P rd rdVal hrd R hR (by includes) Pw hW7 fp p (hsem p hp).1
          (hsem p hp).2
        omega)
    have hsum : (s.mem.map fun m ↦ (2 * R + B + 624) * m.2.1 + 37 + 9).sum =
        (2 * R + B + 624) * memCells s + 46 * s.mem.length := by
      have := sum_map_affine (fun m : ℕ × ℕ × ℕ ↦ m.2.1) (2 * R + B + 624) 46 s.mem
      unfold memCells
      rw [← this]
    rw [hsum] at h3
    simp only [fnPrePrice]
    split_ifs <;> nlinarith

include hR hB in
/-- **Function `j`'s precondition test** (`preTestAtC`), its entry's exponents within `W ≤ 7`
bits: at most `fnPrePrice R B (T.getD j none) + 19`. -/
theorem preTestAt_cost (hP : Includes P preTestAtC.costDeps) (T : Array (Option FnPre))
    (Pw : Array E) (hW7 : W ≤ 7) (j : ℕ) (hj : j < 2 ^ 64) (fp : K)
    (hT : ∀ s, T.getD j none = some s → FnPreWithin W s) :
    machineCost P preTestAtC.costIdx [encodeValue D, encodeValue T, encodeValue Pw, rdVal,
      encodeValue j, encodeValue fp] ≤ fnPrePrice R B (T.getD j none) + 19 := by
  rw [preTestAtC.costEq P hP D T Pw rd rdVal hrd, limbs_of_lt hj,
    limbs_of_lt (by unfold LeanVM.Guest.nFns; norm_num : LeanVM.Guest.nFns < 2 ^ 64)]
  have := fnPreTest_cost P D rd rdVal hrd R hR B hB (by includes) Pw hW7 fp
    (T.getD j none) hT
  simp only [max_self]
  split_ifs <;> omega

end Checks

/-! ## The deployed table -/

/-- An entry of the deployed shape has its exponents within `7` bits. -/
theorem fnPreWithin_of_shape {t : FnPre} (h : fnPreShape t = true) : FnPreWithin 7 t := by
  simp only [fnPreShape, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, he⟩, hp⟩, hm⟩, hs⟩ := h
  exact ⟨fun p hp' ↦ he p hp', fun p hp' ↦ hp p hp', fun m hm' ↦ ⟨(hm m hm').1.1, (hm m hm').1.2, (hm m hm').2⟩,
    fun p hp' ↦ hs p hp'⟩

/-- **An entry of the deployed shape**: its test's price at most `269R + 99B + 86243`. -/
theorem fnPrePrice_of_shape {t : FnPre} (h : fnPreShape t = true) (R B : ℕ) :
    fnPrePrice R B (some t) ≤ 269 * R + 99 * B + 86243 := by
  simp only [fnPreShape, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨he, hp⟩, hm⟩, hs⟩, hpc⟩, -⟩, -⟩, -⟩, -⟩ := h
  simp only [fnPrePrice]
  generalize t.env.length = e at *
  generalize t.pre.length = p at *
  generalize t.mem.length = m at *
  generalize t.sem.length = s at *
  generalize memCells t = c at *
  have h1 : (R + 608) * e ≤ (R + 608) * 1 := Nat.mul_le_mul_left _ he
  have h2 : (R + B + 307) * p + (2 * R + B + 624) * c ≤ (2 * R + B + 624) * (p + c) := by
    nlinarith
  have h3 : (2 * R + B + 624) * (p + c) ≤ (2 * R + B + 624) * 99 := Nat.mul_le_mul_left _ hpc
  have h4 : (70 * R + 23751) * s ≤ (70 * R + 23751) * 1 := Nat.mul_le_mul_left _ hs
  nlinarith

/-- An entry of a table of the deployed shape has that shape. -/
theorem fnPreShape_of_getD {T : Array (Option FnPre)} (hT : tableShape T = true) {j : ℕ}
    {s : FnPre} (hs : T.getD j none = some s) : fnPreShape s = true := by
  unfold tableShape at hT
  rw [List.all_eq_true] at hT
  by_cases hj : j < T.size
  · have hmem : T[j] ∈ T.toList := Array.getElem_mem_toList hj
    have h2 : Option.all fnPreShape (T.getInternal j hj) = true := hT _ hmem
    simp only [Array.getD, hj, ↓reduceDIte] at hs
    rw [hs] at h2
    simpa using h2
  · simp [Array.getD, hj] at hs

/-- **Function `j`'s precondition test on a table of the deployed shape** (`preTable`:
`preTable_shape`, `PreTableShape.lean`), the powers `Pw` any table: at most
`269R + 99B + 86262`. -/
theorem preTestAt_cost_deployed (hP : Includes P preTestAtC.costDeps) (D : DiscreteLogTables)
    (rd : Reader) (rdVal : MachineValue)
    (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
    (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)
    (B : ℕ) (hB : ∀ (w : E) (n : ℕ), n ≤ 34 →
      machineCost P powBelowC.costIdx [encodeValue D, encodeValue w, encodeValue n] ≤ B)
    (T : Array (Option FnPre)) (hT : tableShape T = true) (Pw : Array E) (j : ℕ)
    (hj : j < 2 ^ 64) (fp : K) :
    machineCost P preTestAtC.costIdx [encodeValue D, encodeValue T, encodeValue Pw, rdVal,
      encodeValue j, encodeValue fp] ≤ 269 * R + 99 * B + 86262 := by
  have := preTestAt_cost P D rd rdVal hrd R hR B hB (W := 7) hP T Pw le_rfl j hj fp
    (fun s hs ↦ fnPreWithin_of_shape (fnPreShape_of_getD hT hs))
  cases hg : T.getD j none with
  | none => rw [hg] at this; simp only [fnPrePrice] at this; omega
  | some s =>
    rw [hg] at this
    have := fnPrePrice_of_shape (fnPreShape_of_getD hT hg) R B
    omega

end

end LeanVM.Cost.Bounds
