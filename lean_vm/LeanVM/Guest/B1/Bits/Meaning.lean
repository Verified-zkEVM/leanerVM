/-
  LeanVM.Guest.B1.Bits.Meaning

  The interface of B1's bit, log and exponent functions: what each computes, and the statement
  that its core IR computes it.
-/

module

public import LeanVM.Guest.B1.Common.Basic

/-!
# Bits, logs and the exponent: meanings (TRIAGE G #2, #16-21)

For each function of the guest (`crates/rec_aggregation/guests/lean_ethereum.py` at leanVM
`4af2cdddd`, G below) its meaning `Meaning…` on its argument and return words, and `…_Spec`, the
statement that its core IR relation (`coreProgram.Rel`) is that meaning. A `…_Spec` is a
definition (a `Prop`); its proof is the theorem `…_holds : …_Spec` of the family's modules.

| function | G | meaning |
| --- | --- | --- |
| `assert_canonical` | 493-501 | `IsCanonical128` |
| `exponent_tables` | 652-667 | `ExpTables`: `E(2^j)` and `g^(2^j)`, `j < 34` |
| `g_power_of_word` | 670-683 | `v = E(n)`, `n < 64`, returns `g^n` |
| `verify_log2_ceil` | 686-720 | the bits of `W < 2^34`, returns `g^max(floor, log2Ceil W)` (V:661) and `g^W` |
| `log2_ceil_in_the_exponent` | 723-731 | the same from `g^N` |
| `decode_query_bits` | 734-778 | one sample's chunks of `sampleQueriesAux` (V:1670), and pointers to their bits |
| `grind_check` | 781-807 | `powOk` (V:427): the low `bits` bits of the first limb are zero |

The range checks (`verify_log2_ceil`) are stated on a memory image of at most `2^32` words
(`rangeCheck_iff`), the tables read being present (`ExpTables`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `assert_canonical` (G:493-501, TRIAGE #2) -/

/-- **`assert_canonical(word)`**: the word has no `y²` term; it returns `0`. -/
def MeaningAssertCanonical : List E → List E → Prop
  | [w], rets => IsCanonical128 w ∧ rets = [0]
  | _, _ => False

/-- `assert_canonical`'s core IR is its meaning. -/
def assert_canonical_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "assert_canonical" args rets ↔ MeaningAssertCanonical args rets

/-! ## `exponent_tables` (G:652-667, TRIAGE #16) -/

/-- `SIZE_BITS`: the exponent tables' length. -/
abbrev sizeBits : ℕ := 34

/-- The two exponent tables at `p`, `q`: `p[g^j] = E(2^j)`, `q[g^j] = g^(2^j)`, `j < 34`. -/
def ExpTables (rd : Reader) (p q : E) : Prop :=
  ∀ j < sizeBits, LoadHolds rd p j (eOfNat (2 ^ j)) ∧ LoadHolds rd q j (gen ^ 2 ^ j)

/-- **`exponent_tables()`**: it returns two pointers holding the exponent tables. -/
def MeaningExponentTables (rd : Reader) : List E → List E → Prop
  | [], [p, q] => ExpTables rd p q
  | _, _ => False

/-- `exponent_tables`' core IR is its meaning. -/
def exponent_tables_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "exponent_tables" args rets ↔ MeaningExponentTables rd args rets

/-! ## `g_power_of_word` (G:670-683, TRIAGE #17) -/

/-- **`g_power_of_word(value)`**: the value is the integer `n < 2^6` (`E(n)`), and the function
returns `g^n`. -/
def MeaningGPowerOfWord : List E → List E → Prop
  | [v], rets => ∃ n < 2 ^ 6, v = eOfNat n ∧ rets = [gen ^ n]
  | _, _ => False

/-- `g_power_of_word`'s core IR is its meaning. -/
def g_power_of_word_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "g_power_of_word" args rets ↔ MeaningGPowerOfWord args rets

/-! ## `verify_log2_ceil`, `log2_ceil_in_the_exponent` (G:686-731, TRIAGE #18, #19) -/

/-- **`verify_log2_ceil(bits, g_logs_pow2, g_squares, floor, 34)`**: the 34 words at `bits` are
the bits of `W < 2^34`, a heap run holds the prefix sums `E(W mod 2^j)`, the floored log
`max floor (log2Ceil W)` (V:661) is below 34, and the function returns its g-power and `g^W`. -/
def MeaningVerifyLog2Ceil (fl : ℕ) (rd : Reader) : List E → List E → Prop
  | [bits, _, _], rets =>
      ∃ W < 2 ^ 34, (∀ j < 34, LoadHolds rd bits j (bitE (W.testBit j))) ∧
        max fl (log2Ceil W) < 34 ∧ (∃ ps, ∀ j ≤ 34, LoadHolds rd ps j (eOfNat (W % 2 ^ j))) ∧
        rets = [gen ^ max fl (log2Ceil W), gen ^ W]
  | _, _ => False

/-- `verify_log2_ceil__L{fl}_L34`'s core IR is its meaning, on a memory image of `2^κ` words,
`6 ≤ κ ≤ 32`, holding the exponent tables. -/
def verify_log2_ceil_Spec (name : String) (fl : ℕ) : Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → 6 ≤ κ → ∀ (L : MemImage κ) (bits lp sq : E), ExpTables L.read lp sq →
    ∀ rets : List E, coreProgram.Rel L.read name [bits, lp, sq] rets ↔
      MeaningVerifyLog2Ceil fl L.read [bits, lp, sq] rets

/-- **`log2_ceil_in_the_exponent(g^N, g_logs_pow2, g_squares, floor, 34)`**: `g^N` for
`N < 2^34` (its bits hinted into a heap run and checked by `verify_log2_ceil`), the floored log
below 34, and the function returns `g^max floor (log2Ceil N)`. -/
def MeaningLog2CeilExp (fl : ℕ) (rd : Reader) : List E → List E → Prop
  | [gN, _, _], rets =>
      ∃ N < 2 ^ 34, gN = gen ^ N ∧ max fl (log2Ceil N) < 34 ∧
        (∃ bp, ∀ j < 34, LoadHolds rd bp j (bitE (N.testBit j))) ∧
        (∃ ps, ∀ j ≤ 34, LoadHolds rd ps j (eOfNat (N % 2 ^ j))) ∧
        rets = [gen ^ max fl (log2Ceil N)]
  | _, _ => False

/-- `log2_ceil_in_the_exponent__L{fl}_L34`'s core IR is its meaning, as for
`verify_log2_ceil_Spec`. -/
def log2_ceil_in_the_exponent_Spec (name : String) (fl : ℕ) : Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → 6 ≤ κ → ∀ (L : MemImage κ) (gN lp sq : E), ExpTables L.read lp sq →
    ∀ rets : List E, coreProgram.Rel L.read name [gN, lp, sq] rets ↔
      MeaningLog2CeilExp fl L.read [gN, lp, sq] rets

/-- The deployed specializations: floors `0` and `15`, 34 bits. -/
def log2_Spec : Prop :=
  verify_log2_ceil_Spec "verify_log2_ceil__L0_L34" 0 ∧
    verify_log2_ceil_Spec "verify_log2_ceil__L15_L34" 15 ∧
    log2_ceil_in_the_exponent_Spec "log2_ceil_in_the_exponent__L0_L34" 0 ∧
    log2_ceil_in_the_exponent_Spec "log2_ceil_in_the_exponent__L15_L34" 15

/-! ## `decode_query_bits` (G:734-778, TRIAGE #20) -/

/-- `p` names a frame run holding the 192 bits of `W`: every readable word at `p·g^k`, `k < 192`,
is bit `k` (`addr(bits)`). -/
def FrameBits192 (rd : Reader) (p : E) (W : ℕ) : Prop :=
  IsInK p ∧ ∀ k < 192, ∀ w, rd (p.limb 0 * Parameters.gpow k) = some w → w = bitE (W.testBit k)

/-- **`decode_query_bits(word, positions, bit_ptrs, d)`**: the frame run `p` of the word's 192
bits, and for each group `j < 192 / d` the position `j`, the word's `d` bits from `j·d` (one chunk
of `sampleQueriesAux`, V:1670, `bits = eToNat word`), and the pointer `j`, `p·g^(j·d)`, to its
bits (the Merkle direction bits). -/
def MeaningDecodeQueryBits (d : ℕ) (rd : Reader) : List E → List E → Prop
  | [w, pos, ptrs], rets => rets = [] ∧ ∃ p, FrameBits192 rd p (eToNat w) ∧
      ∀ j < 192 / d, LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * d)) % 2 ^ d)) ∧
        LoadHolds rd ptrs j (p * gen ^ (j * d))
  | _, _ => False

/-- `decode_query_bits__L{d}`'s core IR is its meaning. -/
def decode_query_bits_Spec (name : String) (d : ℕ) : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd name args rets ↔ MeaningDecodeQueryBits d rd args rets

/-- The deployed depths, `14 .. 26`, by name (a name built by `++ toString` does not reduce in a
`module`'s kernel). -/
def decodeQueryBitsNames : List (String × ℕ) :=
  (List.range 13).map fun i ↦
    (["decode_query_bits__L14", "decode_query_bits__L15", "decode_query_bits__L16",
      "decode_query_bits__L17", "decode_query_bits__L18", "decode_query_bits__L19",
      "decode_query_bits__L20", "decode_query_bits__L21", "decode_query_bits__L22",
      "decode_query_bits__L23", "decode_query_bits__L24", "decode_query_bits__L25",
      "decode_query_bits__L26"].getD i "", 14 + i)

/-- Every deployed depth. -/
def decode_query_bits_all_Spec : Prop :=
  ∀ p ∈ decodeQueryBitsNames, decode_query_bits_Spec p.1 p.2

/-! ## `grind_check` (G:781-807, TRIAGE #21) -/

/-- **`grind_check(word, bits)`** (`bits > 0`): the word, the first cell of the permutation the
nonce's challenge comes from, is canonical and the low `bits` bits of its first limb are zero:
`powOk bits` (V:427) of a challenge whose first limb is the word's (`challengeOf_limb0`). -/
def MeaningGrindCheck (bits : ℕ) : List E → List E → Prop
  | [w], rets => rets = [] ∧ IsCanonical128 w ∧ (w.limb 0).lane.toNat % 2 ^ bits = 0
  | _, _ => False

/-- `grind_check__L17`'s core IR is its meaning (`Whir.queryGrindingBits = 17`). -/
def grind_check_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "grind_check__L17" args rets ↔ MeaningGrindCheck 17 args rets

end
end LeanVM.Guest.B1
