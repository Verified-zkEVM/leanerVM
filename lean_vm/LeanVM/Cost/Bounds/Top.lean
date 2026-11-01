module

public import LeanVM.Cost.Bounds.Assembly
public import LeanVM.Cost.Bounds.DecoderShapes
public import LeanVM.Cost.Extractor.Top
import all Statement.LeanIsa
import all Statement.Extractor
import all LeanVM.Protocol.Extraction.Fast.Compiled
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# Bounds: the compiled extractor

`extractorC` (`Cost/Extractor/Top.lean`) is `extractorTop`, point-free: the bytecode's words
(`bytecodeWordsC`), the replay (`afterRootLiteC`), then `Option.bind` with `afterRootStageC`: the
first root, then `stageTC`: the committed leaves (`leavesOfC`), then `runFromLeavesC`: the fast
path's stacks (`fastOfC`), and `runBothC`: the runner's tables, a run per fast stack, else the
decoder's stacks (`decOfC`) and a run per decoded stack. Bounded from their price equations:

* the committed leaves on the chain: `takeN_cost`, `dropN_cost`, `bytesWordC_cost` (`310`),
  `bytesLanesC_cost` (`460` per word), `leafOfWithC_cost`, `bytesDigestC_cost` (`7800`: its four
  words each through `bytesLanes 4`), `subtreeLeavesWithC_cost` (by doubling), a lookup in the
  transcript's index `preimageLookup_cost` (`D·(17 + 192·(D + 2)) + 40`, its keys `PreKey`:
  `transcriptIndex_keys`), **`leavesOfC_cost`** (`transcriptBound` and `leavesBoundC`);
* the bytecode's words: **`bytecodeWordsC_cost`** (`wordsBound ℓ = 4700·2^ℓ + 1100`);
* **`fastOfC_cost`** (`fastBound`), **`decOfC_cost`** (`decodeStacksDistinctC_cost_worst`, at every
  admissible shape: `1752·2^26 + decoderWorst`), **`runBothC_cost`**, **`runFromLeavesC_cost`**,
  **`stageTC_cost`** (`stageBound`), **`afterRootStageC_cost`**;
* **`extractorC_cost`**: on every input of fewer than `2^61 − 2` permutation queries, at most
  `extractorPrice μ R κ ℓ N` at the shape `afterRootLite` announces (`replayPrice ℓ` if it fails);
* **`extractorBudgetAt`** (the Phase 4a draft's form: program, layout, rate, queries) and
  **`extractorC_within`**: the price and the entry's `9` within it wherever `afterRoot` announces a
  shape (`hcost` of `extractorTop_output`);
* **`extractorPrice_28_4`**: at `(28, 4)`, `κ = ℓ = 32`, at most `2^40` queries:
  `263761295154143991351709577217781164 ≈ 2^117.67`, the decoder (`decoderWorst ≈ 2^117.67`) all
  but `≈ 2^71.79` of it (the `1 + 2^18` runs `≈ 2^71.77`, the transcript's index `≈ 2^65.44`).

The `includes` between the top functions' lists of about `500` bodies takes seconds each: those
are lemmas of their own (`includes_stageTC`, …), each with a raised heartbeat budget.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

public section

attribute [local instance] lexOrd

variable (P : LeanVM.Cost.Program)

/-! ## Lists on bytes -/

/-- `List.take n` (`take.c231`): at most `19·n + 6`, whatever the list. -/
theorem takeN_cost (hP : Includes P Auto.List.take.c231.costDeps) {α : Type} [Enc α] :
    ∀ (n : ℕ) (xs : List α), n < 2 ^ 64 →
      machineCost P Auto.List.take.c231.costIdx [enc n, enc xs] ≤ 19 * n + 6 := by
  intro n
  induction n with
  | zero => intro xs _; rw [Auto.List.take.c231.costEq P hP]; simp [limbs_of_lt]
  | succ k ih =>
    intro xs hk
    rw [Auto.List.take.c231.costEq P hP, limbs_of_lt hk]
    cases xs with
    | nil => dsimp only; omega
    | cons x xs => have := ih xs (by omega); dsimp only; omega

/-- `List.drop n` (`drop.c232`): at most `15·n + 6`, whatever the list. -/
theorem dropN_cost (hP : Includes P Auto.List.drop.c232.costDeps) {α : Type} [Enc α] :
    ∀ (n : ℕ) (xs : List α), n < 2 ^ 64 →
      machineCost P Auto.List.drop.c232.costIdx [enc n, enc xs] ≤ 15 * n + 6 := by
  intro n
  induction n with
  | zero => intro xs _; rw [Auto.List.drop.c232.costEq P hP]; simp [limbs_of_lt]
  | succ k ih =>
    intro xs hk
    rw [Auto.List.drop.c232.costEq P hP, limbs_of_lt hk]
    cases xs with
    | nil => dsimp only; omega
    | cons x xs => have := ih xs (by omega); dsimp only; omega

/-- `List.foldr` (`foldr.c86`), the closure's price bounded on the suffixes: `9` per element and
the closure's price, `3` at the end. -/
theorem foldrSuffix_cost (hP : Includes P Auto.List.foldr.c86.costDeps) {α β : Type} [Enc α]
    [Enc β] (f : α → β → β) (fVal : Val)
    (hf : ∀ a b, RunsApp P fVal [enc a, enc b] (enc (f a b))) (B : ℕ) (init : β) :
    ∀ l : List α, (∀ x tl, x :: tl <:+ l → appCost P fVal [enc x, enc (tl.foldr f init)] ≤ B) →
      machineCost P Auto.List.foldr.c86.costIdx [fVal, enc init, enc l] ≤ (B + 9) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.foldr.c86.costEq_nil P hP f fVal hf]; omega
  | cons x l ih =>
    intro hB
    rw [Auto.List.foldr.c86.costEq_cons P hP f fVal hf]
    have h1 := ih fun y tl h ↦ hB y tl (h.trans (List.suffix_cons x l))
    have h2 := hB x l List.suffix_rfl
    simp only [List.length_cons]
    nlinarith

theorem foldr_bytes_lt' (l : List UInt8) :
    l.foldr (fun x acc ↦ x.toNat + 256 * acc) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have := x.toNat_lt
    simp only [List.foldr_cons, List.length_cons, pow_succ]
    nlinarith

/-- **A word of bytes** (`bytesWord.c512`): at most `310`. -/
theorem bytesWordC_cost (hP : Includes P Auto.LeanVM.Extraction.bytesWord.c512.costDeps)
    (b : List UInt8) :
    machineCost P Auto.LeanVM.Extraction.bytesWord.c512.costIdx [enc b] ≤ 310 := by
  rw [Auto.LeanVM.Extraction.bytesWord.c512.costEq P hP]
  have ht := takeN_cost P (by includes) 8 b (by norm_num)
  have hl : (b.take 8).length ≤ 8 := List.length_take_le _ _
  have hf := foldrSuffix_cost P (by includes) _
    (.fn Auto.LeanVM.Extraction.bytesWord.c512.lam0.costIdx [])
    (fun a acc ↦ RunsApp.of_spec
      (Auto.LeanVM.Extraction.bytesWord.c512.lam0.costSpec P (by includes) a acc)) 8 0 (b.take 8)
    (fun x tl h ↦ by
      have hlen : tl.length ≤ 7 := by have := h.length_le; simp at this; omega
      have hacc := foldr_bytes_lt' tl
      have : 256 ^ tl.length ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) hlen
      have hx := x.toNat_lt
      rw [appCost_fn, List.nil_append,
        Auto.LeanVM.Extraction.bytesWord.c512.lam0.costEq P (by includes),
        limbs_of_lt (by omega), limbs_of_lt (by omega), limbs_of_lt (by omega)]
      simp)
  nlinarith

/-- **The first `n` words of bytes** (`bytesLanes.c511`): at most `460·n + 6`. -/
theorem bytesLanesC_cost (hP : Includes P Auto.LeanVM.Extraction.bytesLanes.c511.costDeps) :
    ∀ (n : ℕ) (b : List UInt8), n < 2 ^ 64 →
      machineCost P Auto.LeanVM.Extraction.bytesLanes.c511.costIdx [enc n, enc b] ≤ 460 * n + 6 := by
  intro n
  induction n with
  | zero => intro b _; rw [Auto.LeanVM.Extraction.bytesLanes.c511.costEq P hP]; simp [limbs_of_lt]
  | succ k ih =>
    intro b hk
    rw [Auto.LeanVM.Extraction.bytesLanes.c511.costEq P hP, limbs_of_lt hk]
    have := ih (b.drop 8) (by omega)
    have := bytesWordC_cost P (by includes) b
    have := dropN_cost P (by includes) 8 b (by norm_num)
    dsimp only
    omega

/-- **A leaf** (`leafOfWith.c509`): at most `L + 480·w + 30`, `L` the lookup's price. -/
theorem leafOfWithC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.leafOfWith.c509.costDeps)
    (pre : LeanVM.Protocol.Digest → ℕ → Option (List UInt8)) (preVal : Val)
    (hpre : ∀ d n, RunsApp P preVal [enc d, enc n] (enc (pre d n))) (L : ℕ)
    (hL : ∀ (d : LeanVM.Protocol.Digest) (n : ℕ), n < 2 ^ 64 → appCost P preVal [enc d, enc n] ≤ L)
    (w : ℕ) (hw : w < 2 ^ 61) (d : LeanVM.Protocol.Digest) :
    machineCost P Auto.LeanVM.Extraction.Fast.leafOfWith.c509.costIdx [preVal, enc w, enc d] ≤
      L + 480 * w + 30 := by
  rw [Auto.LeanVM.Extraction.Fast.leafOfWith.c509.costEq P hP pre preVal hpre,
    limbs_of_lt (by omega : w < 2 ^ 64)]
  have := hL d (8 * w) (by omega)
  have := replicate_cost P (by includes) (0 : K) w (by omega)
  generalize pre d (8 * w) = o
  cases o with
  | none => dsimp only; omega
  | some val =>
    have := bytesLanesC_cost P (by includes) w val (by omega)
    have := map_cost P (by includes) _
      (.fn Auto.LeanVM.Extraction.Fast.leafOfWith.c509.lam0.costIdx [])
      (fun a ↦ RunsApp.of_spec
        (Auto.LeanVM.Extraction.Fast.leafOfWith.c509.lam0.costSpec P (by includes) a)) 1
      (LeanVM.Extraction.bytesLanes w val)
      (fun a _ ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Extraction.Fast.leafOfWith.c509.lam0.costEq P (by includes)])
    rw [bytesLanes_length] at this
    dsimp only
    omega

/-- **A digest of bytes** (`bytesDigest.c514`, its four words each through `bytesLanes 4`): at
most `7800`. -/
theorem bytesDigestC_cost (hP : Includes P Auto.LeanVM.Extraction.bytesDigest.c514.costDeps)
    (b : List UInt8) :
    machineCost P Auto.LeanVM.Extraction.bytesDigest.c514.costIdx [enc b] ≤ 7800 := by
  rw [Auto.LeanVM.Extraction.bytesDigest.c514.costEq P hP]
  have hof := ofFnFrom_cost P (by includes) (n := 4) (by norm_num) _
    (.fn Auto.LeanVM.Extraction.bytesDigest.c514.lam0.costIdx [enc b])
    (fun i ↦ RunsApp.of_spec
      (Auto.LeanVM.Extraction.bytesDigest.c514.lam0.costSpec P (by includes) b i)) 1920
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.LeanVM.Extraction.bytesDigest.c514.lam0.costEq P (by includes)]
      have := bytesLanesC_cost P (by includes) 4 b (by norm_num)
      have := getD_cost P (by includes) (LeanVM.Extraction.bytesLanes 4 b) i (by omega) 0
      rw [bytesLanes_length] at this
      omega) 0 (by norm_num)
  rw [ofFnFrom_length]
  omega

/-- **The subtree's leaves** (`subtreeLeavesWith.c508`): with `T` its price,
`T + a ≤ 2^h·(a + b + 8·h)`, `a = L + 17·w + 33000` (an inner node) and `b = L + 480·w + 45` (a
leaf), `L` the lookup's price. -/
theorem subtreeLeavesWithC_cost
    (hP : Includes P Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c508.costDeps)
    (pre : LeanVM.Protocol.Digest → ℕ → Option (List UInt8)) (preVal : Val)
    (hpre : ∀ d n, RunsApp P preVal [enc d, enc n] (enc (pre d n))) (L : ℕ)
    (hL : ∀ (d : LeanVM.Protocol.Digest) (n : ℕ), n < 2 ^ 64 → appCost P preVal [enc d, enc n] ≤ L)
    (w : ℕ) (hw : w < 2 ^ 61) :
    ∀ (h : ℕ) (d : LeanVM.Protocol.Digest),
      machineCost P Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c508.costIdx
          [preVal, enc w, enc h, enc d] + (L + 17 * w + 33000) ≤
        2 ^ h * ((L + 17 * w + 33000) + (L + 480 * w + 45) + 8 * h) := by
  have hleaf := leafOfWithC_cost P (by includes) pre preVal hpre L hL w hw
  have hrep := replicate_cost P (by includes) (0 : K) w (by omega)
  have hdig := fun (b : List UInt8) ↦ bytesDigestC_cost P (by includes) b
  have hd32 := fun (b : List UInt8) ↦ dropN_cost P (by includes) 32 b (by norm_num)
  apply le_of_doubling (fun (h : ℕ) (d : LeanVM.Protocol.Digest) ↦
    machineCost P Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c508.costIdx
      [preVal, enc w, enc h, enc d])
  · intro d
    rw [Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c508.costEq_zero P hP pre preVal hpre]
    have := hleaf d
    omega
  · intro k d
    rw [Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c508.costEq_succ P hP pre preVal hpre]
    have := hL d 64 (by norm_num)
    have hk1 := Nat.lt_two_pow_self (n := k + 1)
    have hk2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hsh : limbs (1 <<< (k + 1)) ≤ 2 ^ (k + 1) + 1 := by
      rw [Nat.shiftLeft_eq, one_mul]; exact limbs_le_add_one _
    have := limbs_le_add_one (k + 1)
    have := limbs_le_add_one k
    simp only [subtreeLeavesWith_size]
    generalize pre d 64 = o
    cases o with
    | none =>
      refine ⟨d, d, ?_⟩
      dsimp only
      omega
    | some val =>
      refine ⟨(splitNode val).1, (splitNode val).2, ?_⟩
      have := hdig val
      have := hdig (val.drop 32)
      have := hd32 val
      dsimp only
      omega

/-! ## The committed leaves -/

/-- The transcript's index holds keys `PreKey`. -/
theorem transcriptIndex_keys (T : List (Common.PermutationQuery KeccakState × KeccakState)) (L : ℕ)
    (hL : L < 2 ^ 64) : KeysIn PreKey (transcriptIndex T L).levels := by
  rw [transcriptIndex, preimageIndex]
  have hgen : ∀ (l : List (List UInt8 × LeanVM.Protocol.Digest))
      (m : SortedMap (List UInt64 × ℕ) Hits), KeysIn PreKey m.levels →
      (∀ p ∈ l, p.1.length < 2 ^ 64) →
      KeysIn PreKey (l.foldl (fun m p ↦
        m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))) m).levels := by
    intro l
    induction l with
    | nil => intro m hm _; exact hm
    | cons x l ih =>
      intro m hm hl
      rw [List.foldl_cons]
      exact ih _ (keysIn_insert hm (preKey_hitKey x (hl x (by simp))) _)
        (fun p hp ↦ hl p (by simp [hp]))
  refine hgen _ _ (fun _ h ↦ by simp [SortedMap.empty] at h) (fun p hp ↦ ?_)
  obtain ⟨e, he, h⟩ := List.mem_map.1 (mem_answerPairs_fst hp)
  rw [← h]
  have := keccakEvaluationsFast_mem_length_le he
  omega

/-- **A preimage lookup** in the transcript's index (`leavesOfC.lam0`, `preimageIn.c517`): a
binary search per level, at most `D·(17 + 192·(D + 2)) + 40`. -/
theorem preimageLookup_cost (hP : Includes P leavesOfC.lam0.costDeps)
    (qs : List (Common.PermutationQuery KeccakState × KeccakState)) (L D : ℕ) (hL : L < 2 ^ 64)
    (hD : D ≤ 61) (hN : qs.length + 2 ≤ 2 ^ D) (d : LeanVM.Protocol.Digest) (len : ℕ)
    (hlen : len < 2 ^ 64) :
    appCost P (.fn leavesOfC.lam0.costIdx [enc (transcriptIndex qs L)]) [enc d, enc len] ≤
      D * (17 + 192 * (D + 2)) + 40 := by
  simp only [appCost_fn, List.cons_append, List.nil_append]
  rw [leavesOfC.lam0.costEq P hP,
    Auto.LeanVM.Extraction.Fast.preimageIn.c517.costEq P (by includes)]
  obtain ⟨hg, hw⟩ := transcriptIndex_bounds qs L
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg (D := D)
    (lt_of_le_of_lt hw (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hN))
  have h62 : 2 ^ D < 2 ^ 62 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hget := getPre_cost P (by includes) (transcriptIndex qs L) (2 ^ D) h62
    (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) (transcriptIndex_keys qs L hL)
    (d.toList, len) ⟨by simp, hlen⟩
  rw [Nat.log2_two_pow] at hget
  have hlv : (transcriptIndex qs L).levels.length * (17 + 192 * (D + 2)) ≤
      D * (17 + 192 * (D + 2)) := Nat.mul_le_mul_right _ hlev
  simp only [Vector.size_toArray]
  generalize (transcriptIndex qs L).get? (d.toList, len) = o1
  generalize (transcriptIndex qs L).getD (d.toList, len) Hits.none = o2
  cases o1 <;> cases o2 <;> dsimp only <;> omega

/-- The committed leaves' bound: a tree of height `h`, leaves of `64` words, a lookup's `D` levels. -/
@[expose] def leavesBoundC (D h : ℕ) : ℕ :=
  2 ^ h * (2 * (D * (17 + 192 * (D + 2)) + 40) + 64853 + 8 * h)

/-- **The committed leaves** (`leavesOfC`, width `64`): the transcript's index, then the subtree. -/
theorem leavesOfC_cost (hP : Includes P leavesOfC.costDeps)
    (qs : List (Common.PermutationQuery KeccakState × KeccakState)) (D : ℕ) (hD : D ≤ 61)
    (hN : qs.length + 2 ≤ 2 ^ D) (h : ℕ) (root : LeanVM.Protocol.Digest) :
    machineCost P leavesOfC.costIdx [enc qs, enc 64, enc h, enc root] ≤
      20 + transcriptBound D 512 qs.length + leavesBoundC D h := by
  rw [leavesOfC.costEq P hP]
  rw [show max 64 (8 * 64) = 512 by norm_num]
  have hT := transcriptIndex_cost P (by includes) D 512 hD (by norm_num) qs hN
  have hS := subtreeLeavesWithC_cost P (by includes) _
    (.fn leavesOfC.lam0.costIdx [enc (transcriptIndex qs 512)])
    (fun d n ↦ RunsApp.of_spec (leavesOfC.lam0.costSpec P (by includes) _ d n))
    (D * (17 + 192 * (D + 2)) + 40)
    (fun d n hn ↦ preimageLookup_cost P (by includes) qs 512 D (by norm_num) hD hN d n hn)
    64 (by norm_num) h root
  rw [limbs_of_lt (by norm_num : (64 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : 8 * 64 < 2 ^ 64)]
  have e : D * (17 + 192 * (D + 2)) + 40 + 17 * 64 + 33000 +
      (D * (17 + 192 * (D + 2)) + 40 + 480 * 64 + 45) + 8 * h =
      2 * (D * (17 + 192 * (D + 2)) + 40) + 64853 + 8 * h := by ring
  rw [e] at hS
  unfold transcriptBound leavesBoundC
  simp only [show (64 : ℕ) ≤ 8 * 64 from by norm_num, ↓reduceIte]
  omega

/-! ## The bytecode's words -/

/-- An instruction's entry (`entry.c498`): at most `120`. -/
theorem entryC_cost (hP : Includes P Auto.LeanVM.Arithmetization.entry.c498.costDeps) (i : Instr) :
    machineCost P Auto.LeanVM.Arithmetization.entry.c498.costIdx [enc i] ≤ 120 := by
  rw [Auto.LeanVM.Arithmetization.entry.c498.costEq P hP]
  cases i with
  | deref o1 o2 o3 mode =>
    dsimp only
    rw [Auto.LeanVM.Arithmetization.derefFlags.c499.costEq P (by includes)]
    cases mode <;> dsimp only <;> omega
  | keccak om otail ob8 ocap oout inOdd outOdd =>
    dsimp only
    rw [Auto.Fin.ofNat.c384.costEq P (by includes), Auto.Fin.ofNat.c384.costEq P (by includes),
      Auto.Fin.ofNat.c384.costEq P (by includes), Auto.Fin.ofNat.c384.costEq P (by includes),
      Auto.LeanVM.Arithmetization.flagK.c500.costEq P (by includes),
      Auto.LeanVM.Arithmetization.flagK.c500.costEq P (by includes)]
    simp only [limbs_of_lt (by norm_num : (0 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : (1 : ℕ) < 2 ^ 64),
      limbs_of_lt (by norm_num : (2 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : (3 : ℕ) < 2 ^ 64)]
    split_ifs <;> omega
  | _ => dsimp only; omega

/-- The bytecode words' bound: `16·2^ℓ` words. -/
@[expose] def wordsBound (ℓ : ℕ) : ℕ := 4700 * 2 ^ ℓ + 1100

/-- **The bytecode's words** (`bytecodeWordsC`): at most `4700·2^ℓ + 1100`. -/
theorem bytecodeWordsC_cost (hP : Includes P bytecodeWordsC.costDeps) (prog : Semantics.Program) :
    machineCost P bytecodeWordsC.costIdx [enc prog] ≤ wordsBound prog.logSize := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  have h2 : 2 ^ prog.logSize < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [bytecodeWordsC.costEq P hP]
  have h1 := finRangeFrom_cost P (by includes) 16 (by norm_num) 0 (by norm_num)
  have hin : ∀ s : Fin 16, appCost P (.fn bytecodeWordsC.lam0.costIdx [enc prog]) [enc s] ≤
      280 * 2 ^ prog.logSize + 30 := by
    intro s
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [bytecodeWordsC.lam0.costEq P (by includes), Nat.one_shiftLeft, limbs_of_lt h2,
      limbs_of_lt (lt_of_le_of_lt hls (by norm_num) : prog.logSize < 2 ^ 64)]
    have hf := finRangeFrom_cost P (by includes) (2 ^ prog.logSize) h2 0 (Nat.zero_le _)
    have hm := map_cost P (by includes) _ (.fn bytecodeWordsC.lam0.lam0.costIdx [enc prog, enc s])
      (fun i ↦ RunsApp.of_spec (bytecodeWordsC.lam0.lam0.costSpec P (by includes) prog s i)) 247
      (List.finRange (2 ^ prog.logSize)) (fun i _ ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [bytecodeWordsC.lam0.lam0.costEq P (by includes),
          Auto.LeanVM.Arithmetization.encodeSlots.c497.costEq P (by includes)]
        have := entryC_cost P (by includes) (prog.code i)
        omega)
    rw [List.length_finRange] at hm
    simp only [Nat.sub_zero] at hf
    omega
  have hm := map_cost P (by includes) _ (.fn bytecodeWordsC.lam0.costIdx [enc prog])
    (fun s ↦ RunsApp.of_spec (bytecodeWordsC.lam0.costSpec P (by includes) prog s))
    (280 * 2 ^ prog.logSize + 30) (List.finRange 16) (fun s _ ↦ hin s)
  have hfl := flatten_cost P (by includes) (2 ^ prog.logSize)
    ((List.finRange 16).map fun s ↦ (List.finRange (2 ^ prog.logSize)).map fun i ↦
      (LeanVM.Arithmetization.encodeSlots (prog.code i))[s])
    (fun l hl ↦ by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hl
      simp)
  simp only [List.length_finRange, List.length_map] at hm hfl
  unfold wordsBound
  omega

/-! ## The stacks -/

/-- **The fast path** on the committed leaves (`fastOfC`, width `64`). -/
theorem fastOfC_cost (hP : Includes P fastOfC.costDeps) (μ R : ℕ) (hμ : μ ≤ 40) (hR : R ≤ 8)
    (leaves : Array (List K)) (h : ℕ) (hh : h < 64) (hl : ∀ l ∈ leaves, l.length ≤ 64) :
    machineCost P fastOfC.costIdx [enc μ, enc R, enc leaves, enc h, enc 64] ≤
      fastBound μ R 64 24 + 10 := by
  rw [fastOfC.costEq P hP]
  have := fastStacksFast_cost P (by includes) μ R hμ hR _
    (.fn fastStacksOfLeavesC.lam0.costIdx [enc leaves, enc h, enc 64])
    (fun a ↦ RunsApp.of_spec (fastStacksOfLeavesC.lam0.costSpec P (by includes) leaves h 64 a))
    (17 * 64 + 24) 64
    (fun v hv ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [fastStacksOfLeavesC.lam0.costEq P (by includes)]
      have := leafAt_cost P (by includes) leaves h 64 v hh hv (by norm_num)
      omega)
    (fun v ↦ leafAt_length_le leaves h 64 v hl)
  unfold fastBound
  simp only [show Whir.initialFold = 6 from rfl] at this
  omega

/-- **The decoder** on the committed leaves (`decOfC`, width `64`), at every admissible shape. -/
theorem decOfC_cost (hP : Includes P decOfC.costDeps) {μ R : ℕ} (hadm : Whir.Admissible μ R)
    (leaves : Array (List K)) (h : ℕ) (hh : h < 64) (hl : ∀ l ∈ leaves, l.length ≤ 64) :
    machineCost P decOfC.costIdx [enc μ, enc R, enc leaves, enc h, enc 64] ≤
      1752 * 2 ^ 26 + Decoder.decoderWorst + 10 := by
  rw [decOfC.costEq P hP]
  have := Decoder.decodeStacksDistinctC_cost_worst P (by includes) hadm _
    (.fn fastStacksOfLeavesC.lam0.costIdx [enc leaves, enc h, enc 64])
    (fun a ↦ RunsApp.of_spec (fastStacksOfLeavesC.lam0.costSpec P (by includes) leaves h 64 a))
    (BW := 17 * 64 + 24) (Lw := 64)
    (fun v hv ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [fastStacksOfLeavesC.lam0.costEq P (by includes)]
      have := leafAt_cost P (by includes) leaves h 64 v hh hv (by norm_num)
      omega)
    (fun v ↦ leafAt_length_le leaves h 64 v hl)
  omega

/-- A stack's run on `afterRootLite`'s layouts: at most `runBound κ ℓ`. -/
theorem runWithTables_le (hP : Includes P runWithTablesC.costDeps) (prog : Semantics.Program)
    (input : PublicInput) (L : LayoutLite) (hf : LayoutFacts L) (q : Vector K (2 ^ L.stackLog)) :
    machineCost P runWithTablesC.costIdx
        [enc (runnerTables prog L), enc prog, enc input, enc L, enc q] ≤
      runBound L.logMemory prog.logSize := by
  have h2 := runWithTables_cost P hP prog input L hf.logMemory_le hf.logBytecode_le
    hf.heights_le hf.heights_length hf.index_lt_word q
  have h3 := stepCapLite_le L hf.logMemory_le hf.logBytecode_le hf.heights_le hf.heights_length
  have h4 := Nat.mul_le_mul_left (stepPrice L.logMemory prog.logSize + 45) h3
  unfold runBound
  omega

/-- **The candidate runs** (`runBothC`): the tables, at most one fast stack, then the decoder's
stacks (`S` their price, at most `2^18` of them). -/
theorem runBothC_cost (hP : Includes P runBothC.costDeps) (prog : Semantics.Program)
    (input : PublicInput) (L : LayoutLite) (hf : LayoutFacts L)
    (fastSts : List (Vector K (2 ^ L.stackLog))) (hfs : fastSts.length ≤ 1)
    (slow : Unit → List (Vector K (2 ^ L.stackLog))) (slowVal : Val)
    (hslow : ∀ a, RunsApp P slowVal [enc a] (enc (slow a))) (S : ℕ)
    (hS : appCost P slowVal [enc ()] ≤ S) (hsl : (slow ()).length ≤ 2 ^ 18) :
    machineCost P runBothC.costIdx [enc prog, enc input, enc L, enc fastSts, slowVal] ≤
      tablesBound L.logMemory prog.logSize + (runBound L.logMemory prog.logSize + 15) * (2 ^ 18 + 1) +
        S + 60 := by
  rw [runBothC.costEq P hP prog input L fastSts slow slowVal hslow]
  have hT : machineCost P runnerTablesC.costIdx [enc prog, enc L] ≤
      tablesBound L.logMemory prog.logSize :=
    runnerTables_cost P (by includes) prog L hf.logMemory_le hf.logBytecode_le hf.heights_le
      hf.heights_length
  have hspec : ∀ q : Vector K (2 ^ L.stackLog), RunsApp P (.fn runBothC.lam0.lam0.costIdx
      [enc prog, enc input, enc L, enc (runnerTables prog L)]) [enc q]
      (enc (runWithTables (runnerTables prog L) prog input L q)) := fun q ↦ RunsApp.of_spec
    (us := [enc prog, enc input, enc L, enc (runnerTables prog L)]) (vs := [enc q])
    (runBothC.lam0.lam0.costSpec P (by includes) prog input L (runnerTables prog L) q)
  have hrun : ∀ q : Vector K (2 ^ L.stackLog), appCost P (.fn runBothC.lam0.lam0.costIdx
      [enc prog, enc input, enc L, enc (runnerTables prog L)]) [enc q] ≤
      runBound L.logMemory prog.logSize + 6 := by
    intro q
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [runBothC.lam0.lam0.costEq P (by includes)]
    have := runWithTables_le P (by includes) prog input L hf q
    omega
  have hF1 := findSome_cost P (by includes) _ _ hspec _ fastSts (fun q _ ↦ hrun q)
  have hF2 := findSome_cost P (by includes) _ _ hspec _ (slow ()) (fun q _ ↦ hrun q)
  have hm1 := Nat.mul_le_mul_left (runBound L.logMemory prog.logSize + 6 + 9) hfs
  have hm2 := Nat.mul_le_mul_left (runBound L.logMemory prog.logSize + 6 + 9) hsl
  rw [Auto.Option.orElse.c502.costEq P (by includes) _
    (fun _ ↦ (slow ()).findSome? (runWithTables (runnerTables prog L) prog input L))
    (.fn runBothC.lam0.costIdx [enc prog, enc input, enc L, slowVal, enc (runnerTables prog L)])
    (fun x ↦ RunsApp.of_spec (runBothC.lam0.costSpec P (by includes) prog input L slow slowVal hslow
      (runnerTables prog L) x))]
  have hlam : appCost P (.fn runBothC.lam0.costIdx
      [enc prog, enc input, enc L, slowVal, enc (runnerTables prog L)]) [enc ()] ≤
      S + (runBound L.logMemory prog.logSize + 6 + 9) * 2 ^ 18 + 16 := by
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [runBothC.lam0.costEq P (by includes) prog input L slow slowVal hslow]
    omega
  generalize List.findSome? (runWithTables (runnerTables prog L) prog input L) fastSts = o
  cases o <;> dsimp only <;> nlinarith

/-! ## The stages -/

/-- The decoder's part of a stage: its stacks, at every admissible shape. -/
@[expose] def decoderPart : ℕ := 1752 * 2 ^ 26 + Decoder.decoderWorst + 17

/-- **The candidate runs from the committed leaves** (`runFromLeavesC`, width `64`). -/
theorem runFromLeavesC_cost (hP : Includes P runFromLeavesC.costDeps) (prog : Semantics.Program)
    (input : PublicInput) (L : LayoutLite) (R : ℕ) (hf : LayoutFacts L)
    (hadm : Whir.Admissible L.stackLog R) (leaves : Array (List K)) (h : ℕ) (hh : h < 64)
    (hl : ∀ l ∈ leaves, l.length ≤ 64) :
    machineCost P runFromLeavesC.costIdx [enc prog, enc input, enc L, enc R, enc leaves, enc h, enc 64] ≤
      fastBound L.stackLog R 64 24 + tablesBound L.logMemory prog.logSize +
        (runBound L.logMemory prog.logSize + 15) * (2 ^ 18 + 1) + decoderPart + 92 := by
  have hadm' := hadm
  obtain ⟨-, h2, -, h4⟩ := hadm'
  simp only [Whir.maxLogStack, Whir.maxLogInvRate] at h2 h4
  rw [runFromLeavesC.costEq P hP]
  have hF := fastOfC_cost P (by includes) L.stackLog R (by omega) (by omega) leaves h hh hl
  have hslow : ∀ x : Unit, RunsApp P (.fn runFromLeavesC.lam0.costIdx
      [enc L, enc R, enc leaves, enc h, enc 64]) [enc x]
      (enc ((fun _ : Unit ↦ decOf L.stackLog R leaves h 64) x)) := fun x ↦
    RunsApp.of_spec (runFromLeavesC.lam0.costSpec P (by includes) L R leaves h 64 x)
  have hB := runBothC_cost P (by includes) prog input L hf (fastOf L.stackLog R leaves h 64)
    (fastStacksFast_length_le _ _ _) (fun _ ↦ decOf L.stackLog R leaves h 64) _ hslow
    (1752 * 2 ^ 26 + Decoder.decoderWorst + 17)
    (by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [runFromLeavesC.lam0.costEq P (by includes)]
      have := decOfC_cost P (by includes) hadm leaves h hh hl
      omega)
    (decodeStacksDistinct_length_le_johnson hadm _)
  unfold decoderPart
  omega

/-- A stage's bound: the committed leaves of height `h` and the candidate runs. -/
@[expose] def stageBound (μ R κ ℓ D N h : ℕ) : ℕ :=
  transcriptBound D 512 N + leavesBoundC D h + fastBound μ R 64 24 + tablesBound κ ℓ +
    (runBound κ ℓ + 15) * (2 ^ 18 + 1) + decoderPart + 133

/-- **A stage** (`stageTC`) at the root `afterRootLite` returns: the committed leaves, the runs. -/
theorem stageTC_cost (hP : Includes P stageTC.costDeps) (prog : Semantics.Program)
    (input : PublicInput) (qs : List (Common.PermutationQuery KeccakState × KeccakState))
    (D : ℕ) (hD : D ≤ 61) (hN : qs.length + 2 ≤ 2 ^ D) {bytecode : List K} {π : Proof}
    {L : LayoutLite} {R : ℕ} {st : ProgState} (har : afterRootLite bytecode π = some ((L, R), st))
    (root : LeanVM.Protocol.Digest) :
    machineCost P stageTC.costIdx [enc prog, enc input, enc L, enc R, enc qs,
        enc (root, L.stackLog - 6 + R, 64)] ≤
      stageBound L.stackLog R L.logMemory prog.logSize D qs.length (L.stackLog - 6 + R) := by
  obtain ⟨hf, hμ1, hμ2, hR1, hR2, -⟩ := afterRootLite_facts har
  have hadm := admissible_of_afterRootLite har
  rw [stageTC.costEq P hP]
  dsimp only
  have hL := leavesOfC_cost P (by includes) qs D hD hN (L.stackLog - 6 + R) root
  have hR := runFromLeavesC_cost P (by includes) prog input L R hf hadm
    (leavesOf qs 64 (L.stackLog - 6 + R) root) (L.stackLog - 6 + R) (by omega)
    (fun l hl ↦ (subtreeLeavesWith_mem_length _ _ _ _ l hl).le)
  unfold stageBound
  omega

/-! The programs' inclusions between the top functions: `includes` on their lists of about `500`
bodies (a membership proof per body) takes seconds each, so each is a lemma of its own. -/

set_option maxHeartbeats 1000000 in
theorem includes_stageTC (hP : Includes P afterRootStageC.costDeps) : Includes P stageTC.costDeps := by
  includes

set_option maxHeartbeats 1000000 in
theorem includes_afterRootStageLam (hP : Includes P afterRootStageC.costDeps) :
    Includes P afterRootStageC.lam0.costDeps := by
  includes

set_option maxHeartbeats 1000000 in
theorem includes_afterRootStageC (hP : Includes P extractorC.costDeps) :
    Includes P afterRootStageC.costDeps := by
  includes

set_option maxHeartbeats 1000000 in
theorem includes_extractorLam (hP : Includes P extractorC.costDeps) :
    Includes P extractorC.lam0.costDeps := by
  includes

set_option maxHeartbeats 1000000 in
theorem includes_afterRootLiteC (hP : Includes P extractorC.costDeps) :
    Includes P afterRootLiteC.costDeps := by
  includes

set_option maxHeartbeats 1000000 in
theorem includes_bytecodeWordsC (hP : Includes P extractorC.costDeps) :
    Includes P bytecodeWordsC.costDeps := by
  includes

set_option maxHeartbeats 1000000 in
theorem includes_bindC (hP : Includes P extractorC.costDeps) :
    Includes P Auto.Option.bind.c323.costDeps := by
  includes

/-- **After the replay** (`afterRootStageC`): the root, then the stage. -/
theorem afterRootStageC_cost (hP : Includes P afterRootStageC.costDeps) (prog : Semantics.Program)
    (input : PublicInput) (qs : List (Common.PermutationQuery KeccakState × KeccakState))
    (D : ℕ) (hD : D ≤ 61) (hN : qs.length + 2 ≤ 2 ^ D) {bytecode : List K} {π : Proof}
    {L : LayoutLite} {R : ℕ} {st : ProgState} (har : afterRootLite bytecode π = some ((L, R), st)) :
    machineCost P afterRootStageC.costIdx [enc prog, enc input, enc qs, enc ((L, R), st)] ≤
      stageBound L.stackLog R L.logMemory prog.logSize D qs.length (L.stackLog - 6 + R) + 35 := by
  obtain ⟨root, hroots⟩ := afterRootLite_roots har
  have hI := includes_afterRootStageLam P hP
  have hI2 := includes_stageTC P hP
  have hk : ∀ t : LeanVM.Protocol.Digest × ℕ × ℕ, RunsApp P
      (.fn afterRootStageC.lam0.costIdx [enc prog, enc input, enc qs, enc R, enc L]) [enc t]
      (enc (stageT prog input L R qs t)) := fun t ↦
    RunsApp.of_spec (us := [enc prog, enc input, enc qs, enc R, enc L]) (vs := [enc t])
      (afterRootStageC.lam0.costSpec P hI prog input qs R L t)
  have hb := Auto.Option.bind.c323.costEq P (by includes) st.roots.head? (stageT prog input L R qs)
    _ hk
  have hlam := afterRootStageC.lam0.costEq P hI prog input qs R L
    (root, L.stackLog - 6 + R, 64)
  have hst := stageTC_cost P hI2 prog input qs D hD hN har root
  rw [afterRootStageC.costEq P hP]
  simp only [hroots, List.head?_cons] at hb ⊢
  simp only [appCost_fn, List.cons_append, List.nil_append] at hb
  omega

/-! ## The extractor -/

/-- **The extractor's price at a shape**: the stack's log-size `μ`, the rate's `R`, the memory's
`κ`, the program's `ℓ`, `N` permutation queries (`D = log₂(N + 2) + 1`): the bytecode's words, the
replay, the root's stage (the transcript's index, the committed leaves of height `μ − 6 + R`, the
fast path, the runner's tables, at most `1 + 2^18` runs, the decoder) and the glue. -/
@[expose] def extractorPrice (μ R κ ℓ N : ℕ) : ℕ :=
  wordsBound ℓ + (144 * 2 ^ ℓ + 1004514000) +
    stageBound μ R κ ℓ (Nat.log2 (N + 2) + 1) N (μ - 6 + R) + 60

/-- The price where the replay fails: the bytecode's words and the replay. -/
@[expose] def replayPrice (ℓ : ℕ) : ℕ := wordsBound ℓ + (144 * 2 ^ ℓ + 1004514000) + 15

/-- **The compiled extractor's price** (`extractorC`), on every input of fewer than `2^61 − 2`
permutation queries: at most `extractorPrice` at the shape `afterRootLite` announces, or
`replayPrice` when the replay fails. -/
theorem extractorC_cost (hP : Includes P extractorC.costDeps) (prog : Semantics.Program)
    (input : PublicInput) (qs : List (Common.PermutationQuery KeccakState × KeccakState))
    (π : Proof) (hq : qs.length + 2 < 2 ^ 61) :
    machineCost P extractorC.costIdx [enc prog, enc input, enc qs, enc π] ≤
      match afterRootLite (bytecodeWords prog) π with
      | none => replayPrice prog.logSize
      | some ((L, R), _) => extractorPrice L.stackLog R L.logMemory prog.logSize qs.length := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  have hbc := bytecodeWords_length prog
  have hW := bytecodeWordsC_cost P (includes_bytecodeWordsC P hP) prog
  have hA := afterRootLite_cost P (includes_afterRootLiteC P hP) (bytecodeWords prog) π (by
    rw [hbc]
    have : 2 ^ prog.logSize ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hls
    omega)
  rw [hbc] at hA
  have hI0 := includes_extractorLam P hP
  have hk : ∀ r : (LayoutLite × ℕ) × ProgState, RunsApp P
      (.fn extractorC.lam0.costIdx [enc prog, enc input, enc qs]) [enc r]
      (enc (afterRootStage prog input qs r)) := fun r ↦
    RunsApp.of_spec (us := [enc prog, enc input, enc qs]) (vs := [enc r])
      (extractorC.lam0.costSpec P hI0 prog input qs r)
  rw [extractorC.costEq P hP, Auto.Option.bind.c323.costEq P (includes_bindC P hP)
    (afterRootLite (bytecodeWords prog) π) (afterRootStage prog input qs) _ hk]
  cases har : afterRootLite (bytecodeWords prog) π with
  | none =>
    show _ ≤ wordsBound prog.logSize + (144 * 2 ^ prog.logSize + 1004514000) + 15
    dsimp only
    omega
  | some r =>
    obtain ⟨⟨L, R⟩, st⟩ := r
    show _ ≤ wordsBound prog.logSize + (144 * 2 ^ prog.logSize + 1004514000) +
      stageBound L.stackLog R L.logMemory prog.logSize (Nat.log2 (qs.length + 2) + 1) qs.length
        (L.stackLog - 6 + R) + 60
    simp only [appCost_fn, List.cons_append, List.nil_append]
    have hl := extractorC.lam0.costEq P hI0 prog input qs ((L, R), st)
    have hD : Nat.log2 (qs.length + 2) + 1 ≤ 61 := by
      have := (Nat.log2_lt (n := qs.length + 2) (k := 61) (by omega)).2 hq
      omega
    have hN : qs.length + 2 ≤ 2 ^ (Nat.log2 (qs.length + 2) + 1) := Nat.le_of_lt Nat.lt_log2_self
    have hs := afterRootStageC_cost P (includes_afterRootStageC P hP) prog input qs _ hD hN har
    omega

/-! ## The efficiency statement's budget -/

/-- **The extractor's budget at a shape** (the form `extractorBudgetAt` of the Phase 4a draft
takes, `Statement/CostMachine.lean` on `wt/phase4a`): `extractorPrice` at the layout and rate the
proof announces, and the entry's `9`. -/
@[expose] def extractorBudgetAt (prog : Semantics.Program) (layout : Layout) (logInverseRate queries : ℕ) :
    ℕ :=
  extractorPrice layout.stackLog logInverseRate layout.logMemory prog.logSize queries + 9

/-- **The price within the budget** (the hypothesis `hcost` of `extractorTop_output`, on
`wt/phase4a`): wherever `afterRoot` announces a shape, the compiled extractor's price and the
entry's `9` are within `extractorBudgetAt`, for fewer than `2^61 − 2` permutation queries. -/
theorem extractorC_within (hP : Includes P extractorC.costDeps) (prog : Semantics.Program)
    (input : PublicInput) (T : Common.OracleQueryLog) (π : Proof) (layout : Layout)
    (logInverseRate : ℕ) (st : ProgState)
    (ha : afterRoot (bytecodeWords prog) π = some ((layout, logInverseRate), st))
    (hq : (permutationQueries T).length + 2 < 2 ^ 61) :
    machineCost P extractorC.costIdx [enc prog, enc input, enc (permutationQueries T), enc π] + 9 ≤
      extractorBudgetAt prog layout logInverseRate (permutationQueries T).length := by
  have h := extractorC_cost P hP prog input (permutationQueries T) π hq
  have hl : afterRootLite (bytecodeWords prog) π = some ((layoutLite layout, logInverseRate), st) := by
    rw [afterRootLite_eq, ha]; rfl
  rw [hl] at h
  unfold extractorBudgetAt
  exact Nat.add_le_add_right h 9

/-! ## At `(28, 4)` -/

theorem stageBound_mono {μ R κ ℓ D D' N N' h : ℕ} (hD : D ≤ D') (hN : N ≤ N') :
    stageBound μ R κ ℓ D N h ≤ stageBound μ R κ ℓ D' N' h := by
  unfold stageBound transcriptBound leavesBoundC replayStepBound
  gcongr

/-- **The extractor's price at `(μ, R) = (28, 4)`**, `κ = ℓ = 32`, at most `2^40` queries: at
most `263761295154143991351709577217781164 ≈ 2^117.67`, the decoder's `2^117.67` dominating. -/
theorem extractorPrice_28_4 (N : ℕ) (hN : N ≤ 2 ^ 40) :
    extractorPrice 28 4 32 32 N ≤ 263761295154143991351709577217781164 := by
  have hD : Nat.log2 (N + 2) + 1 ≤ 41 := by
    have := (Nat.log2_lt (n := N + 2) (k := 41) (by omega)).2 (by omega)
    omega
  have h := stageBound_mono (μ := 28) (R := 4) (κ := 32) (ℓ := 32) (h := 28 - 6 + 4) hD hN
  unfold extractorPrice
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left h _) _) ?_
  unfold stageBound transcriptBound leavesBoundC replayStepBound fastBound tablesBound runBound
    stepPrice decoderPart Decoder.decoderWorst wordsBound
  norm_num

end

end LeanVM.Cost.Bounds
