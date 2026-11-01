module

public import LeanVM.Cost.Bounds.FastPath
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# Bounds: the transcript's replay and its evaluations

* the byte-string helpers (`drop`, `take`, `dropWhile`, `modifyHead`, `modifyTailIdx`), the padding
  (`padBlock_cost`, `keccakPadded_cost`), `stripPad_cost` and **`keccakUnpadded_cost`**: a path's
  bytes read as a padded message, `107·|bs| + 12200`, linear (no Keccak-f: the digest is the path's
  state);
* the replay's block bytes (`blockBytes_cost`) and the cut (`cut_cost`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction
open LeanVM.Extraction.Fast LeanVM.Protocol.KeccakHash LeanVM.Semantics Common

public section

variable (P : Program)

/-! ## Byte-string helpers -/

/-- `List.drop` (`drop.c232`): `15` per position, `13` at the end. -/
theorem drop232_cost (hP : Includes P Auto.List.drop.c232.costDeps) {α : Type} [Enc α] :
    ∀ (n : ℕ) (xs : List α), n < 2 ^ 64 →
      machineCost P Auto.List.drop.c232.costIdx [enc n, enc xs] ≤ 15 * n + 13 := by
  intro n
  induction n with
  | zero => intro xs _; rw [Auto.List.drop.c232.costEq P hP]; simp
  | succ n ih =>
    intro xs hn
    rw [Auto.List.drop.c232.costEq P hP, limbs_of_lt hn]
    cases xs with
    | nil => dsimp only; omega
    | cons x xs => have := ih xs (by omega); dsimp only; omega

/-- `List.take` (`take.c231`): `19` per position, `13` at the end. -/
theorem take231_cost (hP : Includes P Auto.List.take.c231.costDeps) {α : Type} [Enc α] :
    ∀ (n : ℕ) (xs : List α), n < 2 ^ 64 →
      machineCost P Auto.List.take.c231.costIdx [enc n, enc xs] ≤ 19 * n + 13 := by
  intro n
  induction n with
  | zero => intro xs _; rw [Auto.List.take.c231.costEq P hP]; simp
  | succ n ih =>
    intro xs hn
    rw [Auto.List.take.c231.costEq P hP, limbs_of_lt hn]
    cases xs with
    | nil => dsimp only; omega
    | cons x xs => have := ih xs (by omega); dsimp only; omega

/-- `List.dropWhile` (`dropWhile.c336`): `B + 9` per element, `B + 11` at the end. -/
theorem dropWhile336_cost (hP : Includes P Auto.List.dropWhile.c336.costDeps) {α : Type} [Enc α]
    (p : α → Bool) (pVal : Val) (hp : ∀ a : α, RunsApp P pVal [enc a] (enc (p a))) (B : ℕ)
    (hB : ∀ a : α, appCost P pVal [enc a] ≤ B) :
    ∀ l : List α, machineCost P Auto.List.dropWhile.c336.costIdx [pVal, enc l] ≤
      (B + 9) * l.length + B + 11 := by
  intro l
  induction l with
  | nil => rw [Auto.List.dropWhile.c336.costEq_nil P hP p pVal hp]; omega
  | cons x l ih =>
    rw [Auto.List.dropWhile.c336.costEq_cons P hP p pVal hp]
    have := hB x
    simp only [List.length_cons]
    cases p x <;> dsimp only <;> nlinarith

/-- `List.modifyHead` (`modifyHead.c342`) with a closure of price `B`: at most `B + 9`. -/
theorem modifyHead342_cost (hP : Includes P Auto.List.modifyHead.c342.costDeps) {α : Type} [Enc α]
    (f : α → α) (fVal : Val) (hf : ∀ a : α, RunsApp P fVal [enc a] (enc (f a))) (B : ℕ)
    (hB : ∀ a : α, appCost P fVal [enc a] ≤ B) (l : List α) :
    machineCost P Auto.List.modifyHead.c342.costIdx [fVal, enc l] ≤ B + 9 := by
  rw [Auto.List.modifyHead.c342.costEq P hP f fVal hf]
  cases l with
  | nil => dsimp only; omega
  | cons x l => have := hB x; dsimp only; omega

/-- `List.modifyTailIdx.go` (`modifyTailIdx.go.c340`): `20` per position and the closure's price. -/
theorem modifyTailIdx340_cost (hP : Includes P Auto.List.modifyTailIdx.go.c340.costDeps)
    {α : Type} [Enc α] (f : List α → List α) (fVal : Val)
    (hf : ∀ a : List α, RunsApp P fVal [enc a] (enc (f a))) (B : ℕ)
    (hB : ∀ a : List α, appCost P fVal [enc a] ≤ B) :
    ∀ (n : ℕ) (l : List α), n < 2 ^ 64 →
      machineCost P Auto.List.modifyTailIdx.go.c340.costIdx [fVal, enc n, enc l] ≤ 20 * n + B + 8 := by
  intro n
  induction n with
  | zero =>
    intro l _
    rw [Auto.List.modifyTailIdx.go.c340.costEq P hP f fVal hf]
    have := hB l
    simp only [Nat.rec_zero, limbs_zero]
    omega
  | succ n ih =>
    intro l hn
    rw [Auto.List.modifyTailIdx.go.c340.costEq P hP f fVal hf, limbs_of_lt hn]
    cases l with
    | nil => dsimp only; omega
    | cons x l => have := ih l (by omega); dsimp only; omega

/-! ## The padding -/

theorem rate_eq : rate = 136 := rfl

/-- **The padded last block** (`padBlock.c339`) of at most `136` bytes: at most `12000`. -/
theorem padBlock_cost (hP : Includes P Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.costDeps)
    (rest : List UInt8) (hr : rest.length ≤ 136) :
    machineCost P Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.costIdx [enc rest] ≤ 12000 := by
  rw [Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.costEq P hP]
  have hl := listLength_cost P (by includes) rest (by omega)
  have hrep := replicate_cost P (by includes) (0 : UInt8) (rate - rest.length) (by rw [rate_eq]; omega)
  have hap := append_cost P (by includes) rest (List.replicate (rate - rest.length) 0)
  have hmh : ∀ (g : UInt8 → UInt8) (gVal : Val), (∀ a, RunsApp P gVal [enc a] (enc (g a))) →
      (∀ a, appCost P gVal [enc a] ≤ 3) → ∀ l : List UInt8,
      machineCost P Auto.List.modifyHead.c342.costIdx [gVal, enc l] ≤ 12 :=
    fun g gVal hg hB l ↦ modifyHead342_cost P (by includes) g gVal hg 3 hB l
  have h1 := modifyTailIdx340_cost P (by includes) _
    (.fn Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.lam1.costIdx [])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.lam1.costSpec P
      (by includes) a)) 15
    (fun a ↦ by
      rw [appCost_fn, List.nil_append,
        Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.lam1.costEq P (by includes)]
      have := hmh _ (.fn Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.lam1.lam0.costIdx [])
        (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.lam1.lam0.costSpec P
          (by includes) a))
        (fun a ↦ by
          rw [appCost_fn, List.nil_append,
            Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.lam1.lam0.costEq P (by includes)]) a
      omega) rest.length (rest ++ List.replicate (rate - rest.length) 0) (by omega)
  have h2 := modifyTailIdx340_cost P (by includes) _
    (.fn Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.lam0.costSpec P
      (by includes) a)) 15
    (fun a ↦ by
      rw [appCost_fn, List.nil_append,
        Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.lam0.costEq P (by includes)]
      have := hmh _ (.fn Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.lam0.lam0.costIdx [])
        (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.lam0.lam0.costSpec P
          (by includes) a))
        (fun a ↦ by
          rw [appCost_fn, List.nil_append,
            Auto.LeanVM.Protocol.KeccakHash.padBlock.c339.lam0.lam0.costEq P (by includes)]) a
      omega) (rate - 1)
    ((rest ++ List.replicate (rate - rest.length) 0).modify rest.length fun x ↦ x ^^^ padFirst)
    (by rw [rate_eq]; omega)
  rw [limbs_of_lt (by rw [rate_eq]; omega : rate < 2 ^ 64),
    limbs_of_lt (by omega : rest.length < 2 ^ 64)]
  simp only [rate_eq, max_self] at *
  omega

/-- **The Keccak padding** (`keccakPadded.c338`) of `m`: at most `65·|m| + 12100`. -/
theorem keccakPadded_cost (hP : Includes P Auto.LeanVM.keccakPadded.c338.costDeps)
    (m : List UInt8) (hm : m.length < 2 ^ 62) :
    machineCost P Auto.LeanVM.keccakPadded.c338.costIdx [enc m] ≤ 65 * m.length + 12100 := by
  rw [Auto.LeanVM.keccakPadded.c338.costEq P hP]
  have hl := listLength_cost P (by includes) m (by omega)
  have hk : rate * (m.length / rate) ≤ m.length := by rw [rate_eq]; exact Nat.mul_div_le _ _
  have ht := take231_cost P (by includes) (rate * (m.length / rate)) m (by omega)
  have hd := drop232_cost P (by includes) (rate * (m.length / rate)) m (by omega)
  have hpb := padBlock_cost P (by includes) (m.drop (rate * (m.length / rate))) (by
    rw [List.length_drop, rate_eq]
    have := Nat.mod_lt m.length (show 136 > 0 by norm_num)
    have := Nat.div_add_mod m.length 136
    omega)
  have hap := append_cost P (by includes) (m.take (rate * (m.length / rate)))
    (padBlock (m.drop (rate * (m.length / rate))))
  have htl : (m.take (rate * (m.length / rate))).length ≤ m.length := by
    rw [List.length_take]; omega
  rw [limbs_of_lt (by omega : m.length < 2 ^ 64), limbs_of_lt (by rw [rate_eq]; omega : rate < 2 ^ 64),
    limbs_of_lt (by have := Nat.div_le_self m.length rate; omega : m.length / rate < 2 ^ 64)]
  omega

theorem stripPad_length_le (bs : List UInt8) : (Common.stripPad bs).length ≤ bs.length := by
  unfold Common.stripPad
  have hr := List.length_reverse (as := bs)
  generalize bs.reverse = r at hr
  rcases r with _ | ⟨x, rest⟩
  · simp
  · simp only [List.length_cons] at hr
    split
    · rename_i h; simp only [List.cons.injEq] at h; obtain ⟨-, rfl⟩ := h; simp; omega
    · rename_i h; simp only [List.cons.injEq] at h; obtain ⟨-, rfl⟩ := h
      simp only [List.length_reverse, List.length_drop]
      have := (List.dropWhile_suffix (fun x ↦ decide (x = 0)) (l := rest)).length_le
      omega
    · simp at *

/-- `Common.stripPad` (`stripPad.c335`): at most `31·|bs| + 50`. -/
theorem stripPad_cost (hP : Includes P Auto.Common.stripPad.c335.costDeps) (bs : List UInt8)
    (hb : bs.length < 2 ^ 62) :
    machineCost P Auto.Common.stripPad.c335.costIdx [enc bs] ≤ 31 * bs.length + 50 := by
  rw [Auto.Common.stripPad.c335.costEq P hP]
  have h0 := reverseAux_cost P (by includes) bs []
  have hr := List.length_reverse (as := bs)
  generalize bs.reverse = r at hr
  rcases r with _ | ⟨x, tail⟩
  · dsimp only; omega
  · simp only [List.length_cons] at hr
    dsimp only
    have h1 := reverseAux_cost P (by includes) tail []
    have h2 := dropWhile336_cost P (by includes) _ (.fn Auto.Common.stripPad.c335.lam0.costIdx [])
      (fun a ↦ RunsApp.of_spec (Auto.Common.stripPad.c335.lam0.costSpec P (by includes) a)) 3
      (fun a ↦ by rw [appCost_fn, List.nil_append, Auto.Common.stripPad.c335.lam0.costEq P
        (by includes)]) tail
    have h3 := drop232_cost P (by includes) 1 (tail.dropWhile fun x ↦ decide (x = 0)) (by norm_num)
    have hdl := (List.dropWhile_suffix (fun x ↦ decide (x = 0)) (l := tail)).length_le
    have h4 := reverseAux_cost P (by includes) ((tail.dropWhile fun x ↦ decide (x = 0)).drop 1) []
    have : ((tail.dropWhile fun x ↦ decide (x = 0)).drop 1).length ≤ tail.length := by
      simp only [List.length_drop]; omega
    split_ifs <;> omega

/-- **A path's bytes read as a padded message** (`keccakUnpaddedFast`, `keccakUnpaddedC`): strip
the padding, pad again, compare: at most `107·|bs| + 12200`. -/
theorem keccakUnpadded_cost (hP : Includes P keccakUnpaddedC.costDeps) (bs : List UInt8)
    (hb : bs.length < 2 ^ 62) :
    machineCost P keccakUnpaddedC.costIdx [enc bs] ≤ 107 * bs.length + 12200 := by
  rw [keccakUnpaddedC.costEq P hP]
  have h1 := stripPad_cost P (by includes) bs hb
  have hs := stripPad_length_le bs
  have h2 := keccakPadded_cost P (by includes) (Common.stripPad bs) (by omega)
  have h3 := bytesBeq_cost P (by includes) (LeanVM.keccakPadded (Common.stripPad bs)) bs
  split_ifs <;> omega

/-! ## The replay's block bytes and cut -/

theorem wordBytes_length (w : UInt64) : (wordBytes w).length = 8 := by
  unfold wordBytes; simp

/-- A word's bytes (`wordBytes.c328`): at most `312`. -/
theorem wordBytes_cost (hP : Includes P Auto.LeanVM.Protocol.KeccakHash.wordBytes.c328.costDeps)
    (w : UInt64) :
    machineCost P Auto.LeanVM.Protocol.KeccakHash.wordBytes.c328.costIdx [enc w] ≤ 312 := by
  rw [Auto.LeanVM.Protocol.KeccakHash.wordBytes.c328.costEq P hP]
  have h1 := rangeLoop_cost P (by includes) 8 [] (by norm_num)
  have h2 := map_cost P (by includes) _
    (.fn Auto.LeanVM.Protocol.KeccakHash.wordBytes.c328.lam0.costIdx [enc w])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.KeccakHash.wordBytes.c328.lam0.costSpec P
      (by includes) w a)) 9 (List.range 8) (fun k hk ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.LeanVM.Protocol.KeccakHash.wordBytes.c328.lam0.costEq P (by includes),
        limbs_of_lt (by have := List.mem_range.1 hk; omega : k < 2 ^ 64)])
  simp only [List.length_range] at h2
  omega

/-- **A block's bytes** (`blockBytes.c326`): `17` words of `8` bytes, at most `7400`. -/
theorem blockBytes_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.blockBytes.c326.costDeps) (s x : Semantics.KeccakState) :
    machineCost P Auto.LeanVM.Extraction.Fast.blockBytes.c326.costIdx [enc s, enc x] ≤ 7400 := by
  rw [Auto.LeanVM.Extraction.Fast.blockBytes.c326.costEq P hP]
  have h1 := rangeLoop_cost P (by includes) 17 [] (by norm_num)
  have h2 := map_cost P (by includes) _ (.fn Auto.LeanVM.Extraction.Fast.blockBytes.c326.lam0.costIdx [enc s, enc x])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.Fast.blockBytes.c326.lam0.costSpec P (by includes) s x a)) 322
    (List.range 17) (fun k _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.LeanVM.Extraction.Fast.blockBytes.c326.lam0.costEq P (by includes)]
      have := wordBytes_cost P (by includes) (Semantics.Keccak.lane s k ^^^ Semantics.Keccak.lane x k)
      omega)
  have h3 := flatten_map_cost P (by includes) 8
    (fun i ↦ wordBytes (Semantics.Keccak.lane s i ^^^ Semantics.Keccak.lane x i)) (List.range 17)
    (fun i _ ↦ (wordBytes_length _).le)
  simp only [List.length_range] at h2 h3
  omega

theorem blockBytes_length (s x : Semantics.KeccakState) : (blockBytes s x).length = 136 := by
  simp [blockBytes, wordBytes, List.length_flatMap]

/-- The cut (`cut.c325`): at most `7·|bs| + 13`. -/
theorem cut_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.cut.c325.costDeps) (B : ℕ) (hB : B < 2 ^ 64) (bs : List UInt8)
    (hb : bs.length < 2 ^ 64) : machineCost P Auto.LeanVM.Extraction.Fast.cut.c325.costIdx [enc B, enc bs] ≤ 7 * bs.length + 13 := by
  rw [Auto.LeanVM.Extraction.Fast.cut.c325.costEq P hP, limbs_of_lt hb, limbs_of_lt hB]
  have := listLength_cost P (by includes) bs hb
  simp only [max_self]
  split_ifs <;> omega

/-! ## The replay, amortized -/

section Maps

variable {α β : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]

/-- A value a lookup returns is an entry's. -/
theorem get?_some_mem {m : SortedMap α β} {k : α} {v : β} (h : m.get? k = some v) :
    ∃ l ∈ m.levels, ∃ e ∈ l.entries, e.2 = v := by
  rw [SortedMap.get?_eq] at h
  obtain ⟨l, hl, hv⟩ := List.exists_of_findSome?_eq_some h
  simp only [lookup, Option.map_eq_some_iff] at hv
  obtain ⟨e, he, rfl⟩ := hv
  exact ⟨l, hl, e, by simpa using List.mem_of_find?_eq_some he, rfl⟩

/-- An insertion keeps the values in `Q`. -/
theorem valsIn_insert {Q : β → Prop} {m : SortedMap α β}
    (hQ : ∀ l ∈ m.levels, ∀ e ∈ l.entries, Q e.2) (k : α) {v : β} (hv : Q v) :
    ∀ l ∈ (m.insert k v).levels, ∀ e ∈ l.entries, Q e.2 := by
  unfold SortedMap.insert
  have : ∀ (ls : List (Level α β)) (l0 : Level α β), (∀ l ∈ l0 :: ls, ∀ e ∈ l.entries, Q e.2) →
      ∀ l ∈ carry l0 ls, ∀ e ∈ l.entries, Q e.2 := by
    intro ls
    induction ls with
    | nil => intro l h; simpa [carry] using h
    | cons l' ls ih =>
      intro l h
      rw [carry]
      split
      · refine ih _ fun x hx ↦ ?_
        rcases List.mem_cons.1 hx with rfl | hx
        · intro e he
          simp only [Level.merge, List.mem_toArray] at he
          rcases mem_mergeNewer he with h1 | h1
          · exact h l (by simp) e (by simpa using h1)
          · exact h l' (by simp) e (by simpa using h1)
        · exact h x (by simp [hx])
      · exact h
  refine this _ _ fun l hl e he ↦ ?_
  rcases List.mem_cons.1 hl with rfl | hl
  · simp at he; rw [he]; exact hv
  · exact hQ l hl e he

end Maps

/-- A path's bytes are at most `B`. -/
@[expose] def PathOk (B : ℕ) (p : KeccakState × Option (List UInt8)) : Prop :=
  ∀ bs, p.2 = some bs → bs.length ≤ B

/-- **The replay's invariant**, `r` queries left: three good maps of word-list keys (`25` words for
the edges, `8` for the capacities), the paths' bytes at most `B`, room for `r` more insertions
below `2^D`. -/
@[expose] def ReplayInv (B D : ℕ) (τ : ReplayFast) (r : ℕ) : Prop :=
  smGood τ.fwd ∧ smGood τ.inv ∧ smGood τ.caps ∧
    KeysIn (WordsKey 25) τ.fwd.levels ∧ KeysIn (WordsKey 25) τ.inv.levels ∧
    KeysIn (WordsKey 8) τ.caps.levels ∧ (∀ l ∈ τ.caps.levels, ∀ e ∈ l.entries, PathOk B e.2) ∧
    (∀ p ∈ τ.paths, PathOk B p) ∧ smWeightSum τ.fwd + r ≤ 2 ^ D ∧ smWeightSum τ.inv + r ≤ 2 ^ D ∧
    smWeightSum τ.caps + r ≤ 2 ^ D

/-- The replay's potential: its three maps', each at its merge price per entry. -/
@[expose] def replayPot (D : ℕ) (τ : ReplayFast) : ℕ :=
  (23 * 25 + 31) * potential D τ.fwd.levels + (23 * 25 + 31) * potential D τ.inv.levels +
    (23 * 8 + 31) * potential D τ.caps.levels

/-- A replay step's amortized price: two lookups among `25`-word keys, one among `8`-word keys,
three amortized insertions, a block's bytes and the cut. -/
@[expose] def replayStepBound (B D : ℕ) : ℕ :=
  2 * (D * (17 + (60 + 23 * 25) * (D + 2))) + D * (17 + (60 + 23 * 8) * (D + 2)) +
    2 * ((23 * 25 + 31) * D) + (23 * 8 + 31) * D + 120 * D + 16 * B + 10000

theorem toList_length25 (x : KeccakState) : x.toList.length = 25 := by simp

set_option maxRecDepth 20000 in
/-- **One replay step, amortized** (`replayStepC`). -/
theorem replayStep_amortized (hP : Includes P replayStepC.costDeps) (B D : ℕ) (hD : D ≤ 61)
    (hB : B < 2 ^ 62) (τ : ReplayFast) (r : ℕ) (hτ : ReplayInv B D τ (r + 1))
    (q : PermutationQuery KeccakState × KeccakState) :
    ReplayInv B D (ReplayFast.step B τ q) r ∧
      machineCost P replayStepC.costIdx [enc B, enc τ, enc q] + replayPot D (ReplayFast.step B τ q) ≤
        replayPot D τ + replayStepBound B D := by
  obtain ⟨g1, g2, g3, k1, k2, k3, vc, vp, w1, w2, w3⟩ := hτ
  have h62 : 2 ^ D < 2 ^ 62 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨lv1, sz1⟩ := smGood_levels_le g1 (by omega : smWeightSum τ.fwd < 2 ^ D)
  obtain ⟨lv2, sz2⟩ := smGood_levels_le g2 (by omega : smWeightSum τ.inv < 2 ^ D)
  obtain ⟨lv3, sz3⟩ := smGood_levels_le g3 (by omega : smWeightSum τ.caps < 2 ^ D)
  have hU : ∀ k : List UInt64, k.length = 25 → ∀ m : SortedMap (List UInt64) Unit,
      m.levels.length ≤ D → (∀ l ∈ m.levels, l.entries.size ≤ l.weight ∧ l.weight ≤ 2 ^ D) →
      machineCost P Auto.LeanVM.Extraction.Fast.SortedMap.get?.c313.costIdx [enc m, enc k] ≤
        D * (17 + (60 + 23 * 25) * (D + 2)) + 9 := by
    intro k hk m hl hs
    have := getU_cost P (by includes) m (2 ^ D) h62 (fun l hl' ↦ (hs l hl').1.trans (hs l hl').2) k
    rw [Nat.log2_two_pow, hk] at this
    exact this.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 9)
  have hC : ∀ k : List UInt64, k.length = 8 →
      machineCost P Auto.LeanVM.Extraction.Fast.SortedMap.get?.c316.costIdx [enc τ.caps, enc k] ≤
        D * (17 + (60 + 23 * 8) * (D + 2)) + 9 := by
    intro k hk
    have := getC_cost P (by includes) τ.caps (2 ^ D) h62
      (fun l hl' ↦ (sz3 l hl').1.trans (sz3 l hl').2) k
    rw [Nat.log2_two_pow, hk] at this
    exact this.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ lv3) 9)
  -- an insertion into an edge map, amortized
  have hInsU : ∀ (m : SortedMap (List UInt64) Unit), smGood m → KeysIn (WordsKey 25) m.levels →
      smWeightSum m < 2 ^ D → m.levels.length ≤ D → ∀ k : List UInt64, k.length = 25 →
      machineCost P Auto.LeanVM.Extraction.Fast.SortedMap.insert.c319.costIdx [enc m, enc k, enc ()] +
          (23 * 25 + 31) * potential D (m.insert k ()).levels ≤
        (23 * 25 + 31) * potential D m.levels + (23 * 25 + 31) * D + 40 * D + 60 := by
    intro m hm hk hN hl k hkl
    rw [Auto.LeanVM.Extraction.Fast.SortedMap.insert.c319.costEq P (by includes)]
    have := carryU_amortized P (by includes) 25 D (by omega) m hm hk hN
      ⟨1, #[(k, ())], by simp [Ascending]⟩ rfl rfl (fun e he ↦ by
        simp at he; rw [he]; show k.length ≤ 25; omega)
    have hins : (m.insert k ()).levels = carry ⟨1, #[(k, ())], by simp [Ascending]⟩ m.levels := rfl
    rw [hins]
    omega
  have hInsC : ∀ (k : List UInt64), k.length = 8 → ∀ v : KeccakState × Option (List UInt8),
      machineCost P Auto.LeanVM.Extraction.Fast.SortedMap.insert.c330.costIdx
          [enc τ.caps, enc k, enc v] + (23 * 8 + 31) * potential D (τ.caps.insert k v).levels ≤
        (23 * 8 + 31) * potential D τ.caps.levels + (23 * 8 + 31) * D + 40 * D + 60 := by
    intro k hkl v
    rw [Auto.LeanVM.Extraction.Fast.SortedMap.insert.c330.costEq P (by includes)]
    have := carryC_amortized P (by includes) 8 D (by omega) τ.caps g3 k3 (by omega)
      ⟨1, #[(k, v)], by simp [Ascending]⟩ rfl rfl (fun e he ↦ by
        simp at he; rw [he]; show k.length ≤ 8; omega)
    have hins : (τ.caps.insert k v).levels = carry ⟨1, #[(k, v)], by simp [Ascending]⟩ τ.caps.levels :=
      rfl
    rw [hins]
    omega
  have hd : ∀ z : KeccakState, machineCost P Auto.List.drop.c232.costIdx [enc 17, enc z.toList] ≤ 268 :=
    fun z ↦ drop232_cost P (by includes) 17 z.toList (by norm_num)
  have hk25 : ∀ z : KeccakState, WordsKey 25 z.toList := fun z ↦ by simp [WordsKey]
  have hk8 : ∀ z : KeccakState, WordsKey 8 (z.toList.drop 17) := fun z ↦ by simp [WordsKey]
  have hl25 : ∀ z : KeccakState, z.toList.length = 25 := fun z ↦ by simp
  have hl8 : ∀ z : KeccakState, (z.toList.drop 17).length = 8 := fun z ↦ by simp
  obtain ⟨fst, y⟩ := q
  rw [replayStepC.costEq_mk P hP]
  unfold replayStepBound replayPot
  generalize hGU : D * (17 + (60 + 23 * 25) * (D + 2)) = GU at hU
  generalize hGC : D * (17 + (60 + 23 * 8) * (D + 2)) = GC at hC
  cases fst with
  | forward x =>
    simp only [Vector.size_toArray]
    have hgf := hU x.toList (hl25 x) τ.fwd lv1 sz1
    by_cases hc : τ.fwd.contains x.toList = true
    · simp only [ReplayFast.step, hc, ↓reduceIte]
      refine ⟨⟨g1, g2, g3, k1, k2, k3, vc, vp, by omega, by omega, by omega⟩, ?_⟩
      generalize τ.fwd.get? x.toList = o
      cases o <;> dsimp only <;> omega
    · simp only [ReplayFast.step, hc, Bool.false_eq_true, ↓reduceIte]
      have hgc := hC (x.toList.drop 17) (hl8 x)
      have hf := hInsU τ.fwd g1 k1 (by omega) lv1 x.toList (hl25 x)
      have hi := hInsU τ.inv g2 k2 (by omega) lv2 y.toList (hl25 y)
      have hdx := hd x
      have hdy := hd y
      obtain ⟨gf, wf⟩ := smGood_insert g1 x.toList ()
      obtain ⟨gi, wi⟩ := smGood_insert g2 y.toList ()
      cases hg : τ.caps.get? (x.toList.drop 17) with
      | none =>
        dsimp only
        refine ⟨⟨gf, gi, g3, keysIn_insert k1 (hk25 x) (), keysIn_insert k2 (hk25 y) (), k3, vc, vp,
          by (try dsimp only); omega, by (try dsimp only); omega, by (try dsimp only); omega⟩, ?_⟩
        generalize τ.fwd.get? x.toList = o
        cases o <;> dsimp only <;> omega
      | some sv =>
        obtain ⟨s, obs⟩ := sv
        dsimp only
        have hobs : PathOk B (s, obs) := by
          obtain ⟨l, hl, e, he, he2⟩ := get?_some_mem hg
          exact he2 ▸ vc l hl e he
        have hp : PathOk B (y, obs.bind fun bs ↦ cut B (bs ++ blockBytes s x)) := by
          intro bs' h
          simp only [Option.bind_eq_some_iff, cut] at h
          obtain ⟨bs, -, h⟩ := h
          split_ifs at h with hle
          · cases h; exact hle
        have hcI := hInsC (y.toList.drop 17) (hl8 y) (y, obs.bind fun bs ↦ cut B (bs ++ blockBytes s x))
        obtain ⟨gc, wc⟩ := smGood_insert g3 (y.toList.drop 17)
          (y, obs.bind fun bs ↦ cut B (bs ++ blockBytes s x))
        refine ⟨⟨gf, gi, gc, keysIn_insert k1 (hk25 x) (), keysIn_insert k2 (hk25 y) (),
          keysIn_insert k3 (hk8 y) _, valsIn_insert vc _ hp, ?_, by (try dsimp only); omega, by (try dsimp only); omega, by (try dsimp only); omega⟩, ?_⟩
        · intro p hp'
          rcases List.mem_cons.1 hp' with rfl | hp'
          · exact hp
          · exact vp p hp'
        · have hbind : machineCost P Auto.Option.bind.c323.costIdx
              [enc obs, Val.fn replayStepC.lam0.costIdx [enc s, enc x, enc B]] ≤ 16 * B + 8400 := by
            cases obs with
            | none =>
              rw [Auto.Option.bind.c323.costEq_none P (by includes)
                (fun bs ↦ cut B (bs ++ blockBytes s x)) (.fn replayStepC.lam0.costIdx [enc s, enc x, enc B])
                (fun bs ↦ RunsApp.of_spec (replayStepC.lam0.costSpec P (by includes) s x B bs))]; omega
            | some bs =>
              have hbs := hobs bs rfl
              rw [Auto.Option.bind.c323.costEq_some P (by includes) bs
                (fun bs ↦ cut B (bs ++ blockBytes s x)) (.fn replayStepC.lam0.costIdx [enc s, enc x, enc B])
                (fun bs ↦ RunsApp.of_spec (replayStepC.lam0.costSpec P (by includes) s x B bs))]
              simp only [appCost_fn, List.cons_append, List.nil_append]
              rw [replayStepC.lam0.costEq P (by includes)]
              have := blockBytes_cost P (by includes) s x
              have := append_cost P (by includes) bs (blockBytes s x)
              have := cut_cost P (by includes) B (by omega) (bs ++ blockBytes s x)
                (by simp [blockBytes_length]; omega)
              simp only [List.length_append, blockBytes_length] at this
              omega
          generalize τ.fwd.get? x.toList = o
          cases o <;> dsimp only <;> omega
  | inverse y' =>
    simp only [Vector.size_toArray]
    have hgi := hU y'.toList (hl25 y') τ.inv lv2 sz2
    by_cases hc : τ.inv.contains y'.toList = true
    · simp only [ReplayFast.step, hc, ↓reduceIte]
      refine ⟨⟨g1, g2, g3, k1, k2, k3, vc, vp, by omega, by omega, by omega⟩, ?_⟩
      generalize τ.inv.get? y'.toList = o
      cases o <;> dsimp only <;> omega
    · simp only [ReplayFast.step, hc, Bool.false_eq_true, ↓reduceIte]
      have hf := hInsU τ.fwd g1 k1 (by omega) lv1 y.toList (hl25 y)
      have hi := hInsU τ.inv g2 k2 (by omega) lv2 y'.toList (hl25 y')
      obtain ⟨gf, wf⟩ := smGood_insert g1 y.toList ()
      obtain ⟨gi, wi⟩ := smGood_insert g2 y'.toList ()
      refine ⟨⟨gf, gi, g3, keysIn_insert k1 (hk25 y) (), keysIn_insert k2 (hk25 y') (), k3, vc, vp,
        by (try dsimp only); omega, by (try dsimp only); omega, by (try dsimp only); omega⟩, ?_⟩
      generalize τ.inv.get? y'.toList = o
      cases o <;> dsimp only <;> omega

end

end LeanVM.Cost.Bounds
