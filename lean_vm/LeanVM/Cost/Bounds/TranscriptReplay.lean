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
open LeanVM.Extraction.Fast LeanVM.Protocol.KeccakHash

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

end

end LeanVM.Cost.Bounds
