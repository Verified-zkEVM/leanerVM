module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Bounds.SortedMap
public import LeanVM.Cost.Bounds.Samples.CommittedLeaves
public import LeanVM.Cost.Extractor.Transcript
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# Bounds: the committed word's reader

* `replicate_cost`: `List.replicate n a` costs at most `17·n + 6`, for word-sized `n`;
* **`leafAt_cost`**: reading a position of the committed word (`leafAt leaves h w v`, the leaf
  `v mod 2^h`, or `w` zeros) costs at most `17·w + 19`, for `h < 64` and word-sized `v`, `w`.

The committed leaves themselves are bounded by the sample's `committedLeaves_cost`
(`Bounds/Samples/CommittedLeaves.lean`): at most `2^h·(2·L + 617·w + 12060 + 8·h) + 7`, `L` the
preimage lookup's price (`preimageLookup_cost`: `40 + |levels|·(18 + 192·(log₂ N + 2))`, at most
`log₂(N + 1)` levels after `N` insertions by `sm_two_pow_levels_le`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Cost.Bounds.Samples

public section

attribute [local instance] lexOrd

variable (P : Program)

/-- `List.replicate n a`: at most `17·n + 6`. -/
theorem replicate_cost (hP : Includes P Auto.List.replicate.c9.costDeps) {α : Type} [Enc α]
    (a : α) : ∀ n, n < 2 ^ 64 →
      machineCost P Auto.List.replicate.c9.costIdx [enc n, enc a] ≤ 17 * n + 6 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.List.replicate.c9.costEq_zero P hP]
  | succ n ih =>
    intro hn
    rw [Auto.List.replicate.c9.costEq_succ P hP, limbs_of_lt hn]
    have := ih (by omega)
    omega

/-- **A position of the committed word**: at most `17·w + 19`. -/
theorem leafAt_cost (hP : Includes P leafAtC.costDeps) (leaves : Array (List K)) (h w v : ℕ)
    (hh : h < 64) (hv : v < 2 ^ 64) (hw : w < 2 ^ 64) :
    machineCost P leafAtC.costIdx [enc leaves, enc h, enc w, enc v] ≤ 17 * w + 19 := by
  rw [leafAtC.costEq P hP]
  have h2 : 2 ^ h < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hh
  have hr := replicate_cost P (by includes) (0 : K) w hw
  rw [Nat.one_shiftLeft, limbs_of_lt h2, limbs_of_lt (by omega : h < 2 ^ 64), limbs_of_lt hv]
  omega

/-! ## Generic list functions -/

/-- `List.length` (`length.c37`): `7` per element, `3` at the end, for word-sized lists. -/
theorem length37_cost (hP : Includes P Auto.List.length.c37.costDeps) {α : Type} [Enc α] :
    ∀ l : List α, l.length < 2 ^ 64 →
      machineCost P Auto.List.length.c37.costIdx [enc l] ≤ 7 * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.length.c37.costEq_nil P hP]; omega
  | cons x l ih =>
    intro hl
    simp only [List.length_cons] at hl
    rw [Auto.List.length.c37.costEq_cons P hP, limbs_of_lt (by omega : l.length < 2 ^ 64)]
    have := ih (by omega)
    simp only [List.length_cons]
    omega

/-- Byte strings compared (`List.beq`, `beq.c54`): `11` per byte of the second, `9` at the end. -/
theorem beq54_cost (hP : Includes P Auto.List.beq.c54.costDeps) :
    ∀ x y : List UInt8, machineCost P Auto.List.beq.c54.costIdx [enc x, enc y] ≤ 11 * y.length + 9 := by
  intro x
  induction x with
  | nil => intro y; rw [Auto.List.beq.c54.costEq_nil P hP]; cases y <;> simp
  | cons a x ih =>
    intro y
    rw [Auto.List.beq.c54.costEq_cons P hP]
    cases y with
    | nil => simp
    | cons b y =>
      have := ih y
      simp only [List.length_cons]
      split_ifs <;> omega

/-! ## The preimage index's map: keys `(digest words, length)` -/

/-- A preimage key: four words and a word-sized length. -/
@[expose] def PreKey (k : List UInt64 × ℕ) : Prop := k.1.length = 4 ∧ k.2 < 2 ^ 64

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- `mergeNewer` on preimage keys (`mergeNewer.c86`): at most `150` per entry and `9`. -/
theorem mergeNewer86_cost (hP : Includes P mergeNewer.c86.costDeps) :
    ∀ (n : ℕ) (a b : List ((List UInt64 × ℕ) × Hits)), a.length + b.length = n →
      (∀ e ∈ a, PreKey e.1) → (∀ e ∈ b, PreKey e.1) →
      machineCost P mergeNewer.c86.costIdx [enc a, enc b] ≤ 150 * n + 9 := by
  have hcmp := compareLexW_cost P (by includes) _ (.fn Samples.searchInKeys.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (Samples.searchInKeys.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by rw [appCost_fn]; exact cmpWord_cost P (by includes) a b)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn ha hb
  cases a with
  | nil => rw [mergeNewer.c86.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewer.c86.costEq_cons P hP]
    cases b with
    | nil => simp
    | cons y b =>
      dsimp only
      have hx := ha x (by simp)
      have hy := hb y (by simp)
      have hc := hcmp x.1.1 y.1.1
      rw [hy.1] at hc
      have h1 := ih (a.length + (b.length + 1)) (by simp at hn; omega) a (y :: b) (by simp)
        (fun e he ↦ ha e (by simp [he])) hb
      have h2 := ih (a.length + b.length) (by simp at hn; omega) a b rfl
        (fun e he ↦ ha e (by simp [he])) (fun e he ↦ hb e (by simp [he]))
      have h3 := ih (a.length + 1 + b.length) (by simp at hn; omega) (x :: a) b (by simp)
        ha (fun e he ↦ hb e (by simp [he]))
      simp only [List.length_cons] at hn h1 h3
      rw [limbs_of_lt hx.2, limbs_of_lt hy.2]
      generalize compareOn (fun x ↦ x.1) x.1 y.1 = o1
      generalize compare x.1 y.1 = o2
      cases o1 <;> cases o2 <;> dsimp only <;> (try split_ifs) <;> omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- Two levels merged (`Level.merge.c85`): at most `154` per entry and `26`. -/
theorem levelMerge85_cost (hP : Includes P Level.merge.c85.costDeps)
    (l l' : Level (List UInt64 × ℕ) Hits) (hQ : KeysIn PreKey [l, l'])
    (hw : l.weight < 2 ^ 64) (hw' : l'.weight < 2 ^ 64) :
    machineCost P Level.merge.c85.costIdx [enc l, enc l'] ≤
      26 + 154 * (l.entries.size + l'.entries.size) := by
  rw [Level.merge.c85.costEq P hP, limbs_of_lt hw, limbs_of_lt hw']
  have hm := mergeNewer86_cost P (by includes) _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l (by simp) e (by simpa using he))
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList] at hm hlen
  omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **An insertion into the preimage index, amortized** (`carry.c84`): `154·D + 40·(levels + 1)`
plus the drop of `154` times the potential. -/
theorem carry84_amortized (hP : Includes P carry.c84.costDeps) (D : ℕ) (hD : D < 64)
    (m : SortedMap (List UInt64 × ℕ) Hits) (hm : smGood m) (hQ : KeysIn PreKey m.levels)
    (hN : smWeightSum m < 2 ^ D) (l : Level (List UInt64 × ℕ) Hits) (hw : l.weight = 1)
    (hs : l.entries.size = 1) (hk : ∀ e ∈ l.entries, PreKey e.1) :
    machineCost P carry.c84.costIdx [enc l, enc m.levels] + 154 * potential D (carry l m.levels) ≤
      154 * potential D m.levels + 154 * D + 40 * (m.levels.length + 1) := by
  have h64 : 2 ^ D < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hD
  refine insert_amortized PreKey (fun l ls ↦ machineCost P carry.c84.costIdx [enc l, enc ls]) 40 154
    D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carry.c84.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carry.c84.costEq_cons P hP, limbs_of_lt (by omega : l.weight < 2 ^ 64),
      limbs_of_lt (by omega : l'.weight < 2 ^ 64)]
    simp only [hne, ↓reduceIte]
    omega
  · intro l l' ls h1 heq hQ2
    have := levelMerge85_cost P (by includes) l l' hQ2 (by omega) (by omega)
    rw [carry.c84.costEq_cons P hP, limbs_of_lt (by omega : l.weight < 2 ^ 64),
      limbs_of_lt (by omega : l'.weight < 2 ^ 64)]
    simp only [heq, ↓reduceIte]
    omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- A lookup in the preimage index (`SortedMap.get?.c20`): a binary search per level. -/
theorem get20_cost (hP : Includes P SortedMap.get?.c20.costDeps)
    (m : SortedMap (List UInt64 × ℕ) Hits) (H : ℕ) (hH : H < 2 ^ 62)
    (hm : ∀ l ∈ m.levels, l.entries.size ≤ H) (hQ : KeysIn PreKey m.levels)
    (k : List UInt64 × ℕ) (hk : PreKey k) :
    machineCost P SortedMap.get?.c20.costIdx [enc m, enc k] ≤
      m.levels.length * (17 + 192 * (Nat.log2 H + 2)) + 9 := by
  have hlam : ∀ l ∈ m.levels, appCost P (.fn SortedMap.get?.c20.lam0.costIdx [enc k]) [enc l] ≤
      8 + 192 * (Nat.log2 H + 2) := by
    intro l hl
    rw [appCost_fn, List.singleton_append, SortedMap.get?.c20.lam0.costEq P (by includes)]
    have := searchInKeys_cost P (by includes) l.entries k H hH (by have := hm l hl; omega)
      (fun e he ↦ (hQ l hl e he).2) hk.2 0 l.entries.size (by omega) (hm l hl)
    rw [hk.1] at this
    have := log2_mono (show l.entries.size - 0 ≤ H by have := hm l hl; omega)
    nlinarith
  have hfs := findSomeLevels_cost P (by includes) _ (.fn SortedMap.get?.c20.lam0.costIdx [enc k])
    (fun a ↦ RunsApp.of_spec (SortedMap.get?.c20.lam0.costSpec P (by includes) _ a)) _ m.levels hlam
  rw [SortedMap.get?.c20.costEq P hP]
  nlinarith

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- `Hits.merge h (.one y)` (`Hits.merge.c88`): at most `11·|y| + 20`. -/
theorem hitsMerge88_cost (hP : Includes P Hits.merge.c88.costDeps) (h : Hits) (y : List UInt8) :
    machineCost P Hits.merge.c88.costIdx [enc h, enc (Hits.one y)] ≤ 11 * y.length + 20 := by
  cases h with
  | none => rw [Hits.merge.c88.costEq_none P hP]; omega
  | many => rw [Hits.merge.c88.costEq_many P hP]; dsimp only; omega
  | one x =>
    rw [Hits.merge.c88.costEq_one P hP]
    have := beq54_cost P (by includes) x y
    dsimp only
    split_ifs <;> omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- A pair's key (`hitKey.c87`): at most `7·|bytes| + 24`. -/
theorem hitKey87_cost (hP : Includes P hitKey.c87.costDeps) (p : List UInt8 × Protocol.Digest)
    (hp : p.1.length < 2 ^ 64) :
    machineCost P hitKey.c87.costIdx [enc p] ≤ 7 * p.1.length + 24 := by
  rw [hitKey.c87.costEq P hP]
  have := length37_cost P (by includes) p.1 hp
  simp only [Vector.size_toArray]
  omega

/-- The preimage index's invariant after some insertions, `r` left: a good map of keys
`PreKey`, `r` more insertions keeping it below `2^D`. -/
@[expose] def PreInv (D : ℕ) (m : SortedMap (List UInt64 × ℕ) Hits) (r : ℕ) : Prop :=
  smGood m ∧ KeysIn PreKey m.levels ∧ smWeightSum m + r ≤ 2 ^ D

theorem preKey_hitKey (p : List UInt8 × Protocol.Digest) (hp : p.1.length < 2 ^ 64) :
    PreKey (hitKey p) := ⟨by simp [hitKey], hp⟩

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **One step of the preimage index, amortized**: a pair of at most `L` bytes into a map below
`2^D` insertions costs at most `25·L + 192·D² + 595·D + 152` plus the drop of `154` times the
potential. -/
theorem preimageStep_amortized (hP : Includes P preimageIndexC.lam0.costDeps) (D L : ℕ)
    (hD : D ≤ 61) (hL : L < 2 ^ 64) (m : SortedMap (List UInt64 × ℕ) Hits) (r : ℕ)
    (hm : PreInv D m (r + 1)) (p : List UInt8 × Protocol.Digest) (hp : p.1.length ≤ L) :
    PreInv D (m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))) r ∧
      machineCost P preimageIndexC.lam0.costIdx [enc m, enc p] +
          154 * potential D (m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))).levels ≤
        154 * potential D m.levels + (25 * L + 192 * (D * D) + 595 * D + 152) := by
  obtain ⟨hg, hQ, hw⟩ := hm
  have hk := preKey_hitKey p (by omega)
  have hN : smWeightSum m < 2 ^ D := by omega
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg hN
  have h62 : 2 ^ D < 2 ^ 62 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine ⟨?_, ?_⟩
  · obtain ⟨h1, h2⟩ := smGood_insert hg (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))
    exact ⟨h1, keysIn_insert hQ hk _, by omega⟩
  · rw [preimageIndexC.lam0.costEq P hP, SortedMap.insert.c83.costEq P (by includes)]
    have hkey := hitKey87_cost P (by includes) p (by omega)
    have hget := get20_cost P (by includes) m (2 ^ D) h62 (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2)
      hQ (hitKey p) hk
    rw [Nat.log2_two_pow] at hget
    have hmerge := hitsMerge88_cost P (by includes) (m.getD (hitKey p) .none) p.1
    have hcarry := carry84_amortized P (by includes) D (by omega) m hg hQ hN
      ⟨1, #[(hitKey p, (m.getD (hitKey p) .none).merge (.one p.1))], by simp [Ascending]⟩ rfl rfl
      (fun e he ↦ by simp at he; rw [he]; exact hk)
    have hins : (m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))).levels =
        carry ⟨1, #[(hitKey p, (m.getD (hitKey p) .none).merge (.one p.1))], by simp [Ascending]⟩ m.levels := rfl
    rw [hins]
    have hlv : m.levels.length * (17 + 192 * (D + 2)) ≤ D * (17 + 192 * (D + 2)) :=
      Nat.mul_le_mul_right _ hlev
    generalize m.get? (hitKey p) = o
    cases o <;> dsimp only <;> nlinarith

/-- **The preimage index** (`preimageIndex pairs`, compiled as `preimageIndexC`): at most
`n·(25·L + 192·D² + 595·D + 161) + 9` for `n ≤ 2^D` pairs of at most `L` bytes, `D ≤ 61`: per
pair a key, a lookup (`D` binary searches of `≤ D + 2` probes), and an amortized insertion
(`154·D` merged entries). -/
theorem preimageIndex_cost (hP : Includes P preimageIndexC.costDeps) (D L : ℕ) (hD : D ≤ 61)
    (hL : L < 2 ^ 64) (pairs : List (List UInt8 × Protocol.Digest)) (hn : pairs.length ≤ 2 ^ D)
    (hp : ∀ p ∈ pairs, p.1.length ≤ L) :
    machineCost P preimageIndexC.costIdx [enc pairs] ≤
      pairs.length * (25 * L + 192 * (D * D) + 595 * D + 161) + 9 := by
  rw [preimageIndexC.costEq P hP]
  have := listFoldl_amortized P (by includes) _ (.fn preimageIndexC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (preimageIndexC.lam0.costSpec P (by includes) a b))
    (25 * L + 192 * (D * D) + 595 * D + 152) (fun m ↦ 154 * potential D m.levels) (PreInv D)
    pairs SortedMap.empty ⟨smGood_empty, fun _ h ↦ by simp [SortedMap.empty] at h,
      by simp [smWeightSum_empty]; omega⟩
    (fun acc r hacc p hpm ↦ by
      rw [appCost_fn, List.nil_append]
      exact preimageStep_amortized P (by includes) D L hD hL acc r hacc p (hp p hpm))
  have h0 : potential D (SortedMap.empty : SortedMap (List UInt64 × ℕ) Hits).levels = 0 := rfl
  simp only [h0, Nat.mul_zero, Nat.zero_add] at this
  nlinarith

end

end LeanVM.Cost.Bounds
