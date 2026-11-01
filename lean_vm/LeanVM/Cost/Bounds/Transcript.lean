module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Bounds.SortedMap
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
open LeanVM.Extraction LeanVM.Extraction.Fast

public section

attribute [local instance] lexOrd

variable (P : Program)

/-- `List.replicate n a`: at most `17·n + 6`. -/
theorem replicate_cost (hP : Includes P Auto.List.replicate.c346.costDeps) {α : Type} [Enc α]
    (a : α) : ∀ n, n < 2 ^ 64 →
      machineCost P Auto.List.replicate.c346.costIdx [enc n, enc a] ≤ 17 * n + 6 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.List.replicate.c346.costEq_zero P hP]
  | succ n ih =>
    intro hn
    rw [Auto.List.replicate.c346.costEq_succ P hP, limbs_of_lt hn]
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

/-- `List.length` (`length.c229`): `7` per element, `3` at the end, for word-sized lists. -/
theorem length_cost (hP : Includes P Auto.List.length.c229.costDeps) {α : Type} [Enc α] :
    ∀ l : List α, l.length < 2 ^ 64 →
      machineCost P Auto.List.length.c229.costIdx [enc l] ≤ 7 * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.length.c229.costEq_nil P hP]; omega
  | cons x l ih =>
    intro hl
    simp only [List.length_cons] at hl
    rw [Auto.List.length.c229.costEq_cons P hP, limbs_of_lt (by omega : l.length < 2 ^ 64)]
    have := ih (by omega)
    simp only [List.length_cons]
    omega

/-- `List.compareLex` (`compareLex.c284`), any element type: `14` per position of the second list
and the comparison's price, `5` at the end. -/
theorem compareLex_cost (hP : Includes P Auto.List.compareLex.c284.costDeps) {α : Type} [Enc α]
    (cmp : α → α → Ordering) (cmpVal : Val)
    (hc : ∀ a b, RunsApp P cmpVal [enc a, enc b] (enc (cmp a b))) (B : ℕ)
    (hB : ∀ a b : α, appCost P cmpVal [enc a, enc b] ≤ B) :
    ∀ (a b : List α), machineCost P Auto.List.compareLex.c284.costIdx [cmpVal, enc a, enc b] ≤
      (B + 14) * b.length + 5 := by
  intro a
  induction a with
  | nil => intro b; rw [Auto.List.compareLex.c284.costEq P hP cmp cmpVal hc]; cases b <;> simp
  | cons x a ih =>
    intro b
    rw [Auto.List.compareLex.c284.costEq P hP cmp cmpVal hc]
    cases b with
    | nil => simp
    | cons y b =>
      have h1 := ih b
      have h2 := hB x y
      simp only [List.length_cons]
      generalize cmp x y = o
      cases o <;> dsimp only <;> nlinarith

/-- `List.findSome?` (`findSome?.c125`), any element type: `9` per element and the closure's
price, `3` at the end. -/
theorem findSome_cost (hP : Includes P Auto.List.findSome?.c125.costDeps) {α β : Type} [Enc α]
    [Enc β] (f : α → Option β) (fVal : Val) (hf : ∀ a, RunsApp P fVal [enc a] (enc (f a)))
    (B : ℕ) : ∀ ls : List α, (∀ l ∈ ls, appCost P fVal [enc l] ≤ B) →
      machineCost P Auto.List.findSome?.c125.costIdx [fVal, enc ls] ≤ (B + 9) * ls.length + 3 := by
  intro ls
  induction ls with
  | nil => intro _; rw [Auto.List.findSome?.c125.costEq_nil P hP f fVal hf]; omega
  | cons l ls ih =>
    intro hB
    rw [Auto.List.findSome?.c125.costEq_cons P hP f fVal hf]
    have h1 := ih fun l' hl ↦ hB l' (by simp [hl])
    have h2 := hB l (by simp)
    simp only [List.length_cons]
    generalize f l = o
    cases o <;> dsimp only <;> nlinarith

/-- Byte strings compared (`List.beq`, `beq.c54`): `11` per byte of the second, `9` at the end. -/
theorem bytesBeq_cost (hP : Includes P Auto.List.beq.c286.costDeps) :
    ∀ x y : List UInt8, machineCost P Auto.List.beq.c286.costIdx [enc x, enc y] ≤ 11 * y.length + 9 := by
  intro x
  induction x with
  | nil => intro y; rw [Auto.List.beq.c286.costEq_nil P hP]; cases y <;> simp
  | cons a x ih =>
    intro y
    rw [Auto.List.beq.c286.costEq_cons P hP]
    cases y with
    | nil => simp
    | cons b y =>
      have := ih y
      simp only [List.length_cons]
      split_ifs <;> omega

/-! ## The preimage index's map: keys `(digest words, length)` -/

/-- A preimage key: four words and a word-sized length. -/
@[expose] def PreKey (k : List UInt64 × ℕ) : Prop := k.1.length = 4 ∧ k.2 < 2 ^ 64

/-- Two words compared (`searchPreC.lam0`): at most `9`. -/
theorem cmpWord_cost (hP : Includes P searchPreC.lam0.costDeps) (a b : UInt64) :
    machineCost P searchPreC.lam0.costIdx [enc a, enc b] ≤ 9 := by
  rw [searchPreC.lam0.costEq P hP]
  split_ifs <;> omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- The binary search of a preimage key `k` (`searchIn.c289`): at most `C·(log₂(hi − lo) + 2)`,
`C = 100 + 23·|k.1|` the price of a probe, for word-sized indices and lengths. -/
theorem searchPre_cost (hP : Includes P searchIn.c289.costDeps)
    (t : Array ((List UInt64 × ℕ) × Hits)) (k : List UInt64 × ℕ) (H : ℕ) (hH : H < 2 ^ 62)
    (hts : t.size < 2 ^ 64) (ht : ∀ e ∈ t, e.1.2 < 2 ^ 64) (hk : k.2 < 2 ^ 64) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchIn.c289.costIdx [enc t, enc k, enc lo, enc hi] ≤
        (100 + 23 * k.1.length) * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have hcmp := compareLex_cost P (by includes) _ (.fn searchPreC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchPreC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by rw [appCost_fn]; exact cmpWord_cost P (by includes) a b)
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P searchIn.c289.costIdx [enc t, enc k, enc x.1, enc x.2])
    (100 + 23 * k.1.length) (100 + 23 * k.1.length) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchIn.c289.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    cost_simp
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchIn.c289.costEq P hP]
    simp only [show lo < hi by omega, ↓reduceIte]
    generalize hv : t[(lo + hi) / 2]? = ov
    cases ov with
    | none =>
      left
      cost_simp
      split_ifs <;> omega
    | some v =>
      have hv1 : v.1.2 < 2 ^ 64 := ht v (Array.mem_of_getElem? hv)
      cost_simp
      have hc := hcmp v.1.1 k.1
      generalize compareOn (fun x ↦ x.1) v.1 k = o1
      generalize compare v.1 k = o2
      cases o2
      · right
        refine ⟨((lo + hi) / 2 + 1, hi), ⟨by omega, hhi⟩, by dsimp only; omega, ?_⟩
        dsimp only
        cases o1 <;> dsimp only <;> split_ifs <;> omega
      · left
        cases o1 <;> dsimp only <;> split_ifs <;> omega
      · right
        refine ⟨(lo, (lo + hi) / 2), ⟨hlo, by omega⟩, by dsimp only; omega, ?_⟩
        dsimp only
        cases o1 <;> dsimp only <;> split_ifs <;> omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- `mergeNewer` on preimage keys (`mergeNewer.c291`): at most `150` per entry and `9`. -/
theorem mergeNewerPre_cost (hP : Includes P mergeNewer.c291.costDeps) :
    ∀ (n : ℕ) (a b : List ((List UInt64 × ℕ) × Hits)), a.length + b.length = n →
      (∀ e ∈ a, PreKey e.1) → (∀ e ∈ b, PreKey e.1) →
      machineCost P mergeNewer.c291.costIdx [enc a, enc b] ≤ 150 * n + 9 := by
  have hcmp := compareLex_cost P (by includes) _ (.fn searchPreC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchPreC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by rw [appCost_fn]; exact cmpWord_cost P (by includes) a b)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn ha hb
  cases a with
  | nil => rw [mergeNewer.c291.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewer.c291.costEq_cons P hP]
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
/-- Two levels merged (`levelMergePreC`): at most `154` per entry and `26`. -/
theorem levelMergePre_cost (hP : Includes P levelMergePreC.costDeps)
    (l l' : Level (List UInt64 × ℕ) Hits) (hQ : KeysIn PreKey [l, l'])
    (hw : l.weight < 2 ^ 64) (hw' : l'.weight < 2 ^ 64) :
    machineCost P levelMergePreC.costIdx [enc l, enc l'] ≤
      26 + 154 * (l.entries.size + l'.entries.size) := by
  rw [levelMergePreC.costEq P hP, limbs_of_lt hw, limbs_of_lt hw']
  have hm := mergeNewerPre_cost P (by includes) _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l (by simp) e (by simpa using he))
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList] at hm hlen
  omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **An insertion into the preimage index, amortized** (`carry.c294`): `154·D + 40·(levels + 1)`
plus the drop of `154` times the potential. -/
theorem carryPre_amortized (hP : Includes P carry.c294.costDeps) (D : ℕ) (hD : D < 64)
    (m : SortedMap (List UInt64 × ℕ) Hits) (hm : smGood m) (hQ : KeysIn PreKey m.levels)
    (hN : smWeightSum m < 2 ^ D) (l : Level (List UInt64 × ℕ) Hits) (hw : l.weight = 1)
    (hs : l.entries.size = 1) (hk : ∀ e ∈ l.entries, PreKey e.1) :
    machineCost P carry.c294.costIdx [enc l, enc m.levels] + 154 * potential D (carry l m.levels) ≤
      154 * potential D m.levels + 154 * D + 40 * (m.levels.length + 1) := by
  have h64 : 2 ^ D < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hD
  refine insert_amortized PreKey (fun l ls ↦ machineCost P carry.c294.costIdx [enc l, enc ls]) 40 154
    D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carry.c294.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carry.c294.costEq_cons P hP, limbs_of_lt (by omega : l.weight < 2 ^ 64),
      limbs_of_lt (by omega : l'.weight < 2 ^ 64)]
    simp only [hne, ↓reduceIte]
    omega
  · intro l l' ls h1 heq hQ2
    have := levelMergePre_cost P (by includes) l l' hQ2 (by omega) (by omega)
    rw [carry.c294.costEq_cons P hP, limbs_of_lt (by omega : l.weight < 2 ^ 64),
      limbs_of_lt (by omega : l'.weight < 2 ^ 64)]
    simp only [heq, ↓reduceIte]
    omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- A lookup in the preimage index (`getPreC`): a binary search per level. -/
theorem getPre_cost (hP : Includes P getPreC.costDeps)
    (m : SortedMap (List UInt64 × ℕ) Hits) (H : ℕ) (hH : H < 2 ^ 62)
    (hm : ∀ l ∈ m.levels, l.entries.size ≤ H) (hQ : KeysIn PreKey m.levels)
    (k : List UInt64 × ℕ) (hk : PreKey k) :
    machineCost P getPreC.costIdx [enc m, enc k] ≤
      m.levels.length * (17 + 192 * (Nat.log2 H + 2)) + 9 := by
  have hlam : ∀ l ∈ m.levels, appCost P (.fn getPreC.lam0.costIdx [enc k]) [enc l] ≤
      8 + 192 * (Nat.log2 H + 2) := by
    intro l hl
    rw [appCost_fn, List.singleton_append, getPreC.lam0.costEq P (by includes)]
    have := searchPre_cost P (by includes) l.entries k H hH (by have := hm l hl; omega)
      (fun e he ↦ (hQ l hl e he).2) hk.2 0 l.entries.size (by omega) (hm l hl)
    rw [hk.1] at this
    have := log2_mono (show l.entries.size - 0 ≤ H by have := hm l hl; omega)
    nlinarith
  have hfs := findSome_cost P (by includes) _ (.fn getPreC.lam0.costIdx [enc k])
    (fun a ↦ RunsApp.of_spec (getPreC.lam0.costSpec P (by includes) _ a)) _ m.levels hlam
  rw [getPreC.costEq P hP]
  nlinarith

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- `Hits.merge h (.one y)` (`hitsMergeC`): at most `11·|y| + 20`. -/
theorem hitsMerge_cost (hP : Includes P hitsMergeC.costDeps) (h : Hits) (y : List UInt8) :
    machineCost P hitsMergeC.costIdx [enc h, enc (Hits.one y)] ≤ 11 * y.length + 20 := by
  cases h with
  | none => rw [hitsMergeC.costEq_none P hP]; omega
  | many => rw [hitsMergeC.costEq_many P hP]; dsimp only; omega
  | one x =>
    rw [hitsMergeC.costEq_one P hP]
    have := bytesBeq_cost P (by includes) x y
    dsimp only
    split_ifs <;> omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- A pair's key (`hitKeyC`): at most `7·|bytes| + 24`. -/
theorem hitKey_cost (hP : Includes P hitKeyC.costDeps) (p : List UInt8 × Protocol.Digest)
    (hp : p.1.length < 2 ^ 64) :
    machineCost P hitKeyC.costIdx [enc p] ≤ 7 * p.1.length + 24 := by
  rw [hitKeyC.costEq P hP]
  have := length_cost P (by includes) p.1 hp
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
  · rw [preimageIndexC.lam0.costEq P hP, insertPreC.costEq P (by includes)]
    have hkey := hitKey_cost P (by includes) p (by omega)
    have hget := getPre_cost P (by includes) m (2 ^ D) h62 (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2)
      hQ (hitKey p) hk
    rw [Nat.log2_two_pow] at hget
    have hmerge := hitsMerge_cost P (by includes) (m.getD (hitKey p) .none) p.1
    have hcarry := carryPre_amortized P (by includes) D (by omega) m hg hQ hN
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

/-! ## The first answers' map: byte-string keys -/

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- Byte strings compared (`compareLex` with `searchBytesC.lam0`): `23` per byte of the second. -/
theorem compareBytes_cost (hP : Includes P searchIn.c302.costDeps) (a b : List UInt8) :
    machineCost P Auto.List.compareLex.c284.costIdx [.fn searchBytesC.lam0.costIdx [], enc a, enc b] ≤
      23 * b.length + 5 := by
  have := compareLex_cost P (by includes) _ (.fn searchBytesC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchBytesC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by
      rw [appCost_fn, List.nil_append, searchBytesC.lam0.costEq P (by includes)]
      split_ifs <;> omega) a b
  omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- The binary search of a byte string `k` (`searchIn.c302`): at most `(60 + 23·|k|)·(log₂(hi − lo)
+ 2)`. -/
theorem searchBytes_cost (hP : Includes P searchIn.c302.costDeps)
    (t : Array (List UInt8 × Protocol.Digest)) (k : List UInt8) (H : ℕ) (hH : H < 2 ^ 62)
    (hts : t.size < 2 ^ 64) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchIn.c302.costIdx [enc t, enc k, enc lo, enc hi] ≤
        (60 + 23 * k.length) * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have hcmp := compareBytes_cost P (by includes)
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P searchIn.c302.costIdx [enc t, enc k, enc x.1, enc x.2])
    (60 + 23 * k.length) (60 + 23 * k.length) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchIn.c302.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    cost_simp
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchIn.c302.costEq P hP]
    simp only [show lo < hi by omega, ↓reduceIte]
    cost_simp
    generalize hv : t[(lo + hi) / 2]? = ov
    cases ov with
    | none =>
      left
      dsimp only
      split_ifs <;> omega
    | some v =>
      have hc := hcmp v.1 k
      dsimp only
      generalize compare v.1 k = o2
      cases o2
      · right
        refine ⟨((lo + hi) / 2 + 1, hi), ⟨by omega, hhi⟩, by dsimp only; omega, ?_⟩
        dsimp only
        split_ifs <;> omega
      · left
        dsimp only
        split_ifs <;> omega
      · right
        refine ⟨(lo, (lo + hi) / 2), ⟨hlo, by omega⟩, by dsimp only; omega, ?_⟩
        dsimp only
        split_ifs <;> omega

/-- Byte-string keys of at most `L` bytes. -/
@[expose] def BytesKey (L : ℕ) (k : List UInt8) : Prop := k.length ≤ L

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- `mergeNewer` on byte-string keys (`mergeNewer.c304`): at most `23·L + 27` per entry and `9`. -/
theorem mergeNewerBytes_cost (hP : Includes P mergeNewer.c304.costDeps) (L : ℕ) :
    ∀ (n : ℕ) (a b : List (List UInt8 × Protocol.Digest)), a.length + b.length = n →
      (∀ e ∈ b, BytesKey L e.1) →
      machineCost P mergeNewer.c304.costIdx [enc a, enc b] ≤ (23 * L + 27) * n + 9 := by
  have hcmp := compareLex_cost P (by includes) _ (.fn searchBytesC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchBytesC.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by
      rw [appCost_fn, List.nil_append, searchBytesC.lam0.costEq P (by includes)]
      split_ifs <;> omega)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn hb
  cases a with
  | nil => rw [mergeNewer.c304.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewer.c304.costEq_cons P hP]
    cases b with
    | nil => simp
    | cons y b =>
      dsimp only
      have hy : y.1.length ≤ L := hb y (by simp)
      have hc := hcmp x.1 y.1
      have h1 := ih (a.length + (b.length + 1)) (by simp at hn; omega) a (y :: b) (by simp) hb
      have h2 := ih (a.length + b.length) (by simp at hn; omega) a b rfl
        (fun e he ↦ hb e (by simp [he]))
      have h3 := ih (a.length + 1 + b.length) (by simp at hn; omega) (x :: a) b (by simp)
        (fun e he ↦ hb e (by simp [he]))
      simp only [List.length_cons] at hn h1 h3
      have : (9 + 14) * y.1.length ≤ 23 * L := by omega
      generalize compare x.1 y.1 = o2
      subst hn
      cases o2 <;> dsimp only <;> nlinarith

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- Two levels merged (`levelMergeBytesC`): at most `23·L + 31` per entry and `26`. -/
theorem levelMergeBytes_cost (hP : Includes P levelMergeBytesC.costDeps) (L : ℕ)
    (l l' : Level (List UInt8) Protocol.Digest) (hQ : KeysIn (BytesKey L) [l, l'])
    (hw : l.weight < 2 ^ 64) (hw' : l'.weight < 2 ^ 64) :
    machineCost P levelMergeBytesC.costIdx [enc l, enc l'] ≤
      26 + (23 * L + 31) * (l.entries.size + l'.entries.size) := by
  rw [levelMergeBytesC.costEq P hP, limbs_of_lt hw, limbs_of_lt hw']
  have hm := mergeNewerBytes_cost P (by includes) L _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList] at hm hlen
  simp only [max_self]
  nlinarith

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **An insertion into the first answers' map, amortized** (`carry.c307`). -/
theorem carryBytes_amortized (hP : Includes P carry.c307.costDeps) (L D : ℕ) (hD : D < 64)
    (m : SortedMap (List UInt8) Protocol.Digest) (hm : smGood m)
    (hQ : KeysIn (BytesKey L) m.levels) (hN : smWeightSum m < 2 ^ D)
    (l : Level (List UInt8) Protocol.Digest) (hw : l.weight = 1) (hs : l.entries.size = 1)
    (hk : ∀ e ∈ l.entries, BytesKey L e.1) :
    machineCost P carry.c307.costIdx [enc l, enc m.levels] +
        (23 * L + 31) * potential D (carry l m.levels) ≤
      (23 * L + 31) * potential D m.levels + (23 * L + 31) * D + 40 * (m.levels.length + 1) := by
  have h64 : 2 ^ D < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hD
  refine insert_amortized (BytesKey L) (fun l ls ↦ machineCost P carry.c307.costIdx [enc l, enc ls])
    40 (23 * L + 31) D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carry.c307.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carry.c307.costEq_cons P hP, limbs_of_lt (by omega : l.weight < 2 ^ 64),
      limbs_of_lt (by omega : l'.weight < 2 ^ 64)]
    simp only [hne, ↓reduceIte]
    omega
  · intro l l' ls h1 heq hQ2
    have := levelMergeBytes_cost P (by includes) L l l' hQ2 (by omega) (by omega)
    rw [carry.c307.costEq_cons P hP, limbs_of_lt (by omega : l.weight < 2 ^ 64),
      limbs_of_lt (by omega : l'.weight < 2 ^ 64)]
    simp only [heq, ↓reduceIte]
    omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- A lookup in the first answers' map (`getBytesC`): a binary search per level. -/
theorem getBytes_cost (hP : Includes P getBytesC.costDeps)
    (m : SortedMap (List UInt8) Protocol.Digest) (H : ℕ) (hH : H < 2 ^ 62)
    (hm : ∀ l ∈ m.levels, l.entries.size ≤ H) (k : List UInt8) :
    machineCost P getBytesC.costIdx [enc m, enc k] ≤
      m.levels.length * (17 + (60 + 23 * k.length) * (Nat.log2 H + 2)) + 9 := by
  have hlam : ∀ l ∈ m.levels, appCost P (.fn getBytesC.lam0.costIdx [enc k]) [enc l] ≤
      8 + (60 + 23 * k.length) * (Nat.log2 H + 2) := by
    intro l hl
    rw [appCost_fn, List.singleton_append, getBytesC.lam0.costEq P (by includes)]
    have := searchBytes_cost P (by includes) l.entries k H hH (by have := hm l hl; omega)
      0 l.entries.size (by omega) (hm l hl)
    have := log2_mono (show l.entries.size - 0 ≤ H by have := hm l hl; omega)
    have : (60 + 23 * k.length) * (Nat.log2 (l.entries.size - 0) + 2) ≤
        (60 + 23 * k.length) * (Nat.log2 H + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hfs := findSome_cost P (by includes) _
    (.fn getBytesC.lam0.costIdx [enc k])
    (fun a ↦ RunsApp.of_spec (getBytesC.lam0.costSpec P (by includes) _ a)) _ m.levels hlam
  rw [getBytesC.costEq P hP]
  nlinarith

end

end LeanVM.Cost.Bounds
