module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Samples.CommittedLeaves

/-!
# Bound: the committed leaves

The price of the compiled committed leaves (`Cost/Samples/CommittedLeaves.lean`,
`subtreeLeavesWith (preimageIn idx) w h root`), bottom up:

* the lookup: a word comparison (`9`), `List.compareLex` (`14` per word), the binary search
  (`searchInKeys_cost`: `(100 + 23·|key|)·(log₂ n + 2)`, by `le_of_halving`), a search per level
  (`findSomeLevels_cost`), so one preimage lookup costs `lookupBound idx N =
  40 + |levels|·(18 + 192·(log₂ N + 2))` (`preimageLookup_cost`);
* the leaves: `take`/`drop` (`20` per byte), the fold of a word's bytes (its accumulator below
  `2^56`, so its multiplication is one limb), a word (`350`), `bytesLanes` (`550` per word), a leaf
  (`leafOfWith_cost`);
* the tree (`subtreeLeavesWith_cost`, by `le_of_doubling`) and the top (`committedLeaves_cost`):
  at most `2^h·(2·L + 617·w + 12060 + 8·h) + 7`.

Premises: the index's levels hold at most `N < 2^62` entries, their lengths word-sized
(`WordLevels`), and leaves of `w < 2^61` words; nothing on the height (the limbs of `2^h` are
priced, not assumed one).
-/

namespace LeanVM.Cost.Bounds.Samples

open LeanVM.Cost LeanVM.Cost.Samples LeanVM.Cost.Library LeanVM.Cost.Bounds LeanVM.Parameters
open LeanVM.Extraction LeanVM.Extraction.Fast

/-! The functions compiled on demand, by their short names (`rowGet.c7`: `Auto.…rowGet.c7`). -/
open LeanVM.Cost.Auto.LeanVM.Extraction.Fast

public section

attribute [local instance] lexOrd

variable (P : Program)

/-! ## The lookup: a binary search per level of the sorted map -/

/-- The comparison of two words. -/
theorem cmpWord_cost (hP : Includes P searchInKeys.lam0.costDeps) (a b : UInt64) :
    machineCost P searchInKeys.lam0.costIdx [enc a, enc b] ≤ 9 := by
  rw [searchInKeys.lam0.costEq P hP]
  split_ifs <;> omega

/-- `List.compareLex` on words: `14` per common position and the comparison, `5` at the end. -/
theorem compareLexW_cost (hP : Includes P Auto.List.compareLex.c4.costDeps)
    (cmp : UInt64 → UInt64 → Ordering) (cmpVal : Val)
    (hc : ∀ a b, RunsApp P cmpVal [enc a, enc b] (enc (cmp a b))) (B : ℕ)
    (hB : ∀ a b : UInt64, appCost P cmpVal [enc a, enc b] ≤ B) :
    ∀ (a b : List UInt64), machineCost P Auto.List.compareLex.c4.costIdx [cmpVal, enc a, enc b] ≤
      (B + 14) * b.length + 5 := by
  intro a
  induction a with
  | nil => intro b; rw [Auto.List.compareLex.c4.costEq P hP cmp cmpVal hc]; cases b <;> simp
  | cons x a ih =>
    intro b
    rw [Auto.List.compareLex.c4.costEq P hP cmp cmpVal hc]
    cases b with
    | nil => simp
    | cons y b =>
      have h1 := ih b
      have h2 := hB x y
      simp only [List.length_cons]
      generalize cmp x y = o
      cases o <;> dsimp only <;> nlinarith

/-- The binary search of `k` in `t[lo, hi)` (`searchIn`): at most `C·(log₂(hi − lo) + 2)`,
`C = 100 + 23·|k.1|` the price of one probe (a key comparison of `|k.1|` words and the index
arithmetic), for word-sized indices and keys. -/
theorem searchInKeys_cost (hP : Includes P searchInKeys.costDeps)
    (t : Array ((List UInt64 × ℕ) × Hits)) (k : List UInt64 × ℕ) (H : ℕ) (hH : H < 2 ^ 62)
    (hts : t.size < 2 ^ 64) (ht : ∀ e ∈ t, e.1.2 < 2 ^ 64) (hk : k.2 < 2 ^ 64) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchInKeys.costIdx [enc t, enc k, enc lo, enc hi] ≤
        (100 + 23 * k.1.length) * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have hcmp := compareLexW_cost P (by includes) _ (.fn searchInKeys.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (searchInKeys.lam0.costSpec P (by includes) a b)) 9
    (fun a b ↦ by rw [appCost_fn]; exact cmpWord_cost P (by includes) a b)
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦
      machineCost P searchInKeys.costIdx [enc t, enc k, enc x.1, enc x.2]) (100 + 23 * k.1.length)
    (100 + 23 * k.1.length) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchInKeys.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    cost_simp
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchInKeys.costEq P hP]
    simp only [show lo < hi by omega, ↓reduceIte]
    have hmid : (lo + hi) / 2 < hi := by omega
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

/-- `List.findSome?` over the levels: `9` per level and the closure's price, `3` at the end. -/
theorem findSomeLevels_cost (hP : Includes P Auto.List.findSome?.c21.costDeps)
    (f : Level (List UInt64 × ℕ) Hits → Option Hits) (fVal : Val)
    (hf : ∀ a, RunsApp P fVal [enc a] (enc (f a))) (B : ℕ) :
    ∀ ls : List (Level (List UInt64 × ℕ) Hits), (∀ l ∈ ls, appCost P fVal [enc l] ≤ B) →
      machineCost P Auto.List.findSome?.c21.costIdx [fVal, enc ls] ≤ (B + 9) * ls.length + 3 := by
  intro ls
  induction ls with
  | nil => intro _; rw [Auto.List.findSome?.c21.costEq_nil P hP f fVal hf]; omega
  | cons l ls ih =>
    intro hB
    rw [Auto.List.findSome?.c21.costEq_cons P hP f fVal hf]
    have h1 := ih fun l' hl ↦ hB l' (by simp [hl])
    have h2 := hB l (by simp)
    simp only [List.length_cons]
    generalize f l = o
    cases o <;> dsimp only <;> nlinarith

/-- The sorted map's levels hold at most `N` entries each, of word-sized lengths. -/
def WordLevels (idx : SortedMap (List UInt64 × ℕ) Hits) (N : ℕ) : Prop :=
  ∀ l ∈ idx.levels, l.entries.size ≤ N ∧ ∀ e ∈ l.entries, e.1.2 < 2 ^ 64

/-- **The preimage lookup** (`preimageIn idx d len`): at most
`40 + |levels|·(18 + 192·(log₂ N + 2))`, `N` the largest level. -/
theorem preimageLookup_cost (hP : Includes P committedLeavesC.lam0.costDeps)
    (idx : SortedMap (List UInt64 × ℕ) Hits) (N : ℕ) (hN : N < 2 ^ 62) (hidx : WordLevels idx N)
    (d : LeanVM.Protocol.Digest) (len : ℕ) (hlen : len < 2 ^ 64) :
    machineCost P committedLeavesC.lam0.costIdx [enc idx, enc d, enc len] ≤
      40 + idx.levels.length * (18 + 192 * (Nat.log2 N + 2)) := by
  have hlam : ∀ l ∈ idx.levels, appCost P (.fn SortedMap.get?.c20.lam0.costIdx [enc
    (d.toList, len)]) [enc l] ≤
      9 + 192 * (Nat.log2 N + 2) := by
    intro l hl
    obtain ⟨hs, he⟩ := hidx l hl
    rw [appCost_fn, List.singleton_append,
      SortedMap.get?.c20.lam0.costEq P (by includes)]
    have := searchInKeys_cost P (by includes) l.entries (d.toList, len) N hN (by omega) he hlen
      0 l.entries.size (by omega) hs
    have h4 : (d.toList, len).1.length = 4 := by simp
    rw [h4] at this
    have := log2_mono (show l.entries.size - 0 ≤ N by omega)
    nlinarith
  have hfs :=
    findSomeLevels_cost P (by includes) _ (.fn SortedMap.get?.c20.lam0.costIdx [enc
      (d.toList, len)])
    (fun a ↦ RunsApp.of_spec
      (SortedMap.get?.c20.lam0.costSpec P (by includes) _ a))
    _ idx.levels hlam
  rw [committedLeavesC.lam0.costEq P hP,
    preimageIn.c19.costEq P (by includes),
    SortedMap.get?.c20.costEq P (by includes)]
  simp only [Vector.size_toArray]
  generalize idx.get? (d.toList, len) = o
  generalize idx.getD (d.toList, len) Hits.none = hs
  cases o <;> cases hs <;> dsimp only <;> nlinarith

/-! ## The leaves: byte strings read as words -/

/-- `List.take n` on bytes: at most `20·n + 10`. -/
theorem takeBytes_cost (hP : Includes P Auto.List.take.c16.costDeps) :
    ∀ (n : ℕ) (xs : List UInt8), n < 2 ^ 64 →
      machineCost P Auto.List.take.c16.costIdx [enc n, enc xs] ≤ 20 * n + 10 := by
  intro n
  induction n with
  | zero => intro xs _; rw [Auto.List.take.c16.costEq_zero P hP]; omega
  | succ k ih =>
    intro xs hk
    rw [Auto.List.take.c16.costEq P hP]
    cases xs with
    | nil => cost_simp; omega
    | cons x xs => have := ih xs (by omega); cost_simp; omega

/-- `List.drop n` on bytes: at most `20·n + 10`. -/
theorem dropBytes_cost (hP : Includes P Auto.List.drop.c17.costDeps) :
    ∀ (n : ℕ) (xs : List UInt8), n < 2 ^ 64 →
      machineCost P Auto.List.drop.c17.costIdx [enc n, enc xs] ≤ 20 * n + 10 := by
  intro n
  induction n with
  | zero => intro xs _; rw [Auto.List.drop.c17.costEq_zero P hP]; omega
  | succ k ih =>
    intro xs hk
    rw [Auto.List.drop.c17.costEq P hP]
    cases xs with
    | nil => cost_simp; omega
    | cons x xs => have := ih xs (by omega); cost_simp; omega

/-- `List.foldr` on bytes: `10` per byte and the closure's price at the byte and the fold of the
bytes after it, `3` at the end. -/
theorem foldrBytes_cost (hP : Includes P Auto.List.foldr.c14.costDeps) (f : UInt8 → ℕ → ℕ)
    (fVal : Val) (hf : ∀ a b, RunsApp P fVal [enc a, enc b] (enc (f a b))) (B init : ℕ) :
    ∀ l : List UInt8, (∀ x tl, x :: tl <:+ l → appCost P fVal [enc x, enc (tl.foldr f init)] ≤ B) →
      machineCost P Auto.List.foldr.c14.costIdx [fVal, enc init, enc l] ≤
        (B + 10) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.foldr.c14.costEq_nil P hP f fVal hf]; omega
  | cons x l ih =>
    intro hB
    rw [Auto.List.foldr.c14.costEq_cons P hP f fVal hf]
    have h1 := ih fun y tl h ↦ hB y tl (h.trans (List.suffix_cons x l))
    have h2 := hB x l List.suffix_rfl
    simp only [List.length_cons]
    nlinarith

theorem foldr_bytes_lt (l : List UInt8) :
    l.foldr (fun x acc ↦ x.toNat + 256 * acc) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have := x.toNat_lt
    simp only [List.foldr_cons, List.length_cons, pow_succ]
    nlinarith

/-- **A word of bytes** (`bytesWord`): at most `350`. -/
theorem bytesWord_cost (hP : Includes P Auto.LeanVM.Extraction.bytesWord.c13.costDeps)
    (b : List UInt8) : machineCost P Auto.LeanVM.Extraction.bytesWord.c13.costIdx [enc b] ≤
      350 := by
  rw [Auto.LeanVM.Extraction.bytesWord.c13.costEq P hP]
  have ht := takeBytes_cost P (by includes) 8 b (by norm_num)
  have hl : (b.take 8).length ≤ 8 := List.length_take_le _ _
  have hf :=
    foldrBytes_cost P (by includes) _ (.fn Auto.LeanVM.Extraction.bytesWord.c13.lam0.costIdx [])
    (fun a acc ↦ RunsApp.of_spec
      (Auto.LeanVM.Extraction.bytesWord.c13.lam0.costSpec P (by includes) a acc)) 10 0 (b.take 8)
    (fun x tl h ↦ by
      have hlen : tl.length ≤ 7 := by have := h.length_le; simp at this; omega
      have hacc := foldr_bytes_lt tl
      have : 256 ^ tl.length ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) hlen
      have hx := x.toNat_lt
      rw [appCost_fn, List.nil_append,
        Auto.LeanVM.Extraction.bytesWord.c13.lam0.costEq P (by includes)]
      cost_simp
      omega)
  nlinarith

theorem length_bytesLanes (L : ℕ) (b : List UInt8) :
    (LeanVM.Extraction.bytesLanes L b).length = L :=
  LeanVM.Cost.Samples.length_bytesLanes L b

/-- **The first `n` words of bytes** (`bytesLanes`): at most `550·n + 10`. -/
theorem bytesLanes_cost (hP : Includes P Auto.LeanVM.Extraction.bytesLanes.c12.costDeps) :
    ∀ (n : ℕ) (b : List UInt8), n < 2 ^ 64 →
      machineCost P Auto.LeanVM.Extraction.bytesLanes.c12.costIdx [enc n, enc b] ≤
        550 * n + 10 := by
  intro n
  induction n with
  | zero => intro b _; rw [Auto.LeanVM.Extraction.bytesLanes.c12.costEq_zero P hP]; omega
  | succ k ih =>
    intro b hk
    rw [Auto.LeanVM.Extraction.bytesLanes.c12.costEq P hP]
    have := ih (b.drop 8) (by omega)
    have := bytesWord_cost P (by includes) b
    have := dropBytes_cost P (by includes) 8 b (by norm_num)
    cost_simp
    omega

/-- `List.map` of words to `K` by `K.ofLane` (a closure of price `1`): `12` per word. -/
theorem mapLanes_cost (hP : Includes P Auto.List.map.c10.costDeps) (f : UInt64 → K) (fVal : Val)
    (hf : ∀ a, RunsApp P fVal [enc a] (enc (f a))) (B : ℕ)
    (hB : ∀ a : UInt64, appCost P fVal [enc a] ≤ B) :
    ∀ l : List UInt64, machineCost P Auto.List.map.c10.costIdx [fVal, enc l] ≤
      (B + 12) * l.length + 3 := by
  intro l
  induction l with
  | nil => rw [Auto.List.map.c10.costEq_nil P hP f fVal hf]; omega
  | cons x l ih =>
    rw [Auto.List.map.c10.costEq_cons P hP f fVal hf]
    have := hB x
    simp only [List.length_cons]
    nlinarith

/-- `List.replicate n a` in `K`: at most `17·n + 10`. -/
theorem replicateK_cost (hP : Includes P Auto.List.replicate.c9.costDeps) (a : K) :
    ∀ n : ℕ, n < 2 ^ 64 → machineCost P Auto.List.replicate.c9.costIdx [enc n, enc a] ≤
      17 * n + 10 := by
  intro n
  induction n with
  | zero => intro _; rw [Auto.List.replicate.c9.costEq_zero P hP]; omega
  | succ k ih =>
    intro hk
    rw [Auto.List.replicate.c9.costEq P hP]
    have := ih (by omega)
    cost_simp
    omega

/-- **A leaf** (`leafOfWith pre w d`): at most `L + 600·w + 30`, `L` a bound of `pre`'s price. -/
theorem leafOfWith_cost (hP : Includes P leafOfWith.c8.costDeps)
    (pre : LeanVM.Protocol.Digest → ℕ → Option (List UInt8)) (preVal : Val)
    (hpre : ∀ d n, RunsApp P preVal [enc d, enc n] (enc (pre d n))) (L : ℕ)
    (hL : ∀ (d : LeanVM.Protocol.Digest) (n : ℕ), n < 2 ^ 64 → appCost P preVal [enc d, enc n] ≤ L)
    (w : ℕ) (hw : w < 2 ^ 61) (d : LeanVM.Protocol.Digest) :
    machineCost P leafOfWith.c8.costIdx [preVal, enc w, enc d] ≤
      L + 600 * w + 30 := by
  rw [leafOfWith.c8.costEq P hP pre preVal hpre]
  have := hL d (8 * w) (by omega)
  have := replicateK_cost P (by includes) 0 w (by omega)
  generalize pre d (8 * w) = o
  cases o with
  | none => cost_simp; omega
  | some val =>
    have := bytesLanes_cost P (by includes) w val (by omega)
    have :=
      mapLanes_cost P (by includes) _ (.fn leafOfWith.c8.lam0.costIdx [])
      (fun a ↦ RunsApp.of_spec
        (leafOfWith.c8.lam0.costSpec P (by includes) a)) 1
      (fun a ↦ by
        rw [appCost_fn, List.nil_append,
          leafOfWith.c8.lam0.costEq P (by includes)])
      (LeanVM.Extraction.bytesLanes w val)
    rw [length_bytesLanes] at this
    cost_simp
    omega

theorem size_subtreeLeavesWith (pre : LeanVM.Protocol.Digest → ℕ → Option (List UInt8)) (w : ℕ) :
    ∀ h d, (subtreeLeavesWith pre w h d).size = 2 ^ h := by
  intro h
  induction h with
  | zero => intro d; simp [subtreeLeavesWith]
  | succ h ih =>
    intro d
    simp only [subtreeLeavesWith]
    split <;> simp [ih, pow_succ, mul_two]

/-- **The subtree's leaves** (`subtreeLeavesWith pre w h d`): with `T` its price,
`T + a ≤ 2^h·(a + b + 8·h)`, `a = L + 17·w + 12000` (an inner node) and `b = L + 600·w + 60`
(a leaf), `L` a bound of `pre`'s price. -/
theorem subtreeLeavesWith_cost
    (hP : Includes P subtreeLeavesWith.c7.costDeps)
    (pre : LeanVM.Protocol.Digest → ℕ → Option (List UInt8)) (preVal : Val)
    (hpre : ∀ d n, RunsApp P preVal [enc d, enc n] (enc (pre d n))) (L : ℕ)
    (hL : ∀ (d : LeanVM.Protocol.Digest) (n : ℕ), n < 2 ^ 64 → appCost P preVal [enc d, enc n] ≤ L)
    (w : ℕ) (hw : w < 2 ^ 61) :
    ∀ (h : ℕ) (d : LeanVM.Protocol.Digest),
      machineCost P subtreeLeavesWith.c7.costIdx [preVal, enc w, enc h, enc d] +
        (L + 17 * w + 12000) ≤
      2 ^ h * ((L + 17 * w + 12000) + (L + 600 * w + 60) + 8 * h) := by
  have hleaf := leafOfWith_cost P (by includes) pre preVal hpre L hL w hw
  have hrep := replicateK_cost P (by includes) 0 w (by omega)
  have hl4 := fun (b : List UInt8) ↦ bytesLanes_cost P (by includes) 4 b (by norm_num)
  have hd32 := fun (b : List UInt8) ↦ dropBytes_cost P (by includes) 32 b (by norm_num)
  apply le_of_doubling (fun (h : ℕ) (d : LeanVM.Protocol.Digest) ↦
    machineCost P subtreeLeavesWith.c7.costIdx [preVal, enc w, enc h, enc d])
  · intro d
    rw [subtreeLeavesWith.c7.costEq P hP pre preVal hpre]
    have := hleaf d
    cost_simp
    omega
  · intro k d
    rw [subtreeLeavesWith.c7.costEq P hP pre preVal hpre]
    have := hL d 64 (by norm_num)
    have hk1 := Nat.lt_two_pow_self (n := k + 1)
    have hk2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hsh : limbs (1 <<< (k + 1)) ≤ 2 ^ (k + 1) + 1 := by
      rw [Nat.shiftLeft_eq, one_mul]; exact limbs_le_add_one _
    have := limbs_le_add_one (k + 1)
    have := limbs_le_add_one k
    simp only [size_subtreeLeavesWith]
    generalize pre d 64 = o
    cases o with
    | none =>
      refine ⟨d, d, ?_⟩
      cost_simp
      omega
    | some val =>
      refine ⟨(splitNode val).1, (splitNode val).2, ?_⟩
      have := hl4 val
      have := hl4 (val.drop 32)
      have := hd32 val
      simp only [length_bytesLanes]
      omega

/-- The preimage lookup's bound (`preimageLookup_cost`). -/
def lookupBound (idx : SortedMap (List UInt64 × ℕ) Hits) (N : ℕ) : ℕ :=
  40 + idx.levels.length * (18 + 192 * (Nat.log2 N + 2))

/-- **The committed leaves** (`subtreeLeavesWith (preimageIn idx) w h root`, compiled as
`committedLeavesC`): at most `2^h·(2·L + 617·w + 12060 + 8·h) + 7`, `L = lookupBound idx N` the
price of one lookup (`40 + |levels|·(18 + 192·(log₂ N + 2))`, `N` the largest level of the
index), for leaves of `w < 2^61` words. -/
theorem committedLeaves_cost (hP : Includes P committedLeavesC.costDeps)
    (idx : SortedMap (List UInt64 × ℕ) Hits) (N : ℕ) (hN : N < 2 ^ 62) (hidx : WordLevels idx N)
    (w h : ℕ) (hw : w < 2 ^ 61) (root : LeanVM.Protocol.Digest) :
    machineCost P committedLeavesC.costIdx [enc idx, enc w, enc h, enc root] ≤
      2 ^ h * (2 * lookupBound idx N + 617 * w + 12060 + 8 * h) + 7 := by
  rw [committedLeavesC.costEq P hP]
  have := subtreeLeavesWith_cost P (by includes) _ (.fn committedLeavesC.lam0.costIdx [enc idx])
    (fun d len ↦ RunsApp.of_spec (committedLeavesC.lam0.costSpec P (by includes) idx d len))
    (lookupBound idx N)
    (fun d len hlen ↦ by
      rw [appCost_fn, List.singleton_append]
      exact preimageLookup_cost P (by includes) idx N hN hidx d len hlen) w hw h root
  have : 2 ^ h * ((lookupBound idx N + 17 * w + 12000) + (lookupBound idx N + 600 * w + 60) + 8 * h)
      = 2 ^ h * (2 * lookupBound idx N + 617 * w + 12060 + 8 * h) := by ring
  omega

end

end LeanVM.Cost.Bounds.Samples
