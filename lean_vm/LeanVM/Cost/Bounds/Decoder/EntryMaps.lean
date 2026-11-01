module

public import LeanVM.Cost.Bounds.Transcript
public import LeanVM.Cost.Decoder.EntryTable
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# Bound: the entry table's sorted maps, compiled

The two sorted maps of the replayed frame map (`Cost/Decoder/EntryTable.lean`), at the stable
names compiled there: the pc table's (`ℕ` keys, `searchInPcC` … `getPcC`) and the entry table's
(`CallKey` keys: the callee's index and the codes of the call's words, `searchInKeyC` …
`insertIfNewKeyC`). As the transcript's maps (`Bounds/Transcript.lean`): a binary search per
level, a merge per entry, an insertion amortized by the potential (`Bounds/SortedMap.lean`).

* a call key's comparison: the index, then the two lists of codes lexicographically
  (`compareCodes_cost`, `tripleCmp_cost`: `53` per code of the second list), at most
  `keyCmpPrice k = 67·(|args| + |rets|) + 38` against the key `k` searched;
* `searchInKey_cost`, `getKey_cost`: a lookup of `k` in a good map of fewer than `2^D`
  insertions, at most `D·(17 + (keyCmpPrice k + 60)·(D + 2)) + 9`;
* `carryKey_amortized`, `insertIfNewKey_amortized`: an insertion of a key of at most `L` codes
  per list, amortized `b·D + (42 + …)`, `b = 134·L + 71` per merged entry;
* the same for the pc table's `ℕ` keys (`getPc_cost`, `insertPc_amortized`), `b = 32`.

Keys are word-sized (`KeyOK L`, `NatKey`): the comparisons' limbs are `1`. Positions and weights
stay below `2^63` (`D ≤ 62`), one limb each.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Guest.Located

public section

attribute [local instance] lexOrd

variable (P : MachineProgram)

/-! ## Keys -/

/-- A code triple of words. -/
@[expose] def TripleOK (x : ℕ × ℕ × ℕ) : Prop := x.1 < 2 ^ 64 ∧ x.2.1 < 2 ^ 64 ∧ x.2.2 < 2 ^ 64

/-- **A call key of at most `L` codes per list**, every number word-sized. -/
@[expose] def KeyOK (L : ℕ) (k : CallKey) : Prop :=
  k.1 < 2 ^ 64 ∧ k.2.1.length ≤ L ∧ k.2.2.length ≤ L ∧ (∀ x ∈ k.2.1, TripleOK x) ∧
    ∀ x ∈ k.2.2, TripleOK x

/-- A word-sized key of the pc table. -/
@[expose] def NatKey (k : ℕ) : Prop := k < 2 ^ 64

/-- The price of comparing a key with the key `k` searched: `67` per code of `k`, `38`. -/
@[expose] def keyCmpPrice (k : CallKey) : ℕ := 67 * (k.2.1.length + k.2.2.length) + 38

/-- Two code triples compared (`searchInKeyC.lam0`): at most `53`. -/
theorem tripleCmp_cost (hP : Includes P searchInKeyC.lam0.costDeps) (a b : ℕ × ℕ × ℕ)
    (ha : TripleOK a) (hb : TripleOK b) :
    machineCost P searchInKeyC.lam0.costIdx [encodeValue a, encodeValue b] ≤ 53 := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  rw [searchInKeyC.lam0.costEq P hP, limbs_of_lt a1, limbs_of_lt b1, limbs_of_lt a2,
    limbs_of_lt b2, limbs_of_lt a3, limbs_of_lt b3]
  simp only [max_self]
  generalize compareOn (fun x ↦ x.1) a b = o1
  generalize compareOn (fun x ↦ x.1) a.2 b.2 = o2
  cases o1 <;> cases o2 <;> dsimp only <;> split_ifs <;> omega

/-- Two lists of code triples compared (`compareLex` with `searchInKeyC.lam0`): `67` per triple of
the second, `5`. -/
theorem compareCodes_cost (hP : Includes P Auto.List.compareLex.c284.costDeps)
    (hP' : Includes P searchInKeyC.lam0.costDeps) :
    ∀ (a b : List (ℕ × ℕ × ℕ)), (∀ x ∈ a, TripleOK x) → (∀ x ∈ b, TripleOK x) →
      machineCost P Auto.List.compareLex.c284.costIdx
          [.closure searchInKeyC.lam0.costIdx [], encodeValue a, encodeValue b] ≤
        67 * b.length + 5 := by
  have hc : ∀ x y : ℕ × ℕ × ℕ, RunsApp P (.closure searchInKeyC.lam0.costIdx [])
      [encodeValue x, encodeValue y] (encodeValue (compare x y)) :=
    fun x y ↦ RunsApp.of_spec (searchInKeyC.lam0.costSpec P hP' x y)
  intro a
  induction a with
  | nil =>
    intro b _ _
    rw [Auto.List.compareLex.c284.costEq P hP compare _ hc]
    cases b <;> simp
  | cons x a ih =>
    intro b ha hb
    rw [Auto.List.compareLex.c284.costEq P hP compare _ hc]
    cases b with
    | nil => simp
    | cons y b =>
      have h1 := ih b (fun z hz ↦ ha z (by simp [hz])) (fun z hz ↦ hb z (by simp [hz]))
      have h2 : appCost P (.closure searchInKeyC.lam0.costIdx []) [encodeValue x, encodeValue y] ≤
          53 := by
        rw [appCost_fn, List.nil_append]
        exact tripleCmp_cost P hP' x y (ha x (by simp)) (hb y (by simp))
      simp only [List.length_cons]
      generalize compare x y = o
      cases o <;> dsimp only <;> omega

/-! ## The entry table's map: `CallKey` keys -/

/-- **The binary search of a key `k`** (`searchInKeyC`), the entries' keys of at most `L` codes:
at most `(keyCmpPrice k + 60)·(log₂(hi − lo) + 2)`. -/
theorem searchInKey_cost (hP : Includes P searchInKeyC.costDeps) (L : ℕ)
    (t : Array (CallKey × K)) (ht : ∀ e ∈ t, KeyOK L e.1) (k : CallKey) {L' : ℕ} (hk : KeyOK L' k)
    (H : ℕ) (hH : H ≤ 2 ^ 62) (hts : t.size ≤ H) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchInKeyC.costIdx [encodeValue t, encodeValue k, encodeValue lo,
        encodeValue hi] ≤ (keyCmpPrice k + 60) * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have hcmp := compareCodes_cost P (by includes) (by includes)
  obtain ⟨hk1, -, -, hka, hkr⟩ := hk
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P searchInKeyC.costIdx [encodeValue t, encodeValue k, encodeValue x.1,
      encodeValue x.2])
    (keyCmpPrice k + 60) (keyCmpPrice k + 60) ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchInKeyC.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    rw [limbs_of_lt (by omega : lo < 2 ^ 64), limbs_of_lt (by omega : hi < 2 ^ 64)]
    unfold keyCmpPrice
    simp only [max_self]
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchInKeyC.costEq P hP]
    simp only [show lo < hi by omega, ↓reduceIte]
    rw [limbs_of_lt (by omega : lo < 2 ^ 64), limbs_of_lt (by omega : hi < 2 ^ 64),
      limbs_of_lt (by omega : lo + hi < 2 ^ 64), limbs_of_lt (by omega : (lo + hi) / 2 < 2 ^ 64),
      limbs_of_lt (by omega : t.size < 2 ^ 64)]
    simp only [max_self]
    generalize hv : t[(lo + hi) / 2]? = ov
    cases ov with
    | none =>
      left
      dsimp only
      unfold keyCmpPrice
      split_ifs <;> omega
    | some v =>
      have hvt : v ∈ t := Array.mem_of_getElem? hv
      obtain ⟨hv1, -, -, hva, hvr⟩ := ht v hvt
      have hc1 := hcmp v.1.2.1 k.2.1 hva hka
      have hc2 := hcmp v.1.2.2 k.2.2 hvr hkr
      dsimp only
      rw [limbs_of_lt hv1, limbs_of_lt hk1]
      simp only [max_self]
      unfold keyCmpPrice
      generalize compareOn (fun x ↦ x.1) v.1 k = o1
      generalize compareOn (fun x ↦ x.1) v.1.2 k.2 = o3
      generalize compare v.1 k = o2
      cases o2
      · right
        refine ⟨((lo + hi) / 2 + 1, hi), ⟨by omega, hhi⟩, by dsimp only; omega, ?_⟩
        dsimp only
        cases o1 <;> cases o3 <;> dsimp only <;> split_ifs <;> omega
      · left
        dsimp only
        cases o1 <;> cases o3 <;> dsimp only <;> split_ifs <;> omega
      · right
        refine ⟨(lo, (lo + hi) / 2), ⟨hlo, by omega⟩, by dsimp only; omega, ?_⟩
        dsimp only
        cases o1 <;> cases o3 <;> dsimp only <;> split_ifs <;> omega

/-- `mergeNewer` on call keys (`mergeNewerKeyC`), both lists' keys of at most `L` codes: at most
`134·L + 67` per entry and `9`. -/
theorem mergeNewerKey_cost (hP : Includes P mergeNewerKeyC.costDeps) (L : ℕ) :
    ∀ (n : ℕ) (a b : List (CallKey × K)), a.length + b.length = n →
      (∀ e ∈ a, KeyOK L e.1) → (∀ e ∈ b, KeyOK L e.1) →
      machineCost P mergeNewerKeyC.costIdx [encodeValue a, encodeValue b] ≤
        (134 * L + 67) * n + 9 := by
  have hcmp := compareCodes_cost P (by includes) (by includes)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn ha hb
  cases a with
  | nil => rw [mergeNewerKeyC.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewerKeyC.costEq_cons P hP]
    cases b with
    | nil => simp
    | cons y b =>
      dsimp only
      obtain ⟨hx1, -, -, hxa, hxr⟩ := ha x (by simp)
      obtain ⟨hy1, hyl1, hyl2, hya, hyr⟩ := hb y (by simp)
      have hc1 := hcmp x.1.2.1 y.1.2.1 hxa hya
      have hc2 := hcmp x.1.2.2 y.1.2.2 hxr hyr
      have ha' : ∀ e ∈ a, KeyOK L e.1 := fun e he ↦ ha e (by simp [he])
      have hb' : ∀ e ∈ b, KeyOK L e.1 := fun e he ↦ hb e (by simp [he])
      have h1 := ih (a.length + (b.length + 1)) (by simp at hn; omega) a (y :: b) (by simp) ha' hb
      have h2 := ih (a.length + b.length) (by simp at hn; omega) a b rfl ha' hb'
      have h3 := ih (a.length + 1 + b.length) (by simp at hn; omega) (x :: a) b (by simp) ha hb'
      simp only [List.length_cons] at hn h1 h3
      rw [limbs_of_lt hx1, limbs_of_lt hy1]
      simp only [max_self]
      have : 67 * y.1.2.1.length + 67 * y.1.2.2.length ≤ 134 * L := by omega
      subst hn
      have e1 : (134 * L + 67) * (a.length + (b.length + 1)) =
          (134 * L + 67) * (a.length + b.length) + (134 * L + 67) := by ring
      have e3 : (134 * L + 67) * (a.length + 1 + b.length) =
          (134 * L + 67) * (a.length + b.length) + (134 * L + 67) := by ring
      have e0 : (134 * L + 67) * (a.length + 1 + (b.length + 1)) =
          (134 * L + 67) * (a.length + b.length) + 2 * (134 * L + 67) := by ring
      rw [e1] at h1
      rw [e3] at h3
      rw [e0]
      generalize (134 * L + 67) * (a.length + b.length) = X at h1 h2 h3 ⊢
      generalize compareOn (fun x ↦ x.1) x.1 y.1 = o1
      generalize compareOn (fun x ↦ x.1) x.1.2 y.1.2 = o3
      generalize compare x.1 y.1 = o2
      cases o1 <;> cases o3 <;> dsimp only <;> cases o2 <;> dsimp only <;> split_ifs <;> omega

/-- Two levels merged (`levelMergeKeyC`): at most `134·L + 71` per entry and `26`, the weights
word-sized. -/
theorem levelMergeKey_cost (hP : Includes P levelMergeKeyC.costDeps) (L : ℕ)
    (l l' : Level CallKey K) (hQ : KeysIn (KeyOK L) [l, l']) (hw : l.weight < 2 ^ 64)
    (hw' : l'.weight < 2 ^ 64) :
    machineCost P levelMergeKeyC.costIdx [encodeValue l, encodeValue l'] ≤
      26 + (134 * L + 71) * (l.entries.size + l'.entries.size) := by
  rw [levelMergeKeyC.costEq P hP, limbs_of_lt hw, limbs_of_lt hw']
  have hm := mergeNewerKey_cost P (by includes) L _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l (by simp) e (by simpa using he))
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList, max_self] at hm hlen ⊢
  nlinarith

/-- **An insertion into the entry table's map, amortized** (`carryKeyC`), below `2^D ≤ 2^62`
insertions. -/
theorem carryKey_amortized (hP : Includes P carryKeyC.costDeps) (L D : ℕ) (hD : D ≤ 62)
    (m : SortedMap CallKey K) (hm : smGood m) (hQ : KeysIn (KeyOK L) m.levels)
    (hN : smWeightSum m < 2 ^ D) (l : Level CallKey K) (hw : l.weight = 1)
    (hs : l.entries.size = 1) (hk : ∀ e ∈ l.entries, KeyOK L e.1) :
    machineCost P carryKeyC.costIdx [encodeValue l, encodeValue m.levels] +
        (134 * L + 71) * potential D (carry l m.levels) ≤
      (134 * L + 71) * potential D m.levels + (134 * L + 71) * D + 42 * (m.levels.length + 1) := by
  have h64 : 2 ^ D < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine insert_amortized (KeyOK L)
    (fun l ls ↦ machineCost P carryKeyC.costIdx [encodeValue l, encodeValue ls])
    42 (134 * L + 71) D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carryKeyC.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carryKeyC.costEq_cons P hP, limbs_of_lt (by omega : l.weight < 2 ^ 64),
      limbs_of_lt (by omega : l'.weight < 2 ^ 64)]
    simp only [hne, ↓reduceIte, max_self]
    omega
  · intro l l' ls h1 heq hQ2
    have := levelMergeKey_cost P (by includes) L l l' hQ2 (by omega) (by omega)
    rw [carryKeyC.costEq_cons P hP, limbs_of_lt (by omega : l.weight < 2 ^ 64),
      limbs_of_lt (by omega : l'.weight < 2 ^ 64)]
    simp only [heq, ↓reduceIte, max_self]
    omega

/-- **A lookup of `k`** (`getKeyC`) in a map of at most `D` levels of at most `2^D` entries: a
binary search per level, at most `D·(17 + (keyCmpPrice k + 60)·(D + 2)) + 9`. -/
theorem getKey_cost (hP : Includes P getKeyC.costDeps) (L D : ℕ) (hD : D ≤ 62)
    (m : SortedMap CallKey K) (hQ : KeysIn (KeyOK L) m.levels) (hlev : m.levels.length ≤ D)
    (hsz : ∀ l ∈ m.levels, l.entries.size ≤ 2 ^ D) (k : CallKey) {L' : ℕ} (hk : KeyOK L' k) :
    machineCost P getKeyC.costIdx [encodeValue m, encodeValue k] ≤
      D * (17 + (keyCmpPrice k + 60) * (D + 2)) + 9 := by
  have hH : 2 ^ D ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hD
  have hlam : ∀ l ∈ m.levels, appCost P (.closure getKeyC.lam0.costIdx [encodeValue k])
      [encodeValue l] ≤ 8 + (keyCmpPrice k + 60) * (D + 2) := by
    intro l hl
    rw [appCost_fn, List.singleton_append, getKeyC.lam0.costEq P (by includes)]
    have := searchInKey_cost P (by includes) L l.entries (fun e he ↦ hQ l hl e he) k hk (2 ^ D) hH
      (hsz l hl) 0 l.entries.size (Nat.zero_le _) (hsz l hl)
    have h2 : Nat.log2 (l.entries.size - 0) ≤ D := by
      have := log2_mono (show l.entries.size - 0 ≤ 2 ^ D by have := hsz l hl; omega)
      rwa [Nat.log2_two_pow] at this
    have : (keyCmpPrice k + 60) * (Nat.log2 (l.entries.size - 0) + 2) ≤
        (keyCmpPrice k + 60) * (D + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hfs := findSome_cost P (by includes) _ (.closure getKeyC.lam0.costIdx [encodeValue k])
    (fun a ↦ RunsApp.of_spec (getKeyC.lam0.costSpec P (by includes) _ a)) _ m.levels hlam
  rw [getKeyC.costEq P hP]
  generalize (keyCmpPrice k + 60) * (D + 2) = X at hfs ⊢
  have h1 := Nat.mul_le_mul_left (8 + X + 9) hlev
  have h2 : (8 + X + 9) * D = D * (17 + X) := by ring
  omega

/-- The entry table's invariant, `r` insertions left: a good map of keys of at most `L` codes,
`r` more insertions keeping it below `2^D`. -/
@[expose] def KeyInv (L D : ℕ) (m : SortedMap CallKey K) (r : ℕ) : Prop :=
  smGood m ∧ KeysIn (KeyOK L) m.levels ∧ smWeightSum m + r ≤ 2 ^ D

/-- The price of a lookup of a key of at most `L` codes per list, below `2^D` insertions. -/
@[expose] def getKeyPrice (L D : ℕ) : ℕ := D * (17 + (134 * L + 98) * (D + 2)) + 9

/-- The amortized price of an insertion if new of a key of at most `L` codes per list. -/
@[expose] def insertKeyPrice (L D : ℕ) : ℕ := getKeyPrice L D + (134 * L + 71) * D + 42 * D + 72

/-- A lookup of a key of at most `L` codes per list: at most `getKeyPrice L D`. -/
theorem getKey_cost_le (hP : Includes P getKeyC.costDeps) (L D : ℕ) (hD : D ≤ 62)
    (m : SortedMap CallKey K) (r : ℕ) (hm : KeyInv L D m (r + 1)) (k : CallKey) (hk : KeyOK L k) :
    machineCost P getKeyC.costIdx [encodeValue m, encodeValue k] ≤ getKeyPrice L D := by
  obtain ⟨hg, hQ, hw⟩ := hm
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg (D := D) (by omega)
  have := getKey_cost P hP L D hD m hQ hlev (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) k hk
  have hkc : keyCmpPrice k ≤ 134 * L + 38 := by
    unfold keyCmpPrice; have := hk.2.1; have := hk.2.2.1; omega
  have h1 : (keyCmpPrice k + 60) * (D + 2) ≤ (134 * L + 98) * (D + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have : D * (17 + (keyCmpPrice k + 60) * (D + 2)) ≤ D * (17 + (134 * L + 98) * (D + 2)) :=
    Nat.mul_le_mul_left _ (by omega)
  unfold getKeyPrice
  omega

/-- **An insertion if new, amortized** (`insertIfNewKeyC`): a key of at most `L` codes per list. -/
theorem insertIfNewKey_amortized (hP : Includes P insertIfNewKeyC.costDeps) (L D : ℕ) (hD : D ≤ 62)
    (m : SortedMap CallKey K) (r : ℕ) (hm : KeyInv L D m (r + 1)) (k : CallKey) (hk : KeyOK L k)
    (v : K) :
    KeyInv L D (insertIfNew m k v) r ∧
      machineCost P insertIfNewKeyC.costIdx [encodeValue m, encodeValue k, encodeValue v] +
          (134 * L + 71) * potential D (insertIfNew m k v).levels ≤
        (134 * L + 71) * potential D m.levels + insertKeyPrice L D := by
  have hget := getKey_cost_le P (by includes) L D hD m r hm k hk
  obtain ⟨hg, hQ, hw⟩ := hm
  have hN : smWeightSum m < 2 ^ D := by omega
  obtain ⟨hlev, -⟩ := smGood_levels_le hg hN
  rw [insertIfNewKeyC.costEq P hP]
  unfold insertKeyPrice
  by_cases hc : m.contains k = true
  · simp only [insertIfNew, hc, ↓reduceIte]
    refine ⟨⟨hg, hQ, by omega⟩, ?_⟩
    generalize m.get? k = o
    cases o <;> dsimp only <;> nlinarith
  · simp only [insertIfNew, hc, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h1, h2⟩ := smGood_insert hg k v
    refine ⟨⟨h1, keysIn_insert hQ hk v, by omega⟩, ?_⟩
    rw [insertKeyC.costEq P (by includes)]
    have hcarry := carryKey_amortized P (by includes) L D hD m hg hQ hN
      ⟨1, #[(k, v)], by simp [Ascending]⟩ rfl rfl (fun e he ↦ by simp at he; rw [he]; exact hk)
    have hins : (m.insert k v).levels = carry ⟨1, #[(k, v)], by simp [Ascending]⟩ m.levels := rfl
    rw [hins]
    generalize m.get? k = o
    cases o <;> dsimp only <;> nlinarith

/-! ## The pc table's map: `ℕ` keys -/

/-- **The binary search of a pc** (`searchInPcC`): at most `68·(log₂(hi − lo) + 2)`. -/
theorem searchInPc_cost (hP : Includes P searchInPcC.costDeps)
    (t : Array (ℕ × List ℕ)) (ht : ∀ e ∈ t, NatKey e.1) (k : ℕ) (hk : NatKey k)
    (H : ℕ) (hH : H ≤ 2 ^ 62) (hts : t.size ≤ H) :
    ∀ lo hi, lo ≤ H → hi ≤ H →
      machineCost P searchInPcC.costIdx [encodeValue t, encodeValue k, encodeValue lo,
        encodeValue hi] ≤ 68 * (Nat.log2 (hi - lo) + 2) := by
  intro lo hi hlo hhi
  have := le_of_halving (α := ℕ × ℕ) (fun x ↦ x.1 ≤ H ∧ x.2 ≤ H) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P searchInPcC.costIdx [encodeValue t, encodeValue k, encodeValue x.1,
      encodeValue x.2]) 68 68 ?hz ?h (lo, hi) ⟨hlo, hhi⟩
  · dsimp only at this
    nlinarith
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ h0
    dsimp only at *
    rw [searchInPcC.costEq P hP]
    simp only [show ¬lo < hi by omega, ↓reduceIte]
    rw [limbs_of_lt (by omega : lo < 2 ^ 64), limbs_of_lt (by omega : hi < 2 ^ 64)]
    simp only [max_self]
    omega
  · rintro ⟨lo, hi⟩ ⟨hlo, hhi⟩ hpos
    dsimp only at *
    rw [searchInPcC.costEq P hP]
    simp only [show lo < hi by omega, ↓reduceIte]
    rw [limbs_of_lt (by omega : lo < 2 ^ 64), limbs_of_lt (by omega : hi < 2 ^ 64),
      limbs_of_lt (by omega : lo + hi < 2 ^ 64), limbs_of_lt (by omega : (lo + hi) / 2 < 2 ^ 64),
      limbs_of_lt (by omega : t.size < 2 ^ 64)]
    simp only [max_self]
    generalize hv : t[(lo + hi) / 2]? = ov
    cases ov with
    | none =>
      left
      dsimp only
      split_ifs <;> omega
    | some v =>
      have hvt : v ∈ t := Array.mem_of_getElem? hv
      have hv1 : v.1 < 2 ^ 64 := ht v hvt
      have hk1 : k < 2 ^ 64 := hk
      dsimp only
      rw [limbs_of_lt hv1, limbs_of_lt hk1]
      simp only [max_self]
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

/-- `mergeNewer` on pcs (`mergeNewerPcC`): at most `31` per entry and `9`. -/
theorem mergeNewerPc_cost (hP : Includes P mergeNewerPcC.costDeps) :
    ∀ (n : ℕ) (a b : List (ℕ × List ℕ)), a.length + b.length = n →
      (∀ e ∈ a, NatKey e.1) → (∀ e ∈ b, NatKey e.1) →
      machineCost P mergeNewerPcC.costIdx [encodeValue a, encodeValue b] ≤ 31 * n + 9 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn ha hb
  cases a with
  | nil => rw [mergeNewerPcC.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewerPcC.costEq_cons P hP]
    cases b with
    | nil => simp
    | cons y b =>
      dsimp only
      have hx1 : x.1 < 2 ^ 64 := ha x (by simp)
      have hy1 : y.1 < 2 ^ 64 := hb y (by simp)
      have ha' : ∀ e ∈ a, NatKey e.1 := fun e he ↦ ha e (by simp [he])
      have hb' : ∀ e ∈ b, NatKey e.1 := fun e he ↦ hb e (by simp [he])
      have h1 := ih (a.length + (b.length + 1)) (by simp at hn; omega) a (y :: b) (by simp) ha' hb
      have h2 := ih (a.length + b.length) (by simp at hn; omega) a b rfl ha' hb'
      have h3 := ih (a.length + 1 + b.length) (by simp at hn; omega) (x :: a) b (by simp) ha hb'
      simp only [List.length_cons] at hn h1 h3
      rw [limbs_of_lt hx1, limbs_of_lt hy1]
      simp only [max_self]
      generalize compare x.1 y.1 = o2
      subst hn
      cases o2 <;> dsimp only <;> split_ifs <;> omega

/-- Two levels merged (`levelMergePcC`): at most `35` per entry and `26`. -/
theorem levelMergePc_cost (hP : Includes P levelMergePcC.costDeps)
    (l l' : Level ℕ (List ℕ)) (hQ : KeysIn NatKey [l, l']) (hw : l.weight < 2 ^ 64)
    (hw' : l'.weight < 2 ^ 64) :
    machineCost P levelMergePcC.costIdx [encodeValue l, encodeValue l'] ≤
      26 + 35 * (l.entries.size + l'.entries.size) := by
  rw [levelMergePcC.costEq P hP, limbs_of_lt hw, limbs_of_lt hw']
  have hm := mergeNewerPc_cost P (by includes) _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l (by simp) e (by simpa using he))
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList, max_self] at hm hlen ⊢
  omega

/-- **An insertion into the pc table's map, amortized** (`carryPcC`). -/
theorem carryPc_amortized (hP : Includes P carryPcC.costDeps) (D : ℕ) (hD : D ≤ 62)
    (m : SortedMap ℕ (List ℕ)) (hm : smGood m) (hQ : KeysIn NatKey m.levels)
    (hN : smWeightSum m < 2 ^ D) (l : Level ℕ (List ℕ)) (hw : l.weight = 1)
    (hs : l.entries.size = 1) (hk : ∀ e ∈ l.entries, NatKey e.1) :
    machineCost P carryPcC.costIdx [encodeValue l, encodeValue m.levels] +
        35 * potential D (carry l m.levels) ≤
      35 * potential D m.levels + 35 * D + 42 * (m.levels.length + 1) := by
  have h64 : 2 ^ D < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine insert_amortized NatKey
    (fun l ls ↦ machineCost P carryPcC.costIdx [encodeValue l, encodeValue ls])
    42 35 D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carryPcC.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carryPcC.costEq_cons P hP, limbs_of_lt (by omega : l.weight < 2 ^ 64),
      limbs_of_lt (by omega : l'.weight < 2 ^ 64)]
    simp only [hne, ↓reduceIte, max_self]
    omega
  · intro l l' ls h1 heq hQ2
    have := levelMergePc_cost P (by includes) l l' hQ2 (by omega) (by omega)
    rw [carryPcC.costEq_cons P hP, limbs_of_lt (by omega : l.weight < 2 ^ 64),
      limbs_of_lt (by omega : l'.weight < 2 ^ 64)]
    simp only [heq, ↓reduceIte, max_self]
    omega

/-- **A lookup of a pc** (`getPcC`) in a map of at most `D` levels of at most `2^D` entries: at
most `D·(17 + 68·(D + 2)) + 9`. -/
theorem getPc_cost (hP : Includes P getPcC.costDeps) (D : ℕ) (hD : D ≤ 62)
    (m : SortedMap ℕ (List ℕ)) (hQ : KeysIn NatKey m.levels) (hlev : m.levels.length ≤ D)
    (hsz : ∀ l ∈ m.levels, l.entries.size ≤ 2 ^ D) (k : ℕ) (hk : NatKey k) :
    machineCost P getPcC.costIdx [encodeValue m, encodeValue k] ≤ D * (17 + 68 * (D + 2)) + 9 := by
  have hH : 2 ^ D ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hD
  have hlam : ∀ l ∈ m.levels, appCost P (.closure getPcC.lam0.costIdx [encodeValue k])
      [encodeValue l] ≤ 8 + 68 * (D + 2) := by
    intro l hl
    rw [appCost_fn, List.singleton_append, getPcC.lam0.costEq P (by includes)]
    have := searchInPc_cost P (by includes) l.entries (fun e he ↦ hQ l hl e he) k hk (2 ^ D) hH
      (hsz l hl) 0 l.entries.size (Nat.zero_le _) (hsz l hl)
    have h2 : Nat.log2 (l.entries.size - 0) ≤ D := by
      have := log2_mono (show l.entries.size - 0 ≤ 2 ^ D by have := hsz l hl; omega)
      rwa [Nat.log2_two_pow] at this
    omega
  have hfs := findSome_cost P (by includes) _ (.closure getPcC.lam0.costIdx [encodeValue k])
    (fun a ↦ RunsApp.of_spec (getPcC.lam0.costSpec P (by includes) _ a)) _ m.levels hlam
  rw [getPcC.costEq P hP]
  generalize 68 * (D + 2) = X at hfs ⊢
  have h1 := Nat.mul_le_mul_left (8 + X + 9) hlev
  have h2 : (8 + X + 9) * D = D * (17 + X) := by ring
  omega

end

end LeanVM.Cost.Bounds
