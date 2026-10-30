/-
  LeanVM.Guest.B1.KeccakGkr.VkStep

  A step of `verify_keccak` (G:2851-2884): the claim's segment weights, its `ι` term, the layer.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkFirst
public import LeanVM.Guest.B1.KeccakGkr.KFormMath
public import LeanVM.Guest.B1.KeccakGkr.LayerHolds

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The tables -/

/-- The round constant bits of a step's segment are the positions `2^i - 1` of `iotaIdx`. -/
theorem iota_bits : ∀ s < 12, ∀ m < 2,
    (List.range 64).filter (fun z ↦ (keccakRC.getD (12 * (m + 1) - s - 1) 0).toNat.testBit z) =
      (iotaIdx s m).map (fun i ↦ 2 ^ i - 1) := by decide +kernel

theorem iotaIdx_ne : ∀ s < 12, ∀ m < 2, iotaIdx s m ≠ [] := by decide +kernel

theorem iotaIdx_sub : ∀ s < 12, ∀ m < 2, ∀ i ∈ iotaIdx s m, i ∈ iotaUsed s ∧ i < 7 := by
  decide +kernel

/-- The words of `g^(22 s)`. -/
theorem vkGw_eq : ∀ s, 1 ≤ s → s < 12 → word (vkGw s) 0 0 = gen ^ (22 * s) := by
  intro s h1 h2
  rw [word_eOfNat, gen_pow_eq_ofK, ← gpowK_eq (by unfold u128Bound; omega)]
  show ofK (K.ofBits (vkGw s)) = ofK (gpowK (22 * s))
  congr 1
  interval_cases s <;> decide +kernel

/-! ## Chains of additions -/

theorem addChainT_holds {vs : List ℕ} (hne : vs ≠ []) {b : ℕ} {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (addChainT vs b) next kret) :
    σ (.n (addChainV vs b)) = (vs.map fun v ↦ σ (.n v)).sum ∧ next := by
  rw [addChainT, holdsList_map_atoms] at h
  obtain ⟨hall, hn⟩ := h
  refine ⟨?_, hn⟩
  have step : ∀ k, k + 1 < vs.length →
      σ (.n (b + k)) = ((vs.take (k + 2)).map fun v ↦ σ (.n v)).sum := by
    intro k
    induction k with
    | zero =>
      intro hk
      have := hall 0 (by omega)
      simp only [Atom.Holds, ↓reduceIte, Nat.add_zero] at this
      rw [Nat.add_zero, this]
      rcases vs with _ | ⟨a, _ | ⟨b', rest⟩⟩
      · simp at hk
      · simp at hk
      · simp
    | succ k ih =>
      intro hk
      have := hall (k + 1) (by omega)
      simp only [Atom.Holds, show k + 1 ≠ 0 by omega, ↓reduceIte,
        show b + (k + 1) - 1 = b + k by omega] at this
      rw [show b + (k + 1) = b + (k + 1) from rfl, this, ih (by omega),
        List.take_add_one (i := k + 2), List.map_append, List.sum_append]
      simp [List.getElem?_eq_getElem (show k + 2 < vs.length by omega),
        List.getD_eq_getElem?_getD]
  rcases vs with _ | ⟨a, rest⟩
  · exact absurd rfl hne
  · rcases rest with _ | ⟨a', rest'⟩
    · simp [addChainV]
    · have := step (rest'.length) (by simp)
      rw [show (a :: a' :: rest').take (rest'.length + 2) = a :: a' :: rest' by simp] at this
      simp only [addChainV, List.length_cons, show ¬ (rest'.length + 1 + 1 ≤ 1) by omega,
        ↓reduceIte, show b + (rest'.length + 1 + 1) - 2 = b + rest'.length by omega]
      exact this

/-! ## The `ι` term from the flips -/

/-- **The `ι` term** (G:2874-2879): per segment the flips of its bits summed, times the segment's
weight read at `st`. -/
theorem iotaSegT_holds {s b c st : ℕ} (hs : s < 12) {F : ℕ → E} {g0 g1 : E}
    (hF : ∀ i ∈ iotaUsed s, σ (.n (flipOf s b i)) = F i)
    (hg0 : ∀ v, LoadHolds rd (σ (.n st)) 0 v → v = g0)
    (hg1 : ∀ v, LoadHolds rd (σ (.n st)) 1 v → v = g1) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (iotaSegT s b c st) next kret) :
    σ (.n (iotaSegEnd s c - 1)) = g0 * ((iotaIdx s 0).map F).sum +
      g1 * ((iotaIdx s 1).map F).sum ∧ next := by
  have hne0 := iotaIdx_ne s hs 0 (by omega)
  have hne1 := iotaIdx_ne s hs 1 (by omega)
  have hsum : ∀ m < 2, (((iotaIdx s m).map (flipOf s b)).map fun v ↦ σ (.n v)).sum =
      ((iotaIdx s m).map F).sum := by
    intro m hm
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun i hi ↦ ?_
    exact hF i (iotaIdx_sub s hs m hm i hi).1
  simp only [iotaSegT, holdsList_append] at h
  obtain ⟨a0, h⟩ := addChainT_holds (by simpa using hne0) h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l0, m0, h⟩ := h
  obtain ⟨a1, h⟩ := addChainT_holds (by simpa using hne1) h
  obtain ⟨l1, m1, e, hn⟩ := h
  refine ⟨?_, hn⟩
  have hlen0 : (iotaIdx s 0).length ≥ 1 := List.length_pos_of_ne_nil hne0
  have hlen1 : (iotaIdx s 1).length ≥ 1 := List.length_pos_of_ne_nil hne1
  simp only [List.length_map] at l0 m0 l1 m1 e a0 a1
  rw [show iotaSegEnd s c - 1 = c + ((iotaIdx s 0).length - 1) + 2 + ((iotaIdx s 1).length - 1) + 2
    by simp only [iotaSegEnd]; omega, e, m0, m1, hg0 _ l0, hg1 _ l1, a0, a1, hsum 0 (by omega),
    hsum 1 (by omega)]

/-! ## The `ι` term as the specification writes it -/

theorem filterMap_ite_eq {p : ℕ → Bool} (f : ℕ → E) (l : List ℕ) :
    l.filterMap (fun z ↦ if p z = true then some (f z) else none) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/-- **`keccakIota`** (V:1990-1995) through the bit positions `2^i - 1` of the round constants. -/
theorem keccakIota_eq {τ s : ℕ} (hs : s < 12) (hτ : 4 ≤ τ) {c : KeccakClaim}
    (hpt : c.point.length = τ - 3) :
    keccakIota τ s c = (eqKernel [c.point.getD (τ - 4) 0]).getD 0 0 *
        ((iotaIdx s 0).map fun i ↦ c.weights.getD (2 ^ i - 1) 0).sum +
      (eqKernel [c.point.getD (τ - 4) 0]).getD 1 0 *
        ((iotaIdx s 1).map fun i ↦ c.weights.getD (2 ^ i - 1) 0).sum := by
  have hd : c.point.drop (τ - 4) = [c.point.getD (τ - 4) 0] := by
    rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp [show τ - 4 + 1 = c.point.length by omega]
  have hm : ∀ m < 2, sumE ((List.range 64).filterMap fun z ↦
      if (keccakRC.getD (keccakDepth * (m + 1) - s - 1) 0).toNat.testBit z then
        some (c.weights.getD z 0) else none) =
      ((iotaIdx s m).map fun i ↦ c.weights.getD (2 ^ i - 1) 0).sum := by
    intro m hm
    rw [filterMap_ite_eq, show keccakDepth = 12 from rfl, iota_bits s hs m hm, List.map_map,
      LeanVM.Protocol.KeccakGkr.sumE_eq_sum]
    rfl
  simp only [keccakIota, keccakSegments_eq, hd]
  rw [LeanVM.Protocol.KeccakGkr.sumE_eq_sum, listSum_range, Finset.sum_range_succ,
    Finset.sum_range_one]
  rw [hm 0 (by omega), hm 1 (by omega)]

/-- The first claim's weight at a word bit `z < 64`: the lane `0` weight times `x^z`. -/
theorem firstWeights_low (lanes : List E) {z : ℕ} (hz : z < 64) :
    (firstWeights lanes).getD z 0 = lanes.getD 0 0 * gen ^ z := by
  rw [firstWeights, List.getD_eq_getElem _ _ (by simp [keccakBits]; omega), List.getElem_map,
    List.getElem_range, Nat.div_eq_of_lt hz, Nat.mod_eq_of_lt hz, gen_pow_eq_eOfNat hz]

theorem sum_flatMap' {α : Type} (l : List α) (g : α → List E) :
    (l.flatMap g).sum = (l.map fun a ↦ (g a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- A sum over `flipOffs`. -/
theorem flipOffs_sum (i : ℕ) (F : ℕ × ℕ → E) :
    ((flipOffs i).map F).sum = F (keccakPi 0, (2 ^ i - 1 + keccakRho.getD 0 0) % 64) +
      ∑ y ∈ range 5, (F (keccakPi (1 + 5 * y), (2 ^ i - 1 + keccakRho.getD (1 + 5 * y) 0) % 64) +
        F (keccakPi (4 + 5 * y), (2 ^ i + keccakRho.getD (4 + 5 * y) 0) % 64)) := by
  simp only [flipOffs, List.map_cons, List.sum_cons, List.map_flatMap]
  rw [← listSum_range]
  congr 1
  rw [sum_flatMap']
  simp only [List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- **A later claim's weight at `2^i - 1`** (lane `0`): `θ`'s transpose through `ρ`, `π` on the
lane and slice tables, as `flipOffs` lists them. -/
theorem laterWeights_low (lanes a6 : List E) (ha : a6.length = 6) {i : ℕ} (hi : i < 7) :
    (laterWeights lanes (eqKernel a6)).getD (2 ^ i - 1) 0 =
      ((flipOffs i).map fun o ↦ lanes.getD o.1 0 * (eqKernel a6).getD o.2 0).sum := by
  have hz : 2 ^ i - 1 < 64 := by
    have : 2 ^ i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have hg := gOf_later lanes a6 ha (l := 0) (by omega) hz
  simp only [Nat.mul_zero, zero_add] at hg
  rw [laterWeights, keccakLinearTranspose_getD _ (by omega), thetaT,
    show (2 ^ i - 1) / 64 = 0 from Nat.div_eq_of_lt hz,
    show (2 ^ i - 1) % 64 = 2 ^ i - 1 from Nat.mod_eq_of_lt hz, hg,
    colL_later lanes a6 ha (by omega) hz, colL_later lanes a6 ha (by omega) (by omega),
    flipOffs_sum]
  have he : ∀ k, (eqKernel a6).getD (k % 64) 0 = eqAt a6 (k % 64) := by
    intro k
    rw [eqKernel_getD, ha]
    simp [Nat.mod_lt k (show 0 < 64 by norm_num)]
  have hs : (2 ^ i - 1 + 1) % 64 = 2 ^ i % 64 := by rw [Nat.sub_add_cancel h1]
  simp only [he, kLane, kRho]
  rw [add_assoc, ← Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun y _ ↦ ?_)
  simp only [show (0 % 5 + 1) % 5 = 1 from rfl, show (0 % 5 + 4) % 5 = 4 from rfl]
  rw [hs, Nat.mod_add_mod]

/-! ## The flips -/

theorem flipsT_noRet (s b : ℕ) (j : ℕ) :
    Stmt.noRetList (flipT s ((iotaUsed s).getD j 0) (b + flipSz s * j)) = true := by
  unfold flipT
  split
  · rfl
  · rw [noRetList_append, noRetList_append, pairsDotT, noRetList_flatten_map _ (fun k ↦ by
      split <;> rfl)]
    rfl

theorem flipOf_mem {s b i : ℕ} (hi : i ∈ iotaUsed s) :
    flipOf s b i = flipV s b ((iotaUsed s).idxOf i) ∧ (iotaUsed s).idxOf i < (iotaUsed s).length ∧
      (iotaUsed s).getD ((iotaUsed s).idxOf i) 0 = i := by
  refine ⟨rfl, List.idxOf_lt_length_of_mem hi, ?_⟩
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hi), List.getElem_idxOf]

/-- **The first claim's flips** (G:2864-2865): lane `0`'s weight times `x^(2^i - 1)`. -/
theorem flipsT_holds0 {b : ℕ} {L0 : E} (hL : ∀ v, LoadHolds rd (σ (.n 274)) 30 v → v = L0)
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (flipsT 0 b) next kret) :
    (∀ i ∈ iotaUsed 0, σ (.n (flipOf 0 b i)) = L0 * gen ^ (2 ^ i - 1)) ∧ next := by
  rw [flipsT, holdsList_range_flatten _ _ (flipsT_noRet 0 b)] at h
  obtain ⟨hall, hn⟩ := h
  refine ⟨fun i hi ↦ ?_, hn⟩
  obtain ⟨e, hj, hgi⟩ := flipOf_mem (b := b) hi
  have hb := hall _ hj
  simp only [flipT, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, hgi,
    show flipSz 0 = 3 from rfl] at hb
  obtain ⟨l, c, m⟩ := hb
  have hi7 : i < 7 := by
    have := List.mem_filter.1 hi; exact List.mem_range.1 this.1
  have hz : 2 ^ i - 1 < 64 := by
    have : 2 ^ i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [e, flipV, show flipSz 0 = 3 from rfl, show b + 3 * (iotaUsed 0).idxOf i + 3 - 1 =
    b + 3 * (iotaUsed 0).idxOf i + 2 by omega, m, c, hL _ l, word_two_pow hz]

theorem flipOffs_length (i : ℕ) : (flipOffs i).length = 11 := by
  simp [flipOffs, List.length_flatMap]

theorem flipOffs_lt (i : ℕ) : ∀ o ∈ flipOffs i, o.1 < 25 ∧ o.2 < 64 := by
  intro o ho
  simp only [flipOffs, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at ho
  rcases ho with rfl | ⟨y, hy, rfl | rfl⟩
  · exact ⟨keccakPi_lt 0 (by norm_num), Nat.mod_lt _ (by norm_num)⟩
  · exact ⟨keccakPi_lt _ (by omega), Nat.mod_lt _ (by norm_num)⟩
  · exact ⟨keccakPi_lt _ (by omega), Nat.mod_lt _ (by norm_num)⟩

theorem sum_map_getD {l : List (ℕ × ℕ)} (F : ℕ × ℕ → E) :
    (l.map F).sum = ∑ k ∈ range l.length, F (l.getD k (0, 0)) := by
  rw [list_sum_eq_range, List.length_map]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have := Finset.mem_range.1 hk
  rw [List.getD_eq_getElem _ _ (by simpa using this), List.getElem_map,
    List.getD_eq_getElem _ _ this]

/-- **A later claim's flips** (G:2866-2872): lane `0`'s weight at `2^i - 1` through `θ`'s
transpose, from the claim's lanes and slices. -/
theorem flipsT_holdsL {s b : ℕ} (hs : s ≠ 0) {lp sl : E} {lanes eZ : List E}
    (hlp : LoadHolds rd (σ (.n 201)) (22 * s + 3) lp) (hsl : LoadHolds rd (σ (.n 201)) (22 * s + 5) sl)
    (hlanes : ReadsAt rd lp lanes) (hlen : lanes.length = 25) (heZ : ReadsAt rd sl eZ)
    (heL : eZ.length = 64) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (flipsT s b) next kret) :
    (∀ i ∈ iotaUsed s, σ (.n (flipOf s b i)) =
      ((flipOffs i).map fun o ↦ lanes.getD o.1 0 * eZ.getD o.2 0).sum) ∧ next := by
  rw [flipsT, holdsList_range_flatten _ _ (flipsT_noRet s b)] at h
  obtain ⟨hall, hn⟩ := h
  refine ⟨fun i hi ↦ ?_, hn⟩
  obtain ⟨e, hj, hgi⟩ := flipOf_mem (b := b) hi
  have hb := hall _ hj
  simp only [flipT, hs, ↓reduceIte, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    hgi, show flipSz s = 46 by simp [flipSz, hs]] at hb
  obtain ⟨l1, l2, hb⟩ := hb
  have eL := loadHolds_unique l1 hlp
  have eS := loadHolds_unique l2 hsl
  set B := b + 46 * (iotaUsed s).idxOf i with hB
  obtain ⟨hd, hc⟩ := pairsDotT_holds (p := .n B) (q := .n (B + 1))
    (P := fun k ↦ lanes.getD ((flipOffs i).getD k (0, 0)).1 0)
    (Q := fun k ↦ eZ.getD ((flipOffs i).getD k (0, 0)).2 0) (fun k hk v hv ↦ by
      have hlt := (flipOffs_lt i ((flipOffs i).getD k (0, 0)) (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)).1
      rw [eL] at hv
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact loadHolds_unique hv (hlanes _ (by omega)))
    (fun k hk v hv ↦ by
      have hlt := (flipOffs_lt i ((flipOffs i).getD k (0, 0)) (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)).2
      rw [eS] at hv
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact loadHolds_unique hv (heZ _ (by omega))) (by rw [flipOffs_length]; omega) hb
  rw [flipOffs_length] at hd
  rw [e, flipV, show flipSz s = 46 by simp [flipSz, hs], show b + 46 * (iotaUsed s).idxOf i + 46 - 1 =
    B + 45 by omega, hc.1, hd, sum_map_getD, flipOffs_length]

/-! ## The layer's call -/

theorem dispatch_layer {first : ℕ} (hf : first < 2) {x : V} {o : ℕ} (ho : o < 2)
    (hx : σ x = gen ^ o) {args rets : List E}
    (hd : ∃ (j : ℕ) (h : j < [layerName first 0, layerName first 1].length),
      σ x = ofK (gpow j) ∧ coreProgram.Rel rd [layerName first 0, layerName first 1][j] args rets) :
    MeaningKeccakLayer first o rd args rets := by
  obtain ⟨j, hj, e, hc⟩ := hd
  simp only [List.length_cons, List.length_nil] at hj
  rw [hx, gen_pow_eq_ofK] at e
  have := gen_pow_inj (a := o) (b := j) (by omega) (by omega)
    (by rw [gen_pow_eq_ofK, gen_pow_eq_ofK, e])
  subst this
  have hn : [layerName first 0, layerName first 1][o] = layerName first o := by
    interval_cases o <;> rfl
  rw [hn] at hc
  exact keccak_layer_holds first hf o ho rd args rets hc

/-! ## A later step -/

theorem claimRec_loads {P : ℕ} {k : ℕ} {v : E} (h : LoadHolds rd (σ (.n 201) * gen ^ (22 * k)) P v) :
    LoadHolds rd (σ (.n 201)) (22 * k + P) v := (loadHolds_mul_gen_pow rd _ _ _ _).1 h

/-- **Step `s ≥ 1`** (G:2851-2884): the claim at `claims·g^(22 s)`, its `ι` term, and
`keccak_layer` on it. -/
theorem stepT_holdsL {s b : ℕ} (hs1 : 1 ≤ s) (hs : s < 12) {c0 c1 c2 c3 c4 cur : ℕ} {τ : ℕ}
    (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (h17 : σ (.n 17) = gen ^ (τ - 4))
    (h43 : σ (.n 43) = gen ^ ((τ - 3) / 2)) (h47 : σ (.n 47) = gen ^ ((τ - 3) % 2))
    (h48 : σ (.n 48) = gen ^ ((τ - 3) / 2 + (τ - 3) % 2)) {c : KeccakClaim}
    (hcr : ClaimRec rd ((0 : ℕ) = 1) (σ (.n 201) * gen ^ (22 * s)) c (τ - 3))
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (stepT s b [c0, c1, c2, c3, c4] cur vkGw) next
      kret) :
    ∃ (xs : List E) (c' : KeccakClaim) (cap' : List E), ReadsAt rd (σ (.n cur)) xs ∧
      RunsTo (verifyKeccakLayer τ s c) ⟨[σ (.n c0), σ (.n c1), σ (.n c2), σ (.n c3), σ (.n c4)], []⟩
        xs c' ⟨cap', []⟩ ∧
      ClaimRec rd ((0 : ℕ) = 1) (σ (.n 201) * gen ^ (22 * (s + 1))) c' (τ - 3) ∧
      ((List.range 6).map fun j ↦ σ (.n (stepEnd s b - 6 + j))) = cap' ++ [σ (.n cur) * gen ^ xs.length] ∧
      next := by
  have hs0 : s ≠ 0 := by omega
  obtain ⟨hmuL, hptL, hval, hkap, hmus, ⟨pp, hpp, hpt⟩, lp, lanes, hlp, hlen, hlanes, hrest⟩ := hcr
  simp only [show ((0 : ℕ) = 1) = False by decide, decide_false, Bool.false_eq_true,
    ↓reduceIte] at hrest
  obtain ⟨lc, sl, loc, hlc, hlocL, hloc, hsl, hslices, hw⟩ := hrest
  simp only [stepT, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨lcp, -, ecp, h⟩ := h
  have ecp' : σ (.n b) = pp := loadHolds_unique lcp (claimRec_loads hpp)
  -- the segment weights
  have hr : LoadHolds rd (σ (.n (b + 2))) (0 + 0) (c.point.getD (τ - 4) 0) := by
    rw [ecp, ecp', h17, loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ (by omega)]
    exact hpt _ (by omega)
  obtain ⟨hseg, h⟩ := eqtreeT_last (rs := [c.point.getD (τ - 4) 0]) (n := 1) le_rfl rfl
    (fun t ht ↦ by obtain rfl : t = 0 := (by omega); simpa using hr) h
  -- the flips
  obtain ⟨hfl, h⟩ := flipsT_holdsL hs0 (claimRec_loads hlp) (claimRec_loads hsl) hlanes hlen
    hslices (by simp [eqKernel_length, hlocL, keccakLocalBits]) h
  -- the ι term
  obtain ⟨hio, h⟩ := iotaSegT_holds (F := fun i ↦ c.weights.getD (2 ^ i - 1) 0)
    (g0 := (eqKernel [c.point.getD (τ - 4) 0]).getD 0 0)
    (g1 := (eqKernel [c.point.getD (τ - 4) 0]).getD 1 0) hs (fun i hi ↦ by
      rw [hfl i hi, hw, laterWeights_low lanes (loc.take 6) (by simp [hlocL, keccakLocalBits])
        (List.mem_range.1 (List.mem_filter.1 hi).1)])
    (fun v hv ↦ loadHolds_unique hv (by simpa using hseg 0 (by norm_num)))
    (fun v hv ↦ loadHolds_unique hv (by simpa using hseg 1 (by norm_num))) h
  rw [← keccakIota_eq hs (by omega) hptL] at hio
  -- the call
  set T := iotaSegEnd s (b + 6 + flipSz s * (iotaUsed s).length) with hT
  simp only [stepTailT, hs0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨z0, z1, e2, e3, e4, e5, e6, e7, e8, e9, hd, hn⟩ := h
  have hyg : σ (.n (T + 3)) = gen ^ (τ - 3) := by
    rw [e3, h17, e2, word_gen, ← pow_succ]; congr 1; omega
  have hcl : σ (.n (T + 5)) = σ (.n 201) * gen ^ (22 * s) := by rw [e5, e4, vkGw_eq s hs1 hs]
  have hout : σ (.n (T + 9)) = σ (.n 201) * gen ^ (22 * (s + 1)) := by
    rw [e9, e7, e6, e8, vkGw_eq s hs1 hs, vkGw_eq 1 le_rfl (by omega), mul_assoc, ← pow_add]
    congr 2
  have hm := dispatch_layer (first := 0) (by omega) (o := (τ - 3) % 2) (by omega) h47 hd
  simp only [List.map_cons, List.map_nil, List.map_append, z0, z1, word_zero, hyg, h43, h48, hcl,
    hout, hio] at hm
  simp only [MeaningKeccakLayer] at hm
  obtain ⟨xs, c', cap', hxs, hrun, hcr', hrets⟩ := hm (τ - 3) s c 0 rfl (by omega) (by omega) rfl
    rfl rfl ⟨hmuL, hptL, hval, hkap, hmus, ⟨pp, hpp, hpt⟩, lp, lanes, hlp, hlen, hlanes,
      by simp only [show ((0 : ℕ) = 1) = False by decide, decide_false, Bool.false_eq_true,
        ↓reduceIte]; exact ⟨lc, sl, loc, hlc, hlocL, hloc, hsl, hslices, hw⟩⟩
    (fun h ↦ absurd h (by decide)) rfl
  rw [show τ - 3 + 3 = τ by omega] at hrun
  refine ⟨xs, c', cap', hxs, by simpa [plainStart] using hrun, hcr', ?_, hn⟩
  rw [← hrets]
  simp only [stepEnd, ← hT, stepTailSz, hs0, ↓reduceIte, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append, List.map_append]
  rfl

/-! ## The first step -/

/-- **Step `0`** (G:2851-2882): the first claim, its `ι` term, and `keccak_layer` with the
committed outputs' value waiting in the sponge. -/
theorem stepT_holds0 {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (h17 : σ (.n 17) = gen ^ (τ - 4))
    (h43 : σ (.n 43) = gen ^ ((τ - 3) / 2)) (h47 : σ (.n 47) = gen ^ ((τ - 3) % 2))
    (h48 : σ (.n 48) = gen ^ ((τ - 3) / 2 + (τ - 3) % 2)) {c : KeccakClaim} {L0 : E}
    (hcr : ClaimRec rd ((1 : ℕ) = 1) (σ (.n 201)) c (τ - 3))
    (hL0 : ∀ v, LoadHolds rd (σ (.n 274)) 30 v → v = L0)
    (hw0 : ∀ z < 64, c.weights.getD z 0 = L0 * gen ^ z)
    (hpk : FsPackOk σ (.n 191) (191 + 1) dsObserve)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (stepT 0 488 [179, 180, 181, 182, 183] 0 vkGw)
      next kret) :
    ∃ (xs : List E) (c' : KeccakClaim) (cap' : List E), ReadsAt rd (σ (.n 5) * gen) xs ∧
      RunsTo (verifyKeccakLayer τ 0 c)
        ⟨[σ (.n 179), σ (.n 180), σ (.n 181), σ (.n 182), σ (.n 183)], [(σ (.n 191), dsObserve)]⟩
        xs c' ⟨cap', []⟩ ∧
      ClaimRec rd ((0 : ℕ) = 1) (σ (.n 201) * gen ^ (22 * 1)) c' (τ - 3) ∧
      ((List.range 6).map fun j ↦ σ (.n (stepEnd 0 488 - 6 + j))) =
        cap' ++ [σ (.n 5) * gen * gen ^ xs.length] ∧ next := by
  have hcr0 := hcr
  obtain ⟨hmuL, hptL, hval, hkap, hmus, ⟨pp, hpp, hpt⟩, -⟩ := hcr
  simp only [stepT, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨lcp, -, ecp, h⟩ := h
  have ecp' : σ (.n 488) = pp := loadHolds_unique lcp (by simpa using hpp)
  have hr : LoadHolds rd (σ (.n (488 + 2))) (0 + 0) (c.point.getD (τ - 4) 0) := by
    rw [ecp, ecp', h17, loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ (by omega)]
    exact hpt _ (by omega)
  obtain ⟨hseg, h⟩ := eqtreeT_last (rs := [c.point.getD (τ - 4) 0]) (n := 1) le_rfl rfl
    (fun t ht ↦ by obtain rfl : t = 0 := (by omega); simpa using hr) h
  obtain ⟨hfl, h⟩ := flipsT_holds0 hL0 h
  obtain ⟨hio, h⟩ := iotaSegT_holds (F := fun i ↦ c.weights.getD (2 ^ i - 1) 0)
    (g0 := (eqKernel [c.point.getD (τ - 4) 0]).getD 0 0)
    (g1 := (eqKernel [c.point.getD (τ - 4) 0]).getD 1 0) (by norm_num) (fun i hi ↦ by
      have hi7 := List.mem_range.1 (List.mem_filter.1 hi).1
      have hz : 2 ^ i - 1 < 64 := by
        have : 2 ^ i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [hfl i hi, hw0 _ hz])
    (fun v hv ↦ loadHolds_unique hv (by simpa using hseg 0 (by norm_num)))
    (fun v hv ↦ loadHolds_unique hv (by simpa using hseg 1 (by norm_num))) h
  rw [← keccakIota_eq (by norm_num) (by omega) hptL] at hio
  simp only [stepTailT, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨e0, e1, e2, e3, e4, e5, hd, hn⟩ := h
  have hcur : σ (.n (iotaSegEnd 0 (488 + 6 + flipSz 0 * (iotaUsed 0).length) + 1)) =
      σ (.n 5) * gen := by rw [e1, e0, word_gen]
  have hyg : σ (.n (iotaSegEnd 0 (488 + 6 + flipSz 0 * (iotaUsed 0).length) + 3)) =
      gen ^ (τ - 3) := by
    rw [e3, h17, e2, word_gen, ← pow_succ]; congr 1; omega
  have hout : σ (.n (iotaSegEnd 0 (488 + 6 + flipSz 0 * (iotaUsed 0).length) + 5)) =
      σ (.n 201) * gen ^ (22 * 1) := by
    rw [e5, e4, vkGw_eq 1 le_rfl (by omega)]
  have hm := dispatch_layer (first := 1) (by omega) (o := (τ - 3) % 2) (by omega) h47 hd
  simp only [List.map_cons, List.map_nil, List.map_append, hyg, h43, h48, hcur, hout, hio] at hm
  simp only [MeaningKeccakLayer] at hm
  obtain ⟨xs, c', cap', hxs, hrun, hcr', hrets⟩ := hm (τ - 3) 0 c (σ (.n 191)) rfl (by omega)
    (by omega) rfl rfl rfl hcr0 (fun _ hc ↦ fsPackT_cells hpk hc) rfl
  rw [show τ - 3 + 3 = τ by omega] at hrun
  refine ⟨xs, c', cap', hxs, by simpa [plainStart] using hrun, hcr', ?_, hn⟩
  rw [← hrets]
  simp only [stepEnd, stepTailSz, ↓reduceIte, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append, List.map_append]
  rfl

end
end LeanVM.Guest.B1.VerifySub
