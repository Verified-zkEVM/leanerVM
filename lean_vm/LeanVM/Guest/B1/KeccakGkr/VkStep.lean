/-
  LeanVM.Guest.B1.KeccakGkr.VkStep

  A step of `verify_keccak` (G:2853-2886): the claim's segment weights, its `ι` term, the layer.
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

/-- **The `ι` term** (G:2876-2881): per segment the flips of its bits summed, times the segment's
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

end
end LeanVM.Guest.B1.VerifySub
