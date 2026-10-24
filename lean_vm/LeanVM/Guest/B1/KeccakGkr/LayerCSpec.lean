/-
  LeanVM.Guest.B1.KeccakGkr.LayerCSpec

  `keccak_layer`'s honest valuation: the template evaluated from the arguments, its checker's
  count and its stores, for the four specializations.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT
public import LeanVM.Guest.B1.KeccakGkr.LayerCBlock

/-!
# The honest valuation of a layer

`layerσ rd w args first odd`: `layerT first odd` evaluated (`Fwd.ev`) on the memory `rd` and the
oracle `w` from the arguments. The checker accepts the four specializations (`layer_chk`), whose
stores are `layerSt` (`layer_stores`): the next claim's record at `out`, the pack rounds' first
record, the local point, the next claim's lanes and slices. Every statement satisfies its
equations (`layer_good`), and the parameters are the arguments (`layer_param`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The stores of `layerT first odd`. -/
def layerSt (first odd : ℕ) : List Atom :=
  (List.range 16).map (fun i ↦ .load (.n (rmfeStores.getD i 0)) (.n 12) (6 + i)) ++
  [.load (.n 1215) (.n 12) 1,
    .load (.n 1078) (.n 1310) 0, .load (.n 1079) (.n 1310) 16, .load (.n 1080) (.n 1310) 32,
    .load (.n 1081) (.n 1310) 48, .load (.n 1082) (.n 1310) 64, .load (.n 1312) (.n 1310) 80,
    .load (.n 1307) (.n 1310) 96, .load (.n 1313) (.n 1310) 112] ++
  (List.range 11).map (fun i ↦ .load (.n (4 * odd + 1377 + 60 * i)) (.n (4 * odd + 1325)) i) ++
  [.load (.n (weightEnd first (4 * odd) + 33)) (.n 12) 0, .load (.n 1309) (.n 12) 2,
    .load (.n (4 * odd + 1325)) (.n 12) 4] ++
  (List.range 25).map (fun i ↦ .load (.n (weightEnd first (4 * odd) + 38 + 4 * i))
    (.n (weightEnd first (4 * odd) + 34)) i) ++
  [.load (.n (weightEnd first (4 * odd) + 34)) (.n 12) 3] ++
  (List.range 64).map (fun z ↦ .load (.n (eqfVal (weightEnd first (4 * odd) + 135) 6 64 5 z))
    (.n (weightEnd first (4 * odd) + 278)) z) ++
  [.load (.n (weightEnd first (4 * odd) + 278)) (.n 12) 5]

/-- The checker's count after the body. -/
def layerN (first odd : ℕ) : ℕ := if first = 1 then 2483 + 4 * odd else 2815 + 4 * odd

theorem layer_chk {first odd : ℕ} (hf : first < 2) (ho : odd < 2) :
    Fwd.chk 14 (layerT first odd) = some (layerN first odd) := by
  interval_cases first <;> interval_cases odd <;> decide +kernel

theorem layer_stores {first odd : ℕ} (hf : first < 2) (ho : odd < 2) :
    storesOf 14 (layerT first odd) = layerSt first odd := by
  interval_cases first <;> interval_cases odd <;> decide +kernel

/-- **The honest valuation of a layer.** -/
noncomputable def layerσ (rd : Reader) (w : ℕ → E) (args : List E) (first odd : ℕ) : Val :=
  B1.Val.ofArgs (ev rd w args (layerT first odd))

section
variable {rd : Reader} {w : ℕ → E} {args : List E} {first odd : ℕ}

theorem layer_good (hf : first < 2) (ho : odd < 2) (hl : args.length = 14) :
    ∀ s ∈ layerT first odd, GoodS rd (layerSt first odd) w (layerσ rd w args first odd) s := by
  have h := (ev_spec rd w (layerT first odd) args (by rw [hl]; exact layer_chk hf ho)).2.2
  rw [hl, layer_stores hf ho] at h
  exact h

theorem layer_param (hf : first < 2) (ho : odd < 2) (hl : args.length = 14) {i : ℕ}
    (hi : i < 14) : layerσ rd w args first odd (.n i) = args.getD i 0 :=
  ev_params rd w (by rw [hl]; exact layer_chk hf ho) (by rw [hl]; exact hi)

theorem layerσ_idx (v : V) : layerσ rd w args first odd v = layerσ rd w args first odd (.n v.idx) :=
  rfl

end

end
end LeanVM.Guest.B1.VerifySub
