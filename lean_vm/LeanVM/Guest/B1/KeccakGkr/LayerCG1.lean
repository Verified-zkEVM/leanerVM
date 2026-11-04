/-
  LeanVM.Guest.B1.KeccakGkr.LayerCG1

  `keccak_layer`'s body as its completeness sections, and the kernel facts the assembly needs
  about its stores.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCSpec
public import LeanVM.Guest.B1.KeccakGkr.LayerCF

/-!
# The sections and the stores

`layerT_sections`: the body is the sections the completeness lemmas take, in order.
`layer_noStore`: no store goes through the cursor (`7`), the claim (`11`), the last record
(`1072`) or the cursor after the pack rounds (`1078`). `layer_residOk`: the loads the lane
weights, the weight section, the slices' weights, the top coordinate and the flips read are not
stores, and the flips' writes are.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The position rounds. -/
def localS : List Stmt := localRoundsT (.n 1078) (.n 1081) (.n 1079) (cap5 1073) 1082 11

theorem layerT_sections (first : ℕ) : layerT first =
    secA1 first ++ (secA2 first ++ (rmfeBlockT ++ (hornerS first ++ (packSetupT first ++
      (lastT ++ (localS ++ (tReadsT ++ (eqfS ++ (weightT first ++
        tailT (weightEnd first) (weightVal first)))))))))) := by
  simp only [layerT, secA1, secA2, hornerS, localS, eqfS, List.append_assoc]

/-- No store goes through the pointers `ps`. -/
def noStoreVia (ps : List V) (S : List Atom) : Bool := S.all fun a ↦ match a with
  | .load _ p _ => !ps.contains p
  | _ => true

theorem not_mem_of_noStoreVia {ps : List V} {S : List Atom} (h : noStoreVia ps S = true) {p : V}
    (hp : p ∈ ps) (d : V) (off : ℕ) : Atom.load d p off ∉ S := by
  intro hm
  have h' := List.all_eq_true.mp h _ hm
  simp only at h'
  rw [List.contains_iff_mem.mpr hp] at h'
  exact absurd h' (by decide)

theorem layer_noStore {first : ℕ} (hf : first < 2) :
    noStoreVia [.n 7, .n 11, .n 1072, .n 1078] (layerSt first) = true := by
  interval_cases first <;> decide +kernel

/-- None of the atoms `as` is a store. -/
def noneIn (as S : List Atom) : Bool := as.all fun a ↦ !S.contains a

theorem not_mem_of_noneIn {as S : List Atom} (h : noneIn as S = true) : ∀ a ∈ as, a ∉ S := by
  intro a ha hm
  have h' := List.all_eq_true.mp h a ha
  rw [List.contains_iff_mem.mpr hm] at h'
  exact absurd h' (by decide)

theorem layer_residOk {first : ℕ} (hf : first < 2) :
    noneIn (resid (atomsL eqfS)) (layerSt first) = true ∧
    noneIn (resid (atomsL (weightT first))) (layerSt first) = true ∧
    noneIn (resid (atomsL (tailEqf (weightEnd first)))) (layerSt first) = true ∧
    noneIn [.load (.n (topV (weightEnd first))) (.n 1081) 5] (layerSt first) = true ∧
    (∀ i < 7, noneIn (resid (atomsL (flipT (weightEnd first) i))) (layerSt first) = true) ∧
    (∀ i < 7, (layerSt first).contains (.load (.n (flipB (weightEnd first) i + 42))
      (.n (topV (weightEnd first) + 3)) i) = true) := by
  interval_cases first
  all_goals exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

end
end LeanVM.Guest.B1.VerifySub
