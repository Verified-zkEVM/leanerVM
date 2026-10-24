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
(`1317 + d`) or the cursor after the pack rounds (`1323 + d`). `layer_residOk`: the loads the
lane weights, the weight section and the slices' weights read are not stores.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The position rounds of a specialization. -/
def localS (d : ℕ) : List Stmt :=
  localRoundsT (.n (d + 1323)) (.n (d + 1325)) (.n (d + 1324)) (cap5 (d + 1318)) (d + 1326) 11

theorem layerT_sections (first odd : ℕ) : layerT first odd =
    secA1 first ++ (secA2 first ++ (rmfeBlockT ++ (hornerS first ++ (packSetupT first odd ++
      (lastT (4 * odd) ++ (localS (4 * odd) ++ (tReadsT (4 * odd) ++ (eqfS (4 * odd) ++
        (weightT first (4 * odd) ++ tailT (4 * odd) (weightEnd first (4 * odd))
          (weightVal first (4 * odd))))))))))) := by
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

theorem layer_noStore {first odd : ℕ} (hf : first < 2) (ho : odd < 2) :
    noStoreVia [.n 7, .n 11, .n (4 * odd + 1317), .n (4 * odd + 1323)] (layerSt first odd) = true := by
  interval_cases first <;> interval_cases odd <;> decide +kernel

/-- None of the atoms `as` is a store. -/
def noneIn (as S : List Atom) : Bool := as.all fun a ↦ !S.contains a

theorem not_mem_of_noneIn {as S : List Atom} (h : noneIn as S = true) : ∀ a ∈ as, a ∉ S := by
  intro a ha hm
  have h' := List.all_eq_true.mp h a ha
  rw [List.contains_iff_mem.mpr hm] at h'
  exact absurd h' (by decide)

theorem layer_residOk {first odd : ℕ} (hf : first < 2) (ho : odd < 2) :
    noneIn (resid (atomsL (eqfS (4 * odd)))) (layerSt first odd) = true ∧
    noneIn (resid (atomsL (weightT first (4 * odd)))) (layerSt first odd) = true ∧
    noneIn (resid (atomsL (tailEqf (4 * odd) (weightEnd first (4 * odd))))) (layerSt first odd) =
      true := by
  interval_cases first <;> interval_cases odd
  all_goals exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end
end LeanVM.Guest.B1.VerifySub
