/-
  LeanVM.Guest.B1.Main.MainGoalsFCl

  `main`'s claim lists' digests on an honest run.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsF

/-!
# `main`'s claim lists' digests

`mainGoalClX`, `mainGoalClS`: the leanXMSS and leanSPHINCS tables' declared claims are their
`claimCells`, canonical, hashing as the Spec's list digests (`mf_xmss_digest`,
`mf_sphincs_digest`); the counts are below the coverage table's bound (`Limits`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.Hints (claimCells)

@[expose] public section

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- **`claim_list_digest` on the leanXMSS table's declared claims.** -/
theorem mainGoalClX (hL : Limits s w) : MainGoalClX fs cert fp seed s w := by
  have hn : s.claims.xmss.length < claimGroup * maxKeys := by
    have := hL.coverage
    simp only [coverage] at this
    simp only [claimGroup, maxKeys]
    omega
  have e : (hOwn seed s w).getD 1 [] =
      s.claims.xmss.flatMap (fun c => claimCells c.1.root c.1.parameter c.2) ++
        (xPlan s w).dups.flatMap (fun c => claimCells c.1.root c.1.parameter c.2) := by
    rw [← List.flatMap_append]; rfl
  have hl := mf_length_flatMap (fun c : XmssClaim => claimCells c.1.root c.1.parameter c.2)
    (fun c => mf_claimCells_length c.1.root c.1.parameter c.2) s.claims.xmss
  have hc := mf_canon_flatMap (fun c : XmssClaim => claimCells c.1.root c.1.parameter c.2)
    (fun c => mf_claimCells_canon c.1.root c.1.parameter c.2) s.claims.xmss
  have key := claim_list_digest_completeAt fs cert (Lin := hLmain fs fp seed s w)
    (eP := mfB fs fp seed s w 1) hn hl hc
    (fun rd h => by
      have h1 := mf_reads fs fp seed s w h (i := 1) (by omega)
      rw [e] at h1
      exact (readsAt_append'.mp h1).1)
    (fun k hk => mf_region fs fp seed s w (i := 1) (by omega) (by rw [e, List.length_append]; omega))
  have ha : (hm fs fp seed s w).a77 = gen ^ mfB fs fp seed s w 1 := rfl
  have hn' : (hm fs fp seed s w).nlx = s.claims.xmss.length := rfl
  have hd : (hm fs fp seed s w).xd = xmssListDigest s.claims.xmss := rfl
  unfold MainGoalClX
  rw [ha, hn', hd, mf_xmss_digest]
  exact key

/-- **`claim_list_digest` on the leanSPHINCS table's declared claims.** -/
theorem mainGoalClS (hL : Limits s w) : MainGoalClS fs cert fp seed s w := by
  have hn : s.claims.sphincs.length < claimGroup * maxKeys := by
    have := hL.coverage
    simp only [coverage] at this
    simp only [claimGroup, maxKeys]
    omega
  have e : (hOwn seed s w).getD 2 [] =
      s.claims.sphincs.flatMap (fun c => claimCells c.1.root c.1.parameter c.2) ++
        (sPlan s w).dups.flatMap (fun c => claimCells c.1.root c.1.parameter c.2) := by
    rw [← List.flatMap_append]; rfl
  have hl := mf_length_flatMap (fun c : SphincsClaim => claimCells c.1.root c.1.parameter c.2)
    (fun c => mf_claimCells_length c.1.root c.1.parameter c.2) s.claims.sphincs
  have hc := mf_canon_flatMap (fun c : SphincsClaim => claimCells c.1.root c.1.parameter c.2)
    (fun c => mf_claimCells_canon c.1.root c.1.parameter c.2) s.claims.sphincs
  have key := claim_list_digest_completeAt fs cert (Lin := hLmain fs fp seed s w)
    (eP := mfB fs fp seed s w 2) hn hl hc
    (fun rd h => by
      have h1 := mf_reads fs fp seed s w h (i := 2) (by omega)
      rw [e] at h1
      exact (readsAt_append'.mp h1).1)
    (fun k hk => mf_region fs fp seed s w (i := 2) (by omega) (by rw [e, List.length_append]; omega))
  have ha : (hm fs fp seed s w).a80 = gen ^ mfB fs fp seed s w 2 := rfl
  have hn' : (hm fs fp seed s w).nls = s.claims.sphincs.length := rfl
  have hd : (hm fs fp seed s w).sd = sphincsListDigest s.claims.sphincs := rfl
  unfold MainGoalClS
  rw [ha, hn', hd, mf_sphincs_digest]
  exact key

end
end LeanVM.Guest.B1.Main
