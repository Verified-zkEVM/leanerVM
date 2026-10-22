/-
  LeanVM.E2E.Complete.Rom.End

  T6-prob: V_I accepts the honest prover's idealized proof of a generated valid tree, except with
  probability `completeError`, over the random oracle; with no good event as a hypothesis.
-/

module

public import LeanVM.E2E.Complete.Rom.EndOf
public import LeanVM.E2E.Complete.Rom.CompBridge
public import LeanVM.E2E.Complete.Rom.CompTags
public import LeanVM.E2E.Complete.Rom.Valid

/-!
# T6-prob

`docs/roadmap/t6-prob.md` §4.5–§4.6. The pieces of `EndOf.lean` hold (`romPieces`: the bridge,
`CompBridge.lean`; the failure tags, `CompTags.lean`), so for every generator of valid trees
(`ValidGen`, `Valid.lean`) with at most `QG` queries, at a valid rate and a proof-of-work fuel of
at most `2^64` nonces:

    Pr[ ¬ CompleteOK ] ≤ completeError (QG + QP) pfuel
      = (QG+QP)·((1 − 2^-17)^pfuel + (QG+QP)/2^256) + (QG+QP)·(2^-192 + 4(QG+QP+1)/2^256)

(**`idealVerify_complete_rom`**), and V_I run lazily after the prover rejects with at most that
probability (`idealVerify_complete_rom_run`). `QP` bounds the prover's queries on the generated
trees, at most `size · nodeQueries pfuel` (`proverQueries_le`). The instance: the honest leanXMSS
leaf generator (`xmssLeafGen`, P7) at rate `1` and fuel `2^25`, error at most `2^-124`
(`idealVerify_complete_rom_xmssLeaf`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom LeanVM.E2E OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/-- **The pieces hold**, for trees of the deployed shape. -/
theorem romPieces (ρ pfuel : ℕ) : RomPieces ρ pfuel (HonestTree.AllNodes HonestTree.ShapeOK) where
  lookEq h Ht hH := honestProverComp_look ρ pfuel h Ht hH
  natural ℓ T := honestProverComp_lookImpl ρ pfuel ℓ T
  grind h := honestProverM_grind h
  weights h := honestProverM_weights h
  shaped hρ H _ _ hsh h := honestOutN_weights_shaped hρ H
    (HonestTree.allNodes_imp (fun _ h ↦ HonestTree.ShapeOK.kidsLe16 h) _ hsh) h

/-- **T6-prob: completeness of V_I with high probability over the random oracle.** For every
generator `gen` of valid honest trees within the limits (`ValidGen`: at most `N` nodes, the
prover's queries at most `QP`) with at most `QG` queries, a valid rate, a proof-of-work fuel of at
most `2^64` nonces and V_I's fuel at least `N`: except with probability
`completeError (QG + QP) pfuel`, the honest prover outputs a statement with the tree's claims and
V_I accepts its idealized proof at every hash agreeing with the oracle's log. No good event is a
hypothesis. -/
theorem idealVerify_complete_rom {ρ pfuel N QG QP fuel : ℕ} (hρ : validRate ρ)
    (hpf : pfuel ≤ 2 ^ 64) (gen : OracleComp HashSpec (Option HonestTree))
    (hQG : IsTotalQueryBound gen QG) (hgen : ValidGen ρ pfuel N QP gen) (hfuel : N ≤ fuel) :
    Pr{let z ← completeExp ρ pfuel gen}[¬ CompleteOK fuel z] ≤ completeError (QG + QP) pfuel :=
  idealVerify_complete_rom_of ρ pfuel (romPieces ρ pfuel) hρ hpf hQG
    (HonestTree.proverQueries ρ pfuel) (isTotalQueryBound_honestProverComp ρ pfuel) hgen hfuel

/-- **T6-prob with V_I run**: the generator, the honest prover and V_I against one lazily sampled
random oracle; V_I rejects (or the prover fails) with probability at most
`completeError (QG + QP) pfuel`. -/
theorem idealVerify_complete_rom_run {ρ pfuel N QG QP fuel : ℕ} (hρ : validRate ρ)
    (hpf : pfuel ≤ 2 ^ 64) (gen : OracleComp HashSpec (Option HonestTree))
    (hQG : IsTotalQueryBound gen QG) (hgen : ValidGen ρ pfuel N QP gen) (hfuel : N ≤ fuel) :
    Pr{let z ← completeRunVI ρ pfuel gen fuel}[z.1 = some false] ≤
      completeError (QG + QP) pfuel :=
  (prEvent_reject_le_not_completeOK ρ pfuel gen fuel).trans
    (idealVerify_complete_rom hρ hpf gen hQG hgen hfuel)

/-- The leaf generator and the prover make fewer than `2^64` queries at the fuel `2^25`. -/
theorem xmssLeaf_queries_le :
    E2E.xmssKeygenBound + E2E.xmssSignBound + xmssLeafQueries (2 ^ 25) ≤ 2 ^ 64 := by
  have hc : leanVmCost = 13210 := by
    have := leanVmQueryBound_eq
    unfold leanVmQueryBound at this
    omega
  have hv : xmssVerifyBound = 384 := by decide
  rw [xmssLeafGen_queries_eq]
  simp only [xmssLeafQueries, hc, hv, proverFactor, costHeight, blake2sR1csLogSize]
  norm_num

/-- **T6-prob is not vacuous**: for the honest leanXMSS leaf generator at rate `1`, a
proof-of-work fuel of `2^25` nonces and V_I's fuel `1`, the bad outcome has probability at most
`2^-124`. -/
theorem idealVerify_complete_rom_xmssLeaf :
    Pr{let z ← completeExp 1 (2 ^ 25) xmssLeafGen}[¬ CompleteOK 1 z] ≤ (2 : ℝ≥0∞)⁻¹ ^ 124 :=
  (idealVerify_complete_rom hyps_wTree.1 (by norm_num) xmssLeafGen isTotalQueryBound_xmssLeafGen
    (validGen_xmssLeafGen 1 (2 ^ 25)) le_rfl).trans (completeError_le xmssLeaf_queries_le)

end
end LeanVM.E2E.Complete
