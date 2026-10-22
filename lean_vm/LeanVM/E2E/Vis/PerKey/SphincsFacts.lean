/-
  LeanVM.E2E.Vis.PerKey.SphincsFacts

  W-vis, P7b: facts for the per-key leanSPHINCS chain. Key generation's cache holds nothing private
  for its own key, and the per-key event forces good keys.
-/

module

public import LeanVM.E2E.Vis.PerKey.SphincsView
public import LeanVM.E2E.Vis.PerKey.XmssFacts

/-!
# Facts for the per-key leanSPHINCS chain (W-vis, P7b)

The leanSPHINCS counterpart of `Vis/PerKey/XmssFacts.lean`.

* `keygen_cache_not_privJS`: after a leanSPHINCS key generation from the empty cache, no cached
  input is in the key's private class `PrivJ pj` (its queries are two derivations, then scheme
  inputs of the key's parameter: `sphincs_keygenFromSeed_eq`, `walkS_spineNode`).
* `goodKeysS_of_not_keyCollAt`: no coincidence at leanSPHINCS key `j` and key `j` the reduction's
  makes the keys good for reduction `j`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyS

open PerKeyX (XKey SKey sTreeC sLift_bind sLift_pure keyParams_castAdd keyParams_natAdd)

variable {nx ns : ℕ} [Sphincs.Params]

/-- `sTreeC` unfolded. -/
theorem sTreeC_eqS (P : Sphincs.Digest) (S : Sphincs.MasterSeed) :
    sTreeC P S = sLift (Sphincs.Seeded.spineNode P Sphincs.topLayer Sphincs.Concrete.rootTree S
      (Sphincs.totalHeight - Sphincs.subtreeHeight) : OracleComp Sphincs.HashSpec _) := by
  unfold sTreeC; rfl

omit [Sphincs.Params] in
/-- A leanSPHINCS hash query lifted into the schemes' world satisfies what its input does. -/
theorem allQueriesSatisfy_sLift_query (x : List UInt8) {Q : List UInt8 → Prop} (hx : Q x) :
    AllQueriesSatisfy (sLift (liftM (Sphincs.HashSpec.query x) : OracleComp Sphincs.HashSpec _))
      fun t ↦ ∀ y, t = .inr y → Q y :=
  allQueriesSatisfy_sLift ((allQueriesSatisfy_query_iff _ _).mpr hx)

/-- leanSPHINCS's key generation with its tree behind `sTreeC`. -/
theorem keygen_eq_sTreeC :
    (sKeygen : OracleComp OW _) =
      (liftM Sphincs.sampleMasterSeed : OracleComp OW _) >>= fun seed ↦
      sLift (liftM (Sphincs.HashSpec.query (Sphincs.schemeSeedInput seed)) :
        OracleComp Sphincs.HashSpec _) >>= fun S ↦
      sLift (liftM (Sphincs.HashSpec.query (Sphincs.keygenHashInput 0 .parameter S)) :
        OracleComp Sphincs.HashSpec _) >>= fun o ↦
      sTreeC (Sphincs.truncateHash o) S >>= fun root ↦
      pure ((⟨root, Sphincs.truncateHash o⟩ : Sphincs.PublicKey),
        (⟨S, Sphincs.truncateHash o, root⟩ : Sphincs.Seeded.SecretKey)) := by
  unfold sKeygen
  simp only [sphincs_keygenFromSeed_eq, sLift_bind, sLift_pure]
  refine bind_congr fun seed ↦ bind_congr fun S ↦ bind_congr fun o ↦ ?_
  unfold sTreeC
  rfl

/-- The tree's queries are scheme inputs of its parameter. -/
theorem allQueriesSatisfy_sTreeC (P : Sphincs.Digest) (S : Sphincs.MasterSeed) :
    AllQueriesSatisfy (sTreeC P S) fun t ↦ ∀ x, t = .inr x →
      SchemeInputN (Sphincs.bytesLE 16 P) x := by
  rw [sTreeC_eqS]
  exact allQueriesSatisfy_sLift (walkS_spineNode _ _ _ _ _)

/-- **Key generation caches nothing private for its own key**, and its secret key holds its public
key's parameter. -/
theorem keygen_cache_not_privJS :
    ∀ r ∈ support (romRun (sKeygen : OracleComp OW _) ∅),
      r.1.2.parameter = r.1.1.parameter ∧
      ∀ x, r.2 x ≠ none → ¬ PrivJ (Sphincs.bytesLE 16 r.1.2.parameter) x := by
  intro r hr
  rw [keygen_eq_sTreeC] at hr
  simp only [romRun_bind, mem_support_bind_iff] at hr
  obtain ⟨r1, h1, r2, h2, r3, h3, r4, h4, hr⟩ := hr
  rw [romRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  refine ⟨rfl, fun x hx ↦ ?_⟩
  rcases cache_of_allQueries _ _ (allQueriesSatisfy_sTreeC _ _) _ _ h4 x hx with hx | hx
  · rcases cache_of_allQueries DerivShape _ (allQueriesSatisfy_sLift_query _
        (sphincs_paramInput_derivShape _)) _ _ h3 x hx with hx | hx
    · rcases cache_of_allQueries DerivShape _ (allQueriesSatisfy_sLift_query _
          (sphincs_schemeSeedInput_derivShape _)) _ _ h2 x hx with hx | hx
      · rcases cache_of_allQueries (fun _ ↦ False) _ (allQueriesSatisfy_liftM_probComp _ _) _ _
          h1 x hx with hx | hx
        · exact absurd rfl hx
        · exact hx.elim
      · exact fun hp ↦ hp.2.1 hx
    · exact fun hp ↦ hp.2.1 hx
  · exact not_privJ_of_schemeInput hx.1

/-- **No coincidence at leanSPHINCS key `j`, and key `j` the reduction's, make the keys good** for
reduction `j`. -/
theorem goodKeysS_of_not_keyCollAt (keys : Keys nx ns) (j : Fin ns) (kj' : SKey)
    (hj : keys.sphincs j = kj') (hcoll : ¬ KeyCollAt keys (Fin.natAdd nx j)) :
    GoodKeysS (Sphincs.bytesLE 16 kj'.2.parameter) j kj' (keys.xmss, keys.sphincs) := by
  have hpj := keyParams_natAdd keys j
  rw [hj] at hpj
  refine ⟨fun i heq ↦ hcoll (Or.inl ⟨Fin.castAdd ns i, fun h ↦ ?_, ?_⟩),
    fun i ↦ ⟨fun hi ↦ by subst hi; exact hj,
      fun hi heq ↦ hcoll (Or.inl ⟨Fin.natAdd nx i, fun h ↦ hi ?_, ?_⟩)⟩⟩
  · have := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  · rw [keyParams_castAdd, hpj, heq]
  · have := congrArg Fin.val h
    simp only [Fin.val_natAdd] at this
    exact Fin.ext (by omega)
  · rw [keyParams_natAdd, hpj, heq]

end PerKeyS

end
end LeanVM.E2E
