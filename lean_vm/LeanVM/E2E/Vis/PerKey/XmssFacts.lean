/-
  LeanVM.E2E.Vis.PerKey.XmssFacts

  W-vis, P7b: facts for the per-key leanXMSS chain. The lazy oracle's cache holds only what was
  queried; key generation's cache holds nothing private for its own key; the keys' parameters
  by index; and the per-key event forces good keys.
-/

module

public import LeanVM.E2E.Vis.PerKey.XmssView

/-!
# Facts for the per-key chain (W-vis, P7b)

* `cache_of_allQueries`: after a run from `c` whose hash queries satisfy `Q`, every cached input
  was cached before or satisfies `Q`.
* `keygen_cache_not_privJ`: after a leanXMSS key generation from the empty cache, no cached input is
  in the key's private class `PrivJ pj` (its queries are two derivations, then scheme inputs of
  the key's parameter: `xmss_keygenFromSeed_eq`, `walkX_treeNode`).
* `keyParams_castAdd`, `keyParams_natAdd`: the keys' parameters by index.
* `goodKeys_of_not_keyCollAt`: no coincidence at key `j` and key `j` the reduction's makes the keys
  good for reduction `j`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-- **The lazy oracle caches only what is queried.** -/
theorem cache_of_allQueries {α : Type} (Q : List UInt8 → Prop) :
    ∀ (oa : OracleComp OW α), AllQueriesSatisfy oa (fun t ↦ ∀ x, t = .inr x → Q x) →
      ∀ (c : QueryCache LeanXmss.HashSpec), ∀ z ∈ support (romRun oa c), ∀ x, z.2 x ≠ none →
        c x ≠ none ∨ Q x := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro _ c z hz x hx
    simp only [romRun, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl hx
  | query_bind t k ih =>
    intro hq c z hz x hx
    rw [allQueriesSatisfy_query_bind_iff] at hq
    have hz' : z ∈ support (romRun ((liftM (OW.query t) : OracleComp OW _) >>= k) c) := hz
    rw [romRun_query_bind, mem_support_bind_iff] at hz'
    obtain ⟨r, hr, hz'⟩ := hz'
    rcases ih r.1 (hq.2 r.1) r.2 z hz' x hx with h | h
    · rcases t with n | y
      · rw [owImpl_uniform_run, support_map] at hr
        obtain ⟨u, -, rfl⟩ := hr
        exact Or.inl h
      · cases hcy : c y with
        | some u =>
          rw [owImpl_hash_run_some y hcy, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          exact Or.inl h
        | none =>
          rw [owImpl_hash_run_none y hcy, support_map] at hr
          obtain ⟨u, -, rfl⟩ := hr
          by_cases hxy : x = y
          · subst hxy; exact Or.inr (hq.1 x rfl)
          · left
            simpa [QueryCache.cacheQuery, hxy] using h
    · exact Or.inr h

/-- A coin computation makes no hash query. -/
theorem allQueriesSatisfy_liftM_probComp {α : Type} (p : ProbComp α) (Q : List UInt8 → Prop) :
    AllQueriesSatisfy (liftM p : OracleComp OW α) fun t ↦ ∀ x, t = .inr x → Q x := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind n k ih =>
    rw [liftM_bind]
    change AllQueriesSatisfy ((liftM (OW.query (.inl n)) : OracleComp OW _) >>= fun u ↦ liftM (k u)) _
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨fun x hx ↦ (by simp at hx), fun u ↦ ih u⟩

namespace PerKeyX

/-- A leanXMSS hash query lifted into the schemes' world satisfies what its input does. -/
theorem allQueriesSatisfy_liftM_query (x : List UInt8) {Q : List UInt8 → Prop} (hx : Q x) :
    AllQueriesSatisfy (liftM (liftM (LeanXmss.HashSpec.query x) : OracleComp LeanXmss.HashSpec _) :
      OracleComp OW _) fun t ↦ ∀ y, t = .inr y → Q y :=
  allQueriesSatisfy_liftM_hash ((allQueriesSatisfy_query_iff _ _).mpr hx)

/-- leanXMSS's key generation with its tree behind `xTreeC`. -/
theorem keygen_eq_xTreeC :
    (LeanXmss.MultiUser.keygen : OracleComp OW _) =
      (liftM LeanXmss.sampleMasterSeed : OracleComp OW _) >>= fun seed ↦
      (liftM (liftM (LeanXmss.HashSpec.query (LeanXmss.seedHashInput seed)) :
        OracleComp LeanXmss.HashSpec _) : OracleComp OW _) >>= fun S ↦
      (liftM (liftM (LeanXmss.HashSpec.query (LeanXmss.keygenHashInput 0 .parameter S)) :
        OracleComp LeanXmss.HashSpec _) : OracleComp OW _) >>= fun o ↦
      xTreeC (LeanXmss.truncateHash o) S >>= fun root ↦
      pure ((⟨root, LeanXmss.truncateHash o⟩ : LeanXmss.PublicKey),
        (⟨S, LeanXmss.truncateHash o, root⟩ : LeanXmss.Seeded.SecretKey)) := by
  unfold LeanXmss.MultiUser.keygen
  simp only [xmss_keygenFromSeed_eq, liftM_bind, liftM_pure]
  refine bind_congr fun seed ↦ bind_congr fun S ↦ bind_congr fun o ↦ ?_
  unfold xTreeC
  rfl

/-- The tree's queries are scheme inputs of its parameter. -/
theorem allQueriesSatisfy_xTreeC (P : LeanXmss.PublicParameter) (S : LeanXmss.MasterSeed) :
    AllQueriesSatisfy (xTreeC P S) fun t ↦ ∀ x, t = .inr x →
      SchemeInputN (LeanXmss.bytesLE 16 P) x := by
  rw [xTreeC_eq]
  exact allQueriesSatisfy_liftM_hash (walkX_treeNode _ _ _ _ _)

/-- **Key generation caches nothing private for its own key**, and its secret key holds its public
key's parameter. -/
theorem keygen_cache_not_privJ :
    ∀ r ∈ support (romRun (LeanXmss.MultiUser.keygen : OracleComp OW _) ∅),
      r.1.2.parameter = r.1.1.parameter ∧
      ∀ x, r.2 x ≠ none → ¬ PrivJ (LeanXmss.bytesLE 16 r.1.2.parameter) x := by
  intro r hr
  rw [keygen_eq_xTreeC] at hr
  simp only [romRun_bind, mem_support_bind_iff] at hr
  obtain ⟨r1, h1, r2, h2, r3, h3, r4, h4, hr⟩ := hr
  rw [romRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  refine ⟨rfl, fun x hx ↦ ?_⟩
  rcases cache_of_allQueries _ _ (allQueriesSatisfy_xTreeC _ _) _ _ h4 x hx with hx | hx
  · rcases cache_of_allQueries DerivShape _ (allQueriesSatisfy_liftM_query _
        (xmss_paramInput_derivShape _)) _ _ h3 x hx with hx | hx
    · rcases cache_of_allQueries DerivShape _ (allQueriesSatisfy_liftM_query _
          (xmss_seedHashInput_derivShape _)) _ _ h2 x hx with hx | hx
      · rcases cache_of_allQueries (fun _ ↦ False) _ (allQueriesSatisfy_liftM_probComp _ _) _ _
          h1 x hx with hx | hx
        · exact absurd rfl hx
        · exact hx.elim
      · exact fun hp ↦ hp.2.1 hx
    · exact fun hp ↦ hp.2.1 hx
  · exact not_privJ_of_schemeInput hx.1

variable {nx ns : ℕ} [Sphincs.Params]

/-- A leanXMSS key's parameter, by index. -/
theorem keyParams_castAdd (keys : Keys nx ns) (i : Fin nx) :
    (keyParams keys)[Fin.castAdd ns i]? = some (LeanXmss.bytesLE 16 (keys.xmss i).2.parameter) := by
  unfold keyParams
  rw [Fin.getElem?_fin, Fin.val_castAdd, List.getElem?_append_left (by simp), List.getElem?_ofFn]
  simp

/-- A leanSPHINCS key's parameter, by index. -/
theorem keyParams_natAdd (keys : Keys nx ns) (i : Fin ns) :
    (keyParams keys)[Fin.natAdd nx i]? = some (Sphincs.bytesLE 16 (keys.sphincs i).2.parameter) := by
  unfold keyParams
  rw [Fin.getElem?_fin, Fin.val_natAdd, List.getElem?_append_right (by simp), List.length_ofFn, Nat.add_sub_cancel_left,
    List.getElem?_ofFn]
  simp

/-- **No coincidence at key `j`, and key `j` the reduction's, make the keys good** for reduction
`j`. -/
theorem goodKeys_of_not_keyCollAt (keys : Keys nx ns) (j : Fin nx) (kj' : XKey)
    (hj : keys.xmss j = kj') (hcoll : ¬ KeyCollAt keys (Fin.castAdd ns j)) :
    GoodKeys (LeanXmss.bytesLE 16 kj'.2.parameter) j kj' (keys.xmss, keys.sphincs) := by
  have hpj := keyParams_castAdd keys j
  rw [hj] at hpj
  refine ⟨fun i ↦ ⟨fun hi ↦ hi ▸ hj, fun hi heq ↦ hcoll (Or.inl ⟨Fin.castAdd ns i, fun h ↦ hi ?_, ?_⟩)⟩,
    fun i heq ↦ hcoll (Or.inl ⟨Fin.natAdd nx i, fun h ↦ ?_, ?_⟩)⟩
  · exact Fin.castAdd_injective _ _ h
  · rw [keyParams_castAdd, hpj, heq]
  · have := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  · rw [keyParams_natAdd, hpj, heq]

end PerKeyX

end
end LeanVM.E2E
