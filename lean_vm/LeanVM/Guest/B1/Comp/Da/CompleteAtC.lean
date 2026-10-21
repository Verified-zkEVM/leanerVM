/-
  LeanVM.Guest.B1.Comp.Da.CompleteAtC

  `da_verify` complete over a completeness model in the uniform placed form within weights
  (`CompleteAtWS`): the model version of `B1/Da/CompleteAt.lean`'s `da_verify_completeRelAtW`.
-/

module

public import LeanVM.Guest.B1.Comp.Da.VerifyAtC
public import LeanVM.Guest.B1.Da.CompleteAt

/-!
# `da_verify`, uniformly placed, over a completeness model

* `dvLayoutC CM`: `da_verify`'s own words at `fp` over the model, `DaMemC CM` as a layout
  (`daMemC_of_memL`): `dvLayout` with the model's cell digests, vector hash states and trees
  (`treeLM`). Its words have the deployed layout's positions and lengths (`dvLayoutC_shape`), so
  they lie in `dvTot` words and are pairwise disjoint as the deployed ones
  (`dvLayoutC_within`, `dvLayoutC_disj`).
* `da_verify_completeRelAtWC`: `da_verify_completeRelAtW` over `CM`, a witness opening the claim
  over the model's answers and the guest's padding digests, by a tree of `dvTot` words weighing at
  most `dvTot θ` at every frame weight `θ`, valid under `CM.sem`.
* `da_verify_completeRelAtW_of_comp`: the deployed `da_verify_completeRelAtW`, from it at
  `CompModel.deployed`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value LeanVM.E2E.Complete
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef DisjL Within Returns disj_nil completeAtWS_deployed)
open LeanVM.Guest.B1.Main (Layout MemL RegionL CompleteAtWS)

@[expose] public section

/-! ## Layouts by their positions and lengths -/

/-- A layout entry's position and length. -/
def qShape (q : ℕ × List E) : ℕ × ℕ := (q.1, q.2.length)

/-- Two layouts of the same positions and lengths: the first lies where the second does. -/
theorem within_of_shape {L L' : Layout} (h : L.map qShape = L'.map qShape) {b n : ℕ}
    (hw : Within L' b n) : Within L b n := fun q hq => by
  obtain ⟨q', hq', he⟩ := List.mem_map.mp (h ▸ List.mem_map_of_mem (f := qShape) hq)
  simp only [qShape, Prod.mk.injEq] at he
  obtain ⟨h1, h2⟩ := he
  have := hw q' hq'
  rw [h1, h2] at this
  exact this

/-- Two layouts of the same positions and lengths: the first is disjoint when the second is. -/
theorem disjL_of_shape {L L' : Layout} (h : L.map qShape = L'.map qShape) (hd : DisjL L') :
    DisjL L := by
  have e : ∀ M : Layout, DisjL M ↔
      (M.map qShape).Pairwise fun q q' => q.1 + q.2 ≤ q'.1 ∨ q'.1 + q'.2 ≤ q.1 := fun M => by
    unfold DisjL
    rw [List.pairwise_map]
    rfl
  rw [e] at hd ⊢
  rw [h]
  exact hd

/-! ## `da_verify`'s own words over a model -/

/-- A tree's nodes over a model's pairs from `base`, as `TreeAtM` reads them (`treeL`). -/
def treeLM (M : HashModel) (base k : ℕ) (leaf : ℕ → Digest) : Layout :=
  (List.range (k + 1)).flatMap fun l => (List.range (2 ^ (k - l))).map fun j =>
    (base + (lvOff k l + 2 * j), [(digestScalars (nodeM M leaf l j)).1,
      (digestScalars (nodeM M leaf l j)).2])

theorem treeAtM_of_memL {M : HashModel} {rd : Reader} {L : Layout} (h : MemL rd L) {base k : ℕ}
    {leaf : ℕ → Digest} (hs : ∀ q ∈ treeLM M base k leaf, q ∈ L) :
    TreeAtM M rd (gen ^ base) k leaf := fun l hl j hj => by
  rw [← pow_add]
  exact cells_of_memL h (hs _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr (by omega),
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩))

/-- The positions and lengths of a tree's nodes. -/
def treeShape (base k : ℕ) : List (ℕ × ℕ) :=
  (List.range (k + 1)).flatMap fun l => (List.range (2 ^ (k - l))).map fun j =>
    (base + (lvOff k l + 2 * j), 2)

theorem treeLM_shape (M : HashModel) (base k : ℕ) (leaf : ℕ → Digest) :
    (treeLM M base k leaf).map qShape = treeShape base k := by
  simp [treeLM, treeShape, List.map_flatMap, qShape, Function.comp_def]

theorem treeL_shape (base k : ℕ) (leaf : ℕ → Digest) :
    (treeL base k leaf).map qShape = treeShape base k := by
  simp [treeL, treeShape, List.map_flatMap, qShape, Function.comp_def]

section Layout
variable (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (w : Da.Witness) (fp : ℕ)

/-- **`da_verify`'s honest words at `fp` over a completeness model**: `DaMemC` at `dvPtrs`, entry
by entry (`dvLayout`). -/
def dvLayoutC : Layout :=
  let r := w.rows.length
  let lp := LeanDa.logPad r
  (List.range r).map (fun i => (dvPx fs w fp + i, [gen ^ dvDx fs fp * gen ^ (128 * i)])) ++
  (List.range r).flatMap (fun i => (List.range 64).map fun b => (dvDx fs fp + (128 * i + 2 * b),
    [(digestScalars (daCD CM w b i)).1, (digestScalars (daCD CM w b i)).2])) ++
  (List.range 129).map (fun b => (dvHx fs w fp + 2 * b, [(daSC CM w b).1, (daSC CM w b).2])) ++
  [(dvCx cert fp, (List.range 385).map fun k => word (k * 2048) 0 0)] ++
  (List.range r).map (fun i => (dvBx fs w fp + i, [gen ^ dvAx fs w fp * gen ^ (129 * i)])) ++
  (List.range r).map (fun i => (dvAx fs w fp + 129 * i, (List.range 129).map (daA w i))) ++
  treeLM CM.hm (dvTx fs w fp) 7 (fun b => nodeM CM.hm (colLeafM r (daCD CM w) b) lp 0) ++
  treeLM CM.hm (dvWx fs w fp) lp (rowLeafM r (daRD CM w)) ++
  (List.range 128).flatMap (fun b => treeLM CM.hm (dvNode fs w fp b) lp (colLeafM r (daCD CM w) b)) ++
  (List.range 128).map (fun b => (dvLv fs cert w fp b, daWs w b))

/-- **The model's layout has the deployed one's positions and lengths.** -/
theorem dvLayoutC_shape :
    (dvLayoutC CM fs cert w fp).map qShape = (dvLayout fs cert w fp).map qShape := by
  simp only [dvLayoutC, dvLayout, List.map_append, List.map_flatMap, treeLM_shape, treeL_shape]
  simp [qShape, Function.comp_def]

end Layout

/-- **The model's layout is the honest memory over the model** (`daMem_of_memL`). -/
theorem daMemC_of_memL {CM : CompModel} {fs : String → ℕ} {cert : String → V → ℕ} {w : Da.Witness}
    {fp : ℕ} {rd : Reader} {L : Layout} (h : MemL rd L) (hs : ∀ q ∈ dvLayoutC CM fs cert w fp, q ∈ L) :
    DaMemC CM rd (dvPtrs fs cert w.rows.length fp) w := by
  rw [dvPtrs_eq]
  have m : ∀ {q}, q ∈ dvLayoutC CM fs cert w fp → q ∈ L := fun hq => hs _ hq
  simp only [dvLayoutC, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at m
  refine ⟨fun i hi => ?_, fun i hi b hb => ?_, fun b hb => ?_, ?_, fun i hi => ?_, fun i hi b hb => ?_,
    treeAtM_of_memL h fun q hq => m (Or.inl (Or.inl (Or.inl (Or.inr (hq))))),
    treeAtM_of_memL h fun q hq => m (Or.inl (Or.inl (Or.inr (hq)))),
    fun b hb => treeAtM_of_memL h fun q hq => m (Or.inl (Or.inr (⟨b, hb, hq⟩))), fun b hb => ?_⟩
  · rw [← pow_add]
    exact load_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inl (⟨i, hi, rfl⟩)))))))))))
  · rw [← pow_add]
    exact cells_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr (⟨i, hi, b, hb, rfl⟩)))))))))))
  · rw [← pow_add]
    exact cells_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      (⟨b, by omega, rfl⟩))))))))))
  · exact cells_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (rfl)))))))))
  · rw [← pow_add]
    exact load_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨i, hi, rfl⟩))))))))
  · rw [← pow_add]
    have := cells_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨i, hi, rfl⟩))))))) b
      (by simp; omega)
    simpa using this
  · exact cells_of_memL h (m (Or.inr (⟨b, hb, rfl⟩)))

/-- **The model's words lie in `da_verify`'s `dvTot` words** (`dvLayout_within`). -/
theorem dvLayoutC_within (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) {w : Da.Witness}
    (fp : ℕ) (hr1 : 1 ≤ w.rows.length) (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) :
    Within (dvLayoutC CM fs cert w fp) fp (dvTot fs w.rows.length) :=
  within_of_shape (dvLayoutC_shape CM fs cert w fp) (dvLayout_within fs cert fp hr1 hc20 hc4)

/-- **The model's words are pairwise disjoint** (`dvLayout_disj`). -/
theorem dvLayoutC_disj (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (w : Da.Witness)
    (fp : ℕ) (hr1 : 1 ≤ w.rows.length) (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) : DisjL (dvLayoutC CM fs cert w fp) :=
  disjL_of_shape (dvLayoutC_shape CM fs cert w fp) (dvLayout_disj fs cert w fp hr1 hc20 hc4)

/-! ## `da_verify`, complete uniformly over a model -/

/-- **`da_verify` is complete over a completeness model, uniformly placed**, returning the claim a
witness opens over the model's answers, by a tree of `dvTot` words weighing at most its words at
every frame weight (`da_verify_completeRelAtW`). -/
theorem da_verify_completeRelAtWC (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) {CM : CompModel} (w : Da.Witness)
    (root vd : Digest) (hw : w.OpensWith CM.H (Da.toBytes padCellD) (Da.toBytes padRowD) root vd) :
    ∀ (args rets : List E) (Lin : Layout),
      (∀ rd, LowDef κ rd → MemL rd Lin → DaPreAt root vd rd args rets) →
      CompleteAtWS CM.sem fs cert wId κ "da_verify" Lin args (Returns rets) (dvTot fs w.rows.length)
        fun θ => dvTot θ w.rows.length := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  have hsh : ∃ gsq r0 r1 v0 v1, args = [gsq] ∧ rets = [r0, r1, v0, v1] := by
    have h := hpre rd1 hl1 hL1
    unfold DaPreAt at h
    split at h
    · exact ⟨_, _, _, _, _, rfl, rfl⟩
    · exact h.elim
  obtain ⟨gsq, r0, r1, v0, v1, rfl, rfl⟩ := hsh
  obtain ⟨-, hr, hv⟩ := hpre rd1 hl1 hL1
  have hlp : LeanDa.logPad w.rows.length < 16 := by have := logPad_le hw.2.1; omega
  have hR := forced_load (p := gsq * gen ^ LeanDa.logPad w.rows.length) (k := 0)
    (v := gen ^ 2 ^ LeanDa.logPad w.rows.length) (fun rd hl hL => by
      have := (hpre rd hl hL).1 _ hlp
      exact (LeanVM.Guest.B1.Digest.loadHolds_mul_gen_pow _ _ _ _).mpr (by rwa [Nat.add_zero]))
    hl1 hL1
  refine ⟨dvTot fs w.rows.length, dvLayoutC CM fs cert w fp, _, [], ⟨rfl, rfl⟩,
    by rw [List.nil_append]; exact dvLayoutC_within CM fs cert fp hw.1 hc20 hc4,
    by rw [List.nil_append]; exact dvLayoutC_disj CM fs cert w fp hw.1 hc20 hc4, le_rfl,
    fun rd hl hL => ?_⟩
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLi⟩ := Main.memL_append.mp hL
  have hlow : Low16 rd := fun i hi => hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  have h := dv_relAtInC fs cert hlow (hpre rd hl hLi).1 hw hR fp (daMemC_of_memL hLo fun q hq => hq)
  rw [show r0 = (digestScalars root).1 from congrArg Prod.fst hr,
    show r1 = (digestScalars root).2 from congrArg Prod.snd hr,
    show v0 = (digestScalars vd).1 from congrArg Prod.fst hv,
    show v1 = (digestScalars vd).2 from congrArg Prod.snd hv]
  exact h.dmono fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq

/-! ## At the deployed model -/

/-- **The deployed `da_verify_completeRelAtW`**, from the model's at `CompModel.deployed`. -/
theorem da_verify_completeRelAtW_of_comp (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) (w : Da.Witness) (root vd : Digest)
    (hw : w.Opens root vd) :
    ∀ (args rets : List E) (Lin : Layout),
      (∀ rd, LowDef κ rd → MemL rd Lin → DaPreAt root vd rd args rets) →
      LeanVM.Guest.B1.Main.CompleteAtW fs cert wId κ "da_verify" Lin args (Returns rets)
        (dvTot fs w.rows.length) fun θ => dvTot θ w.rows.length := fun args rets Lin hpre =>
  completeAtWS_deployed.mp (da_verify_completeRelAtWC fs cert hκ hc20 hc4 (CM := CompModel.deployed)
    w root vd ((opensWith_deployed_iff root vd w).mpr hw) args rets Lin hpre)

end
end LeanVM.Guest.B1.Digest
