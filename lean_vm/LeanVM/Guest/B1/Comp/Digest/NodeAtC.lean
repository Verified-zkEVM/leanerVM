/-
  LeanVM.Guest.B1.Comp.Digest.NodeAtC

  `NodeAt.lean`'s bounded node and loop lemmas under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B1.Digest.NodeAt
public import LeanVM.Guest.B1.Comp.CompleteAtB
public import LeanVM.Guest.Memory.GuestRelInB

/-!
# A function complete from its valuations, under any semantics

`completeAtS_nodeB` and `completeAtS_loopB` are `NodeAt.lean`'s `completeAt_nodeB` and
`completeAt_loopB` with `S : BlakeSem` a parameter: the events hold under `S` (`Ev.HoldsB S`), the
callees are `CompleteAtBS S`, the composition `UniformS.lean`'s `kidsFromInS_of_kidsB` and
`Memory/RegionsB.lean`'s `relAtInB_of_walk`, `relAtInB_of_walk_loop`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Guest.B1 (LowDef CompleteAtBS kidsFromInS_of_kidsB kidsBound DisjL disj_append Within
  Returns Kid OutsOk CallsMatch RegionsOk outRegion bufL)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A function with callees, complete from its valuations under `S`** (`completeAt_nodeB`): its
own words `Lb fp` lie in its `HeapBuf`s of sizes `sizes`. -/
theorem completeAtS_nodeB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E) (sizes : List ℕ)
    (Lb : ℕ → Layout) (hLb : ∀ fp i, RegionL (Lb fp) i →
      ∃ q ∈ sizes.zip (bases (fp + fs f) sizes), q.2 ≤ i ∧ i < q.2 + q.1)
    (hWb : ∀ fp, Within (Lb fp) (fp + fs f) sizes.sum) (hDb : ∀ fp, DisjL (Lb fp))
    (ks : ℕ → List KidR)
    (bd : Kid → ℕ)
    (hok : ∀ fp, ∀ k ∈ ks fp, k.taken = true →
      CompleteAtBS S fs cert κ k.f k.Lin k.args (Returns k.rets) (bd k.kid))
    (hkR : ∀ fp, ∀ k ∈ ks fp, k.taken = true → ∀ i, RegionL k.Lin i → RegionL (Lb fp) i ∨ RegionL Lin i)
    (B : ℕ) (hB : ∀ fp, fs f + sizes.sum + kidsBound fs bd ((ks fp).map KidR.kid) ≤ B)
    (hσ : ∀ fp rd, LowDef κ rd → MemL rd (Lb fp) → MemL rd Lin →
      (∀ k ∈ ks fp, MemL rd k.Lin) ∧ ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.HoldsB S rd σ) ∧
        CallsR σ (calls es) (ks fp) ∧ addrs es = [] ∧ allocs σ es = sizes ∧
        (allocDsts es).map σ = (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ (RegionL (Lb fp) i ∨ RegionL Lin i)) :
    CompleteAtBS S fs cert κ f Lin args (Returns rets) B := by
  intro fp
  have hok' : ∀ k ∈ (ks fp).map KidR.kid, k.taken = true →
      CompleteAtBS S fs cert κ k.f k.Lin k.args k.Out (bd k) := by
    intro k hk ht
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact hok fp k' hk' ht
  obtain ⟨N, LK, outs, ho, hW, hD, hNb, -, hK⟩ :=
    kidsFromInS_of_kidsB (S := S) (fs := fs) (cert := cert) κ bd _ hok' (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, Lb fp ++ LK, rets, [], ⟨rfl, rfl⟩, ?_, ?_, le_trans (by omega) (hB fp),
    fun rd hlow hL => ?_⟩
  · rw [List.nil_append, LeanVM.Guest.B1.within_append]
    exact ⟨(hWb fp).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append (hDb fp) hD (hWb fp) hW (by omega)
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLb', hLK⟩ := Main.memL_append.mp hLo
  obtain ⟨hkL, σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload⟩ := hσ fp rd hlow hLb' hLin
  have hbo : ∀ i, RegionL (Lb fp) i → ownData cert fp (fp + fs f) f (allocs σ es) es i := fun i hi => by
    rw [hal]; exact Or.inl (hLb fp i hi)
  have h := relAtInB_of_walk (S := S) (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion ((ks fp).map KidR.kid) outs i)
    (fp := fp) (N := N) hf (Or.inl hl) hp hw hr hes (by rw [hal]; exact hbuf) (by rw [ha]; simp) ?_ ?_
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rwa [hal] at h
  · rw [hal]
    refine hK rd σ _ _ (fun _ => False) (callsMatch_of hc ho) hlow hLK (memL_lins_of fun k hk => ?_)
      (regionsOk_all fun k hk ht i hi => ?_)
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact hkL k' hk'
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      rcases hkR fp k' hk' ht i hi with h | h
      · exact Or.inr (by rw [← hal]; exact hbo i h)
      · exact Or.inl h
  · intro A hA
    obtain ⟨i, rfl, h | h⟩ := hload A hA
    · exact ⟨i, rfl, Or.inl (hbo i h)⟩
    · exact ⟨i, rfl, Or.inr (Or.inl h)⟩

/-- **A loop helper without buffers, complete from its valuations under `S`**
(`completeAt_loopB`), its tail call last. -/
theorem completeAtS_loopB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) (κ : ℕ) (Lin : Layout) (args rets : List E) (ks : List KidR)
    (tail : KidR)
    (bd : Kid → ℕ) (bt : ℕ)
    (hok : ∀ k ∈ ks, k.taken = true →
      CompleteAtBS S fs cert κ k.f k.Lin k.args (Returns k.rets) (bd k.kid))
    (htail : tail.taken = true →
      CompleteAtBS S fs cert κ tail.f tail.Lin tail.args (Returns tail.rets) bt)
    (B : ℕ) (hB : fs f + max bt (fs tail.f) + kidsBound fs bd (ks.map KidR.kid) ≤ B)
    (hkR : ∀ k ∈ ks ++ [tail], k.taken = true → ∀ i, RegionL k.Lin i → RegionL Lin i)
    (hσ : ∀ rd, LowDef κ rd → MemL rd Lin →
      (∀ k ∈ ks ++ [tail], MemL rd k.Lin) ∧ ∃ (σ : Val) (es : List Ev) (vs : List V),
        fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.HoldsB S rd σ) ∧
        CallsR σ (calls es) (ks ++ [tail]) ∧ addrs es = [] ∧ allocs σ es = [] ∧ allocDsts es = [] ∧
        ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ RegionL Lin i) :
    CompleteAtBS S fs cert κ f Lin args (Returns rets) B := by
  intro fp
  classical
  have hok' : ∀ k ∈ ks.map KidR.kid, k.taken = true →
      CompleteAtBS S fs cert κ k.f k.Lin k.args k.Out (bd k) := by
    intro k hk ht
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact hok k' hk' ht
  -- the tail, at `fp + fs f`
  obtain ⟨m, Lt, hWt, hDt, hmb, hT⟩ : ∃ (m : ℕ) (Lt : Layout), Within Lt (fp + fs f) m ∧ DisjL Lt ∧
      m ≤ max bt (fs tail.f) ∧
      ∀ rd, LowDef κ rd → MemL rd Lt → MemL rd tail.Lin →
        if tail.taken then RelAtInB S coreProgram fs cert rd (RegionL tail.Lin) (RegionL []) (fp + fs f) m
          tail.f tail.args tail.rets else m = fs tail.f := by
    by_cases ht : tail.taken = true
    · obtain ⟨m, Lown, rets', Lout, ⟨rfl, rfl⟩, hW, hDw, hmb, hR⟩ := htail ht (fp + fs f)
      refine ⟨m, Lown, by simpa using hW, by simpa using hDw, le_trans hmb (le_max_left _ _),
        fun rd hl hL hL' => ?_⟩
      rw [ite_pos' ht]
      exact hR rd hl (by simpa using Main.memL_append.mpr ⟨hL, hL'⟩)
    · refine ⟨fs tail.f, [], fun q hq => by simp at hq, LeanVM.Guest.B1.disj_nil, le_max_right _ _,
        fun rd _ _ _ => ?_⟩
      rw [ite_neg' ht]
  obtain ⟨N, LK, outs, ho, hW, hD, hNb, -, hK⟩ :=
    kidsFromInS_of_kidsB (S := S) (fs := fs) (cert := cert) κ bd _ hok' (fp + fs f + m)
  refine ⟨fs f + m + 0 + N, Lt ++ LK, rets, [], ⟨rfl, rfl⟩, ?_, ?_, le_trans (by omega) hB,
    fun rd hlow hL => ?_⟩
  · rw [List.nil_append, LeanVM.Guest.B1.within_append]
    exact ⟨hWt.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append hDt hD hWt hW le_rfl
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLt, hLK⟩ := Main.memL_append.mp hLo
  obtain ⟨hkL, σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload⟩ := hσ rd hlow hLin
  obtain ⟨cs, c, hcs, hc1, ⟨ct1, ct2, ct3, -⟩⟩ := callsR_snoc hc
  have hTr := hT rd hlow hLt (hkL tail (by simp))
  have h := relAtInB_of_walk_loop (S := S) (P := coreProgram) (fs := fs) (cert := cert) (rd := rd)
    coreProgram_wf
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion (ks.map KidR.kid) outs i)
    (Rt := fun i => tail.taken = true ∧ RegionL tail.Lin i) (Dt := RegionL []) (fp := fp) (m := m)
    (N := N) (c := c) (cs := cs) hf hl hp hw hr
    hes hcs ?_ (by rw [hbuf, hal]; rfl) (by rw [ha]; simp) ?_ ?_ ?_
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rwa [hal] at h
  · by_cases ht : tail.taken = true
    · rw [ct2, ite_pos' ht, ct1, (ct3 ht).1, (ct3 ht).2]
      rw [ite_pos' ht] at hTr
      exact hTr.mono fun i hi => ⟨ht, hi⟩
    · have ht' : tail.taken = false := by simpa using ht
      rw [ct2, ht', ct1]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ht'] at hTr
      exact hTr
  · rw [hal, List.sum_nil, Nat.add_zero]
    refine hK rd σ _ _ (fun _ => False) (callsMatch_of hc1 ho) hlow hLK (memL_lins_of fun k hk => ?_)
      (regionsOk_all fun k hk ht i hi => ?_)
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact hkL k' (List.mem_append_left _ hk')
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact Or.inl (hkR k' (List.mem_append_left _ hk') ht i hi)
  · intro i ⟨ht, hi⟩
    exact Or.inl (hkR tail (by simp) ht i hi)
  · intro A hA
    obtain ⟨i, rfl, h⟩ := hload A hA
    exact ⟨i, rfl, Or.inr (Or.inl h)⟩

end
end LeanVM.Guest.B1.Digest
