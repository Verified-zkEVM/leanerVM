/-
  LeanVM.Guest.B1.Terminal.KidsDep

  Callees whose words depend on the earlier callees' results, placed: `kidsFromIn_of_kidsD` and
  `completeAt_flatD` for a list of callees each a function of the results before it.
-/

module

public import LeanVM.Guest.B1.Tables.FlatAt

/-!
# Dependent callees, placed

A flat body's callees are placed one after another (`kidsFromIn_of_kidsD`), each `CompleteAtD` on
words fixed beforehand. When a callee reads what an earlier callee returns — `column_selector`
the tables `selector_tables` returns, the terminal the buffers `certify_placement` returns —
its arguments and words depend on the earlier results. `KidD`: a callee as a function of the
results before it; `kidsAt ks prev outs`: the callees on the results `outs`.
`kidsFromIn_of_dep`: the placement of `kidsFromIn_of_kidsD` for such callees.
`completeAt_flatDep`: `completeAt_flatD` for them, each callee reading the caller's words, its
buffers, and the buffers the earlier callees return (`RegionsOk`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- A callee, as a function of the results of the callees before it. -/
abbrev KidD : Type := List (List E × Layout) → Kid

/-- The callees on the results `outs`, the results before them `prev`. -/
def kidsAt : List KidD → List (List E × Layout) → List (List E × Layout) → List Kid
  | k :: ks, prev, o :: os => k prev :: kidsAt ks (prev ++ [o]) os
  | _, _, _ => []

/-- The buffers the entered callees return. -/
def outsL : List Kid → List (List E × Layout) → Layout
  | k :: ks, o :: os => (if k.taken = true then o.2 else []) ++ outsL ks os
  | _, _ => []

theorem memL_outsL {rd : Reader} : ∀ {ks : List Kid} {outs : List (List E × Layout)} {L : Layout},
    OutsIn ks outs L → MemL rd L → MemL rd (outsL ks outs)
  | k :: ks, o :: os, L, ⟨h, hs⟩, hL => by
    intro q hq
    simp only [outsL, List.mem_append] at hq
    rcases hq with hq | hq
    · by_cases ht : k.taken = true
      · rw [ite_pos' ht] at hq; exact hL q (h ht q hq)
      · rw [ite_neg' ht] at hq; simp at hq
    · exact memL_outsL hs hL q hq
  | [], _, _, _, _ => fun q hq => by simp [outsL] at hq
  | _ :: _, [], _, _, _ => fun q hq => by simp [outsL] at hq

theorem RegionsOk.mono_R {R R' : ℕ → Prop} (hR : ∀ i, R i → R' i) :
    ∀ {Dacc : ℕ → Prop} {ks : List Kid} {outs : List (List E × Layout)},
      RegionsOk R Dacc ks outs → RegionsOk R' Dacc ks outs
  | _, _ :: _, _ :: _, ⟨h, hs⟩ => ⟨fun ht i hi => (h ht i hi).imp_left (hR i), RegionsOk.mono_R hR hs⟩
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **Dependent callees at their running offsets**: `kidsFromIn_of_kidsD`, each callee on the
results before it. -/
theorem kidsFromIn_of_dep (κ : ℕ) : ∀ (ks : List KidD) (prev : List (List E × Layout)),
    (∀ k ∈ ks, ∀ pv, (k pv).taken = true →
      CompleteAtD fs cert κ (k pv).f (k pv).Lin (k pv).args (k pv).Out) → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), outs.length = ks.length ∧
      OutsOk (kidsAt ks prev outs) outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn (kidsAt ks prev outs) outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop),
        CallsMatch σ cs (kidsAt ks prev outs) outs → LowDef κ rd → MemL rd L →
        MemL rd (Kid.lins (kidsAt ks prev outs)) → RegionsOk R Dacc (kidsAt ks prev outs) outs →
        KidsFromIn coreProgram fs cert rd σ R Dacc cs b N
          (fun i => Dacc i ∨ outRegion (kidsAt ks prev outs) outs i)
  | [], _, _, b => ⟨0, [], [], rfl, trivial, fun _ h => by simp at h, disj_nil, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | kf :: ks, prev, hok, b => by
    by_cases ht : (kf prev).taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hd, hrel⟩ := hok kf (by simp) prev ht b
      obtain ⟨N, L, outs, hlen, ho, hW, hD, hI, hK⟩ := kidsFromIn_of_dep κ ks (prev ++ [(rets, Lout)])
        (fun k' hk' => hok k' (by simp [hk'])) (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, by simp [hlen],
        ⟨fun _ => hout, ho⟩, ?_, disj_append hd hD hw hW le_rfl,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
          simp only [kidsAt, Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := Main.memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨n, N, RegionL (kf prev).Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
          · rw [hct]
            simp only [ht, ↓reduceIte]
            rw [hf, ha, hr]
            exact hrel rd hlow (Main.memL_append.mpr ⟨hL1, hLk⟩)
          · refine kidsFromIn_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · obtain ⟨N, L, outs, hlen, ho, hW, hD, hI, hK⟩ := kidsFromIn_of_dep κ ks (prev ++ [([], [])])
        (fun k' hk' => hok k' (by simp [hk'])) (b + fs (kf prev).f)
      refine ⟨fs (kf prev).f + N, L, ([], []) :: outs, by simp [hlen], ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩, ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [kidsAt, Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs (kf prev).f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · have ht' : (kf prev).taken = false := by simpa using ht
          rw [hct, ht']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hf]
        · refine kidsFromIn_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL (Main.memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this

/-- **A flat function with dependent callees is complete, placed** (`completeAt_flatD`, each
callee on the results before it, reading the caller's words, the buffers and the earlier
callees' results). -/
theorem completeAt_flatDep {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E) (rets : ℕ → List E)
    (Out : List E → Layout → Prop)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hout : ∀ fp, Out (rets fp) (bufL (fp + fs f) sizes (own fp))) (kids : ℕ → List KidD)
    (hkc : ∀ fp, ∀ k ∈ kids fp, ∀ pv, (k pv).taken = true →
      CompleteAtD fs cert κ (k pv).f (k pv).Lin (k pv).args (k pv).Out)
    (hkr : ∀ fp outs, OutsOk (kidsAt (kids fp) [] outs) outs →
      RegionsOk (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i) (fun _ => False)
        (kidsAt (kids fp) [] outs) outs)
    (hkm : ∀ fp outs, OutsOk (kidsAt (kids fp) [] outs) outs → ∀ rd,
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      MemL rd (outsL (kidsAt (kids fp) [] outs) outs) → MemL rd (Kid.lins (kidsAt (kids fp) [] outs)))
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kidsAt (kids fp) [] outs) outs → ∀ rd,
      LowDef κ rd → MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      MemL rd (outsL (kidsAt (kids fp) [] outs) outs) →
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun r => r = rets fp) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
          (kidsAt (kids fp) [] outs) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i ∨
            outRegion (kidsAt (kids fp) [] outs) outs i)) :
    CompleteAtD fs cert κ f Lin args Out := by
  intro fp
  obtain ⟨N, L, outs, -, ho, hW, hD, hI, hK⟩ := kidsFromIn_of_dep (fs := fs) (cert := cert) κ (kids fp)
    [] (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, L, rets fp, bufL (fp + fs f) sizes (own fp), hout fp, ?_,
    disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    fun rd hlow hL => ?_⟩
  · simp only [within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  have hLo := memL_outsL hI hLk
  obtain ⟨σ, hp, hdo, hh, hsz, hbuf, hcm, hld⟩ := hσ fp outs ho rd hlow hB hLin hLo
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets fp := hsat.2
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp)) i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i hi)
  have hk := hK rd σ (calls (pre.flatMap (flEvs σ))) (fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (hkm fp outs ho rd hB hLin hLo)
    ((hkr fp outs ho).mono_R fun i hi => hi.imp_right (hown' i))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL (bufL (fp + fs f) sizes (own fp)))
    (Dk := fun i => False ∨ outRegion (kidsAt (kids fp) [] outs) outs i) (N := N) (fp := fp)
    coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp)
    hk (fun A hA => ?_) (fun i hi => Or.inl (hown' i hi))
  · rw [hal] at h
    exact h
  · rw [i5] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩
    · exact ⟨i, hi, Or.inr (Or.inr (Or.inr h))⟩

end
end LeanVM.Guest.B1
