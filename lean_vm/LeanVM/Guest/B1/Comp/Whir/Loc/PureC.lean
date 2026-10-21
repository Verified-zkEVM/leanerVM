/-
  LeanVM.Guest.B1.Comp.Whir.Loc.PureC

  `open_stacked`'s pure callees' tree sizes under any semantics.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.Loc.OsInstBaseB
public import LeanVM.Guest.B1.Whir.OsPureInst
public import LeanVM.Guest.Memory.StaticSoundB
public import LeanVM.Guest.Memory.SizeTotalB
public import LeanVM.Guest.B1.Comp.FreeTree

/-!
# The pure callees' sizes under any semantics

`osPureSizesC CM fs`: `OsPureSizes` (`Whir/OsPureInst.lean`) under `CM.sem`, at the same bounds
(`osCapBds`, `osResBds`): the caps by their static certificates under any semantics
(`os_capLoop_totC`, `weightLeB_of_stat`), the residual loops free of `BLAKE2S` (`validB_freeOn`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.E2E.Complete

@[expose] public section

/-- **A function calling only a self-calling loop helper**, its certificate constant. -/
theorem os_capLoop_totC {S : BlakeSem} (fs : String → ℕ) {j jl : ℕ} (hj : j < coreProgram.length) (hjl : jl < coreProgram.length)
    {f g : String} (hn : coreProgram[j].name = f) (hnl : coreProgram[jl].name = g) (hfg : f ≠ g)
    (hc : (Stmt.blockCallees coreProgram[j].body).all (· == g) = true)
    (hcl : (Stmt.blockCallees coreProgram[jl].body).all (· == g) = true)
    {w wl : ℕ × List String} (hw : Stmt.blockWords coreProgram[j].body = some w)
    (hwl : Stmt.blockWords coreProgram[jl].body = some wl)
    {B : ℕ} {ks : List (V × ℕ)} (hcf : staticCertOf f = .stat [] ⟨B, []⟩ ks) {cf cl : ℕ} (hωf : omegaOf f = cf)
    (hωl : omegaOf g = cl) (hcl0 : 0 < cl) :
    TotalLeB S coreProgram fs f fun _ => fs f + wordsVal fs w + (B - cf) / cl * (fs g + wordsVal fs wl) := by
  have hf := core_find hj hn
  have hg := core_find hjl hnl
  obtain ⟨-, hcg⟩ := self_hyps (fs := fs) hjl hnl hcl hwl
  let ω' : String → ℕ := fun h => if h = f then fs f + wordsVal fs w else fs g + wordsVal fs wl
  have hloc : LocLe coreProgram fs ω' (fun h => h = f ∨ h = g) := locLe_of_words fun h hh fn hfn => by
    rcases hh with rfl | rfl
    · rw [hf, Option.some.injEq] at hfn; subst hfn; exact ⟨w, hw, by simp [ω']⟩
    · rw [hg, Option.some.injEq] at hfn; subst hfn; exact ⟨wl, hwl, by simp [ω', Ne.symm hfg]⟩
  have hcin : CallsIn coreProgram (fun h => h = f ∨ h = g) := callsIn_of_callees fun h hh fn hfn h' hh' => by
    rcases hh with rfl | rfl
    · rw [hf, Option.some.injEq] at hfn; subst hfn; exact Or.inr (by simpa using List.all_eq_true.mp hc h' hh')
    · rw [hg, Option.some.injEq] at hfn; subst hfn; exact Or.inr (by simpa using List.all_eq_true.mp hcl h' hh')
  intro rd t args rets htn hv hb
  have htot := totalB_le_weight hloc hcin t (Or.inl htn) hv hb
  have hwB : t.weight omegaOf ≤ B := weightLeB_of_stat coreProgram_checked hcf rd t args rets htn hv hb
  match t, hv with
  | .node f' σ bufs kids, hv' =>
    simp only [Tree.name] at htn
    subst f'
    obtain ⟨fn, hfn, -, es, vs, hwk, -, -, hk⟩ := hv'
    rw [hf, Option.some.injEq] at hfn
    subst hfn
    have hcs : ∀ c ∈ calls es, c.f = g := fun c hc' => by
      have := walk_callees (σ := σ) coreProgram[j].body (c := c) (by rw [hwk]; exact hc')
      simpa using List.all_eq_true.mp hc _ this
    rw [Tree.weight, weightKidsB_self hcg kids hk hcs, hωf, hωl] at hwB
    rw [Tree.weight, weightKidsB_self hcg kids hk hcs] at htot
    have hn' : Tree.weightKids (fun _ => 1) kids ≤ (B - cf) / cl :=
      (Nat.le_div_iff_mul_le hcl0).mpr (by rw [Nat.mul_comm]; omega)
    have e1 : ω' f = fs f + wordsVal fs w := by simp [ω']
    have e2 : ω' g = fs g + wordsVal fs wl := by simp [ω', Ne.symm hfg]
    rw [e1, e2] at htot
    exact htot.trans (Nat.add_le_add_left (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn') _)

set_option maxRecDepth 100000 in
/-- **The pure callees' sizes**, at every frame size. -/
theorem osPureSizes_capC {S : BlakeSem} (fs : String → ℕ) : ∀ name ∈ osCapNames,
    TotalLeB S coreProgram fs name fun _ => osPairsMax (osCapBds fs) name := by
  intro name hname
  simp only [osCapNames, List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with rfl | rfl | rfl | rfl | rfl
  · exact fun rd t a r hn hv hb => (os_capLoop_totC (S := S) fs (j := 674) (jl := 1006) (f := "verify_merkle_cap__L4") (g := "__loop454")
      (w := (0, ["__loop454"])) (wl := (0, ["__loop454"])) (B := 512) (cf := 29) (cl := 69)
      (by rw [coreProgram_length]; decide) (by rw [coreProgram_length]; decide) (by decide +kernel) (by decide +kernel)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by rw [certOf_of_idx (j := 674) (by decide +kernel)]; rfl) (by rw [omegaOf_of_idx (j := 674) (by decide +kernel)]; rfl)
      (by rw [omegaOf_of_idx (j := 1006) (by decide +kernel)]; rfl) (by decide) rd t a r hn hv hb).trans
      (osPairsMax_ge (List.mem_cons_self))
  · exact fun rd t a r hn hv hb => (os_capLoop_totC (S := S) fs (j := 586) (jl := 978) (f := "verify_merkle_cap__L5") (g := "__loop433")
      (w := (0, ["__loop433"])) (wl := (0, ["__loop433"])) (B := 1064) (cf := 29) (cl := 69)
      (by rw [coreProgram_length]; decide) (by rw [coreProgram_length]; decide) (by decide +kernel) (by decide +kernel)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by rw [certOf_of_idx (j := 586) (by decide +kernel)]; rfl) (by rw [omegaOf_of_idx (j := 586) (by decide +kernel)]; rfl)
      (by rw [omegaOf_of_idx (j := 978) (by decide +kernel)]; rfl) (by decide) rd t a r hn hv hb).trans
      (osPairsMax_ge (List.mem_cons_of_mem _ (List.mem_cons_self)))
  · exact fun rd t a r hn hv hb => (os_capLoop_totC (S := S) fs (j := 583) (jl := 975) (f := "verify_merkle_cap__L6") (g := "__loop431")
      (w := (0, ["__loop431"])) (wl := (0, ["__loop431"])) (B := 2168) (cf := 29) (cl := 69)
      (by rw [coreProgram_length]; decide) (by rw [coreProgram_length]; decide) (by decide +kernel) (by decide +kernel)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by rw [certOf_of_idx (j := 583) (by decide +kernel)]; rfl) (by rw [omegaOf_of_idx (j := 583) (by decide +kernel)]; rfl)
      (by rw [omegaOf_of_idx (j := 975) (by decide +kernel)]; rfl) (by decide) rd t a r hn hv hb).trans
      (osPairsMax_ge (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
  · exact fun rd t a r hn hv hb => (os_capLoop_totC (S := S) fs (j := 683) (jl := 1008) (f := "verify_merkle_cap__L7") (g := "__loop456")
      (w := (0, ["__loop456"])) (wl := (0, ["__loop456"])) (B := 4376) (cf := 29) (cl := 69)
      (by rw [coreProgram_length]; decide) (by rw [coreProgram_length]; decide) (by decide +kernel) (by decide +kernel)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by rw [certOf_of_idx (j := 683) (by decide +kernel)]; rfl) (by rw [omegaOf_of_idx (j := 683) (by decide +kernel)]; rfl)
      (by rw [omegaOf_of_idx (j := 1008) (by decide +kernel)]; rfl) (by decide) rd t a r hn hv hb).trans
      (osPairsMax_ge (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
  · exact fun rd t a r hn hv hb => (os_capLoop_totC (S := S) fs (j := 579) (jl := 972) (f := "verify_merkle_cap__L8") (g := "__loop429")
      (w := (0, ["__loop429"])) (wl := (0, ["__loop429"])) (B := 8792) (cf := 29) (cl := 69)
      (by rw [coreProgram_length]; decide) (by rw [coreProgram_length]; decide) (by decide +kernel) (by decide +kernel)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by rw [certOf_of_idx (j := 579) (by decide +kernel)]; rfl) (by rw [omegaOf_of_idx (j := 579) (by decide +kernel)]; rfl)
      (by rw [omegaOf_of_idx (j := 972) (by decide +kernel)]; rfl) (by decide) rd t a r hn hv hb).trans
      (osPairsMax_ge (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))


/-- The residual loops are free of `BLAKE2S`. -/
theorem osRes_freeOn : osResLoops.all (fun p => coreProgram.FreeOn [p.1]) = true := by decide +kernel

/-- **The pure callees' sizes over a model**, at the deployed bounds. -/
noncomputable def osPureSizesC (CM : CompModel) (fs : String → ℕ) : OsPureSizesC CM fs where
  capB := (osPureSizes fs).capB
  cap := osPureSizes_capC fs
  resB := (osPureSizes fs).resB
  res := fun p hp rd t args rets hn ha hv hb =>
    (osPureSizes fs).res p hp rd t args rets hn ha
      (by
        have hf := List.all_eq_true.mp osRes_freeOn p hp
        rw [← validB_deployed]
        exact (validB_freeOn (S' := blakeDeployed) hf t args rets (by rw [hn]; exact List.mem_singleton_self _)).mp hv)
      hb

end
end LeanVM.Guest.B1
