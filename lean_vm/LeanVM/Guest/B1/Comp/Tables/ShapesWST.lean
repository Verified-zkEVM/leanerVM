/-
  LeanVM.Guest.B1.Comp.Tables.ShapesWST

  The placed body shapes within weights under any semantics (`ShapesWS.lean`), by trees
  satisfying a predicate of the node and its callees' trees.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.ShapesWS
public import LeanVM.Guest.B1.Comp.TreeRoot
public import LeanVM.Guest.B1.Comp.Tables.LoadsL

/-!
# Placed bodies, their trees satisfying a predicate

`completeAtS_straightW`, `completeAtS_flatW`, `vtcS_completeAt_iteW` with the tree satisfying
`Q fp rd` (`CompleteAtWST`), the callees' trees `qk`: `Q` holds of the node at the valuation the
body holds of, its path's events holding and its callees' trees satisfying their predicates where
placed (`KidsSat`) (`completeAtS_straightWT`, `completeAtS_flatWT`, `vtcS_completeAt_iteWT`, by
`kidsFromInWST_of_kidsBW` and `relAtInWST_of_walk`). `CompleteAtWS.toWST_of_valid`: a predicate
of every valid tree on the memories holding `Lin`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL kidsBoundW kidsWs kidsWs_sum)

@[expose] public section

variable {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type}
  {w : Θ → String → ℕ}

theorem RelAtInWST.wmono {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Bw Bw' : Θ → ℕ} {Q : Tree → Prop} (h : RelAtInWST S fs cert w rd R D fp n f args rets Bw Q)
    (hB : ∀ θ, Bw θ ≤ Bw' θ) : RelAtInWST S fs cert w rd R D fp n f args rets Bw' Q :=
  let ⟨t, hq, hn, hv, hb, hp, ht, hl, hd, hw⟩ := h
  ⟨t, hq, hn, hv, hb, hp, ht, hl, hd, fun θ => (hw θ).trans (hB θ)⟩

/-- **A predicate of every valid tree**: `CompleteAtWS` by a tree satisfying `Q`, when every
valid tree of `f` on its arguments on a memory holding `Lin` does. -/
theorem CompleteAtWS.toWST_of_valid {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw : Θ → ℕ} {Q : ℕ → Reader → Tree → Prop}
    (h : Main.CompleteAtWS S fs cert w κ f Lin args Out B Bw)
    (hQ : ∀ fp rd, LowDef κ rd → MemL rd Lin → ∀ (t : Tree) (rets : List E), t.name = f →
      t.ValidB S coreProgram rd args rets → Q fp rd t) :
    CompleteAtWST S fs cert w κ f Lin args Out B Bw Q := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hn', hv, hb, hp, ht, hl', hd', hw⟩ := hr rd hl hm
    ⟨t, hQ fp rd hl (Main.memL_append.mp hm).2 t rets hn' hv, hn', hv, hb, hp, ht, hl', hd', hw⟩⟩

/-- **`completeAtS_straightW` by a tree satisfying `Q`**: `Q` of the node at the valuation the
body holds of, its callees' trees satisfying theirs. -/
theorem completeAtS_straightWT {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Main.Stmt.straight = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ) (Bk : ℕ) (Bkw : Θ → ℕ)
    (qk : Kid → ℕ → Reader → Tree → Prop) (Q : ℕ → Reader → Tree → Prop)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true →
      CompleteAtWST S fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k) (qk k))
    (hBk : ∀ fp, kidsBound fs bd (kids fp) ≤ Bk) (hBkw : ∀ fp θ, kidsBoundW bdw (kids fp) θ ≤ Bkw θ)
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        CallsMatch σ ((pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) (kids fp) outs ∧
        (∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) ∧
        (∀ es, walk σ fn.body = .ret es vs → (∀ e ∈ es, e.HoldsB S rd σ) → ∀ ks,
          Tree.KidsValidB S coreProgram rd σ (calls es) ks →
          KidsSat (calls es) ((kids fp).map fun k b t => qk k b rd t)
            (bases (fp + fs f + sizes.sum) (ks.map (Tree.total fs))) ks →
          Q fp rd (Memory.Tree.node f σ sizes ks))) :
    CompleteAtWST S fs cert w κ f Lin args (Returns rets) (fs f + sizes.sum + Bk)
      (fun θ => w θ f + Bkw θ) Q := by
  intro fp
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromInWST_of_kidsBW (S := S) (fs := fs) (cert := cert) (w := w) κ bd bdw qk (kids fp)
    (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp) ++ L, rets, [], ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    by have := hBk fp; omega, fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  obtain ⟨σ, hp, hh, hsz, hbuf, hcm, hld, hQσ⟩ := hσ fp outs ho rd hlow hB hLin
  have hw := Main.walk_straight σ vs pre hst
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ pre hst
  have hsat := walkB_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (Main.slEvs σ), e.HoldsB S rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets := hsat.2
  have hal : allocs σ (pre.flatMap (Main.slEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp)) i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (Main.slEvs σ))) (pre.flatMap (Main.slEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i hi)
  have hk := hK rd σ (calls (pre.flatMap (Main.slEvs σ))) (fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (Main.slEvs σ))) (pre.flatMap (Main.slEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (memL_lins (hkm fp rd hB hLin))
    (regionsOk_of fun k hk ht i hi => Or.inl ((hkr fp k hk ht i hi).imp_right (hown' i)))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (Main.slEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have h := relAtInWST_of_walk (S := S) (fs := fs) (cert := cert) (w := w) (R := RegionL Lin)
    (qs := (kids fp).map fun k b t => qk k b rd t) (Q := Q fp rd)
    (D := RegionL []) (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp)
    hk (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    (fun ks hkv hks => by rw [hal] at hks ⊢; exact hQσ _ hw hes ks hkv hks)
  · rw [hal] at h
    refine h.wmono fun θ => ?_
    rw [kidsWs_sum]
    exact Nat.add_le_add_left (hBkw fp θ) _
  · rw [loadAddrs_straight σ pre hst] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩

/-- **`completeAtS_flatW` by a tree satisfying `Q`.** -/
theorem completeAtS_flatWT {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ) (Bk : ℕ) (Bkw : Θ → ℕ)
    (qk : Kid → ℕ → Reader → Tree → Prop) (Q : ℕ → Reader → Tree → Prop)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true →
      CompleteAtWST S fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k) (qk k))
    (hBk : ∀ fp, kidsBound fs bd (kids fp) ≤ Bk) (hBkw : ∀ fp θ, kidsBoundW bdw (kids fp) θ ≤ Bkw θ)
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (kids fp) outs ∧
        (∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) ∧
        (∀ es, walk σ fn.body = .ret es vs → (∀ e ∈ es, e.HoldsB S rd σ) → ∀ ks,
          Tree.KidsValidB S coreProgram rd σ (calls es) ks →
          KidsSat (calls es) ((kids fp).map fun k b t => qk k b rd t)
            (bases (fp + fs f + sizes.sum) (ks.map (Tree.total fs))) ks →
          Q fp rd (Memory.Tree.node f σ sizes ks))) :
    CompleteAtWST S fs cert w κ f Lin args (Returns rets) (fs f + sizes.sum + Bk)
      (fun θ => w θ f + Bkw θ) Q := by
  intro fp
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromInWST_of_kidsBW (S := S) (fs := fs) (cert := cert) (w := w) κ bd bdw qk (kids fp)
    (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp) ++ L, rets, [], ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    by have := hBk fp; omega, fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  obtain ⟨σ, hp, hdo, hh, hsz, hbuf, hcm, hld, hQσ⟩ := hσ fp outs ho rd hlow hB hLin
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hsat := walkB_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.HoldsB S rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets := hsat.2
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp)) i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i hi)
  have hk := hK rd σ (calls (pre.flatMap (flEvs σ))) (fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (memL_lins (hkm fp rd hB hLin))
    (regionsOk_of fun k hk ht i hi => Or.inl ((hkr fp k hk ht i hi).imp_right (hown' i)))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have h := relAtInWST_of_walk (S := S) (fs := fs) (cert := cert) (w := w) (R := RegionL Lin)
    (qs := (kids fp).map fun k b t => qk k b rd t) (Q := Q fp rd)
    (D := RegionL []) (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp)
    hk (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    (fun ks hkv hks => by rw [hal] at hks ⊢; exact hQσ _ hw hes ks hkv hks)
  · rw [hal] at h
    refine h.wmono fun θ => ?_
    rw [kidsWs_sum]
    exact Nat.add_le_add_left (hBkw fp θ) _
  · rw [i5] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩

/-- **`vtcS_completeAt_iteW` by a tree satisfying `Q`.** -/
theorem vtcS_completeAt_iteWT {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre t e post : List Stmt} {c : V} {vs : List V}
    (hb : fn.body = pre ++ .ite c t e :: (post ++ [.ret vs]))
    (h1 : pre.all Main.Stmt.straight = true) (h2 : t.all Main.Stmt.straight = true)
    (h3 : e.all Main.Stmt.straight = true) (h4 : post.all Main.Stmt.straight = true) (br : Bool)
    (haddrs : (pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ) (Bk : ℕ) (Bkw : Θ → ℕ)
    (qk : Kid → ℕ → Reader → Tree → Prop) (Q : ℕ → Reader → Tree → Prop)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true →
      CompleteAtWST S fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k) (qk k))
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, (σ c = 0 ↔ br = true) ∧ fn.params.map σ = args ∧
        Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ fn.body False (fun r => r = rets) ∧
        ((pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.allocSz).map
          (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        (((pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        CallsMatch σ (((pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.callS).map
          (Main.mkCall σ)) (kids fp) outs ∧
        (∀ q ∈ (pre ++ (if br then t else e) ++ post).filterMap Stmt.loadS, ∃ i,
          (σ q.1).limb 0 * gpow q.2 = gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) ∧
        (∀ es, walk σ fn.body = .ret es vs → (∀ e ∈ es, e.HoldsB S rd σ) → ∀ ks,
          Tree.KidsValidB S coreProgram rd σ (calls es) ks →
          KidsSat (calls es) ((kids fp).map fun k b t => qk k b rd t)
            (bases (fp + fs f + sizes.sum) (ks.map (Tree.total fs))) ks →
          Q fp rd (Memory.Tree.node f σ sizes ks)))
    (hbd : ∀ fp, kidsBound fs bd (kids fp) ≤ Bk) (hbdw : ∀ fp θ, kidsBoundW bdw (kids fp) θ ≤ Bkw θ) :
    CompleteAtWST S fs cert w κ f Lin args (Returns rets) (fs f + sizes.sum + Bk)
      (fun θ => w θ f + Bkw θ) Q := by
  intro fp
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromInWST_of_kidsBW (S := S) (fs := fs) (cert := cert) (w := w) κ bd bdw qk (kids fp)
    (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp) ++ L, rets, [], ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    by have := hbd fp; omega, fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  obtain ⟨σ, hc, hp, hh, hsz, hbuf, hcm, hld, hQσ⟩ := hσ fp outs ho rd hlow hB hLin
  set lin := pre ++ (if br then t else e) ++ post with hlin
  have hbr : (if σ c = 0 then t else e) = (if br then t else e) := by
    by_cases h : σ c = 0
    · rw [ite_pos' h, ite_pos' (hc.mp h)]
    · rw [ite_neg' h, ite_neg' (fun h' => h (hc.mpr h'))]
  have hst : lin.all Main.Stmt.straight = true := by
    simp only [hlin, List.all_append, h1, h4, Bool.and_true, Bool.true_and]
    split <;> assumption
  set es := iteEvs σ pre (if br then t else e) post c with hes_def
  have hw : walk σ fn.body = .ret es vs := by rw [hb, walk_ite σ vs c pre t e post h1 h2 h3 h4, hbr]
  obtain ⟨j1, j2, j3, j4, j5⟩ := iteEvs_parts σ pre (if br then t else e) post c
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ lin hst
  have hsat := walkB_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ es, e.HoldsB S rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets := hsat.2
  have hal : allocs σ es = sizes := by rw [j2, i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp)) i →
      ownData cert fp (fp + fs f) f (allocs σ es) es i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i hi)
  have hk := hK rd σ (calls es) (fun i => RegionL Lin i ∨ ownData cert fp (fp + fs f) f (allocs σ es) es i)
    (fun _ => False) (by rw [j4, i4]; exact hcm) hlow hLk (memL_lins (hkm fp rd hB hLin))
    (regionsOk_of fun k hk ht i hi => Or.inl ((hkr fp k hk ht i hi).imp_right (hown' i)))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ es).sum := by rw [hal]
  rw [hb'] at hk
  have h := relAtInWST_of_walk (S := S) (fs := fs) (cert := cert) (w := w) (R := RegionL Lin)
    (qs := (kids fp).map fun k b t => qk k b rd t) (Q := Q fp rd)
    (D := RegionL []) (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    hf (Or.inl hl) hp hw hr hes (by rw [hal, j1, i1]; exact hbuf)
    (by rw [j3, i3, haddrs]; simp) hk (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    (fun ks hkv hks => by rw [hal] at hks ⊢; exact hQσ _ hw hes ks hkv hks)
  · rw [hal] at h
    refine h.wmono fun θ => ?_
    rw [kidsWs_sum]
    exact Nat.add_le_add_left (hbdw fp θ) _
  · rw [j5, loadAddrs_straight σ lin hst] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩

end
end LeanVM.Guest.B1
