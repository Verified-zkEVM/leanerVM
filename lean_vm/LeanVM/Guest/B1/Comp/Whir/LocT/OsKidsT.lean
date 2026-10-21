/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsKidsT

  `open_stacked`'s callees, bounded, over a completeness model, each level's later callees' trees
  satisfying a predicate (`Loc/OsKidsBd.lean` with predicates).
-/

module

public import LeanVM.Guest.B1.Comp.Whir.Loc.OsKidsBd
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsKidsAB
public import LeanVM.Guest.B1.Comp.Whir.LocT.Loads
public import LeanVM.Guest.B1.Comp.Whir.LocT.LoopT

/-!
# The callees with predicates

`os_kids_blockBCT`, `os_levels_kidsBCT`: `os_kids_blockBC`, `os_levels_kidsBC` giving
`KidsFromInWST` (no weights, `wE`): a level `l`'s calls after its query-position loop (`OsLvK.B`)
by trees satisfying `QB l f args`, the others by any trees (`osLvsQs`). `kidsSat_zip`: the callee
tree of an entered call, with its predicate, from `KidsSat`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {CM : CompModel} {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## Calls and their trees' predicates -/

/-- **The callee tree of an entered call, with its predicate**: for `(c, q)` of `cs.zip qs`. -/
theorem kidsSat_zip {S : BlakeSem} {rd : Reader} {σ : Val} {V : FrameVals} :
    ∀ {cs : List Call} {qs : List (ℕ → Tree → Prop)} {bs : List ℕ} {ks : List Tree},
      Tree.KidsValidB S coreProgram rd σ cs ks → KidsSat cs qs bs ks → KidsLinkCalls V σ cs ks →
      bs.length = ks.length → ∀ p ∈ cs.zip qs, p.1.taken = true → ∃ k ∈ ks, ∃ b, p.2 b k ∧
        k.ValidB S coreProgram rd (p.1.args.map σ) (p.1.rets.map σ) ∧ k.name = p.1.f ∧
        (p.1.f ∈ osDecNames → B2C.NodeAgree k (V p.1.f (p.1.args.map σ) (p.1.rets.map σ)))
  | [], _, _, _, _, _, _, _, p, hp, _ => by simp at hp
  | _ :: _, [], _, _, _, _, _, _, p, hp, _ => by simp at hp
  | _ :: _, _ :: _, _, [], hv, _, _, _, _, _, _ => by simp [Tree.KidsValidB] at hv
  | _ :: _, _ :: _, [], _ :: _, _, _, _, hbl, _, _, _ => absurd hbl (by simp)
  | c :: cs, q :: qs, b :: bs, k :: ks, hv, hs, hl, hbl, p, hp, ht => by
    simp only [KidsSat] at hs
    simp only [Tree.KidsValidB] at hv
    rw [KidsLinkCalls] at hl
    rw [List.zip_cons_cons] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · have hv1 := hv.2.1
      rw [ite_eq_left ht] at hv1
      exact ⟨k, List.mem_cons_self, b, hs.1 ht, hv1, hv.1, hl.1 ht⟩
    · obtain ⟨k', hk', b', h1, h2, h3, h4⟩ := kidsSat_zip hv.2.2 hs.2 hl.2 (by simpa using hbl) p hp ht
      exact ⟨k', List.mem_cons_of_mem _ hk', b', h1, h2, h3, h4⟩

theorem kidsWs_emptyE (bdw : Kid → Empty → ℕ) (ks : List Kid) : Main.kidsWs bdw ks = ks.map fun _ => bwE :=
  List.map_congr_left fun _ _ => funext fun θ => θ.elim

/-! ## Blocks of calls -/

theorem os_callsMatch_mapT (σ : Val) (Lk : Layout) : ∀ (cs : List Call) (outs : List (List E × Layout)),
    OutsOk (osKidsOf σ Lk cs) outs → CallsMatch σ cs (osKidsOf σ Lk cs) outs
  | [], [], _ => trivial
  | _ :: cs, _ :: os, ⟨ho, hos⟩ => ⟨rfl, rfl, fun ht => ⟨rfl, (ho ht).1.symm⟩, os_callsMatch_mapT σ Lk cs os hos⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **`os_kids_blockBC` with predicates.** -/
theorem os_kids_blockBCT (κ : ℕ) (Lk : Layout) (σ : Val) (cs : List Call) (bd : String → List E → ℕ)
    (QB : String → List E → ℕ → Reader → Tree → Prop)
    (hc : ∀ c ∈ cs, c.taken = true →
      CompleteAtBST CM.sem fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (bd c.f (c.args.map σ))
        (QB c.f (c.args.map σ)))
    (b : ℕ) :
    ∃ (N : ℕ) (L : Layout), Within L b N ∧ DisjL L ∧ N ≤ osCallsBound fs σ bd cs ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd →
      MemL rd L → MemL rd Lk → (∀ i, RegionL Lk i → R i ∨ Dacc i) →
      KidsFromInWST CM.sem fs cert wE rd σ R Dacc cs (cs.map fun _ => bwE)
        (cs.map fun c b t => QB c.f (c.args.map σ) b rd t) b N (fun _ => False) := by
  obtain ⟨N, L, outs, ho, hW, hD, hN, -, hK⟩ := kidsFromInWST_of_kidsBW (S := CM.sem) (fs := fs) (cert := cert)
    (w := wE) κ (fun k => bd k.f k.args) (fun _ => bwE) (fun k => QB k.f k.args) (osKidsOf σ Lk cs)
    (fun k hk ht => by
      obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hk
      exact (hc c hc' ht).toWSTE) b
  refine ⟨N, L, hW, hD, ?_, fun rd R Dacc hlow hL hLk hR => ?_⟩
  · refine le_trans hN (le_of_eq ?_)
    simp [kidsBound, osCallsBound, osKidsOf, List.map_map, Function.comp_def]
  · have := hK rd σ cs R Dacc (os_callsMatch_mapT σ Lk cs outs ho) hlow hL ?_ ?_
    · rw [kidsWs_emptyE] at this
      simp only [osKidsOf, List.map_map, Function.comp_def] at this
      exact kidsFromInWST_dend cs _ _ _ _ _ (fun _ h => h.elim) this
    · intro q hq
      obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
      exact hLk q hq
    · refine regionsOk_of fun k hk _ i hi => ?_
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
      exact hR i hi

/-- **`os_kidsFromIn_onePBC` with predicates** (any tree). -/
theorem os_kidsFromIn_onePBCT {κ : ℕ} {f : String} {Lin : ℕ → Layout} {args rets : List E} {Lout : ℕ → Layout} {B : ℕ}
    (h : OsCompleteAtPBC CM fs cert κ f Lin args rets Lout B) (σ : Val) (c : Call) (hf : c.f = f) (ht : c.taken = true)
    (ha : c.args.map σ = args) (hr : c.rets.map σ = rets) (b : ℕ) :
    ∃ (n : ℕ) (Lown : Layout), Within (Lout b ++ Lown) b n ∧ DisjL (Lout b ++ Lown) ∧ n ≤ B ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd (Lout b ++ Lown) → MemL rd (Lin b) →
        (∀ i, RegionL (Lin b) i → R i ∨ Dacc i) →
        KidsFromInWST CM.sem fs cert wE rd σ R Dacc [c] [bwE] [fun _ _ => True] b n (RegionL (Lout b)) := by
  obtain ⟨n, Lown, hW, hD, hn, hrel⟩ := h b
  refine ⟨n, Lown, hW, hD, hn, fun rd R Dacc hlow hL hLin hR =>
    ⟨n, 0, RegionL (Lin b), RegionL (Lout b), by omega, hR, ?_, ⟨rfl, fun i hi => Or.inr ⟨ht, hi⟩⟩⟩⟩
  simp only [ht, ↓reduceIte]
  rw [hf, ha, hr]
  obtain ⟨t, h1, h2, h3, h4, h5, h6, h7⟩ := hrel rd hlow (Main.memL_append.mpr ⟨hL, hLin⟩)
  exact ⟨t, trivial, h1, h2, h3, h4, h5, h6, h7, fun θ => θ.elim⟩

/-! ## The levels -/

/-- A level's callees by bounded trees, those after the loop satisfying `QB`. -/
structure OsLvKOkBCT (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (Lk : Layout)
    (W S : ℕ → Layout) (bd : String → List E → ℕ) (QB : String → List E → ℕ → Reader → Tree → Prop)
    (k : OsLvK) : Prop where
  A : ∀ c ∈ k.A, c.taken = true →
    CompleteAtBS CM.sem fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (bd c.f (c.args.map σ))
  taken : k.sq.taken = true
  sq : OsCompleteAtPBC CM fs cert κ k.sq.f (fun p => Lk ++ W p) (k.sq.args.map σ) (k.sq.rets.map σ) S
    (bd k.sq.f (k.sq.args.map σ))
  B : ∀ p, ∀ c ∈ k.B, c.taken = true →
    CompleteAtBST CM.sem fs cert κ c.f (Lk ++ W p ++ S p) (c.args.map σ) (Returns (c.rets.map σ)) (bd c.f (c.args.map σ))
      (QB c.f (c.args.map σ))

/-- The levels' callees' predicates: level `l`'s calls after the loop `QB l`, the others none. -/
def osLvsQs (QB : ℕ → String → List E → ℕ → Tree → Prop) (σ : Val) : ℕ → List OsLvK → List (ℕ → Tree → Prop)
  | _, [] => []
  | l, k :: ks => (k.A.map fun _ => fun (_ : ℕ) (_ : Tree) => True) ++ ((fun _ _ => True) :: k.B.map fun c => QB l c.f (c.args.map σ)) ++
      osLvsQs QB σ (l + 1) ks

theorem length_osLvsQs (QB : ℕ → String → List E → ℕ → Tree → Prop) (σ : Val) :
    ∀ (l : ℕ) (ks : List OsLvK), (osLvsQs QB σ l ks).length = (ks.flatMap OsLvK.calls).length
  | _, [] => rfl
  | l, k :: ks => by
    simp only [osLvsQs, List.flatMap_cons, OsLvK.calls, List.length_append, List.length_map, List.length_cons,
      length_osLvsQs QB σ (l + 1) ks]

theorem mem_zip_map_self {α β : Type} (g : α → β) : ∀ (l : List α), ∀ c ∈ l, (c, g c) ∈ l.zip (l.map g)
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, c, h => by
    rw [List.map_cons, List.zip_cons_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_zip_map_self g l c h)

/-- **A later call of level `l0 + i` with its predicate** is among the calls zipped with `osLvsQs`. -/
theorem osLvsQs_zip_mem (QB : ℕ → String → List E → ℕ → Tree → Prop) (σ : Val) :
    ∀ (ks : List OsLvK) (l0 i : ℕ) (hi : i < ks.length), ∀ c ∈ ks[i].B,
      (c, QB (l0 + i) c.f (c.args.map σ)) ∈ (ks.flatMap OsLvK.calls).zip (osLvsQs QB σ l0 ks)
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | k :: ks, l0, i, hi, c, hc => by
    simp only [List.flatMap_cons, osLvsQs, OsLvK.calls, List.append_assoc, List.cons_append]
    rw [List.zip_append (by simp), List.zip_cons_cons, List.zip_append (by simp)]
    refine List.mem_append_right _ (List.mem_cons_of_mem _ ?_)
    rcases i with _ | i
    · simp only [List.getElem_cons_zero] at hc
      exact List.mem_append_left _ (by simpa using mem_zip_map_self (fun c => QB l0 c.f (c.args.map σ)) k.B c hc)
    · simp only [List.getElem_cons_succ] at hc
      refine List.mem_append_right _ ?_
      have := osLvsQs_zip_mem QB σ ks (l0 + 1) i (by simpa using hi) c hc
      rwa [show l0 + 1 + i = l0 + (i + 1) by omega] at this

private theorem os_regionL_appendT {L L' : Layout} {i : ℕ} (h : RegionL (L ++ L') i) : RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

/-- **`os_levels_kidsBC` with predicates.** -/
theorem os_levels_kidsBCT (κ : ℕ) (σ : Val) (Lk : Layout) (W S : ℕ → ℕ → Layout) (bd : String → List E → ℕ)
    (QB : ℕ → String → List E → ℕ → Reader → Tree → Prop) :
    ∀ (ks : List OsLvK) (l0 : ℕ), (∀ i (h : i < ks.length),
      OsLvKOkBCT CM fs cert κ σ Lk (W (l0 + i)) (S (l0 + i)) bd (QB (l0 + i)) ks[i]) →
      ∀ b, ∃ (N : ℕ) (L : Layout) (ps : List ℕ), ps.length = ks.length ∧ Within L b N ∧ DisjL L ∧
        N ≤ osCallsBound fs σ bd (ks.flatMap OsLvK.calls) ∧
        ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd L → MemL rd Lk →
          (∀ i (h : i < ps.length), MemL rd (W (l0 + i) ps[i])) → (∀ i, RegionL Lk i → R i) →
          (∀ l, l0 ≤ l → l < l0 + ks.length → ∀ p i, RegionL (W l p) i → R i) →
          KidsFromInWST CM.sem fs cert wE rd σ R Dacc (ks.flatMap OsLvK.calls)
            ((ks.flatMap OsLvK.calls).map fun _ => bwE) (osLvsQs (fun l f a b t => QB l f a b rd t) σ l0 ks) b N
            (fun _ => False)
  | [], _, _, b => ⟨0, [], [], rfl, fun _ h => by simp at h, disj_nil, Nat.zero_le _, fun _ _ _ _ _ _ _ _ _ =>
      ⟨rfl, fun _ h => h.elim⟩⟩
  | k :: ks, l0, hok, b => by
    have h0 := hok 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    obtain ⟨NA, LA, hWA, hDA, hNA, hKA⟩ := os_kids_blockBCT (CM := CM) (fs := fs) (cert := cert) κ Lk σ k.A bd
      (fun _ _ _ _ _ => True) (fun c hc ht => (h0.A c hc ht).toBST) b
    obtain ⟨nS, LS, hWS, hDS, hNS, hKS⟩ := os_kidsFromIn_onePBCT (CM := CM) h0.sq σ k.sq rfl h0.taken rfl rfl (b + NA)
    obtain ⟨NB, LB, hWB, hDB, hNB, hKB⟩ := os_kids_blockBCT (CM := CM) (fs := fs) (cert := cert) κ
      (Lk ++ W l0 (b + NA) ++ S l0 (b + NA)) σ k.B bd (QB l0) (h0.B (b + NA)) (b + NA + nS)
    obtain ⟨Nr, Lr, ps, hps, hWr, hDr, hNr, hKr⟩ := os_levels_kidsBCT κ σ Lk W S bd QB ks (l0 + 1) (fun i hi => by
      have := hok (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ, show l0 + (i + 1) = l0 + 1 + i by omega] at this
      exact this) (b + NA + nS + NB)
    have hW3 : Within (LB ++ Lr) (b + NA + nS) (NB + Nr) := by
      rw [within_append]; exact ⟨hWB.mono le_rfl (by omega), hWr.mono (by omega) (by omega)⟩
    have hW2 : Within ((S l0 (b + NA) ++ LS) ++ (LB ++ Lr)) (b + NA) (nS + (NB + Nr)) := by
      rw [within_append]; exact ⟨hWS.mono le_rfl (by omega), hW3.mono (by omega) (by omega)⟩
    refine ⟨NA + (nS + (NB + Nr)), LA ++ ((S l0 (b + NA) ++ LS) ++ (LB ++ Lr)), (b + NA) :: ps,
      by simp [hps], ?_, disj_append hDA (disj_append hDS (disj_append hDB hDr hWB hWr le_rfl) hWS hW3 le_rfl) hWA
        hW2 le_rfl, ?_, ?_⟩
    · rw [within_append]
      exact ⟨hWA.mono le_rfl (by omega), hW2.mono (by omega) (by omega)⟩
    · simp only [List.flatMap_cons, OsLvK.calls, osCallsBound_append, osCallsBound_cons, h0.taken, ↓reduceIte]
      omega
    · intro rd R Dacc hlow hL hLk hWm hR hRW
      obtain ⟨hLA, hL'⟩ := Main.memL_append.mp hL
      obtain ⟨hLS, hL''⟩ := Main.memL_append.mp hL'
      obtain ⟨hLB, hLr⟩ := Main.memL_append.mp hL''
      have hW0 : MemL rd (W l0 (b + NA)) := hWm 0 (by simp)
      have hS0 : MemL rd (S l0 (b + NA)) := (Main.memL_append.mp hLS).1
      simp only [List.flatMap_cons, OsLvK.calls, osLvsQs, List.map_append, List.map_cons, List.append_assoc,
        List.cons_append]
      refine kidsFromInWST_append _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp)
        (hKA rd R Dacc hlow hLA hLk fun i hi => Or.inl (hR i hi)) ?_
      intro D1 _
      rw [show k.sq :: (k.B ++ ks.flatMap OsLvK.calls) = [k.sq] ++ (k.B ++ ks.flatMap OsLvK.calls) from rfl,
        show bwE :: ((k.B.map fun _ => bwE) ++ (ks.flatMap OsLvK.calls).map fun _ => bwE) =
          [bwE] ++ ((k.B.map fun _ => bwE) ++ (ks.flatMap OsLvK.calls).map fun _ => bwE) from rfl,
        show ((fun _ _ => True) :: ((k.B.map fun c b t => QB l0 c.f (c.args.map σ) b rd t) ++
            osLvsQs (fun l f a b t => QB l f a b rd t) σ (l0 + 1) ks) : List (ℕ → Tree → Prop)) =
          [fun _ _ => True] ++ ((k.B.map fun c b t => QB l0 c.f (c.args.map σ) b rd t) ++
            osLvsQs (fun l f a b t => QB l f a b rd t) σ (l0 + 1) ks) from rfl]
      refine kidsFromInWST_append _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
        (hKS rd R D1 hlow hLS (Main.memL_append.mpr ⟨hLk, hW0⟩) fun i hi => ?_) ?_
      · rcases os_regionL_appendT hi with hi | hi
        · exact Or.inl (hR i hi)
        · exact Or.inl (hRW l0 le_rfl (by simp) _ i hi)
      intro D2 hD2
      refine kidsFromInWST_append _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp) (hKB rd R D2 hlow hLB
        (Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨hLk, hW0⟩, hS0⟩) fun i hi => ?_) ?_
      · rcases os_regionL_appendT hi with hi | hi
        · rcases os_regionL_appendT hi with hi | hi
          · exact Or.inl (hR i hi)
          · exact Or.inl (hRW l0 le_rfl (by simp) _ i hi)
        · exact Or.inr (hD2 i hi)
      intro D3 _
      exact hKr rd R D3 hlow hLr hLk (fun i hi => by
        have := hWm (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ, show l0 + (i + 1) = l0 + 1 + i by omega] at this
        exact this) hR (fun l h1 h2 => hRW l (by omega) (by simp; omega))

end
end LeanVM.Guest.B1
