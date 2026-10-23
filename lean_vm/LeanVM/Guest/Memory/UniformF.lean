/-
  LeanVM.Guest.Memory.UniformF

  The uniform placed completeness with the caller's words depending on the frame pointer
  (`CompleteAtF`), and its composition along a caller's calls (`kidsFromIn_of_kidsF`).
-/

module

public import LeanVM.Guest.Memory.Uniform

/-!
# Caller's words at the frame pointer

`CompleteAtD` fixes the caller's words `Lin` and quantifies over the frame pointer. A callee that
stores pointers into its own frame in its caller's memory (`keccak_layer` writes the addresses of
its buffers into its caller's record) reads caller's words that depend on where it is placed:
`CompleteAtF … Lin`, with `Lin : ℕ → Layout` read at the frame pointer. `CompleteAtD` is the
constant case (`CompleteAtD.toF`).

`kidsFromIn_of_kidsF` composes such callees along a caller's calls as `kidsFromIn_of_kidsD`
does, and returns the callees' frame pointers `fps`, chosen before the memory, so the caller can
build its own words (the record) from them: the callees are `KidF.atAll ks fps`, each `KidF`
read at its frame pointer (`KidF.at`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **`f` is complete at every frame pointer `fp`, on disjoint layouts, reading the caller's words
`Lin fp`.** -/
def CompleteAtF (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Lin : ℕ → Layout) (args : List E) (Out : List E → Layout → Prop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin fp) →
      RelAtIn coreProgram fs cert rd (RegionL (Lin fp)) (RegionL Lout) fp n f args rets

/-- A call whose caller's words depend on the callee's frame pointer. -/
structure KidF where
  f : String
  taken : Bool
  args : List E
  Lin : ℕ → Layout
  Out : List E → Layout → Prop

/-- The call placed at `p`. -/
def KidF.at (k : KidF) (p : ℕ) : Kid := ⟨k.f, k.taken, k.args, k.Lin p, k.Out⟩

/-- The calls placed at `fps`. -/
def KidF.atAll (ks : List KidF) (fps : List ℕ) : List Kid := List.zipWith KidF.at ks fps

/-- A call with fixed caller's words. -/
def Kid.toF (k : Kid) : KidF := ⟨k.f, k.taken, k.args, fun _ => k.Lin, k.Out⟩

theorem Kid.toF_at (k : Kid) (p : ℕ) : k.toF.at p = k := rfl

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem CompleteAtD.toF {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAtD fs cert k f Lin args Out) :
    CompleteAtF fs cert k f (fun _ => Lin) args Out := h

theorem CompleteAtF.mono {k k' : ℕ} {f : String} {Lin : ℕ → Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAtF fs cert k' f Lin args Out) (hk : k' ≤ k) :
    CompleteAtF fs cert k f Lin args Out := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm => hr rd (hl.mono hk) hm⟩

/-- **The callees at their running offsets, their caller's words at their frame pointers**: from
`b`, one total `N`, one layout, one result and one frame pointer per callee serve every memory
holding the layouts and the words the callees read where they are placed. -/
theorem kidsFromIn_of_kidsF (κ : ℕ) : ∀ (ks : List KidF),
    (∀ k ∈ ks, k.taken = true → CompleteAtF fs cert κ k.f k.Lin k.args k.Out) → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)) (fps : List ℕ),
      fps.length = ks.length ∧ (∀ p ∈ fps, b ≤ p) ∧
      OutsOk (KidF.atAll ks fps) outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn (KidF.atAll ks fps) outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop),
        CallsMatch σ cs (KidF.atAll ks fps) outs → LowDef κ rd → MemL rd L →
        MemL rd (Kid.lins (KidF.atAll ks fps)) → RegionsOk R Dacc (KidF.atAll ks fps) outs →
        KidsFromIn coreProgram fs cert rd σ R Dacc cs b N
          (fun i => Dacc i ∨ outRegion (KidF.atAll ks fps) outs i)
  | [], _, b => ⟨0, [], [], [], rfl, fun _ h => by simp at h, trivial, fun _ h => by simp at h,
      disj_nil, trivial, fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hd, hrel⟩ := hok k (by simp) ht b
      obtain ⟨N, L, outs, fps, hlen, hge, ho, hW, hD, hI, hK⟩ := kidsFromIn_of_kidsF κ ks
        (fun k' hk' => hok k' (by simp [hk'])) (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, b :: fps, by simp [hlen],
        fun p hp => ?_, ⟨fun _ => hout, ho⟩, ?_, disj_append hd hD hw hW le_rfl,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact le_rfl
        · have := hge p hp; omega
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
          simp only [KidF.atAll, List.zipWith_cons_cons, Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := Main.memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨n, N, RegionL (k.Lin b), RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
          · rw [hct]
            simp only [KidF.at, ht, ↓reduceIte]
            rw [hf, ha, hr]
            exact hrel rd hlow (Main.memL_append.mpr ⟨hL1, hLk⟩)
          · refine kidsFromIn_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct, KidF.atAll] using hR2
    · obtain ⟨N, L, outs, fps, hlen, hge, ho, hW, hD, hI, hK⟩ := kidsFromIn_of_kidsF κ ks
        (fun k' hk' => hok k' (by simp [hk'])) (b + fs k.f)
      refine ⟨fs k.f + N, L, ([], []) :: outs, b :: fps, by simp [hlen], fun p hp => ?_,
        ⟨fun h => absurd h ht, ho⟩, hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩,
        ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact le_rfl
        · have := hge p hp; omega
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [KidF.atAll, List.zipWith_cons_cons, Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · have ht' : k.taken = false := by simpa using ht
          rw [hct]
          simp only [KidF.at, ht', Bool.false_eq_true, ↓reduceIte]
          rw [hf]
          rfl
        · refine kidsFromIn_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL (Main.memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [KidF.atAll, KidF.at, hct, ht, Bool.false_eq_true, false_and, or_false]
              at this ⊢
            exact this

end
end LeanVM.Guest.B1
