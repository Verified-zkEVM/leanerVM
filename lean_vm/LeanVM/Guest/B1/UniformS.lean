/-
  LeanVM.Guest.B1.UniformS

  `Uniform.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Uniform
public import LeanVM.Guest.Memory.RegionsB
public import LeanVM.Guest.Memory.RetempB
public import LeanVM.Guest.Memory.RestrictB
public import LeanVM.Guest.Memory.PlacedB

/-!
# `Uniform.lean` under any `BLAKE2S` semantics

Each definition and lemma of `Uniform.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {S : BlakeSem}

variable (S) in
/-- **`f` is complete at every frame pointer, uniformly in the memory.** -/
def CompleteAtS (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ ∀ rd, LowDef k rd → MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInB S coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets

variable (S) in
/-- **`f` is complete on every precondition `Pre` the caller's words `Lin` make true**, returning the
words `Pre` names and no buffer. -/
def CompleteRelS (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) : Prop :=
  ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) →
    CompleteAtS S fs cert k f Lin args (Returns rets)

/-! ## Composition -/

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem CompleteAtS.mono {k k' : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAtS S fs cert k' f Lin args Out) (hk : k' ≤ k) :
    CompleteAtS S fs cert k f Lin args Out := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, fun rd hl hm => hr rd (hl.mono hk) hm⟩

theorem kidsFromInS_dend {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs : List Call) (Dacc : ℕ → Prop) (b n : ℕ) {D D' : ℕ → Prop}, (∀ i, D' i → D i) →
      KidsFromInB S coreProgram fs cert rd σ R Dacc cs b n D →
      KidsFromInB S coreProgram fs cert rd σ R Dacc cs b n D'
  | [], _, _, _, _, _, hD, ⟨hn, h⟩ => ⟨hn, fun i hi => h i (hD i hi)⟩
  | _ :: cs, _, _, _, _, _, hD, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ =>
      ⟨m, n', Rk, Dk, hn, hR, hc, kidsFromInS_dend cs _ _ _ hD hk⟩

/-- **The callees at their running offsets**: from `b`, one total `N`, one layout and one result
per callee serve every memory holding the layouts and the words the callees read. -/
theorem kidsFromInS_of_kids' (κ : ℕ) : ∀ (ks : List Kid),
    (∀ k ∈ ks, k.taken = true → CompleteAtS S fs cert κ k.f k.Lin k.args k.Out) → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInB S coreProgram fs cert rd σ R Dacc cs b N (fun i => Dacc i ∨ outRegion ks outs i)
  | [], _, b => ⟨0, [], [], trivial, fun _ h => by simp at h, trivial, fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hrel⟩ := hok k (by simp) ht b
      obtain ⟨N, L, outs, ho, hW, hI, hK⟩ := kidsFromInS_of_kids' κ ks
        (fun k' hk' => hok k' (by simp [hk'])) (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, ⟨fun _ => hout, ho⟩, ?_,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
          simp only [Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := Main.memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨n, N, RegionL k.Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
          · rw [hct]
            simp only [ht, ↓reduceIte]
            rw [hf, ha, hr]
            exact hrel rd hlow (Main.memL_append.mpr ⟨hL1, hLk⟩)
          · refine kidsFromInS_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · obtain ⟨N, L, outs, ho, hW, hI, hK⟩ := kidsFromInS_of_kids' κ ks
        (fun k' hk' => hok k' (by simp [hk'])) (b + fs k.f)
      refine ⟨fs k.f + N, L, ([], []) :: outs, ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), ⟨fun h => absurd h ht, hI⟩, ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · have ht' : k.taken = false := by simpa using ht
          rw [hct, ht']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hf]
        · refine kidsFromInS_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL (Main.memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this

theorem kidsFromInS_of_kids (κ : ℕ) (ks : List Kid)
    (hok : ∀ k ∈ ks, k.taken = true → CompleteAtS S fs cert κ k.f k.Lin k.args k.Out) (b : ℕ) :
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInB S coreProgram fs cert rd σ R Dacc cs b N (fun i => Dacc i ∨ outRegion ks outs i) :=
  let ⟨N, L, outs, ho, hW, _, hK⟩ := kidsFromInS_of_kids' κ ks hok b
  ⟨N, L, outs, ho, hW, hK⟩

/-! ## Pure functions -/

theorem relAtInS_dmono {rd : Reader} {R D D' : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAtInB S coreProgram fs cert rd R D fp n f args rets) (hD : ∀ i, D' i → D i) :
    RelAtInB S coreProgram fs cert rd R D' fp n f args rets :=
  let ⟨t, hn, hv, hb, hp, ht, hl, hd⟩ := h
  ⟨t, hn, hv, hb, hp, ht, hl, fun i hi => hd i (hD i hi)⟩

/-- **A pure function complete on every memory holding `Lin` is `CompleteAtS`**, returning `rets`
and no buffer. -/
theorem completeAtS_of_rel_pure {Sz : List String} (hS : coreProgram.PureIn Sz) {g : String}
    (hg : g ∈ Sz) {Lin : Layout} {args rets : List E}
    (h : ∀ rd, MemL rd Lin → coreProgram.RelB S rd g args rets) (k : ℕ) :
    CompleteAtS S fs cert k g Lin args (Returns rets) := by
  intro fp
  classical
  by_cases hex : ∃ rd1, MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd _ hL => absurd ⟨rd, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, h1⟩ := hex
  set rd0 := Main.restrict rd1 (RegionL Lin)
  have h0 : MemL rd0 Lin := Main.memL_restrict h1 fun i hi => hi
  have hsupp := Main.restrict_supp' rd1 (RegionL Lin)
  obtain ⟨n, hn⟩ := relAtInB_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg
    (Memory.relInB_of_rel_supp coreProgram_wf hsupp (h rd0 h0))
  refine ⟨n, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd _ hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  refine relAtInS_dmono (hn fp rd (fun i hi => ?_) (fun A hA => ?_)) (fun i hi => ?_)
  · rw [Main.memL_agree hL' h1 i hi, Main.restrict_of ⟨i, rfl, hi⟩]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi⟩ := hsupp _ _ hv
    rw [Main.memL_agree hL' h1 i hi, ← Main.restrict_of (rd := rd1) (S := RegionL Lin) ⟨i, rfl, hi⟩, hv]
    rfl
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

/-! ## A function's own buffers -/

/-- **A function calling nothing is complete** when, at every frame pointer and on every memory
holding its buffers' honest words `own fp` and the caller's words, a valuation walks its body with
no call and no `frameAddr`, its `HeapBuf` hints of the sizes `sizes` from `fp + fs f`, loading from
its buffers or `Lin`. -/
theorem completeAtS_leaf {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (k : ℕ) (Lin : Layout) (args rets : List E) (sizes : List ℕ)
    (own : ℕ → List (List E)) (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hσ : ∀ fp rd, LowDef k rd → MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.HoldsB S rd σ) ∧
        calls es = [] ∧ addrs es = [] ∧ allocs σ es = sizes ∧
        (allocDsts es).map σ = (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
          (RegionL (bufL (fp + fs f) sizes (own fp)) i ∨ RegionL Lin i)) :
    CompleteAtS S fs cert k f Lin args (Returns rets) := by
  intro fp
  refine ⟨fs f + sizes.sum, bufL (fp + fs f) sizes (own fp), rets, [], ⟨rfl, rfl⟩,
    by simpa using (bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), fun rd hlow hL => ?_⟩
  simp only [List.nil_append] at hL
  obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
  obtain ⟨σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload⟩ := hσ fp rd hlow hL1 hL2
  have h := relAtInB_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw
    hr hes (by rw [hal]; exact hbuf) (by rw [ha]; simp) (by rw [hc]; exact ⟨rfl, fun _ h => h⟩) (fun A hA => ?_)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [hal] at h; simpa using h
  · obtain ⟨i, hi, h | h⟩ := hload A hA
    · exact ⟨i, hi, Or.inl (Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i h))⟩
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩

/-! ## Callees in batches -/

theorem kidsFromInS_dacc {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs : List Call) (Dacc Dacc' : ℕ → Prop) (b n : ℕ) (D : ℕ → Prop), (∀ i, Dacc i → Dacc' i) →
      KidsFromInB S coreProgram fs cert rd σ R Dacc cs b n D →
      KidsFromInB S coreProgram fs cert rd σ R Dacc' cs b n D
  | [], _, _, _, _, _, h, ⟨hn, hD⟩ => ⟨hn, fun i hi => h i (hD i hi)⟩
  | _ :: cs, _, _, _, _, _, h, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ =>
      ⟨m, n', Rk, Dk, hn, fun i hi => (hR i hi).imp_right (h i), hc,
        kidsFromInS_dacc cs _ _ _ _ _ (fun i hi => hi.imp_left (h i)) hk⟩

/-- **Two batches of callees in sequence**: the second from any data that contains the first's
claims. -/
theorem kidsFromInS_append {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs1 cs2 : List Call) (Dacc : ℕ → Prop) (b n1 n2 : ℕ) (D1 D : ℕ → Prop),
      KidsFromInB S coreProgram fs cert rd σ R Dacc cs1 b n1 D1 →
      (∀ Dacc' : ℕ → Prop, (∀ i, D1 i → Dacc' i) →
        KidsFromInB S coreProgram fs cert rd σ R Dacc' cs2 (b + n1) n2 D) →
      KidsFromInB S coreProgram fs cert rd σ R Dacc (cs1 ++ cs2) b (n1 + n2) D
  | [], cs2, Dacc, b, n1, n2, D1, D, ⟨hn, hD⟩, h2 => by
    subst hn; simpa using h2 Dacc hD
  | _ :: cs1, cs2, Dacc, b, n1, n2, D1, D, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩, h2 =>
    ⟨m, n' + n2, Rk, Dk, by omega, hR, hc,
      kidsFromInS_append cs1 cs2 _ (b + m) n' n2 D1 D hk fun Dacc' h => by
        rw [show b + m + n' = b + n1 by omega]; exact h2 Dacc' h⟩

/-! ## Completeness with disjoint layouts

`CompleteAtD` is `CompleteAt` with its layouts pairwise disjoint (`DisjL`), so that a memory
holding them exists; bump allocation gives it everywhere. The generic lemmas in the `D` form:
`kidsFromIn_of_kidsD`, `completeAt_leafD`, `completeAt_of_rel_pureD`. -/

variable (S) in
/-- **`f` is complete at every frame pointer, uniformly in the memory, on disjoint layouts.** -/
def CompleteAtDS (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInB S coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets

variable (S) in
/-- `CompleteRelS` on disjoint layouts. -/
def CompleteRelDS (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) : Prop :=
  ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) →
    CompleteAtDS S fs cert k f Lin args (Returns rets)

theorem CompleteAtDS.toCompleteAt {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAtDS S fs cert k f Lin args Out) :
    CompleteAtS S fs cert k f Lin args Out := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, _, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hr⟩

theorem CompleteRelDS.toCompleteRel {k : ℕ} {f : String} {Pre : Reader → List E → List E → Prop}
    (h : CompleteRelDS S fs cert k f Pre) : CompleteRelS S fs cert k f Pre :=
  fun args rets Lin hp => (h args rets Lin hp).toCompleteAt

theorem CompleteAtDS.mono {k k' : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAtDS S fs cert k' f Lin args Out) (hk : k' ≤ k) :
    CompleteAtDS S fs cert k f Lin args Out := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm => hr rd (hl.mono hk) hm⟩

theorem kidsFromInS_of_kidsD (κ : ℕ) : ∀ (ks : List Kid),
    (∀ k ∈ ks, k.taken = true → CompleteAtDS S fs cert κ k.f k.Lin k.args k.Out) → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      DisjL L ∧ OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInB S coreProgram fs cert rd σ R Dacc cs b N (fun i => Dacc i ∨ outRegion ks outs i)
  | [], _, b => ⟨0, [], [], trivial, fun _ h => by simp at h, disj_nil, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hd, hrel⟩ := hok k (by simp) ht b
      obtain ⟨N, L, outs, ho, hW, hD, hI, hK⟩ := kidsFromInS_of_kidsD κ ks
        (fun k' hk' => hok k' (by simp [hk'])) (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, ⟨fun _ => hout, ho⟩, ?_,
        disj_append hd hD hw hW le_rfl,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
          simp only [Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := Main.memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨n, N, RegionL k.Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
          · rw [hct]
            simp only [ht, ↓reduceIte]
            rw [hf, ha, hr]
            exact hrel rd hlow (Main.memL_append.mpr ⟨hL1, hLk⟩)
          · refine kidsFromInS_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · obtain ⟨N, L, outs, ho, hW, hD, hI, hK⟩ := kidsFromInS_of_kidsD κ ks
        (fun k' hk' => hok k' (by simp [hk'])) (b + fs k.f)
      refine ⟨fs k.f + N, L, ([], []) :: outs, ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩, ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · have ht' : k.taken = false := by simpa using ht
          rw [hct, ht']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hf]
        · refine kidsFromInS_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL (Main.memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this

/-- `completeAtS_of_rel_pure`, on disjoint layouts (no buffer). -/
theorem completeAtS_of_rel_pureD {Sz : List String} (hS : coreProgram.PureIn Sz) {g : String}
    (hg : g ∈ Sz) {Lin : Layout} {args rets : List E}
    (h : ∀ rd, MemL rd Lin → coreProgram.RelB S rd g args rets) (k : ℕ) :
    CompleteAtDS S fs cert k g Lin args (Returns rets) := by
  intro fp
  classical
  by_cases hex : ∃ rd1, MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd _ hL => absurd ⟨rd, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, h1⟩ := hex
  set rd0 := Main.restrict rd1 (RegionL Lin)
  have h0 : MemL rd0 Lin := Main.memL_restrict h1 fun i hi => hi
  have hsupp := Main.restrict_supp' rd1 (RegionL Lin)
  obtain ⟨n, hn⟩ := relAtInB_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg
    (Memory.relInB_of_rel_supp coreProgram_wf hsupp (h rd0 h0))
  refine ⟨n, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd _ hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  refine relAtInS_dmono (hn fp rd (fun i hi => ?_) (fun A hA => ?_)) (fun i hi => ?_)
  · rw [Main.memL_agree hL' h1 i hi, Main.restrict_of ⟨i, rfl, hi⟩]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi⟩ := hsupp _ _ hv
    rw [Main.memL_agree hL' h1 i hi, ← Main.restrict_of (rd := rd1) (S := RegionL Lin) ⟨i, rfl, hi⟩, hv]
    rfl
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

/-- `completeAtS_leaf`, on disjoint layouts (the function's own buffers). -/
theorem completeAtS_leafD {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (k : ℕ) (Lin : Layout) (args rets : List E) (sizes : List ℕ)
    (own : ℕ → List (List E)) (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hσ : ∀ fp rd, LowDef k rd → MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.HoldsB S rd σ) ∧
        calls es = [] ∧ addrs es = [] ∧ allocs σ es = sizes ∧
        (allocDsts es).map σ = (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
          (RegionL (bufL (fp + fs f) sizes (own fp)) i ∨ RegionL Lin i)) :
    CompleteAtDS S fs cert k f Lin args (Returns rets) := by
  intro fp
  refine ⟨fs f + sizes.sum, bufL (fp + fs f) sizes (own fp), rets, [], ⟨rfl, rfl⟩,
    by simpa using (bufL_within _ _ _ (hown fp)).mono (by omega) (by omega),
    by simpa using bufL_disj _ _ _ (hown fp), fun rd hlow hL => ?_⟩
  simp only [List.nil_append] at hL
  obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
  obtain ⟨σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload⟩ := hσ fp rd hlow hL1 hL2
  have h := relAtInB_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw
    hr hes (by rw [hal]; exact hbuf) (by rw [ha]; simp) (by rw [hc]; exact ⟨rfl, fun _ h => h⟩) (fun A hA => ?_)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [hal] at h; simpa using h
  · obtain ⟨i, hi, h | h⟩ := hload A hA
    · exact ⟨i, hi, Or.inl (Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i h))⟩
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩

/-! ## Completeness with bounded trees

`CompleteAtB … B` is `CompleteAtD` with the tree's size at most `B`, so that a caller's size is
bounded by its callees' bounds: `kidsFromIn_of_kidsB`, `completeAt_leafB`,
`completeAt_of_rel_pureB`. -/

variable (S) in
/-- **`f` is complete at every frame pointer, on disjoint layouts, by a tree of at most `B`
words.** -/
def CompleteAtBS (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (B : ℕ) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ n ≤ B ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInB S coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets

variable (S) in
/-- `CompleteRelDS` by trees of at most `B` words. -/
def CompleteRelBS (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) (B : ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) →
    CompleteAtBS S fs cert k f Lin args (Returns rets) B

theorem CompleteAtBS.toCompleteAtD {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} (h : CompleteAtBS S fs cert k f Lin args Out B) :
    CompleteAtDS S fs cert k f Lin args Out := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, _, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩

theorem CompleteRelBS.toCompleteRelD {k : ℕ} {f : String} {Pre : Reader → List E → List E → Prop}
    {B : ℕ} (h : CompleteRelBS S fs cert k f Pre B) : CompleteRelDS S fs cert k f Pre :=
  fun args rets Lin hp => (h args rets Lin hp).toCompleteAtD

theorem CompleteAtBS.mono {k k' : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B B' : ℕ} (h : CompleteAtBS S fs cert k' f Lin args Out B)
    (hk : k' ≤ k) (hB : B ≤ B') : CompleteAtBS S fs cert k f Lin args Out B' := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, le_trans hn hB, fun rd hl hm => hr rd (hl.mono hk) hm⟩

theorem kidsFromInS_of_kidsB (κ : ℕ) (bd : Kid → ℕ) : ∀ (ks : List Kid),
    (∀ k ∈ ks, k.taken = true → CompleteAtBS S fs cert κ k.f k.Lin k.args k.Out (bd k)) → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      DisjL L ∧ N ≤ kidsBound fs bd ks ∧ OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInB S coreProgram fs cert rd σ R Dacc cs b N (fun i => Dacc i ∨ outRegion ks outs i)
  | [], _, b => ⟨0, [], [], trivial, fun _ h => by simp at h, disj_nil, le_rfl, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hd, hnb, hrel⟩ := hok k (by simp) ht b
      obtain ⟨N, L, outs, ho, hW, hD, hNb, hI, hK⟩ := kidsFromInS_of_kidsB κ bd ks
        (fun k' hk' => hok k' (by simp [hk'])) (b + n)
      have hB1 : n + N ≤ kidsBound fs bd (k :: ks) := by
        simp only [kidsBound, List.map_cons, List.sum_cons, ht, ↓reduceIte] at hNb ⊢; omega
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, ⟨fun _ => hout, ho⟩, ?_,
        disj_append hd hD hw hW le_rfl, hB1,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
          simp only [Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := Main.memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨n, N, RegionL k.Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
          · rw [hct]
            simp only [ht, ↓reduceIte]
            rw [hf, ha, hr]
            exact hrel rd hlow (Main.memL_append.mpr ⟨hL1, hLk⟩)
          · refine kidsFromInS_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · obtain ⟨N, L, outs, ho, hW, hD, hNb, hI, hK⟩ := kidsFromInS_of_kidsB κ bd ks
        (fun k' hk' => hok k' (by simp [hk'])) (b + fs k.f)
      have hB1 : fs k.f + N ≤ kidsBound fs bd (k :: ks) := by
        simp only [kidsBound, List.map_cons, List.sum_cons, ht, Bool.false_eq_true, ↓reduceIte]
          at hNb ⊢
        omega
      refine ⟨fs k.f + N, L, ([], []) :: outs, ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, hB1, ⟨fun h => absurd h ht, hI⟩, ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · have ht' : k.taken = false := by simpa using ht
          rw [hct, ht']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hf]
        · refine kidsFromInS_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL (Main.memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this

/-- `completeAtS_of_rel_pure` by a bounded tree: the bound on the valid trees of `g` at the call's
arguments. -/
theorem completeAtS_of_rel_pureBat {Sz : List String} (hS : coreProgram.PureIn Sz) {g : String}
    (hg : g ∈ Sz) {Lin : Layout} {args rets : List E}
    (h : ∀ rd, MemL rd Lin → coreProgram.RelB S rd g args rets) (k : ℕ) {B : ℕ}
    (hB : ∀ rd (t : Tree), t.name = g → t.ValidB S coreProgram rd args rets →
      t.BufsOk coreProgram → t.total fs ≤ B) :
    CompleteAtBS S fs cert k g Lin args (Returns rets) B := by
  intro fp
  classical
  by_cases hex : ∃ rd1, MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd _ hL => absurd ⟨rd, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, h1⟩ := hex
  set rd0 := Main.restrict rd1 (RegionL Lin)
  have h0 : MemL rd0 Lin := Main.memL_restrict h1 fun i hi => hi
  have hsupp := Main.restrict_supp' rd1 (RegionL Lin)
  obtain ⟨n, hn⟩ := relAtInB_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg
    (Memory.relInB_of_rel_supp coreProgram_wf hsupp (h rd0 h0))
  have hnB : n ≤ B := by
    obtain ⟨t, hname, hv, hbo, -, ht, -⟩ := hn fp rd0 (fun _ _ => rfl) (fun _ h => h)
    rw [← ht]; exact hB rd0 t hname hv hbo
  refine ⟨n, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, hnB, fun rd _ hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  refine relAtInS_dmono (hn fp rd (fun i hi => ?_) (fun A hA => ?_)) (fun i hi => ?_)
  · rw [Main.memL_agree hL' h1 i hi, Main.restrict_of ⟨i, rfl, hi⟩]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi⟩ := hsupp _ _ hv
    rw [Main.memL_agree hL' h1 i hi, ← Main.restrict_of (rd := rd1) (S := RegionL Lin) ⟨i, rfl, hi⟩, hv]
    rfl
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

/-- `completeAtS_of_rel_pure` by a bounded tree: the bound on every valid tree of `g`. -/
theorem completeAtS_of_rel_pureB {Sz : List String} (hS : coreProgram.PureIn Sz) {g : String}
    (hg : g ∈ Sz) {Lin : Layout} {args rets : List E}
    (h : ∀ rd, MemL rd Lin → coreProgram.RelB S rd g args rets) (k : ℕ) {B : List E → ℕ}
    (hB : ∀ rd (t : Tree) args rets, t.name = g → t.ValidB S coreProgram rd args rets →
      t.BufsOk coreProgram → t.total fs ≤ B args) :
    CompleteAtBS S fs cert k g Lin args (Returns rets) (B args) :=
  completeAtS_of_rel_pureBat hS hg h k fun rd t hn hv hb => hB rd t args rets hn hv hb

/-- `completeAtS_leaf` by a tree of its frame and buffers. -/
theorem completeAtS_leafB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (k : ℕ) (Lin : Layout) (args rets : List E) (sizes : List ℕ)
    (own : ℕ → List (List E)) (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hσ : ∀ fp rd, LowDef k rd → MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.HoldsB S rd σ) ∧
        calls es = [] ∧ addrs es = [] ∧ allocs σ es = sizes ∧
        (allocDsts es).map σ = (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
          (RegionL (bufL (fp + fs f) sizes (own fp)) i ∨ RegionL Lin i)) :
    CompleteAtBS S fs cert k f Lin args (Returns rets) (fs f + sizes.sum) := by
  intro fp
  refine ⟨fs f + sizes.sum, bufL (fp + fs f) sizes (own fp), rets, [], ⟨rfl, rfl⟩,
    by simpa using (bufL_within _ _ _ (hown fp)).mono (by omega) (by omega),
    by simpa using bufL_disj _ _ _ (hown fp), le_rfl, fun rd hlow hL => ?_⟩
  simp only [List.nil_append] at hL
  obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
  obtain ⟨σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload⟩ := hσ fp rd hlow hL1 hL2
  have h := relAtInB_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw
    hr hes (by rw [hal]; exact hbuf) (by rw [ha]; simp) (by rw [hc]; exact ⟨rfl, fun _ h => h⟩) (fun A hA => ?_)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [hal] at h; simpa using h
  · obtain ⟨i, hi, h | h⟩ := hload A hA
    · exact ⟨i, hi, Or.inl (Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i h))⟩
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩

end
end LeanVM.Guest.B1
