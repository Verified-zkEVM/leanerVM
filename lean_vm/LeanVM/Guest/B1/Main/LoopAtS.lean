/-
  LeanVM.Guest.B1.Main.LoopAtS

  `LoopAt.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Main.LoopAt
public import LeanVM.Guest.B1.UniformS
public import LeanVM.Guest.B1.Tables.VtCSizeS

/-!
# `LoopAt.lean` under any `BLAKE2S` semantics

Each definition and lemma of `LoopAt.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtB Returns Kid CallsMatch OutsOk RegionsOk outRegion
  kidsFromIn_of_kidsB kidsBound relAtIn_dmono within_append
  vtc_loop_total vtc_atom)

@[expose] public section

variable {S : BlakeSem}

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## Bounds -/

variable (S) in
/-- **The least bound** a callee is complete by. -/
noncomputable def kidInfS (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (k : Kid) : ℕ :=
  sInf {B | CompleteAtBS S fs cert κ k.f k.Lin k.args k.Out B}

theorem kidInfS_le {κ : ℕ} {k : Kid} {B : ℕ} (h : CompleteAtBS S fs cert κ k.f k.Lin k.args k.Out B) :
    kidInfS S fs cert κ k ≤ B :=
  Nat.sInf_le h

theorem kidInfS_le' {κ : ℕ} {f : String} {tk : Bool} {args : List E} {Lin : Layout}
    {Out : List E → Layout → Prop} {B : ℕ} (h : CompleteAtBS S fs cert κ f Lin args Out B) :
    kidInfS S fs cert κ ⟨f, tk, args, Lin, Out⟩ ≤ B :=
  Nat.sInf_le h

theorem completeAtBS_kidInf {κ : ℕ} {k : Kid} {B : ℕ}
    (h : CompleteAtBS S fs cert κ k.f k.Lin k.args k.Out B) :
    CompleteAtBS S fs cert κ k.f k.Lin k.args k.Out (kidInfS S fs cert κ k) :=
  Nat.sInf_mem (s := {B | CompleteAtBS S fs cert κ k.f k.Lin k.args k.Out B}) ⟨B, h⟩

variable (S) in
/-- **Callees within bounds**: each entered one complete by a tree within its bound, each one not
entered its frame within it. -/
def KidsBS (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (ks : List Kid) (bs : List ℕ) : Prop :=
  List.Forall₂ (fun k b => (k.taken = true → CompleteAtBS S fs cert κ k.f k.Lin k.args k.Out b) ∧
    (k.taken = false → fs k.f ≤ b)) ks bs

theorem KidsBS.complete {κ : ℕ} {ks : List Kid} {bs : List ℕ} (h : KidsBS S fs cert κ ks bs) :
    ∀ k ∈ ks, k.taken = true → CompleteAtBS S fs cert κ k.f k.Lin k.args k.Out (kidInfS S fs cert κ k) := by
  induction h with
  | nil => intro k hk; simp at hk
  | cons hkb _ ih =>
    intro k hk ht
    rcases List.mem_cons.mp hk with rfl | hk
    · exact completeAtBS_kidInf (hkb.1 ht)
    · exact ih k hk ht

theorem KidsBS.bound {κ : ℕ} {ks : List Kid} {bs : List ℕ} (h : KidsBS S fs cert κ ks bs) :
    kidsBound fs (kidInfS S fs cert κ) ks ≤ bs.sum := by
  induction h with
  | nil => simp [kidsBound]
  | @cons k b ks bs hkb _ ih =>
    simp only [kidsBound, List.map_cons, List.sum_cons] at ih ⊢
    cases ht : k.taken
    · simp only [Bool.false_eq_true, ↓reduceIte]; have := hkb.2 ht; omega
    · simp only [↓reduceIte]; have := kidInfS_le (hkb.1 ht); omega

theorem KidsBS.append {κ : ℕ} {ks ks' : List Kid} {bs bs' : List ℕ} (h : KidsBS S fs cert κ ks bs)
    (h' : KidsBS S fs cert κ ks' bs') : KidsBS S fs cert κ (ks ++ ks') (bs ++ bs') :=
  List.rel_append h h'

/-- **A `mul_range` loop helper with no callee and no `HeapBuf`**: its valid trees over `m`
iterations are within its `m + 1` frames. -/
theorem leafLoopS_total {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre : List Stmt} {ps : List V} {a b c d e : V}
    (hb : fn.body = pre ++ [.callIf c f (e :: .n 1 :: ps), .ret []])
    (hp : fn.params = .n 0 :: .n 1 :: ps)
    (hst : pre.all Stmt.straight = true) (hna : pre.filterMap Stmt.allocSz = [])
    (hcs : pre.filterMap Stmt.callS = [])
    (ha : Core.Stmt.atom (.const a (word 2 0 0)) ∈ pre) (hb1 : Core.Stmt.atom (.mul b (.n 0) a) ∈ pre)
    (hc : Core.Stmt.atom (.add c b (.n 1)) ∈ pre) (hd : Core.Stmt.atom (.const d (word 2 0 0)) ∈ pre)
    (he : Core.Stmt.atom (.mul e (.n 0) d) ∈ pre)
    {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = f) (hv : t.ValidB S coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * fs f + fs f := by
  have key := vtcS_loop_total (S := S) (fs := fs) hf hb hst hna rd m rest 0 ?_ m 0 t rets (by omega) hm hn
    (by rwa [pow_zero]) hbo
  · simpa using key
  intro σ j _ hpσ hes
  rw [hp] at hpσ
  simp only [List.map_cons, List.cons.injEq] at hpσ
  obtain ⟨h0, h1, hr⟩ := hpσ
  have xa := vtcS_atom hes ha
  have xb := vtcS_atom hes hb1
  have xc := vtcS_atom hes hc
  have xd := vtcS_atom hes hd
  have xe := vtcS_atom hes he
  simp only [Atom.HoldsB, word_gen] at xa xb xc xd xe
  refine ⟨by rw [xc, xb, xa, h0, h1], by simp [xe, xd, h0, h1, hr], fun kids hk _ => ?_⟩
  rw [hcs] at hk
  match kids, hk with
  | [], _ => simp [Tree.totalKids]

/-! ## The iterations -/

/-- **A loop helper is complete from its iterations**: iteration `j < m`, its tail of size `mt`
right after its frame (a `RelAtInB` when `j + 1 < m`, the frame of the call not taken otherwise),
is complete at every `fp` with one size, at most `bs j`, and one layout of its own words from
`fp + fs f + mt`. -/
theorem completeAtS_loop {f : String} (κ : ℕ) (Lin : Layout) (A : ℕ → List E) (m : ℕ)
    (bs : ℕ → ℕ)
    (step : ∀ j < m, ∀ fp mt : ℕ, ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧
      n ≤ bs j ∧ ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) →
        (j + 1 < m → RelAtInB S coreProgram fs cert rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          (A (j + 1)) []) →
        (j + 1 = m → mt = fs f) →
        RelAtInB S coreProgram fs cert rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f
          (A j) []) :
    ∀ j < m, CompleteAtBS S fs cert κ f Lin (A j) (Returns []) (loopSum (fs f) bs j (m - j)) := by
  have key : ∀ t j, j + t + 1 = m →
      CompleteAtBS S fs cert κ f Lin (A j) (Returns []) (loopSum (fs f) bs j (t + 1)) := by
    intro t
    induction t with
    | zero =>
      intro j hj fp
      obtain ⟨n, L, hW, hD, hn, hS⟩ := step j (by omega) fp (fs f)
      refine ⟨fs f + fs f + n, L, [], [], ⟨rfl, rfl⟩, ?_, by simpa using hD,
        by simp only [loopSum]; omega, fun rd hl hL => ?_⟩
      · simpa using hW.mono (by omega) (by omega)
      · refine relAtInS_dmono (hS rd hl (by simpa using hL) (fun h => by omega) (fun _ => rfl))
          fun i hi => ?_
        obtain ⟨q, hq, _⟩ := hi; simp at hq
    | succ t ih =>
      intro j hj fp
      obtain ⟨nt, Lt, rt, Lo, ⟨rfl, rfl⟩, hWt, hDt, hnt, hSt⟩ := ih (j + 1) (by omega) (fp + fs f)
      obtain ⟨n, L, hW, hD, hn, hS⟩ := step j (by omega) fp nt
      simp only [List.nil_append] at hWt hDt
      refine ⟨fs f + nt + n, Lt ++ L, [], [], ⟨rfl, rfl⟩, ?_, by simpa using disj_append hDt hD hWt hW le_rfl,
        by rw [loopSum]; omega, fun rd hl hL => ?_⟩
      · simp only [List.nil_append]
        rw [within_append]
        exact ⟨hWt.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
      · simp only [List.nil_append, List.append_assoc] at hL
        obtain ⟨hL1, hL2⟩ := memL_append.mp hL
        refine relAtInS_dmono (hS rd hl hL2 (fun _ => ?_) (fun h => by omega)) fun i hi => ?_
        · refine relAtInS_dmono (hSt rd hl (by simpa using memL_append.mpr ⟨hL1, (memL_append.mp hL2).2⟩))
            fun i hi => ?_
          exact hi.elim
        · obtain ⟨q, hq, _⟩ := hi; simp at hq
  intro j hj
  have := key (m - 1 - j) j (by omega)
  rwa [show m - 1 - j + 1 = m - j by omega] at this

/-! ## A straight-line iteration -/

/-- **A straight-line loop iteration, placed**: the body `pre ++ [ret []]` places nothing, its
callees before the tail are the `Kid`s `ks` (each `CompleteAtBS` by `bd`, reading within `Lin`),
and on every memory holding their words and `Lin`, for their results, a valuation satisfies the
body with the frames matching the kids and loads reading `Lin`. -/
theorem loopStepS_straight {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) {pre : List Stmt} (hb : fn.body = pre ++ [.ret []])
    (hs : pre.all Stmt.straight = true) (hal : pre.filterMap Stmt.allocSz = [])
    (had : pre.filterMap Stmt.addrS = []) (κ : ℕ) (Lin : Layout) (args : List E)
    (fronts : List (Option V × String × List V × List V)) (tc : V) (targs : List V)
    (hcs : pre.filterMap Stmt.callS = fronts ++ [(some tc, f, targs, [])])
    (ks : List Kid) (bd : Kid → ℕ)
    (hks : ∀ k ∈ ks, k.taken = true → CompleteAtBS S fs cert κ k.f k.Lin k.args k.Out (bd k))
    (hsub : ∀ k ∈ ks, ∀ q ∈ k.Lin, q ∈ Lin)
    (targs' : List E) (more : Bool) (fp mt : ℕ)
    (hσ : ∀ rd, LowDef κ rd → MemL rd Lin → ∀ outs, OutsOk ks outs → ∃ σ : Val,
      fn.params.map σ = args ∧
      Stmt.HoldsListB S (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = []) ∧
      CallsMatch σ (fronts.map (mkCall σ)) ks outs ∧ decide (σ tc ≠ 0) = more ∧
      targs.map σ = targs' ∧
      ∀ q ∈ pre.filterMap LeanVM.Guest.B1.Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧ RegionL Lin i) :
    ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧ n ≤ kidsBound fs bd ks ∧
      ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) →
        (more = true → RelAtInB S coreProgram fs cert rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          targs' []) →
        (more = false → mt = fs f) →
        RelAtInB S coreProgram fs cert rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f args [] := by
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromInS_of_kidsB (S := S) (fs := fs) (cert := cert) κ bd ks hks
    (fp + fs f + mt + 0)
  refine ⟨N, L, by simpa using hW, hD, hNb, fun rd hlow hL htail hnot => ?_⟩
  obtain ⟨hL1, hL2⟩ := memL_append.mp hL
  obtain ⟨σ, hp, hH, hcm, htk, hta, hld⟩ := hσ rd hlow hL2 outs ho
  have hwf : Stmt.wfList coreProgram fn.body = true :=
    coreProgram_wf fn (List.mem_of_find?_eq_some hf)
  have hw := walk_straight σ [] pre hs
  rw [← hb] at hw
  have hsat := walkB_sat fn.body hwf hH
  rw [hw] at hsat
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ pre hs
  rw [hal] at e1 e2
  rw [had] at e3
  rw [hcs, List.map_append] at e4
  have hld' := LeanVM.Guest.B1.loadAddrs_straight σ pre hs
  have hc : (mkCall σ (some tc, f, targs, [])).taken = more := htk
  have hsumz : (allocs σ (pre.flatMap (Main.slEvs σ))).sum = 0 := by rw [e2]; rfl
  have := relAtInB_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := fun _ => False) (Dk := fun i => False ∨ outRegion ks outs i) (Rt := RegionL Lin)
    (Dt := fun _ => False) (fp := fp) (m := mt) (N := N) (σ := σ) (rd := rd) coreProgram_wf hf hl hp hw rfl
    (fun e he => (hsat.1 e he).1) e4 ?_ (by rw [e1, e2]; rfl) (by rw [e3]; simp) ?_
    (fun i hi => Or.inl hi) ?_ (fun i hi => hi.elim)
  · rwa [hsumz, Nat.add_zero] at this
  · cases more with
    | true =>
      simp only [hc, ↓reduceIte]
      simp only [mkCall, List.map_nil]
      rw [hta]
      exact htail rfl
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact hnot rfl
  · rw [hsumz]
    have hK' := hK rd σ _ (fun i => RegionL Lin i ∨ ownData cert fp (fp + fs f + mt) f
      (allocs σ (pre.flatMap (Main.slEvs σ))) (pre.flatMap (Main.slEvs σ)) i) (fun _ => False) hcm hlow
      hL1 (memL_mono (fun q hq => by
        obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hq
        exact hsub k hk q hq) hL2)
      (regionsOk_of_sub _ _ _ fun k hk i hi => Or.inl (regionL_mono (hsub k hk) hi))
    exact hK'
  · intro A hA
    rw [hld', List.mem_map] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    obtain ⟨i, hi, hr⟩ := hld q hq
    exact ⟨i, hi, Or.inr (Or.inl hr)⟩

/-- **A straight-line loop iteration with its own buffers, placed**: as `loopStepS_straight`, the
body's `HeapBuf`s of sizes `sizes` from `fp + fs f + mt`, holding `bufs`, and its callees reading
within `Lin` and those buffers. -/
theorem loopStepS_bufs {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) {pre : List Stmt} (hb : fn.body = pre ++ [.ret []])
    (hs : pre.all Stmt.straight = true) (AL : List (V × (ℕ ⊕ V))) (hal : pre.filterMap Stmt.allocSz = AL)
    (had : pre.filterMap Stmt.addrS = []) (κ : ℕ) (Lin : Layout) (args : List E)
    (fronts : List (Option V × String × List V × List V)) (tc : V) (targs : List V)
    (hcs : pre.filterMap Stmt.callS = fronts ++ [(some tc, f, targs, [])])
    (sizes : List ℕ) (bufs : List (List E)) (hbl : List.Forall₂ (fun c s => c.length ≤ s) bufs sizes)
    (fp mt : ℕ) (ks : List Kid) (bd : Kid → ℕ)
    (hks : ∀ k ∈ ks, k.taken = true → CompleteAtBS S fs cert κ k.f k.Lin k.args k.Out (bd k))
    (hsub : ∀ k ∈ ks, SubL k.Lin (bufL (fp + fs f + mt) sizes bufs ++ Lin))
    (targs' : List E) (more : Bool)
    (hσ : ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f + mt) sizes bufs ++ Lin) → ∀ outs, OutsOk ks outs →
      ∃ σ : Val, fn.params.map σ = args ∧
      Stmt.HoldsListB S (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = []) ∧
      AL.map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
      (AL.map Prod.fst).map σ = (bases (fp + fs f + mt) sizes).map (fun b => ofK (gpow b)) ∧
      CallsMatch σ (fronts.map (mkCall σ)) ks outs ∧ decide (σ tc ≠ 0) = more ∧
      targs.map σ = targs' ∧
      ∀ q ∈ pre.filterMap LeanVM.Guest.B1.Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
        (RegionL Lin i ∨ RegionL (bufL (fp + fs f + mt) sizes bufs) i)) :
    ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧
      n ≤ sizes.sum + kidsBound fs bd ks ∧
      ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) →
        (more = true → RelAtInB S coreProgram fs cert rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          targs' []) →
        (more = false → mt = fs f) →
        RelAtInB S coreProgram fs cert rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f args [] := by
  set Lb := bufL (fp + fs f + mt) sizes bufs with hLb
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromInS_of_kidsB (S := S) (fs := fs) (cert := cert) κ bd ks hks
    (fp + fs f + mt + sizes.sum)
  refine ⟨sizes.sum + N, Lb ++ L, ?_,
    disj_append (bufL_disj _ _ _ hbl) hD (LeanVM.Guest.B1.bufL_within _ _ _ hbl) hW le_rfl,
    by omega, fun rd hlow hL htail hnot => ?_⟩
  · rw [within_append]
    exact ⟨(LeanVM.Guest.B1.bufL_within _ _ _ hbl).mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
  rw [List.append_assoc] at hL
  obtain ⟨hLb, hL'⟩ := memL_append.mp hL
  obtain ⟨hL1, hL2⟩ := memL_append.mp hL'
  obtain ⟨σ, hp, hH, hsz, hdst, hcm, htk, hta, hld⟩ := hσ rd hlow (memL_append.mpr ⟨hLb, hL2⟩) outs ho
  have hwf : Stmt.wfList coreProgram fn.body = true :=
    coreProgram_wf fn (List.mem_of_find?_eq_some hf)
  have hw := walk_straight σ [] pre hs
  rw [← hb] at hw
  have hsat := walkB_sat fn.body hwf hH
  rw [hw] at hsat
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ pre hs
  rw [hal] at e1 e2
  have hsz' := e2.trans hsz
  rw [had] at e3
  rw [hcs, List.map_append] at e4
  have hld' := LeanVM.Guest.B1.loadAddrs_straight σ pre hs
  have hc : (mkCall σ (some tc, f, targs, [])).taken = more := htk
  have hown : ∀ i, RegionL Lb i → ownData cert fp (fp + fs f + mt) f (allocs σ (pre.flatMap (slEvs σ)))
      (pre.flatMap (slEvs σ)) i := fun i hi => by
    rw [hsz']
    exact Or.inl (LeanVM.Guest.B1.bufL_region _ _ _ hbl i hi)
  have := relAtInB_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := fun _ => False) (Dk := fun i => False ∨ outRegion ks outs i) (Rt := RegionL Lin)
    (Dt := fun _ => False) (fp := fp) (m := mt) (N := N) (σ := σ) (rd := rd) coreProgram_wf hf hl hp hw rfl
    (fun e he => (hsat.1 e he).1) e4 ?_ (by rw [e1, hsz']; exact hdst) (by rw [e3]; simp) ?_
    (fun i hi => Or.inl hi) ?_ (fun i hi => hi.elim)
  · rwa [hsz', Nat.add_assoc] at this
  · cases more with
    | true =>
      simp only [hc, ↓reduceIte]
      simp only [mkCall, List.map_nil]
      rw [hta]
      exact htail rfl
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact hnot rfl
  · have hsum : (allocs σ (pre.flatMap (slEvs σ))).sum = sizes.sum := by rw [hsz']
    rw [hsum]
    exact hK rd σ _ _ (fun _ => False) hcm hlow hL1
      (LeanVM.Guest.B1.memL_lins fun k hk => (hsub k hk).1 rd (memL_append.mpr ⟨hLb, hL2⟩))
      (regionsOk_of_sub _ _ _ fun k hk i hi =>
        (regionL_append_or ((hsub k hk).2 i hi)).elim (fun h => Or.inr (hown i h)) Or.inl)
  · intro A hA
    rw [hld', List.mem_map] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    obtain ⟨i, hi, hr⟩ := hld q hq
    exact ⟨i, hi, hr.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inl (hown i h)⟩

end
end LeanVM.Guest.B1.Main
