/-
  LeanVM.Guest.B1.Comp.Digest.LoadsT

  Completeness with trees loading given words: the uniform placed form of a callee whose tree
  loads the words its precondition names, and the leaf, node and loop lemmas building such trees.
-/

module

public import LeanVM.Guest.B1.Comp.TreeRoot
public import LeanVM.Guest.B1.Comp.Digest.NodeAtC
public import LeanVM.Guest.B1.Comp.Tables.LoadsL

/-!
# Callees whose trees load the words they read

The image the decoder reads holds the honest tree's load equations (`Tree.loadEqns`), not every
word of the caller's layout. A callee's precondition names the words it reads (`LoadHolds`,
`CellsAt`, `ReadsAt`); here its tree loads them:

* `LoadsAt t p off v` (`(p·g^off, v)` is a load equation of `t`, as `LoadHolds rd p off v`),
  `LoadsCells t p xs` (as `CellsAt rd p xs`), `LoadsAll A t` (every equation of `A`);
* `CompleteRelBST`: `CompleteRelBS` by trees satisfying `Q args rets` (`CompleteRelBST.toBS`
  forgets it);
* `CompleteAtBS.toBST_valid`: when every valid tree satisfies `Q`, the placed tree does (pure
  callees);
* `completeAtS_leafBT`, `completeAtS_nodeBT`, `completeAtS_loopBT`: `completeAtS_leafB`,
  `completeAtS_nodeB`, `completeAtS_loopB` by trees loading `A`, each equation of `A` loaded by
  the node's path or by an entered callee's tree (`relAtInBT_of_walk_loop` the loop's
  composition);
* `loadEq_of_load`: a load event of a path whose events hold reads the word the memory holds.

The callees' trees are bounded by `CompleteAtBST`, composed through `TreeRoot.lean`'s weighted
forms at no weights (`wE`, over `Empty`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Digest (KidR CallsR callsMatch_of callsR_snoc regionsOk_all memL_lins_of)

@[expose] public section

/-! ## Words a tree loads -/

/-- **The tree loads `v` through `p` at offset `off`**: `(p·g^off, v)` is one of its load
equations (`LoadHolds rd p off v`'s word). -/
def LoadsAt (t : Tree) (p : E) (off : ℕ) (v : E) : Prop :=
  (p.limb 0 * Parameters.gpow off, v) ∈ t.loadEqns coreProgram

/-- **The tree loads the cells `xs` at `p, p·g, …`** (`CellsAt rd p xs`'s words). -/
def LoadsCells (t : Tree) (p : E) (xs : List E) : Prop :=
  ∀ k (h : k < xs.length), LoadsAt t p k xs[k]

/-- **The tree loads every equation of `A`.** -/
def LoadsAll (A : K × E → Prop) (t : Tree) : Prop :=
  ∀ q, A q → q ∈ t.loadEqns coreProgram

/-- The load equations of the cells `xs` at `p, p·g, …`. -/
def CellsEq (p : E) (xs : List E) (q : K × E) : Prop :=
  ∃ k, ∃ h : k < xs.length, q = (p.limb 0 * Parameters.gpow k, xs[k])

theorem LoadsAll.at {A : K × E → Prop} {t : Tree} (h : LoadsAll A t) {p : E} {off : ℕ} {v : E}
    (hA : A (p.limb 0 * Parameters.gpow off, v)) : LoadsAt t p off v :=
  h _ hA

theorem LoadsAll.cells {A : K × E → Prop} {t : Tree} (h : LoadsAll A t) {p : E} {xs : List E}
    (hA : ∀ q, CellsEq p xs q → A q) : LoadsCells t p xs :=
  fun k hk => h _ (hA _ ⟨k, hk, rfl⟩)

theorem LoadsAll.mono {A A' : K × E → Prop} {t : Tree} (h : LoadsAll A t) (hA : ∀ q, A' q → A q) :
    LoadsAll A' t :=
  fun q hq => h q (hA q hq)

/-- Cells loaded at a g-power `ofK (g^c)`: the words at `g^(c+k)` (`LoadsWords`). -/
theorem LoadsCells.gpow {t : Tree} {c : ℕ} {xs : List E} (h : LoadsCells t (ofK (Parameters.gpow c)) xs) :
    ∀ k (hk : k < xs.length), (Parameters.gpow (c + k), xs[k]) ∈ t.loadEqns coreProgram := by
  intro k hk
  have := h k hk
  unfold LoadsAt at this
  rwa [Main.addr_ofK] at this

/-- **A load event reads the memory's word**: on a path whose events hold, the load through `p`
at `off`, `σ p = p'`, is the load equation `(p'·g^off, v)` of the word `p'·g^off` holds. -/
theorem loadEq_of_load {S : BlakeSem} {rd : Reader} {σ : Val} {es : List Ev} {d p : V} {off : ℕ}
    {p' v : E} (hes : ∀ e ∈ es, e.HoldsB S rd σ) (hm : Ev.atom (.load d p off) ∈ es) (hp : σ p = p')
    (hv : LoadHolds rd p' off v) : (p'.limb 0 * Parameters.gpow off, v) ∈ evLoadEqns σ es := by
  have hl : LoadHolds rd (σ p) off (σ d) := hes _ hm
  rw [hp] at hl
  rw [← hp, show v = σ d from Option.some.inj (hv.2.symm.trans hl.2)]
  exact mem_evLoadEqns hm

/-! ## The placed form with loads -/

variable {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ}

variable (S) in
/-- **`CompleteRelBS` by trees satisfying `Q args rets`** (at the frame pointer and the memory). -/
def CompleteRelBST (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) (B : ℕ)
    (Q : List E → List E → ℕ → Reader → Tree → Prop) : Prop :=
  ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) →
    CompleteAtBST S fs cert k f Lin args (Returns rets) B (Q args rets)

theorem CompleteRelBST.toBS {k : ℕ} {f : String} {Pre : Reader → List E → List E → Prop} {B : ℕ}
    {Q : List E → List E → ℕ → Reader → Tree → Prop} (h : CompleteRelBST S fs cert k f Pre B Q) :
    CompleteRelBS S fs cert k f Pre B :=
  fun args rets Lin hp => (h args rets Lin hp).toBS

theorem CompleteRelBST.mono {k : ℕ} {f : String} {Pre : Reader → List E → List E → Prop} {B : ℕ}
    {Q Q' : List E → List E → ℕ → Reader → Tree → Prop} (h : CompleteRelBST S fs cert k f Pre B Q)
    (hQ : ∀ args rets fp rd t, Q args rets fp rd t → Q' args rets fp rd t) :
    CompleteRelBST S fs cert k f Pre B Q' := fun args rets Lin hp fp =>
  let ⟨n, Lown, rets', Lout, ho, hW, hd, hn, hr⟩ := h args rets Lin hp fp
  ⟨n, Lown, rets', Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hq, hn', hv, hb, hp', ht, hl', hd'⟩ := hr rd hl hm
    ⟨t, hQ args rets fp rd t hq, hn', hv, hb, hp', ht, hl', hd'⟩⟩

/-- `CompleteAtBST` at a weaker predicate. -/
theorem CompleteAtBST.qmono {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Q Q' : ℕ → Reader → Tree → Prop}
    (h : CompleteAtBST S fs cert κ f Lin args Out B Q) (hQ : ∀ fp rd t, Q fp rd t → Q' fp rd t) :
    CompleteAtBST S fs cert κ f Lin args Out B Q' := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hq, hn', hv, hb, hp, ht, hl', hd'⟩ := hr rd hl hm
    ⟨t, hQ fp rd t hq, hn', hv, hb, hp, ht, hl', hd'⟩⟩

theorem CompleteAtBST.bmono {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B B' : ℕ} {Q : ℕ → Reader → Tree → Prop}
    (h : CompleteAtBST S fs cert κ f Lin args Out B Q) (hB : B ≤ B') :
    CompleteAtBST S fs cert κ f Lin args Out B' Q := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn.trans hB, hr⟩

/-- The class is empty, or a memory of it exists (`completeRel_casesBS` with predicates). -/
theorem completeRel_casesBST {κ : ℕ} {f : String} {Pre : Reader → List E → List E → Prop} {B : ℕ}
    {Q : List E → List E → ℕ → Reader → Tree → Prop}
    (h : ∀ args rets Lin, (∀ rd, LowDef κ rd → MemL rd Lin → Pre rd args rets) →
      ∀ rd1, LowDef κ rd1 → MemL rd1 Lin →
        CompleteAtBST S fs cert κ f Lin args (Returns rets) B (Q args rets)) :
    CompleteRelBST S fs cert κ f Pre B Q := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  · obtain ⟨rd1, hl1, hL1⟩ := hex
    exact h args rets Lin hpre rd1 hl1 hL1 fp
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL

/-- **Every valid tree satisfies `Q`, so the placed one does.** -/
theorem CompleteAtBS.toBST_valid {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Q : ℕ → Reader → Tree → Prop}
    (h : CompleteAtBS S fs cert κ f Lin args Out B)
    (hQ : ∀ fp rd (t : Tree) rets Lout, Out rets Lout → LowDef κ rd → MemL rd Lin → t.name = f →
      t.ValidB S coreProgram rd args rets → Q fp rd t) :
    CompleteAtBST S fs cert κ f Lin args Out B Q := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hn', hv, hb, hp, ht, hl', hd'⟩ := hr rd hl hm
    ⟨t, hQ fp rd t rets Lout ho hl (Main.memL_append.mp hm).2 hn' hv, hn', hv, hb, hp, ht, hl', hd'⟩⟩

/-! ## No weights -/

/-- No weights: `TreeRoot.lean`'s weighted forms over `Empty`. -/
abbrev wE : Empty → String → ℕ := fun e => e.elim

theorem RelAtInWST.toBT {Θ : Type} {w : Θ → String → ℕ} {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ}
    {f : String} {args rets : List E} {Bw : Θ → ℕ} {Q : Tree → Prop}
    (h : RelAtInWST S fs cert w rd R D fp n f args rets Bw Q) :
    RelAtInBT S fs cert rd R D fp n f args rets Q :=
  let ⟨t, hq, hn, hv, hb, hp, ht, hl, hd, _⟩ := h
  ⟨t, hq, hn, hv, hb, hp, ht, hl, hd⟩

theorem RelAtInBT.toWSTE {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Q : Tree → Prop} (h : RelAtInBT S fs cert rd R D fp n f args rets Q) :
    RelAtInWST S fs cert wE rd R D fp n f args rets (fun e => e.elim) Q :=
  let ⟨t, hq, hn, hv, hb, hp, ht, hl, hd⟩ := h
  ⟨t, hq, hn, hv, hb, hp, ht, hl, hd, fun θ => θ.elim⟩

theorem CompleteAtBST.toWSTE {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Q : ℕ → Reader → Tree → Prop}
    (h : CompleteAtBST S fs cert κ f Lin args Out B Q) :
    CompleteAtWST S fs cert wE κ f Lin args Out B (fun e => e.elim) Q := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm => (hr rd hl hm).toWSTE⟩

/-! ## The callees' loads -/

/-- **The entered callees' trees load their equations**: a callee's tree satisfying
`LoadsAll (Ak k)` where it is placed, its equations are the caller's callees'. -/
theorem loadsKids_of_sat {rd : Reader} {σ : Val} (Ak : Kid → K × E → Prop) :
    ∀ {cs : List Call} {ks : List KidR} {bs : List ℕ} {kids : List Tree},
    CallsR σ cs ks → Tree.KidsValidB S coreProgram rd σ cs kids → bs.length = kids.length →
    KidsSat cs ((ks.map KidR.kid).map fun k (_ : ℕ) t => LoadsAll (Ak k) t) bs kids →
    ∀ k ∈ ks, k.taken = true → ∀ q, Ak k.kid q → q ∈ Tree.loadEqnsKids coreProgram kids
  | [], [], _, _, _, _, _, _, _, hk, _, _, _ => absurd hk List.not_mem_nil
  | [], _ :: _, _, _, hc, _, _, _, _, _, _, _, _ => hc.elim
  | _ :: _, [], _, _, hc, _, _, _, _, _, _, _, _ => hc.elim
  | _ :: _, _ :: _, _, [], _, hv, _, _, _, _, _, _, _ => hv.elim
  | _ :: _, _ :: _, [], _ :: _, _, _, hb, _, _, _, _, _, _ => absurd hb (by simp)
  | _ :: _, k :: ks, _ :: _, _ :: _, ⟨_, hct, _, hc⟩, hv, hb, hs, k', hk', ht, q, hq => by
    simp only [List.map_cons, KidsSat] at hs
    rw [Tree.loadEqnsKids]
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact List.mem_append_left _ (hs.1 (hct.trans ht) q hq)
    · exact List.mem_append_right _
        (loadsKids_of_sat Ak hc hv.2.2 (by simpa using hb) hs.2 k' hk' ht q hq)

/-! ## A function's own buffers -/

/-- **`completeAtS_leafB` by a tree loading `A`**: each equation of `A` loaded by the path. -/
theorem completeAtS_leafBT {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (k : ℕ) (Lin : Layout) (args rets : List E) (sizes : List ℕ)
    (own : ℕ → List (List E)) (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (A : K × E → Prop)
    (hσ : ∀ fp rd, LowDef k rd → MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.HoldsB S rd σ) ∧
        calls es = [] ∧ addrs es = [] ∧ allocs σ es = sizes ∧
        (allocDsts es).map σ = (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
          (RegionL (bufL (fp + fs f) sizes (own fp)) i ∨ RegionL Lin i)) ∧
        ∀ q, A q → q ∈ evLoadEqns σ es) :
    CompleteAtBST S fs cert k f Lin args (Returns rets) (fs f + sizes.sum) fun _ _ t => LoadsAll A t := by
  intro fp
  refine ⟨fs f + sizes.sum, bufL (fp + fs f) sizes (own fp), rets, [], ⟨rfl, rfl⟩,
    by simpa using (bufL_within _ _ _ (hown fp)).mono (by omega) (by omega),
    by simpa using bufL_disj _ _ _ (hown fp), le_rfl, fun rd hlow hL => ?_⟩
  simp only [List.nil_append] at hL
  obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
  obtain ⟨σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload, hA⟩ := hσ fp rd hlow hL1 hL2
  have h := relAtInWST_of_walk (S := S) (fs := fs) (cert := cert) (w := wE) (rd := rd) (σ := σ)
    (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp) (bws := [])
    (qs := []) (Q := LoadsAll A) hf (Or.inl hl) hp hw hr hes (by rw [hal]; exact hbuf)
    (by rw [ha]; simp) (by rw [hc]; exact ⟨rfl, fun _ h => h⟩) (fun A hA => ?_)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq) (fun kids _ _ q hq => ?_)
  · rw [hal] at h; simpa using h.toBT
  · obtain ⟨i, hi, h | h⟩ := hload A hA
    · exact ⟨i, hi, Or.inl (Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i h))⟩
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
  · rw [Tree.loadEqns, events_node hf hw]
    exact List.mem_append_left _ (hA q hq)

/-! ## A function with callees -/

/-- **`completeAtS_nodeB` by a tree loading `A`**: the entered callees' trees loading `Ak`, each
equation of `A` loaded by the path or by an entered callee. -/
theorem completeAtS_nodeBT {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E) (sizes : List ℕ)
    (Lb : ℕ → Layout) (hLb : ∀ fp i, RegionL (Lb fp) i →
      ∃ q ∈ sizes.zip (bases (fp + fs f) sizes), q.2 ≤ i ∧ i < q.2 + q.1)
    (hWb : ∀ fp, Within (Lb fp) (fp + fs f) sizes.sum) (hDb : ∀ fp, DisjL (Lb fp))
    (ks : ℕ → List KidR) (bd : Kid → ℕ) (Ak : Kid → K × E → Prop)
    (hok : ∀ fp, ∀ k ∈ ks fp, k.taken = true →
      CompleteAtBST S fs cert κ k.f k.Lin k.args (Returns k.rets) (bd k.kid)
        fun _ _ t => LoadsAll (Ak k.kid) t)
    (hkR : ∀ fp, ∀ k ∈ ks fp, k.taken = true → ∀ i, RegionL k.Lin i → RegionL (Lb fp) i ∨ RegionL Lin i)
    (B : ℕ) (hB : ∀ fp, fs f + sizes.sum + kidsBound fs bd ((ks fp).map KidR.kid) ≤ B)
    (A : K × E → Prop)
    (hσ : ∀ fp rd, LowDef κ rd → MemL rd (Lb fp) → MemL rd Lin →
      (∀ k ∈ ks fp, MemL rd k.Lin) ∧ ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.HoldsB S rd σ) ∧
        CallsR σ (calls es) (ks fp) ∧ addrs es = [] ∧ allocs σ es = sizes ∧
        (allocDsts es).map σ = (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ (RegionL (Lb fp) i ∨ RegionL Lin i)) ∧
        ∀ q, A q → q ∈ evLoadEqns σ es ∨ ∃ k ∈ ks fp, k.taken = true ∧ Ak k.kid q) :
    CompleteAtBST S fs cert κ f Lin args (Returns rets) B fun _ _ t => LoadsAll A t := by
  intro fp
  have hok' : ∀ k ∈ (ks fp).map KidR.kid, k.taken = true →
      CompleteAtWST S fs cert wE κ k.f k.Lin k.args k.Out (bd k) (fun e => e.elim)
        (fun _ _ t => LoadsAll (Ak k) t) := by
    intro k hk ht
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact (hok fp k' hk' ht).toWSTE
  obtain ⟨N, LK, outs, ho, hW, hD, hNb, -, hK⟩ :=
    kidsFromInWST_of_kidsBW (S := S) (fs := fs) (cert := cert) (w := wE) κ bd (fun _ e => e.elim)
      (fun k _ _ t => LoadsAll (Ak k) t) _ hok' (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, Lb fp ++ LK, rets, [], ⟨rfl, rfl⟩, ?_, ?_, le_trans (by omega) (hB fp),
    fun rd hlow hL => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨(hWb fp).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append (hDb fp) hD (hWb fp) hW (by omega)
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLb', hLK⟩ := Main.memL_append.mp hLo
  obtain ⟨hkL, σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload, hA⟩ := hσ fp rd hlow hLb' hLin
  have hbo : ∀ i, RegionL (Lb fp) i → ownData cert fp (fp + fs f) f (allocs σ es) es i := fun i hi => by
    rw [hal]; exact Or.inl (hLb fp i hi)
  have h := relAtInWST_of_walk (S := S) (fs := fs) (cert := cert) (w := wE) (rd := rd) (σ := σ)
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion ((ks fp).map KidR.kid) outs i)
    (fp := fp) (N := N) (bws := Main.kidsWs (fun _ e => e.elim) ((ks fp).map KidR.kid))
    (qs := ((ks fp).map KidR.kid).map fun k _ t => LoadsAll (Ak k) t) (Q := LoadsAll A) hf (Or.inl hl) hp hw hr hes (by rw [hal]; exact hbuf)
    (by rw [ha]; simp) ?_ ?_ (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq) ?_
  · rw [hal] at h; exact h.toBT
  · rw [hal]
    refine hK rd σ _ _ (fun _ => False) (Digest.callsMatch_of hc ho) hlow hLK (memL_lins_of fun k hk => ?_)
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
  · intro kids hkv hks q hq
    rw [Tree.loadEqns, events_node hf hw]
    rcases hA q hq with h | ⟨k, hk, ht, h⟩
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (loadsKids_of_sat Ak hc hkv (by rw [length_bases, List.length_map])
        hks k hk ht q h)

/-! ## A loop helper -/

section Loop

variable {rd : Reader} {σ : Val}

/-- **`relAtInB_of_walk_loop` by a tree satisfying `Q`**: its other callees' trees satisfying
`qs` where they are placed (`KidsFromInWST` at no weights), its tail's `qt` when entered. -/
theorem relAtInBT_of_walk_loop {R D Dk Rt Dt : ℕ → Prop} {fp m N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {cs : List Call} {c : Call}
    {bws : List (Empty → ℕ)} {qs : List (ℕ → Tree → Prop)} {qt : Tree → Prop} {Q : Tree → Prop}
    (hf : coreProgram.find? f = some fn) (hl : coreProgram.loop f = true) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.HoldsB S rd σ)
    (hc : calls es = cs ++ [c])
    (htail : if c.taken then RelAtInBT S fs cert rd Rt Dt (fp + fs f) m c.f (c.args.map σ)
      (c.rets.map σ) qt else m = fs c.f)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f + m) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromInWST S fs cert wE rd σ
      (fun i => R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i)
      (fun _ => False) cs bws qs (fp + fs f + m + (allocs σ es).sum) N Dk)
    (hRt : ∀ i, Rt i → R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ R i ∨ Dk i ∨ (c.taken = true ∧ Dt i)))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i ∨
      (c.taken = true ∧ Dt i))
    (hQ : ∀ (ks : List Tree) (k : Tree), Tree.KidsValidB S coreProgram rd σ cs ks →
      KidsSat cs qs (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))) ks →
      (c.taken = true → qt k) → Q (Memory.Tree.node f σ (allocs σ es) (ks ++ [k]))) :
    RelAtInBT S fs cert rd R D fp (fs f + m + (allocs σ es).sum + N) f args rets Q := by
  have htk := takes_of_calls coreProgram_wf (List.mem_of_find?_eq_some hf) hw
  rw [hc] at htk
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl, -, hkq⟩ := kidsST_of_kidsFromInWT _ _ _ _ _ _ _ _
    (fun c' hc' => htk c' (List.mem_append_left _ hc')) hk
  have htail' : if c.taken then RelAtInWST S fs cert wE rd Rt Dt (fp + fs f) m c.f (c.args.map σ)
      (c.rets.map σ) (fun e => e.elim) ((fun _ => qt) (fp + fs f)) else m = fs c.f := by
    by_cases ht : c.taken = true
    · rw [ite_eq_left ht] at htail ⊢; exact htail.toWSTE
    · rw [ite_eq_right ht] at htail ⊢; exact htail
  obtain ⟨k, hkv', hkb', hkp', hkt, hkl', hkd', -, hkq'⟩ :=
    kidST_ofInW (q := fun _ => qt) (htk c (List.mem_append_right _ List.mem_cons_self)) htail'
  have hns : (ks ++ [k]).map (Tree.total fs) = ks.map (Tree.total fs) ++ [m] := by
    rw [List.map_append, List.map_singleton, hkt]
  have hbb : bufBase fs coreProgram.loop fp f ((ks ++ [k]).map (Tree.total fs)) = fp + fs f + m := by
    rw [hns]; simp [bufBase, hl]
  have hkpos : kidPos fs coreProgram.loop fp f (allocs σ es) ((ks ++ [k]).map (Tree.total fs)) =
      bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs)) ++ [fp + fs f] := by
    rw [kidPos, ite_eq_left hl, hbb, hns, List.dropLast_concat, List.getLast?_concat]
    rfl
  have hlen : (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))).length = ks.length := by
    rw [length_bases, List.length_map]
  have hdata : ∀ i, (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i ↔
      ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨
        Tree.DataKids coreProgram fs cert (bases (fp + fs f + m + (allocs σ es).sum)
          (ks.map (Tree.total fs))) ks i ∨
        k.Data coreProgram fs cert (fp + fs f) i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos, dataKids_append hlen, dataKids_cons]
    simp only [not_dataKids_nil, or_false]
  refine ⟨.node f σ (allocs σ es) (ks ++ [k]), hQ ks k hkv hkq hkq', rfl,
    ⟨fn, hf, hp, es, vs, hw, hr, hes, by rw [hc]; exact kidsValidB_append hkv hkv'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Tree.BufsOk, events_node hf hw]
    refine ⟨rfl, bufsOkKids_append hkb ?_⟩
    rw [Tree.BufsOkKids, Tree.BufsOkKids]
    exact ⟨hkb', trivial⟩
  · rw [placed_node, events_node hf hw, NodeAt, hbb, hkpos]
    refine ⟨⟨hbuf, haddr⟩, placedKids_append hlen hkp ?_⟩
    rw [placedKids_cons]
    exact ⟨hkp', placedKids_nil⟩
  · rw [total_node, totalKids_eq_sum, hns, List.sum_append, hks]
    simp only [List.sum_cons, List.sum_nil]
    omega
  · have hDk : ∀ i, Dk i → (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i :=
      fun i h => (hkd i h).elim (fun h => h.elim) fun h => (hdata i).mpr (Or.inr (Or.inl h))
    have hDt : ∀ i, c.taken = true ∧ Dt i →
        (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i :=
      fun i h => (hdata i).mpr (Or.inr (Or.inr (hkd' h.1 i h.2)))
    have hown : ∀ i, ownData cert fp (fp + fs f + m) f (allocs σ es) es i →
        (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i :=
      fun i h => (hdata i).mpr (Or.inl h)
    rw [loadsIn_node, events_node hf hw, hkpos]
    refine ⟨fun A hA => ?_, loadsInKids_append hlen ?_ ?_⟩
    · obtain ⟨i, hi, h⟩ := hload A hA
      refine ⟨i, hi, ?_⟩
      rcases h with h | h | h | h
      · exact Or.inl (hown i h)
      · exact Or.inr h
      · exact Or.inl (hDk i h)
      · exact Or.inl (hDt i h)
    · exact hkl _ (fun i hi => hi.elim Or.inr fun h => Or.inl (hown i h)) (fun _ h => h.elim)
        (fun i hi => Or.inl ((hdata i).mpr (Or.inr (Or.inl hi))))
    · rw [loadsInKids_cons]
      refine ⟨loadsIn_mono k _ (fun i hi => ?_) hkl', loadsInKids_nil⟩
      rcases hRt i hi with h | h | h
      · exact Or.inr h
      · exact Or.inl (hown i h)
      · exact Or.inl (hDk i h)
  · intro i hi
    rcases hD i hi with h | h | h
    · exact (hdata i).mpr (Or.inl h)
    · exact (hkd i h).elim (fun h => h.elim) fun h => (hdata i).mpr (Or.inr (Or.inl h))
    · exact (hdata i).mpr (Or.inr (Or.inr (hkd' h.1 i h.2)))

end Loop

/-- **`completeAtS_loopB` by a tree loading `A`**: its other callees' trees loading `Ak`, its
tail's `At`, each equation of `A` loaded by the path, an entered callee or the entered tail. -/
theorem completeAtS_loopBT {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) (κ : ℕ) (Lin : Layout) (args rets : List E) (ks : List KidR)
    (tail : KidR) (bd : Kid → ℕ) (bt : ℕ) (Ak : Kid → K × E → Prop) (At : K × E → Prop)
    (hok : ∀ k ∈ ks, k.taken = true →
      CompleteAtBST S fs cert κ k.f k.Lin k.args (Returns k.rets) (bd k.kid)
        fun _ _ t => LoadsAll (Ak k.kid) t)
    (htail : tail.taken = true →
      CompleteAtBST S fs cert κ tail.f tail.Lin tail.args (Returns tail.rets) bt
        fun _ _ t => LoadsAll At t)
    (B : ℕ) (hB : fs f + max bt (fs tail.f) + kidsBound fs bd (ks.map KidR.kid) ≤ B)
    (hkR : ∀ k ∈ ks ++ [tail], k.taken = true → ∀ i, RegionL k.Lin i → RegionL Lin i)
    (A : K × E → Prop)
    (hσ : ∀ rd, LowDef κ rd → MemL rd Lin →
      (∀ k ∈ ks ++ [tail], MemL rd k.Lin) ∧ ∃ (σ : Val) (es : List Ev) (vs : List V),
        fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.HoldsB S rd σ) ∧
        CallsR σ (calls es) (ks ++ [tail]) ∧ addrs es = [] ∧ allocs σ es = [] ∧ allocDsts es = [] ∧
        (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ RegionL Lin i) ∧
        ∀ q, A q → q ∈ evLoadEqns σ es ∨ (∃ k ∈ ks, k.taken = true ∧ Ak k.kid q) ∨
          (tail.taken = true ∧ At q)) :
    CompleteAtBST S fs cert κ f Lin args (Returns rets) B fun _ _ t => LoadsAll A t := by
  intro fp
  classical
  have hok' : ∀ k ∈ ks.map KidR.kid, k.taken = true →
      CompleteAtWST S fs cert wE κ k.f k.Lin k.args k.Out (bd k) (fun e => e.elim)
        (fun _ _ t => LoadsAll (Ak k) t) := by
    intro k hk ht
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact (hok k' hk' ht).toWSTE
  -- the tail, at `fp + fs f`
  obtain ⟨m, Lt, hWt, hDt, hmb, hT⟩ : ∃ (m : ℕ) (Lt : Layout), Within Lt (fp + fs f) m ∧ DisjL Lt ∧
      m ≤ max bt (fs tail.f) ∧
      ∀ rd, LowDef κ rd → MemL rd Lt → MemL rd tail.Lin →
        if tail.taken then RelAtInBT S fs cert rd (RegionL tail.Lin) (RegionL []) (fp + fs f) m
          tail.f tail.args tail.rets (LoadsAll At) else m = fs tail.f := by
    by_cases ht : tail.taken = true
    · obtain ⟨m, Lown, rets', Lout, ⟨rfl, rfl⟩, hW, hDw, hmb, hR⟩ := htail ht (fp + fs f)
      refine ⟨m, Lown, by simpa using hW, by simpa using hDw, le_trans hmb (le_max_left _ _),
        fun rd hl hL hL' => ?_⟩
      rw [ite_pos' ht]
      exact hR rd hl (by simpa using Main.memL_append.mpr ⟨hL, hL'⟩)
    · refine ⟨fs tail.f, [], fun q hq => by simp at hq, disj_nil, le_max_right _ _,
        fun rd _ _ _ => ?_⟩
      rw [ite_neg' ht]
  obtain ⟨N, LK, outs, ho, hW, hD, hNb, -, hK⟩ :=
    kidsFromInWST_of_kidsBW (S := S) (fs := fs) (cert := cert) (w := wE) κ bd (fun _ e => e.elim)
      (fun k _ _ t => LoadsAll (Ak k) t) _ hok' (fp + fs f + m)
  refine ⟨fs f + m + 0 + N, Lt ++ LK, rets, [], ⟨rfl, rfl⟩, ?_, ?_, le_trans (by omega) hB,
    fun rd hlow hL => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hWt.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append hDt hD hWt hW le_rfl
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLt, hLK⟩ := Main.memL_append.mp hLo
  obtain ⟨hkL, σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload, hA⟩ := hσ rd hlow hLin
  obtain ⟨cs, c, hcs, hc1, ⟨ct1, ct2, ct3, -⟩⟩ := callsR_snoc hc
  have hTr := hT rd hlow hLt (hkL tail (by simp))
  have h := relAtInBT_of_walk_loop (S := S) (fs := fs) (cert := cert) (rd := rd) (σ := σ)
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion (ks.map KidR.kid) outs i)
    (Rt := fun i => tail.taken = true ∧ RegionL tail.Lin i) (Dt := RegionL []) (fp := fp) (m := m)
    (N := N) (c := c) (cs := cs) (bws := Main.kidsWs (fun _ e => e.elim) (ks.map KidR.kid))
    (qs := (ks.map KidR.kid).map fun k _ t => LoadsAll (Ak k) t) (qt := LoadsAll At) (Q := LoadsAll A) hf hl hp hw hr
    hes hcs ?_ (by rw [hbuf, hal]; rfl) (by rw [ha]; simp) ?_ ?_ ?_
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq) ?_
  · rwa [hal] at h
  · by_cases ht : tail.taken = true
    · rw [ct2, ite_pos' ht, ct1, (ct3 ht).1, (ct3 ht).2]
      rw [ite_pos' ht] at hTr
      obtain ⟨t, hq, hn, hv, hb, hp', htt, hl', hd'⟩ := hTr
      exact ⟨t, hq, hn, hv, hb, hp', htt, loadsIn_mono t _ (fun i hi => ⟨ht, hi⟩) hl', hd'⟩
    · have ht' : tail.taken = false := by simpa using ht
      rw [ct2, ht', ct1]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ht'] at hTr
      exact hTr
  · rw [hal, List.sum_nil, Nat.add_zero]
    refine hK rd σ _ _ (fun _ => False) (Digest.callsMatch_of hc1 ho) hlow hLK (memL_lins_of fun k hk => ?_)
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
  · intro kids k hkv hks hkt q hq
    rw [Tree.loadEqns, events_node hf hw, loadEqnsKids_append]
    rcases hA q hq with h | ⟨k', hk', ht, h⟩ | ⟨ht, h⟩
    · exact List.mem_append_left _ h
    · refine List.mem_append_right _ (List.mem_append_left _ ?_)
      exact loadsKids_of_sat Ak hc1 hkv (by rw [length_bases, List.length_map]) hks k' hk' ht q h
    · refine List.mem_append_right _ (List.mem_append_right _ ?_)
      rw [Tree.loadEqnsKids]
      exact List.mem_append_left _ (hkt (ct2.trans ht) q h)

end
end LeanVM.Guest.B1
