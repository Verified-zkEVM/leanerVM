/-
  LeanVM.Guest.B1.Comp.FreeTree

  The trees of a function free of `BLAKE2S` are valid under every semantics alike, so its placed
  completeness (`CompleteAtBS`, `CompleteAtWS`) and its trees' bounds carry over from the deployed
  ones.
-/

module

public import LeanVM.Guest.B1.Comp.CompleteAtB
public import LeanVM.Guest.B1.Main.WeightBS

/-!
# Functions free of `BLAKE2S`, placed

`relB_eq_of_freeOn` (CoreB) says a function of a set `F` closed under calls and free of `BLAKE2S`
(`Program.FreeOn`) has the same relation under every semantics. Its trees too: the path of a body
free of `BLAKE2S` has no `BLAKE2S` event and calls only functions of `F` (`walk_freeIn`), so every
event checks alike under any two semantics (`ev_holdsB_freeIn`) and a tree of a function of `F` is
valid under one when it is under the other (`validB_freeOn`). Hence:

* `relAtInB_freeOn`, `relAtInWS_freeOn`: the placed relations agree;
* `completeAtBS_of_freeOn`, `completeAtWS_of_freeOn`: the deployed placed completeness
  (`CompleteAtB`, `Main.CompleteAtW`) gives it under any semantics;
* `totalLeB_of_freeOn`, `weightLeB_of_freeOn`: the deployed bounds on its trees.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {F : List String}

/-- An event that is no `BLAKE2S` check and sets up frames of `F` only. -/
def Ev.FreeIn (F : List String) : Ev → Prop
  | .atom (.blake2s ..) => False
  | .call f _ _ => f ∈ F
  | .skip f _ => f ∈ F
  | _ => True

/-- An outcome whose events are `Ev.FreeIn F`. -/
def Out.FreeIn (F : List String) : Out → Prop
  | .fall es => ∀ e ∈ es, e.FreeIn F
  | .ret es _ => ∀ e ∈ es, e.FreeIn F
  | .stuck => True

theorem Out.freeIn_pre {es : List Ev} {o : Out} (h1 : ∀ e ∈ es, e.FreeIn F) (h2 : o.FreeIn F) :
    (o.pre es).FreeIn F := by
  cases o with
  | fall es' => exact fun e he => (List.mem_append.mp he).elim (h1 e) (h2 e)
  | ret es' vs => exact fun e he => (List.mem_append.mp he).elim (h1 e) (h2 e)
  | stuck => trivial

theorem Out.freeIn_seq {o k : Out} (h1 : o.FreeIn F) (h2 : k.FreeIn F) : (o.seq k).FreeIn F := by
  cases o with
  | fall es => exact Out.freeIn_pre h1 h2
  | ret es vs => exact h1
  | stuck => trivial

theorem pick_freeIn (σ : Val) (x : V) (args rets : List V) :
    ∀ (j : ℕ) (fs : List String), fs.all F.contains = true → (pick σ x args rets j fs).FreeIn F
  | _, [], _ => trivial
  | j, f :: fs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    unfold pick
    split
    · intro e he
      rw [List.mem_singleton] at he
      subst he
      exact List.contains_iff_mem.mp h.1
    · exact pick_freeIn σ x args rets (j + 1) fs h.2

mutual
theorem walk1_freeIn (σ : Val) : ∀ (s : Stmt), Stmt.freeIn F s = true → (walk1 σ s).FreeIn F
  | .atom a, h => by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    cases a <;> trivial
  | .ite c z n, h => by
    simp only [Stmt.freeIn, Bool.and_eq_true] at h
    rw [walk1]
    refine Out.freeIn_pre (fun e he => ?_) ?_
    · rw [List.mem_singleton] at he; subst he; trivial
    · split
      · exact walk_freeIn σ z h.1
      · exact walk_freeIn σ n h.2
  | .match_ x arms, h => by
    simp only [Stmt.freeIn] at h
    rw [walk1]
    exact walkArms_freeIn σ x 0 arms h
  | .call f args rets, h => by
    simp only [Stmt.freeIn] at h
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact List.contains_iff_mem.mp h
  | .callIf c f args, h => by
    simp only [Stmt.freeIn] at h
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    · trivial
    · split
      · exact List.contains_iff_mem.mp h
      · exact List.contains_iff_mem.mp h
  | .dispatch x fs args rets, h => by
    simp only [Stmt.freeIn] at h
    rw [walk1]
    exact pick_freeIn σ x args rets 0 fs h
  | .ret vs, _ => by
    intro e he
    simp at he

theorem walk_freeIn (σ : Val) : ∀ (ss : List Stmt), Stmt.freeInList F ss = true → (walk σ ss).FreeIn F
  | [], _ => by intro e he; simp at he
  | s :: ss, h => by
    simp only [Stmt.freeInList, Bool.and_eq_true] at h
    rw [walk]
    exact Out.freeIn_seq (walk1_freeIn σ s h.1) (walk_freeIn σ ss h.2)

theorem walkArms_freeIn (σ : Val) (x : V) :
    ∀ (j : ℕ) (arms : List (List Stmt)), Stmt.freeInArms F arms = true →
      (walkArms σ x j arms).FreeIn F
  | _, [], _ => trivial
  | j, a :: as, h => by
    simp only [Stmt.freeInArms, Bool.and_eq_true] at h
    rw [walkArms]
    split
    · exact walk_freeIn σ a h.1
    · exact walkArms_freeIn σ x (j + 1) as h.2
end

variable {S S' : BlakeSem} {rd : Reader} {σ : Val}

/-- An event free of `BLAKE2S` checks alike under any two semantics. -/
theorem ev_holdsB_freeIn : ∀ (e : Ev), e.FreeIn F → (e.HoldsB S rd σ ↔ e.HoldsB S' rd σ)
  | .atom a, h => by cases a <;> first | exact Iff.rfl | exact h.elim
  | .inK _, _ => Iff.rfl
  | .call .., _ => Iff.rfl
  | .skip .., _ => Iff.rfl

/-- The frames of events free of `BLAKE2S` are of `F`. -/
theorem calls_freeIn {es : List Ev} (h : ∀ e ∈ es, e.FreeIn F) : ∀ c ∈ calls es, c.f ∈ F := by
  intro c hc
  obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
  have hf := h e he
  cases e <;> simp only [Ev.call?, reduceCtorEq, Option.some.injEq] at hce
  all_goals (subst hce; exact hf)

theorem freeIn_body {P : Core.Program} (hP : P.FreeOn F = true) {f : String} (hf : f ∈ F) {fn : Fn}
    (hfind : P.find? f = some fn) : Stmt.freeInList F fn.body = true := by
  have h := List.all_eq_true.mp hP f hf
  rw [hfind] at h
  exact h

mutual
/-- **A tree of a function free of `BLAKE2S` is valid under every semantics alike.** -/
theorem validB_freeOn {P : Core.Program} (hP : P.FreeOn F = true) :
    ∀ (t : Tree) (args rets : List E), t.name ∈ F →
      (t.ValidB S P rd args rets ↔ t.ValidB S' P rd args rets)
  | .node f σ bufs kids, args, rets, hf => by
    simp only [Tree.ValidB]
    constructor
    · rintro ⟨fn, hfind, hp, es, vs, hw, hr, hes, hk⟩
      have hE := walk_freeIn σ fn.body (freeIn_body hP hf hfind)
      rw [hw] at hE
      exact ⟨fn, hfind, hp, es, vs, hw, hr, fun e he => (ev_holdsB_freeIn e (hE e he)).mp (hes e he),
        (kidsValidB_freeOn hP σ (calls es) kids (calls_freeIn hE)).mp hk⟩
    · rintro ⟨fn, hfind, hp, es, vs, hw, hr, hes, hk⟩
      have hE := walk_freeIn σ fn.body (freeIn_body hP hf hfind)
      rw [hw] at hE
      exact ⟨fn, hfind, hp, es, vs, hw, hr, fun e he => (ev_holdsB_freeIn e (hE e he)).mpr (hes e he),
        (kidsValidB_freeOn hP σ (calls es) kids (calls_freeIn hE)).mpr hk⟩
  | .phantom .., _, _, _ => by simp only [Tree.ValidB]

/-- `validB_freeOn` for the callees. -/
theorem kidsValidB_freeOn {P : Core.Program} (hP : P.FreeOn F = true) (σ : Val) :
    ∀ (cs : List Call) (ks : List Tree), (∀ c ∈ cs, c.f ∈ F) →
      (Tree.KidsValidB S P rd σ cs ks ↔ Tree.KidsValidB S' P rd σ cs ks)
  | [], [], _ => by simp only [Tree.KidsValidB]
  | [], _ :: _, _ => by simp only [Tree.KidsValidB]
  | _ :: _, [], _ => by simp only [Tree.KidsValidB]
  | c :: cs, k :: ks, h => by
    simp only [Tree.KidsValidB]
    have hc : k.name = c.f → k.name ∈ F := fun hn => hn ▸ h c List.mem_cons_self
    have ih := kidsValidB_freeOn hP σ cs ks fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    constructor
    · rintro ⟨hn, hv, hk⟩
      refine ⟨hn, ?_, ih.mp hk⟩
      split
      · rename_i ht
        simp only [ht, ↓reduceIte] at hv
        exact (validB_freeOn hP k _ _ (hc hn)).mp hv
      · rename_i ht
        simp only [ht, Bool.false_eq_true, ↓reduceIte] at hv
        exact hv
    · rintro ⟨hn, hv, hk⟩
      refine ⟨hn, ?_, ih.mpr hk⟩
      split
      · rename_i ht
        simp only [ht, ↓reduceIte] at hv
        exact (validB_freeOn hP k _ _ (hc hn)).mpr hv
      · rename_i ht
        simp only [ht, Bool.false_eq_true, ↓reduceIte] at hv
        exact hv
end

variable {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The placed relation of a function free of `BLAKE2S`** is the same under any two semantics. -/
theorem relAtInB_freeOn (hP : P.FreeOn F = true) {f : String} (hf : f ∈ F) {R D : ℕ → Prop}
    {fp n : ℕ} {args rets : List E} :
    RelAtInB S P fs cert rd R D fp n f args rets ↔ RelAtInB S' P fs cert rd R D fp n f args rets := by
  constructor
  · rintro ⟨t, hn, hv, h⟩
    exact ⟨t, hn, (validB_freeOn hP t args rets (hn ▸ hf)).mp hv, h⟩
  · rintro ⟨t, hn, hv, h⟩
    exact ⟨t, hn, (validB_freeOn hP t args rets (hn ▸ hf)).mpr hv, h⟩

/-- The deployed bound on the trees of a function free of `BLAKE2S` holds under any semantics. -/
theorem totalLeB_of_freeOn (hP : P.FreeOn F = true) {f : String} (hf : f ∈ F) {B : List E → ℕ}
    (h : TotalLe P fs f B) : TotalLeB S P fs f B := by
  intro rd t args rets hn hv hb
  refine h rd t args rets hn ?_ hb
  rw [← validB_deployed]
  exact (validB_freeOn (S' := blakeDeployed) hP t args rets (hn ▸ hf)).mp hv

/-- The deployed weight bound on the trees of a function free of `BLAKE2S` holds under any
semantics. -/
theorem weightLeB_of_freeOn (hP : P.FreeOn F = true) {f : String} (hf : f ∈ F) {ω : String → ℕ}
    {B : List E → ℕ} (h : WeightLe P ω f B) : WeightLeB S P ω f B := by
  intro rd t args rets hn hv hb
  refine h rd t args rets hn ?_ hb
  rw [← validB_deployed]
  exact (validB_freeOn (S' := blakeDeployed) hP t args rets (hn ▸ hf)).mp hv

end
end LeanVM.Guest.Memory

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {S : BlakeSem} {F : List String} {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The deployed placed completeness of a function free of `BLAKE2S`** holds under any
semantics. -/
theorem completeAtBS_of_freeOn (hP : coreProgram.FreeOn F = true) {f : String} (hf : f ∈ F) {k : ℕ}
    {Lin : Layout} {args : List E} {Out : List E → Layout → Prop} {B : ℕ}
    (h : CompleteAtB fs cert k f Lin args Out B) : CompleteAtBS S fs cert k f Lin args Out B := by
  rw [← completeAtBS_deployed] at h
  intro fp
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  exact ⟨n, Lown, rets, Lout, ho, hw, hd, hn, fun rd hl hm => (relAtInB_freeOn hP hf).mp (hr rd hl hm)⟩

/-- **At the deployed semantics, `RelAtInWS` is `Main.RelAtInW`.** -/
theorem relAtInWS_deployed {Θ : Type} {w : Θ → String → ℕ} {rd : Reader} {R D : ℕ → Prop}
    {fp n : ℕ} {f : String} {args rets : List E} {Bw : Θ → ℕ} :
    Main.RelAtInWS blakeDeployed fs cert w rd R D fp n f args rets Bw ↔
      Main.RelAtInW fs cert w rd R D fp n f args rets Bw := by
  simp only [Main.RelAtInWS, Main.RelAtInW, validB_deployed]

/-- **At the deployed semantics, `CompleteAtWS` is `Main.CompleteAtW`.** -/
theorem completeAtWS_deployed {Θ : Type} {w : Θ → String → ℕ} {k : ℕ} {f : String} {Lin : Layout}
    {args : List E} {Out : List E → Layout → Prop} {B : ℕ} {Bw : Θ → ℕ} :
    Main.CompleteAtWS blakeDeployed fs cert w k f Lin args Out B Bw ↔
      Main.CompleteAtW fs cert w k f Lin args Out B Bw := by
  simp only [Main.CompleteAtWS, Main.CompleteAtW, relAtInWS_deployed]

/-- **The deployed placed completeness within weights of a function free of `BLAKE2S`** holds
under any semantics. -/
theorem completeAtWS_of_freeOn (hP : coreProgram.FreeOn F = true) {f : String} (hf : f ∈ F)
    {Θ : Type} {w : Θ → String → ℕ} {k : ℕ} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw : Θ → ℕ}
    (h : Main.CompleteAtW fs cert w k f Lin args Out B Bw) :
    Main.CompleteAtWS S fs cert w k f Lin args Out B Bw := by
  rw [← completeAtWS_deployed] at h
  intro fp
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  refine ⟨n, Lown, rets, Lout, ho, hw, hd, hn, fun rd hl hm => ?_⟩
  obtain ⟨t, hnm, hv, h'⟩ := hr rd hl hm
  exact ⟨t, hnm, (validB_freeOn (S' := blakeDeployed) hP t args rets (hnm ▸ hf)).mpr hv, h'⟩

end
end LeanVM.Guest.B1
