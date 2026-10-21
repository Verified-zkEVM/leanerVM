/-
  LeanVM.Guest.B1.Comp.Tables.FwdIC

  Forward completion over items under a completeness model: the `fs_next` and `squeeze`
  templates at the model's total hash, every other item as deployed.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.CompletesB
public import LeanVM.Guest.B1.Tables.VerifyTablesFwdI
public import LeanVM.Guest.B1.Tables.FlockLoopsM

/-!
# Forward completion over items, over a completeness model

`VerifyTablesFwdI.lean` over a hash model's total hash: `FItem.valsC M` is `FItem.vals` with an
`fs_next` item's values `fsValsD` at the answer `obsCvT M` and a `squeeze`'s `sqValsD` at
`sqCvT M`; `fRunIC M` runs the items forward with them. The items' shapes, their kernel-checked
facts (`fOkI`, `iObs`, `fEqs`) are the deployed ones. The obligations (`IOb.HoldsC M`) add that the
model answers each `fs_next`'s absorb and each `squeeze`. `completes_itemsC`: a body of items
completes under a completeness model's semantics once they hold (`completes_items`);
`fRunIC_eqs`, `fRunIC_eq_of_def`: its definitions hold of the final valuation.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.Guest.Memory LeanVM.E2E.Complete

@[expose] public section

/-- The values an item other than an atom sets, from `σ`, at a hash model's total hash
(`FItem.vals`). -/
noncomputable def FItem.valsC (M : HashModel) (rd : Reader) (hv : ℕ → E) (σ : Val) : FItem → List E
  | .fs s0 s1 cur j _ => memAt rd (σ cur) j :: (List.range 14).map fun k =>
      fsValsD (memAt rd (σ cur) j) (obsCvT M (decodeCv (σ s0) (σ s1)) (memAt rd (σ cur) j)) 1 k
  | .sq s0 s1 _ => (List.range 14).map fun k => sqValsD (sqCvT M (decodeCv (σ s0) (σ s1))) k
  | it => it.sets.map fun v => hv v.idx

/-- One item forward at the total hash (`fStepI`). -/
noncomputable def fStepIC (M : HashModel) (rd : Reader) (lo : ℕ) (hv : ℕ → E) (D : List ℕ)
    (σ : Val) : FItem → List ℕ × Val
  | .atom a => fStep rd lo D σ a
  | it => (fAddMany D it.sets, updMany σ it.sets (it.valsC M rd hv σ))

theorem fStepIC_fst (M : HashModel) (rd : Reader) (lo : ℕ) (hv : ℕ → E) (D : List ℕ) (σ : Val)
    (it : FItem) : (fStepIC M rd lo hv D σ it).1 = fDStepI lo D it := by
  cases it <;> simp only [fStepIC, fDStepI, fStep_fst]

/-- The items forward at the total hash (`fRunI`). -/
noncomputable def fRunIC (M : HashModel) (rd : Reader) (lo : ℕ) (hv : ℕ → E) :
    List ℕ → Val → List FItem → Val
  | _, σ, [] => σ
  | D, σ, it :: its =>
      fRunIC M rd lo hv (fStepIC M rd lo hv D σ it).1 (fStepIC M rd lo hv D σ it).2 its

/-- What an item's obligation asks of the final valuation, over a hash model: `IOb.Holds`, the
model answering each `fs_next`'s absorb and each `squeeze`. -/
def IOb.HoldsC (M : HashModel) (C : CallRel) (rd : Reader) (σf : Val) : IOb → Prop
  | .ob o => o.Holds rd σf
  | .fs s0 s1 cur j => IsInK (σf cur) ∧ (rd ((σf cur).limb 0 * Parameters.gpow j)).isSome ∧
      ∃ cv, (σf s0, σf s1) = digestScalars cv ∧
        obsCvM M cv (memAt rd (σf cur) j) = some (obsCvT M cv (memAt rd (σf cur) j))
  | .sq s0 s1 => ∃ cv, (σf s0, σf s1) = digestScalars cv ∧ sqCvM M cv = some (sqCvT M cv)
  | .callIf c f args => IsInK (σf c) ∧ (σf c ≠ 0 → C f (args.map σf) [])
  | .disp x fns args rets => ∃ (j : ℕ) (h : j < fns.length), σf x = ofK (Parameters.gpow j) ∧
      C fns[j] (args.map σf) (rets.map σf)

/-- What an item asks of the final valuation, over a hash model (`IObl`). -/
def IOblC (M : HashModel) (C : CallRel) (rd : Reader) (lo : ℕ) (D : List ℕ) (σf : Val) :
    FItem → Prop
  | .atom a => fObl1 rd lo D σf a
  | .fs s0 s1 cur j _ => IOb.HoldsC M C rd σf (.fs s0 s1 cur j)
  | .sq s0 s1 _ => IOb.HoldsC M C rd σf (.sq s0 s1)
  | .callIf c f args => IsInK (σf c) ∧ (σf c ≠ 0 → C f (args.map σf) [])
  | .disp x fns args rets => ∃ (j : ℕ) (h : j < fns.length), σf x = ofK (Parameters.gpow j) ∧
      C fns[j] (args.map σf) (rets.map σf)
  | .hint _ => True

/-- A body's obligations over a hash model (`IObls`). -/
def IOblsC (M : HashModel) (C : CallRel) (rd : Reader) (lo : ℕ) (σf : Val) :
    List ℕ → List FItem → Prop
  | _, [] => True
  | D, it :: its => IOblC M C rd lo D σf it ∧ IOblsC M C rd lo σf (fDStepI lo D it) its

/-! ## Framing -/

section
variable {M : HashModel}

theorem fStepIC_frame (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) {D : List ℕ} (σ : Val) {it : FItem}
    (hok : fOkI1 lo hi D it = true) {v : V} (h : fDef lo D v = true) :
    (fStepIC M rd lo hv D σ it).2 v = σ v := by
  cases it with
  | atom a => exact fStep_frame rd lo D σ a h
  | _ =>
    simp only [fOkI1, Bool.and_eq_true] at hok
    exact updMany_of_not_mem σ _ _ (not_mem_sets hok.1.2 h)

theorem fStepIC_upd (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) {D : List ℕ} (σ : Val) {it : FItem}
    (hok : fOkI1 lo hi D it = true) {v : V} (h : (fStepIC M rd lo hv D σ it).2 v ≠ σ v) :
    fNew lo hi D v = true := by
  cases it with
  | atom a => exact fStep_upd rd σ hok h
  | _ =>
    simp only [fOkI1, Bool.and_eq_true] at hok
    by_contra hn
    refine h (updMany_of_not_mem σ _ _ fun hm => hn ?_)
    exact List.all_eq_true.mp hok.1.2 v hm

theorem fRunIC_frame (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) : ∀ (its : List FItem) (D : List ℕ)
    (σ : Val), fOkI lo hi D its = true → ∀ {v : V}, fDef lo D v = true →
      fRunIC M rd lo hv D σ its v = σ v
  | [], _, _, _, _, _ => rfl
  | it :: its, D, σ, hok, v, h => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunIC]
    rw [fRunIC_frame rd hv its _ _ (by rw [fStepIC_fst]; exact hok.2)
      (by rw [fStepIC_fst]; exact fDStepI_mono it h), fStepIC_frame rd hv σ hok.1 h]

theorem fRunIC_upd (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) : ∀ (its : List FItem) (D : List ℕ)
    (σ : Val), fOkI lo hi D its = true → ∀ v, fRunIC M rd lo hv D σ its v ≠ σ v →
      ∃ k, v = .n k ∧ lo ≤ k ∧ k < hi
  | [], _, _, _, v, h => absurd rfl h
  | it :: its, D, σ, hok, v, h => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunIC] at h
    by_cases e : (fStepIC M rd lo hv D σ it).2 v = σ v
    · rw [← e] at h
      exact fRunIC_upd rd hv its _ _ (by rw [fStepIC_fst]; exact hok.2) v h
    · exact fNew_num (fStepIC_upd rd hv σ hok.1 e)

theorem fRunIC_ext (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) {its : List FItem} {D : List ℕ}
    {σ : Val} (hok : fOkI lo hi D its = true) : Ext lo hi σ (fRunIC M rd lo hv D σ its) := by
  intro v hv'
  by_contra hne
  obtain ⟨k, rfl, h1, h2⟩ := fRunIC_upd rd hv its D σ hok v hne
  exact hv' k h1 h2 rfl

end

/-! ## The items hold -/

theorem sets_getC {M : HashModel} {rd : Reader} {hv : ℕ → E} {σ : Val} {lo hi : ℕ} {D : List ℕ}
    {it : FItem} (hok : fOkI1 lo hi D it = true)
    (hl : it.sets.length = (it.valsC M rd hv σ).length) (σ1 : Val)
    (h1 : σ1 = updMany σ it.sets (it.valsC M rd hv σ))
    (i : ℕ) (hi : i < it.sets.length) : σ1 it.sets[i] = (it.valsC M rd hv σ)[i]'(by omega) := by
  cases it with
  | atom a => simp [FItem.sets] at hi
  | _ =>
    simp only [fOkI1, Bool.and_eq_true, decide_eq_true_eq] at hok
    rw [h1]; exact updMany_get σ _ _ hok.2 hl i hi

/-- An atom of a window is not a `BLAKE2S`. -/
theorem fOk1_noBlake {lo hi : ℕ} {D : List ℕ} {a : Atom} (hok : fOk1 lo hi D a = true) :
    Stmt.noBlakeList [.atom a] = true := by
  cases a <;> simp_all [fOk1, Stmt.noBlakeList, Stmt.noBlake]

set_option maxRecDepth 10000 in
/-- **An item holds over a completeness model** at a valuation agreeing with its step on its
values, once its obligation does (`fStepI_holds`). -/
theorem fStepIC_holds {CM : CompModel} {C : CallRel} (rd : Reader) {lo hi : ℕ} (hv : ℕ → E)
    {D : List ℕ} {σ : Val} {it : FItem} (hok : fOkI1 lo hi D it = true) {σf : Val}
    (hag : ∀ v, fDef lo (fDStepI lo D it) v = true → σf v = (fStepIC CM.hm rd lo hv D σ it).2 v)
    (hob : IOblC CM.hm C rd lo D σf it) {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsListB CM.sem C rd σf it.stmts next kret := by
  cases it with
  | atom a =>
    have h := fStep_holds rd hok (fun v hv' => hag v (fOk1_vars hok v hv')) hob
    exact (holdsListB_iff_of_noBlake (fOk1_noBlake hok) next kret).mpr ⟨h, hn⟩
  | fs s0 s1 cur j b =>
    have hv' := fOkI1_vars hok
    have hok' := hok
    simp only [fOkI1, Bool.and_eq_true, decide_eq_true_eq] at hok'
    have hrd : ∀ v ∈ [s0, s1, cur], σf v = σ v := fun v hm => by
      rw [hag v (hv' v (List.mem_append_left _ hm))]
      exact updMany_of_not_mem σ _ _ (not_mem_sets hok'.1.2 (List.all_eq_true.mp hok'.1.1 v hm))
    have hl : (FItem.fs s0 s1 cur j b).sets.length =
        ((FItem.fs s0 s1 cur j b).valsC CM.hm rd hv σ).length := by
      simp [FItem.sets, FItem.valsC]
    have hset := fun i (hi : i < 15) =>
      (hag _ (hv' _ (List.mem_append_right _ (List.getElem_mem (by simp [FItem.sets]; exact hi))))).trans
        (sets_getC hok hl _ rfl i (by simp [FItem.sets]; exact hi))
    obtain ⟨o1, o2, cv, o3, o4⟩ := hob
    rw [hrd cur (by simp)] at o1 o2 o4
    rw [hrd s0 (by simp), hrd s1 (by simp)] at o3
    have hdec : decodeCv (σ s0) (σ s1) = cv :=
      digestScalars_injective ((decodeCv_spec ⟨cv, o3⟩).symm.trans o3)
    have e0 := hset 0 (by omega)
    simp only [FItem.sets, FItem.valsC, List.getElem_map, List.getElem_range,
      List.getElem_cons_zero, Nat.add_zero] at e0
    rw [FItem.stmts]
    refine holdsB_fsNextT_comp s0 s1 cur j b ⟨⟨by rw [hrd cur (by simp), e0]; exact loadHolds_memAt o1 o2,
      cv, obsCvT CM.hm cv (memAt rd (σ cur) j), ?_, by rw [e0]; exact o4, fun k hk1 hk2 => ?_⟩, hn⟩
    · rw [hrd s0 (by simp), hrd s1 (by simp)]; exact o3
    · have e := hset (k + 1) (by omega)
      simp only [FItem.sets, FItem.valsC, List.getElem_map, List.getElem_range,
        List.getElem_cons_succ] at e
      rw [show b + 1 + k = b + (k + 1) by ring, e, e0, hdec]
  | sq s0 s1 b =>
    have hv' := fOkI1_vars hok
    have hok' := hok
    simp only [fOkI1, Bool.and_eq_true, decide_eq_true_eq] at hok'
    have hrd : ∀ v ∈ [s0, s1], σf v = σ v := fun v hm => by
      rw [hag v (hv' v (List.mem_append_left _ hm))]
      exact updMany_of_not_mem σ _ _ (not_mem_sets hok'.1.2 (List.all_eq_true.mp hok'.1.1 v hm))
    have hl : (FItem.sq s0 s1 b).sets.length = ((FItem.sq s0 s1 b).valsC CM.hm rd hv σ).length := by
      simp [FItem.sets, FItem.valsC]
    obtain ⟨cv, o3, o4⟩ := hob
    rw [hrd s0 (by simp), hrd s1 (by simp)] at o3
    have hdec : decodeCv (σ s0) (σ s1) = cv :=
      digestScalars_injective ((decodeCv_spec ⟨cv, o3⟩).symm.trans o3)
    rw [FItem.stmts]
    refine holdsB_squeezeT_comp s0 s1 b ⟨⟨cv, sqCvT CM.hm cv, ?_, o4, fun k hk => ?_⟩, hn⟩
    · rw [hrd s0 (by simp), hrd s1 (by simp)]; exact o3
    · have := (hag _ (hv' _ (List.mem_append_right _ (List.getElem_mem (by simp [FItem.sets]; exact hk))))).trans
        (sets_getC hok hl _ rfl k (by simp [FItem.sets]; exact hk))
      simp only [FItem.sets, FItem.valsC, List.getElem_map, List.getElem_range] at this
      rw [this, hdec]
  | callIf c f args => exact ⟨hob.1, hob.2, hn⟩
  | disp x fns args rets => exact ⟨hob, hn⟩
  | hint h => exact ⟨trivial, hn⟩

theorem holdsListB_flatMapI {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val}
    {kret : List E → Prop} : ∀ (its : List FItem) {next : Prop},
      (∀ it ∈ its, ∀ {next' : Prop}, next' → Stmt.HoldsListB S C rd σ it.stmts next' kret) → next →
      Stmt.HoldsListB S C rd σ (its.flatMap FItem.stmts) next kret
  | [], _, _, hn => hn
  | it :: its, _, h, hn => by
    rw [List.flatMap_cons, holdsListB_append]
    exact h it (List.mem_cons_self ..)
      (holdsListB_flatMapI its (fun i hi => h i (List.mem_cons_of_mem _ hi)) hn)

/-- **A body's items hold over a completeness model** once its obligations do (`fRunI_holds`). -/
theorem fRunIC_holds {CM : CompModel} {C : CallRel} (rd : Reader) {lo hi : ℕ} (hv : ℕ → E)
    (σf : Val) : ∀ (its : List FItem) (D : List ℕ) (σ : Val), fOkI lo hi D its = true →
      (∀ v, fRunIC CM.hm rd lo hv D σ its v = σf v) → IOblsC CM.hm C rd lo σf D its →
      ∀ it ∈ its, ∀ (next : Prop) (kret : List E → Prop), next →
        Stmt.HoldsListB CM.sem C rd σf it.stmts next kret
  | [], _, _, _, _, _, it, hit => absurd hit (by simp)
  | b :: its, D, σ, hok, hf, hob, it, hit => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunIC] at hf
    obtain ⟨hob1, hob2⟩ := hob
    rcases List.mem_cons.mp hit with rfl | hit
    · intro next kret hn
      refine fStepIC_holds (σ := σ) rd hv hok.1 (fun v hv' => ?_) hob1 hn
      rw [← hf v, fRunIC_frame rd hv its _ _ (by rw [fStepIC_fst]; exact hok.2)
        (by rw [fStepIC_fst]; exact hv')]
    · rw [fStepIC_fst] at hf
      exact fRunIC_holds rd hv σf its _ _ hok.2 hf hob2 it hit

/-- **A body of items completes forward over a completeness model** (`completes_items`), its
values set by `fRunIC`, once its obligations hold there. -/
theorem completes_itemsC {CM : CompModel} {C : CallRel} {rd : Reader} {lo hi : ℕ} (hv : ℕ → E)
    (its : List FItem) (hok : fOkI lo hi [] its = true) (σ : Val)
    (hob : IOblsC CM.hm C rd lo (fRunIC CM.hm rd lo hv [] σ its) [] its) :
    CompletesB CM.sem C rd lo hi (its.flatMap FItem.stmts) σ
      (fun σ' => σ' = fRunIC CM.hm rd lo hv [] σ its) :=
  ⟨_, fRunIC_ext rd hv hok, rfl, fun _ _ hn =>
    holdsListB_flatMapI its (fun it hit _ hn' =>
      fRunIC_holds rd hv _ its [] σ hok (fun _ => rfl) hob it hit _ _ hn') hn⟩

theorem IOblC_of_obs {M : HashModel} {C : CallRel} {rd : Reader} {lo : ℕ} {D : List ℕ} {σf : Val}
    {it : FItem} (h : ∀ o ∈ iObs1 lo D it, o.HoldsC M C rd σf) : IOblC M C rd lo D σf it := by
  cases it with
  | atom a => exact fObl1_of_obs fun o ho => h (.ob o) (List.mem_map_of_mem ho)
  | fs s0 s1 cur j b => exact h _ (List.mem_singleton_self _)
  | sq s0 s1 b => exact h _ (List.mem_singleton_self _)
  | callIf c f args => exact h _ (List.mem_singleton_self _)
  | disp x fns args rets => exact h _ (List.mem_singleton_self _)
  | hint _ => trivial

theorem IOblsC_of_obs {M : HashModel} {C : CallRel} {rd : Reader} {lo : ℕ} {σf : Val} :
    ∀ (its : List FItem) (D : List ℕ), (∀ o ∈ iObs lo D its, o.HoldsC M C rd σf) →
      IOblsC M C rd lo σf D its
  | [], _, _ => trivial
  | _ :: its, _, h => ⟨IOblC_of_obs fun o ho => h o (List.mem_append_left _ ho),
      IOblsC_of_obs its _ fun o ho => h o (List.mem_append_right _ ho)⟩

/-! ## What a body defines -/

section
variable {M : HashModel}

theorem fRunIC_eq_of_def (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) {its : List FItem} {D : List ℕ}
    {σ : Val} {σf : Val} (hok : fOkI lo hi D its = true)
    (hf : ∀ v, fRunIC M rd lo hv D σ its v = σf v) {v : V} (h : fDef lo D v = true) :
    σf v = σ v := by
  rw [← hf v, fRunIC_frame rd hv its D σ hok h]

theorem FItem.valsC_congr (rd : Reader) (hv : ℕ → E) {σ σ' : Val} (it : FItem)
    (h : ∀ v ∈ it.reads, σ' v = σ v) : it.valsC M rd hv σ' = it.valsC M rd hv σ := by
  cases it with
  | fs s0 s1 cur j b =>
    simp only [FItem.reads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h
    simp only [FItem.valsC, h.1, h.2.1, h.2.2]
  | sq s0 s1 b =>
    simp only [FItem.reads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h
    simp only [FItem.valsC, h.1, h.2]
  | _ => rfl

theorem FItem.valsC_length (rd : Reader) (hv : ℕ → E) (σ : Val) (it : FItem) :
    (it.valsC M rd hv σ).length = it.sets.length := by
  cases it <;> simp [FItem.valsC, FItem.sets]

theorem fStepIC_nonatom (rd : Reader) (lo : ℕ) (hv : ℕ → E) (D : List ℕ) (σ : Val) {it : FItem}
    (h : it.isAtom = false) :
    fStepIC M rd lo hv D σ it = (fAddMany D it.sets, updMany σ it.sets (it.valsC M rd hv σ)) := by
  cases it <;> simp_all [FItem.isAtom, fStepIC]

/-- **An item's values are its own**, at the final valuation (`fRunI_sets`). -/
theorem fRunIC_sets (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) (σf : Val) : ∀ (its : List FItem)
    (D : List ℕ) (σ : Val), fOkI lo hi D its = true → (∀ v, fRunIC M rd lo hv D σ its v = σf v) →
      ∀ it ∈ fSetItems its, ∀ (i : ℕ) (hi : i < it.sets.length)
        (hj : i < (it.valsC M rd hv σf).length), σf it.sets[i] = (it.valsC M rd hv σf)[i]
  | [], _, _, _, _, it, hit => absurd hit (by simp [fSetItems])
  | b :: its, D, σ, hok, hf, it, hit => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunIC] at hf
    rw [fStepIC_fst] at hf
    rw [fSetItems_cons, List.mem_append] at hit
    rcases hit with hit | hit
    · cases hb : b.isAtom
      · rw [hb] at hit
        simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hit
        subst hit
        intro i hi hj
        have hfr := fun v (hv' : fDef lo (fDStepI lo D it) v = true) =>
          (hf v).symm.trans (fRunIC_frame rd hv its _ _ hok.2 hv')
        have hvars := fOkI1_vars hok.1
        have hok1 := hok.1
        have hn : it.isAtom = false := hb
        cases it with
        | atom a => simp [FItem.isAtom] at hn
        | _ =>
          simp only [fOkI1, Bool.and_eq_true, decide_eq_true_eq] at hok1
          have hrd : ∀ v ∈ FItem.reads _, σf v = σ v := fun v hm => by
            rw [hfr v (hvars v (List.mem_append_left _ hm)), fStepIC_nonatom rd lo hv D σ hn]
            exact updMany_of_not_mem σ _ _
              (not_mem_sets hok1.1.2 (List.all_eq_true.mp hok1.1.1 v hm))
          rw [hfr _ (hvars _ (List.mem_append_right _ (List.getElem_mem hi))),
            fStepIC_nonatom rd lo hv D σ hn]
          dsimp only
          rw [updMany_get σ _ _ hok1.2 (FItem.valsC_length rd hv σ _).symm i hi]
          simp only [FItem.valsC_congr rd hv _ hrd]
      · rw [hb] at hit; exact absurd hit (by simp)
    · exact fRunIC_sets rd hv σf its _ _ hok.2 hf it hit

end

/-- What a definition says of the final valuation, its items' values at the total hash
(`FEq.Holds`). -/
def FEq.HoldsC (M : HashModel) (rd : Reader) (hv : ℕ → E) (σf : Val) : FEq → Prop
  | .item it => ∀ (i : ℕ) (hi : i < it.sets.length) (hj : i < (it.valsC M rd hv σf).length),
      σf it.sets[i] = (it.valsC M rd hv σf)[i]
  | e => e.Holds rd hv σf

theorem fEqs1_holdsC {M : HashModel} {rd : Reader} {hv : ℕ → E} {σf : Val} {lo : ℕ}
    {D : List ℕ} {a : Atom} {e : FEq} (he : e ∈ fEqs1 lo D a) (h : e.Holds rd hv σf) :
    e.HoldsC M rd hv σf := by
  cases e with
  | item it =>
    exfalso
    cases a <;> simp only [fEqs1] at he <;> (try split_ifs at he) <;> simp_all
  | _ => exact h

/-- **Every definition of a body holds** of its final valuation, its items' at the total hash
(`fRunI_eqs`). -/
theorem fRunIC_eqs {M : HashModel} (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) (σf : Val) :
    ∀ (its : List FItem) (D : List ℕ) (σ : Val), fOkI lo hi D its = true →
      (∀ v, fRunIC M rd lo hv D σ its v = σf v) → ∀ e ∈ fEqs lo D its, e.HoldsC M rd hv σf
  | [], _, _, _, _, e, he => absurd he (by simp [fEqs])
  | .atom b :: its, D, σ, hok, hf, e, he => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunIC] at hf
    rw [fStepIC_fst] at hf
    simp only [fEqs, List.mem_append] at he
    rcases he with he | he
    · refine fEqs1_holdsC he (fStep_eqs (σ := σ) rd hok.1 (fun v hv' => ?_) hv e he)
      rw [← hf v]
      exact fRunIC_frame rd hv its _ _ hok.2 (fOk1_vars hok.1 v hv')
    · exact fRunIC_eqs rd hv σf its _ _ hok.2 hf e he
  | .fs s0 s1 cur j b :: its, D, σ, hok, hf, e, he
  | .sq s0 s1 b :: its, D, σ, hok, hf, e, he
  | .callIf s0 j cur :: its, D, σ, hok, hf, e, he
  | .disp s0 j cur s1 :: its, D, σ, hok, hf, e, he
  | .hint s0 :: its, D, σ, hok, hf, e, he => by
    have hall := fRunIC_sets rd hv σf (_ :: its) D σ (by simpa using hok) (by simpa using hf)
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunIC] at hf
    rw [fStepIC_fst] at hf
    simp only [fEqs, List.mem_cons] at he
    rcases he with rfl | he
    · exact hall _ (by simp [fSetItems])
    · exact fRunIC_eqs rd hv σf its _ _ hok.2 hf e he

end
end LeanVM.Guest.B1.VerifySub
