/-
  LeanVM.Guest.B1.Comp.CompletesB

  `Completes` over any semantics: the completeness of a block under `Stmt.HoldsListB S`, its frame
  lemma, sequencing and one-atom steps; hash-free blocks carried over from `Completes`, and the
  deployed `Completes` recovered at `blakeDeployed`.
-/

module

public import LeanVM.Guest.B1.Sig.Frame
public import LeanVM.Guest.B1.Sig.Model.Hashing
public import LeanVM.Guest.B1.Basic

/-!
# Completeness of a block over a semantics

`Completes C rd lo hi ss σ Post` (`Sig/Frame.lean`) is the deployed completeness of a block: a
valuation changing `σ` only on `lo ..< hi`, satisfying `Post`, under which `ss` holds before any
true continuation. `CompletesB S` is the same under `Stmt.HoldsListB S`, the guest's statements
with the `BLAKE2S` atoms checked by `S` (`Guest/CoreB.lean`).

* `completesB_deployed`: at `blakeDeployed` it is `Completes`.
* `CompletesB.of_free`, `completesB_iff_free`: a block with no `BLAKE2S` atom, calling only
  functions of some `F` (`Stmt.freeInList F`, by `rfl` or `decide`), completes under every
  semantics exactly as under the deployed one, so its deployed `Completes` lemma carries over.
* The frame lemma `holdsListB_frame` and the `Completes` toolkit over `S`: `append`, `mono`,
  `nil`, `of_ext`, `withExt`, `withHolds`, `post`, `atom_cons`, `atom_cons0`, `append_holds`,
  `append_tail`, `append_atom`, `hint_cons`, `flatMap_range`, `flatten`, `completesB_upds`,
  `completesB_setv`, `completesB_hint`.
* `CompletesB.holds`: a function body completing on its fresh values from a valuation of its
  parameters, then a `ret`, gives the function's relation (`relB_of_completesB`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem} {C : CallRel} {rd : Reader}

/-! ## Definition -/

variable (S) in
/-- **Completeness of a block under the semantics `S`** (`Completes`): from `σ`, a valuation
changing only `lo ..< hi` under which the block holds before any true continuation. -/
def CompletesB (C : CallRel) (rd : Reader) (lo hi : Nat) (ss : List Stmt) (σ : Val)
    (Post : Val → Prop) : Prop :=
  ∃ σ', Ext lo hi σ σ' ∧ Post σ' ∧
    ∀ (next : Prop) (kret : List E → Prop), next → Stmt.HoldsListB S C rd σ' ss next kret

/-- **At the deployed semantics**, `CompletesB` is `Completes`. -/
theorem completesB_deployed {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop} :
    CompletesB blakeDeployed C rd lo hi ss σ P ↔ Completes C rd lo hi ss σ P := by
  simp only [CompletesB, Completes, holdsListB_deployed]

theorem CompletesB.of_deployed {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : CompletesB blakeDeployed C rd lo hi ss σ P) : Completes C rd lo hi ss σ P :=
  completesB_deployed.mp h

/-! ## Hash-free blocks -/

/-- A block with no `BLAKE2S` atom, calling only functions of `F`, holds under any semantics
exactly when it holds under the deployed one (`holdsListB_free`, with calls). -/
theorem holdsListB_iff_of_freeIn {F : List String} {ss : List Stmt}
    (hfree : Stmt.freeInList F ss = true) (σ : Val) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ ss next kret ↔ Stmt.HoldsList C rd σ ss next kret := by
  rw [holdsListB_freeIn (S' := blakeDeployed) (C' := C) (fun _ _ _ _ => Iff.rfl) ss hfree,
    holdsListB_deployed]

/-- **A hash-free block completes under every semantics** as it does under the deployed one. -/
theorem completesB_iff_free {F : List String} {lo hi : Nat} {ss : List Stmt} {σ : Val}
    {P : Val → Prop} (hfree : Stmt.freeInList F ss = true) :
    CompletesB S C rd lo hi ss σ P ↔ Completes C rd lo hi ss σ P := by
  simp only [CompletesB, Completes, holdsListB_iff_of_freeIn hfree]

/-- A hash-free block's deployed completeness, under any semantics. -/
theorem CompletesB.of_free {F : List String} {lo hi : Nat} {ss : List Stmt} {σ : Val}
    {P : Val → Prop} (hfree : Stmt.freeInList F ss = true) (h : Completes C rd lo hi ss σ P) :
    CompletesB S C rd lo hi ss σ P :=
  (completesB_iff_free hfree).mpr h

/-! ## The frame lemma -/

theorem atomB_congrV {σ σ' : Val} (a : Atom) (h : ∀ v ∈ a.vals, σ v = σ' v) :
    a.HoldsB S rd σ ↔ a.HoldsB S rd σ' := by
  cases a with
  | frameAddr p run =>
      simp only [Atom.vals, List.mem_cons] at h
      simp only [Atom.HoldsB]
      rw [h p (Or.inl rfl)]
      refine and_congr_right fun _ => forall_congr' fun k => forall_congr' fun hk =>
        forall_congr' fun w => imp_congr_right fun _ => ?_
      rw [h run[k] (Or.inr (List.getElem_mem hk))]
  | hint => simp [Atom.HoldsB]
  | _ => simp only [Atom.vals, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq] at h; simp only [Atom.HoldsB, h]

mutual
theorem holdsB_congrV {σ σ' : Val} : ∀ (s : Stmt), (∀ v ∈ s.vals, σ v = σ' v) →
    ∀ (next : Prop) (kret : List E → Prop),
    (Stmt.HoldsB S C rd σ s next kret ↔ Stmt.HoldsB S C rd σ' s next kret)
  | .atom a, h, _, _ => by simp only [Stmt.HoldsB, atomB_congrV a h]
  | .ite c z n, h, next, kret => by
      simp only [Stmt.vals, List.mem_cons, List.mem_append] at h
      simp only [Stmt.HoldsB]
      rw [h c (Or.inl (Or.inl rfl)),
        holdsListB_congrV z (fun v hv => h v (Or.inl (Or.inr hv))) next kret,
        holdsListB_congrV n (fun v hv => h v (Or.inr hv)) next kret]
  | .match_ x arms, h, next, kret => by
      simp only [Stmt.vals, List.mem_cons] at h
      simp only [Stmt.HoldsB]
      exact holdsArmsB_congrV x arms (h x (Or.inl rfl)) (fun v hv => h v (Or.inr hv)) 0 next kret
  | .call f args rets, h, _, _ => by
      simp only [Stmt.vals, List.mem_append] at h
      simp only [Stmt.HoldsB, map_congr fun v hv => h v (Or.inl hv),
        map_congr fun v hv => h v (Or.inr hv)]
  | .callIf c f args, h, _, _ => by
      simp only [Stmt.vals, List.mem_cons] at h
      simp only [Stmt.HoldsB, h c (Or.inl rfl), map_congr fun v hv => h v (Or.inr hv)]
  | .dispatch x fs args rets, h, _, _ => by
      simp only [Stmt.vals, List.mem_cons, List.mem_append] at h
      simp only [Stmt.HoldsB, h x (Or.inl (Or.inl rfl)),
        map_congr fun v hv => h v (Or.inl (Or.inr hv)), map_congr fun v hv => h v (Or.inr hv)]
  | .ret vs, h, _, _ => by simp only [Stmt.HoldsB, Stmt.vals] at h ⊢; rw [map_congr h]

theorem holdsListB_congrV {σ σ' : Val} : ∀ (ss : List Stmt),
    (∀ v ∈ Stmt.valsList ss, σ v = σ' v) → ∀ (next : Prop) (kret : List E → Prop),
    (Stmt.HoldsListB S C rd σ ss next kret ↔ Stmt.HoldsListB S C rd σ' ss next kret)
  | [], _, _, _ => Iff.rfl
  | s :: ss, h, next, kret => by
      simp only [Stmt.valsList, List.mem_append] at h
      simp only [Stmt.HoldsListB]
      rw [holdsListB_congrV ss (fun v hv => h v (Or.inr hv)) next kret]
      exact holdsB_congrV s (fun v hv => h v (Or.inl hv)) _ kret

theorem holdsArmsB_congrV {σ σ' : Val} (x : V) : ∀ (arms : List (List Stmt)),
    σ x = σ' x → (∀ v ∈ Stmt.valsArms arms, σ v = σ' v) →
    ∀ (j : Nat) (next : Prop) (kret : List E → Prop),
    (Stmt.HoldsArmsB S C rd σ x j arms next kret ↔ Stmt.HoldsArmsB S C rd σ' x j arms next kret)
  | [], _, _, _, _, _ => Iff.rfl
  | a :: as, hx, h, j, next, kret => by
      simp only [Stmt.valsArms, List.mem_append] at h
      simp only [Stmt.HoldsArmsB]
      rw [hx, holdsListB_congrV a (fun v hv => h v (Or.inl hv)) next kret,
        holdsArmsB_congrV x as hx (fun v hv => h v (Or.inr hv)) (j + 1) next kret]
end

/-- **The frame lemma over a semantics** (`holdsList_frame`). -/
theorem holdsListB_frame {hi : Nat} {σ σ' : Val} {ss : List Stmt}
    (hb : NumBelow hi (Stmt.valsList ss)) (hσ : AgreeBelow hi σ σ') (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ ss next kret ↔ Stmt.HoldsListB S C rd σ' ss next kret :=
  holdsListB_congrV ss (fun v hv => let ⟨k, hk, e⟩ := hb v hv; e ▸ hσ k hk) next kret

theorem atomB_frame {hi : Nat} {σ σ' : Val} {a : Atom} (hb : NumBelow hi a.vals)
    (hσ : AgreeBelow hi σ σ') : a.HoldsB S rd σ ↔ a.HoldsB S rd σ' :=
  atomB_congrV a fun v hv => let ⟨k, hk, e⟩ := hb v hv; e ▸ hσ k hk

/-! ## Sequencing -/

/-- Completeness in sequence (`Completes.append`). -/
theorem CompletesB.append {lo m hi : Nat} {xs ys : List Stmt} {σ : Val} {P Q : Val → Prop}
    (hlo : lo ≤ m) (hhi : m ≤ hi) (hxs : NumBelow m (Stmt.valsList xs))
    (h1 : CompletesB S C rd lo m xs σ P)
    (h2 : ∀ σ', Ext lo m σ σ' → P σ' → CompletesB S C rd m hi ys σ' Q) :
    CompletesB S C rd lo hi (xs ++ ys) σ Q := by
  obtain ⟨σ1, he1, hp1, hh1⟩ := h1
  obtain ⟨σ2, he2, hq2, hh2⟩ := h2 σ1 he1 hp1
  refine ⟨σ2, he1.trans he2 hlo hhi, hq2, fun next kret hn => ?_⟩
  rw [holdsListB_append]
  exact (holdsListB_frame hxs he2.agree _ _).mp (hh1 _ kret (hh2 next kret hn))

theorem CompletesB.mono {lo hi lo' hi' : Nat} {ss : List Stmt} {σ : Val} {P Q : Val → Prop}
    (h : CompletesB S C rd lo hi ss σ P) (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (hPQ : ∀ σ', P σ' → Q σ') : CompletesB S C rd lo' hi' ss σ Q :=
  let ⟨σ', he, hp, hh⟩ := h; ⟨σ', he.mono hlo hhi, hPQ σ' hp, hh⟩

theorem CompletesB.nil (lo hi : Nat) (σ : Val) {P : Val → Prop} (hp : P σ) :
    CompletesB S C rd lo hi [] σ P :=
  ⟨σ, Ext.refl _ _ _, hp, fun _ _ hn => hn⟩

/-- `CompletesB` from a valuation already changed on the same range. -/
theorem CompletesB.of_ext {lo hi : Nat} {ss : List Stmt} {σ σ1 : Val} {P : Val → Prop}
    (he : Ext lo hi σ σ1) (h : CompletesB S C rd lo hi ss σ1 P) : CompletesB S C rd lo hi ss σ P :=
  let ⟨σ', he', hp, hh⟩ := h
  ⟨σ', fun v hv => (he' v hv).trans (he v hv), hp, hh⟩

/-- The valuation's change recorded in the postcondition. -/
theorem CompletesB.withExt {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : CompletesB S C rd lo hi ss σ P) :
    CompletesB S C rd lo hi ss σ (fun σ' => P σ' ∧ Ext lo hi σ σ') :=
  let ⟨σ', he, hp, hh⟩ := h; ⟨σ', he, ⟨hp, he⟩, hh⟩

/-- The block's relation recorded in the postcondition. -/
theorem CompletesB.withHolds {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : CompletesB S C rd lo hi ss σ P) : CompletesB S C rd lo hi ss σ (fun σ' => P σ' ∧
      Ext lo hi σ σ' ∧ ∀ (next : Prop) (kret : List E → Prop), next →
        Stmt.HoldsListB S C rd σ' ss next kret) :=
  let ⟨σ', he, hp, hh⟩ := h; ⟨σ', he, ⟨hp, he, hh⟩, hh⟩

theorem CompletesB.post {lo hi : Nat} {ss : List Stmt} {σ : Val} {P Q : Val → Prop}
    (h : CompletesB S C rd lo hi ss σ P) (hpq : ∀ σ', Ext lo hi σ σ' → P σ' → Q σ') :
    CompletesB S C rd lo hi ss σ Q := by
  obtain ⟨σ', he, hp, hh⟩ := h
  exact ⟨σ', he, hpq σ' he hp, hh⟩

/-- A block over values below the range that holds already. -/
theorem CompletesB.append_holds {k hi : Nat} {xs ys : List Stmt} {σ : Val} {P : Val → Prop}
    (hb : NumBelow k (Stmt.valsList xs)) (hx : ∀ (next : Prop) (kret : List E → Prop), next →
      Stmt.HoldsListB S C rd σ xs next kret) (h : CompletesB S C rd k hi ys σ P) :
    CompletesB S C rd k hi (xs ++ ys) σ P := by
  obtain ⟨σ', he, hp, hh⟩ := h
  refine ⟨σ', he, hp, fun next kret hn => ?_⟩
  rw [holdsListB_append]
  exact (holdsListB_frame hb he.agree _ _).mp (hx _ kret (hh next kret hn))

/-- A completing block followed by statements that hold on any valuation it reaches. -/
theorem CompletesB.append_tail {lo hi : Nat} {xs ys : List Stmt} {σ : Val} {P : Val → Prop}
    (h : CompletesB S C rd lo hi xs σ P)
    (hys : ∀ σ', Ext lo hi σ σ' → ∀ (next : Prop) (kret : List E → Prop), next →
      Stmt.HoldsListB S C rd σ' ys next kret) :
    CompletesB S C rd lo hi (xs ++ ys) σ P := by
  obtain ⟨σ', he, hp, hh⟩ := h
  exact ⟨σ', he, hp, fun next kret hn => by rw [holdsListB_append]; exact hh _ _ (hys σ' he next kret hn)⟩

/-- A block completing, then an atom over values it leaves. -/
theorem CompletesB.append_atom {lo hi : Nat} {xs : List Stmt} {a : Atom} {σ : Val}
    {P Q : Val → Prop} (h : CompletesB S C rd lo hi xs σ P)
    (ha : ∀ σ', P σ' → a.HoldsB S rd σ' ∧ Q σ') :
    CompletesB S C rd lo hi (xs ++ [.atom a]) σ Q := by
  obtain ⟨σ', he, hp, hh⟩ := h
  refine ⟨σ', he, (ha σ' hp).2, fun next kret hn => ?_⟩
  rw [holdsListB_append]
  exact hh _ kret ⟨(ha σ' hp).1, hn⟩

/-! ## One atom at a time -/

/-- An atom writing the fresh value `k` (`Completes.atom_cons`). -/
theorem CompletesB.atom_cons {k hi : Nat} {a : Atom} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (e : E) (hk : k + 1 ≤ hi) (hb : NumBelow (k + 1) a.vals)
    (ha : a.HoldsB S rd (Function.update σ (.n k) e))
    (h : CompletesB S C rd (k + 1) hi ss (Function.update σ (.n k) e) P) :
    CompletesB S C rd k hi (.atom a :: ss) σ P := by
  obtain ⟨σ', he, hp, hh⟩ := h
  have hu : Ext k (k + 1) σ (Function.update σ (.n k) e) := fun _ hv =>
    Function.update_of_ne (hv k le_rfl (Nat.lt_succ_self k)) _ _
  refine ⟨σ', hu.trans he (Nat.le_succ k) hk, hp, fun next kret hn => ?_⟩
  rw [holdsListB_cons_atom]
  exact ⟨(atomB_frame hb he.agree).mp ha, hh next kret hn⟩

/-- An atom over values below the range (`Completes.atom_cons0`). -/
theorem CompletesB.atom_cons0 {k hi : Nat} {a : Atom} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (hb : NumBelow k a.vals) (ha : a.HoldsB S rd σ) (h : CompletesB S C rd k hi ss σ P) :
    CompletesB S C rd k hi (.atom a :: ss) σ P := by
  obtain ⟨σ', he, hp, hh⟩ := h
  refine ⟨σ', he, hp, fun next kret hn => ?_⟩
  rw [holdsListB_cons_atom]
  exact ⟨(atomB_frame hb he.agree).mp ha, hh next kret hn⟩

theorem CompletesB.hint_cons {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop} (h : Hint)
    (hc : CompletesB S C rd lo hi ss σ P) : CompletesB S C rd lo hi (.atom (.hint h) :: ss) σ P :=
  let ⟨σ', he, hp, hh⟩ := hc
  ⟨σ', he, hp, fun next kret hn => ⟨trivial, hh next kret hn⟩⟩

/-- A block completes with a valuation updated on its range (`completes_upds`). -/
theorem completesB_upds {lo hi : Nat} {ss : List Stmt} {σ : Val} {Post : Val → Prop}
    (l : List (Nat × E)) (hl : ∀ p ∈ l, lo ≤ p.1 ∧ p.1 < hi)
    (hh : ∀ (next : Prop) (kret : List E → Prop), next →
      Stmt.HoldsListB S C rd (upds σ l) ss next kret)
    (hp : Post (upds σ l)) : CompletesB S C rd lo hi ss σ Post :=
  ⟨upds σ l, upds_ext σ l hl, hp, hh⟩

theorem setv_extB (σ : Val) (b n : Nat) (f : Nat → E) : Ext b (b + n) σ (setv σ b n f) := by
  intro v hv
  unfold setv
  split
  · rename_i h
    exact absurd (by cases v; simp_all) (hv v.idx h.2.2.1 h.2.2.2)
  · rfl

/-- A block completes with a valuation set on its range (`completes_setv`). -/
theorem completesB_setv {lo n : Nat} {ss : List Stmt} {σ : Val} {Post : Val → Prop} (f : Nat → E)
    (hh : ∀ (next : Prop) (kret : List E → Prop), next →
      Stmt.HoldsListB S C rd (setv σ lo n f) ss next kret)
    (hp : Post (setv σ lo n f)) : CompletesB S C rd lo (lo + n) ss σ Post :=
  ⟨setv σ lo n f, setv_extB σ lo n f, hp, hh⟩

/-- One fresh value set by a hint (`completes_hint`). -/
theorem completesB_hint {k : Nat} {h : Hint} {σ : Val} {Post : Val → Prop} (e : E)
    (hp : Post (upds σ [(k, e)])) : CompletesB S C rd k (k + 1) [.atom (.hint h)] σ Post :=
  completesB_upds [(k, e)] (by simp) (fun _ _ hn => ⟨trivial, hn⟩) hp

/-! ## Families of blocks -/

theorem mono_of_succB {st : Nat → Nat} {n : Nat} (hst : ∀ i < n, st i ≤ st (i + 1)) :
    ∀ i j, i ≤ j → j ≤ n → st i ≤ st j := by
  intro i j hij hj
  induction j with
  | zero => rw [show i = 0 by omega]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact le_trans (ih (by omega) (by omega)) (hst j (by omega))

/-- **A family of blocks completes in sequence** (`Completes.flatten`). -/
theorem CompletesB.flatten {blk : Nat → List Stmt} {st : Nat → Nat} {Inv : Nat → Val → Prop} :
    ∀ n, (∀ i < n, st i ≤ st (i + 1)) → (∀ i < n, NumBelow (st (i + 1)) (Stmt.valsList (blk i))) →
    (∀ i < n, ∀ σ, Inv i σ → CompletesB S C rd (st i) (st (i + 1)) (blk i) σ (Inv (i + 1))) →
    ∀ σ, Inv 0 σ → CompletesB S C rd (st 0) (st n) ((List.range n).map blk).flatten σ (Inv n)
  | 0, _, _, _, σ, h0 => CompletesB.nil _ _ σ h0
  | n + 1, hst, hnb, hb, σ, h0 => by
    rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
      List.flatten_singleton]
    have hm := mono_of_succB hst
    refine CompletesB.append (hm 0 n (by omega) (by omega)) (hst n (by omega)) ?_
      (CompletesB.flatten n (fun i hi => hst i (by omega)) (fun i hi => hnb i (by omega))
        (fun i hi => hb i (by omega)) σ h0)
      (fun σ' _ hσ' => hb n (by omega) σ' hσ')
    rw [List.flatten_eq_flatMap, List.flatMap_map]
    refine numBelow_valsList_flatMap _ _ fun i hi => ?_
    have hi' : i < n := by simpa using hi
    exact (hnb i (by omega)).mono (hm (i + 1) n (by omega) (by omega))

/-- Blocks over a range in sequence (`Completes.flatMap_range`). -/
theorem CompletesB.flatMap_range {f : Nat → List Stmt} {base : Nat → Nat} {Inv : Nat → Val → Prop}
    (hbase : ∀ j, base j ≤ base (j + 1)) :
    ∀ (q : Nat), (∀ j < q, NumBelow (base (j + 1)) (Stmt.valsList (f j))) →
      (∀ j < q, ∀ σ, Inv j σ → CompletesB S C rd (base j) (base (j + 1)) (f j) σ (Inv (j + 1))) →
      ∀ σ, Inv 0 σ → CompletesB S C rd (base 0) (base q) ((List.range q).flatMap f) σ (Inv q) := by
  intro q hb h σ h0
  have := CompletesB.flatten (S := S) (C := C) (rd := rd) (blk := f) (st := base) (Inv := Inv) q
    (fun j _ => hbase j) hb h σ h0
  rwa [List.flatten_eq_flatMap, List.flatMap_map] at this

/-! ## Functions -/

/-- **A function body that completes gives the function's relation**: from a valuation of the
parameters, the body `X` completing on its fresh values `lo ..< hi` above them, then `ret`s of
the values its postcondition fixes. -/
theorem relB_of_completesB {P : Core.Program} {f : String} {fn : Fn} (hf : P.find? f = some fn)
    {X : List Stmt} {rv : List V} (hbody : fn.body = X ++ [.ret rv]) {lo hi : Nat} {σ : Val}
    {args rets : List E} (hpar : NumBelow lo fn.params) (hargs : fn.params.map σ = args)
    (h : CompletesB S (P.RelB S rd) rd lo hi X σ (fun σ' => rv.map σ' = rets)) :
    P.RelB S rd f args rets := by
  obtain ⟨σ', he, hr, hh⟩ := h
  refine (relB_iff_sem hf args rets).mpr ⟨σ', ?_, ?_⟩
  · rw [← hargs]
    exact List.map_congr_left fun v hv => (he.agree.apply (hpar v hv))
  · rw [hbody, holdsListB_append]
    exact hh _ _ (by simp only [Stmt.HoldsListB, Stmt.HoldsB]; exact hr)

end
end LeanVM.Guest.B1.Sig
