/-
  LeanVM.Protocol.Rpm.RpmRelabel

  The random-permutation experiment of `LeanVM/Spec/Rpm.lean`, on lane states, is the real world
  of `lean_rpm`'s transfer game, on byte states.
-/

import LeanVM.Protocol.Rpm.Game
import LeanRpm.Keccak

/-!
# The experiment on lanes is the real world on bytes

A uniformly random permutation of the lane states, read on bytes through `stateEquiv`, is a
uniformly random permutation of the byte states: the lazily sampled permutation on lanes
(`LeanRpm.lazyPerm` at `KState`) is the one on bytes (at `LeanRpm.KState`) with its edges read
on lanes (`lazyPerm_relabel`), a fresh answer being uniform among the unused points on either side
(`uniformAvoiding_map`). With Keccak-256 over the permutation on lanes being `lean_rpm`'s sponge
over it (`keccak256With_rpm`), the experiment `rpmExperiment` (`LeanVM/Spec/Rpm.lean`) is the real
world `LeanRpm.realGame2` of the transfer game `game` (`rpmExperiment_evalDistEq`), and so is the
completeness experiment (`rpmCompleteness_evalDistEq`).
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

/-! ## A fresh answer through a bijection -/

section Avoiding

variable {S₁ S₂ : Type} [Fintype S₁] [DecidableEq S₁] [SampleableType S₁]
  [Fintype S₂] [DecidableEq S₂] [SampleableType S₂]

omit [Fintype S₁] [DecidableEq S₁] [SampleableType S₁] [Fintype S₂] [DecidableEq S₂]
  [SampleableType S₂] in
theorem mem_map_equiv (e : S₁ ≃ S₂) (l : List S₁) (y : S₂) : y ∈ l.map e ↔ e.symm y ∈ l := by
  constructor
  · rintro hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    simpa using ha
  · intro hm
    exact List.mem_map.mpr ⟨e.symm y, hm, by simp⟩

/-- **A uniform draw avoiding a list, through a bijection**, is a uniform draw avoiding the
list's image. -/
theorem uniformAvoiding_map (e : S₁ ≃ S₂) (l : List S₁) :
    e <$> LeanRpm.uniformAvoiding l =ᵈ LeanRpm.uniformAvoiding (l.map e) := by
  by_cases h : ∃ y, y ∉ l
  · have h' : ∃ y, y ∉ l.map e := by
      obtain ⟨y, hy⟩ := h
      exact ⟨e y, fun hm ↦ hy (by simpa using hm)⟩
    have hcard : (Finset.univ.filter fun y ↦ y ∉ l.map e).card =
        (Finset.univ.filter fun y ↦ y ∉ l).card := by
      refine Finset.card_bij (fun y _ ↦ e.symm y) (fun y hy ↦ ?_) (fun _ _ _ _ h ↦ by simpa using h)
        (fun y hy ↦ ⟨e y, ?_, by simp⟩)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact fun hm ↦ hy (by simpa using List.mem_map_of_mem (f := e) hm)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        simpa using hy
    refine evalDistEq_iff_forall_prEvent_eq_output.mpr fun y ↦ ?_
    rw [prEvent_map]
    have e1 := LeanRpm.prEvent_uniformAvoiding h (fun x ↦ e x = y)
    have e2 := LeanRpm.prEvent_uniformAvoiding h' (fun x ↦ x = y)
    rw [e1, e2, hcard]
    congr 2
    by_cases hy : y ∈ l.map e
    · have hy' : e.symm y ∈ l := (mem_map_equiv e l y).mp hy
      rw [Finset.card_eq_zero.mpr, Finset.card_eq_zero.mpr] <;>
        refine Finset.eq_empty_of_forall_notMem fun x hx ↦ ?_ <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      · exact hx.1 (hx.2 ▸ hy)
      · exact hx.1 (by rw [← e.symm_apply_apply x, hx.2]; exact hy')
    · have hy' : e.symm y ∉ l := fun hm ↦ hy ((mem_map_equiv e l y).mpr hm)
      rw [Finset.card_eq_one.mpr ⟨y, ?_⟩, Finset.card_eq_one.mpr ⟨e.symm y, ?_⟩]
      · ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨-, rfl⟩; simp
        · rintro rfl; exact ⟨hy', by simp⟩
      · ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨-, rfl⟩; rfl
        · rintro rfl; exact ⟨hy, rfl⟩
  · have h' : ¬ ∃ y, y ∉ l.map e := by
      rintro ⟨y, hy⟩
      exact h ⟨e.symm y, fun hm ↦ hy (by simpa using List.mem_map_of_mem (f := e) hm)⟩
    simp only [LeanRpm.uniformAvoiding, h, h', ↓reduceDIte]
    exact SampleableType.map_uniformSample_evalDistEq_of_bijective e.bijective

end Avoiding

/-! ## The lazily sampled permutation through a bijection -/

section Perm

variable {S₁ S₂ : Type} [Fintype S₁] [DecidableEq S₁] [SampleableType S₁]
  [Fintype S₂] [DecidableEq S₂] [SampleableType S₂]

/-- The edges of a log, read through `f`. -/
def logMap (f : S₂ → S₁) (E : LeanRpm.PermLog S₂) : LeanRpm.PermLog S₁ :=
  E.map fun p ↦ (f p.1, f p.2)

/-- A query read through `e`. -/
def mapQ (e : S₁ ≃ S₂) : LeanRpm.PermQuery S₁ → LeanRpm.PermQuery S₂
  | .fwd x => .fwd (e x)
  | .inv y => .inv (e y)

omit [Fintype S₁] [SampleableType S₁] [Fintype S₂] [SampleableType S₂] in
theorem fwdLookup_logMap (e : S₁ ≃ S₂) (E : LeanRpm.PermLog S₂) (x : S₁) :
    LeanRpm.fwdLookup (logMap e.symm E) x = (LeanRpm.fwdLookup E (e x)).map e.symm := by
  induction E with
  | nil => rfl
  | cons p E ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : a = e x
    · subst h; simp [logMap, LeanRpm.fwdLookup]
    · have h' : ¬ e.symm a = x := fun h' ↦ h (by rw [← h']; simp)
      simp only [logMap, List.map_cons, LeanRpm.fwdLookup, h, h', ↓reduceIte] at ih ⊢
      exact ih

omit [Fintype S₁] [SampleableType S₁] [Fintype S₂] [SampleableType S₂] in
theorem invLookup_logMap (e : S₁ ≃ S₂) (E : LeanRpm.PermLog S₂) (y : S₁) :
    LeanRpm.invLookup (logMap e.symm E) y = (LeanRpm.invLookup E (e y)).map e.symm := by
  induction E with
  | nil => rfl
  | cons p E ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : b = e y
    · subst h; simp [logMap, LeanRpm.invLookup]
    · have h' : ¬ e.symm b = y := fun h' ↦ h (by rw [← h']; simp)
      simp only [logMap, List.map_cons, LeanRpm.invLookup, h, h', ↓reduceIte] at ih ⊢
      exact ih

/-- **The lazily sampled permutation through a bijection**: a query read through `e` against the
permutation on `S₂`, its answer and edges read back, is the query against the permutation on
`S₁` with the edges read back. -/
theorem lazyPerm_relabel (e : S₁ ≃ S₂) (q : LeanRpm.PermQuery S₁) (E : LeanRpm.PermLog S₂) :
    Prod.map e.symm (logMap e.symm) <$> (LeanRpm.lazyPerm (mapQ e q)).run E =ᵈ
      (LeanRpm.lazyPerm q).run (logMap e.symm E) := by
  cases q with
  | fwd x =>
    simp only [mapQ, LeanRpm.lazyPerm, StateT.run_mk, fwdLookup_logMap]
    rcases h : LeanRpm.fwdLookup E (e x) with _ | y
    · simp only [Option.map_none, Functor.map_map]
      have hl : (logMap e.symm E).map Prod.snd = (E.map Prod.snd).map e.symm := by
        simp [logMap, Function.comp_def]
      rw [hl]
      refine EvalDistEq.trans ?_ ((uniformAvoiding_map e.symm _).map
        fun y ↦ (y, (x, y) :: logMap e.symm E))
      rw [Functor.map_map]
      simp [logMap]
    · simp
  | inv y =>
    simp only [mapQ, LeanRpm.lazyPerm, StateT.run_mk, invLookup_logMap]
    rcases h : LeanRpm.invLookup E (e y) with _ | x
    · simp only [Option.map_none, Functor.map_map]
      have hl : (logMap e.symm E).map Prod.fst = (E.map Prod.fst).map e.symm := by
        simp [logMap, Function.comp_def]
      rw [hl]
      refine EvalDistEq.trans ?_ ((uniformAvoiding_map e.symm _).map
        fun x ↦ (x, (x, y) :: logMap e.symm E))
      rw [Functor.map_map]
      simp [logMap]
    · simp

end Perm

/-! ## The real world of the game -/

/-- The real world of `lean_rpm`'s two-oracle model: `H` the sponge over the lazily sampled
permutation, `π`, `π⁻¹` and `F = π` the permutation. -/
noncomputable abbrev RR : QueryImpl D2Spec (StateT (LeanRpm.PermLog LeanRpm.KState) ProbComp) :=
  LeanRpm.realImpl LeanRpm.keccakPadding LeanRpm.KState.zero ∘ₛ LeanRpm.toOne

/-- The edges of a byte log, read on lanes. -/
abbrev projLog : LeanRpm.PermLog LeanRpm.KState → PermLog := logMap stateEquiv.symm

theorem RR_advEmbed_perm (q : LeanRpm.PermQuery LeanRpm.KState) :
    (RR ∘ₛ LeanRpm.advEmbed) (.inr (.inr q)) = LeanRpm.lazyPerm q := by
  simp [LeanRpm.advEmbed, LeanRpm.toOne, LeanRpm.realImpl]

theorem hq_eq {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
    [∀ t : hs.Domain, SampleableType (hs.Range t)] (t : ι) :
    LeanRpm.hq (hs := hs) t = (liftM ((unifSpec + hs).query (.inr t)) : OracleComp _ _) := rfl

theorem RR_hfEmbed_toRHF_F (x : KState) :
    (RR ∘ₛ LeanRpm.hfEmbed ∘ₛ toRHF) (.inr x) =
      KState.ofRpm <$> LeanRpm.lazyPerm (.fwd (KState.toRpm x)) := by
  simp [toRHF, hq_eq, LeanRpm.hfEmbed, LeanRpm.toOne, LeanRpm.realImpl]

theorem RR_hfEmbed_toRHF_H (m : Bytes) :
    (RR ∘ₛ LeanRpm.hfEmbed ∘ₛ toRHF) (.inl m) =
      Digest.ofRpm <$> LeanRpm.spongeWith LeanRpm.keccakPadding LeanRpm.KState.zero
        (fun x ↦ LeanRpm.lazyPerm (.fwd x)) m := by
  simp [toRHF, hq_eq, LeanRpm.hfEmbed, LeanRpm.toOne, LeanRpm.realImpl]

/-! ## Stateful computations related through a projection of the state -/

section StRel

variable {σ₁ σ₂ α β : Type}

/-- Two stateful computations related through a projection of their states: run from any state
and its projection, they agree in distribution, the first's final state projected. -/
def StRel (proj : σ₁ → σ₂) (m₁ : StateT σ₁ ProbComp α) (m₂ : StateT σ₂ ProbComp α) : Prop :=
  ∀ s, Prod.map id proj <$> m₁.run s =ᵈ m₂.run (proj s)

theorem StRel.pure (proj : σ₁ → σ₂) (a : α) :
    StRel proj (pure a : StateT σ₁ ProbComp α) (pure a) := fun s ↦ by
  simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  exact EvalDistEq.rfl

theorem StRel.bind {proj : σ₁ → σ₂} {m₁ : StateT σ₁ ProbComp α} {m₂ : StateT σ₂ ProbComp α}
    {k₁ : α → StateT σ₁ ProbComp β} {k₂ : α → StateT σ₂ ProbComp β} (h : StRel proj m₁ m₂)
    (hk : ∀ a, StRel proj (k₁ a) (k₂ a)) : StRel proj (m₁ >>= k₁) (m₂ >>= k₂) := fun s ↦ by
  simp only [StateT.run_bind, map_bind]
  calc (m₁.run s >>= fun z ↦ Prod.map id proj <$> (k₁ z.1).run z.2)
      =ᵈ (m₁.run s >>= fun z ↦ (k₂ z.1).run (proj z.2)) :=
        EvalDistEq.bind_right _ fun z ↦ hk z.1 z.2
    _ = ((Prod.map id proj <$> m₁.run s) >>= fun z ↦ (k₂ z.1).run z.2) := by
        rw [bind_map_left]; rfl
    _ =ᵈ (m₂.run (proj s) >>= fun z ↦ (k₂ z.1).run z.2) := EvalDistEq.bind_left (h s) _

theorem StRel.map {proj : σ₁ → σ₂} {m₁ : StateT σ₁ ProbComp α} {m₂ : StateT σ₂ ProbComp α}
    (h : StRel proj m₁ m₂) (f : α → β) : StRel proj (f <$> m₁) (f <$> m₂) := fun s ↦ by
  simp only [StateT.run_map, Functor.map_map]
  have := (h s).map (Prod.map f id)
  simp only [Functor.map_map] at this
  exact this

theorem absorbAll_rel {proj : σ₁ → σ₂} (π₁ : LeanRpm.KState → StateT σ₁ ProbComp LeanRpm.KState)
    (π₂ : LeanRpm.KState → StateT σ₂ ProbComp LeanRpm.KState) (h : ∀ x, StRel proj (π₁ x) (π₂ x)) :
    ∀ (st : LeanRpm.KState) (bs : List LeanRpm.KBlock),
      StRel proj (LeanRpm.absorbAll π₁ st bs) (LeanRpm.absorbAll π₂ st bs)
  | st, [] => StRel.pure proj st
  | st, B :: bs => by
    rw [LeanRpm.absorbAll_cons, LeanRpm.absorbAll_cons]
    exact StRel.bind (h _) fun y ↦ absorbAll_rel π₁ π₂ h y bs

end StRel

/-! ## The verifier's queries -/

/-- `π` on lanes is the lane reading of `π` on bytes. -/
theorem perm_eq_lanePerm :
    (perm : KState → StateT PermLog ProbComp KState) =
      lanePerm (fun x ↦ KState.toRpm <$> perm (KState.ofRpm x)) := by
  funext s
  simp only [lanePerm, Functor.map_map, ofRpm_toRpm, id_map']

/-- A forward query on bytes is the forward query on lanes, read on bytes. -/
theorem lazyPerm_fwd_rel (x : LeanRpm.KState) :
    StRel projLog (LeanRpm.lazyPerm (.fwd x)) (KState.toRpm <$> perm (KState.ofRpm x)) := by
  intro s
  have h := (lazyPerm_relabel stateEquiv (.fwd (KState.ofRpm x)) s).map (Prod.map KState.toRpm id)
  simp only [mapQ, stateEquiv_apply, Functor.map_map] at h
  rw [toRpm_ofRpm] at h
  have e : (fun a ↦ Prod.map KState.toRpm id (Prod.map (⇑stateEquiv.symm)
      (logMap ⇑stateEquiv.symm) a)) = Prod.map id projLog := by
    funext p
    obtain ⟨a, b⟩ := p
    simp only [Prod.map_apply, stateEquiv_symm_apply, toRpm_ofRpm, id_eq]
  rw [e] at h
  rw [perm, StateT.run_map]
  exact h

/-- **The verifier's queries on bytes in the real world are the verifier's queries in the
random-permutation experiment**, the permutation's edges read on lanes. -/
theorem post_relabel {β : Type} (X : OracleComp HashSpec β) (s : LeanRpm.PermLog LeanRpm.KState) :
    Prod.map id projLog <$> (simulateQ (RR ∘ₛ LeanRpm.hfEmbed ∘ₛ toRHF) X).run s =ᵈ
      (simulateQ rpmImpl X).run (projLog s) := by
  refine LeanRpm.map_run_simulateQ_evalDistEq_of_inv _ _ (fun _ ↦ True) projLog
    (fun _ _ _ _ _ ↦ trivial) (fun t s' _ ↦ ?_) X s trivial
  rcases t with m | x
  · rw [RR_hfEmbed_toRHF_H]
    change _ =ᵈ (keccak256With perm m).run _
    rw [perm_eq_lanePerm, keccak256With_rpm]
    exact (StRel.map (absorbAll_rel _ _ lazyPerm_fwd_rel _ _) _).map _ s'
  · rw [RR_hfEmbed_toRHF_F]
    change _ =ᵈ (LeanRpm.lazyPerm (.fwd x)).run _
    have h := lazyPerm_relabel stateEquiv (.fwd x) s'
    simp only [mapQ, stateEquiv_apply] at h
    rw [StateT.run_map, Functor.map_map]
    exact h

/-! ## The adversary -/

/-- **The adversary on bytes with its transcript, in the real world, is the adversary of the
random-permutation experiment**, the permutation's edges read on lanes. -/
theorem adv_relabel {α : Type} (A : OracleComp PermSpec α) (s : LeanRpm.PermLog LeanRpm.KState)
    (T : Transcript) :
    (fun p ↦ (p.1.1, (projLog p.2, p.1.2))) <$>
        (simulateQ (RR ∘ₛ LeanRpm.advEmbed) ((simulateQ logRel A).run T)).run s =ᵈ
      (simulateQ loggedPerm A).run (projLog s, T) := by
  induction A using OracleComp.inductionOn generalizing s T with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact EvalDistEq.rfl
  | query_bind q k ih =>
    have hq : mapQ stateEquiv q = permQueryToRpm q := by cases q <;> rfl
    have hrel : simulateQ (RR ∘ₛ LeanRpm.advEmbed) (relP q) =
        KState.ofRpm <$> LeanRpm.lazyPerm (permQueryToRpm q) := by
      rw [relP, simulateQ_map, simulateQ_spec_query, RR_advEmbed_perm]
    simp only [StateT.run_bind, simulateQ_bind, simulateQ_spec_query, logRel, loggedPerm,
      StateT.run_mk, hrel, bind_map_left, map_bind]
    calc _ =ᵈ ((LeanRpm.lazyPerm (permQueryToRpm q)).run s >>= fun a ↦
            (simulateQ loggedPerm (k (KState.ofRpm a.1))).run
              (projLog a.2, T ++ [(q, KState.ofRpm a.1)])) :=
          EvalDistEq.bind_right _ fun a ↦ ih _ _ _
      _ = ((Prod.map KState.ofRpm projLog <$> (LeanRpm.lazyPerm (permQueryToRpm q)).run s) >>=
            fun a ↦ (simulateQ loggedPerm (k a.1)).run (a.2, T ++ [(q, a.1)])) := by
          rw [bind_map_left]; rfl
      _ =ᵈ _ := EvalDistEq.bind_left (by rw [← hq]; exact lazyPerm_relabel stateEquiv q s) _

/-! ## The experiments -/

theorem post_relabel' {β : Type} (X : OracleComp HashSpec β) (s : LeanRpm.PermLog LeanRpm.KState) :
    (simulateQ (RR ∘ₛ LeanRpm.hfEmbed ∘ₛ toRHF) X).run' s =ᵈ
      (simulateQ rpmImpl X).run' (projLog s) := by
  have h := (post_relabel X s).map Prod.fst
  simp only [Functor.map_map] at h
  simpa [StateT.run'_eq] using h

theorem realGame2_eq {δ : Type} (D : OracleComp D2Spec δ) :
    LeanRpm.realGame2 LeanRpm.keccakPadding LeanRpm.KState.zero D = (simulateQ RR D).run' [] := by
  rw [LeanRpm.realGame2, LeanRpm.realGame, QueryImpl.simulateQ_compose]

/-- **The random-permutation experiment is the real world of the transfer game.** -/
theorem rpmExperiment_evalDistEq (A : RpmAdversary) :
    rpmExperiment A =ᵈ LeanRpm.realGame2 LeanRpm.keccakPadding LeanRpm.KState.zero (game A) := by
  rw [realGame2_eq, game, LeanRpm.rpmGame2]
  simp only [simulateQ_pure, pure_bind, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  simp only [postR, simulateQ_map, StateT.run_map, Functor.map_map, RR,
    QueryImpl.simulateQ_compose]
  have hadv := (adv_relabel A [] []).symm
  simp only [projLog, logMap, List.map_nil, QueryImpl.simulateQ_compose] at hadv
  rw [rpmExperiment, advR]
  refine EvalDistEq.trans (EvalDistEq.bind_left hadv _) ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun p ↦ ?_
  have h := (post_relabel' (verifier queryH queryF p.1.1.1.1 p.1.1.1.2 p.1.1.2) p.2).symm.map
    fun v ↦ ((p.1.1, v), p.1.2)
  simp only [StateT.run'_eq, Functor.map_map, QueryImpl.simulateQ_compose, projLog, logMap] at h
  simp only [StateT.run'_eq, bind_pure_comp, Functor.map_map]
  exact h

/-- The completeness game: nothing before, no adversary, then the honest computation with the
hash and the direct permutation calls. -/
def honestGame {β : Type} (X : OracleComp HashSpec β) : OracleComp D2Spec β :=
  LeanRpm.rpmGame2 (pure ()) (fun _ ↦ (pure () : OracleComp RSpec Unit))
    (fun _ _ ↦ simulateQ toRHF X)

/-- **An honest computation in the random-permutation model is the real world of its game.** -/
theorem rpmHonest_evalDistEq {β : Type} (X : OracleComp HashSpec β) :
    (simulateQ rpmImpl X).run' [] =ᵈ
      LeanRpm.realGame2 LeanRpm.keccakPadding LeanRpm.KState.zero (honestGame X) := by
  rw [realGame2_eq, honestGame, LeanRpm.rpmGame2]
  simp only [simulateQ_pure, pure_bind]
  have h := (post_relabel' X []).symm
  simp only [projLog, logMap, List.map_nil] at h
  refine h.trans ?_
  simp only [RR, QueryImpl.simulateQ_compose]
  exact EvalDistEq.rfl

end LeanVM.Rpm
