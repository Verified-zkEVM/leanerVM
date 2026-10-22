/-
  LeanVM.E2E.Vis.PerKey.Agree

  W-vis, P7: agreement of computations with a private cache on their good outputs, in the
  schemes' lazy random oracle. The per-key reductions change a computation only where its output
  is bad (a key coincidence, an abort), and every event they bound forces a good output.
-/

module

public import LeanVM.E2E.Vis.PerKey.Sim

/-!
# Agreement on good outputs (W-vis, P7)

A per-key reduction runs computations of `PM`: the schemes' world with a private cache as state.
Two such computations `x`, `y` **agree on good outputs** (`AgreeOn good x y`) when, whatever runs
after them, every event that forces their output good has the same probability under the schemes'
lazy random oracle, from any pair of caches.

* `agreeOn_bind`: binds that agree where a condition `G` holds of the prefix's output, and give
  only bad outputs where it fails, agree;
* `agreeOn_sequenceFin`: sequences of agreeing computations agree on the outputs good everywhere;
* `prEvent_eq_of_agreeOn`: an event of a continuation that keeps a copy (`key`) of the output
  and forces it good has the same probability after two agreeing computations, the
  continuations agreeing on good outputs.

Agreement is an equivalence (`AgreeOn.refl`, `AgreeOn.symm`, `AgreeOn.trans`), is kept by a
common prefix (`agreeOn_bind_congr`) and by a continuation whose good outputs come from good
outputs (`AgreeOn.bind_comb`, `AgreeOn.bind_pure`), and holds when neither computation has a good
output (`AgreeOn.of_not_good`).
-/

namespace LeanVM.E2E

open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-- Computations with a private cache over the schemes' world. -/
abbrev PM : Type → Type := StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW)

/-- **Agreement on good outputs**: for every continuation that keeps the output, and every event
forcing the output good, the event has the same probability under the schemes' lazy random oracle. -/
def AgreeOn {α : Type} (good : α → Prop) (x y : PM α) : Prop :=
  ∀ (β : Type) (k : α → PM β)
    (ev : α → β → QueryCache LeanXmss.HashSpec → QueryCache LeanXmss.HashSpec → Prop)
    (cp c : QueryCache LeanXmss.HashSpec), (∀ a b cp' c', ev a b cp' c' → good a) →
    Pr{let z ← romRun ((x >>= fun a ↦ (a, ·) <$> k a).run cp) c}[ev z.1.1.1 z.1.1.2 z.1.2 z.2] =
    Pr{let z ← romRun ((y >>= fun a ↦ (a, ·) <$> k a).run cp) c}[ev z.1.1.1 z.1.1.2 z.1.2 z.2]

/-! ## Runs of private-cache computations -/

/-- The lazy oracle's run of a bind with a private cache. -/
theorem romRun_pm_bind {α β : Type} (x : PM α) (f : α → PM β) (cp c : QueryCache LeanXmss.HashSpec) :
    romRun ((x >>= f).run cp) c =
      romRun (x.run cp) c >>= fun r ↦ romRun ((f r.1.1).run r.1.2) r.2 := by
  rw [StateT.run_bind, romRun_bind]

/-- The lazy oracle's run of a map with a private cache. -/
theorem romRun_pm_map {α β : Type} (f : α → β) (x : PM α) (cp c : QueryCache LeanXmss.HashSpec) :
    romRun ((f <$> x).run cp) c =
      (fun z ↦ ((f z.1.1, z.1.2), z.2)) <$> romRun (x.run cp) c := by
  simp only [romRun, StateT.run_map, simulateQ_map]

/-- The lazy oracle's outputs are outputs of the computation. -/
theorem fst_mem_support_of_mem_romRun {α : Type} {oa : OracleComp OW α}
    {c : QueryCache LeanXmss.HashSpec} {z : α × QueryCache LeanXmss.HashSpec}
    (hz : z ∈ support (romRun oa c)) : z.1 ∈ support oa := by
  have h1 : z.1 ∈ support ((simulateQ owImpl oa).run' c) := by
    rw [StateT.run'_eq, support_map]; exact ⟨z, hz, rfl⟩
  exact support_simulateQ_run'_subset _ _ _ h1

/-- An output of a computation followed by a continuation that keeps its output. -/
theorem mem_support_pm_bind_pair {α β : Type} {x : PM α} {k : α → PM β}
    {cp : QueryCache LeanXmss.HashSpec} {z : (α × β) × QueryCache LeanXmss.HashSpec}
    (hz : z ∈ support ((x >>= fun a ↦ (a, ·) <$> k a).run cp)) :
    ∃ cp₁, (z.1.1, cp₁) ∈ support (x.run cp) ∧ (z.1.2, z.2) ∈ support ((k z.1.1).run cp₁) := by
  rw [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨p, hp, hz⟩ := hz
  rw [StateT.run_map, support_map] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  exact ⟨p.2, hp, hq⟩

/-- A continuation that keeps its input outputs it. -/
theorem fst_eq_of_mem_romRun_pair {α β : Type} {a : α} {k : α → PM β}
    {cp c : QueryCache LeanXmss.HashSpec}
    {z : ((α × β) × QueryCache LeanXmss.HashSpec) × QueryCache LeanXmss.HashSpec}
    (hz : z ∈ support (romRun (((a, ·) <$> k a).run cp) c)) : z.1.1.1 = a := by
  have h := fst_mem_support_of_mem_romRun hz
  rw [StateT.run_map, support_map] at h
  obtain ⟨q, -, hq⟩ := h
  rw [← hq]

/-! ## Agreement is an equivalence -/

theorem AgreeOn.refl {α : Type} (good : α → Prop) (x : PM α) : AgreeOn good x x :=
  fun _ _ _ _ _ _ ↦ rfl

theorem AgreeOn.symm {α : Type} {good : α → Prop} {x y : PM α} (h : AgreeOn good x y) :
    AgreeOn good y x :=
  fun _ k ev cp c hev ↦ (h _ k ev cp c hev).symm

theorem AgreeOn.trans {α : Type} {good : α → Prop} {x y z : PM α} (h : AgreeOn good x y)
    (h' : AgreeOn good y z) : AgreeOn good x z :=
  fun _ k ev cp c hev ↦ (h _ k ev cp c hev).trans (h' _ k ev cp c hev)

/-! ## Agreement under binds -/

/-- **Computations with no good output agree.** -/
theorem AgreeOn.of_not_good {α : Type} {good : α → Prop} {x y : PM α}
    (hx : ∀ cp, ∀ z ∈ support (x.run cp), ¬ good z.1)
    (hy : ∀ cp, ∀ z ∈ support (y.run cp), ¬ good z.1) : AgreeOn good x y := by
  have zero : ∀ (w : PM α), (∀ cp, ∀ z ∈ support (w.run cp), ¬ good z.1) →
      ∀ (β : Type) (k : α → PM β)
        (ev : α → β → QueryCache LeanXmss.HashSpec → QueryCache LeanXmss.HashSpec → Prop)
        (cp c : QueryCache LeanXmss.HashSpec), (∀ a b cp' c', ev a b cp' c' → good a) →
        Pr{let z ← romRun ((w >>= fun a ↦ (a, ·) <$> k a).run cp) c}[
          ev z.1.1.1 z.1.1.2 z.1.2 z.2] = 0 := by
    intro w hw β k ev cp c hev
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' ↦ ?_
    obtain ⟨cp₁, h1, -⟩ := mem_support_pm_bind_pair (fst_mem_support_of_mem_romRun hz)
    exact hw cp _ h1 (hev _ _ _ _ hz')
  intro β k ev cp c hev
  rw [zero x hx β k ev cp c hev, zero y hy β k ev cp c hev]

/-- **A common prefix keeps agreement.** -/
theorem agreeOn_bind_congr {γ α : Type} {good : α → Prop} (x : PM γ) (A B : γ → PM α)
    (h : ∀ m, AgreeOn good (A m) (B m)) : AgreeOn good (x >>= A) (x >>= B) := by
  intro β k ev cp c hev
  rw [bind_assoc, bind_assoc, romRun_pm_bind, romRun_pm_bind]
  exact prEvent_bind_congr _ _ _ _ _ fun r ↦ h r.1.1 β k ev r.1.2 r.2 hev

/-- **Agreement where a condition holds, bad outputs where it fails.** -/
theorem agreeOn_bind {γ α : Type} (x : PM γ) (d d' : γ → PM α) (G : γ → Prop) (good : α → Prop)
    (hd : ∀ m, G m → d m = d' m)
    (hbad : ∀ m, ¬ G m → ∀ cp, (∀ z ∈ support ((d m).run cp), ¬ good z.1) ∧
      ∀ z ∈ support ((d' m).run cp), ¬ good z.1) :
    AgreeOn good (x >>= d) (x >>= d') := by
  refine agreeOn_bind_congr x d d' fun m ↦ ?_
  by_cases hm : G m
  · rw [hd m hm]; exact AgreeOn.refl _ _
  · exact AgreeOn.of_not_good (fun cp ↦ (hbad m hm cp).1) fun cp ↦ (hbad m hm cp).2

/-- **A continuation whose good outputs come from good outputs keeps agreement.** -/
theorem AgreeOn.bind_comb {α δ γ : Type} {good : α → Prop} {x y : PM α} (h : AgreeOn good x y)
    (good' : γ → Prop) (B : α → PM δ) (comb : α → δ → γ)
    (hc : ∀ a t, good' (comb a t) → good a) :
    AgreeOn good' (x >>= fun a ↦ B a >>= fun t ↦ pure (comb a t))
      (y >>= fun a ↦ B a >>= fun t ↦ pure (comb a t)) := by
  intro β k ev cp c hev
  have hre : ∀ w : PM α,
      ((w >>= fun a ↦ B a >>= fun t ↦ pure (comb a t)) >>= fun v ↦ (v, ·) <$> k v) =
        (fun p : α × (δ × β) ↦ (comb p.1 p.2.1, p.2.2)) <$>
          (w >>= fun a ↦ (a, ·) <$> (B a >>= fun t ↦ (t, ·) <$> k (comb a t))) := by
    intro w
    simp only [bind_assoc, pure_bind, map_bind, Functor.map_map]
  rw [hre x, hre y, romRun_pm_map, romRun_pm_map, prEvent_map, prEvent_map]
  exact h _ (fun a ↦ B a >>= fun t ↦ (t, ·) <$> k (comb a t))
    (fun a tb cp' c' ↦ ev (comb a tb.1) tb.2 cp' c') cp c
    fun a tb cp' c' he ↦ hc a tb.1 (hev _ _ _ _ he)

/-- **A pure continuation whose good outputs come from good outputs keeps agreement.** -/
theorem AgreeOn.bind_pure {α γ : Type} {good : α → Prop} {x y : PM α} (h : AgreeOn good x y)
    (good' : γ → Prop) (comb : α → γ) (hc : ∀ a, good' (comb a) → good a) :
    AgreeOn good' (x >>= fun a ↦ pure (comb a)) (y >>= fun a ↦ pure (comb a)) := by
  simpa only [pure_bind] using
    h.bind_comb good' (fun _ ↦ (pure () : PM Unit)) (fun a _ ↦ comb a) fun a _ ↦ hc a

/-! ## Sequences -/

/-- **Sequences of agreeing computations agree** on the outputs good everywhere. -/
theorem agreeOn_sequenceFin {α : Type} {n : ℕ} (good : α → Prop) (f g : Fin n → PM α)
    (h : ∀ i, AgreeOn good (f i) (g i)) :
    AgreeOn (fun v : Fin n → α ↦ ∀ i, good (v i)) (LeanXmss.Concrete.sequenceFin f)
      (LeanXmss.Concrete.sequenceFin g) := by
  induction n with
  | zero => exact AgreeOn.refl _ _
  | succ n ih =>
    have e : ∀ F : Fin (n + 1) → PM α, LeanXmss.Concrete.sequenceFin F =
        F 0 >>= fun a ↦ LeanXmss.Concrete.sequenceFin (fun i : Fin n ↦ F i.succ) >>= fun t ↦
          pure (Fin.cases (motive := fun _ ↦ α) a t) := fun _ ↦ rfl
    rw [e f, e g]
    have h1 := (h 0).bind_comb (fun v : Fin (n + 1) → α ↦ ∀ i, good (v i))
      (fun _ ↦ LeanXmss.Concrete.sequenceFin fun i : Fin n ↦ f i.succ)
      (fun a t ↦ Fin.cases (motive := fun _ ↦ α) a t) fun a t hv ↦ by simpa using hv 0
    have h2 := agreeOn_bind_congr (g 0)
      (fun a ↦ LeanXmss.Concrete.sequenceFin (fun i : Fin n ↦ f i.succ) >>= fun t ↦
        pure (Fin.cases (motive := fun _ ↦ α) a t))
      (fun a ↦ LeanXmss.Concrete.sequenceFin (fun i : Fin n ↦ g i.succ) >>= fun t ↦
        pure (Fin.cases (motive := fun _ ↦ α) a t)) fun a ↦
      (ih (fun i ↦ f i.succ) (fun i ↦ g i.succ) fun i ↦ h i.succ).bind_pure
        (fun v : Fin (n + 1) → α ↦ ∀ i, good (v i)) (fun t ↦ Fin.cases (motive := fun _ ↦ α) a t)
        fun t hv i ↦ by simpa using hv i.succ
    exact h1.trans h2

/-! ## Events after agreeing computations -/

/-- **An event after agreeing computations**: the continuations agree on good outputs and keep a
copy `key` of their input, and the event forces it good. -/
theorem prEvent_eq_of_agreeOn {α β : Type} {good : α → Prop} {x y : PM α} (h : AgreeOn good x y)
    (k k' : α → PM β) (hk : ∀ a, good a → k a = k' a) (key : β → α)
    (hkey : ∀ a, ∀ cp, ∀ z ∈ support ((k a).run cp), key z.1 = a)
    (hkey' : ∀ a, ∀ cp, ∀ z ∈ support ((k' a).run cp), key z.1 = a)
    (ev : β → QueryCache LeanXmss.HashSpec → QueryCache LeanXmss.HashSpec → Prop)
    (hev : ∀ b cp c, ev b cp c → good (key b)) (cp c : QueryCache LeanXmss.HashSpec) :
    Pr{let z ← romRun ((x >>= k).run cp) c}[ev z.1.1 z.1.2 z.2] =
      Pr{let z ← romRun ((y >>= k').run cp) c}[ev z.1.1 z.1.2 z.2] := by
  -- the event, with the output kept
  let ev' : α → β → QueryCache LeanXmss.HashSpec → QueryCache LeanXmss.HashSpec → Prop :=
    fun a b cp' c' ↦ ev b cp' c' ∧ key b = a
  have hev' : ∀ a b cp' c', ev' a b cp' c' → good a := fun a b cp' c' he ↦ he.2 ▸ hev _ _ _ he.1
  have keep : ∀ (w : PM α) (k₀ : α → PM β),
      (∀ a, ∀ cp, ∀ z ∈ support ((k₀ a).run cp), key z.1 = a) →
      Pr{let z ← romRun ((w >>= k₀).run cp) c}[ev z.1.1 z.1.2 z.2] =
        Pr{let z ← romRun ((w >>= fun a ↦ (a, ·) <$> k₀ a).run cp) c}[
          ev' z.1.1.1 z.1.1.2 z.1.2 z.2] := by
    intro w k₀ hk₀
    have hre : w >>= k₀ = Prod.snd <$> (w >>= fun a ↦ (a, ·) <$> k₀ a) := by
      simp only [map_bind, Functor.map_map, id_map']
    rw [hre, romRun_pm_map, prEvent_map]
    refine prEvent_congr_of_support _ _ _ fun z hz ↦ ?_
    obtain ⟨cp₁, -, h2⟩ := mem_support_pm_bind_pair (fst_mem_support_of_mem_romRun hz)
    exact ⟨fun he ↦ ⟨he, hk₀ _ _ _ h2⟩, fun he ↦ he.1⟩
  rw [keep x k hkey, keep y k' hkey', h β k ev' cp c hev', romRun_pm_bind, romRun_pm_bind]
  refine prEvent_bind_congr _ _ _ _ _ fun r ↦ ?_
  by_cases hr : good r.1.1
  · rw [hk _ hr]
  · have zero : ∀ k₀ : α → PM β, Pr{let z ← romRun (((r.1.1, ·) <$> k₀ r.1.1).run r.1.2) r.2}[
        ev' z.1.1.1 z.1.1.2 z.1.2 z.2] = 0 := fun k₀ ↦
      prEvent_eq_zero_of_forall_mem_support _ _ fun z hz he ↦
        hr (fst_eq_of_mem_romRun_pair hz ▸ hev' _ _ _ _ he)
    rw [zero, zero]

end
end LeanVM.E2E
