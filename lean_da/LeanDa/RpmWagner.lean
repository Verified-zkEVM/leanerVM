import LeanDa.RpmCodeBinding
import Mathlib.Data.Set.Finite.List

/-!
# Code binding in the random-permutation model: Wagner's bound for each `H`

The simulated world of code binding (`codeBindingExpG`) has two random oracles: `H` and the
challenges `G`. With `G` read as one random oracle of vectors (`run'_romImpl_evalDistEq_vec`),
and `H` sampled in advance on the strings of at most `2048` bytes as a table `h`
(`run'_romImpl_evalDistEq_eager`; every string the verifier hashes is that short), the world is,
for each table `h`, Wagner's random-oracle game (`PqDas`) for LeanDA with the hash `Hh h`, against
the adversary `advH h` that runs the simulated adversary with `H` answered from `h` on short
strings and lazily on long ones (`prob_cbWorld_eq`). Wagner's code-binding bound
(`leanDa_codeBinding`) holds for each `h`, and averages over `h` (`sq_tsub_avg_le`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanRpm LeanRpm.Duplex PqDas
open scoped ENNReal

namespace LeanDa

/-! ## The oracles -/

/-- Wagner's oracles: coins and the challenges `G`, a random oracle of the roots. -/
abbrev WSpec := unifSpec + (Digest →ₒ Challenges)

/-- The challenges and `H`. -/
abbrev TSpec := (Digest →ₒ Challenges) + roSpec (List UInt8) KDigest

/-- A cache of `H`. -/
abbrev HCache := (roSpec (List UInt8) KDigest).QueryCache

/-- A short string: at most `2048` bytes, a cell's. -/
def shortP (a : List UInt8) : Prop := a.length ≤ 2048

instance : DecidablePred shortP := fun a ↦ inferInstanceAs (Decidable (a.length ≤ 2048))

noncomputable instance : Fintype {a : List UInt8 // shortP a} :=
  (List.finite_length_le (α := UInt8) 2048).fintype

/-- A table of `H` on the short strings. -/
abbrev HTab := {a : List UInt8 // shortP a} → KDigest

/-- **The hash of a table**: the table's answer on a short string, `default` on a long one. -/
def Hh (h : HTab) (a : List UInt8) : Digest := if ha : shortP a then h ⟨a, ha⟩ else default

/-- **`H` from a table, in Wagner's world**: the table on short strings, lazily sampled on long
ones (the state), the challenges forwarded to Wagner's random oracle. -/
noncomputable def tImpl (h : HTab) : QueryImpl (unifSpec + TSpec) (StateT HCache (OracleComp WSpec))
  | .inl k => StateT.mk fun c ↦ (·, c) <$> liftM (WSpec.query (.inl k))
  | .inr (.inl d) => StateT.mk fun c ↦ (·, c) <$> liftM (WSpec.query (.inr d))
  | .inr (.inr a) =>
      if ha : shortP a then StateT.mk fun c ↦ pure (h ⟨a, ha⟩, c)
      else StateT.mk fun c ↦ liftM (((roSpec (List UInt8) KDigest).randomOracle a).run c)

/-- The `H` part of a cache. -/
def hPart (c : TSpec.QueryCache) : HCache := QueryCache.ofFn fun a ↦ c (.inr a)

/-- The challenges part of a cache. -/
def gPart (c : TSpec.QueryCache) : (Digest →ₒ Challenges).QueryCache :=
  QueryCache.ofFn fun d ↦ c (.inl d)

/-- A cache with no short string of `H`. -/
def NoShort (c : TSpec.QueryCache) : Prop := ∀ a, shortP a → c (.inr a) = none

theorem hPart_cacheQuery_inr (c : TSpec.QueryCache) (a : List UInt8) (u : KDigest) :
    hPart (c.cacheQuery (.inr a) u) = (hPart c).cacheQuery a u := by
  ext b
  by_cases h : b = a
  · subst h; simp [hPart]
  · simp [hPart, h]

theorem gPart_cacheQuery_inr (c : TSpec.QueryCache) (a : List UInt8) (u : KDigest) :
    gPart (c.cacheQuery (.inr a) u) = gPart c := by
  ext d; simp [gPart]

theorem hPart_cacheQuery_inl (c : TSpec.QueryCache) (d : Digest) (u : Challenges) :
    hPart (c.cacheQuery (.inl d) u) = hPart c := by
  ext a; simp [hPart]

theorem gPart_cacheQuery_inl (c : TSpec.QueryCache) (d : Digest) (u : Challenges) :
    gPart (c.cacheQuery (.inl d) u) = (gPart c).cacheQuery d u := by
  ext e
  by_cases h : e = d
  · subst h; simp [gPart]
  · simp [gPart, h]

/-- **`H` sampled in advance on short strings is `H` from a table in Wagner's world.** -/
theorem run'_eagerImpl_tImpl (h : HTab) {α : Type} (Z : OracleComp (unifSpec + TSpec) α) :
    (simulateQ (eagerImpl (hs := Digest →ₒ Challenges) shortP h) Z).run' ∅ =ᵈ
      (simulateQ (Digest →ₒ Challenges).romImpl ((simulateQ (tImpl h) Z).run' ∅)).run' ∅ := by
  rw [run'_simulateQ_foldWith]
  have h0 : (fun c : TSpec.QueryCache ↦ (hPart c, gPart c)) ∅ = (∅, ∅) := by
    simp only [Prod.mk.injEq]; constructor <;> ext <;> rfl
  rw [← h0]
  refine run'_simulateQ_evalDistEq_of_inv _ _ NoShort (fun c ↦ (hPart c, gPart c)) ?_ ?_ Z ∅
    (fun _ _ ↦ rfl)
  · intro t c hc z hz
    rcases t with k | d | a
    · change z ∈ support ((unifFwdImpl _ k).run c) at hz
      rw [unifFwd_run, support_map] at hz
      obtain ⟨_, -, rfl⟩ := hz
      exact hc
    · rcases mem_support_randomOracle_run hz with e | ⟨u, e⟩
      · rw [e]; exact hc
      · intro a ha; rw [e, QueryCache.cacheQuery_of_ne _ _ (by simp)]; exact hc a ha
    · simp only [eagerImpl] at hz
      split at hz
      · simp only [StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hc
      · next ha =>
        rcases mem_support_randomOracle_run hz with e | ⟨u, e⟩
        · rw [e]; exact hc
        · intro b hb
          rw [e, QueryCache.cacheQuery_of_ne _ _ (by rintro ⟨⟩; exact ha hb)]
          exact hc b hb
  · intro t c hc
    rcases t with k | d | a
    · change _ <$> (unifFwdImpl _ k).run c =ᵈ _
      rw [unifFwd_run, foldWith_run]
      simp only [tImpl, StateT.run_mk, simulateQ_map, StateT.run_map, Functor.map_map]
      rw [simulateQ_spec_query, show ((Digest →ₒ Challenges).romImpl (.inl k)).run (gPart c) =
        (·, gPart c) <$> (unifSpec.query k : ProbComp _) from
        unifFwdImpl.simulateQ_run (hashSpec := Digest →ₒ Challenges)
          (unifSpec.query k : ProbComp (Fin (k + 1))) (gPart c), Functor.map_map]
      exact EvalDistEq.rfl
    · rw [foldWith_run]
      simp only [tImpl, StateT.run_mk, simulateQ_map, StateT.run_map, Functor.map_map]
      rw [simulateQ_spec_query, romImpl_apply_inr]
      change _ <$> (TSpec.randomOracle (.inl d)).run c =ᵈ
        _ <$> ((Digest →ₒ Challenges).randomOracle d).run (gPart c)
      rw [randomOracle.run_eq, randomOracle.run_eq]
      have e : (gPart c) d = c (.inl d) := rfl
      rw [e]
      rcases c (.inl d) with _ | u
      · simp only [map_bind, map_pure, Prod.map_apply, id_eq, gPart_cacheQuery_inl,
          hPart_cacheQuery_inl]
        exact EvalDistEq.rfl
      · simp only [map_pure, Prod.map_apply, id_eq]
        exact EvalDistEq.rfl
    · rw [foldWith_run]
      simp only [eagerImpl, tImpl]
      split
      · next ha =>
        simp only [StateT.run_mk, simulateQ_pure, StateT.run_pure, map_pure, hc a ha,
          Option.getD_none, Prod.map_apply, id_eq]
        exact EvalDistEq.rfl
      · next ha =>
        simp only [StateT.run_mk]
        rw [simulateQ_romImpl_liftM_run, Functor.map_map, randomOracle.run_eq,
          randomOracle.run_eq]
        have e : (hPart c) a = c (.inr a) := rfl
        rw [e]
        rcases c (.inr a) with _ | u
        · simp only [map_bind, map_pure, Prod.map_apply, id_eq, gPart_cacheQuery_inr,
            hPart_cacheQuery_inr]
          exact EvalDistEq.rfl
        · simp only [map_pure, Prod.map_apply, id_eq]
          exact EvalDistEq.rfl

/-! ## The verifier hashes short strings -/

section Short

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem length_cellBytes (x : Cell) : (cellBytes x).length = 2048 := by
  rw [cellBytes, List.length_flatMap]
  simp only [length_kBytes, List.map_const', List.length_ofFn, List.sum_replicate, smul_eq_mul]

theorem length_pairBytes (a b : Digest) : (pairBytes a b).length = 64 := by
  simp [pairBytes]

theorem walkM_congr {H₁ H₂ : List UInt8 → m Digest} (hH : ∀ a, shortP a → H₁ a = H₂ a)
    (idx : ℕ) (node : Digest) (path : List Digest) :
    walkM H₁ idx node path = walkM H₂ idx node path := by
  induction path generalizing idx node with
  | nil => rfl
  | cons s rest ih =>
    simp only [walkM]
    rw [hH _ (by split <;> simp [shortP, length_pairBytes])]
    exact bind_congr fun d ↦ ih _ _

theorem verifyCellM_congr {H₁ H₂ : List UInt8 → m Digest} (hH : ∀ a, shortP a → H₁ a = H₂ a)
    (r : ℕ) (com : Digest) (p : Fin (r * 128)) (x : Cell) (τ : Opening) :
    verifyCellM H₁ r com p x τ = verifyCellM H₂ r com p x τ := by
  simp only [verifyCellM]
  rw [hH _ (by simp [shortP, length_cellBytes])]
  refine bind_congr fun d ↦ ?_
  rw [walkM_congr hH]
  refine bind_congr fun w ↦ ?_
  rw [hH _ (by simp [shortP, length_pairBytes])]

theorem walkM_pure (H : List UInt8 → Digest) (idx : ℕ) (node : Digest) (path : List Digest) :
    walkM (m := m) (fun a ↦ pure (H a)) idx node path = pure (walk H idx node path) := by
  induction path generalizing idx node with
  | nil => rfl
  | cons s rest ih =>
    simp only [walkM, pure_bind, ih, walk_cons]

/-- **Over a pure hash, the verification is `verifyCell`**, in any monad. -/
theorem verifyCellM_pure (H : List UInt8 → Digest) (r : ℕ) (com : Digest) (p : Fin (r * 128))
    (x : Cell) (τ : Opening) :
    verifyCellM (m := m) (fun a ↦ pure (H a)) r com p x τ = pure (verifyCell H r com p x τ) := by
  simp only [verifyCellM, pure_bind, walkM_pure, verifyCell, cellDigest]
  rfl

theorem run_mapM_const_state {σ β γ : Type} (f : β → StateT σ m γ) (g : β → m γ)
    (hf : ∀ b s, (f b).run s = (·, s) <$> g b) (l : List β) (s : σ) :
    (l.mapM f).run s = (·, s) <$> l.mapM g := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.mapM_cons, StateT.run_bind, hf, bind_map_left, StateT.run_pure, map_bind]
    refine bind_congr fun c ↦ ?_
    simp only [ih, bind_map_left, map_pure]

end Short

/-! ## The simulated world from a table of `H` -/

/-- A query of Wagner's random oracle, as his scheme makes it. -/
noncomputable abbrev wQ (d : Digest) : OracleComp WSpec Challenges :=
  HasQuery.query (spec := (Digest →ₒ Challenges)) d

theorem wQ_eq (d : Digest) : wQ d = liftM (WSpec.query (.inr d)) := rfl

/-- The challenges of a root read component by component from Wagner's random oracle. -/
noncomputable def readVecW (d : Digest) : OracleComp WSpec Challenges :=
  (fun l j ↦ l.getD j default) <$> (List.finRange 14).mapM fun j ↦ (fun v : Challenges ↦ v j) <$> wQ d

/-- The simulated world's oracles from a table `h` of `H`. -/
noncomputable def phiG (h : HTab) :
    QueryImpl (unifSpec + GSpec (List UInt8) KDigest Digest E 14) (StateT HCache (OracleComp WSpec)) :=
  tImpl h ∘ₛ (swapImpl ∘ₛ toV)

theorem simulateQ_phiG (h : HTab) {α : Type}
    (X : OracleComp (unifSpec + GSpec (List UInt8) KDigest Digest E 14) α) :
    simulateQ (tImpl h) (simulateQ swapImpl (simulateQ toV X)) = simulateQ (phiG h) X := by
  rw [phiG, QueryImpl.simulateQ_compose, QueryImpl.simulateQ_compose]

theorem phiG_G_run (h : HTab) (d : Digest) (j : Fin 14) (s : HCache) :
    (phiG h (.inr (.inr (d, j)))).run s = (fun v : Challenges ↦ (v j, s)) <$> wQ d := by
  simp only [phiG, QueryImpl.apply_compose, toV, simulateQ_map, simulateQ_spec_query, swapImpl,
    tImpl, StateT.run_map, StateT.run_mk, Functor.map_map]
  rfl

theorem phiG_H_run (h : HTab) (a : List UInt8) (ha : shortP a) (s : HCache) :
    (phiG h (.inr (.inl a))).run s = pure (Hh h a, s) := by
  simp only [phiG, QueryImpl.apply_compose, toV, simulateQ_spec_query, swapImpl, tImpl, ha,
    ↓reduceDIte, StateT.run_mk, Hh]

theorem run_readVec_phiG (h : HTab) (d : Digest) (s : HCache) :
    (simulateQ (phiG h) (readVec (Msg := List UInt8) (Dg := KDigest) (n := 14) d)).run s =
      (·, s) <$> readVecW d := by
  rw [readVec, simulateQ_map, StateT.run_map]
  have hp : ∀ {α} (a : α), simulateQ (phiG h) (pure a :
      OracleComp (unifSpec + GSpec (List UInt8) KDigest Digest E 14) α) = pure a :=
    fun a ↦ simulateQ_pure _ a
  have hb : ∀ {α β} (x : OracleComp (unifSpec + GSpec (List UInt8) KDigest Digest E 14) α)
      (f : α → OracleComp (unifSpec + GSpec (List UInt8) KDigest Digest E 14) β),
      simulateQ (phiG h) (x >>= f) = simulateQ (phiG h) x >>= fun a ↦ simulateQ (phiG h) (f a) :=
    fun x f ↦ simulateQ_bind _ x f
  rw [mapM_map (fun x ↦ simulateQ (phiG h) x) hp hb,
    run_mapM_const_state _ (fun j ↦ (fun v : Challenges ↦ v j) <$> wQ d) ?_, Functor.map_map,
    readVecW, Functor.map_map]
  intro j s'
  rw [gaP, simulateQ_spec_query, phiG_G_run, Functor.map_map]

/-- The win of the openings with the hash of the table `h` and the challenges `l`. -/
noncomputable def postP (r : ℕ) {Crs Proof : Type}
    {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel) (h : HTab)
    (crs : Crs) (out : (Digest × Proof) × List (Fin (r * 128) × Cell × Opening)) (l : Challenges) :
    Bool :=
  cbWin r out (out.2.map fun o ↦ verifyCell (Hh h) r out.1.1 o.1 o.2.1 o.2.2)
    (ps.verify crs ((), out.1.1, l) out.1.2)

theorem run_postV_phiG (r : ℕ) {Crs Proof : Type}
    {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel) (h : HTab)
    (crs : Crs) (out : (Digest × Proof) × List (Fin (r * 128) × Cell × Opening)) (l : Challenges)
    (s : HCache) :
    (simulateQ (phiG h) (simulateQ embG (postV r ps crs out l))).run s =
      pure (postP r ps h crs out l, s) := by
  rw [← QueryImpl.simulateQ_compose]
  have hp : ∀ {α} (a : α), simulateQ (phiG h ∘ₛ embG) (pure a :
      OracleComp (unifSpec + roSpec (List UInt8) KDigest) α) = pure a :=
    fun a ↦ simulateQ_pure _ a
  have hb : ∀ {α β} (x : OracleComp (unifSpec + roSpec (List UInt8) KDigest) α)
      (f : α → OracleComp (unifSpec + roSpec (List UInt8) KDigest) β),
      simulateQ (phiG h ∘ₛ embG) (x >>= f) =
        simulateQ (phiG h ∘ₛ embG) x >>= fun a ↦ simulateQ (phiG h ∘ₛ embG) (f a) :=
    fun x f ↦ simulateQ_bind _ x f
  have hHs : ∀ a, shortP a → simulateQ (phiG h ∘ₛ embG) (LeanDa.hH a) =
      (pure (Hh h a) : StateT HCache (OracleComp WSpec) Digest) := by
    intro a ha
    rw [LeanDa.hH, simulateQ_spec_query, QueryImpl.apply_compose]
    simp only [embG]
    rw [hP, simulateQ_spec_query]
    ext s
    rw [phiG_H_run h a ha]
    rfl
  rw [postV, hb, mapM_map (fun x ↦ simulateQ (phiG h ∘ₛ embG) x) hp hb]
  simp only [verifyCellM_map (fun x ↦ simulateQ (phiG h ∘ₛ embG) x) hp hb]
  rw [show (fun o : Fin (r * 128) × Cell × Opening ↦ verifyCellM
      (fun a ↦ simulateQ (phiG h ∘ₛ embG) (LeanDa.hH a)) r out.1.1 o.1 o.2.1 o.2.2) =
      fun o ↦ pure (verifyCell (Hh h) r out.1.1 o.1 o.2.1 o.2.2) from
    funext fun o ↦ (verifyCellM_congr hHs _ _ _ _ _).trans (verifyCellM_pure _ _ _ _ _ _)]
  rw [List.mapM_pure, pure_bind, hp]
  rfl

/-! ## Wagner's adversary for a table of `H` -/

section Adversary

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)

/-- The crs the adversary runs with: the given one when the setup can output it, else one it
can (the bound on the adversary's queries holds for these). -/
noncomputable def fixCrs (crs : Crs) : Crs := by
  classical
  exact if crs ∈ support ps.setup then crs else (support_nonempty ps.setup).some

theorem fixCrs_of_mem {crs : Crs} (h : crs ∈ support ps.setup) : fixCrs r ps crs = crs := by
  classical
  unfold fixCrs
  simp only [h, ↓reduceIte]

theorem fixCrs_mem (crs : Crs) : fixCrs r ps crs ∈ support ps.setup := by
  classical
  unfold fixCrs
  split
  · assumption
  · exact (support_nonempty ps.setup).some_mem

/-- The adversary in the simulated world: `H` queried at the label, then the RPM adversary with
its permutation queries simulated from `H` and `F`, `F` answered by the duplex lemma's simulator. -/
noncomputable def advSim (A : CodeBindingAdvRpm r Crs Proof) (crs : Crs) :
    OracleComp (unifSpec + GSpec (List UInt8) KDigest Digest E 14)
      ((Digest × Proof) × List (Fin (r * 128) × Cell × Opening)) :=
  (simulateQ (simImpl daDuplex hP gaP) (hQ (St := KState) daDuplex.label >>= fun _ ↦
    advS2 keccakPadding KState.zero (A ((), crs)))).run' SimSt.init

/-- **Wagner's adversary for the table `h` of `H`**: the simulated adversary, with `H` answered
from `h` on short strings and lazily on long ones, and the challenges `G` from Wagner's random
oracle. -/
noncomputable def advH (A : CodeBindingAdvRpm r Crs Proof) (h : HTab) :
    ErasureCodeCommitment.CodeBindingAdv (OracleComp WSpec) Cell (r * 128) (Unit × Crs)
      (Digest × Proof) Opening :=
  fun ck ↦ (simulateQ (phiG h) (advSim r A (fixCrs r ps ck.2))).run' ∅

/-- The simulated world for the table `h` and the crs: Wagner's adversary, then the openings
verified with the hash of `h` and the challenges of the root. -/
noncomputable def gameW (A : CodeBindingAdvRpm r Crs Proof) (h : HTab) (crs : Crs) :
    OracleComp WSpec Bool :=
  advH r ps A h ((), crs) >>= fun out ↦ postP r ps h crs out <$> readVecW out.1.1

/-- **The simulated world is, for each table of `H`, Wagner's world.** -/
theorem cbIdealG_evalDistEq (A : CodeBindingAdvRpm r Crs Proof) {crs : Crs}
    (hcrs : crs ∈ support ps.setup) :
    cbIdealG r ps A crs =ᵈ ($ᵗ HTab >>= fun h ↦
      (simulateQ (Digest →ₒ Challenges).romImpl (gameW r ps A h crs)).run' ∅) := by
  rw [cbIdealG]
  refine (run'_romImpl_evalDistEq_vec _).trans ?_
  refine (run'_romImpl_evalDistEq_swap _ _).trans ?_
  rw [swapCache_empty]
  refine (run'_romImpl_evalDistEq_eager shortP _ ∅).trans ?_
  refine EvalDistEq.bind_right _ fun h ↦ (run'_eagerImpl_tImpl h _).trans ?_
  rw [simulateQ_phiG]
  have e : (simulateQ (phiG h) ((simulateQ (simImpl daDuplex hP gaP)
      (hQ (St := KState) daDuplex.label >>= fun _ ↦ advS2 keccakPadding KState.zero (A ((), crs)))).run'
        SimSt.init >>= fun out ↦ readVec (Msg := List UInt8) (Dg := KDigest) out.1.1 >>= fun l ↦
          simulateQ embG (postV r ps crs out l))).run' ∅ = gameW r ps A h crs := by
    rw [gameW, advH, fixCrs_of_mem r ps hcrs, ← advSim, simulateQ_bind, StateT.run'_eq,
      StateT.run_bind, StateT.run'_eq, map_bind, bind_map_left]
    refine bind_congr fun z ↦ ?_
    rw [simulateQ_bind, StateT.run_bind, run_readVec_phiG, bind_map_left]
    simp only [run_postV_phiG, map_pure, map_bind]
    rw [map_eq_bind_pure_comp]
    rfl
  rw [e]

end Adversary

/-! ## Wagner's verification: one query of the challenges -/

section Verify

variable (r : ℕ) {Crs Proof : Type}

/-- Wagner's verification of the openings, the challenges queried for each. -/
noncomputable def verifyW (H : List UInt8 → Digest) (ps : Argument r H Crs Proof) (crs : Crs)
    (out : (Digest × Proof) × List (Fin (r * 128) × Cell × Opening)) : OracleComp WSpec Bool := do
  let vs ← out.2.mapM fun p ↦ (fun l ↦ ps.verify crs ((), out.1.1, l) out.1.2 &&
    verifyCell H r out.1.1 p.1 p.2.1 p.2.2) <$> wQ out.1.1
  pure (vs.all id && !decide ((code r).Consistent (out.2.map fun p ↦ (p.1, p.2.1))))

/-- **Wagner's code-binding experiment for LeanDA** as a probability. -/
theorem codeBindingExp_eq (H : List UInt8 → Digest) (ps : Argument r H Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp WSpec) Cell (r * 128) (Unit × Crs)
      (Digest × Proof) Opening) :
    (leanDa r H ps).codeBindingExp (code r) (roRuntime Digest Challenges) A {true} =
      Pr{let b ← ps.setup >>= fun crs ↦
        (simulateQ (Digest →ₒ Challenges).romImpl (A ((), crs) >>= verifyW r H ps crs)).run' ∅}[
          b = true] := by
  unfold ErasureCodeCommitment.codeBindingExp
  rw [← evalDist_simulateRom, evalDist_singleton_eq_prEvent]
  unfold leanDa scheme
  simp only [simulateRom, merkleVC, bind_assoc, pure_bind]
  have e1 : (monadLift (pure () : ProbComp Unit) : OracleComp WSpec Unit) = pure () := rfl
  rw [e1, pure_bind]
  erw [simulateRomWithCache_liftM_bind]
  refine LeanRpm.prEvent_bind_congr _ _ _ _ _ fun crs ↦ ?_
  simp only [simulateRomWithCache, map_eq_bind_pure_comp, Function.comp_def]
  rfl

abbrev WCache := (Digest →ₒ Challenges).QueryCache

theorem run_wQ (d : Digest) (c : WCache) :
    (simulateQ (Digest →ₒ Challenges).romImpl (wQ d)).run c = roStep d c :=
  run_hq (hs := Digest →ₒ Challenges) d c

theorem run_mapM_wQ_cached {β γ : Type} (d : Digest) (f : β → Challenges → γ) (l : List β)
    (c : WCache) (v : Challenges) (hc : c d = some v) :
    (simulateQ (Digest →ₒ Challenges).romImpl (l.mapM fun b ↦ f b <$> wQ d)).run c =
      pure (l.map fun b ↦ f b v, c) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
      run_wQ, roStep_of_some hc, map_pure, pure_bind, ih, simulateQ_pure, StateT.run_pure,
      List.map_cons]

/-- **Queries of one root's challenges**: the first is a random-oracle step, the others hit. -/
theorem run_mapM_wQ {β γ : Type} (d : Digest) (f : β → Challenges → γ) (b₀ : β) (l : List β)
    (c : WCache) :
    (simulateQ (Digest →ₒ Challenges).romImpl ((b₀ :: l).mapM fun b ↦ f b <$> wQ d)).run c =ᵈ
      (fun w ↦ ((b₀ :: l).map fun b ↦ f b w.1, w.2)) <$> roStep d c := by
  rw [List.mapM_cons]
  simp only [simulateQ_bind, StateT.run_bind, run_wQ, bind_map_left, simulateQ_pure,
    StateT.run_pure]
  conv_rhs => rw [← bind_pure_comp]
  refine EvalDistEq.bind_congr_of_support _ fun w hw ↦ ?_
  obtain ⟨-, hwd⟩ := le_of_mem_support_roStep d c hw
  simp only [run_mapM_wQ_cached d f l w.2 w.1 hwd, pure_bind, List.map_cons]
  exact EvalDistEq.rfl

theorem all_map_and {β : Type} (b : Bool) (f : β → Bool) (b₀ : β) (l : List β) :
    ((b₀ :: l).map fun q ↦ b && f q).all id = (((b₀ :: l).map f).all id && b) := by
  cases b <;> simp

/-- The argument for the relation of a hash `H`, from an argument for any relation. -/
def argH {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)
    (H : List UInt8 → Digest) : Argument r H Crs Proof :=
  ⟨ps.setup, ps.prove, ps.verify⟩

/-- **The challenges read once or for every opening.** -/
theorem prob_postP_eq_verifyW {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel) (h : HTab)
    (crs : Crs) (out : (Digest × Proof) × List (Fin (r * 128) × Cell × Opening)) (c : WCache) :
    Pr{let b ← (simulateQ (Digest →ₒ Challenges).romImpl
        (postP r ps h crs out <$> readVecW out.1.1)).run' c}[b = true] =
      Pr{let b ← (simulateQ (Digest →ₒ Challenges).romImpl
        (verifyW r (Hh h) (argH r ps (Hh h)) crs out)).run' c}[b = true] := by
  obtain ⟨com, l⟩ := out
  have hfin : List.finRange 14 = (0 : Fin 14) :: (List.finRange 13).map Fin.succ :=
    List.finRange_succ
  have hread : (simulateQ (Digest →ₒ Challenges).romImpl
      (postP r ps h crs (com, l) <$> readVecW com.1)).run' c =ᵈ
      (fun w ↦ postP r ps h crs (com, l) w.1) <$> roStep com.1 c := by
    rw [readVecW, Functor.map_map, StateT.run'_eq, simulateQ_map, StateT.run_map, hfin,
      Functor.map_map]
    refine ((run_mapM_wQ com.1 (fun j v ↦ v j) 0 _ c).map _).trans ?_
    rw [Functor.map_map]
    have hv : ∀ v : Challenges, (fun j : Fin 14 ↦
        (List.map (fun b ↦ v b) (0 :: List.map Fin.succ (List.finRange 13))).getD j default) = v := by
      intro v
      rw [← hfin]
      funext j
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
      rfl
    simp only [hv]
    exact EvalDistEq.rfl
  rw [hread.prEvent_eq]
  rcases l with _ | ⟨o, l⟩
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun b hb ↦ ?_,
      prEvent_eq_zero_of_forall_mem_support _ _ fun b hb ↦ ?_]
    · simp only [verifyW, List.mapM_nil, pure_bind, simulateQ_pure, StateT.run'_eq,
        StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at hb
      subst hb
      simp [consistent_nil]
    · simp only [support_map, Set.mem_image] at hb
      obtain ⟨w, -, rfl⟩ := hb
      simp [postP, cbWin, consistent_nil]
  · have hW : (simulateQ (Digest →ₒ Challenges).romImpl
        (verifyW r (Hh h) (argH r ps (Hh h)) crs (com, o :: l))).run' c =ᵈ
        (fun w : Challenges × WCache ↦ (((o :: l).map fun p ↦ ps.verify crs ((), com.1, w.1) com.2 &&
          verifyCell (Hh h) r com.1 p.1 p.2.1 p.2.2).all id &&
            !decide ((code r).Consistent ((o :: l).map fun p ↦ (p.1, p.2.1))))) <$>
          roStep com.1 c := by
      simp only [verifyW, StateT.run'_eq, simulateQ_bind, StateT.run_bind]
      have hm := run_mapM_wQ com.1 (fun (p : Fin (r * 128) × Cell × Opening) (v : Challenges) ↦
        (argH r ps (Hh h)).verify crs ((), com.1, v) com.2 &&
          verifyCell (Hh h) r com.1 p.1 p.2.1 p.2.2) o l c
      refine ((EvalDistEq.bind_left hm _).map _).trans ?_
      simp only [bind_map_left, simulateQ_pure, StateT.run_pure, map_bind, map_pure]
      rw [← bind_pure_comp]
      exact EvalDistEq.rfl
    rw [hW.prEvent_eq, prEvent_map, prEvent_map]
    congr 2
    funext w
    simp only [postP, cbWin, all_map_and]

end Verify

/-! ## Wagner's adversary queries the challenges at most `Q` times -/

/-- Queries of Wagner's random oracle, one each. -/
def wCalls : WSpec.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem hashQueryBound_of_isWeightBound {α : Type} {X : OracleComp WSpec α} {Q : ℕ}
    (h : IsWeightBound X wCalls Q) : CommittedSoundness.HashQueryBound X Q := by
  induction X using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    rw [CommittedSoundness.hashQueryBound_query_bind_iff]
    rcases t with n | d
    · exact ⟨trivial, fun u ↦ by simpa [wCalls] using ih u (h.2 u)⟩
    · have h1 := h.1
      simp only [wCalls] at h1
      exact ⟨by omega, fun u ↦ by simpa [wCalls] using ih u (h.2 u)⟩

/-- **Each step of the oracles from a table makes at most one query of the challenges**, and only
for one of `G`. -/
theorem isWeightBound_phiG (h : HTab) (t : (unifSpec + GSpec (List UInt8) KDigest Digest E 14).Domain)
    (s : HCache) : IsWeightBound ((phiG h t).run s) wCalls (gCalls t) := by
  rcases t with k | m | ⟨d, j⟩
  · simp only [phiG, QueryImpl.apply_compose, toV, simulateQ_spec_query, swapImpl, tImpl,
      StateT.run_mk]
    exact isWeightBound_map _ (isWeightBound_query (spec := WSpec) wCalls (.inl k))
  · simp only [phiG, QueryImpl.apply_compose, toV, simulateQ_spec_query, swapImpl, tImpl]
    split
    · trivial
    · exact isWeightBound_liftM_probComp wCalls (fun _ ↦ rfl) _
  · rw [phiG_G_run]
    exact isWeightBound_map _ (isWeightBound_query (spec := WSpec) wCalls (.inr d))

section Bound

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)

/-- **Wagner's adversary makes at most `Q` queries of the challenges.** -/
theorem hashQueryBound_advH (A : CodeBindingAdvRpm r Crs Proof) (Q : ℕ)
    (hQ : IsWeightBound (codeBindingGame r ps A) permCalls2 Q) (h : HTab) (ck : Unit × Crs) :
    CommittedSoundness.HashQueryBound (advH r ps A h ck) Q := by
  apply hashQueryBound_of_isWeightBound
  have hB := isWeightBound_advS2 r ps A Q hQ _ (fixCrs_mem r ps ck.2)
  have hP : IsWeightBound (LeanRpm.Duplex.hQ (St := KState) daDuplex.label >>= fun _ ↦
      advS2 keccakPadding KState.zero (A ((), fixCrs r ps ck.2)))
      (fCalls (Msg := List UInt8) (Dg := KDigest) (St := KState)) Q := by
    simpa using (isWeightBound_hQ (Dg := KDigest) (St := KState) daDuplex.label).bind fun _ ↦ hB
  have hS := isWeightBound_run_simulateQ _ _ _ (isWeightBound_simImpl (D := daDuplex)) hP
    SimSt.init
  rw [advH, advSim, StateT.run'_eq, StateT.run'_eq]
  exact isWeightBound_map _ (isWeightBound_run_simulateQ _ _ _ (isWeightBound_phiG h)
    (isWeightBound_map _ hS) _)

end Bound

/-! ## Averaging Wagner's bound over `H` -/

/-- **Cauchy–Schwarz** for finite weights and values. -/
theorem sq_sum_mul_le {T : Type} (s : Finset T) (μ d : T → ℝ≥0∞) (hμ : ∀ t, μ t ≠ ⊤)
    (hd : ∀ t, d t ≠ ⊤) :
    (∑ t ∈ s, μ t * d t) ^ 2 ≤ (∑ t ∈ s, μ t) * ∑ t ∈ s, μ t * d t ^ 2 := by
  have eμ : μ = fun t ↦ ((μ t).toNNReal : ℝ≥0∞) := funext fun t ↦ (ENNReal.coe_toNNReal (hμ t)).symm
  have ed : d = fun t ↦ ((d t).toNNReal : ℝ≥0∞) := funext fun t ↦ (ENNReal.coe_toNNReal (hd t)).symm
  have key : (∑ x ∈ s, (μ x).toNNReal * (d x).toNNReal) ^ 2 ≤
      (∑ x ∈ s, (μ x).toNNReal) * ∑ x ∈ s, (μ x).toNNReal * (d x).toNNReal ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun _ _ ↦ zero_le) (fun _ _ ↦ zero_le)
      fun _ _ ↦ le_of_eq (by ring)
  rw [eμ, ed]
  beta_reduce
  exact_mod_cast key

/-- The probability that a computation returns `true`. -/
noncomputable abbrev prT (x : ProbComp Bool) : ℝ≥0∞ := Pr{let b ← x}[b = true]

/-- **Averaging a squared bound**: Wagner's bound for each `t` gives it for a random `t`, the
averages of the three probabilities in place of each. -/
theorem sq_tsub_avg_le {T : Type} [Fintype T] (mx : ProbComp T) (cb ks w f : T → ProbComp Bool)
    (C δ : ℝ≥0∞) (h : ∀ t, (prT (cb t) - (prT (ks t) + prT (w t))) ^ 2 ≤ C * (prT (f t) + δ)) :
    (prT (mx >>= cb) - (prT (mx >>= ks) + prT (mx >>= w))) ^ 2 ≤ C * (prT (mx >>= f) + δ) := by
  simp only [prT, OracleComp.prEvent_bind_eq_tsum, tsum_fintype]
  set μ : T → ℝ≥0∞ := fun t ↦ Pr{let z ← mx}[z = t] with hμdef
  have hμ1 : ∑ t, μ t ≤ 1 := by
    have := OracleComp.tsum_prEvent_le_one mx
    rwa [tsum_fintype] at this
  have hμ : ∀ t, μ t ≠ ⊤ := fun t ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
  set d : T → ℝ≥0∞ := fun t ↦ prT (cb t) - (prT (ks t) + prT (w t)) with hddef
  have hd : ∀ t, d t ≠ ⊤ := fun t ↦
    ne_top_of_le_ne_top ENNReal.one_ne_top (tsub_le_self.trans (prEvent_le_one _))
  have h1 : ∑ t, μ t * prT (cb t) - (∑ t, μ t * prT (ks t) + ∑ t, μ t * prT (w t)) ≤
      ∑ t, μ t * d t := by
    rw [tsub_le_iff_right, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t _ ↦ ?_
    rw [← mul_add, ← mul_add]
    gcongr
    exact le_tsub_add
  calc (∑ t, μ t * prT (cb t) - (∑ t, μ t * prT (ks t) + ∑ t, μ t * prT (w t))) ^ 2
      ≤ (∑ t, μ t * d t) ^ 2 := pow_le_pow_left₀ zero_le h1 2
    _ ≤ (∑ t, μ t) * ∑ t, μ t * d t ^ 2 := sq_sum_mul_le _ μ d hμ hd
    _ ≤ 1 * ∑ t, μ t * (C * (prT (f t) + δ)) := by
        gcongr with t
        exact h t
    _ = C * (∑ t, μ t * prT (f t) + (∑ t, μ t) * δ) := by
        rw [one_mul, mul_add, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        ring
    _ ≤ C * (∑ t, μ t * prT (f t) + δ) := by
        gcongr
        exact mul_le_of_le_one_left' hμ1

/-! ## Code binding in the random-permutation model -/

theorem prEvent_bind_congr_of_support {α β : Type} (mx : ProbComp α) (f g : α → ProbComp β)
    (P : β → Prop) (hp : ∀ x ∈ support mx, Pr{let y ← f x}[P y] = Pr{let y ← g x}[P y]) :
    Pr{let y ← mx >>= f}[P y] = Pr{let y ← mx >>= g}[P y] := by
  simp only [OracleComp.prEvent_bind_eq_tsum]
  refine tsum_congr fun x ↦ ?_
  by_cases hx : x ∈ support mx
  · rw [hp x hx]
  · simp [prEvent_eq_zero_of_not_mem_support mx hx]

section Final

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)

/-- **The simulated world is the average over `H` of Wagner's worlds.** -/
theorem prT_codeBindingExpG (A : CodeBindingAdvRpm r Crs Proof) :
    prT (codeBindingExpG r ps A) = prT (($ᵗ HTab : ProbComp HTab) >>= fun h ↦ ps.setup >>= fun crs ↦
      (simulateQ (Digest →ₒ Challenges).romImpl (gameW r ps A h crs)).run' ∅) := by
  rw [prT, codeBindingExpG]
  rw [prEvent_bind_congr_of_support _ _ (fun crs ↦ ($ᵗ HTab : ProbComp HTab) >>= fun h ↦
    (simulateQ (Digest →ₒ Challenges).romImpl (gameW r ps A h crs)).run' ∅) _
      fun crs hcrs ↦ (cbIdealG_evalDistEq r ps A hcrs).prEvent_eq _]
  exact (EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _

/-- **Wagner's world for the table `h`** is his code-binding experiment for LeanDA with the hash
`Hh h`, against `advH h`. -/
theorem prT_gameW (A : CodeBindingAdvRpm r Crs Proof) (h : HTab) :
    prT (ps.setup >>= fun crs ↦
      (simulateQ (Digest →ₒ Challenges).romImpl (gameW r ps A h crs)).run' ∅) =
      (leanDa r (Hh h) (argH r ps (Hh h))).codeBindingExp (code r) (roRuntime Digest Challenges)
        (advH r ps A h) {true} := by
  rw [codeBindingExp_eq, prT]
  refine LeanRpm.prEvent_bind_congr _ _ _ _ _ fun crs ↦ ?_
  have e : ∀ K : ((Digest × Proof) × List (Fin (r * 128) × Cell × Opening)) → OracleComp WSpec Bool,
      (simulateQ (Digest →ₒ Challenges).romImpl (advH r ps A h ((), crs) >>= K)).run' ∅ =
        (simulateQ (Digest →ₒ Challenges).romImpl (advH r ps A h ((), crs))).run ∅ >>= fun z ↦
          (simulateQ (Digest →ₒ Challenges).romImpl (K z.1)).run' z.2 := by
    intro K
    simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
  rw [gameW, e, e]
  exact LeanRpm.prEvent_bind_congr _ _ _ _ _ fun z ↦ prob_postP_eq_verifyW r ps h crs z.1 z.2

/-- Wagner's knowledge-soundness experiment for the table `h`: his reduction `ksReduction` from
`advH h`, against the argument `ps` for the relation with the hash `Hh h`. -/
noncomputable def ksExpH
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : CodeBindingAdvRpm r Crs Proof) (h : HTab) : ProbComp Bool :=
  (argH r ps (Hh h)).knowledgeSoundnessExp ext (ksReduction (merkleVC r (Hh h)) (advH r ps A h))

/-- The collision experiment of `Hh h` against Wagner's weak-position-binding reduction from
`advH h`, through `merkleCollider`. -/
noncomputable def wpbCollExpH [NeZero r]
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : CodeBindingAdvRpm r Crs Proof) (h : HTab) : ProbComp Bool :=
  hashCollisionExp (Hh h) (merkleCollider r (Hh h)
    ((wpbReduction (argH r ps (Hh h)) ext (advH r ps A h)).toPosBindingAdv (merkleVC r (Hh h))))

/-- The collision experiment of `Hh h` against Wagner's forking reduction from `advH h` (at most
`Q + 1` queries of the challenges), through `merkleCollider`. -/
noncomputable def forkCollExpH [NeZero r]
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : CodeBindingAdvRpm r Crs Proof) (Q : ℕ) (h : HTab) : ProbComp Bool :=
  hashCollisionExp (Hh h) (merkleCollider r (Hh h)
    ((CommittedSoundness.forkCollisionReduction (code r) (merkleVC r (Hh h)) (checker r)
      (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) (Q + 1)).toPosBindingAdv
        (merkleVC r (Hh h))))

end Final

end LeanDa
