/-
  LeanVM.E2E.Reduction.Seeds

  leanSPHINCS's multi-user key generation (all seeds drawn at once, then the keys in order) is,
  in the schemes' lazy random oracle, the game's (each key from its own fresh seed, in order).
-/

module

public import LeanVM.E2E.Reduction.Commute
public import LeanVM.E2E.Reduction.Lift

/-!
# leanSPHINCS's multi-user key generation

`Sphincs.Security.Multi.gameCore` draws the `n` seeds at once (`sampleSeeds`, a uniform function)
and generates the keys in order (`keygenAll`, by its last key); the game draws each key's seed
before generating it (`keygen`, a sequence by its first key). In the schemes' lazy random oracle
the two have the same distribution of keys and final cache (`romRun_sKeygenAll`):

* `keygenAll` is `sequenceFin` of the per-key generations (`keygenAll_eq_sequenceFin`), a sequence
  being one by its last element too (`sequenceFin_snoc`);
* a uniform function on `Fin n` is a sequence of `n` uniform draws (`evalDistEq_sampleSeeds`);
* a coin commutes past a computation in the random oracle (`romRun_bind_comm`), so drawing all
  seeds first is drawing each before its key (`romRun_seeds_first`).
-/

namespace LeanVM.E2E

open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-- **A sequence is one by its last element too.** -/
theorem sequenceFin_snoc {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} :
    ∀ {k : ℕ} (f : Fin (k + 1) → m α), LeanXmss.Concrete.sequenceFin f = do
      let init ← LeanXmss.Concrete.sequenceFin fun i : Fin k ↦ f i.castSucc
      let l ← f (Fin.last k)
      pure (Fin.lastCases l init)
  | 0, f => by
    simp only [LeanXmss.Concrete.sequenceFin, pure_bind]
    rw [show Fin.last 0 = (0 : Fin 1) from rfl]
    refine bind_congr fun h ↦ ?_
    congr 1
    funext i
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    rfl
  | k + 1, f => by
    conv_lhs => rw [LeanXmss.Concrete.sequenceFin]
    simp only [sequenceFin_snoc (fun i : Fin (k + 1) ↦ f i.succ), bind_assoc, pure_bind]
    conv_rhs => rw [LeanXmss.Concrete.sequenceFin]
    simp only [bind_assoc, pure_bind, Fin.castSucc_zero]
    refine bind_congr fun h ↦ bind_congr fun init ↦ ?_
    simp only [Fin.succ_last]
    refine bind_congr fun l ↦ ?_
    congr 1
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [show (0 : Fin (k + 1 + 1)) = Fin.castSucc 0 from rfl, Fin.lastCases_castSucc]
      rfl
    · rw [Fin.cases_succ]
      refine Fin.lastCases ?_ (fun i ↦ ?_) j
      · rw [Fin.lastCases_last, Fin.succ_last, Fin.lastCases_last]
      · rw [Fin.lastCases_castSucc, Fin.succ_castSucc, Fin.lastCases_castSucc, Fin.cases_succ]

/-- **leanSPHINCS's multi-user key generation is a sequence** of the per-key generations. -/
theorem keygenAll_eq_sequenceFin [Sphincs.Params] :
    ∀ (n : ℕ) (seeds : Fin n → Sphincs.MasterSeed), Sphincs.Security.Multi.keygenAll n seeds =
      LeanXmss.Concrete.sequenceFin fun i ↦ Sphincs.Seeded.keygenFromSeed (seeds i)
  | 0, _ => rfl
  | n + 1, seeds => by
    rw [sequenceFin_snoc, ← keygenAll_eq_sequenceFin n]
    rfl

/-- A lifted sequence is the sequence of the lifts, in leanSPHINCS's world. -/
theorem liftM_sequenceFin_sphincs {α : Type} :
    ∀ {n : ℕ} (c : Fin n → OracleComp Sphincs.HashSpec α),
      (liftM (LeanXmss.Concrete.sequenceFin c) : OracleComp Sphincs.OracleWorld _) =
        LeanXmss.Concrete.sequenceFin fun i ↦ (liftM (c i) : OracleComp Sphincs.OracleWorld _)
  | 0, _ => by simp [LeanXmss.Concrete.sequenceFin]
  | n + 1, c => by
    simp only [LeanXmss.Concrete.sequenceFin, liftM_bind, liftM_pure]
    refine bind_congr fun h ↦ ?_
    rw [liftM_sequenceFin_sphincs (fun i ↦ c i.succ)]

/-- A lifted sequence is the sequence of the lifts. -/
theorem sLift_sequenceFin {α : Type} {n : ℕ} (c : Fin n → OracleComp Sphincs.HashSpec α) :
    sLift (LeanXmss.Concrete.sequenceFin c) = LeanXmss.Concrete.sequenceFin fun i ↦ sLift (c i) :=
  liftM_sequenceFin_sphincs c

/-- A sequence of `n` uniform seeds returns each tuple with probability `|seed|⁻ⁿ`. -/
theorem prEvent_sequenceFin_seed :
    ∀ (n : ℕ) (f : Fin n → Sphincs.MasterSeed),
      Pr{let y ← LeanXmss.Concrete.sequenceFin fun _ : Fin n ↦ Sphincs.sampleMasterSeed}[y = f] =
        ((Fintype.card Sphincs.MasterSeed : ℝ≥0∞) ^ n)⁻¹
  | 0, f => by
    simp only [LeanXmss.Concrete.sequenceFin, pow_zero, inv_one]
    rw [prEvent_pure]
    simp [Subsingleton.elim f Fin.elim0]
  | n + 1, f => by
    simp only [LeanXmss.Concrete.sequenceFin]
    have h : ∀ (a : Sphincs.MasterSeed) (t : Fin n → Sphincs.MasterSeed),
        (Fin.cases a t : Fin (n + 1) → Sphincs.MasterSeed) = f ↔
          (t = fun i ↦ f i.succ) ∧ a = f 0 := by
      intro a t
      rw [show (Fin.cases a t : Fin (n + 1) → Sphincs.MasterSeed) = Fin.cons a t from rfl,
        ← Fin.cons_self_tail f, Fin.cons_inj]
      exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩
    have e : Pr{let y ← (do
          let head ← Sphincs.sampleMasterSeed
          let tail ← LeanXmss.Concrete.sequenceFin fun _ : Fin n ↦ Sphincs.sampleMasterSeed
          pure (fun i ↦ Fin.cases head tail i : Fin (n + 1) → Sphincs.MasterSeed))}[y = f] =
        Pr{let a ← Sphincs.sampleMasterSeed; let t ← (LeanXmss.Concrete.sequenceFin
          fun _ : Fin n ↦ Sphincs.sampleMasterSeed)}[(t = fun i ↦ f i.succ) ∧ a = f 0] := by
      simp only [map_bind, bind_pure_comp, Functor.map_map, h]
    rw [e, prEvent_bind_and_eq_mul _ _ _ _ (fun _ ↦ prEvent_sequenceFin_seed n _)]
    unfold Sphincs.sampleMasterSeed
    rw [@SampleableType.prEvent_uniformSample_eq_singleton _ (SampleableType.ofFintype _) _ (f 0),
      pow_succ, ENNReal.mul_inv (by simp) (by simp)]

/-- **A uniform function on `Fin n` is a sequence of `n` uniform seeds.** -/
theorem evalDistEq_sampleSeeds (n : ℕ) :
    Sphincs.Security.Multi.sampleSeeds n =ᵈ
      LeanXmss.Concrete.sequenceFin fun _ : Fin n ↦ Sphincs.sampleMasterSeed := by
  rw [evalDistEq_iff_forall_prEvent_eq_output]
  intro f
  rw [prEvent_sequenceFin_seed, Sphincs.Security.Multi.sampleSeeds,
    @SampleableType.prEvent_uniformSample_eq_singleton _ (SampleableType.ofFintype _) _ f]
  simp

/-- Coins in the schemes' random oracle leave the cache. -/
theorem romRun_liftM_bind {α β : Type} (p : ProbComp α) (k : α → OracleComp OW β)
    (c : QueryCache LeanXmss.HashSpec) :
    romRun ((liftM p : OracleComp OW α) >>= k) c = p >>= fun a ↦ romRun (k a) c := by
  rw [romRun_bind]
  have h : romRun (liftM p : OracleComp OW α) c = (·, c) <$> p :=
    roSim.run_liftM (ro := (randomOracle : QueryImpl LeanXmss.HashSpec
      (StateT (QueryCache LeanXmss.HashSpec) ProbComp))) p c
  rw [h, bind_map_left]

/-- **Seeds drawn first are seeds drawn before each key**, in the schemes' random oracle. -/
theorem romRun_seeds_first {α β γ : Type} (coin : ProbComp β) (g : β → OracleComp OW α) :
    ∀ (n : ℕ) (K : (Fin n → α) → OracleComp OW γ) (c : QueryCache LeanXmss.HashSpec),
      romRun ((liftM (LeanXmss.Concrete.sequenceFin fun _ : Fin n ↦ coin) : OracleComp OW _) >>=
          fun seeds ↦ LeanXmss.Concrete.sequenceFin (fun i ↦ g (seeds i)) >>= K) c =ᵈ
        romRun (LeanXmss.Concrete.sequenceFin (fun _ : Fin n ↦ (liftM coin : OracleComp OW _) >>= g)
          >>= K) c
  | 0, K, c => by
    simp only [LeanXmss.Concrete.sequenceFin, liftM_pure, pure_bind]
    exact .rfl
  | n + 1, K, c => by
    simp only [LeanXmss.Concrete.sequenceFin, liftM_bind, liftM_pure, bind_assoc, pure_bind,
      Fin.cases_zero, Fin.cases_succ]
    rw [romRun_liftM_bind, romRun_liftM_bind]
    refine EvalDistEq.bind_right _ fun h ↦ ?_
    refine EvalDistEq.trans (m'' := ProbComp) (romRun_bind_comm
      (liftM (LeanXmss.Concrete.sequenceFin fun _ : Fin n ↦ coin) : OracleComp OW _) (g h)
      (fun t k0 ↦ LeanXmss.Concrete.sequenceFin (fun i ↦ g (t i)) >>=
        fun ks ↦ K fun i ↦ Fin.cases k0 ks i) c) ?_
    rw [romRun_bind, romRun_bind]
    exact EvalDistEq.bind_right _ fun r ↦
      romRun_seeds_first coin g n (fun ks ↦ K fun i ↦ Fin.cases r.1 ks i) r.2

/-- One leanSPHINCS key from its uniform seed, in the schemes' world. -/
noncomputable def sKeygen [Sphincs.Params] :
    OracleComp OW (Sphincs.PublicKey × Sphincs.Seeded.SecretKey) := do
  let seed ← (liftM Sphincs.sampleMasterSeed : OracleComp OW _)
  sLift (Sphincs.Seeded.keygenFromSeed seed)

/-- **leanSPHINCS's multi-user key generation is the game's**, in the schemes' random oracle:
before any continuation, the keys and the final cache have the same distribution. -/
theorem romRun_sKeygenAll [Sphincs.Params] {n : ℕ} {γ : Type}
    (K : (Fin n → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) → OracleComp OW γ)
    (c : QueryCache LeanXmss.HashSpec) :
    romRun ((liftM (Sphincs.Security.Multi.sampleSeeds n) : OracleComp OW _) >>= fun seeds ↦
        sLift (Sphincs.Security.Multi.keygenAll n seeds) >>= K) c =ᵈ
      romRun (LeanXmss.Concrete.sequenceFin (fun _ : Fin n ↦ sKeygen) >>= K) c := by
  rw [romRun_liftM_bind]
  simp only [keygenAll_eq_sequenceFin, sLift_sequenceFin]
  refine EvalDistEq.trans (m' := ProbComp)
    ((evalDistEq_sampleSeeds n).bind (g := fun seeds ↦ romRun
      (LeanXmss.Concrete.sequenceFin (fun i ↦ sLift (Sphincs.Seeded.keygenFromSeed (seeds i))) >>= K)
        c) fun _ ↦ .rfl) ?_
  rw [← romRun_liftM_bind]
  exact romRun_seeds_first Sphincs.sampleMasterSeed
    (fun seed ↦ sLift (Sphincs.Seeded.keygenFromSeed seed)) n K c

end
end LeanVM.E2E
