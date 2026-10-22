/-
  LeanVM.E2E.Vis.PerKey.XmssView

  W-vis, P7b: the per-key leanXMSS reduction's view. Its run under the single-key game's oracles
  and the class-routed game agree on every event that forces good keys.
-/

module

public import LeanVM.E2E.Vis.PerKey.XmssKeygen
public import VCVio.OracleComp.EvalDist.Sum

/-!
# The reduction's view (W-vis, P7b)

* `agreeOn_sequenceFin_at`: sequences agree on outputs good at every index, for an
  index-dependent goodness.
* `agreeOn_keys`: the class-routed game's key generation (key `j` given) and the reduction's agree
  on keys where no other parameter is `pj` (`GoodKeys`).
* `prEvent_view`: the class-routed game's run after key `j`, and the reduction's run under the
  game's oracles, give every event forcing good keys the same probability.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-! ## Agreement: weakening and sequences -/

/-- Agreement on more goodness is agreement on less. -/
theorem AgreeOn.mono {α : Type} {good good' : α → Prop} {x y : PM α} (h : AgreeOn good x y)
    (hg : ∀ a, good' a → good a) : AgreeOn good' x y :=
  fun β k ev cp c hev ↦ h β k ev cp c fun a b cp' c' he ↦ hg a (hev a b cp' c' he)

/-- **Sequences agree on outputs good at every index.** -/
theorem agreeOn_sequenceFin_at {α : Type} :
    ∀ {n : ℕ} (good : Fin n → α → Prop) (f g : Fin n → PM α),
      (∀ i, AgreeOn (good i) (f i) (g i)) →
      AgreeOn (fun v : Fin n → α ↦ ∀ i, good i (v i)) (LeanXmss.Concrete.sequenceFin f)
        (LeanXmss.Concrete.sequenceFin g)
  | 0, _, _, _, _ => AgreeOn.refl _ _
  | n + 1, good, f, g, h => by
    have e : ∀ F : Fin (n + 1) → PM α, LeanXmss.Concrete.sequenceFin F =
        F 0 >>= fun a ↦ LeanXmss.Concrete.sequenceFin (fun i : Fin n ↦ F i.succ) >>= fun t ↦
          pure (Fin.cases (motive := fun _ ↦ α) a t) := fun _ ↦ rfl
    rw [e f, e g]
    have h1 := (h 0).bind_comb (fun v : Fin (n + 1) → α ↦ ∀ i, good i (v i))
      (fun _ ↦ LeanXmss.Concrete.sequenceFin fun i : Fin n ↦ f i.succ)
      (fun a t ↦ Fin.cases (motive := fun _ ↦ α) a t) fun a t hv ↦ by simpa using hv 0
    have h2 := agreeOn_bind_congr (g 0)
      (fun a ↦ LeanXmss.Concrete.sequenceFin (fun i : Fin n ↦ f i.succ) >>= fun t ↦
        pure (Fin.cases (motive := fun _ ↦ α) a t))
      (fun a ↦ LeanXmss.Concrete.sequenceFin (fun i : Fin n ↦ g i.succ) >>= fun t ↦
        pure (Fin.cases (motive := fun _ ↦ α) a t)) fun a ↦
      (agreeOn_sequenceFin_at (fun i ↦ good i.succ) (fun i ↦ f i.succ) (fun i ↦ g i.succ)
        fun i ↦ h i.succ).bind_pure
        (fun v : Fin (n + 1) → α ↦ ∀ i, good i (v i)) (fun t ↦ Fin.cases (motive := fun _ ↦ α) a t)
        fun t hv i ↦ by simpa using hv i.succ
    exact h1.trans h2

/-- A monad morphism maps a sequence to the sequence of its images. -/
theorem morph_sequenceFin {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    {φ : ∀ {α : Type}, m α → n α} (hφ : IsMorphism @φ) {α : Type} :
    ∀ {k : ℕ} (f : Fin k → m α),
      φ (LeanXmss.Concrete.sequenceFin f) = LeanXmss.Concrete.sequenceFin fun i ↦ φ (f i)
  | 0, _ => hφ.pure _
  | k + 1, f => by
    simp only [LeanXmss.Concrete.sequenceFin, hφ.bind, hφ.pure]
    refine bind_congr fun a ↦ ?_
    rw [morph_sequenceFin hφ (fun i : Fin k ↦ f i.succ)]

/-- **The value in a pure position of a sequence is immaterial**: the continuation may overwrite
it (lean_xmss's `sequenceFin_slot`). -/
theorem sequenceFin_slot' {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} {n : ℕ}
    (j : Fin n) (x y : α) (c : Fin n → m α) (G : (Fin n → α) → m β) :
    (LeanXmss.Concrete.sequenceFin (fun i ↦ if i = j then pure x else c i) >>= fun keys ↦
        G (fun i ↦ if i = j then y else keys i)) =
      LeanXmss.Concrete.sequenceFin (fun i ↦ if i = j then pure y else c i) >>= G := by
  have map : ∀ {k : ℕ} (f : Fin k → m α) (g : Fin k → α → α),
      LeanXmss.Concrete.sequenceFin (fun i ↦ g i <$> f i) =
        (fun r i ↦ g i (r i)) <$> LeanXmss.Concrete.sequenceFin f := by
    intro k
    induction k with
    | zero => intro f g; simp only [LeanXmss.Concrete.sequenceFin, map_pure]; congr 1; funext i; exact i.elim0
    | succ k ih =>
      intro f g
      simp only [LeanXmss.Concrete.sequenceFin, map_bind, bind_map_left, map_pure]
      refine bind_congr fun head ↦ ?_
      rw [ih (fun i ↦ f i.succ) (fun i ↦ g i.succ), bind_map_left]
      refine bind_congr fun tail ↦ ?_
      congr 1
      funext i
      cases i using Fin.cases <;> rfl
  have h : (fun i ↦ if i = j then pure y else c i) =
      fun i ↦ (fun a ↦ if i = j then y else a) <$> (if i = j then pure x else c i) := by
    funext i
    by_cases hi : i = j
    · simp only [hi, ↓reduceIte, map_pure]
    · simp only [hi, ↓reduceIte, id_map']
  rw [h, map, bind_map_left]

namespace PerKeyX

variable {nx ns : ℕ} [Sphincs.Params]

/-- A leanXMSS key pair. -/
abbrev XKey : Type := LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey
/-- A leanSPHINCS key pair. -/
abbrev SKey : Type := Sphincs.PublicKey × Sphincs.Seeded.SecretKey

/-- **Good keys for reduction `j`**, key `j` being `kj'`: every other parameter is not `pj`. -/
def GoodKeys (pj : Bytes) (j : Fin nx) (kj' : XKey) (p : (Fin nx → XKey) × (Fin ns → SKey)) :
    Prop :=
  (∀ i, (i = j → p.1 i = kj') ∧ (i ≠ j → LeanXmss.bytesLE 16 (p.1 i).2.parameter ≠ pj)) ∧
    ∀ i, Sphincs.bytesLE 16 (p.2 i).2.parameter ≠ pj

/-- The class-routed game's key generation, key `j` given. -/
noncomputable def gKeys (pj : Bytes) (j : Fin nx) (kj' : XKey) :
    PM ((Fin nx → XKey) × (Fin ns → SKey)) := do
  let xs ← LeanXmss.Concrete.sequenceFin fun i : Fin nx ↦
    if i = j then pure kj'
    else simulateQ (routeImpl (PrivJ pj)) (LeanXmss.MultiUser.keygen : OracleComp OW _)
  let ss ← LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦
    simulateQ (routeImpl (PrivJ pj)) (sKeygen : OracleComp OW _)
  pure (xs, ss)

/-- The reduction's key generation, under the game's oracles, key `j` given. -/
noncomputable def rKeys (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) (j : Fin nx) (kj' : XKey) :
    PM ((Fin nx → XKey) × (Fin ns → SKey)) := do
  let xs ← LeanXmss.Concrete.sequenceFin fun i : Fin nx ↦
    if i = j then pure kj' else ΦJ sk (xKeygenR pj)
  let ss ← LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ ΦJ sk (sKeygenR pj)
  pure (xs, ss)

/-- **The two key generations agree on good keys.** -/
theorem agreeOn_keys (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) (hpj : pj.length = 16)
    (j : Fin nx) (kj' : XKey) :
    AgreeOn (GoodKeys (ns := ns) pj j kj') (gKeys pj j kj') (rKeys sk pj j kj') := by
  -- the leanXMSS sequence
  have hx : AgreeOn (fun v : Fin nx → XKey ↦ ∀ i,
        (i = j → v i = kj') ∧ (i ≠ j → LeanXmss.bytesLE 16 (v i).2.parameter ≠ pj))
      (LeanXmss.Concrete.sequenceFin fun i : Fin nx ↦
        if i = j then pure kj'
        else simulateQ (routeImpl (PrivJ pj)) (LeanXmss.MultiUser.keygen : OracleComp OW _))
      (LeanXmss.Concrete.sequenceFin fun i : Fin nx ↦
        if i = j then pure kj' else ΦJ sk (xKeygenR pj)) := by
    refine agreeOn_sequenceFin_at (fun (i : Fin nx) (k : XKey) ↦ (i = j → k = kj') ∧
      (i ≠ j → LeanXmss.bytesLE 16 k.2.parameter ≠ pj)) _ _ fun i ↦ ?_
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
      exact AgreeOn.refl _ _
    · simp only [hij, ↓reduceIte]
      exact (agreeOn_xKeygen sk pj hpj).mono fun k hk ↦ hk.2 hij
  -- the leanSPHINCS sequence
  have hs : AgreeOn (fun v : Fin ns → SKey ↦ ∀ i, Sphincs.bytesLE 16 (v i).2.parameter ≠ pj)
      (LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦
        simulateQ (routeImpl (PrivJ pj)) (sKeygen : OracleComp OW _))
      (LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ ΦJ sk (sKeygenR pj)) :=
    agreeOn_sequenceFin_at (fun (_ : Fin ns) (k : SKey) ↦ Sphincs.bytesLE 16 k.2.parameter ≠ pj) _ _
      fun _ ↦ agreeOn_sKeygen sk pj hpj
  unfold gKeys rKeys
  refine AgreeOn.trans (hx.bind_comb (GoodKeys pj j kj') _ (fun a t ↦ (a, t))
    fun a t h ↦ h.1) ?_
  exact agreeOn_bind_congr _ _ _ fun a ↦ hs.bind_pure (GoodKeys pj j kj') (fun t ↦ (a, t))
    fun t h ↦ h.2

/-- The game after key `j`'s generation: the other keys, then the rest, key `j` being `kj`. -/
noncomputable def RJ (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin nx)
    (kj : XKey) : OracleComp OW (GameOutcome nx ns × Log) := do
  let xs ← LeanXmss.Concrete.sequenceFin fun i : Fin nx ↦
    if i = j then pure kj else (LeanXmss.MultiUser.keygen : OracleComp OW _)
  let ss ← LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ (sKeygen : OracleComp OW _)
  gameRest guest fuel budget A ⟨xs, ss⟩

/-- Key `j` replaced by `k` in a list of leanXMSS keys. -/
def updJ (j : Fin nx) (k : XKey) (v : Fin nx → XKey) : Fin nx → XKey := fun i ↦ if i = j then k else v i

/-- Key `j` replaced by `k` in the keys. -/
def setJ (j : Fin nx) (k : XKey) (keys : Keys nx ns) : Keys nx ns := ⟨updJ j k keys.xmss, keys.sphincs⟩

/-- An outcome whose keys have key `j` replaced. -/
def holeOut (j : Fin nx) (k : XKey) (z : GameOutcome nx ns × Log) : GameOutcome nx ns × Log :=
  (withKeys (setJ j k z.1.keys) z.1, z.2)

/-- The routed rest's outcome reads its keys: a map of it is decided on the keys it was given. -/
theorem map_route_gameRest_congr (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (Pr : List UInt8 → Prop) [DecidablePred Pr] (keys : Keys nx ns)
    {β : Type} (f g : GameOutcome nx ns × Log → β)
    (h : ∀ z : GameOutcome nx ns × Log, z.1.keys = keys → f z = g z) :
    f <$> simulateQ (routeImpl Pr) (gameRest guest fuel budget A keys) =
      g <$> simulateQ (routeImpl Pr) (gameRest guest fuel budget A keys) := by
  unfold gameRest
  simp only [simulateQ_bind, simulateQ_pure, map_bind, map_pure]
  exact bind_congr fun q ↦ bind_congr fun q' ↦ congrArg pure (h _ rfl)

omit [Sphincs.Params] in
/-- `ΦJ` of a key position. -/
theorem ΦJ_ite (sk : LeanXmss.Seeded.SecretKey) {α : Type} (p : Prop) [Decidable p] (a : α)
    (x : RM α) : ΦJ sk (if p then pure a else x) = if p then pure a else ΦJ sk x := by
  split
  · exact ΦJ_pure sk a
  · rfl

omit [Sphincs.Params] in
/-- Events after a common draw, its continuations agreeing on its possible outputs. -/
theorem prEvent_bind_congr_supp {α β γ : Type} (oa : ProbComp α) (f : α → ProbComp β)
    (g : α → ProbComp γ) (p : β → Prop) (q : γ → Prop)
    (h : ∀ x ∈ support oa, Pr{let y ← f x}[p y] = Pr{let y ← g x}[q y]) :
    Pr{let y ← oa >>= f}[p y] = Pr{let y ← oa >>= g}[q y] := by
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
  refine tsum_congr fun x ↦ ?_
  by_cases hx : x ∈ support oa
  · rw [h x hx]
  · have h0 : Pr{let z ← oa}[z = x] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hzx ↦ hx (hzx ▸ hz)
    rw [h0, zero_mul, zero_mul]

omit [Sphincs.Params] in
/-- A pure position of a sequence holds its value: the sequence is its own update there. -/
theorem sequenceFin_slot_self {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} {n : ℕ}
    (j : Fin n) (x : α) (c : Fin n → m α) :
    LeanXmss.Concrete.sequenceFin (fun i ↦ if i = j then pure x else c i) =
      LeanXmss.Concrete.sequenceFin (fun i ↦ if i = j then pure x else c i) >>= fun keys ↦
        pure (fun i ↦ if i = j then x else keys i) := by
  rw [sequenceFin_slot' j x x c pure, bind_pure]

/-- The class-routed game's keys hold key `j`'s value. -/
theorem gKeys_slot (pj : Bytes) (j : Fin nx) (kj' : XKey) (cp : QueryCache LeanXmss.HashSpec)
    (z : ((Fin nx → XKey) × (Fin ns → SKey)) × QueryCache LeanXmss.HashSpec)
    (hz : z ∈ support ((gKeys pj j kj').run cp)) : z.1.1 j = kj' := by
  unfold gKeys at hz
  rw [sequenceFin_slot_self j kj'] at hz
  simp only [bind_assoc, pure_bind, StateT.run_bind, mem_support_bind_iff, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, -, r', -, hz⟩ := hz
  rw [hz]
  simp

/-- The reduction's rest keeps its keys. -/
theorem ΦJ_restJ_keys (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) (j : Fin nx) (keys : Keys nx ns)
    (cp : QueryCache LeanXmss.HashSpec) (z : XmssRed.BOut nx ns × QueryCache LeanXmss.HashSpec)
    (hz : z ∈ support ((ΦJ sk (restJ guest fuel budget A pj j keys)).run cp)) : z.1.1 = keys := by
  unfold restJ at hz
  simp only [ΦJ_bind, ΦJ_pure, StateT.run_bind, mem_support_bind_iff, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, -, r', -, hz⟩ := hz
  rw [hz]

omit [Sphincs.Params] in
/-- Replacing a position twice keeps the last. -/
theorem updJ_updJ (j : Fin nx) (k k' : XKey) (v : Fin nx → XKey) :
    updJ j k (updJ j k' v) = updJ j k v := by
  funext i; unfold updJ; split <;> rfl

omit [Sphincs.Params] in
/-- Replacing a position by its value is the identity. -/
theorem updJ_self (j : Fin nx) (v : Fin nx → XKey) : updJ j (v j) v = v := by
  funext i; unfold updJ; split <;> simp_all

/-- **The reduction's view.** The class-routed game after key `j` (key `j`'s secret key replaced by
the reduction's hole key) and the reduction's run under the game's oracles give every event that
forces good keys the same probability. -/
theorem prEvent_view (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (sk : LeanXmss.Seeded.SecretKey) (pkj : LeanXmss.PublicKey) (hsk : sk.parameter = pkj.parameter)
    (j : Fin nx) (ev : GameOutcome nx ns × Log → QueryCache LeanXmss.HashSpec →
      QueryCache LeanXmss.HashSpec → Prop)
    (hev : ∀ z cp c, ev z cp c → GoodKeys (LeanXmss.bytesLE 16 sk.parameter) j (pkj, holeKey pkj)
      (z.1.keys.xmss, z.1.keys.sphincs))
    (cp c : QueryCache LeanXmss.HashSpec) :
    Pr{let z ← romRun ((holeOut j (pkj, holeKey pkj) <$> simulateQ (routeImpl
        (PrivJ (LeanXmss.bytesLE 16 sk.parameter))) (RJ guest fuel budget A j (pkj, sk))).run cp) c}[
        ev z.1.1 z.1.2 z.2] =
      Pr{let z ← romRun ((outJ <$> ΦJ sk (xBodyJ guest fuel budget A j pkj)).run cp) c}[
        ev z.1.1 z.1.2 z.2] := by
  set pj := LeanXmss.bytesLE 16 sk.parameter with hpjdef
  have hpj : pj.length = 16 := length_bytesLE16_x _
  have hpjk : pjOf pkj = pj := by rw [pjOf, hpjdef, hsk]
  set kj' : XKey := (pkj, holeKey pkj) with hkj'
  -- the continuations
  let G' : (Fin nx → XKey) × (Fin ns → SKey) → PM (GameOutcome nx ns × Log) := fun p ↦
    holeOut j kj' <$> simulateQ (routeImpl (PrivJ pj))
      (gameRest guest fuel budget A ⟨updJ j (pkj, sk) p.1, p.2⟩)
  let k : (Fin nx → XKey) × (Fin ns → SKey) → PM (GameOutcome nx ns × Log) := fun p ↦
    (fun z ↦ (withKeys ⟨p.1, p.2⟩ z.1, z.2)) <$> simulateQ (routeImpl (PrivJ pj))
      (gameRest guest fuel budget A ⟨updJ j (pkj, sk) p.1, p.2⟩)
  let k' : (Fin nx → XKey) × (Fin ns → SKey) → PM (GameOutcome nx ns × Log) := fun p ↦
    outJ <$> ΦJ sk (restJ guest fuel budget A pj j ⟨p.1, p.2⟩)
  -- the game side is the keys, then `G'`
  have hL : holeOut j kj' <$> simulateQ (routeImpl (PrivJ pj)) (RJ guest fuel budget A j (pkj, sk)) =
      gKeys pj j kj' >>= G' := by
    unfold RJ gKeys
    simp only [simulateQ_bind, Xmss.simulateQ_sequenceFin, map_bind, bind_assoc, pure_bind, G']
    have hite : (fun i : Fin nx ↦ simulateQ (routeImpl (PrivJ pj))
        (if i = j then pure (pkj, sk) else (LeanXmss.MultiUser.keygen : OracleComp OW _))) =
        fun i ↦ if i = j then pure (pkj, sk)
          else simulateQ (routeImpl (PrivJ pj)) (LeanXmss.MultiUser.keygen : OracleComp OW _) := by
      funext i; split <;> simp
    rw [hite, ← sequenceFin_slot' j kj' (pkj, sk)]
    rfl
  -- the reduction side is the keys, then `k'`
  have hR : outJ <$> ΦJ sk (xBodyJ guest fuel budget A j pkj) = rKeys sk pj j kj' >>= k' := by
    unfold xBodyJ rKeys
    simp only [ΦJ_bind, morph_sequenceFin (isMorphism_ΦJ sk), ΦJ_ite, map_bind, bind_assoc,
      pure_bind, k', hpjk]
    rfl
  -- `G'` is `k` on the game's possible keys
  have hGk : Pr{let z ← romRun ((gKeys pj j kj' >>= G').run cp) c}[ev z.1.1 z.1.2 z.2] =
      Pr{let z ← romRun ((gKeys pj j kj' >>= k).run cp) c}[ev z.1.1 z.1.2 z.2] := by
    rw [romRun_pm_bind, romRun_pm_bind]
    refine prEvent_bind_congr_supp _ _ _ _ _ fun r hr ↦ ?_
    have hslot := gKeys_slot pj j kj' cp r.1 (fst_mem_support_of_mem_romRun hr)
    have hG : G' r.1.1 = k r.1.1 := by
      refine map_route_gameRest_congr guest fuel budget A _ _ _ _ fun z hz ↦ ?_
      simp only [holeOut, setJ, hz, updJ_updJ]
      rw [← hslot, updJ_self]
    rw [hG]
  rw [hL, hR, hGk]
  refine prEvent_eq_of_agreeOn (agreeOn_keys sk pj hpj j kj') k k' (fun p hp ↦ ?_)
    (fun z ↦ (z.1.keys.xmss, z.1.keys.sphincs)) (fun p cp z hz ↦ ?_) (fun p cp z hz ↦ ?_) ev
    (fun z cp c he ↦ hev z cp c he) cp c
  · -- the continuations agree on good keys
    have hj : p.1 j = kj' := (hp.1 j).1 rfl
    have hx : ∀ i, i ≠ j → p.1 i = updJ j (pkj, sk) p.1 i := fun i hi ↦ by
      simp [updJ, hi]
    have hgood : GoodJ pj j (⟨updJ j (pkj, sk) p.1, p.2⟩ : Keys nx ns) :=
      ⟨fun i hi ↦ by dsimp only; rw [← hx i hi]; exact (hp.1 i).2 hi, hp.2⟩
    have h := map_ΦJ_restJ guest fuel budget A sk j ⟨p.1, p.2⟩ ⟨updJ j (pkj, sk) p.1, p.2⟩ hx rfl
      (by simp [updJ]) (by dsimp only; rw [hj]; simp [updJ, hkj']) hgood
    exact h.symm
  · -- `k` keeps its keys
    simp only [k, StateT.run_map, support_map, Set.mem_image] at hz
    obtain ⟨w, -, rfl⟩ := hz
    rfl
  · -- `k'` keeps its keys
    simp only [k', StateT.run_map, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have := ΦJ_restJ_keys guest fuel budget A sk pj j ⟨p.1, p.2⟩ cp w hw
    simp only [outJ, this]

end PerKeyX

end
end LeanVM.E2E
