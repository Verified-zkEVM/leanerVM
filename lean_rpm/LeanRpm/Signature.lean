import LeanRpm.Keccak
import LeanRpm.Lemmas
import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Signature games in the random-permutation model

The SUF-CMA game of a hash-based signature scheme whose hash `H : List UInt8 → D` returns a
digest type `D` in bijection with the 32 bytes of Keccak-256 (`e : KDigest ≃ D`), as in
leanXMSS and leanSPHINCS (`D = BitVec 256`, the bytes read little endian: `digestBitVec`).

* **The ROM game** (`romGame`, `romExperiment`): a seed sampled, keys generated from it, the
  adversary run with the hash and a signing oracle that logs its requests, the forgery verified,
  all hashing through one random oracle; the experiment counts every hash call, cache hits
  included. These are the games of `lean_xmss` and `lean_sphincs`, written for any scheme.
* **The RPM game** (`rpmGame`, `rpmExperiment`): the same game where `H` is Keccak-256, the sponge
  over the random permutation `π` read through `e`, and the adversary also queries `π` and `π⁻¹`
  (and Keccak-256 itself).

`rpm_le_rom`: for an RPM adversary `A`, the ROM adversary `romAdv A` (`A` with its permutation
queries answered by the indifferentiability simulator) wins the ROM game with probability at least
`A`'s RPM probability minus `Q² / 2^509`, where `Q` bounds the permutation calls of the RPM game
(`permCalls`: a hash of `n` bytes costs `⌊n / 136⌋ + 1`, a call of `π` or `π⁻¹` one), and its
experiment makes at most `q` hash calls whenever the RPM game makes at most `q` calls of `H`, `π`
and `π⁻¹` in all (`oracleCalls`). Both budgets bound every path of the game, whatever the
answers (`IsWeightBound`). A ROM bound `q / 2^b` therefore gives the RPM bound
`q / 2^b + Q² / 2^509` (`rpm_bound`).

The signing oracle runs inside the adversary's phase: the transfer (`keccak256_transfer`) takes as
its adversary the RPM adversary together with the signer, whose secret key comes from the honest
key generation before it, so the ROM adversary is the RPM adversary with the simulator, and the
signing oracle stays the game's.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace LeanRpm.SufCma

/-! ## Digests as bit vectors -/

/-- **The digest bytes as a bit vector**, little endian: byte `i` is bits `8 i … 8 i + 7`
(`digestBitVec_extract`). -/
def digestBitVec : KDigest ≃ BitVec 256 :=
  (arrayVectorEquivFin UInt8 32).trans <|
    (Equiv.arrowCongr (Equiv.refl _) uInt8EquivFin).trans <|
      finFunctionFinEquiv.trans <| (finCongr (show 256 ^ 32 = 2 ^ 256 by norm_num)).trans
        ⟨BitVec.ofFin, BitVec.toFin, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Bits `8 i … 8 i + 7` of a digest's bit vector are its byte `i`. -/
theorem digestBitVec_symm_getElem (b : BitVec 256) (i : Fin 32) :
    (digestBitVec.symm b)[i] = UInt8.ofBitVec (b.extractLsb' (8 * i) 8) := by
  apply UInt8.toNat_inj.mp
  simp only [digestBitVec, Equiv.symm_trans_apply, uInt8EquivFin, arrayVectorEquivFin]
  simp
  change ((finFunctionFinEquiv (m := 256) (n := 32)).symm b.toFin i : ℕ) = _
  rw [finFunctionFinEquiv_symm_apply_val, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

/-- Bits `8 i … 8 i + 7` of a digest's bit vector are its byte `i`. -/
theorem digestBitVec_extract (d : KDigest) (i : Fin 32) :
    (digestBitVec d).extractLsb' (8 * i) 8 = d[i].toBitVec := by
  have h := digestBitVec_symm_getElem (digestBitVec d) i
  rw [Equiv.symm_apply_apply] at h
  rw [h]

/-! ## Two simulations commute -/

section Commute

variable {ι ι₁ ι₂ ι₃ ι₄ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁}
  {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄} {σ L α : Type}
  [EmptyCollection L] [Append L] [LawfulAppend L]

/-- **A state layer and a writer layer commute.** Simulating with a stateful `f₁` then a writer
`g₁` (then `h₁`) is simulating with a writer `f₂` then a stateful `g₂`, when it is so query by
query. -/
theorem simulateQ_state_writer_comm
    (f₁ : QueryImpl spec (StateT σ (OracleComp spec₁)))
    (g₁ : QueryImpl spec₁ (WriterT L (OracleComp spec₂)))
    (h₁ : QueryImpl spec₂ (OracleComp spec₃))
    (f₂ : QueryImpl spec (WriterT L (OracleComp spec₄)))
    (g₂ : QueryImpl spec₄ (StateT σ (OracleComp spec₃)))
    (hstep : ∀ t s, simulateQ h₁ ((simulateQ g₁ ((f₁ t).run s)).run) =
      (fun z ↦ ((z.1.1, z.2), z.1.2)) <$> (simulateQ g₂ ((f₂ t).run)).run s)
    (oa : OracleComp spec α) (s : σ) :
    simulateQ h₁ ((simulateQ g₁ ((simulateQ f₁ oa).run s)).run) =
      (fun z ↦ ((z.1.1, z.2), z.1.2)) <$> (simulateQ g₂ ((simulateQ f₂ oa).run)).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, WriterT.run_bind', map_bind]
    rw [hstep, bind_map_left]
    refine bind_congr fun z ↦ ?_
    rw [simulateQ_map, ih, simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]
    rfl

end Commute

/-! ## The games -/

/-- The oracles of the random-permutation model: coins, Keccak-256 `H`, `π` and `π⁻¹`. -/
abbrev KSpec := dSpec (List UInt8) KDigest KState

/-- The random oracle of the transfer: byte strings to Keccak-256 digests. -/
abbrev KRom := unifSpec + roSpec (List UInt8) KDigest

/-- A hash `List UInt8 → D`. -/
abbrev HSpec (D : Type) := List UInt8 →ₒ D

/-- Coins and the hash. -/
abbrev World (D : Type) := unifSpec + HSpec D

/-- **A signature scheme** with hash `H : List UInt8 → D`: a seed sampler, key generation from a
seed, the signer answering a request `Req` with `Resp`, the verifier of a claimed forgery `F`, and
the winning condition on the signing transcript and the forgery. -/
structure Scheme (D Seed PK SK Req Resp F : Type) where
  /-- Sample the secret seed. -/
  sample : ProbComp Seed
  /-- Generate the keys from the seed. -/
  keygen : Seed → OracleComp (HSpec D) (PK × SK)
  /-- Answer a signing request. -/
  sign : SK → Req → OracleComp (HSpec D) Resp
  /-- Verify a claimed forgery. -/
  verify : PK → F → OracleComp (HSpec D) Bool
  /-- The transcript and the forgery make a win (when the forgery verifies). -/
  win : QueryLog (Req →ₒ Resp) → F → Bool

variable {D Seed PK SK Req Resp F : Type}

/-- The signing oracle: answer a request with the signer, and log it. -/
def signingOracle (S : Scheme D Seed PK SK Req Resp F) (sk : SK) :
    QueryImpl (Req →ₒ Resp) (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp (World D))) :=
  QueryImpl.withLogging fun r ↦ liftM (S.sign sk r : OracleComp (HSpec D) Resp)

/-- **The ROM game**: sample the seed, generate the keys, run the adversary with the hash and a
logging signing oracle, verify its forgery. -/
noncomputable def romGame (S : Scheme D Seed PK SK Req Resp F)
    (main : PK → OracleComp (World D + (Req →ₒ Resp)) F) : OracleComp (World D) Bool := do
  let seed ← liftM S.sample
  let (pk, sk) ← liftM (S.keygen seed)
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ (QueryImpl.ofLift (World D)
      (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp (World D))) + signingOracle S sk)
      (main pk)).run
  let verified ← liftM (S.verify pk forgery)
  return S.win log forgery && verified

variable [SampleableType D]

/-- The random oracle with every hash call counted, cache hits included. -/
noncomputable def countedImpl :=
  (unifFwdImpl (HSpec D) +
    (randomOracle : QueryImpl (HSpec D) (StateT (QueryCache (HSpec D)) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- **The ROM experiment**: the ROM game in the random oracle model, with its hash calls. -/
noncomputable def romExperiment (S : Scheme D Seed PK SK Req Resp F)
    (main : PK → OracleComp (World D + (Req →ₒ Resp)) F) : ProbComp (Bool × Nat) :=
  (simulateQ countedImpl (romGame S main)).run.run' ∅

variable (e : KDigest ≃ D)

/-- The hash as Keccak-256 read through `e`, in the random-permutation model. -/
def hashK : QueryImpl (HSpec D) (OracleComp KSpec) :=
  fun m ↦ e <$> (liftM (KSpec.query (.inr (.inl m))) : OracleComp KSpec KDigest)

/-- The signing oracle in the random-permutation model. -/
def signingOracleK (S : Scheme D Seed PK SK Req Resp F) (sk : SK) :
    QueryImpl (Req →ₒ Resp) (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpec)) :=
  QueryImpl.withLogging fun r ↦ simulateQ (hashK e) (S.sign sk r)

/-- **The RPM game**: the game with `H` Keccak-256 over the permutation, read through `e`, and
an adversary that also queries Keccak-256, `π` and `π⁻¹`. -/
noncomputable def rpmGame (S : Scheme D Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) : OracleComp KSpec Bool := do
  let seed ← liftM S.sample
  let (pk, sk) ← simulateQ (hashK e) (S.keygen seed)
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ (QueryImpl.ofLift KSpec (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpec)) +
      signingOracleK e S sk) (main pk)).run
  let verified ← simulateQ (hashK e) (S.verify pk forgery)
  return S.win log forgery && verified

/-- **The RPM experiment**: the RPM game against the lazily sampled random permutation. -/
noncomputable def rpmExperiment (S : Scheme D Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) : ProbComp Bool :=
  realGame keccakPadding KState.zero (rpmGame e S main)

/-- Calls of `H`, `π` and `π⁻¹`, one each. -/
def oracleCalls : KSpec.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- **Calls of the permutation**: a hash of `n` bytes costs `⌊n / 136⌋ + 1` (one per block of the
padded message), a call of `π` or `π⁻¹` one. -/
def permCalls : KSpec.Domain → ℕ
  | .inl _ => 0
  | .inr (.inl m) => m.length / 136 + 1
  | .inr (.inr _) => 1

/-- The permutation calls are the cost of the transfer. -/
theorem permCalls_eq : permCalls = queryCost (Dg := KDigest) (St := KState) keccakPadding := by
  funext t
  rcases t with n | m | q
  · rfl
  · exact (keccakPad_length m).symm
  · rfl

/-! ## The ROM adversary -/

/-- The hash as the transfer's random oracle read through `e`. -/
def hashR : QueryImpl (HSpec D) (OracleComp KRom) :=
  fun m ↦ e <$> (liftM (KRom.query (.inr m)) : OracleComp KRom KDigest)

/-- The scheme's oracles in the transfer's random-oracle model: coins, and `H` read through
`e`. -/
def toK : QueryImpl (World D) (OracleComp KRom)
  | .inl n => liftM (KRom.query (.inl n))
  | .inr m => hashR e m

/-- The transfer's oracles from the scheme's: coins, and `H` read back through `e⁻¹`. -/
def ofK : QueryImpl KRom (OracleComp (World D))
  | .inl n => liftM ((World D).query (.inl n))
  | .inr m => e.symm <$> (liftM ((World D).query (.inr m)) : OracleComp (World D) D)

/-- The transfer's oracles from the scheme's, with signing requests: coins, and `H` read back
through `e⁻¹`. -/
def ofKS : QueryImpl KRom (OracleComp (World D + (Req →ₒ Resp)))
  | .inl n => liftM ((World D + (Req →ₒ Resp)).query (.inl (.inl n)))
  | .inr m => e.symm <$>
      (liftM ((World D + (Req →ₒ Resp)).query (.inl (.inr m))) : OracleComp (World D + (Req →ₒ Resp)) D)

/-- The RPM adversary's oracles from the scheme's ROM oracles: its coins, Keccak-256, `π` and
`π⁻¹` as in the ideal world of indifferentiability (`H` read back through `e⁻¹`, the permutation
answered by the simulator), its signing requests forwarded. -/
noncomputable def simAdv :
    QueryImpl (KSpec + (Req →ₒ Resp))
      (StateT (SimState KDigest KRest KCap) (OracleComp (World D + (Req →ₒ Resp))))
  | .inl t => StateT.mk fun σ ↦ simulateQ (ofKS e) ((idealImpl keccakPadding t).run σ)
  | .inr r => liftM ((World D + (Req →ₒ Resp)).query (.inr r))

/-- **The ROM adversary of an RPM adversary**: its permutation queries answered by the
simulator, from its initial state. -/
noncomputable def romAdv (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) (pk : PK) :
    OracleComp (World D + (Req →ₒ Resp)) F :=
  (simulateQ (simAdv e) (main pk)).run' (SimState.init KState.zero)

theorem simulateQ_toK_ofK {β : Type} (X : OracleComp KRom β) :
    simulateQ (toK e) (simulateQ (ofK e) X) = X := by
  rw [← QueryImpl.simulateQ_compose]
  conv_rhs => rw [← simulateQ_id' X]
  congr 1
  funext t
  rcases t with n | m
  · simp [ofK, toK]
  · simp [ofK, toK, hashR]

/-- The hash of the RPM game is that of the transfer's ROM, lifted. -/
theorem simulateQ_hashK {β : Type} (X : OracleComp (HSpec D) β) :
    simulateQ (hashK e) X = liftH (E := KRest) (C := KCap) (simulateQ (hashR e) X) := by
  rw [liftH, ← QueryImpl.simulateQ_compose]
  congr 1

/-- A query lifted into a writer writes nothing. -/
theorem run_liftM_query_writer {ι : Type} {spec : OracleSpec ι} {L : Type} [EmptyCollection L]
    [Append L] (t : spec.Domain) :
    (liftM (spec.query t) : WriterT L (OracleComp spec) _).run =
      (·, ∅) <$> (liftM (spec.query t) : OracleComp spec _) := rfl

/-- A simulation whose every step writes nothing writes nothing. -/
theorem run_simulateQ_writer_of_run {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {L β : Type} [EmptyCollection L] [Append L] [LawfulAppend L]
    (impl : QueryImpl spec (WriterT L (OracleComp spec'))) (j : QueryImpl spec (OracleComp spec'))
    (h : ∀ t, (impl t).run = (·, ∅) <$> j t) (X : OracleComp spec β) :
    (simulateQ impl X).run = (·, ∅) <$> simulateQ j X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, WriterT.run_bind', h, ih, bind_map_left, map_bind,
      Functor.map_map]
    simp

/-- A computation of the scheme's oracles run as a writer that logs nothing. -/
theorem run_simulateQ_ofLift_writer {ι : Type} {spec : OracleSpec ι} {L β : Type}
    [EmptyCollection L] [Append L] [LawfulAppend L] (X : OracleComp spec β) :
    (simulateQ (QueryImpl.ofLift spec (WriterT L (OracleComp spec))) X).run = (·, ∅) <$> X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, WriterT.run_bind', QueryImpl.ofLift_apply]
    have : (liftM (spec.query t) : WriterT L (OracleComp spec) _).run =
        (·, ∅) <$> (liftM (spec.query t) : OracleComp spec _) := rfl
    simp [this, ih, map_bind]

/-- **The ROM adversary against the game's signing oracle is the simulated RPM adversary with
the signer**: the ROM game's middle phase, its hash read as the transfer's random oracle, is the
ideal world of the RPM game's middle phase. -/
theorem toK_middle (S : Scheme D Seed PK SK Req Resp F) (sk : SK) {α : Type}
    (oa : OracleComp (KSpec + (Req →ₒ Resp)) α) (σ : SimState KDigest KRest KCap) :
    simulateQ (toK e) ((simulateQ (QueryImpl.ofLift (World D)
      (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp (World D))) + signingOracle S sk)
        ((simulateQ (simAdv e) oa).run σ)).run) =
      (fun z ↦ ((z.1.1, z.2), z.1.2)) <$> (simulateQ (idealImpl keccakPadding)
        ((simulateQ (QueryImpl.ofLift KSpec (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpec)) +
          signingOracleK e S sk) oa).run)).run σ := by
  refine simulateQ_state_writer_comm _ _ _ _ _ (fun t s ↦ ?_) oa σ
  rcases t with t | r
  · have h1 : (simAdv (Req := Req) (Resp := Resp) e (.inl t)).run s =
        simulateQ (ofKS e) ((idealImpl keccakPadding t).run s) := rfl
    have h3 : ∀ u, (((QueryImpl.ofLift (World D)
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp (World D))) + signingOracle S sk) ∘ₛ
          ofKS e) u).run = (·, ∅) <$> ofK e u := by
      intro u
      rcases u with n | m
      · rfl
      · simp [ofKS, ofK, run_liftM_query_writer, Functor.map_map]
    have h2 : ((QueryImpl.ofLift KSpec (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpec)) +
        signingOracleK e S sk) (.inl t)).run =
          (·, ∅) <$> (liftM (KSpec.query t) : OracleComp KSpec _) := rfl
    rw [h1, ← QueryImpl.simulateQ_compose, run_simulateQ_writer_of_run _ _ h3, simulateQ_map,
      simulateQ_toK_ofK, h2, simulateQ_map, StateT.run_map, Functor.map_map,
      simulateQ_spec_query]
    rfl
  · have h1 : (simAdv (Req := Req) (Resp := Resp) e (.inr r)).run s =
        (fun u ↦ (u, s)) <$>
          (liftM ((World D + (Req →ₒ Resp)).query (.inr r)) : OracleComp _ Resp) := by
      simp [simAdv]
    have h2 : ((QueryImpl.ofLift (World D)
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp (World D))) + signingOracle S sk)
          (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
            (liftM (S.sign sk r : OracleComp (HSpec D) Resp) : OracleComp (World D) Resp) := by
      simp [signingOracle]
    have h3 : ((QueryImpl.ofLift KSpec (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpec)) +
        signingOracleK e S sk) (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
          simulateQ (hashK e) (S.sign sk r) := by
      simp [signingOracleK]
    have h4 : simulateQ (toK e)
        (liftM (S.sign sk r : OracleComp (HSpec D) Resp) : OracleComp (World D) Resp) =
          simulateQ (hashR e) (S.sign sk r) :=
      QueryImpl.simulateQ_liftComp_right_eq_of_apply (toK e) (hashR e) (fun _ ↦ rfl) _
    rw [h1, simulateQ_map, simulateQ_spec_query, WriterT.run_map', h2, h3, simulateQ_map,
      simulateQ_map, simulateQ_map, h4, simulateQ_hashK, StateT.run_map, run_idealImpl_liftH,
      Functor.map_map, Functor.map_map, Functor.map_map]
    rfl

/-! ## The games in the shape of the transfer -/

/-- The honest part before the adversary: the seed and the keys, hashing in the transfer's
ROM. -/
noncomputable def preR (S : Scheme D Seed PK SK Req Resp F) : OracleComp KRom (PK × SK) := do
  let seed ← liftM S.sample
  simulateQ (hashR e) (S.keygen seed)

/-- The adversary of the transfer: the RPM adversary with the signing oracle. -/
noncomputable def advK (S : Scheme D Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) (x : PK × SK) :
    OracleComp KSpec (F × QueryLog (Req →ₒ Resp)) :=
  (simulateQ (QueryImpl.ofLift KSpec (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpec)) +
    signingOracleK e S x.2) (main x.1)).run

/-- The honest part after the adversary: verify the forgery, hashing in the transfer's ROM. -/
noncomputable def postR (S : Scheme D Seed PK SK Req Resp F) (x : PK × SK)
    (a : F × QueryLog (Req →ₒ Resp)) : OracleComp KRom Bool := do
  let verified ← simulateQ (hashR e) (S.verify x.1 a.1)
  return S.win a.2 a.1 && verified

/-- A coin computation, lifted. -/
theorem liftH_liftM {β : Type} (p : ProbComp β) :
    liftH (E := KRest) (C := KCap) (liftM p : OracleComp KRom β) = (liftM p : OracleComp KSpec β) := by
  change simulateQ hEmbed (OracleComp.liftComp p _) = OracleComp.liftComp p _
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply hEmbed (fun n ↦ hEmbed (.inl n))
    (fun _ ↦ rfl), OracleComp.liftComp_def]
  rfl

/-- **The RPM game has the transfer's shape.** -/
theorem rpmGame_eq (S : Scheme D Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) :
    rpmGame e S main = LeanRpm.rpmGame (preR e S) (advK e S main) (postR e S) := by
  have h1 := liftH_liftM S.sample
  have h2 := simulateQ_hashK e (D := D) (β := Bool)
  have h3 := simulateQ_hashK e (D := D) (β := PK × SK)
  simp only [liftH] at h1 h2 h3
  simp only [rpmGame, LeanRpm.rpmGame, preR, postR, advK, liftH, simulateQ_bind, bind_assoc,
    h1, ← h2, ← h3, simulateQ_pure]

/-- Coins, read in the transfer's ROM. -/
theorem simulateQ_toK_liftM_probComp {β : Type} (p : ProbComp β) :
    simulateQ (toK e) (liftM p : OracleComp (World D) β) = (liftM p : OracleComp KRom β) := by
  change simulateQ (toK e) (OracleComp.liftComp p _) = OracleComp.liftComp p _
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply (toK e) (fun n ↦ toK e (.inl n))
    (fun _ ↦ rfl), OracleComp.liftComp_def]
  rfl

/-- The scheme's hashing, read in the transfer's ROM. -/
theorem simulateQ_toK_liftM_hash {β : Type} (X : OracleComp (HSpec D) β) :
    simulateQ (toK e) (liftM X : OracleComp (World D) β) = simulateQ (hashR e) X :=
  QueryImpl.simulateQ_liftComp_right_eq_of_apply (toK e) (hashR e) (fun _ ↦ rfl) X

/-- **The ROM game against the ROM adversary is the ideal world of the RPM game**: read in the
transfer's ROM, it is the transfer's ROM game against `advS` of the RPM adversary with the
signer. -/
theorem simulateQ_toK_romGame (S : Scheme D Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) :
    simulateQ (toK e) (romGame S (romAdv e main)) =
      preR e S >>= fun x ↦ advS keccakPadding KState.zero (advK e S main x) >>= fun a ↦
        postR e S x a := by
  simp only [romGame, preR, postR, advK, advS, romAdv, simulateQ_bind, bind_assoc,
    simulateQ_toK_liftM_probComp, simulateQ_toK_liftM_hash, simulateQ_pure, StateT.run'_eq,
    simulateQ_map, WriterT.run_map']
  refine bind_congr fun seed ↦ bind_congr fun x ↦ ?_
  rw [toK_middle, Functor.map_map]
  rfl

/-! ## A random oracle read through a bijection is a random oracle -/

/-- A cache of the transfer's random oracle, read through `e`. -/
def cacheMap (c : (roSpec (List UInt8) KDigest).QueryCache) : (HSpec D).QueryCache :=
  QueryCache.ofFn fun m ↦ (c m).map e

theorem cacheMap_cacheQuery (c : (roSpec (List UInt8) KDigest).QueryCache) (m : List UInt8)
    (u : KDigest) : cacheMap e (c.cacheQuery m u) = (cacheMap e c).cacheQuery m (e u) := by
  refine QueryCache.ext fun m' ↦ ?_
  by_cases h : m' = m
  · subst h; simp [cacheMap]
  · have := QueryCache.cacheQuery_of_ne c u h
    simp only [cacheMap, QueryCache.ofFn_apply]
    rw [QueryCache.cacheQuery_of_ne _ _ h, this]
    rfl

/-- **The random oracle read through `e` is the random oracle on `D`**: running a game of the
scheme's oracles in the transfer's ROM, its hash read through `e`, gives the game's ROM
distribution. -/
theorem romRun_toK {β : Type} (Y : OracleComp (World D) β) :
    romRun (simulateQ (toK e) Y) =ᵈ (simulateQ (HSpec D).romImpl Y).run' ∅ := by
  have h0 : cacheMap e (∅ : (roSpec (List UInt8) KDigest).QueryCache) = ∅ := by
    exact QueryCache.ext fun _ ↦ rfl
  rw [romRun, ← QueryImpl.simulateQ_compose, ← h0]
  refine run'_simulateQ_evalDistEq_of_inv _ _ (fun _ ↦ True) (cacheMap e)
    (fun _ _ _ _ _ ↦ trivial) (fun t c _ ↦ ?_) Y ∅ trivial
  rcases t with n | m
  · have h1 : ∀ {ι : Type} {sp : OracleSpec ι} (c : sp.QueryCache),
        (unifFwdImpl sp n).run c = (·, c) <$> (unifSpec.query n : ProbComp _) := fun c ↦ by
      simpa using unifFwdImpl.simulateQ_run (unifSpec.query n : ProbComp _) c
    simp only [QueryImpl.apply_compose, toK]
    simp only [simulateQ_spec_query, QueryImpl.add_apply_inl, h1, Functor.map_map]
    exact EvalDistEq.rfl
  · simp only [QueryImpl.apply_compose, toK, hashR, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, Functor.map_map]
    rw [OracleSpec.romImpl_apply_inr, OracleSpec.romImpl_apply_inr, randomOracle.run_eq,
      randomOracle.run_eq]
    cases h : c m with
    | some v =>
      have h' : cacheMap e c m = some (e v) := by simp [cacheMap, h]
      simp only [h']
      simp
    | none =>
      have h' : cacheMap e c m = none := by simp [cacheMap, h]
      simp only [h']
      simp only [map_bind, map_pure, Prod.map, id, cacheMap_cacheQuery]
      refine EvalDistEq.trans ?_ (EvalDistEq.bind_left
        (SampleableType.map_uniformSample_evalDistEq_of_bijective e.bijective)
        (fun u ↦ (pure (u, (cacheMap e c).cacheQuery m u) : ProbComp _)))
      rw [bind_map_left]

/-! ## Hash calls -/

/-- Hash calls of the transfer's ROM, one each. -/
def romCalls : KRom.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- Hash calls of the scheme's ROM, one each. -/
def hashCalls : (World D).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- Coins make no hash call. -/
theorem isWeightBound_liftM_probComp_krom {β : Type} (p : ProbComp β) :
    IsWeightBound (liftM p : OracleComp KRom β) romCalls 0 :=
  isWeightBound_liftM_probComp romCalls (fun _ ↦ rfl) p

/-- **Each step of the ideal world makes at most one hash call**, none for a coin. -/
theorem isWeightBound_idealImpl (t : KSpec.Domain) (s : SimState KDigest KRest KCap) :
    IsWeightBound ((idealImpl keccakPadding t).run s) romCalls (oracleCalls t) := by
  have hu : IsWeightBound (liftM ($ᵗ KState) : OracleComp KRom KState) romCalls 0 :=
    isWeightBound_liftM_probComp_krom _
  rcases t with n | m | q
  · simp only [idealImpl, StateT.run_monadLift, monadLift_self]
    exact (isWeightBound_liftM_probComp_krom _).bind fun _ ↦ isWeightBound_pure _ _ 0
  · simp only [idealImpl, StateT.run_monadLift, monadLift_self]
    exact (isWeightBound_query romCalls (.inr m)).bind fun _ ↦ isWeightBound_pure _ _ 0
  · cases q with
    | fwd x =>
      simp only [idealImpl, simulator, StateT.run_mk]
      split
      · trivial
      · split
        · refine (IsWeightBound.bind (b := 0) ?_ fun _ ↦ isWeightBound_pure _ _ 0)
          unfold rootedAnswer
          split
          · exact ((isWeightBound_query romCalls (.inr _)).bind fun _ ↦
              (isWeightBound_liftM_probComp_krom _).bind fun _ ↦ isWeightBound_pure _ _ 0)
          · exact (isWeightBound_liftM_probComp_krom _).mono (Nat.zero_le _)
        · exact (hu.bind fun _ ↦ isWeightBound_pure _ _ 0).mono (Nat.zero_le _)
    | inv y =>
      simp only [idealImpl, simulator, StateT.run_mk]
      split
      · trivial
      · exact (hu.bind fun _ ↦ isWeightBound_pure _ _ 0).mono (Nat.zero_le _)

/-- A hash-call bound of a game read in the transfer's ROM is one of the game. -/
theorem isWeightBound_of_toK {β : Type} {Y : OracleComp (World D) β} {Q : ℕ}
    (h : IsWeightBound (simulateQ (toK e) Y) romCalls Q) : IsWeightBound Y (hashCalls (D := D)) Q := by
  induction Y using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map] at h
    rw [isWeightBound_query_bind_iff]
    rcases t with n | m
    · obtain ⟨h1, h2⟩ := (isWeightBound_query_bind_iff _ _ _ _).mp h
      exact ⟨h1, fun u ↦ ih u (h2 u)⟩
    · simp only [toK, hashR, bind_map_left] at h
      obtain ⟨h1, h2⟩ := (isWeightBound_query_bind_iff _ _ _ _).mp h
      refine ⟨h1, fun u ↦ ih u ?_⟩
      have := h2 (e.symm u)
      rwa [Equiv.apply_symm_apply] at this

/-- **The counted hash calls of a run are at most its bound.** -/
theorem count_le_of_isWeightBound {β : Type} {Y : OracleComp (World D) β} {Q : ℕ}
    (h : IsWeightBound Y (hashCalls (D := D)) Q) (c : (HSpec D).QueryCache) :
    ∀ z ∈ support ((simulateQ (countedImpl (D := D)) Y).run.run c),
      Multiplicative.toAdd z.1.2 ≤ Q := by
  induction Y using OracleComp.inductionOn generalizing Q c with
  | pure a =>
    intro z hz
    simp at hz
    subst hz
    exact Nat.zero_le _
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, WriterT.run_bind, StateT.run_bind] at hz
    simp only [countedImpl, QueryImpl.withAddCost_apply] at hz
    simp at hz
    obtain ⟨a, b, -, a1, a2, b1, h2, rfl⟩ := hz
    have h3 := ih a (h.2 a) b ((a1, Multiplicative.ofAdd a2), b1) (by simpa [countedImpl] using h2)
    have h4 := h.1
    rcases t with n | m
    · change 0 + a2 ≤ Q
      change a2 ≤ Q - 0 at h3
      omega
    · change 1 + a2 ≤ Q
      simp only [hashCalls] at h3 h4
      change a2 ≤ Q - 1 at h3
      omega

/-! ## The transfer of the game -/

/-- The ideal world of a game of the transfer's shape is its ROM game against `advS`. -/
theorem run'_idealImpl_rpmGame {β γ δ : Type} (pre : OracleComp KRom β)
    (A : β → OracleComp KSpec γ) (post : β → γ → OracleComp KRom δ) :
    (simulateQ (idealImpl keccakPadding) (LeanRpm.rpmGame pre A post)).run'
        (SimState.init KState.zero) =
      pre >>= fun x ↦ advS keccakPadding KState.zero (A x) >>= fun a ↦ post x a := by
  simp only [LeanRpm.rpmGame, advS, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    run_idealImpl_liftH, bind_map_left, map_bind, Functor.map_map]
  refine bind_congr fun x ↦ ?_
  simp

theorem fst_map_run_withAddCost {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] (impl : QueryImpl spec m) (c : spec.Domain → ℕ) {β : Type}
    (oa : OracleComp spec β) :
    Prod.fst <$> (simulateQ (impl.withAddCost c) oa).run = simulateQ impl oa :=
  QueryImpl.fst_map_run_withCost impl _ oa

/-- The ROM experiment's success, its counter dropped. -/
theorem prob_romExperiment (S : Scheme D Seed PK SK Req Resp F)
    (main : PK → OracleComp (World D + (Req →ₒ Resp)) F) :
    Pr{let r ← romExperiment S main}[r.1 = true] =
      Pr{let b ← (simulateQ (HSpec D).romImpl (romGame S main)).run' ∅}[b = true] := by
  have h2 : Prod.fst <$> romExperiment S main =
      (simulateQ (HSpec D).romImpl (romGame S main)).run' ∅ := by
    have h : Prod.fst <$> (simulateQ (countedImpl (D := D)) (romGame S main)).run =
        simulateQ (HSpec D).romImpl (romGame S main) := fst_map_run_withAddCost _ _ _
    rw [StateT.run'_eq, ← h, StateT.run_map, romExperiment, StateT.run'_eq, Functor.map_map]
    exact Functor.map_map _ _ _
  rw [← h2, prEvent_map]

/-- **The RPM game against the ROM game.** For an RPM adversary whose game makes at most `Q`
permutation calls (`permCalls`) and at most `q` calls of `H`, `π` and `π⁻¹` (`oracleCalls`) on
every path, the ROM adversary `romAdv e main` wins the ROM game with probability at least the RPM
one minus `Q² / 2^509`, and its ROM experiment makes at most `q` hash calls on every outcome. -/
theorem rpm_le_rom (S : Scheme D Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) (q Q : ℕ)
    (hq : IsWeightBound (rpmGame e S main) oracleCalls q)
    (hQ : IsWeightBound (rpmGame e S main) permCalls Q) :
    Pr{let b ← rpmExperiment e S main}[b = true] ≤
        Pr{let r ← romExperiment S (romAdv e main)}[r.1 = true] + (Q ^ 2 : ℝ≥0∞) / 2 ^ 509 ∧
      ∀ r ∈ support (romExperiment S (romAdv e main)), r.2 ≤ q := by
  rw [rpmGame_eq] at hq hQ
  rw [permCalls_eq] at hQ
  constructor
  · obtain ⟨h1, -⟩ := keccak256_transfer (preR e S) (advK e S main) (postR e S) Q hQ (· = true)
    rw [rpmExperiment, rpmGame_eq, prob_romExperiment, ← (romRun_toK e _).prEvent_eq,
      simulateQ_toK_romGame]
    exact h1
  · have h1 : IsWeightBound (simulateQ (toK e) (romGame S (romAdv e main))) romCalls q := by
      rw [simulateQ_toK_romGame, ← run'_idealImpl_rpmGame, StateT.run'_eq]
      exact isWeightBound_map _ (isWeightBound_run_simulateQ _ _ _ isWeightBound_idealImpl hq _)
    have h2 := count_le_of_isWeightBound (isWeightBound_of_toK e h1) ∅
    intro r hr
    rw [romExperiment, StateT.run'_eq] at hr
    erw [support_map] at hr
    obtain ⟨z, hz, rfl⟩ := hr
    exact h2 z hz

/-- **The RPM bound from a ROM bound.** If every ROM adversary whose experiment makes at most `q`
hash calls wins with probability at most `q / 2^bits` (`q ≥ 1`), then every RPM adversary whose
game makes at most `q ≥ 1` calls of `H`, `π` and `π⁻¹`, and at most `Q` permutation calls, on
every path, wins the RPM game with probability at most `q / 2^bits + Q² / 2^509`. -/
theorem rpm_bound (S : Scheme D Seed PK SK Req Resp F) (bits : ℕ)
    (hrom : ∀ q, 1 ≤ q → ∀ main : PK → OracleComp (World D + (Req →ₒ Resp)) F,
      (∀ r ∈ support (romExperiment S main), r.2 ≤ q) →
        Pr{let r ← romExperiment S main}[r.1 = true] ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞))
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) (q Q : ℕ) (hq1 : 1 ≤ q)
    (hq : IsWeightBound (rpmGame e S main) oracleCalls q)
    (hQ : IsWeightBound (rpmGame e S main) permCalls Q) :
    Pr{let b ← rpmExperiment e S main}[b = true] ≤
      q / ((2 ^ bits : ℕ) : ℝ≥0∞) + (Q ^ 2 : ℝ≥0∞) / 2 ^ 509 := by
  obtain ⟨h1, h2⟩ := rpm_le_rom e S main q Q hq hQ
  exact h1.trans (add_le_add (hrom q hq1 _ h2) le_rfl)

/-- A call of `H`, `π` or `π⁻¹` makes at least one permutation call. -/
theorem oracleCalls_le_permCalls (t : KSpec.Domain) : oracleCalls t ≤ permCalls t := by
  rcases t with n | m | q <;> simp [oracleCalls, permCalls]

/-- **The RPM bound in permutation calls alone**: `Q / 2^bits + Q² / 2^509` for an adversary
whose game makes at most `Q ≥ 1` permutation calls on every path. -/
theorem rpm_bound_perm (S : Scheme D Seed PK SK Req Resp F) (bits : ℕ)
    (hrom : ∀ q, 1 ≤ q → ∀ main : PK → OracleComp (World D + (Req →ₒ Resp)) F,
      (∀ r ∈ support (romExperiment S main), r.2 ≤ q) →
        Pr{let r ← romExperiment S main}[r.1 = true] ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞))
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp)) F) (Q : ℕ) (hQ1 : 1 ≤ Q)
    (hQ : IsWeightBound (rpmGame e S main) permCalls Q) :
    Pr{let b ← rpmExperiment e S main}[b = true] ≤
      Q / ((2 ^ bits : ℕ) : ℝ≥0∞) + (Q ^ 2 : ℝ≥0∞) / 2 ^ 509 :=
  rpm_bound e S bits hrom main Q Q hQ1 (hQ.mono_weight oracleCalls_le_permCalls) hQ

end LeanRpm.SufCma
