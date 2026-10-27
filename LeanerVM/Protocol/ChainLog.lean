/-
  LeanerVM.Protocol.ChainLog

  The verifier's chain walk replayed on a log of the hash's answers: it asks every step of the
  chain it walks, so a successful replay leaves the whole chain, as its history, in the log.
-/

module

public import LeanerVM.Protocol.DecodeWalk
public import LeanerVM.Protocol.Replay

/-!
# The chain in the replayed log

The verifier replayed on a log answers each hash from it (`QueryLog.replayImpl ans`) and records
the queries. Every step of the chain is one hash: an observe step, a squeeze, a nonce absorbed;
the grinding base and check are hashes that are not steps. `walkChain_log`: if the chain walk
replayed from a state succeeds, the logged walk at the hash the log's answers give
(`walkChainLogged`, at `fun t ↦ (ans t).getD default`) succeeds with the same wire and state, and
the queries the replay recorded contain every step of the history it logs
(`HashChain.queries Block.input`), from the starting state to the final one
(`HashChain.last`).

`accepts_of_replay`: a replay of the verifier that accepts walks the chain first, then the
openings, only appending to the log (`prefix_of_runReplay_walkOpenings`, through the replay as a
morphism of the readers' monads), and its algebra accepts their wire and rows. So
`chain_in_log_of_replay`: when the verifier replayed on a log accepts, the
logged chain walk at the log's hash succeeds on the proof and the replay's log holds every step of
its history from the statement's seed. `accepts_of_runFrom` and `chain_in_log_of_runFrom` are the
same for the verifier from a computed start (`verifyFrom`): the start runs first, its queries a
prefix `log₀` of the log, and the walk starts from its state with `log₀` recorded.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa Verify DecodeChain OracleSpec

@[expose] public section

namespace ChainLog

/-- The proof reader whose hash is answered from a log. -/
abbrev RW : Type → Type := Walk (StateT (List UInt8 →ₒ Digest).QueryLog Option)

/-- A run of the replayed reader from a state and a log. -/
abbrev runReplay {α : Type} (a : RW α) (st : ReaderState PrunedMerklePaths)
    (log : (List UInt8 →ₒ Digest).QueryLog) :
    Option (Except ReadError (α × ReaderState PrunedMerklePaths) ×
      (List UInt8 →ₒ Digest).QueryLog) :=
  ((a.run st).run).run log

theorem runReplay_bind {α β : Type} (a : RW α) (f : α → RW β) (st log) :
    runReplay (a >>= f) st log = match runReplay a st log with
      | some (.ok (x, st'), log') => runReplay (f x) st' log'
      | some (.error e, log') => some (.error e, log')
      | none => none := by
  simp only [runReplay, StateT.run_bind, ExceptT.run_bind]
  rcases (((a.run st).run).run log) with _ | ⟨_ | ⟨x, st'⟩, log'⟩ <;> rfl

variable (ans : List UInt8 → Option Digest)

/-- The hash the log's answers give. -/
def hashOf (t : List UInt8) : Id Digest := (ans t).getD default

/-- **The replayed walk asks its chain**: whenever the replayed reader succeeds, the logged reader
at the log's hash succeeds with the same value and state, appending a history whose steps the
replay asked, from the starting state to the final one. -/
private def logRel : MonadRel RW (LoggedWalk Id) where
  R a b := ∀ st log x st' log', runReplay a st log = some (.ok (x, st'), log') →
    ∀ hist₀, ∃ hist, runLogged b hist₀ st = .ok ((x, hist₀ ++ hist), st') ∧
      (∃ L, log' = log ++ L ∧ ∀ e ∈ HashChain.queries Block.input st.fs.cv hist, e ∈ L) ∧
      st'.fs.cv = HashChain.last st.fs.cv hist
  pure x := by
    intro st log y st' log' h hist₀
    simp only [runReplay] at h
    cases h
    exact ⟨[], by simp [runLogged_pure], ⟨[], by simp, by simp [HashChain.queries]⟩, rfl⟩
  bind {α β a₁ a₂ f₁ f₂} h₁ h₂ := by
    intro st log y st'' log'' h hist₀
    rw [runReplay_bind] at h
    rcases hr : runReplay a₁ st log with _ | ⟨_ | ⟨x, st'⟩, log'⟩ <;> rw [hr] at h
    · cases h
    · cases h
    obtain ⟨c₁, hc₁, ⟨L₁, hlog₁, hL₁⟩, hv₁⟩ := h₁ st log x st' log' hr hist₀
    obtain ⟨c₂, hc₂, ⟨L₂, hlog₂, hL₂⟩, hv₂⟩ := h₂ x st' log' y st'' log'' h (hist₀ ++ c₁)
    refine ⟨c₁ ++ c₂, ?_, ⟨L₁ ++ L₂, by rw [hlog₂, hlog₁, List.append_assoc], fun e he ↦ ?_⟩, ?_⟩
    · rw [runLogged_bind, hc₁]
      simpa using hc₂
    · rw [HashChain.queries_append, ← hv₁, List.mem_append] at he
      rcases he with he | he
      · exact List.mem_append_left _ (hL₁ e he)
      · exact List.mem_append_right _ (hL₂ e he)
    · rw [HashChain.last_append, ← hv₁, hv₂]

/-! ## The primitives -/

theorem runReplay_get (st : ReaderState PrunedMerklePaths) (log) :
    runReplay (get : RW (ReaderState PrunedMerklePaths)) st log = some (.ok (st, st), log) := rfl

theorem runReplay_modify (g : ReaderState PrunedMerklePaths → ReaderState PrunedMerklePaths)
    (st : ReaderState PrunedMerklePaths) (log) :
    runReplay (modify g : RW Unit) st log = some (.ok ((), g st), log) := rfl

theorem runReplay_throw {α : Type} (e : ReadError) (st : ReaderState PrunedMerklePaths)
    (log) :
    runReplay (throw e : RW α) st log = some (.error e, log) := rfl

theorem runReplay_pure {α : Type} (x : α) (st : ReaderState PrunedMerklePaths) (log) :
    runReplay (pure x : RW α) st log = some (.ok (x, st), log) := rfl

theorem runReplay_liftM {α : Type} (c : StateT (List UInt8 →ₒ Digest).QueryLog Option α)
    (st : ReaderState PrunedMerklePaths) (log) :
    runReplay (liftM c : RW α) st log = (c.run log).bind fun p ↦ some (.ok (p.1, st), p.2) := by
  simp only [runReplay, liftM, monadLift, MonadLift.monadLift, StateT.run_lift, ExceptT.lift,
    ExceptT.mk]
  rw [ExceptT.run_bind]
  show ((Except.ok <$> c) >>= _).run log = _
  simp only [StateT.run_bind, StateT.run_map]
  rcases c.run log with _ | ⟨a, log'⟩ <;> rfl

theorem run_replayImpl (t : List UInt8) (log : (List UInt8 →ₒ Digest).QueryLog) :
    (QueryLog.replayImpl ans t).run log = (ans t).bind fun u ↦ some (u, log ++ [⟨t, u⟩]) := by
  rcases h : ans t with _ | u
  · simp [QueryLog.replayImpl, h]
  · simp [QueryLog.replayImpl, h]

/-- A replayed scalar: one observe step, answered from the log and recorded. -/
theorem replay_nextScalar (fs : FsState) (y : E) (rest : List E)
    (ms : List PrunedMerklePaths) (log : (List UInt8 →ₒ Digest).QueryLog) :
    runReplay (Reader.nextScalar (QueryLog.replayImpl ans)) ⟨fs, y :: rest, ms⟩ log =
      (ans (Block.input fs.cv (.observe y))).bind fun u ↦
        some (.ok (y, ⟨⟨u⟩, rest, ms⟩), log ++ [⟨Block.input fs.cv (.observe y), u⟩]) := by
  simp only [Reader.nextScalar, Reader.takeRaw, Reader.observe, FsState.observe, runReplay_bind,
    runReplay_get, runReplay_modify, runReplay_pure, runReplay_liftM, StateT.run_map,
    run_replayImpl]
  rw [show FsState.stepBytes fs.cv y FsState.observeTag = Block.input fs.cv (.observe y) from rfl]
  rcases ans (Block.input fs.cv (.observe y)) with _ | u <;> rfl

/-- A replayed challenge: one squeeze step, answered from the log and recorded. -/
theorem replay_sample (st : ReaderState PrunedMerklePaths)
    (log : (List UInt8 →ₒ Digest).QueryLog) :
    runReplay (Reader.sample (QueryLog.replayImpl ans)) st log =
      (ans (Block.input st.fs.cv .squeeze)).bind fun u ↦
        some (.ok (FsState.challengeOf u, { st with fs := ⟨u⟩ }),
          log ++ [⟨Block.input st.fs.cv .squeeze, u⟩]) := by
  simp only [Reader.sample, FsState.sample, runReplay_bind, runReplay_get, runReplay_modify,
    runReplay_pure, runReplay_liftM, StateT.run_bind, StateT.run_pure, run_replayImpl]
  rw [show FsState.stepBytes st.fs.cv 0 FsState.squeezeTag = Block.input st.fs.cv .squeeze
    from rfl]
  rcases ans (Block.input st.fs.cv .squeeze) with _ | u <;> rfl

/-- A scalar's step is asked by the replay. -/
private theorem log_scalar :
    logRel.R (Reader.nextScalar (QueryLog.replayImpl ans)) (loggedScalar (hashOf ans)) := by
  intro st log x st' log' h hist₀
  rcases st with ⟨fs, _ | ⟨y, rest⟩, ms⟩
  · exact nomatch h
  rw [replay_nextScalar] at h
  rcases ha : ans (Block.input fs.cv (.observe y)) with _ | u <;> rw [ha] at h
  · exact nomatch h
  simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  refine ⟨[(.observe y, u)], ?_, ⟨[⟨Block.input fs.cv (.observe y), u⟩], rfl,
    by simp [HashChain.queries]⟩, by simp [HashChain.last]⟩
  rw [loggedScalar, runLogged_logged]
  have hu : hashOf ans (FsState.stepBytes fs.cv y FsState.observeTag) = u := by
    simp only [hashOf]
    rw [show FsState.stepBytes fs.cv y FsState.observeTag = Block.input fs.cv (.observe y)
      from rfl, ha]
    rfl
  simp [runPlain, Reader.nextScalar, Reader.takeRaw, Reader.observe, FsState.observe, hu]
  rfl

/-- A challenge's step is asked by the replay. -/
private theorem log_sample :
    logRel.R (Reader.sample (QueryLog.replayImpl ans)) (stepOps (hashOf ans)).sample := by
  intro st log x st' log' h hist₀
  rw [replay_sample] at h
  rcases ha : ans (Block.input st.fs.cv .squeeze) with _ | u <;> rw [ha] at h
  · exact nomatch h
  simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  refine ⟨[(.squeeze, u)], ?_, ⟨[⟨Block.input st.fs.cv .squeeze, u⟩], rfl,
    by simp [HashChain.queries]⟩, by simp [HashChain.last]⟩
  simp only [stepOps]
  rw [runLogged_logged]
  have hu : hashOf ans (FsState.stepBytes st.fs.cv 0 FsState.squeezeTag) = u := by
    simp only [hashOf]
    rw [show FsState.stepBytes st.fs.cv 0 FsState.squeezeTag = Block.input st.fs.cv .squeeze
      from rfl, ha]
    rfl
  simp [runPlain, Reader.sample, FsState.sample, hu]
  rfl

private theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

private theorem id_map {α β : Type} (f : α → β) (x : Id α) : f <$> x = f x := rfl

private theorem id_pure {α : Type} (x : α) : (pure x : Id α) = x := rfl

/-- A grinding check's nonce step is asked by the replay, after its base and check. -/
private theorem log_checkPow (bits : ℕ) :
    logRel.R (Reader.checkPow (QueryLog.replayImpl ans) bits)
      ((stepOps (hashOf ans)).checkPow bits) := by
  intro st log x st' log' h hist₀
  rcases st with ⟨fs, _ | ⟨n, rest⟩, ms⟩
  · exact nomatch h
  simp only [Reader.checkPow, Reader.takeRaw, FsState.checkPow, FsState.powBase, FsState.powOk,
    FsState.absorbNonce, runReplay_bind, runReplay_get, runReplay_modify, runReplay_pure,
    runReplay_liftM, StateT.run_bind, run_replayImpl] at h
  rcases ha₁ : ans (FsState.stepBytes fs.cv 0 FsState.powBaseTag) with _ | b₁ <;>
    simp only [ha₁, Option.bind_none, Option.bind_some] at h
  · exact nomatch h
  rcases ha₃ : ans (FsState.stepBytes fs.cv n FsState.powNonceTag) with _ | u
  · by_cases hb : bits = 0 <;> simp [hb, StateT.run_bind, StateT.run_map, run_replayImpl, ha₃] at h
  by_cases hb : bits = 0
  · simp [hb, StateT.run_map, run_replayImpl, ha₃] at h
    split at h
    · rename_i hn
      subst hn
      rw [runReplay_pure, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨[(.nonce 0, u)], ?_, ⟨_, rfl, fun e he ↦ ?_⟩, by simp [HashChain.last]⟩
      · simp only [stepOps]
        rw [runLogged_logged]
        simp [runPlain, Reader.checkPow, Reader.takeRaw, FsState.checkPow, FsState.powBase,
          FsState.absorbNonce, hashOf, ha₃, hb, id_bind, id_map, id_pure]
      · simp only [HashChain.queries, List.mem_singleton] at he
        subst he
        simp [Block.input, Block.elem, Block.tag]
    · exact nomatch h
  · rcases ha₂ : ans (FsState.stepBytes b₁ n FsState.powNonceTag) with _ | b₂
    · simp [hb, StateT.run_bind, StateT.run_map, run_replayImpl, ha₂, ha₃] at h
    simp [hb, StateT.run_bind, StateT.run_map, run_replayImpl, ha₂, ha₃] at h
    split at h
    · rename_i hok
      rw [runReplay_pure, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨[(.nonce n, u)], ?_, ⟨_, rfl, fun e he ↦ ?_⟩, by simp [HashChain.last]⟩
      · simp only [stepOps]
        rw [runLogged_logged]
        simp [runPlain, Reader.checkPow, Reader.takeRaw, FsState.checkPow, FsState.powBase,
          FsState.powOk, FsState.absorbNonce, hashOf, ha₁, ha₂, ha₃, hb, hok, id_bind, id_map,
          id_pure]
      · simp only [HashChain.queries, List.mem_singleton] at he
        subst he
        simp [Block.input, Block.elem, Block.tag]
    · exact nomatch h

private theorem log_throw {α : Type} (e : ReadError) : logRel.R (throw e : RW α) (throw e) := by
  intro st log x st' log' h
  exact nomatch h

/-- The replayed reader's primitives and the logged reader's at the log's hash are related. -/
private theorem related_log :
    ChainOps.Related logRel (readerOps (QueryLog.replayImpl ans)) (stepOps (hashOf ans)) where
  nextScalar := log_scalar ans
  sample := log_sample ans
  nextRoot := by
    refine logRel.bind (log_scalar ans) fun a ↦ logRel.bind (log_scalar ans) fun b ↦ ?_
    rcases digestOfScalars (a, b) with _ | d
    · exact log_throw _
    · exact logRel.pure d
  checkPow := log_checkPow ans

/-- **The replayed chain walk asks its chain**: if the verifier's chain walk, every hash answered
from a log by `ans` and recorded, succeeds from a state, the chain walk with its steps logged at
the hash `ans` gives succeeds with the same wire and state, and the recorded queries contain every
step of the history it logs, from the starting state's chaining value to the final one's. -/
theorem walkChain_log {prog : Program} {s : Sizes} {input : PublicInput} {shs : List LevelShape}
    {st st' : ReaderState PrunedMerklePaths} {w : Wire} {log log' : (List UInt8 →ₒ Digest).QueryLog}
    (h : runReplay (walkChain (readerOps (QueryLog.replayImpl ans)) prog s input shs) st log =
      some (.ok (w, st'), log')) :
    ∃ hist, walkChainLogged prog s input shs (hashOf ans) st = .ok ((w, hist), st') ∧
      (∃ L, log' = log ++ L ∧ ∀ e ∈ HashChain.queries Block.input st.fs.cv hist, e ∈ L) ∧
      st'.fs.cv = HashChain.last st.fs.cv hist := by
  obtain ⟨hist, h₁, h₂, h₃⟩ :=
    walkChain_rel (related_log ans) prog s input shs st log w st' log' h []
  exact ⟨hist, by simpa [walkChainLogged] using h₁, h₂, h₃⟩

/-! ## The verifier's replay -/

/-- The replay as a morphism of the readers' monads: the oracle reader's run, every query
answered from the log and recorded. -/
abbrev replayHom : Walk (OracleComp hashSpec) →ᵐ RW :=
  ReadM.mapHom (simulateQ' (QueryLog.replayImpl ans))

private theorem readerOps_replay :
    (readerOps hashQuery).map (replayHom ans) = readerOps (QueryLog.replayImpl ans) := by
  rw [readerOps_hom]
  congr
  funext t
  simp [hashQuery]

theorem walkOpenings_replay (nLanes : ℕ) (first : Bool) (root : Digest)
    (shs : List LevelShape) (ls : List WhirLevel) :
    replayHom ans (walkOpenings (readerOps hashQuery) nLanes first root shs ls) =
      walkOpenings (readerOps (QueryLog.replayImpl ans)) nLanes first root shs ls := by
  rw [← readerOps_replay]
  induction shs generalizing first root ls with
  | nil => simp [walkOpenings]
  | cons sh shs ih =>
    cases ls with
    | nil => simp [walkOpenings]
    | cons l ls => simp [walkOpenings, ih, ChainOps.map]

/-- **The openings only append to the replay's log.** -/
theorem prefix_of_runReplay_walkOpenings {nLanes : ℕ} {first : Bool} {root : Digest}
    {shs : List LevelShape} {ls : List WhirLevel} {st : ReaderState PrunedMerklePaths}
    {log log' : (List UInt8 →ₒ Digest).QueryLog}
    {r : Except ReadError (List (List (List K)) × ReaderState PrunedMerklePaths)}
    (h : runReplay (walkOpenings (readerOps (QueryLog.replayImpl ans)) nLanes first root shs ls)
      st log = some (r, log')) : log <+: log' := by
  rw [← walkOpenings_replay] at h
  exact QueryLog.prefix_of_run_simulateQ_replayImpl ans _ h

/-- **A replay of the verifier from a computed start that accepts**: if the verifier from the
start `seed`, replayed on a log, accepts a proof, recording the queries `logV`, the proof
announces sizes and a rate with a ladder, the start runs with a state `fs` and the queries `log₀`,
the chain walk replayed from `fs` succeeds with a wire, recording `log₀` and then a prefix of
`logV`, the openings replayed after it succeed with rows, and the algebra accepts the wire and the
rows. -/
theorem accepts_of_runFrom {log : (List UInt8 →ₒ Digest).QueryLog}
    {seed : StateT (List UInt8 →ₒ Digest).QueryLog Option FsState} {prog : Program}
    {input : PublicInput} {proof : Proof PrunedMerklePaths} {logV : (List UInt8 →ₒ Digest).QueryLog}
    (h : (verifyFrom (QueryLog.replayImpl (MerkleTree.logAnswer log)) seed prog input proof).run
      [] = some (true, logV)) :
    ∃ s ρ levels fs log₀ w st₁ log₁ rows st₂ log₂, setup? prog proof = some (s, ρ) ∧
      ladderOf prog s ρ = some levels ∧ seed.run [] = some (fs, log₀) ∧
      runReplay (walkChain (readerOps (QueryLog.replayImpl (MerkleTree.logAnswer log))) prog s
        input (levelShapes (stackMu prog s) levels))
        ⟨fs, proof.stream, proof.merkle⟩ log₀ = some (.ok (w, st₁), log₁) ∧
      runReplay (walkOpenings (readerOps (QueryLog.replayImpl (MerkleTree.logAnswer log)))
        (nLanes prog s) true w.root (levelShapes (stackMu prog s) levels) w.whir) st₁ log₁ =
        some (.ok (rows, st₂), log₂) ∧
      algebra prog s input (levelShapes (stackMu prog s) levels) w rows = true ∧
      log₁ <+: logV := by
  unfold verifyFrom at h
  rcases hs : setup? prog proof with _ | ⟨s, ρ⟩
  · simp [hs] at h
  rcases hl : ladderOf prog s ρ with _ | levels
  · simp [hs, hl] at h
  simp only [hs, hl] at h
  split at h
  · simp at h
  let shs := levelShapes (stackMu prog s) levels
  let ops := readerOps (QueryLog.replayImpl (MerkleTree.logAnswer log))
  let X : RW (Wire × List (List (List K))) := do
    let x ← walkProof ops prog s input shs
    Reader.finish
    return x
  have h' : (seed >>= fun fs ↦ ((X.run' ⟨fs, proof.stream, proof.merkle⟩).run) >>= fun r ↦
      match r with
      | .error _ => pure false
      | .ok (w, rows) => pure (algebra prog s input shs w rows) :
      StateT (List UInt8 →ₒ Digest).QueryLog Option Bool).run [] = some (true, logV) := h
  rw [StateT.run_bind] at h'
  obtain ⟨⟨fs, log₀⟩, hseed, h'⟩ := Option.bind_eq_some_iff.mp h'
  let st₀ : ReaderState PrunedMerklePaths := ⟨fs, proof.stream, proof.merkle⟩
  rw [StateT.run_bind] at h'
  obtain ⟨⟨r, l⟩, hr, hK⟩ := Option.bind_eq_some_iff.mp h'
  rcases r with _ | ⟨w, rows⟩
  · simp at hK
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨halg, rfl⟩ := hK
  rw [StateT.run'_eq, ExceptT.run_map, StateT.run_map] at hr
  obtain ⟨⟨r', l'⟩, hr', he⟩ := Option.map_eq_some_iff.mp hr
  simp only [Prod.mk.injEq] at he
  obtain ⟨hr'', rfl⟩ := he
  change runReplay X st₀ log₀ = _ at hr'
  simp only [X, walkProof, bind_assoc] at hr'
  rw [runReplay_bind] at hr'
  rcases hc : runReplay (walkChain ops prog s input shs) st₀ log₀ with
    _ | ⟨_ | ⟨w₁, st₁⟩, log₁⟩ <;> rw [hc] at hr'
  · cases hr'
  · cases hr'
    cases hr''
  simp only at hr'
  rw [runReplay_bind] at hr'
  rcases ho : runReplay (walkOpenings ops (nLanes prog s) true w₁.root shs w₁.whir) st₁ log₁ with
    _ | ⟨r₂, log₂⟩ <;> rw [ho] at hr'
  · cases hr'
  have hpre := prefix_of_runReplay_walkOpenings _ ho
  rcases r₂ with _ | ⟨rows₂, st₃⟩
  · cases hr'
    cases hr''
  simp only [pure_bind] at hr'
  rw [runReplay_bind] at hr'
  have hfin : ∀ st (lg : (List UInt8 →ₒ Digest).QueryLog), ∃ r,
      runReplay (Reader.finish : RW Unit) st lg = some (r, lg) := by
    intro st lg
    unfold Reader.finish
    rw [runReplay_bind, runReplay_get]
    simp only
    split
    · exact ⟨_, runReplay_pure _ _ _⟩
    · exact ⟨_, runReplay_throw _ _ _⟩
  obtain ⟨rf, hf⟩ := hfin st₃ log₂
  rw [hf] at hr'
  rcases rf with _ | ⟨_, st₄⟩
  · cases hr'
    cases hr''
  simp only [runReplay_pure, Option.some.injEq, Prod.mk.injEq] at hr'
  obtain ⟨rfl, rfl⟩ := hr'
  cases hr''
  exact ⟨s, ρ, levels, fs, log₀, w, st₁, log₁, rows, st₃, log₂, rfl, hl, hseed, hc, ho, halg,
    hpre⟩

/-- **A replay the verifier accepts**: if the verifier replayed on a log accepts a proof,
recording the queries `logV`, the proof announces sizes and a rate with a ladder, the chain walk
replayed from the proof's start succeeds with a wire, recording a prefix of `logV`, the openings
replayed after it succeed with rows, and the algebra accepts the wire and the rows. -/
theorem accepts_of_replay {log : (List UInt8 →ₒ Digest).QueryLog} {prog : Program}
    {input : PublicInput} {proof : Proof PrunedMerklePaths} {logV : (List UInt8 →ₒ Digest).QueryLog}
    (h : replay log prog input proof = some (true, logV)) :
    ∃ s ρ levels w st₁ log₁ rows st₂ log₂, setup? prog proof = some (s, ρ) ∧
      ladderOf prog s ρ = some levels ∧
      runReplay (walkChain (readerOps (QueryLog.replayImpl (MerkleTree.logAnswer log))) prog s
        input (levelShapes (stackMu prog s) levels))
        ⟨FsState.seed prog input, proof.stream, proof.merkle⟩ [] = some (.ok (w, st₁), log₁) ∧
      runReplay (walkOpenings (readerOps (QueryLog.replayImpl (MerkleTree.logAnswer log)))
        (nLanes prog s) true w.root (levelShapes (stackMu prog s) levels) w.whir) st₁ log₁ =
        some (.ok (rows, st₂), log₂) ∧
      algebra prog s input (levelShapes (stackMu prog s) levels) w rows = true ∧
      log₁ <+: logV := by
  obtain ⟨s, ρ, levels, fs, log₀, w, st₁, log₁, rows, st₂, log₂, hs, hl, hseed, hc, ho, halg,
    hpre⟩ := accepts_of_runFrom (seed := pure (FsState.seed prog input)) h
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hseed
  obtain ⟨rfl, rfl⟩ := hseed
  exact ⟨s, ρ, levels, w, st₁, log₁, rows, st₂, log₂, hs, hl, hc, ho, halg, hpre⟩

/-- **An accepted replay from a computed start holds the chain**: if the verifier from the start
`seed`, replayed on a log, accepts a proof, recording `logV`, the proof announces sizes and a rate
with a ladder, the start runs with a state `fs` and the queries `log₀`, a prefix of `logV`, the
chain walk with its steps logged at the log's hash succeeds on the proof from `fs`, and every
step of the history it logs is in `logV`, from `fs`. -/
theorem chain_in_log_of_runFrom {log : (List UInt8 →ₒ Digest).QueryLog}
    {seed : StateT (List UInt8 →ₒ Digest).QueryLog Option FsState} {prog : Program}
    {input : PublicInput} {proof : Proof PrunedMerklePaths} {logV : (List UInt8 →ₒ Digest).QueryLog}
    (h : (verifyFrom (QueryLog.replayImpl (MerkleTree.logAnswer log)) seed prog input proof).run
      [] = some (true, logV)) :
    ∃ s ρ levels fs log₀ w st₁ hist, setup? prog proof = some (s, ρ) ∧
      ladderOf prog s ρ = some levels ∧ seed.run [] = some (fs, log₀) ∧ log₀ <+: logV ∧
      walkChainLogged prog s input (levelShapes (stackMu prog s) levels)
        (hashOf (MerkleTree.logAnswer log)) ⟨fs, proof.stream, proof.merkle⟩ =
        .ok ((w, hist), st₁) ∧
      ∀ e ∈ HashChain.queries Block.input fs.cv hist, e ∈ logV := by
  obtain ⟨s, ρ, levels, fs, log₀, w, st₁, log₁, -, -, -, hs, hl, hseed, hc, -, -, hpre⟩ :=
    accepts_of_runFrom h
  obtain ⟨hist, hw, ⟨L, hL, hq⟩, -⟩ := walkChain_log _ hc
  refine ⟨s, ρ, levels, fs, log₀, w, st₁, hist, hs, hl, hseed, ?_, hw, fun e he ↦ hpre.subset ?_⟩
  · rw [hL] at hpre
    exact (List.prefix_append log₀ L).trans hpre
  · rw [hL]
    exact List.mem_append_right _ (hq e he)

/-- **An accepted replay's log holds the chain**: if the verifier replayed on a log accepts a
proof, recording `logV`, the proof announces sizes and a rate with a ladder, the chain walk with its
steps logged at the log's hash succeeds on the proof, and every step of the history it logs is in
`logV`, from the statement's seed. -/
theorem chain_in_log_of_replay {log : (List UInt8 →ₒ Digest).QueryLog} {prog : Program}
    {input : PublicInput} {proof : Proof PrunedMerklePaths} {logV : (List UInt8 →ₒ Digest).QueryLog}
    (h : replay log prog input proof = some (true, logV)) :
    ∃ s ρ levels w st₁ hist, setup? prog proof = some (s, ρ) ∧ ladderOf prog s ρ = some levels ∧
      walkChainLogged prog s input (levelShapes (stackMu prog s) levels)
        (hashOf (MerkleTree.logAnswer log)) ⟨FsState.seed prog input, proof.stream, proof.merkle⟩ =
        .ok ((w, hist), st₁) ∧
      ∀ e ∈ HashChain.queries Block.input (FsState.seed prog input).cv hist, e ∈ logV := by
  obtain ⟨s, ρ, levels, fs, log₀, w, st₁, hist, hs, hl, hseed, -, hw, hq⟩ :=
    chain_in_log_of_runFrom (seed := pure (FsState.seed prog input)) h
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hseed
  obtain ⟨rfl, rfl⟩ := hseed
  exact ⟨s, ρ, levels, w, st₁, hist, hs, hl, hw, hq⟩

end ChainLog

end

end LeanerVM.Protocol
