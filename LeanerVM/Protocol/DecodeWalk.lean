/-
  LeanerVM.Protocol.DecodeWalk

  The verifier's chain walk with its steps logged, and the walk read back off the log: what the
  walk reads on a proof, the walk reads on its logged history.
-/

module

public import LeanerVM.Protocol.DecodeChain
public import LeanerVM.Protocol.Verify.Rel

/-!
# The logged chain walk

`stepOps H` is the proof reader's primitives (`readerOps H`) with every step of the chain logged:
the block it absorbs, with the chain state it leads to (`Reading`). A root logs its two observe
steps, a grinding check its nonce step; the grinding base and check are not steps and are not
logged. Its openings are not walked: the chain walk never opens a commitment.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa Verify

@[expose] public section

namespace DecodeChain

/-- The proof reader under a log of the chain's steps. -/
abbrev LoggedWalk (m : Type → Type) : Type → Type := StateT (List Reading) (Walk m)

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- Log a step: its block, with the reader's chain state after it. -/
def logStep (b : Block) : LoggedWalk m Unit := do
  let st ← getThe (ReaderState PrunedMerklePaths)
  modifyThe (List Reading) (· ++ [(b, st.fs.cv)])

/-- Read and observe a scalar, logged. -/
def loggedScalar : LoggedWalk m E := do
  let x ← (Reader.nextScalar H : Walk m E)
  logStep (.observe x)
  return x

/-- **The proof reader's primitives with the chain's steps logged**: a scalar its observe step, a
challenge its squeeze step, a root its two observe steps, a grinding check its nonce step (the
grinding base and check are not steps). The chain walk opens no commitment, and this reader opens
none. -/
def stepOps : ChainOps (LoggedWalk m) where
  nextScalar := loggedScalar H
  sample := do
    let x ← (Reader.sample H : Walk m E)
    logStep .squeeze
    return x
  nextRoot := do
    let a ← loggedScalar H
    let b ← loggedScalar H
    match digestOfScalars (a, b) with
    | some d => return d
    | none => throw .nonCanonicalEncoding
  checkPow bits := do
    let x ← (Reader.checkPow H bits : Walk m E)
    logStep (.nonce x)
    return x
  nextOpening _ _ _ _ _ := throw .missingHint

/-! ## Runs in `Id` -/

/-- A run of the proof reader in `Id`. -/
abbrev runPlain {α : Type} (b : Walk Id α) (st : ReaderState PrunedMerklePaths) :
    Except ReadError (α × ReaderState PrunedMerklePaths) :=
  (b.run st).run

/-- A run of the logged reader in `Id`, from a log. -/
abbrev runLogged {α : Type} (a : LoggedWalk Id α) (log : List Reading)
    (st : ReaderState PrunedMerklePaths) :
    Except ReadError ((α × List Reading) × ReaderState PrunedMerklePaths) :=
  ((a.run log).run st).run

/-- The chain walk of the verifier on a proof's stream from a chain state, its steps logged: the
wire, the history and the reader's state after it, or the reader's error. -/
def walkChainLogged (prog : Program) (s : Sizes) (input : PublicInput) (shs : List LevelShape)
    (H : List UInt8 → Id Digest) (st : ReaderState PrunedMerklePaths) :
    Except ReadError ((Wire × List Reading) × ReaderState PrunedMerklePaths) :=
  runLogged (walkChain (stepOps H) prog s input shs) [] st

private theorem runPlain_bind {α β : Type} (b : Walk Id α) (f : α → Walk Id β) (st) :
    runPlain (b >>= f) st = match runPlain b st with
      | .ok (x, st') => runPlain (f x) st'
      | .error e => .error e := by
  simp only [runPlain, StateT.run_bind, ExceptT.run_bind]
  rcases (b.run st).run with e | ⟨x, st'⟩ <;> rfl

theorem runLogged_bind {α β : Type} (a : LoggedWalk Id α) (f : α → LoggedWalk Id β) (log st) :
    runLogged (a >>= f) log st = match runLogged a log st with
      | .ok ((x, log'), st') => runLogged (f x) log' st'
      | .error e => .error e := by
  simp only [runLogged, StateT.run_bind, ExceptT.run_bind]
  rcases ((a.run log).run st).run with e | ⟨⟨x, log'⟩, st'⟩ <;> rfl

theorem runLogged_pure {α : Type} (x : α) (log st) :
    runLogged (pure x : LoggedWalk Id α) log st = .ok ((x, log), st) := rfl

private theorem runPlain_pure {α : Type} (x : α) (st) :
    runPlain (pure x : Walk Id α) st = .ok (x, st) := rfl

/-- A reader step, then its block logged with the chain state after it. -/
theorem runLogged_logged {α : Type} (b : Walk Id α) (g : α → Block) (log st) :
    runLogged (do let x ← (b : Walk Id α); logStep (g x); return x) log st =
      match runPlain b st with
      | .ok (x, st') => .ok ((x, log ++ [(g x, st'.fs.cv)]), st')
      | .error e => .error e := by
  simp only [runLogged, runPlain, logStep, StateT.run_bind, StateT.run_monadLift,
    ExceptT.run_bind]
  rcases (b.run st).run with e | ⟨x, st'⟩ <;> rfl

/-! ## The scalars a history reads -/

/-- The scalars of the stream a history's steps read: an observed scalar, a nonce; a squeeze reads
none. -/
def streamOf (hist : List Reading) : List E :=
  hist.filterMap fun r ↦ match r.1 with
    | .observe x => some x
    | .nonce n => some n
    | .squeeze => none

theorem streamOf_append (c c' : List Reading) : streamOf (c ++ c') = streamOf c ++ streamOf c' :=
  List.filterMap_append

/-! ## The reader's steps -/

section Steps

variable (H : List UInt8 → Id Digest)

private theorem runPlain_nextScalar {st : ReaderState PrunedMerklePaths} {x : E}
    {st' : ReaderState PrunedMerklePaths}
    (h : runPlain (Reader.nextScalar H) st = .ok (x, st')) : st.stream = x :: st'.stream := by
  rcases st with ⟨fs, _ | ⟨y, rest⟩, ms⟩
  · simp [runPlain, Reader.nextScalar, Reader.takeRaw] at h
  · simp [runPlain, Reader.nextScalar, Reader.takeRaw, Reader.observe] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

private theorem runPlain_sample {st : ReaderState PrunedMerklePaths} {x : E}
    {st' : ReaderState PrunedMerklePaths}
    (h : runPlain (Reader.sample H) st = .ok (x, st')) :
    x = FsState.challengeOf st'.fs.cv ∧ st'.stream = st.stream := by
  simp [runPlain, Reader.sample, FsState.sample] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

private theorem runPlain_checkPow (bits : ℕ) {st : ReaderState PrunedMerklePaths} {x : E}
    {st' : ReaderState PrunedMerklePaths}
    (h : runPlain (Reader.checkPow H bits) st = .ok (x, st')) : st.stream = x :: st'.stream := by
  rcases st with ⟨fs, _ | ⟨y, rest⟩, ms⟩
  · simp [runPlain, Reader.checkPow, Reader.takeRaw] at h
  · simp only [runPlain, Reader.checkPow, Reader.takeRaw] at h
    simp at h
    revert h
    generalize (FsState.checkPow H fs bits y : Id (Bool × FsState)) = p
    rcases p with ⟨_ | _, fs'⟩
    · intro h
      cases h
    · intro h
      cases h
      rfl

end Steps

/-! ## The logged walk reads its history -/

/-- `a` simulates the slot `b` on its log: whenever the logged reader succeeds, it appends steps
that account for the scalars it read and that `b` reads back as the same value. -/
private def simRel : MonadRel (LoggedWalk Id) (Slot Reading) where
  R a b := ∀ log st x log' st', runLogged a log st = .ok ((x, log'), st') →
    ∃ c, log' = log ++ c ∧ st.stream = streamOf c ++ st'.stream ∧
      ∀ rest, b.read (c ++ rest) = some (x, rest)
  pure x := by
    intro log st y log' st' h
    rw [runLogged_pure] at h
    cases h
    exact ⟨[], by simp, by simp [streamOf], fun _ ↦ rfl⟩
  bind {α β a₁ a₂ f₁ f₂} h₁ h₂ := by
    intro log st y log'' st'' h
    rw [runLogged_bind] at h
    split at h
    · rename_i x log' st' hx
      obtain ⟨c₁, rfl, hs₁, hr₁⟩ := h₁ log st x log' st' hx
      obtain ⟨c₂, rfl, hs₂, hr₂⟩ := h₂ x _ st' y log'' st'' h
      refine ⟨c₁ ++ c₂, by simp, by rw [hs₁, hs₂, streamOf_append, List.append_assoc],
        fun rest ↦ ?_⟩
      rw [Slot.read_bind, List.append_assoc, hr₁, Option.bind_some, hr₂]
    · cases h

/-- `b` succeeds only where the logged `a` succeeds, with the same value and reader state. -/
private def backRel : MonadRel (LoggedWalk Id) (Walk Id) where
  R a b := ∀ st x st', runPlain b st = .ok (x, st') → ∀ log, ∃ log',
    runLogged a log st = .ok ((x, log'), st')
  pure x := by
    intro st y st' h log
    rw [runPlain_pure] at h
    cases h
    exact ⟨log, rfl⟩
  bind {α β a₁ a₂ f₁ f₂} h₁ h₂ := by
    intro st y st'' h log
    rw [runPlain_bind] at h
    split at h
    · rename_i x st' hx
      obtain ⟨log', hl'⟩ := h₁ st x st' hx log
      obtain ⟨log'', hl''⟩ := h₂ x st' y st'' h log'
      exact ⟨log'', by rw [runLogged_bind, hl']; exact hl''⟩
    · cases h

/-- A reader step, its block logged, simulates a slot that reads that block back. -/
private theorem sim_logged {α : Type} {b : Walk Id α} {g : α → Block} {s : Slot Reading α}
    (hb : ∀ {st x st'}, runPlain b st = .ok (x, st') →
      st.stream = streamOf [(g x, st'.fs.cv)] ++ st'.stream ∧
        ∀ rest, s.read ((g x, st'.fs.cv) :: rest) = some (x, rest)) :
    simRel.R (do let x ← b; logStep (g x); return x) s := by
  intro log st x log' st' h
  rw [runLogged_logged] at h
  split at h
  · rename_i y st'' hy
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨_, rfl, (hb hy).1, (hb hy).2⟩
  · cases h

/-- A reader step, its block logged, succeeds where the step does. -/
private theorem back_logged {α : Type} (b : Walk Id α) (g : α → Block) :
    backRel.R (do let x ← b; logStep (g x); return x) b := by
  intro st x st' h log
  rw [runLogged_logged, h]
  exact ⟨_, rfl⟩

variable (H : List UInt8 → Id Digest)

private theorem sim_scalar : simRel.R (loggedScalar H) historyOps.nextScalar :=
  sim_logged fun hy ↦ ⟨by simp [runPlain_nextScalar H hy, streamOf], fun _ ↦ rfl⟩

/-- The logged reader simulates the walk on its history. -/
private theorem related_sim : ChainOps.Related simRel (stepOps H) historyOps where
  nextScalar := sim_scalar H
  sample := sim_logged fun hy ↦ by
    obtain ⟨rfl, hs⟩ := runPlain_sample H hy
    exact ⟨by simp [hs, streamOf], fun _ ↦ rfl⟩
  nextRoot := by
    refine simRel.bind (sim_scalar H) fun a ↦ simRel.bind (sim_scalar H) fun b ↦ ?_
    rcases digestOfScalars (a, b) with _ | d
    · exact fun _ _ _ _ _ h ↦ nomatch h
    · exact simRel.pure d
  checkPow bits := sim_logged fun hy ↦
    ⟨by simp [runPlain_checkPow H bits hy, streamOf], fun _ ↦ rfl⟩

/-- The logged reader succeeds wherever the proof reader does. -/
private theorem related_back : ChainOps.Related backRel (stepOps H) (readerOps H) where
  nextScalar := back_logged _ _
  sample := back_logged _ _
  nextRoot := by
    refine backRel.bind (back_logged _ _) fun a ↦ backRel.bind (back_logged _ _) fun b ↦ ?_
    rcases digestOfScalars (a, b) with _ | d
    · exact fun _ _ _ h ↦ nomatch h
    · exact backRel.pure d
  checkPow _ := back_logged _ _

/-- **The logged walk reads its own history**: if the chain walk succeeds on the logged reader,
the walk on the history it logged reads the same wire, and the history accounts for the stream's
scalars the walk read. -/
theorem walkChain_history {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List LevelShape} {st st' : ReaderState PrunedMerklePaths} {w : Wire}
    {hist : List Reading} (h : walkChainLogged prog s input shs H st = .ok ((w, hist), st')) :
    (walkChain historyOps prog s input shs).read hist = some (w, []) ∧
      st.stream = streamOf hist ++ st'.stream := by
  obtain ⟨c, hc, hs, hr⟩ := walkChain_rel (related_sim H) prog s input shs [] st w hist st' h
  rw [List.nil_append] at hc
  subst hc
  exact ⟨by simpa using hr [], hs⟩

/-- **The logged walk succeeds where the walk does**: a chain walk the proof reader accepts is
accepted by the logged reader, with the same wire and reader state. -/
theorem walkChainLogged_of_walkChain {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List LevelShape} {st st' : ReaderState PrunedMerklePaths} {w : Wire}
    (h : runPlain (walkChain (readerOps H) prog s input shs) st = .ok (w, st')) :
    ∃ hist, walkChainLogged prog s input shs H st = .ok ((w, hist), st') :=
  walkChain_rel (related_back H) prog s input shs st w st' h []

end DecodeChain

end

end LeanerVM.Protocol
