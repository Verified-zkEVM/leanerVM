/-
  LeanerVM.Protocol.ToArkLib.FrontRun

  A front component's verifier run on one transcript, as an option: its verdict when its check
  passes; likewise a guarded component's, with its oracles. Runs of appended components compose,
  the transcripts of the one-round and empty schedules are built from their values, and a run of
  sumcheck rounds unfolds round by round. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.SumcheckRound

/-!
# Runs of front components

A front component (`Component.Front`) has a check and a verdict on its input statement and its
transcript. `Front.run F s tr` is the verdict when the check passes and `none` otherwise: what an
executable verifier computes from the same values. Runs compose along appends (`run_append`):
the run of `F₁.append F₂` is the run of `F₁` on the first part of the transcript, followed by the
run of `F₂` on the second from its verdict. The basic components run as their definitions say
(`run_sampleFront`, `run_sendCheckedFront`, `run_drawPushesFront`), and a run of sumcheck rounds
unfolds one round at a time (`run_roundsFront_zero`, `run_roundsFront_succ`).

A guarded component (`Component.Guarded`) has a check and a verdict on its statement, its oracles
and its transcript, and may read the oracles. `Guarded.run G p tr` is the verdict with the output
oracles when the check passes; the component's verifier, run as an oracle computation, returns it
(`Guarded.verifier_run`; for a front component `Front.verifier_run`, its run with the oracles
handed on). Guarded runs compose along appends (`Guarded.run_append`), so the verifier of a
protocol assembled from components reduces to its components' runs.

The transcripts of the one-round schedules are built from their values (`msgTr`, `chalTr`), the
empty schedule's is `nilTr`, and every transcript of these schedules is so built (`eq_msgTr`,
`eq_chalTr`, `eq_nilTr`). `chalsTr` builds the transcript of `k` challenges, the first one
first.

Compiled code appends transcripts entry by entry (`appendFast`, `@[csimp]`): ArkLib's
`FullTranscript.append` recurses on the second transcript's length at every read, which the
nested appends of a long protocol cannot afford; the two are equal (`append_eq_appendFast`).
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

/-! ## Appending transcripts, as compiled code does -/

section Append

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Two transcripts appended entry by entry: the first's entries, then the second's. It is
`FullTranscript.append` (`append_eq_appendFast`), which compiled code runs as this: that one
recurses on the second transcript's length at every read, which nested appends cannot afford. -/
def appendFast (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.FullTranscript) :
    (pSpec₁ ++ₚ pSpec₂).FullTranscript := fun i ↦
  Fin.addCases (motive := fun i ↦ (pSpec₁ ++ₚ pSpec₂).«Type» i)
    (fun j ↦ cast (by simp [Fin.vappend_eq_append]) (T₁ j))
    (fun j ↦ cast (by simp [Fin.vappend_eq_append]) (T₂ j)) i

/-- The first part of two transcripts appended entry by entry is the first. -/
private theorem fst_appendFast (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.FullTranscript) :
    (appendFast T₁ T₂).fst = T₁ := by
  funext i
  simp [FullTranscript.fst, appendFast]

/-- The second part of two transcripts appended entry by entry is the second. -/
private theorem snd_appendFast (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.FullTranscript) :
    (appendFast T₁ T₂).snd = T₂ := by
  funext i
  simp [FullTranscript.snd, appendFast]

/-- Appending entry by entry is ArkLib's append. -/
theorem append_eq_appendFast (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.FullTranscript) :
    T₁ ++ₜ T₂ = appendFast T₁ T₂ := by
  rw [← FullTranscript.append_fst_snd (appendFast T₁ T₂), fst_appendFast, snd_appendFast]

end Append

/-- Compiled code appends transcripts entry by entry. -/
@[csimp] theorem append_eq_appendFast' : @FullTranscript.append = @appendFast := by
  funext m n pSpec₁ pSpec₂ T₁ T₂
  exact append_eq_appendFast T₁ T₂

/-! ## Transcripts of the small schedules -/

/-- The transcript of one message. -/
def msgTr {M : Type} (m : M) : (say M).FullTranscript := fun | ⟨0, _⟩ => m

/-- The transcript of one challenge. -/
def chalTr {C : Type} (c : C) : (draw C).FullTranscript := fun | ⟨0, _⟩ => c

/-- The transcript of no round. -/
def nilTr : (!p[] : ProtocolSpec 0).FullTranscript := fun i ↦ Fin.elim0 i

/-- The transcript of `k` challenges, the first one first. -/
def chalsTr {C : Type} : (k : ℕ) → (Fin k → C) → (draws C k).FullTranscript
  | 0, _ => nilTr
  | k + 1, f => chalsTr k (fun i ↦ f i.castSucc) ++ₜ chalTr (f (Fin.last k))

/-- A vector is its first entries with its last one pushed. -/
theorem push_ofFn_castSucc {C : Type} {n : ℕ} (u : Vector C (n + 1)) :
    (Vector.ofFn fun i : Fin n ↦ u[i.castSucc]).push u[Fin.last n] = u := by
  refine Vector.ext fun j hj ↦ ?_
  simp only [Vector.getElem_push, Vector.getElem_ofFn, Fin.getElem_fin, Fin.val_castSucc,
    Fin.val_last]
  split
  · rfl
  · congr 1
    omega

/-- The message of the transcript of one message. -/
@[simp] theorem msgTr_zero {M : Type} (m : M) : msgTr m 0 = m := rfl

/-- The challenge of the transcript of one challenge. -/
@[simp] theorem chalTr_zero {C : Type} (c : C) : chalTr c 0 = c := rfl

/-- A transcript of one message is the transcript of its message. -/
theorem eq_msgTr {M : Type} (t : (say M).FullTranscript) : t = msgTr (t 0) :=
  funext fun | ⟨0, _⟩ => rfl

/-- A transcript of one challenge is the transcript of its challenge. -/
theorem eq_chalTr {C : Type} (t : (draw C).FullTranscript) : t = chalTr (t 0) :=
  funext fun | ⟨0, _⟩ => rfl

/-- The transcript of no round is the only one. -/
theorem eq_nilTr (t : (!p[] : ProtocolSpec 0).FullTranscript) : t = nilTr :=
  funext fun i ↦ Fin.elim0 i

/-- A transcript of two schedules in sequence is two transcripts appended. -/
theorem exists_eq_append {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n}
    (t : (p₁ ++ₚ p₂).FullTranscript) : ∃ t₁ t₂, t = t₁ ++ₜ t₂ :=
  ⟨_, _, (FullTranscript.append_fst_snd t).symm⟩

/-- A transcript of `k` challenges is the transcript of its challenges. -/
theorem exists_eq_chalsTr {C : Type} : ∀ (k : ℕ) (t : (draws C k).FullTranscript),
    ∃ f, t = chalsTr k f
  | 0, t => ⟨Fin.elim0, eq_nilTr t⟩
  | k + 1, t => by
    obtain ⟨f, hf⟩ := exists_eq_chalsTr k
      (FullTranscript.fst (pSpec₁ := draws C k) (pSpec₂ := draw C) t)
    refine ⟨Fin.snoc (α := fun _ ↦ C) f
      (FullTranscript.snd (pSpec₁ := draws C k) (pSpec₂ := draw C) t 0), ?_⟩
    refine (FullTranscript.append_fst_snd (pSpec₁ := draws C k) (pSpec₂ := draw C) t).symm.trans
      ?_
    show _ = chalsTr k (fun i ↦ Fin.snoc (α := fun _ ↦ C) f _ i.castSucc) ++ₜ
      chalTr (Fin.snoc (α := fun _ ↦ C) f _ (Fin.last k))
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← hf, ← eq_chalTr]

namespace Component.Front

variable {ι : Type} {OStmt : ι → Type} [∀ i, OracleInterface (OStmt i)]

section Run

variable {StmtIn StmtOut WitIn WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]
  {D : Def StmtIn OStmt WitIn StmtOut OStmt WitOut pSpec}

/-- The run of a front component on a transcript: its verdict when its check passes. -/
def run (F : Front D) (s : StmtIn) (tr : pSpec.FullTranscript) : Option StmtOut :=
  if F.check s tr then some (F.out s tr) else none

/-- A run returns a verdict exactly when the check passes and the verdict is it. -/
theorem run_eq_some_iff (F : Front D) {s : StmtIn} {tr : pSpec.FullTranscript} {o : StmtOut} :
    F.run s tr = some o ↔ F.check s tr = true ∧ F.out s tr = o := by
  unfold run
  cases F.check s tr <;> simp

/-- A run whose check passes returns the verdict. -/
theorem run_of_check (F : Front D) {s : StmtIn} {tr : pSpec.FullTranscript}
    (h : F.check s tr = true) : F.run s tr = some (F.out s tr) := by
  simp [run, h]

end Run

variable {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type} {m₁ m₂ : ℕ}
  {pSpec₁ : ProtocolSpec m₁} {pSpec₂ : ProtocolSpec m₂}
  [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, OracleInterface (pSpec₂.Message i)] [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- **Runs compose**: the run of two front components in sequence is the first one's run on the
first part of the transcript, then the second one's from its verdict on the second part. -/
theorem run_append {E₁ : Def Stmt₁ OStmt Wit₁ Stmt₂ OStmt Wit₂ pSpec₁}
    {E₂ : Def Stmt₂ OStmt Wit₂ Stmt₃ OStmt Wit₃ pSpec₂} (F₁ : Front E₁) (F₂ : Front E₂)
    (s : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    (F₁.append F₂).run s tr = (F₁.run s tr.fst).bind fun s' ↦ F₂.run s' tr.snd := by
  simp only [run, Front.append]
  by_cases h : F₁.check s tr.fst = true <;> simp [h]

end Component.Front

/-! ## Runs of guarded components -/

namespace Component.Guarded

section Run

variable {StmtIn : Type} {ιi : Type} {OStmtIn : ιi → Type} {WitIn StmtOut : Type} {ιo : Type}
  {OStmtOut : ιo → Type} {WitOut : Type} [∀ i, OracleInterface (OStmtIn i)]
  [∀ i, OracleInterface (OStmtOut i)] {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]
  {D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}

/-- The run of a guarded component on a statement, its oracles and a transcript: the verdict and
the output oracles when the check passes. -/
def run (G : Guarded D) (s : StmtIn × ∀ i, OStmtIn i) (tr : pSpec.FullTranscript) :
    Option (StmtOut × ∀ i, OStmtOut i) :=
  if G.guarded.check s tr then some (G.guarded.out s tr) else none

/-- **The verifier's run is the guarded run**: run as an oracle computation, the component's
verifier returns the guarded run. -/
theorem verifier_run (G : Guarded D) (s : StmtIn × ∀ i, OStmtIn i)
    (tr : pSpec.FullTranscript) :
    (D.red.toReduction.verifier.run s tr).run = pure (G.run s tr) := by
  change (D.red.toReduction.verifier.verify s tr).run = _
  rw [G.guarded.verify_eq s tr, run]
  cases G.guarded.check s tr <;> rfl

/-- A run returns a verdict exactly when the check passes and the verdict is it. -/
theorem run_eq_some_iff (G : Guarded D) {s : StmtIn × ∀ i, OStmtIn i}
    {tr : pSpec.FullTranscript} {o : StmtOut × ∀ i, OStmtOut i} :
    G.run s tr = some o ↔ G.guarded.check s tr = true ∧ G.guarded.out s tr = o := by
  unfold run
  cases G.guarded.check s tr <;> simp

end Run

variable {ι₁ ι₂ ι₃ : Type} {OStmt₁ : ι₁ → Type} {OStmt₂ : ι₂ → Type} {OStmt₃ : ι₃ → Type}
  [∀ i, OracleInterface (OStmt₁ i)] [∀ i, OracleInterface (OStmt₂ i)]
  [∀ i, OracleInterface (OStmt₃ i)] {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type} {m₁ m₂ : ℕ}
  {pSpec₁ : ProtocolSpec m₁} {pSpec₂ : ProtocolSpec m₂}
  [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, OracleInterface (pSpec₂.Message i)] [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- **Guarded runs compose**: the run of two components in sequence is the first one's run on the
first part of the transcript, then the second one's from its verdict on the second part. -/
theorem run_append {D₁ : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁}
    {D₂ : Def Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂} (G₁ : Guarded D₁) (G₂ : Guarded D₂)
    (s : Stmt₁ × ∀ i, OStmt₁ i) (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    (G₁.append G₂).run s tr = (G₁.run s tr.fst).bind fun s' ↦ G₂.run s' tr.snd := by
  simp only [run, Guarded.append, guardedAppend_check, guardedAppend_out]
  by_cases h : G₁.guarded.check s tr.fst = true <;> simp [h]

/-- A front component's guarded run is its run, the oracles handed on. -/
theorem run_toGuarded {D : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₁ Wit₂ pSpec₁} (F : Front D)
    (p : Stmt₁ × ∀ i, OStmt₁ i) (tr : pSpec₁.FullTranscript) :
    F.toGuarded.run p tr = (F.run p.1 tr).map fun s' ↦ (s', p.2) := by
  simp only [run, Front.toGuarded, Front.run]
  by_cases hc : F.check p.1 tr = true <;> simp [hc]

/-- A run of two components in sequence that returns a verdict: the first one's run on the first
part of the transcript returns a verdict, from which the second one's returns the verdict. Applied
to a hypothesis, it unfolds the components' definitions as unification needs. -/
theorem run_append_eq_some {D₁ : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁}
    {D₂ : Def Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂} {G₁ : Guarded D₁} {G₂ : Guarded D₂}
    {s : Stmt₁ × ∀ i, OStmt₁ i} {tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript}
    {o : Stmt₃ × ∀ i, OStmt₃ i} (h : (G₁.append G₂).run s tr = some o) :
    ∃ x, G₁.run s tr.fst = some x ∧ G₂.run x tr.snd = some o := by
  rwa [run_append, Option.bind_eq_some_iff] at h

/-- A front component's guarded run that returns a verdict: its run returns it, the oracles
handed on. -/
theorem run_toGuarded_eq_some {D : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₁ Wit₂ pSpec₁} (F : Front D)
    {p : Stmt₁ × ∀ i, OStmt₁ i} {tr : pSpec₁.FullTranscript} {x : Stmt₂ × ∀ i, OStmt₁ i}
    (h : F.toGuarded.run p tr = some x) : ∃ y, F.run p.1 tr = some y ∧ (y, p.2) = x := by
  rwa [run_toGuarded, Option.map_eq_some_iff] at h

/-- A run of two components in sequence returns the second one's verdict, when the first one's
run on the first part of the transcript returns a verdict from which the second one's run returns
it. -/
theorem run_append_of_eq_some {D₁ : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁}
    {D₂ : Def Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂} {G₁ : Guarded D₁} {G₂ : Guarded D₂}
    {s : Stmt₁ × ∀ i, OStmt₁ i} {tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript}
    {x : Stmt₂ × ∀ i, OStmt₂ i} {o : Stmt₃ × ∀ i, OStmt₃ i} (h₁ : G₁.run s tr.fst = some x)
    (h₂ : G₂.run x tr.snd = some o) : (G₁.append G₂).run s tr = some o := by
  rw [run_append, h₁, Option.bind_some, h₂]

/-- A front component's guarded run returns its run's verdict, the oracles handed on. -/
theorem run_toGuarded_of_eq_some {D : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₁ Wit₂ pSpec₁}
    (F : Front D) {p : Stmt₁ × ∀ i, OStmt₁ i} {tr : pSpec₁.FullTranscript} {y : Stmt₂}
    (h : F.run p.1 tr = some y) : F.toGuarded.run p tr = some (y, p.2) := by
  rw [run_toGuarded, h]
  rfl

/-- A component whose verifier is pure, as a guarded one. -/
def ofPure {D : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁}
    (P : D.red.toReduction.verifier.PureForm) : Guarded D :=
  ⟨P.toGuardedForm⟩

/-- A pure component's run returns its verdict. -/
theorem run_ofPure {D : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁}
    (P : D.red.toReduction.verifier.PureForm) (s : Stmt₁ × ∀ i, OStmt₁ i)
    (tr : pSpec₁.FullTranscript) : (ofPure P).run s tr = some (P.verify s tr) :=
  rfl

/-- A pure component's run that returns a verdict returns its verdict. -/
theorem run_ofPure_eq_some {D : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁}
    {P : D.red.toReduction.verifier.PureForm} {s : Stmt₁ × ∀ i, OStmt₁ i}
    {tr : pSpec₁.FullTranscript} {x : Stmt₂ × ∀ i, OStmt₂ i} (h : (ofPure P).run s tr = some x) :
    P.verify s tr = x :=
  Option.some.inj h

end Component.Guarded

namespace Component.Front

variable {ι : Type} {OStmt : ι → Type} [∀ i, OracleInterface (OStmt i)]
  {StmtIn StmtOut WitIn WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]
  {D : Def StmtIn OStmt WitIn StmtOut OStmt WitOut pSpec}

/-- **A front component's verifier is its run**: run as an oracle computation, the component's
verifier returns the run, the oracles handed on. -/
theorem verifier_run (F : Front D) (s : StmtIn) (o : ∀ i, OStmt i)
    (tr : pSpec.FullTranscript) :
    (D.red.toReduction.verifier.run (s, o) tr).run = pure ((F.run s tr).map fun s' ↦ (s', o)) := by
  rw [F.toGuarded.verifier_run, Guarded.run_toGuarded]

end Component.Front

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)] {StmtIn StmtOut W : Type}

/-- The sample-challenge component runs its check, then maps the statement by the challenge. -/
theorem run_sampleFront (C : Type) [SampleableType C] (check : StmtIn → Bool)
    (f : StmtIn → C → StmtOut) (s : StmtIn) (c : C) :
    (sampleFront (W := W) OStmt C check f).run s (chalTr c) =
      if check s then some (f s c) else none :=
  rfl

/-- The checked message runs its check on the message, then maps the statement by it. -/
theorem run_sendCheckedFront (M : Type) (honest : (StmtIn × ∀ i, OStmt i) × W → M)
    (check : StmtIn → M → Bool) (out : StmtIn → M → StmtOut) (s : StmtIn) (m : M) :
    (sendCheckedFront OStmt M honest check out).run s (msgTr m) =
      if check s m then some (out s m) else none :=
  rfl

/-- The draws push their challenges, in order, onto the vector beside the statement. -/
theorem run_drawPushesFront (C : Type) [SampleableType C] :
    ∀ (j : ℕ) (s : StmtIn) (f : Fin j → C),
      (drawPushesFront (S := StmtIn) (W := W) OStmt C j).run s (chalsTr j f) =
        some (s, Vector.ofFn f)
  | 0, s, f => congrArg some (Prod.ext rfl (Vector.ext fun k h ↦ absurd h (Nat.not_lt_zero k)))
  | j + 1, s, f => by
    erw [Front.run_append]
    simp only [chalsTr, FullTranscript.append_fst, FullTranscript.append_snd]
    erw [run_drawPushesFront C j s, Option.bind_some, run_sampleFront]
    rw [Vector.ofFn_succ (f := f)]
    rfl

end Component

namespace SumcheckRound

section Transcript

variable {F : Type} {d : ℕ}

/-- The transcript of one round: the message, then the challenge. -/
def roundTr (q : Vector F (d + 1)) (c : F) : (roundSpec F d).FullTranscript :=
  msgTr q ++ₜ chalTr c

/-- The transcript of `i + 1` rounds: the first round's message and challenge, then the rest. -/
def roundsCons {i : ℕ} (q : Vector F (d + 1)) (c : F) (t : (roundsSpec F d i).FullTranscript) :
    (roundsSpec F d (i + 1)).FullTranscript :=
  roundTr q c ++ₜ t

/-- A transcript of rounds is its first round's message and challenge, then the rest. -/
theorem eq_roundsCons {i : ℕ} (t : (roundsSpec F d (i + 1)).FullTranscript) :
    t = roundsCons
        ((FullTranscript.fst (pSpec₁ := roundSpec F d) (pSpec₂ := roundsSpec F d i) t).fst 0)
        ((FullTranscript.fst (pSpec₁ := roundSpec F d) (pSpec₂ := roundsSpec F d i) t).snd 0)
        (FullTranscript.snd (pSpec₁ := roundSpec F d) (pSpec₂ := roundsSpec F d i) t) := by
  refine (FullTranscript.append_fst_snd (pSpec₁ := roundSpec F d) (pSpec₂ := roundsSpec F d i)
    t).symm.trans ?_
  rw [roundsCons, roundTr, ← eq_msgTr, ← eq_chalTr, FullTranscript.append_fst_snd]

end Transcript

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] {X : Type} {ι : Type}
  {O : ι → Type} [∀ i, OracleInterface (O i)] {W : Type} {d : ℕ}
  (P : Polys F X O W d) (wt : Weights F X) (m : ℕ)

/-- With no round left, the rounds' run carries the statement across the equality of stages. -/
theorem run_roundsFront_zero (j : ℕ) (h : j + 0 = m) (s : Stmt X F j)
    (tr : (roundsSpec F d 0).FullTranscript) :
    (roundsFront P wt m 0 j h).run s tr = some (s.1, (Vector.cast (by omega) s.2.1, s.2.2)) :=
  rfl

/-- **A round of the run**: the message is checked against the running claim, and the rest runs
from the statement with the challenge appended and the message's value there as the claim. -/
theorem run_roundsFront_succ (i j : ℕ) (h : j + (i + 1) = m) (s : Stmt X F j) (q : Message F d)
    (c : F) (tr : (roundsSpec F d i).FullTranscript) :
    (roundsFront P wt m (i + 1) j h).run s (roundsCons q c tr) =
      if check j wt s q then
        (roundsFront P wt m i (j + 1) (by omega)).run (next j s (evaluate d q c) c) tr
      else none := by
  rw [roundsCons]
  erw [Component.Front.run_append, FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [roundTr, FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.run_sendCheckedFront]
  simp only [ite_true, Option.bind_some]
  erw [Component.run_sampleFront]
  by_cases hc : check j wt s q = true <;> simp [hc]

end SumcheckRound

end
end LeanerVM.Protocol
