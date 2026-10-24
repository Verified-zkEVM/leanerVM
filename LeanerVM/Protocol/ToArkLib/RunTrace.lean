/-
  LeanerVM.Protocol.ToArkLib.RunTrace

  A run against a wire read off the transcript it returns: in a monad whose computations run
  from state to state, every run of a prover against a wire steps through the wire's rounds on
  its transcript, each message written as the transcript has it and each challenge read as it has
  it; the steps of two schedules in sequence split at the seam. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.RunCodec
public import LeanerVM.Protocol.ToArkLib.ExtractIn

/-!
# The trace of a run against a wire

`Prover.runWith c P` runs `P` round by round against the wire `c` (`LeanerVM.Protocol.ToArkLib.
RunCodec`). In a monad whose computations run deterministically from state to state (`RunSem`:
`Runs x s a s'`, inverting `pure` and `bind`), what the run does is a function of the transcript
it returns: `RoundCodec.RunsAs c tr s s'` says that the wire, stepped on the rounds of `tr`, goes
from `s` to `s'` through one state per round, each message round writing `tr`'s message and each
challenge round reading `tr`'s challenge.

* `Prover.runWith_runsAs`: every run from `s` to `s'` returning the transcript `tr` steps through
  the wire on `tr`, whatever the prover;
* `RoundCodec.RunsAs.append_inv`: the steps of `c₁.append c₂` on a transcript are those of `c₁` on
  its first half, then those of `c₂` on its second half;
* the steps of the one-round wires (`runsAs_msg`, `runsAs_sendOne`, `runsAs_chal`) and of the
  empty one (`runsAs_empty`).

So a property of what a run writes is proved on the wire's schedule, phase by phase, with the
transcript in hand and no prover state.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

/-- The second half of a transcript of two schedules in sequence, at a round, is the transcript
at that round, up to the cast of the schedule. -/
theorem FullTranscript.snd_heq {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (i : Fin n) :
    HEq (T.snd i) (T (Fin.natAdd m i)) := by
  unfold FullTranscript.snd
  exact cast_heq _ _

/-- A deterministic reading of a monad `w` on states `σ`: `Runs x s a s'` when `x`, run from `s`,
returns `a` in `s'`. It inverts `pure` and `bind`, and a run returns a value of which the
computation satisfies whatever `SatisfiesM` says. -/
structure RunSem (w : Type → Type) [Monad w] (σ : Type) where
  /-- `x` run from `s` returns `a` in `s'`. -/
  Runs : {α : Type} → w α → σ → α → σ → Prop
  /-- A pure computation returns its value and keeps the state. -/
  pure_inv : ∀ {α : Type} {a b : α} {s s' : σ}, Runs (pure a) s b s' → b = a ∧ s' = s
  /-- A bound computation runs its first part, then its continuation. -/
  bind_inv : ∀ {α β : Type} {x : w α} {f : α → w β} {s s' : σ} {b : β},
    Runs (x >>= f) s b s' → ∃ a sm, Runs x s a sm ∧ Runs (f a) sm b s'
  /-- A run returns a value of which the computation satisfies what it satisfies. -/
  satisfies : ∀ {α : Type} {p : α → Prop} {x : w α} {s s' : σ} {a : α},
    SatisfiesM p x → Runs x s a s' → p a

namespace RoundCodec

variable {w : Type → Type} [Monad w] {σ : Type} (sem : RunSem w σ)

/-- Round `i` of the wire from `s` to `s'` on the round's value `x`: written, if it is a message;
read as `x`, if it is a challenge. -/
def StepAs {n : ℕ} {pSpec : ProtocolSpec n} (c : RoundCodec w pSpec) (i : Fin n)
    (x : pSpec.Type i) (s s' : σ) : Prop :=
  (∀ h : pSpec.dir i = .P_to_V, sem.Runs (c.send i h x) s () s') ∧
    ∀ h : pSpec.dir i = .V_to_P, sem.Runs (c.draw i h) s x s'

/-- **The steps of the wire on a transcript**: from `s` to `s'` through a state at every round,
each round stepped on the transcript's value. -/
def RunsAs {n : ℕ} {pSpec : ProtocolSpec n} (c : RoundCodec w pSpec) (tr : pSpec.FullTranscript)
    (s s' : σ) : Prop :=
  ∃ st : Fin (n + 1) → σ, st 0 = s ∧ st (Fin.last n) = s' ∧
    ∀ i : Fin n, c.StepAs sem i (tr i) (st i.castSucc) (st i.succ)

/-! ## The seam -/

/-- A function of a round's direction and type, carried along equalities of both, applies as
before. -/
private theorem apply_heq_send {R : Type} {A A' : Direction} {B B' : Type}
    {f : A = .P_to_V → B → R} {f' : A' = .P_to_V → B' → R} (hA : A = A') (hB : B = B')
    (hf : HEq f f') (h : A = .P_to_V) (h' : A' = .P_to_V) {x : B} {x' : B'} (hx : HEq x x') :
    f h x = f' h' x' := by
  subst hA hB
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hx
  rfl

/-- A source of a round's challenge, carried along equalities of its direction and type, runs
as before. -/
private theorem runs_heq_draw {A A' : Direction} {B B' : Type} {f : A = .V_to_P → w B}
    {f' : A' = .V_to_P → w B'} (hA : A = A') (hB : B = B') (hf : HEq f f') (h : A = .V_to_P)
    (h' : A' = .V_to_P) {x : B} {x' : B'} (hx : HEq x x') {s s' : σ} :
    sem.Runs (f h) s x s' ↔ sem.Runs (f' h') s x' s' := by
  subst hA hB
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hx
  rfl

variable {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n} (c₁ : RoundCodec w p₁)
  (c₂ : RoundCodec w p₂)

omit [Monad w] in
/-- Below the seam, the appended wire writes as the first. -/
private theorem send_append_left (i : Fin m) :
    HEq ((c₁.append c₂).send (Fin.castAdd n i)) (c₁.send i) := by
  change HEq (fappend₂Lazy (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .P_to_V → type → w Unit) c₁.send c₂.send (Fin.castAdd n i)) _
  rw [← fappend₂_eq_fappend₂Lazy, Fin.fappend₂_left]
  exact cast_heq _ _

omit [Monad w] in
/-- Past the seam, the appended wire writes as the second. -/
private theorem send_append_right (i : Fin n) :
    HEq ((c₁.append c₂).send (Fin.natAdd m i)) (c₂.send i) := by
  change HEq (fappend₂Lazy (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .P_to_V → type → w Unit) c₁.send c₂.send (Fin.natAdd m i)) _
  rw [← fappend₂_eq_fappend₂Lazy, Fin.fappend₂_right]
  exact cast_heq _ _

omit [Monad w] in
/-- Below the seam, the appended wire reads as the first. -/
private theorem draw_append_left (i : Fin m) :
    HEq ((c₁.append c₂).draw (Fin.castAdd n i)) (c₁.draw i) := by
  change HEq (fappend₂Lazy (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .V_to_P → w type) c₁.draw c₂.draw (Fin.castAdd n i)) _
  rw [← fappend₂_eq_fappend₂Lazy, Fin.fappend₂_left]
  exact cast_heq _ _

omit [Monad w] in
/-- Past the seam, the appended wire reads as the second. -/
private theorem draw_append_right (i : Fin n) :
    HEq ((c₁.append c₂).draw (Fin.natAdd m i)) (c₂.draw i) := by
  change HEq (fappend₂Lazy (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .V_to_P → w type) c₁.draw c₂.draw (Fin.natAdd m i)) _
  rw [← fappend₂_eq_fappend₂Lazy, Fin.fappend₂_right]
  exact cast_heq _ _

/-- A round below the seam steps as the first wire's. -/
private theorem stepAs_append_left (i : Fin m) {x : (p₁ ++ₚ p₂).Type (Fin.castAdd n i)}
    {x' : p₁.Type i} (hx : HEq x x') {s s' : σ}
    (h : (c₁.append c₂).StepAs sem (Fin.castAdd n i) x s s') : c₁.StepAs sem i x' s s' := by
  have hA : (p₁ ++ₚ p₂).dir (Fin.castAdd n i) = p₁.dir i := Fin.vappend_left _ _ _
  have hB : (p₁ ++ₚ p₂).Type (Fin.castAdd n i) = p₁.Type i := Fin.vappend_left _ _ _
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · have := h.1 (hA.trans h')
    rwa [apply_heq_send hA hB (send_append_left c₁ c₂ i) (hA.trans h') h' hx] at this
  · exact (runs_heq_draw sem hA hB (draw_append_left c₁ c₂ i) (hA.trans h') h' hx).mp
      (h.2 (hA.trans h'))

/-- A round past the seam steps as the second wire's. -/
private theorem stepAs_append_right (i : Fin n) {x : (p₁ ++ₚ p₂).Type (Fin.natAdd m i)}
    {x' : p₂.Type i} (hx : HEq x x') {s s' : σ}
    (h : (c₁.append c₂).StepAs sem (Fin.natAdd m i) x s s') : c₂.StepAs sem i x' s s' := by
  have hA : (p₁ ++ₚ p₂).dir (Fin.natAdd m i) = p₂.dir i := Fin.vappend_right _ _ _
  have hB : (p₁ ++ₚ p₂).Type (Fin.natAdd m i) = p₂.Type i := Fin.vappend_right _ _ _
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · have := h.1 (hA.trans h')
    rwa [apply_heq_send hA hB (send_append_right c₁ c₂ i) (hA.trans h') h' hx] at this
  · exact (runs_heq_draw sem hA hB (draw_append_right c₁ c₂ i) (hA.trans h') h' hx).mp
      (h.2 (hA.trans h'))

variable {c₁ c₂} in
/-- **The steps of two wires in sequence split at the seam**: the first wire's on the first half
of the transcript, then the second's on the second half. -/
theorem RunsAs.append_inv {tr : (p₁ ++ₚ p₂).FullTranscript} {s s' : σ}
    (h : (c₁.append c₂).RunsAs sem tr s s') :
    ∃ sm, c₁.RunsAs sem tr.fst s sm ∧ c₂.RunsAs sem tr.snd sm s' := by
  obtain ⟨st, h0, hl, hs⟩ := h
  refine ⟨st ⟨m, by omega⟩, ⟨fun k ↦ st ⟨k.val, by omega⟩, ?_, rfl, fun i ↦ ?_⟩,
    ⟨fun k ↦ st ⟨m + k.val, by omega⟩, rfl, ?_, fun i ↦ ?_⟩⟩
  · rw [← h0]
    rfl
  · exact stepAs_append_left sem c₁ c₂ i (FullTranscript.fst_heq tr i).symm (hs (Fin.castAdd n i))
  · rw [← hl]
    rfl
  · exact stepAs_append_right sem c₁ c₂ i (FullTranscript.snd_heq tr i).symm (hs (Fin.natAdd m i))

/-! ## The one-round wires -/

variable {sem}

/-- The empty wire stays put. -/
theorem runsAs_empty {tr : (!p[] : ProtocolSpec 0).FullTranscript} {s s' : σ}
    (h : (empty : RoundCodec w !p[]).RunsAs sem tr s s') : s' = s := by
  obtain ⟨st, h0, hl, -⟩ := h
  rw [← hl, ← h0]
  rfl

/-- A message's wire writes the transcript's message. -/
theorem runsAs_msg {M : Type} {enc : M → w Unit} {tr : (say M).FullTranscript} {s s' : σ}
    (h : (msg enc).RunsAs sem tr s s') : sem.Runs (enc (tr 0)) s () s' := by
  obtain ⟨st, h0, hl, hs⟩ := h
  rw [← h0, ← hl]
  exact (hs 0).1 rfl

/-- A message's wire of a literal schedule writes the transcript's message. -/
theorem runsAs_sendOne {M : Type} {enc : M → w Unit}
    {tr : (⟨!v[.P_to_V], !v[M]⟩ : ProtocolSpec 1).FullTranscript} {s s' : σ}
    (h : (sendOne enc).RunsAs sem tr s s') : sem.Runs (enc (tr 0)) s () s' := by
  obtain ⟨st, h0, hl, hs⟩ := h
  rw [← h0, ← hl]
  exact (hs 0).1 rfl

/-- A challenge's wire reads the transcript's challenge. -/
theorem runsAs_chal {C : Type} {smp : w C} {tr : (Protocol.draw C).FullTranscript} {s s' : σ}
    (h : (chal smp).RunsAs sem tr s s') : sem.Runs smp s (tr 0) s' := by
  obtain ⟨st, h0, hl, hs⟩ := h
  rw [← h0, ← hl]
  exact (hs 0).2 rfl

end RoundCodec

/-! ## Every run steps through the wire on its transcript -/

namespace Prover

variable {w : Type → Type} [Monad w] [LawfulMonad w] {σ : Type} (sem : RunSem w σ)
  {St Wt St' Wt' : Type} {n : ℕ} {pSpec : ProtocolSpec n} (c : RoundCodec w pSpec)
  (P : Prover []ₒ St Wt St' Wt' pSpec)

/-- The rounds up to `i` step through the wire on the partial transcript they return. -/
theorem runToRoundWith_runsAs (stmt : St) (wit : Wt) :
    ∀ (i : Fin (n + 1)) {s s' : σ} {r : pSpec.Transcript i × P.PrvState i},
      sem.Runs (runToRoundWith c P i stmt wit) s r s' →
      ∃ st : Fin (n + 1) → σ, st 0 = s ∧ st i = s' ∧
        ∀ (j : Fin n) (hj : j.val < i.val),
          c.StepAs sem j (r.1 ⟨j.val, hj⟩) (st j.castSucc) (st j.succ) := by
  intro i
  induction i using Fin.induction with
  | zero =>
    intro s s' r h
    obtain ⟨-, hs⟩ := sem.pure_inv h
    exact ⟨fun _ ↦ s, rfl, hs.symm, fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩
  | succ j ih =>
    intro s s' r h
    rw [runToRoundWith_succ, processRoundWith] at h
    obtain ⟨⟨tr, stP⟩, sm, h₁, h₂⟩ := sem.bind_inv h
    obtain ⟨st, h0, hj, hs⟩ := ih h₁
    have key : ∀ (x : pSpec.Type j), c.StepAs sem j x sm s' →
        r.1 = tr.concat x → ∃ st' : Fin (n + 1) → σ, st' 0 = s ∧ st' j.succ = s' ∧
          ∀ (k : Fin n) (hk : k.val < j.succ.val),
            c.StepAs sem k (r.1 ⟨k.val, hk⟩) (st' k.castSucc) (st' k.succ) := by
      intro x hx hr
      refine ⟨Function.update st j.succ s', ?_, by simp, fun k hk ↦ ?_⟩
      · rw [Function.update_of_ne (Fin.succ_ne_zero j).symm, h0]
      · have hk' : k.val ≤ j.val := by simp only [Fin.val_succ] at hk; omega
        have hc : k.castSucc ≠ j.succ := by
          intro he
          have := congrArg Fin.val he
          simp only [Fin.val_castSucc, Fin.val_succ] at this
          omega
        rw [Function.update_of_ne hc]
        rcases Nat.lt_or_eq_of_le hk' with hlt | heq
        · have hs' : k.succ ≠ j.succ := fun he ↦ by
            have := congrArg Fin.val he
            simp only [Fin.val_succ] at this
            omega
          rw [Function.update_of_ne hs', hr]
          have hv := eq_of_heq (Transcript.concat_apply_lt tr x k.val hlt hk)
          rw [hv]
          exact hs k hlt
        · obtain rfl : k = j := Fin.ext heq
          rw [Function.update_self, hj, hr]
          have hv := eq_of_heq (Transcript.concat_apply_last tr x k.val rfl hk)
          rw [hv]
          exact hx
    unfold stepWith at h₂
    split at h₂
    · rename_i hDir
      obtain ⟨x, sm₂, h₃, h₄⟩ := sem.bind_inv h₂
      rw [runNoOracle_eq_pure (w := w), pure_bind] at h₄
      obtain ⟨hr, rfl⟩ := sem.pure_inv h₄
      refine key x ⟨fun h' ↦ absurd (h'.symm.trans hDir) (by decide), fun _ ↦ h₃⟩ ?_
      rw [hr]
    · rename_i hDir
      rw [runNoOracle_eq_pure (w := w), pure_bind] at h₂
      obtain ⟨u, sm₂, h₃, h₄⟩ := sem.bind_inv h₂
      obtain ⟨hr, rfl⟩ := sem.pure_inv h₄
      refine key _ ⟨fun _ ↦ h₃, fun h' ↦ absurd (h'.symm.trans hDir) (by decide)⟩ ?_
      rw [hr]

/-- **Every run against a wire steps through the wire on the transcript it returns**: a message
round writes the transcript's message, a challenge round reads the transcript's challenge,
whatever the prover. -/
theorem runWith_runsAs (stmt : St) (wit : Wt) {s s' : σ}
    {r : pSpec.FullTranscript × St' × Wt'} (h : sem.Runs (runWith c P stmt wit) s r s') :
    c.RunsAs sem r.1 s s' := by
  unfold runWith at h
  obtain ⟨r₀, sm, h₁, h₂⟩ := sem.bind_inv h
  rw [runNoOracle_eq_pure (w := w), pure_bind] at h₂
  obtain ⟨rfl, rfl⟩ := sem.pure_inv h₂
  obtain ⟨st, h0, hl, hs⟩ := runToRoundWith_runsAs sem c P stmt wit (Fin.last n) h₁
  exact ⟨st, h0, hl, fun i ↦ hs i i.isLt⟩

omit [LawfulMonad w] in
/-- Two provers whose runs agree on an input run alike on it on every challenge vector. -/
theorem runWithChallenges_eq_of_run_eq {P' : Prover []ₒ St Wt St' Wt' pSpec} {stmt : St}
    {wit : Wt} (h : P.run stmt wit = P'.run stmt wit) (ch : pSpec.Challenges) :
    runWithChallenges P ch stmt wit = runWithChallenges P' ch stmt wit := by
  have h₁ := simulateQ_run_eq_runWithChallenges (r := Id) P ch stmt wit
  have h₂ := simulateQ_run_eq_runWithChallenges (r := Id) P' ch stmt wit
  rw [h] at h₁
  exact h₁.symm.trans h₂

end Prover

/-! ## The run on given challenges of two provers in sequence -/

section Append

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- The challenges of the first schedule in a challenge vector of two schedules in sequence. -/
def challengesLeft (ch : (pSpec₁ ++ₚ pSpec₂).Challenges) : pSpec₁.Challenges :=
  fun i ↦ cast (challenge_append_inl i) (ch (ChallengeIdx.inl i))

/-- A computation of the first schedule, lifted into the sequence, with the challenge oracle
answered off a vector: the computation with its own challenges answered off the vector's first
part. -/
theorem simulateQ_liftAppendLeft_challenges {r : Type → Type} [Monad r] [LawfulMonad r] {α : Type}
    (ch : (pSpec₁ ++ₚ pSpec₂).Challenges) (oa : OracleComp ([]ₒ + [pSpec₁.Challenge]ₒ) α) :
    simulateQ ((fun t ↦ isEmptyElim t : QueryImpl []ₒ r) + Prover.challengesImpl (r := r) ch)
        (liftAppendLeft pSpec₂ oa) =
      simulateQ ((fun t ↦ isEmptyElim t : QueryImpl []ₒ r) +
        Prover.challengesImpl (r := r) (challengesLeft ch)) oa := by
  unfold liftAppendLeft
  apply QueryImpl.simulateQ_liftM_eq_of_query
  intro t
  rcases t with t | ⟨i, ⟨⟩⟩
  · exact isEmptyElim t
  · change simulateQ _ (cast (challenge_append_inl (pSpec₂ := pSpec₂) i) <$>
        (liftM (([]ₒ + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).query
          (Sum.inr ⟨ChallengeIdx.inl i, ()⟩)))) = _
    rw [simulateQ_map]
    trans cast (challenge_append_inl (pSpec₂ := pSpec₂) i) <$> (pure (ch (ChallengeIdx.inl i)) : r _)
    · congr 1
      exact (simulateQ_spec_query ((fun t ↦ isEmptyElim t : QueryImpl []ₒ r) +
        Prover.challengesImpl (r := r) ch) (Sum.inr ⟨ChallengeIdx.inl i, ()⟩ :
          ([]ₒ + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Domain)).trans rfl
    · rw [map_pure]
      rfl

/-- **The transcript of two provers in sequence, on given challenges, begins with the first's**:
the first prover's run on the challenges of its schedule. -/
theorem runWithChallenges_append_fst {S₁ W₁ S₂ W₂ S₃ W₃ : Type}
    (P₁ : Prover []ₒ S₁ W₁ S₂ W₂ pSpec₁) (P₂ : Prover []ₒ S₂ W₂ S₃ W₃ pSpec₂)
    (ch : (pSpec₁ ++ₚ pSpec₂).Challenges) (stmt : S₁) (wit : W₁) :
    (Prover.runWithChallenges (P₁.append P₂) ch stmt wit).1.fst =
      (Prover.runWithChallenges P₁ (challengesLeft ch) stmt wit).1 := by
  have h := Prover.simulateQ_run_eq_runWithChallenges (r := Id) (P₁.append P₂) ch stmt wit
  rw [Prover.append_run, simulateQ_bind, simulateQ_liftAppendLeft_challenges,
    Prover.simulateQ_run_eq_runWithChallenges, pure_bind] at h
  rcases hR : Prover.runWithChallenges P₁ (challengesLeft ch) stmt wit with ⟨tr₁, s₂, w₂⟩
  rw [hR] at h
  rw [← show _ = Prover.runWithChallenges (P₁.append P₂) ch stmt wit from h]
  simp only [simulateQ_bind, simulateQ_pure]
  generalize (simulateQ ((fun t ↦ isEmptyElim t : QueryImpl []ₒ Id) +
    Prover.challengesImpl (r := Id) ch) (liftAppendRight pSpec₁ (P₂.run s₂ w₂)) : Id _) = X
  obtain ⟨t₂, s₃, w₃⟩ := X
  exact FullTranscript.append_fst _ _

end Append

end
end LeanerVM.Protocol
