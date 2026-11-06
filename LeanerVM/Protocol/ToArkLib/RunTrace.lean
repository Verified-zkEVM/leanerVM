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
  empty one (`runsAs_empty`);
* `Prover.runWith_total_or`: in a reading where `pure` and `bind` also run forward, a run against
  a wire every round of which runs from every state but the bad ones (`RoundCodec.Every`) returns,
  or its first rounds reach a bad state; the property of every round is carried along `append` and
  the schedules' builders (`every_*`).

So a property of what a run writes is proved on the wire's schedule, phase by phase, with the
transcript in hand and no prover state.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

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

/-- A computation that runs from every state. -/
def RunSem.Total {w : Type → Type} [Monad w] {σ : Type} (sem : RunSem w σ) {α : Type}
    (x : w α) : Prop :=
  ∀ s, ∃ a s', sem.Runs x s a s'

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
  change HEq (Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .P_to_V → type → w Unit) c₁.send c₂.send (Fin.castAdd n i)) _
  rw [Fin.fappend₂_left]
  exact cast_heq _ _

omit [Monad w] in
/-- Past the seam, the appended wire writes as the second. -/
private theorem send_append_right (i : Fin n) :
    HEq ((c₁.append c₂).send (Fin.natAdd m i)) (c₂.send i) := by
  change HEq (Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .P_to_V → type → w Unit) c₁.send c₂.send (Fin.natAdd m i)) _
  rw [Fin.fappend₂_right]
  exact cast_heq _ _

omit [Monad w] in
/-- Below the seam, the appended wire reads as the first. -/
private theorem draw_append_left (i : Fin m) :
    HEq ((c₁.append c₂).draw (Fin.castAdd n i)) (c₁.draw i) := by
  change HEq (Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .V_to_P → w type) c₁.draw c₂.draw (Fin.castAdd n i)) _
  rw [Fin.fappend₂_left]
  exact cast_heq _ _

omit [Monad w] in
/-- Past the seam, the appended wire reads as the second. -/
private theorem draw_append_right (i : Fin n) :
    HEq ((c₁.append c₂).draw (Fin.natAdd m i)) (c₂.draw i) := by
  change HEq (Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .V_to_P → w type) c₁.draw c₂.draw (Fin.natAdd m i)) _
  rw [Fin.fappend₂_right]
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

/-! ## A property of every round of a wire -/

/-- A property of every computation the wire runs: each message's write and each challenge's
read. -/
def Every (P : ∀ α : Type, w α → Prop) {n : ℕ} {pSpec : ProtocolSpec n}
    (c : RoundCodec w pSpec) : Prop :=
  (∀ i h x, P _ (c.send i h x)) ∧ ∀ i h, P _ (c.draw i h)

variable {P : ∀ α : Type, w α → Prop}

omit [Monad w] in
/-- A property carried along an equality of value types. -/
private theorem prop_heq {α β : Type} (hab : α = β) {x : w α} {y : w β} (hxy : HEq x y)
    (hx : P α x) : P β y := by
  subst hab
  obtain rfl := eq_of_heq hxy
  exact hx

omit [Monad w] in
/-- A source of a round's challenge, carried along equalities of its direction and type, reads
as before. -/
private theorem apply_heq_draw {A A' : Direction} {B B' : Type} {f : A = .V_to_P → w B}
    {f' : A' = .V_to_P → w B'} (hA : A = A') (hB : B = B') (hf : HEq f f') (h : A = .V_to_P)
    (h' : A' = .V_to_P) : HEq (f h) (f' h') := by
  subst hA hB
  obtain rfl := eq_of_heq hf
  rfl

omit [Monad w] in
/-- Two wires in sequence have a property of every round when both do. -/
theorem Every.append {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n}
    {c₁ : RoundCodec w p₁} {c₂ : RoundCodec w p₂} (h₁ : Every P c₁) (h₂ : Every P c₂) :
    Every P (c₁.append c₂) := by
  refine ⟨fun i h x ↦ ?_, fun i h ↦ ?_⟩
  · induction i using Fin.addCases with
    | left j =>
      have hA : (p₁ ++ₚ p₂).dir (Fin.castAdd n j) = p₁.dir j := Fin.vappend_left _ _ _
      have hB : (p₁ ++ₚ p₂).Type (Fin.castAdd n j) = p₁.Type j := Fin.vappend_left _ _ _
      rw [apply_heq_send hA hB (send_append_left c₁ c₂ j) h (hA ▸ h) (cast_heq hB x).symm]
      exact h₁.1 _ _ _
    | right j =>
      have hA : (p₁ ++ₚ p₂).dir (Fin.natAdd m j) = p₂.dir j := Fin.vappend_right _ _ _
      have hB : (p₁ ++ₚ p₂).Type (Fin.natAdd m j) = p₂.Type j := Fin.vappend_right _ _ _
      rw [apply_heq_send hA hB (send_append_right c₁ c₂ j) h (hA ▸ h) (cast_heq hB x).symm]
      exact h₂.1 _ _ _
  · induction i using Fin.addCases with
    | left j =>
      have hA : (p₁ ++ₚ p₂).dir (Fin.castAdd n j) = p₁.dir j := Fin.vappend_left _ _ _
      have hB : (p₁ ++ₚ p₂).Type (Fin.castAdd n j) = p₁.Type j := Fin.vappend_left _ _ _
      exact prop_heq hB.symm (apply_heq_draw hA hB (draw_append_left c₁ c₂ j) h (hA ▸ h)).symm
        (h₁.2 _ _)
    | right j =>
      have hA : (p₁ ++ₚ p₂).dir (Fin.natAdd m j) = p₂.dir j := Fin.vappend_right _ _ _
      have hB : (p₁ ++ₚ p₂).Type (Fin.natAdd m j) = p₂.Type j := Fin.vappend_right _ _ _
      exact prop_heq hB.symm (apply_heq_draw hA hB (draw_append_right c₁ c₂ j) h (hA ▸ h)).symm
        (h₂.2 _ _)

omit [Monad w] in
/-- The empty wire runs nothing. -/
theorem every_empty : Every P (empty : RoundCodec w !p[]) :=
  ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩

omit [Monad w] in
/-- A message's wire has a property of every round when its encoder does. -/
theorem every_msg {M : Type} {enc : M → w Unit} (h : ∀ x, P _ (enc x)) : Every P (msg enc) :=
  ⟨fun i _ x ↦ (match i with | ⟨0, _⟩ => h x), fun i h ↦ match i, h with | ⟨0, _⟩, h => nomatch h⟩

omit [Monad w] in
/-- A message's wire of a literal schedule has a property of every round when its encoder
does. -/
theorem every_sendOne {M : Type} {enc : M → w Unit} (h : ∀ x, P _ (enc x)) :
    Every P (sendOne enc) :=
  ⟨fun i _ x ↦ (match i with | ⟨0, _⟩ => h x), fun i h ↦ match i, h with | ⟨0, _⟩, h => nomatch h⟩

omit [Monad w] in
/-- A challenge's wire has a property of every round when its source does. -/
theorem every_chal {C : Type} {smp : w C} (h : P C smp) : Every P (chal smp) :=
  ⟨fun i h ↦ (match i, h with | ⟨0, _⟩, h => nomatch h), fun i _ ↦ match i with | ⟨0, _⟩ => h⟩

omit [Monad w] in
/-- Runs of challenges. -/
theorem every_chals {C : Type} {smp : w C} (h : P C smp) : ∀ k, Every P (chals smp k)
  | 0 => every_empty
  | k + 1 => (every_chals h k).append (every_chal h)

omit [Monad w] in
/-- Runs of rounds. -/
theorem every_rounds {C : Type} {d : ℕ} {enc : Vector C (d + 1) → w Unit} {smp : w C}
    (he : ∀ x, P _ (enc x)) (hs : P C smp) : ∀ m, Every P (rounds enc smp m)
  | 0 => every_empty
  | m + 1 => ((every_msg he).append (every_chal hs)).append (every_rounds he hs m)

omit [Monad w] in
/-- A grand-product layer. -/
theorem every_step {C : Type} {nside : ℕ} (ρ m : ℕ) {enc : Vector C (2 ^ ρ + 1) → w Unit}
    {children : (Fin nside → Vector C (2 ^ ρ)) → w Unit} {smp : w C} (he : ∀ x, P _ (enc x))
    (hc : ∀ x, P _ (children x)) (hs : P C smp) : Every P (step ρ m enc children smp) :=
  (((every_chal hs).append (every_rounds he hs m)).append (every_msg hc)).append
    (every_chals hs ρ)

omit [Monad w] in
/-- The grand-product argument. -/
theorem every_gkr {C : Type} {nside : ℕ} (μ : ℕ) {enc₁ : Vector C (2 ^ 1 + 1) → w Unit}
    {children₁ : (Fin nside → Vector C (2 ^ 1)) → w Unit} {enc₂ : Vector C (2 ^ 2 + 1) → w Unit}
    {children₂ : (Fin nside → Vector C (2 ^ 2)) → w Unit} {smp : w C} (he₁ : ∀ x, P _ (enc₁ x))
    (hc₁ : ∀ x, P _ (children₁ x)) (he₂ : ∀ x, P _ (enc₂ x)) (hc₂ : ∀ x, P _ (children₂ x))
    (hs : P C smp) : Every P (gkr μ enc₁ children₁ enc₂ children₂ smp) := by
  have hsteps : ∀ k m, Every P (steps enc₂ children₂ smp k m) := by
    intro k
    induction k with
    | zero => exact fun _ ↦ every_empty
    | succ k ih => exact fun m ↦ (every_step 2 m he₂ hc₂ hs).append (ih (m + 2))
  have hodd : ∀ r, Every P (odd enc₁ children₁ smp r) := fun r ↦ match r with
    | 0 => every_empty
    | _ + 1 => every_step 1 0 he₁ hc₁ hs
  exact ((hodd _).append (hsteps _ _)).append (every_chal hs)

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
    obtain ⟨x, hx, hr⟩ : ∃ x, c.StepAs sem j x sm s' ∧ r.1 = tr.concat x := by
      unfold stepWith at h₂
      split at h₂
      · rename_i hDir
        obtain ⟨x, sm₂, h₃, h₄⟩ := sem.bind_inv h₂
        rw [runNoOracle_eq_pure (w := w), pure_bind] at h₄
        obtain ⟨hr, rfl⟩ := sem.pure_inv h₄
        exact ⟨x, ⟨fun h' ↦ absurd (h'.symm.trans hDir) (by decide), fun _ ↦ h₃⟩, by rw [hr]⟩
      · rename_i hDir
        rw [runNoOracle_eq_pure (w := w), pure_bind] at h₂
        obtain ⟨u, sm₂, h₃, h₄⟩ := sem.bind_inv h₂
        obtain ⟨hr, rfl⟩ := sem.pure_inv h₄
        exact ⟨_, ⟨fun _ ↦ h₃, fun h' ↦ absurd (h'.symm.trans hDir) (by decide)⟩, by rw [hr]⟩
    refine ⟨Function.update st j.succ s', ?_, by simp, fun k hk ↦ ?_⟩
    · rw [Function.update_of_ne (Fin.succ_ne_zero j).symm, h0]
    have hk' : k ≤ j := Fin.le_iff_val_le_val.mpr (by simp only [Fin.val_succ] at hk; omega)
    rw [Function.update_of_ne (Fin.castSucc_lt_succ_iff.mpr hk').ne, hr]
    rcases hk'.lt_or_eq with hlt | rfl
    · rw [Function.update_of_ne (Fin.succ_lt_succ_iff.mpr hlt).ne,
        eq_of_heq (Transcript.concat_apply_lt tr x k.val hlt hk)]
      exact hs k hlt
    · rw [Function.update_self, hj, eq_of_heq (Transcript.concat_apply_last tr x k.val rfl hk)]
      exact hx

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

/-- **A run against a wire runs, or stops at a bad state it reaches**, when every round of the
wire runs from every state but the bad ones: from `s`, either the run returns, or for some `i` the
first `i` rounds run from `s` to a bad state. -/
theorem runWith_total_or (Bad : σ → Prop)
    (hpure : ∀ {α : Type} (a : α) (s : σ), sem.Runs (pure a) s a s)
    (hbind : ∀ {α β : Type} {x : w α} {f : α → w β} {s sm s' : σ} {a : α} {b : β},
      sem.Runs x s a sm → sem.Runs (f a) sm b s' → sem.Runs (x >>= f) s b s')
    (hc : c.Every fun _ x ↦ ∀ s, (∃ a s', sem.Runs x s a s') ∨ Bad s) (stmt : St) (wit : Wt)
    (s : σ) :
    (∃ r s', sem.Runs (runWith c P stmt wit) s r s') ∨
      ∃ i r s', sem.Runs (runToRoundWith c P i stmt wit) s r s' ∧ Bad s' := by
  have hstep : ∀ (j : Fin n) tr st sm,
      (∃ b s', sem.Runs (stepWith c P j tr st) sm b s') ∨ Bad sm := by
    intro j tr st sm
    unfold stepWith
    split
    · rename_i hDir
      simp only [runNoOracle_eq_pure (w := w), pure_bind]
      exact (hc.2 j hDir sm).imp_left fun ⟨_, s', h₁⟩ ↦ ⟨_, s', hbind h₁ (hpure _ s')⟩
    · rename_i hDir
      simp only [runNoOracle_eq_pure (w := w), pure_bind]
      exact (hc.1 j hDir _ sm).imp_left fun ⟨_, s', h₁⟩ ↦ ⟨_, s', hbind h₁ (hpure _ s')⟩
  have hround : ∀ i : Fin (n + 1), (∃ r s', sem.Runs (runToRoundWith c P i stmt wit) s r s') ∨
      ∃ i r s', sem.Runs (runToRoundWith c P i stmt wit) s r s' ∧ Bad s' := by
    intro i
    induction i using Fin.induction with
    | zero =>
      simp only [runToRoundWith, Fin.induction_zero]
      exact .inl ⟨_, s, hpure _ s⟩
    | succ j ih =>
      rcases ih with ⟨r, sm, h₁⟩ | hb
      · rcases hstep j r.1 r.2 sm with ⟨b, s', h₂⟩ | hb
        · rw [runToRoundWith_succ, processRoundWith]
          exact .inl ⟨b, s', hbind h₁ h₂⟩
        · exact .inr ⟨_, r, sm, h₁, hb⟩
      · exact .inr hb
  refine (hround (Fin.last n)).imp_left fun ⟨r, sm, h₁⟩ ↦ ?_
  unfold runWith
  simp only [runNoOracle_eq_pure (w := w), pure_bind]
  exact ⟨_, sm, hbind h₁ (hpure _ sm)⟩

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
    trans cast (challenge_append_inl (pSpec₂ := pSpec₂) i) <$>
      (pure (ch (ChallengeIdx.inl i)) : r _)
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
