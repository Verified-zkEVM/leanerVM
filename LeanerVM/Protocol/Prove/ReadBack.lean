/-
  LeanerVM.Protocol.Prove.ReadBack

  The verifier's chain walk reads the honest prover's stream back: on the stream the compiled
  protocol's honest prover writes against its wire, the walk returns the wire of the prover's
  transcript, challenges included, up to what the algebra does not read.
-/

module

public import LeanerVM.Protocol.Prove
public import LeanerVM.Protocol.ToArkLib.RunTrace
public import LeanerVM.Protocol.Verify.WireOf
public import LeanerVM.Protocol.Verify.Erase

/-!
# The walk reads the prover's stream back

The honest prover (`LeanerVM.Protocol.Prove`) runs the compiled protocol's prover against the
wire of its schedule (`compiledCodec`) in `ProveM Id`, the writer of the proof beside a book of
the commitments and positions it keeps. That monad runs from state to state (`proveSem`), so by
`Prover.runWith_runsAs` every run steps through the wire on the transcript it returns: what the
prover writes is a function of its transcript, phase by phase.

`Reads rd w w' b`: the reader `rd`, run from the writer state `w`'s chain state on what the writer
appended between `w` and `w'`, followed by anything, returns `b`, consumes exactly that and ends in
`w'`'s chain state (the round trip of `LeanerVM.Protocol.Proof`'s `ReadsBack`, for one run).
`Back rd s s' b` is `Reads` with the book and the openings kept.

* the writer's primitives (`proveOps`) read back by the walk's (`Verify.readerOps`): a scalar,
  a challenge, the grinding nonce, a committed root, the positions;
* each phase's wire read back by its walk: the level-0 commitment's root, the bus phase
  (`back_bus`), the table sumcheck, the public input, the Flock phase, and WHIR's levels
  (`back_ladder`), the walk's wire equal to the transcript's (`DecodeChain.wireOf`) but for the
  roots, the nonces and the positions' reduction (`Verify.Wire.erase`);
* `walkChain_reads`: the chain walk reads the announcement and the whole wire back, and the book
  holds the commitments and positions the openings need.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa Whir CompPoly
open OracleComp OracleSpec ProtocolSpec StepSchedule DecodeChain

@[expose] public section

namespace Prove

/-! ## The prover's monad, run from state to state -/

/-- The prover's state: the book and the writer's state. -/
abbrev PState : Type := Book × WriterState PrunedMerklePaths

/-- The prover's monad in `Id`, read from state to state. -/
def proveSem : RunSem (ProveM Id) PState where
  Runs x s a s' := ((x.run s.1).run s.2).run = some ((a, s'.1), s'.2)
  pure_inv h := by
    simp only [StateT.run_pure, OptionT.run_pure] at h
    obtain ⟨⟨rfl, h₁⟩, h₂⟩ := Prod.mk.inj (Option.some.inj h) |>.imp Prod.mk.inj id
    exact ⟨rfl, Prod.ext h₁.symm h₂.symm⟩
  bind_inv {α β x f s s' b} h := by
    simp only [StateT.run_bind, OptionT.run_bind] at h
    rcases h₁ : ((x.run s.1).run s.2).run with _ | ⟨⟨a, bk⟩, ws⟩
    · rw [h₁] at h
      cases h
    · rw [h₁] at h
      exact ⟨a, (bk, ws), rfl, h⟩
  satisfies {α p x s s' a} h hr := by
    obtain ⟨x', rfl⟩ := h
    simp only [StateT.run_map, OptionT.run_map] at hr
    rcases h₁ : ((x'.run s.1).run s.2).run with _ | ⟨⟨a', bk⟩, ws⟩
    · rw [h₁] at hr
      cases hr
    · rw [h₁] at hr
      obtain ⟨⟨rfl, -⟩, -⟩ := Prod.mk.inj (Option.some.inj hr) |>.imp Prod.mk.inj id
      exact a'.2

/-- A writer's step lifted to the prover keeps the book. -/
theorem runs_lift {α : Type} {y : WriteM Id PrunedMerklePaths α} {s s' : PState} {a : α} :
    proveSem.Runs (StateT.lift y : ProveM Id α) s a s' ↔
      s'.1 = s.1 ∧ (y.run s.2).run = some (a, s'.2) := by
  change (((StateT.lift y : ProveM Id α).run s.1).run s.2).run = some ((a, s'.1), s'.2) ↔ _
  simp only [StateT.run_lift, StateT.run_bind, OptionT.run_bind, StateT.run_pure,
    OptionT.run_pure]
  rcases s' with ⟨bk', ws'⟩
  generalize (y.run s.2).run = o
  rcases o with _ | ⟨a', ws⟩
  · simp [Option.elimM, Option.elim, bind, pure]
  · simp only [Option.elimM, Option.elim, bind, pure]
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, h⟩
      cases h
      rfl

/-- A bound computation runs when its parts run in sequence. -/
theorem runs_bind {α β : Type} {x : ProveM Id α} {f : α → ProveM Id β} {s sm s' : PState} {a : α}
    {b : β} (h₁ : proveSem.Runs x s a sm) (h₂ : proveSem.Runs (f a) sm b s') :
    proveSem.Runs (x >>= f) s b s' := by
  change (((x >>= f).run s.1).run s.2).run = _
  simp only [StateT.run_bind, OptionT.run_bind]
  change (((x.run s.1).run s.2).run = some ((a, sm.1), sm.2)) at h₁
  rw [h₁]
  exact h₂

/-! ## Reading back one run -/

/-- **The reader reads back one run of the writer**: from the writer state `w` to `w'`, the
writer appended scalars `xs` and openings `ms`, and the reader `rd`, run from `w`'s chain state on
them followed by anything, returns `b`, consuming exactly them and ending in `w'`'s chain
state. -/
def Reads {β : Type} (rd : Verify.Walk Id β) (w w' : WriterState PrunedMerklePaths) (b : β) :
    Prop :=
  ∃ xs ms, w'.stream.toList = w.stream.toList ++ xs ∧ w'.merkle.toList = w.merkle.toList ++ ms ∧
    ∀ tail mtail, (rd.run ⟨w.fs, xs ++ tail, ms ++ mtail⟩).run =
      Except.ok (b, ⟨w'.fs, tail, mtail⟩)

/-- `Reads` with the book and the openings kept. -/
def Back {β : Type} (rd : Verify.Walk Id β) (s s' : PState) (b : β) : Prop :=
  s'.1 = s.1 ∧ s'.2.merkle = s.2.merkle ∧ Reads rd s.2 s'.2 b

namespace Reads

variable {β γ : Type}

/-- A pure reader reads nothing back. -/
theorem pure (w : WriterState PrunedMerklePaths) (b : β) : Reads (Pure.pure b) w w b :=
  ⟨[], [], by simp, by simp, fun _ _ ↦ rfl⟩

/-- Reading back composes along `bind`. -/
theorem bind {rd : Verify.Walk Id β} {f : β → Verify.Walk Id γ}
    {w₁ w₂ w₃ : WriterState PrunedMerklePaths} {a : β} {b : γ} (h₁ : Reads rd w₁ w₂ a)
    (h₂ : Reads (f a) w₂ w₃ b) : Reads (rd >>= f) w₁ w₃ b := by
  obtain ⟨xs, ms, hxs, hms, hrd⟩ := h₁
  obtain ⟨xs', ms', hxs', hms', hf⟩ := h₂
  refine ⟨xs ++ xs', ms ++ ms', by simp [hxs', hxs], by simp [hms', hms], fun tail mtail ↦ ?_⟩
  rw [StateT.run_bind, ExceptT.run_bind, List.append_assoc, List.append_assoc, hrd]
  exact hf tail mtail

/-- Reading back a map of a reader. -/
theorem map {rd : Verify.Walk Id β} {w w' : WriterState PrunedMerklePaths} {a : β} (g : β → γ)
    (h : Reads rd w w' a) : Reads (g <$> rd) w w' (g a) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind (pure _ _)

end Reads

namespace Back

variable {β γ : Type}

/-- A pure reader reads nothing back. -/
theorem pure (s : PState) (b : β) : Back (Pure.pure b) s s b := ⟨rfl, rfl, Reads.pure _ _⟩

/-- Reading back composes along `bind`. -/
theorem bind {rd : Verify.Walk Id β} {f : β → Verify.Walk Id γ} {s₁ s₂ s₃ : PState} {a : β}
    {b : γ} (h₁ : Back rd s₁ s₂ a) (h₂ : Back (f a) s₂ s₃ b) : Back (rd >>= f) s₁ s₃ b :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₁.2.2.bind h₂.2.2⟩

/-- Reading back a map of a reader. -/
theorem map {rd : Verify.Walk Id β} {s s' : PState} {a : β} (g : β → γ) (h : Back rd s s' a) :
    Back (g <$> rd) s s' (g a) :=
  ⟨h.1, h.2.1, h.2.2.map g⟩

/-- A reader that returns a function of what it read. -/
theorem bind_ret {rd : Verify.Walk Id β} {g : β → γ} {s s' : PState} {a : β} {b : γ}
    (h : Back rd s s' a) (hb : g a = b) : Back (rd >>= fun x ↦ Pure.pure (g x)) s s' b :=
  h.bind (hb ▸ pure _ _)

/-- A pure reader, of a value equal to the expected one. -/
theorem pure_eq {s : PState} {a b : β} (h : a = b) : Back (Pure.pure a) s s b := h ▸ pure _ _

end Back

/-! ## The primitives read back -/

section Primitives

variable (H : List UInt8 → Id Digest) (fuel : ℕ)

/-- Sending a scalar leaves the openings. -/
theorem merkle_addScalar {x : E} {w w' : WriterState PrunedMerklePaths} {u : Unit}
    (h : ((Writer.addScalar H x).run w).run = some (u, w')) : w'.merkle = w.merkle := by
  have h₀ : ((Writer.addScalar H x).run w).run = some ((), { w with
      fs := Id.run (w.fs.observe H x), stream := w.stream.push x }) := rfl
  rw [h₀] at h
  cases h
  rfl

/-- Sending scalars leaves the openings. -/
theorem merkle_addScalars : ∀ (xs : List E) {w w' : WriterState PrunedMerklePaths} {u : Unit},
    ((Writer.addScalars H xs).run w).run = some (u, w') → w'.merkle = w.merkle
  | [], w, w', u, h => by
    cases h
    rfl
  | x :: xs, w, w', u, h => by
    have h₀ : ((Writer.addScalar H x).run w).run = some ((), { w with
        fs := Id.run (w.fs.observe H x), stream := w.stream.push x }) := rfl
    change ((Writer.addScalar H x >>= fun _ ↦ Writer.addScalars H xs).run w).run = _ at h
    rw [StateT.run_bind, OptionT.run_bind, h₀] at h
    exact merkle_addScalars xs (w := { w with
      fs := Id.run (w.fs.observe H x), stream := w.stream.push x }) h

/-- Squeezing a challenge leaves the openings. -/
theorem merkle_sample {w w' : WriterState PrunedMerklePaths} {x : E}
    (h : ((Writer.sample H).run w).run = some (x, w')) : w'.merkle = w.merkle := by
  have h₀ : ((Writer.sample H).run w).run = some ((Id.run (w.fs.sample H)).1,
      { w with fs := (Id.run (w.fs.sample H)).2 }) := rfl
  rw [h₀] at h
  cases h
  rfl

/-- Grinding leaves the openings. -/
theorem merkle_grind {fuel bits : ℕ} {w w' : WriterState PrunedMerklePaths} {u : Unit}
    (h : ((Writer.grind H fuel bits).run w).run = some (u, w')) : w'.merkle = w.merkle := by
  rcases hg : Id.run (w.fs.grind H fuel bits) with _ | ⟨nonce, fs'⟩ <;>
    simp [Writer.grind, StateT.run_bind, show w.fs.grind H fuel bits = Pure.pure _ from hg] at h
  cases h
  rfl

/-- A scalar sent is read back. -/
theorem back_send {x : E} {s s' : PState} {u : Unit}
    (h : proveSem.Runs ((proveOps H fuel).send x) s u s') :
    Back (Verify.readerOps H).nextScalar s s' x := by
  obtain ⟨hb, hw⟩ := runs_lift.mp h
  have hm := merkle_addScalar H hw
  obtain ⟨xs, ms, b, h₁, h₂, rfl, h₃⟩ := readsBack_scalar H x _ _ _ hw
  exact ⟨hb, hm, xs, ms, h₁, h₂, h₃⟩

/-- A challenge squeezed is read back. -/
theorem back_sample {x : E} {s s' : PState} (h : proveSem.Runs (proveOps H fuel).sample s x s') :
    Back (Verify.readerOps H).sample s s' x := by
  obtain ⟨hb, hw⟩ := runs_lift.mp h
  have hm := merkle_sample H hw
  obtain ⟨xs, ms, b, h₁, h₂, rfl, h₃⟩ := readsBack_sample (M := PrunedMerklePaths) H _ _ _ hw
  exact ⟨hb, hm, xs, ms, h₁, h₂, h₃⟩

/-- The grinding nonce is read back, and passes the check. -/
theorem back_grind {s s' : PState} {u : Unit} (h : proveSem.Runs (proveOps H fuel).grind s u s') :
    ∃ nonce, Back ((Verify.readerOps H).checkPow queryGrindingBits) s s' nonce := by
  obtain ⟨hb, hw⟩ := runs_lift.mp h
  have hm := merkle_grind H hw
  obtain ⟨xs, ms, b, h₁, h₂, -, h₃⟩ :=
    readsBack_grind (M := PrunedMerklePaths) H fuel queryGrindingBits _ _ _ hw
  exact ⟨b, hb, hm, xs, ms, h₁, h₂, h₃⟩

/-- A commitment is kept in the book, and its root is read back. -/
theorem runs_commit {depth leafWords : ℕ} {rows : Vector (List K) (2 ^ depth)} {s s' : PState}
    {u : Unit} (h : proveSem.Runs ((proveOps H fuel).commit depth leafWords rows) s u s') :
    s'.1 = { s.1 with commits := s.1.commits.push ⟨depth, merkleCommitWith H leafWords rows⟩ } ∧
      s'.2.merkle = s.2.merkle ∧
      Reads (Verify.readerOps H).nextRoot s.2 s'.2 (merkleCommitWith H leafWords rows).root := by
  have hc : (merkleCommitWithM H leafWords rows : Id (MerkleCommitment depth)) =
      merkleCommitWith H leafWords rows :=
    merkleCommitWithM_pure (m := Id) H leafWords rows
  change ((((do
      let c ← (merkleCommitWithM H leafWords rows : Id (MerkleCommitment depth))
      modify fun b : Book ↦ { b with commits := b.commits.push ⟨depth, c⟩ }
      StateT.lift (Writer.addRoot H c.root) : ProveM Id Unit)).run s.1).run s.2).run = _ at h
  rw [hc] at h
  simp [liftM, monadLift, StateT.run_bind, StateT.run_lift] at h
  generalize ho : (StateT.run (Writer.addRoot H (Id.run (merkleCommitWith H leafWords rows)).root)
    s.2).run = o at h
  rcases s' with ⟨bk', ws'⟩
  rcases o with _ | ⟨a, ws⟩
  · cases h
  · obtain ⟨xs, ms, b, h₁, h₂, rfl, h₃⟩ := readsBack_root (M := PrunedMerklePaths) H _ _ _ _ ho
    have hm := merkle_addScalars H _ ho
    cases h
    exact ⟨rfl, hm, xs, ms, h₁, h₂, h₃⟩

/-- A level's positions are kept in the book; nothing is written. -/
theorem runs_record {ps : List ℕ} {s s' : PState} {u : Unit}
    (h : proveSem.Runs ((proveOps H fuel).record ps) s u s') :
    s'.1 = { s.1 with positions := s.1.positions.push ps } ∧ s'.2 = s.2 := by
  rcases s' with ⟨bk', ws'⟩
  change ((((modify fun b : Book ↦ { b with positions := b.positions.push ps }) :
    ProveM Id Unit).run s.1).run s.2).run = some ((u, bk'), ws') at h
  simp at h
  obtain ⟨⟨-, rfl⟩, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- Scalars sent are read back. -/
theorem back_sendAll : ∀ (l : List E) {s s' : PState} {u : Unit},
    proveSem.Runs (sendAll (proveOps H fuel) l) s u s' →
    Back ((Verify.readerOps H).nextScalars l.length) s s' l
  | [], s, s', u, h => by
    obtain ⟨-, rfl⟩ := proveSem.pure_inv h
    exact Back.pure _ _
  | x :: xs, s, s', u, h => by
    obtain ⟨_, sm, h₁, h₂⟩ := proveSem.bind_inv h
    exact (back_send H fuel h₁).bind ((back_sendAll xs h₂).bind (Back.pure _ _))

/-- Challenges squeezed are read back, as many as squeezed. -/
theorem back_samples : ∀ (k : ℕ) {s s' : PState} {xs : List E},
    proveSem.Runs (samples (proveOps H fuel) k) s xs s' →
    Back (Verify.samples (Verify.readerOps H) k) s s' xs ∧ xs.length = k
  | 0, s, s', xs, h => by
    obtain ⟨rfl, rfl⟩ := proveSem.pure_inv h
    exact ⟨Back.pure _ _, rfl⟩
  | k + 1, s, s', xs, h => by
    obtain ⟨x, sm, h₁, h₂⟩ := proveSem.bind_inv h
    obtain ⟨ys, sm₂, h₃, h₄⟩ := proveSem.bind_inv h₂
    obtain ⟨rfl, rfl⟩ := proveSem.pure_inv h₄
    obtain ⟨h₅, h₆⟩ := back_samples k h₃
    exact ⟨(back_sample H fuel h₁).bind (h₅.bind (Back.pure _ _)), by simp [h₆]⟩

/-- Positions squeezed by the verifier's function are read back by it; each lies in the tree,
and there are as many as needed when a squeeze gives one. -/
theorem back_positionsWith (depth : ℕ) : ∀ (f need : ℕ) {s s' : PState} {ps : List ℕ},
    proveSem.Runs (Verify.positionsWith (proveOps H fuel).sample depth f need) s ps s' →
    Back (Verify.positionsWith (Verify.readerOps H).sample depth f need) s s' ps ∧
      (∀ q ∈ ps, q < 2 ^ depth) ∧ (0 < 192 / depth → need ≤ f → ps.length = need)
  | 0, need, s, s', ps, h => by
    obtain ⟨rfl, rfl⟩ := proveSem.pure_inv h
    refine ⟨Back.pure _ _, by simp, fun _ hn ↦ ?_⟩
    simp only [List.length_nil]
    omega
  | f + 1, 0, s, s', ps, h => by
    obtain ⟨rfl, rfl⟩ := proveSem.pure_inv h
    exact ⟨Back.pure _ _, by simp, fun _ _ ↦ rfl⟩
  | f + 1, need + 1, s, s', ps, h => by
    obtain ⟨x, sm, h₁, h₂⟩ := proveSem.bind_inv h
    obtain ⟨rest, sm₂, h₃, h₄⟩ := proveSem.bind_inv h₂
    obtain ⟨rfl, rfl⟩ := proveSem.pure_inv h₄
    obtain ⟨h₅, h₆, h₇⟩ := back_positionsWith depth f _ h₃
    refine ⟨(back_sample H fuel h₁).bind (h₅.bind (Back.pure _ _)), fun q hq ↦ ?_, fun hd hn ↦ ?_⟩
    · rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨c, -, rfl⟩ := List.mem_map.mp hq
        exact Nat.mod_lt _ (Nat.two_pow_pos depth)
      · exact h₆ q hq
    · have hk : 1 ≤ min (192 / depth) (need + 1) := le_min hd (by omega)
      have hk' := min_le_right (192 / depth) (need + 1)
      rw [List.length_append, List.length_map, List.length_range, h₇ hd (by omega)]
      omega

/-- A level's positions are squeezed, kept in the book and read back by the walk. -/
theorem runs_positions {depth t : ℕ} {s s' : PState} {pos : Fin t → Fin (2 ^ depth)}
    (h : proveSem.Runs (positions (proveOps H fuel) depth t) s pos s') :
    ∃ ps, pos = Verify.positionsOf t depth ps ∧
      s'.1 = { s.1 with positions := s.1.positions.push ps } ∧ s'.2.merkle = s.2.merkle ∧
      Reads (Verify.walkPositions (Verify.readerOps H) depth t t) s.2 s'.2 ps ∧
      (∀ q ∈ ps, q < 2 ^ depth) ∧ (0 < 192 / depth → ps.length = t) := by
  obtain ⟨ps, sm, h₁, h₂⟩ := proveSem.bind_inv h
  obtain ⟨u, sm₂, h₃, h₄⟩ := proveSem.bind_inv h₂
  obtain ⟨rfl, rfl⟩ := proveSem.pure_inv h₄
  obtain ⟨⟨hb, hm, hr⟩, h₅, h₆⟩ := back_positionsWith H fuel depth t t h₁
  obtain ⟨hb', hw⟩ := runs_record H fuel h₃
  refine ⟨ps, rfl, by rw [hb', hb], by rw [hw, hm], ?_, h₅, fun hd ↦ h₆ hd le_rfl⟩
  rw [hw]
  exact hr

/-- A plain round polynomial of positive degree is read back as its wire. -/
theorem back_sendPlain {d : ℕ} (hd : 0 < d) (c : Vector E (d + 1)) {s s' : PState} {u : Unit}
    (h : proveSem.Runs (sendPlain (proveOps H fuel) c) s u s') :
    Back ((Verify.readerOps H).nextScalars d) s s' (polyWire 1 c) := by
  have h₁ := back_sendAll H fuel _ h
  rwa [RoundPoly.length_encode hd] at h₁

/-- A round polynomial with its equality weight factored out, of positive degree, is read back as
its wire. -/
theorem back_sendNormal {d : ℕ} (hd : 0 < d) (c : Vector E (d + 1)) {s s' : PState} {u : Unit}
    (h : proveSem.Runs (sendNormal (proveOps H fuel) c) s u s') :
    Back ((Verify.readerOps H).nextScalars d) s s' (polyWire 0 c) := by
  have h₁ := back_sendAll H fuel _ h
  rwa [RoundPoly.length_encode hd] at h₁

end Primitives

/-! ## The walk's reads regrouped -/

section Regroup

variable {n : Type → Type} [Monad n] [LawfulMonad n] (ops : Verify.ChainOps n)

/-- `k + 1` challenges are the first `k`, then the last. -/
private theorem samples_succ : ∀ k, Verify.samples ops (k + 1) = do
    let xs ← Verify.samples ops k
    let x ← ops.sample
    return xs ++ [x]
  | 0 => by simp [Verify.samples]
  | k + 1 => by
    conv_lhs => rw [Verify.samples, samples_succ k]
    conv_rhs => rw [Verify.samples]
    simp

/-- `a + b` scalars are the first `a`, then the next `b`. -/
private theorem nextScalars_add (b : ℕ) : ∀ a, ops.nextScalars (a + b) = do
    let xs ← ops.nextScalars a
    let ys ← ops.nextScalars b
    return xs ++ ys
  | 0 => by simp [Verify.ChainOps.nextScalars]
  | a + 1 => by
    rw [Nat.add_right_comm, Verify.ChainOps.nextScalars, nextScalars_add b a,
      Verify.ChainOps.nextScalars]
    simp

/-- `a + b` rounds are the first `a`, then the next `b`. -/
private theorem readRounds_add (d b : ℕ) : ∀ a, Verify.readRounds ops d (a + b) = do
    let rs₁ ← Verify.readRounds ops d a
    let rs₂ ← Verify.readRounds ops d b
    return rs₁ ++ rs₂
  | 0 => by simp [Verify.readRounds]
  | a + 1 => by
    rw [Nat.add_right_comm, Verify.readRounds, readRounds_add d b a, Verify.readRounds]
    simp

/-- `k + 1` fold rounds: the first challenge, then `k` rounds of a polynomial and a challenge,
then the last polynomial. -/
private theorem walkFolds_eq : ∀ k, Verify.walkFolds ops (k + 1) = do
    let c ← ops.sample
    let rs ← Verify.readRounds ops 2 k
    let w ← ops.nextScalars 2
    return foldsWire c rs w
  | 0 => by simp [Verify.walkFolds, Verify.readRounds, foldsWire]
  | k + 1 => by
    conv_lhs => rw [Verify.walkFolds, walkFolds_eq k]
    conv_rhs => rw [Verify.readRounds, Verify.readRound]
    simp [foldsWire]

/-- `k + 1` tail rounds: the first challenge, then `k` rounds of a polynomial and a
challenge. -/
private theorem walkTail_eq : ∀ k, Verify.walkTail ops (k + 1) = do
    let c ← ops.sample
    let rs ← Verify.readRounds ops 2 k
    return foldsWire c rs []
  | 0 => by simp [Verify.walkTail, Verify.readRounds, foldsWire]
  | k + 1 => by
    conv_lhs => rw [Verify.walkTail, walkTail_eq k]
    conv_rhs => rw [Verify.readRounds, Verify.readRound]
    simp [foldsWire]

end Regroup

/-! ## The wires of runs of challenges and rounds -/

section Runs

variable (H : List UInt8 → Id Digest) (fuel : ℕ)

/-- A run of challenges is read back as its list. -/
theorem back_chals : ∀ (k : ℕ) {t : (draws E k).FullTranscript} {s s' : PState},
    (RoundCodec.chals (proveOps H fuel).sample k).RunsAs proveSem t s s' →
    Back (Verify.samples (Verify.readerOps H) k) s s' (drawsList k t)
  | 0, t, s, s', h => by
    rw [RoundCodec.runsAs_empty h]
    exact Back.pure _ _
  | k + 1, t, s, s', h => by
    obtain ⟨sm, h₁, h₂⟩ := RoundCodec.RunsAs.append_inv proveSem h
    rw [samples_succ]
    exact (back_chals k h₁).bind
      ((back_sample H fuel (RoundCodec.runsAs_chal h₂)).bind (Back.pure _ _))

/-- A run of rounds is read back as its rounds' wires, each polynomial read back as its wire. -/
theorem back_rounds {d : ℕ} (drop : ℕ) {enc : Vector E (d + 1) → ProveM Id Unit}
    (henc : ∀ (c : Vector E (d + 1)) {s s' : PState} {u : Unit}, proveSem.Runs (enc c) s u s' →
      Back ((Verify.readerOps H).nextScalars d) s s' (polyWire drop c)) :
    ∀ (m : ℕ) {t : (roundsSpec E d m).FullTranscript} {s s' : PState},
      (RoundCodec.rounds enc (proveOps H fuel).sample m).RunsAs proveSem t s s' →
      Back (Verify.readRounds (Verify.readerOps H) d m) s s' (roundsWire drop m t)
  | 0, t, s, s', h => by
    rw [RoundCodec.runsAs_empty h]
    exact Back.pure _ _
  | m + 1, t, s, s', h => by
    obtain ⟨sm, h₁, h₂⟩ := RoundCodec.RunsAs.append_inv proveSem h
    obtain ⟨sm₁, h₃, h₄⟩ := RoundCodec.RunsAs.append_inv proveSem h₁
    exact ((henc _ (RoundCodec.runsAs_msg h₃)).bind
      ((back_sample H fuel (RoundCodec.runsAs_chal h₄)).bind_ret rfl)).bind
      ((back_rounds drop henc m h₂).bind_ret rfl)

/-- Scalars sent in two parts are sent one part after the other. -/
theorem runs_sendAll_append (l₁ l₂ : List E) {s s' : PState} {u : Unit}
    (h : proveSem.Runs (sendAll (proveOps H fuel) (l₁ ++ l₂)) s u s') :
    ∃ sm, proveSem.Runs (sendAll (proveOps H fuel) l₁) s () sm ∧
      proveSem.Runs (sendAll (proveOps H fuel) l₂) sm () s' := by
  induction l₁ generalizing s with
  | nil => exact ⟨s, rfl, h⟩
  | cons x xs ih =>
    obtain ⟨_, sm, h₁, h₂⟩ := proveSem.bind_inv h
    obtain ⟨sm', h₃, h₄⟩ := ih h₂
    exact ⟨sm', runs_bind h₁ h₃, h₄⟩

end Runs

/-! ## The front phases -/

section Front

variable (H : List UInt8 → Id Digest) (fuel : ℕ)

/-- **The table sumcheck read back**: `ξ`, the rounds' wires and the columns' values. -/
theorem back_table (I : M3Instance) {t : (tableSpec I).FullTranscript} {s s' : PState}
    (h : (tableCodec (proveOps H fuel) I).RunsAs proveSem t s s') :
    Back (Verify.walkTables (Verify.readerOps H) I.τmax I.tableColumns) s s'
      (tableWireOf I t) := by
  obtain ⟨s₂, h₂, h₃⟩ := RoundCodec.RunsAs.append_inv proveSem h
  obtain ⟨s₁, h₀, h₁⟩ := RoundCodec.RunsAs.append_inv proveSem h₂
  have hv := RoundCodec.runsAs_msg h₃
  replace hv := back_sendAll H fuel _ hv
  rw [Vector.length_toList] at hv
  exact (back_sample H fuel (RoundCodec.runsAs_chal h₀)).bind
    ((back_rounds H fuel 1 (fun c _ _ _ hc ↦ back_sendPlain H fuel (by norm_num) c hc) I.τmax
      h₁).bind (hv.bind_ret rfl))

/-- **The public input read back**: `r` and the values sent, one per sent line. -/
theorem back_pub {nSent : ℕ} {t : pubSpec.FullTranscript} {s s' : PState}
    (h : (pubCodec (proveOps H fuel)).RunsAs proveSem t s s') (hn : (t 1).length = nSent) :
    Back (Verify.walkPub (Verify.readerOps H) nSent) s s' (pubWireOf t) := by
  obtain ⟨st, h0, hl, hs⟩ := h
  have h₁ : proveSem.Runs (proveOps H fuel).sample (st 0) (t 0) (st 1) := (hs 0).2 rfl
  have h₂ : proveSem.Runs (sendAll (proveOps H fuel) (t 1)) (st 1) () (st 2) := (hs 1).1 rfl
  subst h0 hl hn
  exact (back_sample H fuel h₁).bind ((back_sendAll H fuel _ h₂).bind_ret rfl)

/-- **The Flock phase read back**, for `2 ^ k` compressions. -/
theorem back_flock (k : ℕ) {t : (flockSpecOf k).FullTranscript} {s s' : PState}
    (h : (flockCodecOf (proveOps H fuel) k).RunsAs proveSem t s s') :
    Back (Verify.walkFlock (Verify.readerOps H) k) s s' (flockWireOf k t) := by
  obtain ⟨s₉, h₉, hr⟩ := RoundCodec.RunsAs.append_inv proveSem h
  obtain ⟨s₈, h₈, hsl⟩ := RoundCodec.RunsAs.append_inv proveSem h₉
  obtain ⟨s₇, h₇, hlin⟩ := RoundCodec.RunsAs.append_inv proveSem h₈
  obtain ⟨s₆, h₆, hal⟩ := RoundCodec.RunsAs.append_inv proveSem h₇
  obtain ⟨s₅, h₅, hab⟩ := RoundCodec.RunsAs.append_inv proveSem h₆
  obtain ⟨s₄, h₄, hzk⟩ := RoundCodec.RunsAs.append_inv proveSem h₅
  obtain ⟨s₃, h₃, hz8⟩ := RoundCodec.RunsAs.append_inv proveSem h₄
  obtain ⟨s₂, h₂, hzs⟩ := RoundCodec.RunsAs.append_inv proveSem h₃
  obtain ⟨s₁, hpt, hsk⟩ := RoundCodec.RunsAs.append_inv proveSem h₂
  have hskip := RoundCodec.runsAs_msg hsk
  have hab' := RoundCodec.runsAs_msg hab
  have hsl' := RoundCodec.runsAs_msg hsl
  replace hskip := back_sendAll H fuel _ hskip
  replace hab' := back_sendAll H fuel _ hab'
  replace hsl' := back_sendAll H fuel _ hsl'
  rw [Vector.length_toList] at hskip hab' hsl'
  have hn : ∀ (m : ℕ) {t' : (roundsSpec E 2 m).FullTranscript} {a b : PState},
      (RoundCodec.rounds (sendNormal (proveOps H fuel)) (proveOps H fuel).sample m).RunsAs
        proveSem t' a b →
      Back (Verify.readRounds (Verify.readerOps H) 2 m) a b (roundsWire 0 m t') :=
    back_rounds H fuel 0 (fun c _ _ _ hc ↦ back_sendNormal H fuel (by norm_num) c hc)
  simp only [Verify.walkFlock, readRounds_add]
  exact (back_chals H fuel (k + 1) hpt).bind (hskip.bind
    ((back_sample H fuel (RoundCodec.runsAs_chal hzs)).bind (((hn 8 hz8).bind
      ((hn k hzk).bind_ret rfl)).bind (hab'.bind
    ((back_sample H fuel (RoundCodec.runsAs_chal hal)).bind
    ((back_rounds H fuel 1 (fun c _ _ _ hc ↦ back_sendPlain H fuel (by norm_num) c hc) 8
      hlin).bind (hsl'.bind ((back_chals H fuel 6 hr).bind_ret rfl))))))))

end Front

/-! ## The bus phase -/

section Layers

variable {n : Type → Type} [Monad n] [LawfulMonad n] (ops : Verify.ChainOps n)

/-- The three trees' descendants of a layer of radix `2 ^ ρ`. -/
private def children3 (ρ : ℕ) : n (List (List E)) := do
  let c₀ ← ops.nextScalars (2 ^ ρ)
  let c₁ ← ops.nextScalars (2 ^ ρ)
  let c₂ ← ops.nextScalars (2 ^ ρ)
  return [c₀, c₁, c₂]

/-- A layer's reads before the next combiner: its rounds, the trees' descendants and the
combination challenges. -/
private def layerBody (ρ j : ℕ) : n (List Verify.Round × List (List E) × List E) := do
  let rounds ← Verify.readRounds ops (2 ^ ρ) j
  let cs ← children3 ops ρ
  let combos ← Verify.samples ops ρ
  return (rounds, cs, combos)

/-- A combiner, then the layers of the given radix exponents from depth `j`. -/
private def combLayers (ρs : List ℕ) (j : ℕ) : n (E × List Verify.GkrLayer) := do
  let c ← ops.sample
  let ls ← Verify.walkLayers ops ρs j
  return (c, ls)

private theorem combLayers_nil (j : ℕ) :
    combLayers ops [] j = do
      let c ← ops.sample
      return (c, []) := by
  simp [combLayers, Verify.walkLayers]

private theorem combLayers_cons (ρ : ℕ) (rest : List ℕ) (j : ℕ) :
    combLayers ops (ρ :: rest) j = do
      let c ← ops.sample
      let b ← layerBody ops ρ j
      let p ← combLayers ops rest (j + ρ)
      return (c, ⟨b.1, b.2.1, b.2.2, p.1⟩ :: p.2) := by
  simp [combLayers, layerBody, children3, Verify.walkLayers, Verify.walkLayer]

end Layers

section Bus

variable (H : List UInt8 → Id Digest) (fuel : ℕ)

/-- The three trees' descendants are read back. -/
private theorem back_children (ρ : ℕ) (c : Fin 3 → Vector E (2 ^ ρ)) {s s' : PState} {u : Unit}
    (h : proveSem.Runs (sendTables (proveOps H fuel) c) s u s') :
    Back (children3 (Verify.readerOps H) ρ) s s' (List.ofFn fun i ↦ (c i).toList) := by
  have hl : (List.finRange 3).flatMap (fun t ↦ (c t).toList) =
      (c 0).toList ++ ((c 1).toList ++ (c 2).toList) := by
    simp [List.finRange_succ]
  change proveSem.Runs (sendAll _ ((List.finRange 3).flatMap fun t ↦ (c t).toList)) s u s' at h
  rw [hl] at h
  obtain ⟨sm, h₁, h₂⟩ := runs_sendAll_append H fuel _ _ h
  obtain ⟨sm', h₃, h₄⟩ := runs_sendAll_append H fuel _ _ h₂
  have b₁ := back_sendAll H fuel _ h₁
  have b₂ := back_sendAll H fuel _ h₃
  have b₃ := back_sendAll H fuel _ h₄
  rw [Vector.length_toList] at b₁ b₂ b₃
  exact b₁.bind (b₂.bind (b₃.bind_ret (by simp [List.ofFn_succ])))

/-- A layer of the grand product read back: its combiner, then its body. -/
private theorem back_step (ρ m : ℕ) {t : (stepSpec E 3 ρ m).FullTranscript} {s s' : PState}
    (h : (RoundCodec.step ρ m (sendNormal (proveOps H fuel)) (sendTables (proveOps H fuel))
      (proveOps H fuel).sample).RunsAs proveSem t s s') :
    ∃ s₁, Back (Verify.readerOps H).sample s s₁ (layerCombiner t) ∧
      Back (layerBody (Verify.readerOps H) ρ m) s₁ s'
        (roundsWire 0 m t.fst.fst.snd, List.ofFn fun i ↦ (msgOf t.fst.snd i).toList,
          drawsList ρ t.snd) := by
  obtain ⟨s₃, h₃, hc⟩ := RoundCodec.RunsAs.append_inv proveSem h
  obtain ⟨s₂, h₂, hch⟩ := RoundCodec.RunsAs.append_inv proveSem h₃
  obtain ⟨s₁, h₁, hr⟩ := RoundCodec.RunsAs.append_inv proveSem h₂
  refine ⟨s₁, back_sample H fuel (RoundCodec.runsAs_chal h₁), ?_⟩
  have hk := RoundCodec.runsAs_msg hch
  exact (back_rounds H fuel 0 (fun c _ _ _ hc' ↦ back_sendNormal H fuel (Nat.two_pow_pos ρ) c hc')
    m hr).bind ((back_children H fuel ρ _ hk).bind ((back_chals H fuel ρ hc).bind_ret rfl))

/-- Layers of radix four read back, a combiner before them and the last after them. -/
private theorem back_steps : ∀ (k m : ℕ) {t : (stepsSpec E 3 k m).FullTranscript}
    {s sm s' : PState} {last : E},
    (RoundCodec.steps (sendNormal (proveOps H fuel)) (sendTables (proveOps H fuel))
      (proveOps H fuel).sample k m).RunsAs proveSem t s sm →
    Back (Verify.readerOps H).sample sm s' last →
    Back (combLayers (Verify.readerOps H) (List.replicate k 2) m) s s' (stepsWire k m t last)
  | 0, m, t, s, sm, s', last, h, hl => by
    rw [RoundCodec.runsAs_empty h] at hl
    rw [List.replicate_zero, combLayers_nil]
    exact hl.bind_ret rfl
  | k + 1, m, t, s, sm, s', last, h, hl => by
    obtain ⟨s₂, h₁, h₂⟩ := RoundCodec.RunsAs.append_inv proveSem h
    obtain ⟨s₁, hc, hb⟩ := back_step H fuel 2 m h₁
    rw [List.replicate_succ, combLayers_cons]
    exact hc.bind (hb.bind ((back_steps k (m + 2) h₂ hl).bind_ret rfl))

/-- The grand product read back from its odd part's parity `r`. -/
private theorem back_gkrAux : ∀ (r k : ℕ), r < 2 →
    ∀ {t : (oddSpec E 3 r ++ₚ stepsSpec E 3 k r ++ₚ Protocol.draw E).FullTranscript}
      {s s' : PState},
    (((RoundCodec.odd (sendNormal (proveOps H fuel)) (sendTables (proveOps H fuel))
      (proveOps H fuel).sample r).append (RoundCodec.steps (sendNormal (proveOps H fuel))
        (sendTables (proveOps H fuel)) (proveOps H fuel).sample k r)).append
        (RoundCodec.chal (proveOps H fuel).sample)).RunsAs proveSem t s s' →
    Back (combLayers (Verify.readerOps H) ((if r = 1 then [1] else []) ++ List.replicate k 2) 0)
      s s' (oddWire r t.fst.fst (stepsWire k r t.fst.snd (drawOf t.snd)))
  | 0, k, _, t, s, s', h => by
    obtain ⟨s₂, h₁, hl⟩ := RoundCodec.RunsAs.append_inv proveSem h
    obtain ⟨s₁, ho, hs⟩ := RoundCodec.RunsAs.append_inv proveSem h₁
    rw [RoundCodec.runsAs_empty ho] at hs
    exact back_steps H fuel k 0 hs (back_sample H fuel (RoundCodec.runsAs_chal hl))
  | 1, k, _, t, s, s', h => by
    obtain ⟨s₂, h₁, hl⟩ := RoundCodec.RunsAs.append_inv proveSem h
    obtain ⟨s₁, ho, hs⟩ := RoundCodec.RunsAs.append_inv proveSem h₁
    obtain ⟨s₀, hc, hb⟩ := back_step H fuel 1 0 ho
    rw [ite_eq_left rfl, List.singleton_append, combLayers_cons]
    exact hc.bind (hb.bind ((back_steps H fuel k 1 hs
      (back_sample H fuel (RoundCodec.runsAs_chal hl))).bind_ret rfl))

/-- **The grand product read back**: the combiner after the roots, then the layers. -/
theorem back_gkr (μ : ℕ) {t : (gkrSpec E 3 μ).FullTranscript} {s s' : PState}
    (h : (RoundCodec.gkr μ (sendNormal (proveOps H fuel)) (sendTables (proveOps H fuel))
      (sendNormal (proveOps H fuel)) (sendTables (proveOps H fuel))
      (proveOps H fuel).sample).RunsAs proveSem t s s') :
    Back (do
        let c ← (Verify.readerOps H).sample
        let ls ← Verify.walkLayers (Verify.readerOps H) (Verify.gkrRadices μ) 0
        return (c, ls)) s s' (gkrWire μ t) :=
  back_gkrAux H fuel (μ % 2) (μ / 2) (Nat.mod_lt _ (by norm_num)) h

/-- Four challenges read as a function, by position, are the four. -/
private theorem ofFn_getD : ∀ {l : List E}, l.length = 4 →
    List.ofFn (fun i : Fin 4 ↦ l.getD i 0) = l
  | [_, _, _, _], _ => by simp [List.ofFn_succ]

/-- **The bus phase read back**: `α`, `β`, the roots, the grand product's combiner and layers,
and the boundary values. -/
theorem back_bus (I : M3Instance) {t : (busSpec I).FullTranscript} {s s' : PState}
    (h : (busCodec (proveOps H fuel) I).RunsAs proveSem t s s') :
    Back (Verify.walkBus (Verify.readerOps H) I.μBus I.busClaims) s s' (busWireOf I t) := by
  obtain ⟨s₃, h₃, hv⟩ := RoundCodec.RunsAs.append_inv proveSem h
  obtain ⟨s₂, h₂, hg⟩ := RoundCodec.RunsAs.append_inv proveSem h₃
  obtain ⟨s₁, h₀, hr⟩ := RoundCodec.RunsAs.append_inv proveSem h₂
  have hc := RoundCodec.runsAs_chal h₀
  obtain ⟨a, sa, ha, hc₂⟩ := proveSem.bind_inv hc
  obtain ⟨b, sb, hb, hc₃⟩ := proveSem.bind_inv hc₂
  obtain ⟨hfp, rfl⟩ := proveSem.pure_inv hc₃
  obtain ⟨ba, hlen⟩ := back_samples H fuel 4 ha
  have hr' := RoundCodec.runsAs_msg hr
  obtain ⟨u, sm, hr₁, hr₂⟩ := proveSem.bind_inv hr'
  have hv' := RoundCodec.runsAs_msg hv
  replace hv' := back_sendAll H fuel _ hv'
  rw [Vector.length_toList] at hv'
  have hw : Verify.walkBus (Verify.readerOps H) I.μBus I.busClaims = do
      let alpha ← Verify.samples (Verify.readerOps H) 4
      let beta ← (Verify.readerOps H).sample
      let shared ← (Verify.readerOps H).nextScalar
      let count ← (Verify.readerOps H).nextScalar
      let p ← (do
        let c ← (Verify.readerOps H).sample
        let ls ← Verify.walkLayers (Verify.readerOps H) (Verify.gkrRadices I.μBus) 0
        return (c, ls))
      let values ← (Verify.readerOps H).nextScalars I.busClaims
      return ⟨alpha, beta, shared, count, p.1, p.2, values⟩ := by
    simp [Verify.walkBus]
  rw [hw]
  refine ba.bind ((back_sample H fuel hb).bind ((back_send H fuel hr₁).bind
    ((back_send H fuel hr₂).bind ((back_gkr H fuel I.μBus hg).bind (hv'.bind_ret ?_)))))
  simp only [busWireOf, hfp, ofFn_getD hlen]

end Bus

/-! ## WHIR's levels -/

section Whir

/-- Raw positions standing for a level's query positions: each in the word, as many as queried,
and reducing to them. -/
def PosRead {t b : ℕ} (ps : List ℕ) (pos : Fin t → Fin (2 ^ b)) : Prop :=
  (∀ q ∈ ps, q < 2 ^ b) ∧ ps.length = t ∧ Verify.positionsOf t b ps = pos

/-- The positions of a level with a successor, on its transcript. -/
abbrev levelPositions {sh sh' : Whir.Shape} {κ' : ℕ} {k : List Step}
    (t : (seqSpec (levelSteps sh sh' κ' k)).FullTranscript) :
    Fin sh.t → Fin (2 ^ (Kap sh' κ' + sh.R)) :=
  drawOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
    t)))))))))

/-- The word a level with a successor sends, on its transcript. -/
abbrev levelWord {sh sh' : Whir.Shape} {κ' : ℕ} {k : List Step}
    (t : (seqSpec (levelSteps sh sh' κ' k)).FullTranscript) : WordOf sh' κ' :=
  msgOf (seqHead (seqTail (seqTail (seqTail t))))

/-- The positions of the final level, on its transcript. -/
abbrev finalPositions {sh : Whir.Shape} {nf : ℕ} (t : (seqSpec (finalSteps sh nf)).FullTranscript) :
    Fin sh.t → Fin (2 ^ (nf + 1 + sh.R)) :=
  drawOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail t))))))

/-- The positions reduced from a transcript's positions are them. -/
theorem positionsOf_positionsList {t b : ℕ} (pos : Fin t → Fin (2 ^ b)) :
    Verify.positionsOf t b (positionsList pos) = pos := by
  funext q
  apply Fin.ext
  simp [Verify.positionsOf, positionsList, Nat.mod_eq_of_lt (pos q).isLt]

/-- Reducing a transcript's positions leaves them. -/
theorem reducePositions_positionsList {t b : ℕ} (pos : Fin t → Fin (2 ^ b)) :
    Verify.reducePositions t b (positionsList pos) = positionsList pos := by
  rw [Verify.reducePositions, positionsOf_positionsList]
  rfl

/-- Raw positions standing for a transcript's reduce as the transcript's do. -/
theorem reducePositions_of_posRead {t b : ℕ} {ps : List ℕ} {pos : Fin t → Fin (2 ^ b)}
    (h : PosRead ps pos) :
    Verify.reducePositions t b ps = Verify.reducePositions t b (positionsList pos) := by
  simp only [Verify.reducePositions, positionsOf_positionsList, h.2.2]

/-- Reading back extends the stream. -/
theorem Reads.stream {β : Type} {rd : Verify.Walk Id β} {w w' : WriterState PrunedMerklePaths}
    {b : β} (h : Reads rd w w' b) : ∃ xs, w'.stream.toList = w.stream.toList ++ xs :=
  let ⟨xs, _, h₁, _⟩ := h
  ⟨xs, h₁⟩

theorem Reads.bind_ret {β γ : Type} {rd : Verify.Walk Id β} {g : β → γ}
    {w w' : WriterState PrunedMerklePaths} {a : β} {b : γ} (h : Reads rd w w' a) (hb : g a = b) :
    Reads (rd >>= fun x ↦ Pure.pure (g x)) w w' b :=
  h.bind (hb ▸ Reads.pure _ _)

variable (H : List UInt8 → Id Digest) (fuel : ℕ)

/-- **A level with a successor read back**: the walk's level, equal to the transcript's but for
what the algebra does not read; the next word's commitment and the level's positions kept in the
book; the positions standing for the transcript's; the root the walk reads the commitment's; and
the rest of the opening run on the rest of the transcript. -/
theorem back_level (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    {rest : RoundCodec (ProveM Id) (seqSpec k)}
    (hd : 0 < 192 / (Kap sh' κ' + sh.R))
    {t : (seqSpec (levelSteps sh sh' κ' k)).FullTranscript} {s s' : PState}
    (h : (levelCodec (proveOps H fuel) sh sh' κ' rest).RunsAs proveSem t s s') :
    ∃ sm l, Reads (Verify.walkLevel (Verify.readerOps H) ⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, false⟩)
        s.2 sm.2 l ∧
      l.erase ⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, false⟩ =
        (levelWire t).1.erase ⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, false⟩ ∧
      sm.1 = ⟨s.1.commits.push
          ⟨κ' + sh'.R, merkleCommitWith H (3 * 2 ^ sh'.ℓ) (laterRows (levelWord t))⟩,
        s.1.positions.push l.positions⟩ ∧ sm.2.merkle = s.2.merkle ∧
      PosRead l.positions (levelPositions t) ∧
      l.root = some (merkleCommitWith H (3 * 2 ^ sh'.ℓ) (laterRows (levelWord t))).root ∧
      rest.RunsAs proveSem (levelWire t).2 sm s' := by
  obtain ⟨σ₁, h₁, t₁⟩ := RoundCodec.RunsAs.append_inv proveSem h
  obtain ⟨σ₂, h₂, t₂⟩ := RoundCodec.RunsAs.append_inv proveSem t₁
  obtain ⟨σ₃, h₃, t₃⟩ := RoundCodec.RunsAs.append_inv proveSem t₂
  obtain ⟨σ₄, h₄, t₄⟩ := RoundCodec.RunsAs.append_inv proveSem t₃
  obtain ⟨σ₅, h₅, t₅⟩ := RoundCodec.RunsAs.append_inv proveSem t₄
  obtain ⟨σ₆, h₆, t₆⟩ := RoundCodec.RunsAs.append_inv proveSem t₅
  obtain ⟨σ₇, h₇, t₇⟩ := RoundCodec.RunsAs.append_inv proveSem t₆
  obtain ⟨σ₈, h₈, t₈⟩ := RoundCodec.RunsAs.append_inv proveSem t₇
  obtain ⟨σ₉, h₉, t₉⟩ := RoundCodec.RunsAs.append_inv proveSem t₈
  obtain ⟨σ₁₀, h₁₀, t₁₀⟩ := RoundCodec.RunsAs.append_inv proveSem t₉
  obtain ⟨σ₁₁, h₁₁, t₁₁⟩ := RoundCodec.RunsAs.append_inv proveSem t₁₀
  obtain ⟨σ₁₂, h₁₂, t₁₂⟩ := RoundCodec.RunsAs.append_inv proveSem t₁₁
  obtain ⟨σ₁₃, h₁₃, t₁₃⟩ := RoundCodec.RunsAs.append_inv proveSem t₁₂
  have b₁ := back_sample H fuel (RoundCodec.runsAs_chal h₁)
  have b₂ := back_rounds H fuel 1 (fun c _ _ _ hc ↦ back_sendPlain H fuel (by norm_num) c hc)
    sh.lm1 h₂
  have b₃ := back_sendPlain H fuel (by norm_num) _ (RoundCodec.runsAs_msg h₃)
  have r₄ : proveSem.Runs ((proveOps H fuel).commit (κ' + sh'.R) (3 * 2 ^ sh'.ℓ)
      (laterRows (levelWord t))) σ₃ () σ₄ := RoundCodec.runsAs_msg h₄
  obtain ⟨hk₄, hm₄, b₄⟩ := runs_commit H fuel r₄
  have b₅ := back_chals H fuel _ h₅
  have b₆ := back_send H fuel (RoundCodec.runsAs_msg h₆)
  have b₇ := back_sendPlain H fuel (by norm_num) _ (RoundCodec.runsAs_msg h₇)
  obtain ⟨nonce, b₈⟩ := back_grind H fuel (RoundCodec.runsAs_msg h₈)
  obtain ⟨ps, hpos, hk₉, hm₉, b₉, hlt, hlen⟩ := runs_positions H fuel (RoundCodec.runsAs_chal h₉)
  have b₁₀ := back_sample H fuel (RoundCodec.runsAs_chal h₁₀)
  have e₁₁ := RoundCodec.runsAs_empty h₁₁
  have b₁₂ := back_sendPlain H fuel (by norm_num) _ (RoundCodec.runsAs_msg h₁₂)
  have e₁₃ := RoundCodec.runsAs_empty h₁₃
  subst e₁₁ e₁₃
  have hw : Verify.walkLevel (Verify.readerOps H) ⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, false⟩ = do
      let c ← (Verify.readerOps H).sample
      let rs ← Verify.readRounds (Verify.readerOps H) 2 sh.lm1
      let w ← (Verify.readerOps H).nextScalars 2
      let root ← (Verify.readerOps H).nextRoot
      let ood ← Verify.samples (Verify.readerOps H) (Kap sh' κ')
      let oodValue ← (Verify.readerOps H).nextScalar
      let oodWire ← (Verify.readerOps H).nextScalars 2
      let nonce ← (Verify.readerOps H).checkPow Whir.queryGrindingBits
      let positions ← Verify.walkPositions (Verify.readerOps H) (Kap sh' κ' + sh.R) sh.t sh.t
      let lam ← (Verify.readerOps H).sample
      let queryWire ← (Verify.readerOps H).nextScalars 2
      return ⟨foldsWire c rs w, some root, ood, oodValue, oodWire, [], nonce, positions, lam,
        queryWire, []⟩ := by
    simp [Verify.walkLevel, Whir.Shape.ℓ, walkFolds_eq]
  refine ⟨σ₁₃, ⟨foldsWire (drawOf (seqHead t)) (roundsWire 1 sh.lm1 (seqHead (seqTail t)))
      (polyWire 1 (msgOf (seqHead (seqTail (seqTail t))))),
    some (merkleCommitWith H (3 * 2 ^ sh'.ℓ) (laterRows (levelWord t))).root,
    drawsList (Kap sh' κ') (seqHead (seqTail (seqTail (seqTail (seqTail t))))),
    msgOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail t)))))),
    polyWire 1 (msgOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail t)))))))),
    [], nonce, ps,
    drawOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
      (seqTail t)))))))))),
    polyWire 1 (msgOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
      (seqTail (seqTail (seqTail (seqTail t))))))))))))), []⟩,
    ?_, ?_, ?_, ?_, ⟨hlt, hlen hd, hpos.symm⟩, rfl, t₁₃⟩
  · rw [hw]
    exact b₁.2.2.bind (b₂.2.2.bind (b₃.2.2.bind (b₄.bind (b₅.2.2.bind (b₆.2.2.bind
      (b₇.2.2.bind (b₈.2.2.bind (b₉.bind (b₁₀.2.2.bind (b₁₂.2.2.bind_ret rfl))))))))))
  · simp only [Verify.WhirLevel.erase, levelWire,
      reducePositions_of_posRead (show PosRead ps (levelPositions t) from
        ⟨hlt, hlen hd, hpos.symm⟩)]
  · rw [b₁₂.1, b₁₀.1, hk₉, b₈.1, b₇.1, b₆.1, b₅.1, hk₄, b₃.1, b₂.1, b₁.1]
  · rw [b₁₂.2.1, b₁₀.2.1, hm₉, b₈.2.1, b₇.2.1, b₆.2.1, b₅.2.1, hm₄, b₃.2.1, b₂.2.1, b₁.2.1]

/-- **The final level read back**: the walk's level, equal to the transcript's but for what the
algebra does not read; the level's positions kept in the book and standing for the transcript's. -/
theorem back_final (sh : Whir.Shape) (nf : ℕ) (hd : 0 < 192 / (nf + 1 + sh.R))
    {t : (seqSpec (finalSteps sh nf)).FullTranscript} {s s' : PState}
    (h : (finalCodec (proveOps H fuel) sh nf).RunsAs proveSem t s s') :
    ∃ l, Reads (Verify.walkLevel (Verify.readerOps H) ⟨sh.ℓ, nf + 1, sh.R, sh.t, true⟩)
        s.2 s'.2 l ∧
      l.erase ⟨sh.ℓ, nf + 1, sh.R, sh.t, true⟩ =
        (finalWire t).erase ⟨sh.ℓ, nf + 1, sh.R, sh.t, true⟩ ∧
      s'.1 = ⟨s.1.commits, s.1.positions.push l.positions⟩ ∧ s'.2.merkle = s.2.merkle ∧
      PosRead l.positions (finalPositions t) := by
  obtain ⟨σ₁, h₁, t₁⟩ := RoundCodec.RunsAs.append_inv proveSem h
  obtain ⟨σ₂, h₂, t₂⟩ := RoundCodec.RunsAs.append_inv proveSem t₁
  obtain ⟨σ₃, h₃, t₃⟩ := RoundCodec.RunsAs.append_inv proveSem t₂
  obtain ⟨σ₄, h₄, t₄⟩ := RoundCodec.RunsAs.append_inv proveSem t₃
  obtain ⟨σ₅, h₅, t₅⟩ := RoundCodec.RunsAs.append_inv proveSem t₄
  obtain ⟨σ₆, h₆, t₆⟩ := RoundCodec.RunsAs.append_inv proveSem t₅
  obtain ⟨σ₇, h₇, t₇⟩ := RoundCodec.RunsAs.append_inv proveSem t₆
  obtain ⟨σ₈, h₈, t₈⟩ := RoundCodec.RunsAs.append_inv proveSem t₇
  obtain ⟨σ₉, h₉, t₉⟩ := RoundCodec.RunsAs.append_inv proveSem t₈
  obtain ⟨σ₁₀, h₁₀, t₁₀⟩ := RoundCodec.RunsAs.append_inv proveSem t₉
  obtain ⟨σ₁₁, h₁₁, t₁₁⟩ := RoundCodec.RunsAs.append_inv proveSem t₁₀
  obtain ⟨σ₁₂, h₁₂, t₁₂⟩ := RoundCodec.RunsAs.append_inv proveSem t₁₁
  have b₁ := back_sample H fuel (RoundCodec.runsAs_chal h₁)
  have b₂ := back_rounds H fuel 1 (fun c _ _ _ hc ↦ back_sendPlain H fuel (by norm_num) c hc)
    sh.lm1 h₂
  have b₃ := back_sendPlain H fuel (by norm_num) _ (RoundCodec.runsAs_msg h₃)
  have r₄ := RoundCodec.runsAs_msg h₄
  replace r₄ := back_sendAll H fuel _ r₄
  rw [Vector.length_toList] at r₄
  obtain ⟨nonce, b₅⟩ := back_grind H fuel (RoundCodec.runsAs_msg h₅)
  obtain ⟨ps, hpos, hk₆, hm₆, b₆, hlt, hlen⟩ := runs_positions H fuel (RoundCodec.runsAs_chal h₆)
  have b₇ := back_sample H fuel (RoundCodec.runsAs_chal h₇)
  have e₈ := RoundCodec.runsAs_empty h₈
  have b₉ := back_sendPlain H fuel (by norm_num) _ (RoundCodec.runsAs_msg h₉)
  have e₁₀ := RoundCodec.runsAs_empty h₁₀
  have b₁₁ := back_sample H fuel (RoundCodec.runsAs_chal h₁₁)
  have b₁₂ := back_rounds H fuel 1 (fun c _ _ _ hc ↦ back_sendPlain H fuel (by norm_num) c hc)
    nf h₁₂
  have e₁₃ := RoundCodec.runsAs_empty t₁₂
  subst e₈ e₁₀ e₁₃
  have hw : Verify.walkLevel (Verify.readerOps H) ⟨sh.ℓ, nf + 1, sh.R, sh.t, true⟩ = do
      let c ← (Verify.readerOps H).sample
      let rs ← Verify.readRounds (Verify.readerOps H) 2 sh.lm1
      let w ← (Verify.readerOps H).nextScalars 2
      let residual ← (Verify.readerOps H).nextScalars (2 ^ (nf + 1))
      let nonce ← (Verify.readerOps H).checkPow Whir.queryGrindingBits
      let positions ← Verify.walkPositions (Verify.readerOps H) (nf + 1 + sh.R) sh.t sh.t
      let lam ← (Verify.readerOps H).sample
      let queryWire ← (Verify.readerOps H).nextScalars 2
      let c' ← (Verify.readerOps H).sample
      let rs' ← Verify.readRounds (Verify.readerOps H) 2 nf
      return ⟨foldsWire c rs w, none, [], 0, [], residual, nonce, positions, lam, queryWire,
        foldsWire c' rs' []⟩ := by
    simp [Verify.walkLevel, Whir.Shape.ℓ, walkFolds_eq, walkTail_eq]
  refine ⟨⟨foldsWire (drawOf (seqHead t)) (roundsWire 1 sh.lm1 (seqHead (seqTail t)))
      (polyWire 1 (msgOf (seqHead (seqTail (seqTail t))))), none, [], 0, [],
    Vector.toList (msgOf (seqHead (seqTail (seqTail (seqTail t)))) : Vector E (2 ^ (nf + 1))),
    nonce, ps,
    drawOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail t))))))),
    polyWire 1 (msgOf (seqHead
      (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail t)))))))))),
    foldsWire (drawOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
      (seqTail (seqTail (seqTail t)))))))))))) (roundsWire 1 nf (seqHead (seqTail (seqTail
      (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
      t))))))))))))) []⟩, ?_, ?_, ?_, ?_, ⟨hlt, hlen hd, hpos.symm⟩⟩
  · rw [hw]
    exact b₁.2.2.bind (b₂.2.2.bind (b₃.2.2.bind (r₄.2.2.bind (b₅.2.2.bind (b₆.bind
      (b₇.2.2.bind (b₉.2.2.bind (b₁₁.2.2.bind (b₁₂.2.2.bind_ret rfl)))))))))
  · simp only [Verify.WhirLevel.erase, finalWire,
      reducePositions_of_posRead (show PosRead ps (finalPositions t) from
        ⟨hlt, hlen hd, hpos.symm⟩)]
  · rw [b₁₂.1, b₁₁.1, b₉.1, b₇.1, hk₆, b₅.1, r₄.1, b₃.1, b₂.1, b₁.1]
  · rw [b₁₂.2.1, b₁₁.2.1, b₉.2.1, b₇.2.1, hm₆, b₅.2.1, r₄.2.1, b₃.2.1, b₂.2.1, b₁.2.1]

/-- What the prover's run of a chain of levels leaves for the openings, level by level: the walk's
level; on a level with a successor, the commitment to the next word it keeps, whose root the walk
reads; the level's raw positions, kept, standing for the transcript's. -/
def LadderRead (H : List UInt8 → Id Digest) : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) →
    (seqSpec L.steps).FullTranscript → List Verify.WhirLevel →
    List (Σ k, MerkleCommitment k) → List (List ℕ) → Prop
  | _, _, .last _ _, t, ls, cs, pss =>
    ∃ l, ls = [l] ∧ cs = [] ∧ pss = [l.positions] ∧ PosRead l.positions (finalPositions t)
  | _, _, @Ladder.cons _ sh' κ' L, t, ls, cs, pss =>
    ∃ l ls' cs' pss', ls = l :: ls' ∧
      cs = ⟨κ' + sh'.R, merkleCommitWith H (3 * 2 ^ sh'.ℓ) (laterRows (levelWord t))⟩ :: cs' ∧
      pss = l.positions :: pss' ∧ PosRead l.positions (levelPositions t) ∧
      l.root = some (merkleCommitWith H (3 * 2 ^ sh'.ℓ) (laterRows (levelWord t))).root ∧
      LadderRead H L (levelWire t).2 ls' cs' pss'

/-- **A chain of levels read back**: the walk's levels, equal to the transcript's but for what the
algebra does not read; the commitments and positions kept, in order; and what the openings
need. -/
theorem back_ladder : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ),
    (∀ x ∈ L.shapes, 0 < 192 / (x.msgLog + x.rate)) →
    ∀ {t : (seqSpec L.steps).FullTranscript} {s s' : PState},
    (ladderCodec (proveOps H fuel) L).RunsAs proveSem t s s' →
    ∃ ls cs pss, Reads (Verify.walkLevels (Verify.readerOps H) L.shapes) s.2 s'.2 ls ∧
      Verify.eraseLevels L.shapes ls = Verify.eraseLevels L.shapes (ladderWire L t) ∧
      s'.1.commits.toList = s.1.commits.toList ++ cs ∧
      s'.1.positions.toList = s.1.positions.toList ++ pss ∧ s'.2.merkle = s.2.merkle ∧
      LadderRead H L t ls cs pss
  | _, _, .last sh nf, hd, t, s, s', h => by
    obtain ⟨l, hr, he, hb, hm, hp⟩ :=
      back_final H fuel sh nf (hd _ (List.mem_singleton_self _)) h
    refine ⟨[l], [], [l.positions], ?_, ?_, by rw [hb]; simp, by rw [hb]; simp, hm,
      ⟨l, rfl, rfl, rfl, hp⟩⟩
    · exact hr.bind ((Reads.pure _ _).bind_ret rfl)
    · simp only [Whir.Ladder.shapes, Verify.eraseLevels, ladderWire, he]
  | _, _, @Ladder.cons sh sh' κ' L, hd, t, s, s', h => by
    obtain ⟨sm, l, hr, he, hb, hm, hp, ho, hrest⟩ :=
      back_level H fuel sh sh' κ' (hd _ (List.mem_cons_self ..)) h
    obtain ⟨ls, cs, pss, hr', he', hc', hp', hm', hl'⟩ :=
      back_ladder L (fun x hx ↦ hd x (List.mem_cons_of_mem _ hx)) hrest
    refine ⟨l :: ls, _ :: cs, l.positions :: pss, hr.bind (hr'.bind_ret rfl), ?_,
      by rw [hc', hb]; simp, by rw [hp', hb]; simp, hm'.trans hm,
      ⟨l, ls, cs, pss, rfl, rfl, rfl, hp, ho, hl'⟩⟩
    simp only [Whir.Ladder.shapes, Verify.eraseLevels, ladderWire, he, he']

end Whir

/-! ## The chain read back -/

section Chain

variable (H : List UInt8 → Id Digest) (fuel : ℕ)

/-- The proof reader's scalars are the reader's. -/
theorem readerOps_nextScalars : ∀ k : ℕ,
    (Verify.readerOps H).nextScalars k = Reader.nextScalars (M := PrunedMerklePaths) H k
  | 0 => rfl
  | k + 1 => by
    simp only [Verify.ChainOps.nextScalars, Reader.nextScalars, readerOps_nextScalars k]
    rfl

/-- The announced sizes and rate are read back as the eight scalars of the announcement. -/
theorem reads_announce {s : Sizes} {ρ : ℕ} {s₀ s₁ : PState} {u : Unit}
    (h : proveSem.Runs (StateT.lift (Writer.announce H s ρ) : ProveM Id Unit) s₀ u s₁) :
    s₁.1 = s₀.1 ∧ s₁.2.merkle = s₀.2.merkle ∧
      Reads ((Verify.readerOps H).nextScalars 8) s₀.2 s₁.2 (announcement s ρ) := by
  obtain ⟨hb, hw⟩ := runs_lift.mp h
  have hm := merkle_addScalars H _ hw
  have hs := readsBack_scalars (M := PrunedMerklePaths) H (announcement s ρ)
  rw [show (announcement s ρ).length = 8 by simp [announcement]] at hs
  obtain ⟨xs, ms, b, h₁, h₂, rfl, h₃⟩ := hs _ _ _ hw
  refine ⟨hb, hm, xs, ms, h₁, h₂, ?_⟩
  rw [readerOps_nextScalars]
  exact h₃

/-- The level-0 word of a transcript of the compiled protocol. -/
abbrev level0Word {I : M3Instance} {sh : Whir.Shape} {κ : ℕ} {L : Ladder sh κ}
    (t : (listBindingSpec I sh κ L).FullTranscript) : KWord sh.ℓ (κ + sh.R) sh.t :=
  t.fst.fst.fst.fst.fst.fst.fst 0

/-- The public-input message of a transcript of the compiled protocol. -/
abbrev pubMessage {I : M3Instance} {sh : Whir.Shape} {κ : ℕ} {L : Ladder sh κ}
    (t : (listBindingSpec I sh κ L).FullTranscript) : List E :=
  t.fst.fst.fst.fst.snd 1

/-- WHIR's chain of levels' transcript within a transcript of the compiled protocol. -/
abbrev ladderPart {I : M3Instance} {sh : Whir.Shape} {κ : ℕ} {L : Ladder sh κ}
    (t : (listBindingSpec I sh κ L).FullTranscript) : (seqSpec L.steps).FullTranscript :=
  seqTail (seqTail t.snd)

/-- **The chain walk reads the honest prover's stream back**: run from before the announcement,
on the announcement and the stream the compiled protocol's prover writes against its wire, the
walk returns a wire equal to the transcript's (`wireOf`) but for what the algebra does not read,
the commitment root the level-0 word's; the book keeps the level-0 commitment, then the later
ones, and the levels' raw positions, as the openings need (`LadderRead`). The public input's
message must have one value per sent line, which the walk reads. -/
theorem walkChain_reads {prog : Program} {s : Sizes} {ρ : ℕ} (input : PublicInput)
    {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (n : ℕ)
    (hd : ∀ x ∈ L.shapes, 0 < 192 / (x.msgLog + x.rate))
    {t : (listBindingSpec (Verify.leanVm prog s) sh κ L).FullTranscript} {s₀ s₁ s₂ : PState}
    {u : Unit} (hann : proveSem.Runs (StateT.lift (Writer.announce H s ρ) : ProveM Id Unit)
      s₀ u s₁)
    (h : (compiledCodec (proveOps H fuel) (Verify.leanVm prog s) n L).RunsAs proveSem t s₁ s₂)
    (hpub : (pubMessage t).length =
      PublicInput.sentCount (Verify.leanVm prog s) ((Verify.leanVm prog s).publicLines input)) :
    ∃ w cs pss, Reads (Verify.walkChain (Verify.readerOps H) prog s input L.shapes) s₀.2 s₂.2 w ∧
      w.erase L.shapes = (wireOf (Verify.leanVm prog s) L t).erase L.shapes ∧
      w.root = (merkleCommitWith H (2 ^ sh.ℓ) (level0Rows n (level0Word t))).root ∧
      s₂.1.commits.toList = s₀.1.commits.toList ++
        ⟨κ + sh.R, merkleCommitWith H (2 ^ sh.ℓ) (level0Rows n (level0Word t))⟩ :: cs ∧
      s₂.1.positions.toList = s₀.1.positions.toList ++ pss ∧ s₂.2.merkle = s₀.2.merkle ∧
      (∃ ys, s₂.2.stream.toList = s₁.2.stream.toList ++ ys) ∧
      LadderRead H L (ladderPart t) w.whir cs pss := by
  obtain ⟨hb₀, hm₀, r₀⟩ := reads_announce H hann
  obtain ⟨f₇, h₇, hwh⟩ := RoundCodec.RunsAs.append_inv proveSem h
  obtain ⟨f₆, h₆, he⟩ := RoundCodec.RunsAs.append_inv proveSem h₇
  obtain ⟨f₅, h₅, hlam⟩ := RoundCodec.RunsAs.append_inv proveSem h₆
  obtain ⟨f₄, h₄, hfl⟩ := RoundCodec.RunsAs.append_inv proveSem h₅
  obtain ⟨f₃, h₃, hpb⟩ := RoundCodec.RunsAs.append_inv proveSem h₄
  obtain ⟨f₂, h₂, htb⟩ := RoundCodec.RunsAs.append_inv proveSem h₃
  obtain ⟨f₁, hcm, hbs⟩ := RoundCodec.RunsAs.append_inv proveSem h₂
  have rc : proveSem.Runs ((proveOps H fuel).commit (κ + sh.R) (2 ^ sh.ℓ)
      (level0Rows n (level0Word t))) s₁ () f₁ := RoundCodec.runsAs_sendOne hcm
  obtain ⟨hkc, hmc, bc⟩ := runs_commit H fuel rc
  have bbus := back_bus H fuel _ hbs
  have btab := back_table H fuel _ htb
  have bpub := back_pub H fuel hpb hpub
  have bfl := back_flock H fuel (s.τ 5) hfl
  have blam := back_sample H fuel (RoundCodec.runsAs_chal hlam)
  have ee := RoundCodec.runsAs_empty he
  subst ee
  obtain ⟨g₁, hg₀, hg⟩ := RoundCodec.RunsAs.append_inv proveSem hwh
  have eg := RoundCodec.runsAs_empty hg₀
  subst eg
  obtain ⟨g₂, hfirst, hlad⟩ := RoundCodec.RunsAs.append_inv proveSem hg
  have bfirst := back_sendPlain H fuel (by norm_num) _ (RoundCodec.runsAs_msg hfirst)
  obtain ⟨ls, cs, pss, rl, el, hcl, hpl, hml, hrl⟩ := back_ladder H fuel L hd hlad
  have hw : Verify.walkChain (Verify.readerOps H) prog s input L.shapes = do
      let _ ← (Verify.readerOps H).nextScalars 8
      let root ← (Verify.readerOps H).nextRoot
      let bus ← Verify.walkBus (Verify.readerOps H) (Verify.leanVm prog s).μBus
        (Verify.leanVm prog s).busClaims
      let table ← Verify.walkTables (Verify.readerOps H) (Verify.leanVm prog s).τmax
        (Verify.leanVm prog s).tableColumns
      let pub ← Verify.walkPub (Verify.readerOps H)
        (PublicInput.sentCount (Verify.leanVm prog s)
          ((Verify.leanVm prog s).publicLines input))
      let flock ← Verify.walkFlock (Verify.readerOps H) (s.τ 5)
      let lam ← (Verify.readerOps H).sample
      let first ← (Verify.readerOps H).nextScalars 2
      let ls ← Verify.walkLevels (Verify.readerOps H) L.shapes
      return ⟨root, bus, table, pub, flock, lam, first, ls⟩ := by
    simp [Verify.walkChain, Verify.walkSetup, Verify.walkWhir]
  refine ⟨⟨(merkleCommitWith H (2 ^ sh.ℓ) (level0Rows n (level0Word t))).root,
    busWireOf _ t.fst.fst.fst.fst.fst.fst.snd, tableWireOf _ t.fst.fst.fst.fst.fst.snd,
    pubWireOf t.fst.fst.fst.fst.snd, flockWireOf (s.τ 5) t.fst.fst.fst.snd,
    drawOf t.fst.fst.snd, polyWire 1 (msgOf (seqHead (seqTail t.snd))), ls⟩, cs, pss, ?_, ?_,
    rfl, ?_, ?_, ?_, ?_, hrl⟩
  · rw [hw]
    exact r₀.bind (bc.bind (bbus.2.2.bind (btab.2.2.bind (bpub.2.2.bind (bfl.2.2.bind
      (blam.2.2.bind (bfirst.2.2.bind (rl.bind_ret rfl))))))))
  · simp only [Verify.Wire.erase, wireOf, whirWireOf, el]
    rfl
  · rw [hcl, bfirst.1, blam.1, bfl.1, bpub.1, btab.1, bbus.1, hkc, hb₀]
    simp
  · rw [hpl, bfirst.1, blam.1, bfl.1, bpub.1, btab.1, bbus.1, hkc, hb₀]
  · rw [hml, bfirst.2.1, blam.2.1, bfl.2.1, bpub.2.1, btab.2.1, bbus.2.1, hmc, hm₀]
  · obtain ⟨y₁, e₁⟩ := bc.stream
    obtain ⟨y₂, e₂⟩ := bbus.2.2.stream
    obtain ⟨y₃, e₃⟩ := btab.2.2.stream
    obtain ⟨y₄, e₄⟩ := bpub.2.2.stream
    obtain ⟨y₅, e₅⟩ := bfl.2.2.stream
    obtain ⟨y₆, e₆⟩ := blam.2.2.stream
    obtain ⟨y₇, e₇⟩ := bfirst.2.2.stream
    obtain ⟨y₈, e₈⟩ := rl.stream
    refine ⟨y₁ ++ (y₂ ++ (y₃ ++ (y₄ ++ (y₅ ++ (y₆ ++ (y₇ ++ y₈)))))), ?_⟩
    rw [e₈, e₇, e₆, e₅, e₄, e₃, e₂, e₁]
    simp only [List.append_assoc]

end Chain

end Prove

end
end LeanerVM.Protocol
