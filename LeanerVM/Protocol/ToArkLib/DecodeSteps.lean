/-
  LeanerVM.Protocol.ToArkLib.DecodeSteps

  Slot decoders of the repository's schedules: runs of challenges, runs of sumcheck rounds, and
  lists of steps. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.DecodeTranscript
public import LeanerVM.Protocol.ToArkLib.StepSchedule

/-!
# Decoding schedules of steps

The decoders of `LeanerVM.Protocol.ToArkLib.DecodeTranscript` for the schedules of
`LeanerVM.Protocol.ToArkLib.Schedule` and `LeanerVM.Protocol.ToArkLib.StepSchedule`:

* `SlotDecoder.draws s k` decodes `draws C k`, each challenge by the slot `s`;
* `SlotDecoder.rounds poly chal next σ m` decodes `roundsSpec C d m`, carrying a state (the
  running claim, say) from each round to the next;
* a `SeqDecoder α l` holds a decoder of each step of a list `l` of steps, given the transcripts of
  the steps before it, and `SeqDecoder.toDecoder` decodes `seqSpec l` (`SeqDecoder.runFull_cons`,
  `SeqDecoder.decode_cons`).

For example, take readings `ρ` that are absorbed values or squeezed states, read by partial maps
`absorbed? : ρ → Option M` and `squeezed? : ρ → Option S`. A message absorbed as one reading, a
challenge derived from one squeezed state by `challengeOf : S → C`, and the commitment of a word
whose root takes two readings, the word itself given by a supplier `w` (the root unchecked), are
the steps `[.msg M, .chal C _, .oracle W _]`, decoded by the `SeqDecoder ρ` of them

```
(single (Slot.next absorbed?), fun _ ↦
  (single (Slot.next fun r ↦ (squeezed? r).map challengeOf), fun _ ↦
    (single (Slot.take 2 fun _ ↦ some w), fun _ ↦ ⟨⟩)))
```

where a later decoder may read any transcript before it in place of `_`.
-/

namespace LeanerVM.Protocol

open ProtocolSpec StepSchedule

@[expose] public section

namespace SlotDecoder

variable {α : Type}

/-- `k` challenges in `C`, each read by the slot `s`. -/
def draws {C : Type} (s : Slot α C) : (k : ℕ) → SlotDecoder α (Protocol.draws C k)
  | 0 => empty
  | k + 1 => append (pSpec₁ := Protocol.draws C k) (pSpec₂ := draw C) (draws s k)
      fun _ ↦ single s

/-- `m` sumcheck rounds of degree `d` over `C`: the polynomial of each round by `poly σ` and its
challenge by `chal σ`, where the state `σ` (the running claim, say) is carried from each round to
the next by `next`. The challenge's slot sees the state, not the round's polynomial. -/
def rounds {C σ : Type} {d : ℕ} (poly : σ → Slot α (Vector C (d + 1))) (chal : σ → Slot α C)
    (next : σ → (roundSpec C d).FullTranscript → σ) : σ → (m : ℕ) → SlotDecoder α (roundsSpec C d m)
  | _, 0 => empty
  | s, m + 1 => append (pSpec₁ := roundSpec C d) (pSpec₂ := roundsSpec C d m)
      (append (pSpec₁ := say (Vector C (d + 1))) (pSpec₂ := draw C) (single (poly s))
        fun _ ↦ single (chal s))
      fun t ↦ rounds poly chal next (next s t) m

/-- A run of `k + 1` challenges as one slot: the first `k`, then the last. -/
theorem toSlot_draws_succ {C : Type} (s : Slot α C) (k : ℕ) :
    (draws s (k + 1)).toSlot = do
      let t ← (draws s k).toSlot
      let x ← s
      return t ++ₜ oneTranscript (pSpec := draw C) x := by
  have h := toSlot_append (pSpec₁ := Protocol.draws C k) (pSpec₂ := draw C) (draws s k)
    fun _ ↦ single s
  rw [toSlot_single] at h
  simp only [bind_map_left] at h
  exact h

/-- A run of `m + 1` sumcheck rounds as one slot: the first round's polynomial and challenge, then
the rest from the state they lead to. -/
theorem toSlot_rounds_succ {C σ : Type} {d : ℕ} (poly : σ → Slot α (Vector C (d + 1)))
    (chal : σ → Slot α C) (next : σ → (roundSpec C d).FullTranscript → σ) (a : σ) (m : ℕ) :
    (rounds poly chal next a (m + 1)).toSlot = do
      let p ← poly a
      let c ← chal a
      let t ← (rounds poly chal next (next a (oneTranscript (pSpec := say (Vector C (d + 1))) p ++ₜ
        oneTranscript (pSpec := draw C) c)) m).toSlot
      return (oneTranscript (pSpec := say (Vector C (d + 1))) p ++ₜ
        oneTranscript (pSpec := draw C) c) ++ₜ t := by
  have h := toSlot_append (pSpec₁ := roundSpec C d) (pSpec₂ := roundsSpec C d m)
    (append (pSpec₁ := say (Vector C (d + 1))) (pSpec₂ := draw C) (single (poly a))
      fun _ ↦ single (chal a)) fun t ↦ rounds poly chal next (next a t) m
  rw [toSlot_append (pSpec₁ := say (Vector C (d + 1))) (pSpec₂ := draw C), toSlot_single,
    toSlot_single] at h
  simp only [bind_map_left, bind_assoc, pure_bind] at h
  exact h

/-- Runs of challenges read alike when their slots do. -/
theorem readsAlike_draws {C : Type} {s s' : Slot α C} (h : Slot.Agree (fun _ _ ↦ True) s s') :
    (k : ℕ) → ReadsAlike (draws s k) (draws s' k)
  | 0 => readsAlike_empty
  | k + 1 => readsAlike_append (readsAlike_draws h k) fun _ _ ↦ readsAlike_single h

/-- Runs of sumcheck rounds read alike when their polynomials' and challenges' slots do, whatever
states they carry. -/
theorem readsAlike_rounds {C σ σ' : Type} {d : ℕ} {poly : σ → Slot α (Vector C (d + 1))}
    {poly' : σ' → Slot α (Vector C (d + 1))} {chal : σ → Slot α C} {chal' : σ' → Slot α C}
    {next : σ → (roundSpec C d).FullTranscript → σ}
    {next' : σ' → (roundSpec C d).FullTranscript → σ'}
    (hp : ∀ a b, Slot.Agree (fun _ _ ↦ True) (poly a) (poly' b))
    (hc : ∀ a b, Slot.Agree (fun _ _ ↦ True) (chal a) (chal' b)) :
    ∀ (a : σ) (b : σ') (m : ℕ),
      ReadsAlike (rounds poly chal next a m) (rounds poly' chal' next' b m)
  | _, _, 0 => readsAlike_empty
  | a, b, m + 1 => readsAlike_append
      (readsAlike_append (readsAlike_single (hp a b)) fun _ _ ↦ readsAlike_single (hc a b))
      fun t t' ↦ readsAlike_rounds hp hc (next a t) (next' b t') m

end SlotDecoder

/-- Decoders of the steps of a list, each given the transcripts of the steps before it. -/
def SeqDecoder (α : Type) : List Step → Type
  | [] => PUnit
  | a :: l => SlotDecoder α a.spec × (a.spec.FullTranscript → SeqDecoder α l)

namespace SeqDecoder

variable {α : Type}

/-- The decoder of `seqSpec l`: the steps' decoders in sequence. -/
def toDecoder : {l : List Step} → SeqDecoder α l → SlotDecoder α (seqSpec l)
  | [], _ => SlotDecoder.empty
  | a :: l, D => SlotDecoder.append (pSpec₁ := a.spec) (pSpec₂ := seqSpec l) D.1
      fun t ↦ (D.2 t).toDecoder

/-- The full run of a list of steps is the full run of its first step, then that of the rest. -/
theorem runFull_cons {a : Step} {l : List Step} (D : SeqDecoder α (a :: l)) (r : List α) :
    D.toDecoder.runFull r = (D.1.runFull r).bind fun p ↦
      ((D.2 p.1).toDecoder.runFull p.2).map fun q ↦ (p.1 ++ₜ q.1, q.2) :=
  SlotDecoder.runFull_append _ _ r

/-- Exact decoding of a list of steps is the full run of its first step, then exact decoding of
the rest. -/
theorem decode_cons {a : Step} {l : List Step} (D : SeqDecoder α (a :: l)) (r : List α) :
    D.toDecoder.decode r =
      (D.1.runFull r).bind fun p ↦ ((D.2 p.1).toDecoder.decode p.2).map (p.1 ++ₜ ·) :=
  SlotDecoder.decode_append _ _ r

end SeqDecoder

end

end LeanerVM.Protocol
