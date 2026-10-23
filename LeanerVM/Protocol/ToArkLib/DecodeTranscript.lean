/-
  LeanerVM.Protocol.ToArkLib.DecodeTranscript

  The transcript of a protocol decoded round by round from a list of readings: at each round a
  slot reads the round's value off the front of the list, given the rounds before it. Decoders of
  appended schedules and of lists of steps are built from decoders of their parts. Candidate for
  ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.KnowledgeAppend
public import LeanerVM.Protocol.ToArkLib.StepSchedule

/-!
# Decoding transcripts from readings

A run of a protocol may be recorded as a flat list of readings (the blocks a Fiat–Shamir chain
absorbed and squeezed, say) rather than as a transcript. A `Slot α β` reads a value of type `β` off
the front of a `List α` and returns the readings left; what it reads depends only on the readings
it consumes (`Slot.read_append`). `Slot.pure`, `Slot.next`, `Slot.take`, `Slot.map` and
`Slot.bind` build slots. A `SlotDecoder α pSpec` gives, at each round of `pSpec`, the slot that
reads the round's value, from the transcript of the rounds before it: a message may be decoded
with a claim the earlier rounds leave. Then

* `run D i hi l`: the first `i` rounds read off `l`, with the readings left; `runFull D l`: all of
  them;
* `decodeAt D i l`: the transcript of the first `i` rounds, if they read exactly `l`;
* `decode D l`: the full transcript, if it reads exactly `l`;
* `decodePrefix D l`: the longest prefix that reads exactly `l`, with its number of rounds
  (`decodePrefix_eq_some_iff`).

`decodePrefix_mono`: readings appended to `l` only extend the prefix decoded from it.
`decode_eq_of_decodePrefix`: the full transcript decoded from `l ++ l'` begins with the prefix
decoded from `l`.

Decoders compose. `empty` decodes a schedule of no round, `single s` one of one round by the slot
`s` (`runFull_empty`, `runFull_single`). `append D₁ D₂` decodes `pSpec₁ ++ₚ pSpec₂`: the rounds
of `pSpec₁` by `D₁`, then those of `pSpec₂` by `D₂ t₁`, where `t₁` is the transcript of `pSpec₁`
read first. `runFull_append` and `decode_append` give its full decoding as the two in sequence;
`run_append_left` and `run_append_right` its partial runs, read through the projections
`Verifier.KnowledgeAppend.left`, `firstOf` and `right`. `draws` decodes a run of challenges,
`rounds` a run of sumcheck rounds carrying a state (the running claim, say) from round to round. A
`SeqDecoder α l` holds a decoder of each step of a list `l` of schedule steps, given the
transcripts of the steps before it; `SeqDecoder.toDecoder` decodes `seqSpec l`
(`SeqDecoder.runFull_cons`, `SeqDecoder.decode_cons`).

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

/-! ## Slots -/

/-- A value of type `β` read off the front of a list of readings, with the readings left. What it
reads depends only on the readings it consumes: readings appended after them change neither the
value nor what is left before them. -/
structure Slot (α β : Type) where
  /-- The value read off the front of the readings, and the readings left. -/
  read : List α → Option (β × List α)
  /-- Readings appended to the input are left after the value. -/
  read_append : ∀ {l : List α} {x : β} {r : List α}, read l = some (x, r) →
    ∀ l', read (l ++ l') = some (x, r ++ l')

namespace Slot

variable {α β γ : Type}

/-- The value `x`, read off no reading. -/
def pure (x : β) : Slot α β where
  read l := some (x, l)
  read_append h l' := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rfl

/-- One reading, through a partial map. -/
def next (f : α → Option β) : Slot α β where
  read
    | [] => none
    | a :: r => (f a).map (·, r)
  read_append {l x r} h l' := by
    cases l with
    | nil => cases h
    | cons a l =>
      obtain ⟨y, hy, he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      simp [hy]

/-- `k` readings, through a partial map of the list of them. -/
def take (k : ℕ) (f : List α → Option β) : Slot α β where
  read l := if k ≤ l.length then (f (l.take k)).map (·, l.drop k) else none
  read_append {l x r} h l' := by
    by_cases hk : k ≤ l.length
    · rw [ite_eq_left hk] at h
      obtain ⟨y, hy, he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [ite_eq_left (by simp; omega), List.take_append_of_le_length hk,
        List.drop_append_of_le_length hk, hy]
      rfl
    · rw [ite_eq_right hk] at h
      cases h

/-- The value of `s`, mapped by `g`. -/
def map (g : β → γ) (s : Slot α β) : Slot α γ where
  read l := (s.read l).map fun p ↦ (g p.1, p.2)
  read_append {l x r} h l' := by
    obtain ⟨⟨y, r'⟩, hy, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rw [s.read_append hy l']
    rfl

/-- The slot `s`, then the slot `f x` for the value `x` it read. -/
def bind (s : Slot α β) (f : β → Slot α γ) : Slot α γ where
  read l := (s.read l).bind fun p ↦ (f p.1).read p.2
  read_append {l x r} h l' := by
    obtain ⟨⟨y, r'⟩, hy, hf⟩ := Option.bind_eq_some_iff.mp h
    rw [s.read_append hy l']
    exact (f y).read_append hf l'

end Slot

/-! ## Slot decoders -/

/-- A slot decoder for `pSpec`: at each round, given the transcript of the rounds before it, the
slot that reads the round's value. -/
structure SlotDecoder (α : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- The slot of round `k`, given the transcript of the rounds before it. -/
  slot : (k : Fin n) → pSpec.Transcript k.castSucc → Slot α (pSpec.«Type» k)

namespace SlotDecoder

variable {α : Type}

section Run

variable {n : ℕ} {pSpec : ProtocolSpec n} (D : SlotDecoder α pSpec)

/-- The first `i` rounds read off `l`, with the readings left. -/
def run : (i : ℕ) → (hi : i ≤ n) → List α → Option (pSpec.Transcript ⟨i, by omega⟩ × List α)
  | 0, _, l => some (fun a ↦ a.elim0, l)
  | i + 1, hi, l => (run i (by omega) l).bind fun p ↦
      ((D.slot ⟨i, hi⟩ p.1).read p.2).map fun q ↦ (Transcript.concat (m := ⟨i, hi⟩) q.1 p.1, q.2)

/-- Every round read off `l`, with the readings left. -/
def runFull (l : List α) : Option (pSpec.FullTranscript × List α) := D.run n le_rfl l

/-- The value read, if no reading is left. -/
def whole {β : Type} : Option (β × List α) → Option β
  | some (x, []) => some x
  | _ => none

/-- The transcript of the first `i` rounds, if they read exactly `l`. -/
def decodeAt (i : Fin (n + 1)) (l : List α) : Option (pSpec.Transcript i) :=
  whole (D.run i.val (by omega) l)

/-- The full transcript, if it reads exactly `l`. -/
def decode (l : List α) : Option pSpec.FullTranscript := whole (D.runFull l)

/-- The longest prefix of at most `k` rounds that reads exactly `l`, with its number of rounds. -/
def prefixUpTo (l : List α) : (k : ℕ) → k ≤ n → Option (Σ i : Fin (n + 1), pSpec.Transcript i)
  | 0, _ => (D.decodeAt ⟨0, by omega⟩ l).map (⟨⟨0, by omega⟩, ·⟩)
  | k + 1, hk => ((D.decodeAt ⟨k + 1, by omega⟩ l).map (⟨⟨k + 1, by omega⟩, ·⟩)).or
      (prefixUpTo l k (by omega))

/-- The longest prefix of the transcript that reads exactly `l`, with its number of rounds. -/
def decodePrefix (l : List α) : Option (Σ i : Fin (n + 1), pSpec.Transcript i) :=
  D.prefixUpTo l n le_rfl

/-- `whole o` is the value of `o` exactly when no reading is left. -/
theorem whole_eq_some {β : Type} {o : Option (β × List α)} {x : β} :
    whole o = some x ↔ o = some (x, []) := by
  rcases o with _ | ⟨y, _ | ⟨a, r⟩⟩ <;> simp [whole]

/-- The first `i` rounds read exactly `l` when their run leaves no reading. -/
theorem decodeAt_eq_some {i : Fin (n + 1)} {l : List α} {tr : pSpec.Transcript i} :
    D.decodeAt i l = some tr ↔ D.run i.val (by omega) l = some (tr, []) := whole_eq_some

/-- The full transcript reads exactly `l` when the full run leaves no reading. -/
theorem decode_eq_some {l : List α} {t : pSpec.FullTranscript} :
    D.decode l = some t ↔ D.runFull l = some (t, []) := whole_eq_some

/-- Readings appended to the input of a run are left after it. -/
theorem run_append {i : ℕ} {hi : i ≤ n} {l : List α} {tr : pSpec.Transcript ⟨i, by omega⟩}
    {r : List α} (h : D.run i hi l = some (tr, r)) (l' : List α) :
    D.run i hi (l ++ l') = some (tr, r ++ l') := by
  induction i generalizing r with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rfl
  | succ i ih =>
    obtain ⟨⟨t, s⟩, hp, ⟨x, s'⟩, hq, he⟩ := by
      simpa only [run, Option.bind_eq_some_iff, Option.map_eq_some_iff] using h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    simp only [run, ih (hi := by omega) hp, Option.bind_some, (D.slot _ _).read_append hq,
      Option.map_some]

/-- A run of `j` rounds passes through the run of `i ≤ j` rounds, with the transcript's first `i`
rounds. -/
theorem run_take {j : ℕ} {hj : j ≤ n} {l : List α} {tr : pSpec.Transcript ⟨j, by omega⟩}
    {r : List α} (h : D.run j hj l = some (tr, r)) (i : ℕ) (hij : i ≤ j) :
    ∃ r', D.run i (hij.trans hj) l = some (FullTranscript.take i hij tr, r') := by
  induction j generalizing r with
  | zero =>
    obtain rfl : i = 0 := by omega
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨_, rfl⟩
  | succ j ih =>
    by_cases hji : i = j + 1
    · subst hji
      exact ⟨r, h⟩
    · obtain ⟨⟨t, s⟩, hp, ⟨x, s'⟩, hq, he⟩ := by
        simpa only [run, Option.bind_eq_some_iff, Option.map_eq_some_iff] using h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      obtain ⟨r', hr'⟩ := ih (hj := by omega) hp (by omega)
      refine ⟨r', hr'.trans ?_⟩
      congr 2
      funext a
      exact (Transcript.concat_castSucc (m := ⟨j, hj⟩) x t
        (Fin.castLE (show i ≤ j by omega) a)).symm

private theorem prefixUpTo_eq_some_iff {l : List α} {k : ℕ} {hk : k ≤ n} {i : Fin (n + 1)}
    {tr : pSpec.Transcript i} :
    D.prefixUpTo l k hk = some ⟨i, tr⟩ ↔
      i.val ≤ k ∧ D.decodeAt i l = some tr ∧
        ∀ j : Fin (n + 1), i < j → j.val ≤ k → D.decodeAt j l = none := by
  induction k with
  | zero =>
    simp only [prefixUpTo, Option.map_eq_some_iff, Sigma.mk.inj_iff]
    constructor
    · rintro ⟨t, ht, rfl, he⟩
      obtain rfl := eq_of_heq he
      exact ⟨le_rfl, ht, fun j hj hj0 ↦ absurd (Fin.lt_def.mp hj) (by simp only; omega)⟩
    · rintro ⟨hi0, ht, -⟩
      obtain rfl : i = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext (Nat.le_zero.mp hi0)
      exact ⟨tr, ht, rfl, HEq.rfl⟩
  | succ k ih =>
    simp only [prefixUpTo, Option.or_eq_some_iff, Option.map_eq_some_iff, Sigma.mk.inj_iff,
      Option.map_eq_none_iff, ih]
    constructor
    · rintro (⟨t, ht, rfl, he⟩ | ⟨hn, hik, ht, hlater⟩)
      · obtain rfl := eq_of_heq he
        exact ⟨le_rfl, ht, fun j hj hjk ↦ absurd (Fin.lt_def.mp hj) (by simp only; omega)⟩
      · refine ⟨by omega, ht, fun j hj hjk ↦ ?_⟩
        by_cases hjk' : j.val ≤ k
        · exact hlater j hj hjk'
        · obtain rfl : j = ⟨k + 1, Nat.lt_succ_of_le hk⟩ := Fin.ext (show j.val = k + 1 by omega)
          exact hn
    · rintro ⟨hik, ht, hlater⟩
      by_cases hik' : i.val = k + 1
      · obtain rfl : i = ⟨k + 1, Nat.lt_succ_of_le hk⟩ := Fin.ext hik'
        exact Or.inl ⟨tr, ht, rfl, HEq.rfl⟩
      · exact Or.inr ⟨hlater _ (Fin.lt_def.mpr (show i.val < k + 1 by omega)) le_rfl, by omega,
          ht, fun j hj hjk ↦ hlater j hj (by omega)⟩

/-- `decodePrefix l` is the longest prefix that reads exactly `l`. -/
theorem decodePrefix_eq_some_iff {l : List α} {i : Fin (n + 1)} {tr : pSpec.Transcript i} :
    D.decodePrefix l = some ⟨i, tr⟩ ↔
      D.decodeAt i l = some tr ∧ ∀ j : Fin (n + 1), i < j → D.decodeAt j l = none := by
  rw [decodePrefix, prefixUpTo_eq_some_iff]
  exact ⟨fun ⟨_, ht, hj⟩ ↦ ⟨ht, fun j h ↦ hj j h (by omega)⟩,
    fun ⟨ht, hj⟩ ↦ ⟨by omega, ht, fun j h _ ↦ hj j h⟩⟩

/-- Readings the full transcript reads exactly have it as their longest prefix. -/
theorem decodePrefix_of_decode {l : List α} {t : pSpec.FullTranscript} (h : D.decode l = some t) :
    D.decodePrefix l = some ⟨Fin.last n, t⟩ :=
  D.decodePrefix_eq_some_iff.mpr ⟨h, fun j hj ↦ absurd hj (not_lt.mpr (Fin.le_last j))⟩

/-- **Monotone in the input**: readings appended to `l` only extend the prefix decoded from it. -/
theorem decodePrefix_mono {l l' : List α} {i j : Fin (n + 1)} {tr : pSpec.Transcript i}
    {tr' : pSpec.Transcript j} (h : D.decodePrefix l = some ⟨i, tr⟩)
    (h' : D.decodePrefix (l ++ l') = some ⟨j, tr'⟩) :
    ∃ hij : i.val ≤ j.val, FullTranscript.take i.val hij tr' = tr := by
  have hr := D.decodeAt_eq_some.mp (D.decodePrefix_eq_some_iff.mp h).1
  have hr' := D.decodeAt_eq_some.mp (D.decodePrefix_eq_some_iff.mp h').1
  have ha := D.run_append hr l'
  by_cases hij : i.val ≤ j.val
  · obtain ⟨r', hr''⟩ := D.run_take hr' i.val hij
    rw [ha] at hr''
    exact ⟨hij, (Prod.mk.inj (Option.some.inj hr'')).1.symm⟩
  · obtain ⟨s, hs⟩ := D.run_take hr j.val (by omega)
    have hs' := D.run_append hs l'
    rw [hr'] at hs'
    obtain rfl : l' = [] := (List.append_eq_nil_iff.mp (Prod.mk.inj (Option.some.inj hs')).2.symm).2
    rw [List.append_nil, h] at h'
    exact absurd (congrArg Fin.val (Sigma.mk.inj_iff.mp (Option.some.inj h')).1) (by omega)

/-- The full transcript decoded from `l ++ l'` begins with the prefix decoded from `l`. -/
theorem decode_eq_of_decodePrefix {l l' : List α} {t : pSpec.FullTranscript} {i : Fin (n + 1)}
    {tr : pSpec.Transcript i} (ht : D.decode (l ++ l') = some t)
    (h : D.decodePrefix l = some ⟨i, tr⟩) : FullTranscript.take i.val i.is_le t = tr := by
  have ha := D.run_append (D.decodeAt_eq_some.mp (D.decodePrefix_eq_some_iff.mp h).1) l'
  obtain ⟨r', hr'⟩ := D.run_take (D.decode_eq_some.mp ht) i.val i.is_le
  rw [ha] at hr'
  exact (Prod.mk.inj (Option.some.inj hr')).1.symm

end Run

/-! ## Schedules of no round and of one round -/

/-- The decoder of a schedule of no round. -/
def empty {pSpec : ProtocolSpec 0} : SlotDecoder α pSpec where
  slot k := k.elim0

/-- The decoder of a schedule of one round, by the slot `s`. -/
def single {pSpec : ProtocolSpec 1} (s : Slot α (pSpec.«Type» 0)) : SlotDecoder α pSpec where
  slot
    | ⟨0, _⟩, _ => s

/-- A schedule of no round reads nothing. -/
theorem runFull_empty {pSpec : ProtocolSpec 0} (l : List α) :
    (empty : SlotDecoder α pSpec).runFull l = some (fun i ↦ i.elim0, l) := rfl

/-- A schedule of one round reads its value by its slot. -/
theorem runFull_single {pSpec : ProtocolSpec 1} (s : Slot α (pSpec.«Type» 0)) (l : List α) :
    ((single s).runFull l).map (fun p ↦ (p.1 0, p.2)) = s.read l := by
  change Option.map _ (Option.map _ (s.read l)) = s.read l
  cases s.read l <;> rfl

/-! ## Appended schedules -/

section Append

open Verifier.KnowledgeAppend

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- The rounds of `pSpec₁` in a transcript of `pSpec₁ ++ₚ pSpec₂` that has passed them, as a full
transcript of `pSpec₁`. -/
def firstOf {k : Fin (m + n + 1)} (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k) (h : m ≤ k.val) :
    pSpec₁.FullTranscript :=
  left tr (Fin.last m) h

/-- The decoder of `pSpec₁ ++ₚ pSpec₂`: the rounds of `pSpec₁` by `D₁`, then those of `pSpec₂` by
`D₂ t₁`, where `t₁` is the transcript of `pSpec₁` read first. -/
def append (D₁ : SlotDecoder α pSpec₁) (D₂ : pSpec₁.FullTranscript → SlotDecoder α pSpec₂) :
    SlotDecoder α (pSpec₁ ++ₚ pSpec₂) where
  slot := Fin.addCases (motive := fun k ↦
      (pSpec₁ ++ₚ pSpec₂).Transcript k.castSucc → Slot α ((pSpec₁ ++ₚ pSpec₂).«Type» k))
    (fun i tr ↦ (D₁.slot i (left tr i.castSucc (by simp))).map
      (cast (append_Type_castAdd (pSpec₂ := pSpec₂) i).symm))
    (fun j tr ↦ ((D₂ (firstOf tr (by simp))).slot j (right tr j.castSucc (by simp))).map
      (cast (append_Type_natAdd (pSpec₁ := pSpec₁) j).symm))

variable (D₁ : SlotDecoder α pSpec₁) (D₂ : pSpec₁.FullTranscript → SlotDecoder α pSpec₂)

private theorem append_slot_left (i : ℕ) (hi : i < m) (h : i < m + n)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ⟨i, by omega⟩) :
    (D₁.append D₂).slot ⟨i, h⟩ tr = (D₁.slot ⟨i, hi⟩ (left tr ⟨i, by omega⟩ le_rfl)).map
      (cast (append_Type_castAdd (pSpec₂ := pSpec₂) ⟨i, hi⟩).symm) := by
  dsimp only [append]
  exact congrFun (Fin.addCases_left (motive := fun k ↦
    (pSpec₁ ++ₚ pSpec₂).Transcript k.castSucc → Slot α ((pSpec₁ ++ₚ pSpec₂).«Type» k)) ⟨i, hi⟩) tr

private theorem append_slot_right (j : ℕ) (hj : j < n) (h : m + j < m + n)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ⟨m + j, by omega⟩) :
    (D₁.append D₂).slot ⟨m + j, h⟩ tr =
      ((D₂ (firstOf tr (Nat.le_add_right m j))).slot ⟨j, hj⟩ (right tr ⟨j, by omega⟩ le_rfl)).map
        (cast (append_Type_natAdd (pSpec₁ := pSpec₁) ⟨j, hj⟩).symm) := by
  dsimp only [append]
  exact congrFun (Fin.addCases_right (motive := fun k ↦
    (pSpec₁ ++ₚ pSpec₂).Transcript k.castSucc → Slot α ((pSpec₁ ++ₚ pSpec₂).«Type» k)) ⟨j, hj⟩) tr

/-- A run inside the first schedule is the first decoder's run, read through `left`. -/
theorem run_append_left (i : ℕ) (hi : i ≤ m) (l : List α) :
    ((D₁.append D₂).run i (by omega) l).map (fun p ↦ (left p.1 ⟨i, by omega⟩ le_rfl, p.2)) =
      D₁.run i hi l := by
  induction i with
  | zero =>
    simp only [run, Option.map_some]
    congr 2
    funext a
    exact a.elim0
  | succ i ih =>
    have ih := ih (by omega)
    simp only [run]
    cases ho : (D₁.append D₂).run i (by omega) l with
    | none =>
      rw [ho, Option.map_none] at ih
      rw [← ih]
      rfl
    | some p =>
      rw [ho, Option.map_some] at ih
      rw [← ih, Option.bind_some, Option.bind_some, append_slot_left D₁ D₂ i (by omega)]
      simp only [Slot.map, Option.map_map]
      cases hq : (D₁.slot ⟨i, by omega⟩ (left p.1 ⟨i, by omega⟩ le_rfl)).read p.2 with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Function.comp_apply, Option.some.injEq, Prod.mk.injEq,
          and_true]
        refine (left_concat (i := ⟨i, by omega⟩) p.1 _ ⟨i, by omega⟩ rfl
          (append_Type_castAdd (pSpec₂ := pSpec₂) ⟨i, by omega⟩)).trans ?_
        simp only [cast_cast, cast_eq]
        rfl

private theorem runFull_append_first (l : List α) :
    ((D₁.append D₂).run m (by omega) l).map (fun p ↦ (firstOf p.1 le_rfl, p.2)) = D₁.runFull l :=
  run_append_left D₁ D₂ m le_rfl l

private theorem run_append_right_aux (j : ℕ) (hj : j ≤ n) (l : List α) (i : ℕ) (hi : i ≤ m + n)
    (hij : i = m + j) :
    ((D₁.append D₂).run i hi l).map
        (fun p ↦ (firstOf p.1 (by simp only; omega), right p.1 ⟨j, by omega⟩ (by simp only; omega),
          p.2)) =
      (D₁.runFull l).bind fun p ↦ ((D₂ p.1).run j hj p.2).map fun q ↦ (p.1, q.1, q.2) := by
  induction j generalizing i with
  | zero =>
    have hij : i = m := hij
    subst i
    have hl := runFull_append_first D₁ D₂ l
    cases ho : (D₁.append D₂).run m hi l with
    | none =>
      rw [ho, Option.map_none] at hl
      rw [← hl]
      rfl
    | some p =>
      rw [ho, Option.map_some] at hl
      rw [← hl, Option.map_some, Option.bind_some]
      simp only [run, Option.map_some]
      refine congrArg some (Prod.ext rfl (Prod.ext ?_ rfl))
      funext a
      exact a.elim0
  | succ j ih =>
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    obtain rfl : i = m + j := by omega
    have ih := ih (by omega) (m + j) (by omega) rfl
    simp only [run]
    cases ho : (D₁.append D₂).run (m + j) (by omega) l with
    | none =>
      rw [ho, Option.map_none] at ih
      rw [Option.bind_none, Option.map_none]
      cases hf : D₁.runFull l with
      | none => rfl
      | some p =>
        rw [hf, Option.bind_some, eq_comm, Option.map_eq_none_iff] at ih
        rw [Option.bind_some, ih, Option.bind_none, Option.map_none]
    | some p =>
      rw [ho, Option.map_some, eq_comm, Option.bind_eq_some_iff] at ih
      obtain ⟨⟨t₁, r₁⟩, hf, hq⟩ := ih
      obtain ⟨⟨t₂, r₂⟩, hr, he⟩ := Option.map_eq_some_iff.mp hq
      obtain ⟨rfl, rfl, rfl⟩ : t₁ = _ ∧ t₂ = _ ∧ r₂ = _ := by simpa using he
      rw [hf, Option.bind_some, Option.bind_some, hr, Option.bind_some,
        append_slot_right D₁ D₂ j (by omega)]
      simp only [Slot.map, Option.map_map]
      cases hq : ((D₂ (firstOf p.1 (Nat.le_add_right m j))).slot ⟨j, by omega⟩
          (right p.1 ⟨j, by omega⟩ le_rfl)).read p.2 with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Function.comp_apply, Option.some.injEq, Prod.mk.injEq,
          and_true]
        refine ⟨left_concat_eq (i := ⟨m + j, by omega⟩) p.1 _ (Fin.last m) (by simp), ?_⟩
        refine (right_concat (i := ⟨m + j, by omega⟩) p.1 _ ⟨j, by omega⟩ rfl
          (append_Type_natAdd (pSpec₁ := pSpec₁) ⟨j, by omega⟩)).trans ?_
        simp only [cast_cast, cast_eq]
        rfl

/-- A run past the first schedule is the first decoder's full run, then the second decoder's run
on what it left, read through `firstOf` and `right`. -/
theorem run_append_right (j : ℕ) (hj : j ≤ n) (l : List α) :
    ((D₁.append D₂).run (m + j) (by omega) l).map
        (fun p ↦ (firstOf p.1 (Nat.le_add_right m j), right p.1 ⟨j, by omega⟩ le_rfl, p.2)) =
      (D₁.runFull l).bind fun p ↦ ((D₂ p.1).run j hj p.2).map fun q ↦ (p.1, q.1, q.2) :=
  run_append_right_aux D₁ D₂ j hj l (m + j) (by omega) rfl

/-- **The append law**: the full run of `append D₁ D₂` is the full run of `D₁`, then the full run
of `D₂` on its transcript and the readings it left. -/
theorem runFull_append (l : List α) :
    (D₁.append D₂).runFull l =
      (D₁.runFull l).bind fun p ↦ ((D₂ p.1).runFull p.2).map fun q ↦ (p.1 ++ₜ q.1, q.2) := by
  have h : ((D₁.append D₂).runFull l).map (fun p ↦ (p.1.fst, p.1.snd, p.2)) =
      (D₁.runFull l).bind fun p ↦ ((D₂ p.1).runFull p.2).map fun q ↦ (p.1, q.1, q.2) :=
    run_append_right D₁ D₂ n le_rfl l
  cases ho : (D₁.append D₂).runFull l with
  | none =>
    rw [ho, Option.map_none] at h
    cases hf : D₁.runFull l with
    | none => rfl
    | some p =>
      rw [hf, Option.bind_some, eq_comm, Option.map_eq_none_iff] at h
      rw [Option.bind_some, h, Option.map_none]
  | some p =>
    rw [ho, Option.map_some, eq_comm, Option.bind_eq_some_iff] at h
    obtain ⟨⟨t₁, r₁⟩, hf, hq⟩ := h
    obtain ⟨⟨t₂, r₂⟩, hr, he⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨rfl, rfl, rfl⟩ : t₁ = _ ∧ t₂ = _ ∧ r₂ = _ := by simpa using he
    rw [hf, Option.bind_some, hr, Option.map_some, FullTranscript.append_fst_snd]

/-- **The append law** for exact decoding. -/
theorem decode_append (l : List α) :
    (D₁.append D₂).decode l =
      (D₁.runFull l).bind fun p ↦ ((D₂ p.1).decode p.2).map (p.1 ++ₜ ·) := by
  rw [decode, runFull_append]
  cases D₁.runFull l with
  | none => rfl
  | some p =>
    simp only [Option.bind_some, decode]
    cases (D₂ p.1).runFull p.2 with
    | none => rfl
    | some q => rcases q with ⟨t, _ | ⟨a, r⟩⟩ <;> rfl

end Append

/-! ## Runs of challenges and of sumcheck rounds -/

/-- `k` challenges in `C`, each read by the slot `s`. -/
def draws {C : Type} (s : Slot α C) : (k : ℕ) → SlotDecoder α (Protocol.draws C k)
  | 0 => empty
  | k + 1 => append (pSpec₁ := Protocol.draws C k) (pSpec₂ := draw C) (draws s k)
      fun _ ↦ single s

/-- `m` sumcheck rounds of degree `d` over `C`: the polynomial of each round by `poly σ` and its
challenge by `chal σ`, where the state `σ` (the running claim, say) is carried from each round to
the next by `next`. -/
def rounds {C σ : Type} {d : ℕ} (poly : σ → Slot α (Vector C (d + 1))) (chal : σ → Slot α C)
    (next : σ → (roundSpec C d).FullTranscript → σ) : σ → (m : ℕ) → SlotDecoder α (roundsSpec C d m)
  | _, 0 => empty
  | s, m + 1 => append (pSpec₁ := roundSpec C d) (pSpec₂ := roundsSpec C d m)
      (append (pSpec₁ := say (Vector C (d + 1))) (pSpec₂ := draw C) (single (poly s))
        fun _ ↦ single (chal s))
      fun t ↦ rounds poly chal next (next s t) m

end SlotDecoder

/-! ## Lists of steps -/

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
